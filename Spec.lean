/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and
  `bar.toml` records the SHA-256 it had then. The proofs live
  in `Proofs` (`Proofs/SpecProofs.lean`); `lake comparator`
  checks that each one proves exactly the statement written
  here. The `sorry` below is expected in this file only.

  The statements use only the definitions in `Dns/Value.lean`
  and `Dns/Parse.lean`, the code under proof named in
  `bar.toml`. No definition of their own is needed, so this
  project has no `Spec/Defs.lean`.
-/

import Dns

open Dns

/-! ## The round trips

The statements the slice stands on. Each one is the statement
of the proved theorem of the same shape in
`Proofs/RoundTrip.lean`, over the same well formedness
predicate, `Dns.WF`. -/

/-- Parsing the printed form of a well formed message gives
    the message back, all four sections. The printed form
    holds no compression, so this statement is about the
    uncompressed printing. -/
theorem Spec.parse_print {m : Message} (hw : WF m) :
    parse (print m) = some m := sorry

/-- The question only case of the same claim, the first
    slice's result: a message with a well formed header and
    well formed questions, and the other three sections
    empty, parses back from its printed form. -/
theorem Spec.parse_print_question_only {h : Header}
    {qs : List Question} (hh : WFHeader h)
    (hq : ∀ q ∈ qs, WFQuestion q)
    (hlen : qs.length < 65536) :
    parse (print ⟨h, qs, [], [], []⟩) =
      some ⟨h, qs, [], [], []⟩ := sorry

/-! ## The header

How the twelve header bytes are read, for every input. The
round trips above hold for any pair of reader and printer that
agree with each other, so they do not pin which bit is which;
these statements do, against RFC 1035 section 4.1.1 and the
layout of the fourth byte in RFC 6895 section 2. -/

/-- The header fields, read from the twelve header bytes, for
    any bytes after them, when the Z bit (0x40 of the fourth
    byte) is clear. The third byte holds QR (0x80), the
    opcode (0x78), AA (0x04), TC (0x02), and RD (0x01). The
    fourth holds RA (0x80), Z (0x40), AD (0x20, RFC 4035
    section 3.2.3), CD (0x10, RFC 4035 section 3.2.2), and
    the RCODE (0x0F). AD and CD are read like any other flag:
    a message with either set is not turned away for it. The
    counts are the next four big endian byte pairs. -/
theorem Spec.parseHeader_fields
    (i1 i2 f1 f2 q1 q2 a1 a2 n1 n2 r1 r2 : UInt8) (rest : List UInt8)
    (hz : (f2.toNat / 64) % 2 = 0) :
    parseHeader (i1 :: i2 :: f1 :: f2 ::
      q1 :: q2 :: a1 :: a2 :: n1 :: n2 :: r1 :: r2 :: rest) =
      some ({ id := i1.toNat * 256 + i2.toNat,
              qr := f1.toNat / 128, opcode := (f1.toNat / 8) % 16,
              aa := (f1.toNat / 4) % 2, tc := (f1.toNat / 2) % 2,
              rd := f1.toNat % 2,
              ra := f2.toNat / 128, ad := (f2.toNat / 32) % 2,
              cd := (f2.toNat / 16) % 2, rcode := f2.toNat % 16 },
        q1.toNat * 256 + q2.toNat, a1.toNat * 256 + a2.toNat,
        n1.toNat * 256 + n2.toNat, r1.toNat * 256 + r2.toNat, rest) := sorry

/-- A message whose Z bit (0x40 of the fourth byte) is set is
    refused, whatever the other bytes hold. Z is the one flag
    bit RFC 6895 section 2 still reserves. -/
theorem Spec.rejects_z_bit (i1 i2 f1 f2 : UInt8) (rest : List UInt8)
    (hz : (f2.toNat / 64) % 2 = 1) :
    parse (i1 :: i2 :: f1 :: f2 :: rest) = none := sorry

/-! ## Refused inputs

Single inputs the parser refuses, one for each headline rule
of `SPEC.md`. Each input is one of the named rejection cases
in the test harness, built there with its own builders, and
stands here byte for byte the same. The differential tests
cover these rules on many more inputs; these statements pin
them so a reader of the specification can check each rule
against one concrete case. -/


/-- A pointer that aims at its own position is refused.
    The name at offset 12 is a pointer to offset 12, and a
    target must be strictly earlier than the pointer. -/
theorem Spec.rejects_pointer_self :
    (parse ([0, 7, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      192, 12, 0, 1, 0, 1] : List UInt8)).isSome = false := sorry

/-- A pointer that aims forward is refused. The name at
    offset 12 points at offset 32, later in the message,
    where a name does sit; a target must be strictly
    earlier than the pointer. -/
theorem Spec.rejects_pointer_forward :
    (parse ([0, 7, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      192, 32, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 5, 108, 97, 116,
      101, 114, 0, 0, 1, 0, 1] : List UInt8)).isSome = false := sorry

/-- A pointer whose target lies past the end of the
    message is refused. The name at offset 12 points at
    offset 1023 in a message of 18 bytes. -/
theorem Spec.rejects_pointer_past_end :
    (parse ([0, 7, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      195, 255, 0, 1, 0, 1] : List UInt8)).isSome = false := sorry

/-- A pointer into the middle of a label is refused. The
    second name points at offset 14, the second byte of
    the label abc in the first name, and the byte there,
    98, stands in the reserved range for a length byte. -/
theorem Spec.rejects_pointer_mid_label :
    (parse ([0, 7, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0,
      3, 97, 98, 99, 0, 0, 1, 0, 1, 192, 14, 0,
      1, 0, 1] : List UInt8)).isSome = false := sorry

/-- A reserved length form in a record name is refused.
    The answer record's name starts with the byte 64,
    which has exactly one of its top two bits set. -/
theorem Spec.rejects_reserved_in_record :
    (parse ([0, 7, 128, 128, 0, 1, 0, 1, 0, 0, 0, 0,
      1, 120, 0, 0, 1, 0, 1, 64, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- A record whose data length runs past the end of the
    message is refused. The length says 10 bytes of data
    and 3 stand in the message. -/
theorem Spec.rejects_data_past_end :
    (parse ([0, 7, 128, 128, 0, 1, 0, 1, 0, 0, 0, 0,
      1, 120, 0, 0, 1, 0, 1, 1, 121, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, 10, 97, 98, 99] : List UInt8)).isSome = false := sorry

/-- An expanded name over 255 bytes, reached by
    chaining, is refused. Each name adds one 60 byte
    label and points at the name before it, and the
    fifth expansion needs 306 wire bytes, over the 255
    byte budget. -/
theorem Spec.rejects_chain_over_255 :
    (parse ([0, 7, 1, 0, 0, 5, 0, 0, 0, 0, 0, 0,
      60, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 0, 0, 1, 0, 1, 60, 98, 98, 98, 98, 98,
      98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98,
      98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98,
      98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98,
      98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98,
      98, 98, 98, 98, 98, 98, 98, 192, 12, 0, 1, 0,
      1, 60, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
      99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
      99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
      99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
      99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
      99, 99, 192, 78, 0, 1, 0, 1, 60, 100, 100, 100,
      100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
      100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
      100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
      100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
      100, 100, 100, 100, 100, 100, 100, 100, 100, 192, 145, 0,
      1, 0, 1, 60, 101, 101, 101, 101, 101, 101, 101, 101,
      101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101,
      101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101,
      101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101,
      101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101,
      101, 101, 101, 101, 192, 212, 0, 1, 0, 1] : List UInt8)).isSome = false := sorry

/-- A cycle that passes through a label is refused. The
    header bytes double as a name fragment: the label
    abcd stands at offset 5, a pointer back to offset 5
    stands at offset 10, and the question name at offset
    12 is that same pointer. Reading walks label,
    pointer, label, pointer; the backwards rule alone
    does not stop it, and the 255 byte budget turns it
    away. -/
theorem Spec.rejects_pointer_cycle_through_label :
    (parse ([0, 0, 0, 0, 0, 4, 97, 98, 99, 100, 192, 5,
      192, 5, 0, 1, 0, 1] : List UInt8)).isSome = false := sorry
