/-
  The DNS whole message parser. It reads all four sections and
  expands compressed names while reading.

  A name is read from a suffix of the whole message. Keeping the
  whole message beside the suffix lets a compression pointer use
  its fourteen bit offset as a position in that whole message.
  The position of a byte in the suffix is the length of the
  whole message minus the length of the suffix.

  Pointer safety is enforced in `parseNameGo`. No single
  rule below is the whole story. Termination and rejection
  come from the rules together:

  - A pointer is two bytes with both top bits set. A byte with
    exactly one top bit set is a reserved form and is rejected.
  - The pointer target is strictly less than the position of
    the pointer's first byte. A pointer therefore points
    backwards. That rule on its own does not stop a cycle:
    a pointer can aim back at a label, and the bytes after
    that label can run forward again to the same pointer, so
    reading would walk label, pointer, label, pointer,
    without end if nothing else stopped it. Only a chain that
    jumps from pointer straight to pointer has strictly
    decreasing target offsets.
  - The target lies inside the message, because it is less than
    that pointer position.
  - The bytes at the target are read by the same name rules.
  - The remaining expanded-name budget travels through a jump.
    Labels read at the target count toward the same 255 byte
    expanded wire limit as labels read before the jump. This
    budget is what turns away the label cycle above: each
    pass through a label spends its length byte and its bytes
    from the budget, so after finitely many passes the budget
    is spent and the reading is rejected. For a four byte
    label the spend is 5 bytes a pass, so the budget runs out
    after 51 passes, well before the fuel below.
  - A fuel count also falls at every label, zero, or pointer
    step. The fuel starts at the message length plus 257. A
    successful walk through a deterministic byte graph cannot
    repeat a starting position without looping forever, so it
    has at most one step per byte position, plus room for one
    step per possible byte of an expanded name. Fuel is a
    second bound: it ends any walk that keeps spending steps
    without finishing, including a cycle whose steps add
    little or nothing to the expanded name.

  A record holds its data as opaque bytes. The parser does not
  look inside record data, including when record data happens
  to contain bytes shaped like a name.
-/

import Dns.Value

namespace Dns

/-- Read two bytes as a big endian value, with the rest of the
    input. Fewer than two bytes gives `none`. -/
def getU16 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: rest => some (u16 a b, rest)
  | _ => none

/-- Read four bytes as a big endian value, with the rest of the
    input. Fewer than four bytes gives `none`. -/
def getU32 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: c :: d :: rest => some (u32 a b c d, rest)
  | _ => none

/-- Take exactly `n` bytes, with the rest of the input. Fewer
    than `n` bytes gives `none`. -/
def takeBytes (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if bs.length ≥ n then some (bs.take n, bs.drop n) else none

/-- Read a name at the front of `rest`, a suffix of `full`.

    `fuel` bounds the steps, and `budget` is the expanded wire
    length the name may still take, counting each label length
    byte, the label bytes, and the final zero. Returns the
    expanded name, the suffix after the name at the place it was
    read, and the remaining budget.

    A pointer ends the name at the place it is read. Its target
    is read for labels and budget only; reading does not resume
    after the target name. -/
def parseNameGo : Nat → List UInt8 → Nat → List UInt8 →
    Option (Name × List UInt8 × Nat)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, full, budget, b :: rest =>
    if b = 0 then
      if 1 ≤ budget then some ([], rest, budget - 1) else none
    else if b.toNat ≤ 63 then
      if b.toNat + 1 ≤ budget then
        let label := rest.take b.toNat
        if label.length = b.toNat then
          match parseNameGo fuel full (budget - (b.toNat + 1))
              (rest.drop b.toNat) with
          | some (ls, rest', remaining) => some (label :: ls, rest', remaining)
          | none => none
        else none
      else none
    else if 192 ≤ b.toNat then
      match rest with
      | [] => none
      | c :: after =>
        let pointerPosition := full.length - (b :: c :: after).length
        let target := (b.toNat - 192) * 256 + c.toNat
        if target < pointerPosition ∧ target < full.length then
          match parseNameGo fuel full budget (full.drop target) with
          | some (ls, _, remaining) => some (ls, after, remaining)
          | none => none
        else none
    else none

/-- Read a name in a whole message, with the full 255 byte
    expanded budget and the standard fuel. -/
def parseNameIn (full rest : List UInt8) :
    Option (Name × List UInt8 × Nat) :=
  parseNameGo (full.length + 257) full 255 rest

/-- Read a name when the bytes supplied are the whole message.
    This keeps the first slice's top level name entry point. -/
def parseName (bs : List UInt8) : Option (Name × List UInt8) :=
  match parseNameIn bs bs with
  | some (nm, rest, _) => some (nm, rest)
  | none => none

/-- Read one question from a suffix of a whole message. -/
def parseQuestionIn (full bs : List UInt8) :
    Option (Question × List UInt8) :=
  (parseNameIn full bs).bind fun (nm, rest, _) =>
  (getU16 rest).bind fun (qt, rest) =>
  (getU16 rest).bind fun (qc, rest) =>
  some (⟨nm, qt, qc⟩, rest)

/-- Read one question when the bytes supplied are the whole
    message. -/
def parseQuestion (bs : List UInt8) : Option (Question × List UInt8) :=
  parseQuestionIn bs bs

/-- Read exactly `n` questions from a suffix of a whole
    message. -/
def parseQuestionsIn : Nat → List UInt8 → List UInt8 →
    Option (List Question × List UInt8)
  | 0, _, bs => some ([], bs)
  | n + 1, full, bs =>
    parseQuestionIn full bs >>= fun (q, rest) =>
    parseQuestionsIn n full rest >>= fun (qs, rest') =>
    some (q :: qs, rest')

/-- Read exactly `n` questions when the bytes supplied are the
    whole message. -/
def parseQuestions (n : Nat) (bs : List UInt8) :
    Option (List Question × List UInt8) :=
  parseQuestionsIn n bs bs

/-- Read one record from a suffix of a whole message. -/
def parseRecordIn (full bs : List UInt8) :
    Option (Record × List UInt8) :=
  (parseNameIn full bs).bind fun (nm, rest, _) =>
  (getU16 rest).bind fun (rt, rest) =>
  (getU16 rest).bind fun (rc, rest) =>
  (getU32 rest).bind fun (ttl, rest) =>
  (getU16 rest).bind fun (rdlen, rest) =>
  (takeBytes rdlen rest).bind fun (data, rest) =>
  some (⟨nm, rt, rc, ttl, data⟩, rest)

/-- Read one record when the bytes supplied are the whole
    message. -/
def parseRecord (bs : List UInt8) : Option (Record × List UInt8) :=
  parseRecordIn bs bs

/-- Read exactly `n` records from a suffix of a whole message. -/
def parseRecordsIn : Nat → List UInt8 → List UInt8 →
    Option (List Record × List UInt8)
  | 0, _, bs => some ([], bs)
  | n + 1, full, bs =>
    parseRecordIn full bs >>= fun (r, rest) =>
    parseRecordsIn n full rest >>= fun (rs, rest') =>
    some (r :: rs, rest')

/-- Read exactly `n` records when the bytes supplied are the
    whole message. -/
def parseRecords (n : Nat) (bs : List UInt8) :
    Option (List Record × List UInt8) :=
  parseRecordsIn n bs bs

/-- Read the twelve header bytes. Returns the header, the four
    section counts, and the rest of the input. A set reserved
    flag bit gives `none`. -/
def parseHeader : List UInt8 →
    Option (Header × Nat × Nat × Nat × Nat × List UInt8)
  | i1 :: i2 :: f1 :: f2 ::
    q1 :: q2 :: a1 :: a2 :: n1 :: n2 :: r1 :: r2 :: rest =>
    if (f2.toNat / 16) % 8 = 0 then
      some (⟨u16 i1 i2, f1.toNat / 128, (f1.toNat / 8) % 16,
        (f1.toNat / 4) % 2, (f1.toNat / 2) % 2, f1.toNat % 2,
        f2.toNat / 128, f2.toNat % 16⟩,
        u16 q1 q2, u16 a1 a2, u16 n1 n2, u16 r1 r2, rest)
    else none
  | _ => none

/-- Parse a whole message: the header, then all four sections
    in order, and nothing after the last entry. -/
def parse (bs : List UInt8) : Option Message :=
  parseHeader bs >>= fun (h, qd, an, ns, ar, rest) =>
  parseQuestionsIn qd bs rest >>= fun (qs, rest) =>
  parseRecordsIn an bs rest >>= fun (answers, rest) =>
  parseRecordsIn ns bs rest >>= fun (authorities, rest) =>
  parseRecordsIn ar bs rest >>= fun (additionals, rest) =>
  if rest = [] then some ⟨h, qs, answers, authorities, additionals⟩ else none

end Dns
