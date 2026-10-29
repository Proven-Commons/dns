/-
  Proofs of the statements in `Spec.lean`, under the same
  names.

  The round trips are the theorems proved in
  `Proofs/RoundTrip.lean`. The refusals are single inputs,
  checked in the kernel with `decide +kernel`: no native
  evaluation, which the bar forbids.
-/

import Dns
import Proofs.RoundTrip

open Dns

theorem Spec.parse_print {m : Message} (hw : WF m) :
    parse (print m) = some m :=
  Dns.Proofs.parse_print hw

theorem Spec.parse_print_question_only {h : Header}
    {qs : List Question} (hh : WFHeader h)
    (hq : ∀ q ∈ qs, WFQuestion q)
    (hlen : qs.length < 65536) :
    parse (print ⟨h, qs, [], [], []⟩) =
      some ⟨h, qs, [], [], []⟩ :=
  Dns.Proofs.parse_print_question_only hh hq hlen


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
        n1.toNat * 256 + n2.toNat, r1.toNat * 256 + r2.toNat, rest) := by
  rw [Dns.Proofs.parseHeader_step, if_pos hz]
  rfl

theorem Spec.rejects_z_bit (i1 i2 f1 f2 : UInt8) (rest : List UInt8)
    (hz : (f2.toNat / 64) % 2 = 1) :
    parse (i1 :: i2 :: f1 :: f2 :: rest) = none := by
  have hh : parseHeader (i1 :: i2 :: f1 :: f2 :: rest) = none := by
    match rest with
    | q1 :: q2 :: a1 :: a2 :: n1 :: n2 :: r1 :: r2 :: rest =>
      rw [Dns.Proofs.parseHeader_step, if_neg (by omega)]
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
    | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] => rfl
  show (parseHeader (i1 :: i2 :: f1 :: f2 :: rest) >>= _) = none
  rw [hh]
  rfl

theorem Spec.rejects_pointer_self :
    (parse ([0, 7, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      192, 12, 0, 1, 0, 1] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_pointer_forward :
    (parse ([0, 7, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      192, 32, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 5, 108, 97, 116,
      101, 114, 0, 0, 1, 0, 1] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_pointer_past_end :
    (parse ([0, 7, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      195, 255, 0, 1, 0, 1] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_pointer_mid_label :
    (parse ([0, 7, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0,
      3, 97, 98, 99, 0, 0, 1, 0, 1, 192, 14, 0,
      1, 0, 1] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_reserved_in_record :
    (parse ([0, 7, 128, 128, 0, 1, 0, 1, 0, 0, 0, 0,
      1, 120, 0, 0, 1, 0, 1, 64, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97,
      0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_data_past_end :
    (parse ([0, 7, 128, 128, 0, 1, 0, 1, 0, 0, 0, 0,
      1, 120, 0, 0, 1, 0, 1, 1, 121, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, 10, 97, 98, 99] : List UInt8)).isSome = false := by
  decide +kernel


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
      101, 101, 101, 101, 192, 212, 0, 1, 0, 1] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_pointer_cycle_through_label :
    (parse ([0, 0, 0, 0, 0, 4, 97, 98, 99, 100, 192, 5,
      192, 5, 0, 1, 0, 1] : List UInt8)).isSome = false := by
  decide +kernel
