/-
  The DNS message parser. It reads a list of bytes and returns
  the message, or `none` when the bytes break any of the rules
  the plan states:

  - The header is twelve bytes. The answer, authority, and
    additional counts must all be zero, and the three reserved
    flag bits must be zero.
  - Exactly the header's question count of questions is read,
    and no bytes may follow the last one.
  - A name reads labels until a zero length byte. A length byte
    from 1 to 63 introduces that many label bytes. A length byte
    with either of its top two bits set is a compression pointer
    or a reserved form, and turns the message away; this slice
    does not read compression. The name's wire length, length
    bytes, label bytes, and the final zero together, must stay
    within 255 bytes.

  `parseNameGo` takes a fuel count and a byte budget. The fuel
  is one more than the length of the input, which is always
  enough, since every step takes at least one byte. The budget
  starts at 255 and falls by what each label and the final zero
  take. A hostile input is rejected, never looped on.
-/

import Dns.Value

namespace Dns

/-- Read two bytes as a big endian value, with the rest of the
    input. Fewer than two bytes gives `none`. -/
def getU16 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: rest => some (u16 a b, rest)
  | _ => none

/-- Read a name from the front of the input. `fuel` bounds the
    steps, and `budget` is the wire length the name may still
    take, counting each length byte, the label bytes, and the
    final zero. Returns the name and the input after it. -/
def parseNameGo : Nat → Nat → List UInt8 → Option (Name × List UInt8)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, budget, b :: rest =>
    if b = 0 then
      if 1 ≤ budget then some ([], rest) else none
    else if b.toNat ≤ 63 then
      if b.toNat + 1 ≤ budget then
        let label := rest.take b.toNat
        if label.length = b.toNat then
          match parseNameGo fuel (budget - (b.toNat + 1)) (rest.drop b.toNat) with
          | some (ls, rest') => some (label :: ls, rest')
          | none => none
        else none
      else none
    else none

/-- Read a name, with the full 255 byte budget. -/
def parseName (bs : List UInt8) : Option (Name × List UInt8) :=
  parseNameGo (bs.length + 1) 255 bs

/-- Read one question: a name, then QTYPE and QCLASS, two bytes
    each, big endian. -/
def parseQuestion (bs : List UInt8) : Option (Question × List UInt8) :=
  (parseName bs).bind fun (nm, rest) =>
  (getU16 rest).bind fun (qt, rest) =>
  (getU16 rest).bind fun (qc, rest) =>
  some (⟨nm, qt, qc⟩, rest)

/-- Read exactly `n` questions. -/
def parseQuestions : Nat → List UInt8 → Option (List Question × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    parseQuestion bs >>= fun (q, rest) =>
    parseQuestions n rest >>= fun (qs, rest') =>
    some (q :: qs, rest')

/-- Read the twelve header bytes. Returns the header, the
    question count, and the rest of the input. A nonzero answer,
    authority, or additional count, or a set reserved flag bit,
    gives `none`. -/
def parseHeader : List UInt8 → Option (Header × Nat × List UInt8)
  | i1 :: i2 :: f1 :: f2 ::
    q1 :: q2 :: a1 :: a2 :: n1 :: n2 :: r1 :: r2 :: rest =>
    if (f2.toNat / 16) % 8 = 0 ∧ u16 a1 a2 = 0 ∧
        u16 n1 n2 = 0 ∧ u16 r1 r2 = 0 then
      some (⟨u16 i1 i2, f1.toNat / 128, (f1.toNat / 8) % 16,
        (f1.toNat / 4) % 2, (f1.toNat / 2) % 2, f1.toNat % 2,
        f2.toNat / 128, f2.toNat % 16⟩, u16 q1 q2, rest)
    else none
  | _ => none

/-- Parse a whole message: the header, then its questions, and
    nothing after them. -/
def parse (bs : List UInt8) : Option Message :=
  parseHeader bs >>= fun (h, qd, rest) =>
  parseQuestions qd rest >>= fun (qs, rest') =>
  if rest' = [] then some ⟨h, qs⟩ else none

end Dns
