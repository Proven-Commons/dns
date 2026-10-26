/-
  The DNS message data model and the canonical printer. This
  slice reads the header and the question section of a DNS
  message, in the wire format of RFC 1035 sections 3 and 4. It
  does not read resource records, and it does not read name
  compression.

  A message is a header and a list of questions. The header holds
  the identifier and the flag fields of RFC 1035 section 4.1.1:
  QR, the four bit opcode, AA, TC, RD, RA, and the four bit
  RCODE. The reserved three flag bits are not held: the printer
  writes them as zero, and the parser turns a message away when
  one of them is set. The four section counts are not held
  either: the printer fills the question count from the question
  list and writes the other three as zero, and the parser turns
  a message away when one of those three is nonzero.

  Numbers are held as plain natural numbers, not as fixed width
  types. The identifier, QTYPE, and QCLASS are the values of two
  byte fields; the flag fields hold 0 or 1, and the opcode and
  RCODE hold values of four bits. Well formedness, below, states
  those bounds.

  A question is a name, a QTYPE, and a QCLASS. A name is a list
  of labels, and a label is a list of bytes. On the wire a name
  is each label written as a length byte and its bytes, ended by
  a zero byte.
-/

namespace Dns

/-- One label of a name: its bytes, without the length byte. -/
abbrev Label := List UInt8

/-- A name: its labels, in order. The empty list is the root. -/
abbrev Name := List Label

/-- The header fields of a message. The flag fields qr, aa, tc,
    rd, and ra hold 0 or 1 in a well formed header; opcode and
    rcode hold a four bit value. -/
structure Header where
  /-- The message identifier, a two byte value. -/
  id : Nat
  /-- QR: 0 for a query, 1 for a response. -/
  qr : Nat
  /-- The four bit opcode. -/
  opcode : Nat
  /-- AA: authoritative answer. -/
  aa : Nat
  /-- TC: truncation. -/
  tc : Nat
  /-- RD: recursion desired. -/
  rd : Nat
  /-- RA: recursion available. -/
  ra : Nat
  /-- The four bit response code. -/
  rcode : Nat
  deriving DecidableEq, Repr

/-- One question: a name, a QTYPE, and a QCLASS, each of the
    last two a two byte value. -/
structure Question where
  name : Name
  qtype : Nat
  qclass : Nat
  deriving DecidableEq, Repr

/-- A message: a header and its questions. -/
structure Message where
  header : Header
  questions : List Question
  deriving DecidableEq, Repr

/-- A value as two bytes, big endian. The value is taken modulo
    2^16; callers only pass values below that. -/
def be16 (n : Nat) : List UInt8 :=
  [ (n / 256).toUInt8, n.toUInt8 ]

/-- The value of two bytes read big endian. -/
def u16 (a b : UInt8) : Nat :=
  a.toNat * 256 + b.toNat

/-- The first flag byte: QR in the top bit, then the opcode in
    four bits, then AA, TC, and RD. -/
def flags1 (h : Header) : UInt8 :=
  (h.qr * 128 + h.opcode * 8 + h.aa * 4 + h.tc * 2 + h.rd).toUInt8

/-- The second flag byte: RA in the top bit, then the three
    reserved bits, written as zero, then the RCODE in four
    bits. -/
def flags2 (h : Header) : UInt8 :=
  (h.ra * 128 + h.rcode).toUInt8

/-- A name in printed form: each label as a length byte and its
    bytes, then a zero byte. -/
def printName : Name → List UInt8
  | [] => [0]
  | l :: ls => (l.length.toUInt8 :: l) ++ printName ls

/-- The wire length of a name: one length byte per label, the
    label bytes, and the final zero byte. -/
def wireLen : Name → Nat
  | [] => 1
  | l :: ls => (l.length + 1) + wireLen ls

/-- One question in printed form. -/
def printQuestion (q : Question) : List UInt8 :=
  printName q.name ++ be16 q.qtype ++ be16 q.qclass

/-- The questions in printed form, in order. -/
def printQuestions : List Question → List UInt8
  | [] => []
  | q :: qs => printQuestion q ++ printQuestions qs

/-- The header in printed form, with the question count filled
    in and the other three counts written as zero. -/
def printHeader (h : Header) (qd : Nat) : List UInt8 :=
  be16 h.id ++ [flags1 h, flags2 h] ++ be16 qd ++
    be16 0 ++ be16 0 ++ be16 0

/-- A message in printed form. -/
def print (m : Message) : List UInt8 :=
  printHeader m.header m.questions.length ++ printQuestions m.questions

/-- A well formed header: the identifier fits two bytes, each
    single flag field is 0 or 1, and the opcode and the RCODE
    fit four bits. -/
def WFHeader (h : Header) : Prop :=
  h.id < 65536 ∧ h.qr ≤ 1 ∧ h.opcode < 16 ∧ h.aa ≤ 1 ∧ h.tc ≤ 1 ∧
    h.rd ≤ 1 ∧ h.ra ≤ 1 ∧ h.rcode < 16

/-- A well formed question: QTYPE and QCLASS fit two bytes,
    every label holds 1 to 63 bytes, and the name fits the 255
    byte wire bound. -/
def WFQuestion (q : Question) : Prop :=
  q.qtype < 65536 ∧ q.qclass < 65536 ∧
    (∀ l ∈ q.name, 1 ≤ l.length ∧ l.length ≤ 63) ∧
    wireLen q.name ≤ 255

/-- A well formed message: a well formed header, well formed
    questions, and a question count that fits two bytes. -/
def WF (m : Message) : Prop :=
  WFHeader m.header ∧ (∀ q ∈ m.questions, WFQuestion q) ∧
    m.questions.length < 65536

end Dns
