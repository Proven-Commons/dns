/-
  The DNS message data model and the canonical printer.

  A message holds the header fields and four sections: questions,
  answer records, authority records, and additional records. The
  header is the one in RFC 1035 section 4.1.1, with the three
  bits after RA as RFC 6895 section 2 lays them out: an
  identifier, QR, the four bit opcode, AA, TC, RD, RA, Z, AD,
  CD, and the four bit RCODE. AD and CD (RFC 4035 section 3.2)
  are held as fields. Z, the one bit still reserved, is not
  held: the printer writes it as zero, and the parser turns a
  message away when it is set. The four section counts are not
  held either. The printer fills them from the four lists.

  Numbers are held as plain natural numbers, not as fixed width
  types. Well formedness, which states the wire bounds, is part
  of the specification, in `Dns/Spec/Defs.lean`.

  Names in this model are always expanded. A name is a list of
  labels, and a label is a list of bytes. Compression can occur
  in bytes read by the parser, but it never occurs in this model
  or in the printer. The printer writes every name in full.
-/

namespace Dns

/-- One label of a name: its bytes, without the length byte. -/
abbrev Label := List UInt8

/-- A name: its labels, in order. The empty list is the root. -/
abbrev Name := List Label

/-- The header fields of a message. The flag fields qr, aa, tc,
    rd, ra, ad, and cd hold 0 or 1 in a well formed header;
    opcode and rcode hold a four bit value. -/
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
  /-- AD: authentic data (RFC 4035 section 3.2.3). -/
  ad : Nat
  /-- CD: checking disabled (RFC 4035 section 3.2.2). -/
  cd : Nat
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

/-- One resource record. Its data is opaque at this layer. -/
structure Record where
  name : Name
  type : Nat
  rclass : Nat
  ttl : Nat
  data : List UInt8
  deriving DecidableEq, Repr

/-- A whole message: a header and its four sections. -/
structure Message where
  header : Header
  questions : List Question
  answers : List Record
  authorities : List Record
  additionals : List Record
  deriving DecidableEq, Repr

/-- A value as two bytes, big endian. The value is taken modulo
    2^16; callers only pass values below that. -/
def be16 (n : Nat) : List UInt8 :=
  [ (n / 256).toUInt8, n.toUInt8 ]

/-- The value of two bytes read big endian. -/
def u16 (a b : UInt8) : Nat :=
  a.toNat * 256 + b.toNat

/-- A value as four bytes, big endian. The value is taken modulo
    2^32; callers only pass values below that. -/
def be32 (n : Nat) : List UInt8 :=
  [ (n / 16777216).toUInt8, (n / 65536).toUInt8,
    (n / 256).toUInt8, n.toUInt8 ]

/-- The value of four bytes read big endian. -/
def u32 (a b c d : UInt8) : Nat :=
  a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat

/-- The first flag byte: QR in the top bit, then the opcode in
    four bits, then AA, TC, and RD. -/
def flags1 (h : Header) : UInt8 :=
  (h.qr * 128 + h.opcode * 8 + h.aa * 4 + h.tc * 2 + h.rd).toUInt8

/-- The second flag byte (RFC 6895 section 2): RA in the top
    bit, then Z, the reserved bit, written as zero, then AD,
    then CD, then the RCODE in four bits. -/
def flags2 (h : Header) : UInt8 :=
  (h.ra * 128 + h.ad * 32 + h.cd * 16 + h.rcode).toUInt8

/-- A name in printed form: each label as a length byte and its
    bytes, then a zero byte. -/
def printName : Name → List UInt8
  | [] => [0]
  | l :: ls => (l.length.toUInt8 :: l) ++ printName ls

/-- One question in printed form. -/
def printQuestion (q : Question) : List UInt8 :=
  printName q.name ++ be16 q.qtype ++ be16 q.qclass

/-- The questions in printed form, in order. -/
def printQuestions : List Question → List UInt8
  | [] => []
  | q :: qs => printQuestion q ++ printQuestions qs

/-- One record in printed form. The name is expanded. Then come
    type, class, TTL, the data length, and the data. -/
def printRecord (r : Record) : List UInt8 :=
  printName r.name ++ be16 r.type ++ be16 r.rclass ++ be32 r.ttl ++
    be16 r.data.length ++ r.data

/-- The records in printed form, in order. -/
def printRecords : List Record → List UInt8
  | [] => []
  | r :: rs => printRecord r ++ printRecords rs

/-- The header in printed form, with all four counts supplied by
    the caller. -/
def printHeader (h : Header) (qd an ns ar : Nat) : List UInt8 :=
  be16 h.id ++ [flags1 h, flags2 h] ++ be16 qd ++
    be16 an ++ be16 ns ++ be16 ar

/-- A whole message in printed form. Names are uncompressed. -/
def print (m : Message) : List UInt8 :=
  printHeader m.header m.questions.length m.answers.length
      m.authorities.length m.additionals.length ++
    printQuestions m.questions ++ printRecords m.answers ++
    printRecords m.authorities ++ printRecords m.additionals

end Dns
