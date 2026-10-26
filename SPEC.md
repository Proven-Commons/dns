# Specification: dns

A DNS wire format parser and printer in Lean, for the header
and the question section of a message, following RFC 1035
sections 3 and 4. This slice reads no resource records and no
name compression.

## The header

A message starts with twelve bytes, RFC 1035 section 4.1.1:

| Bytes | Field |
|-------|-------|
| 0, 1 | ID, the message identifier |
| 2 | QR (top bit), opcode (next four bits), AA, TC, RD (last bit) |
| 3 | RA (top bit), the reserved three bits, RCODE (last four bits) |
| 4, 5 | QDCOUNT, the number of questions |
| 6, 7 | ANCOUNT, the number of answer records |
| 8, 9 | NSCOUNT, the number of authority records |
| 10, 11 | ARCOUNT, the number of additional records |

All counts are two byte values, big endian.

The data model holds the identifier and the flag fields. QR,
AA, TC, RD, and RA are held as numbers, 0 or 1 in a well formed
header. The opcode and the RCODE are held as numbers that fit
four bits. The reserved three bits are not held: the printer
writes them as zero. The four counts are not held: the printer
fills QDCOUNT from the question list and writes the other
three as zero.

Reading turns the message away when ANCOUNT, NSCOUNT, or
ARCOUNT is nonzero, and when any of the three reserved bits
is set, as the RFC asks senders to set them to zero. A shorter
input than twelve bytes is turned away.

## Questions and names

Exactly QDCOUNT questions follow the header, and the input
must end with the last one. Leftover bytes turn the message
away.

A question is a name, then QTYPE (two bytes, big endian), then
QCLASS (two bytes, big endian). QTYPE and QCLASS are held as
the values of those two byte fields; this layer gives them no
meaning.

A name is a row of labels ended by a zero byte, RFC 1035
section 3.1. A label is a length byte and that many bytes:

- The length byte holds a value from 1 to 63, with both of its
  top two bits clear.
- A length byte with either top bit set is a compression
  pointer or a reserved form. Both turn the message away in
  this slice. Compression is not read.
- Label bytes may hold any value.
- The name's wire length, one length byte per label, the label
  bytes, and the final zero together, stays within 255 bytes.
- A zero byte ends the name. The empty name, a single zero
  byte, is the root.

A label cut short by the end of the input, a name that runs
off the end, or QTYPE or QCLASS bytes cut short all turn the
message away.

## Printing

The printer writes the header with QDCOUNT filled from the
question list and the other three counts zero, then each
question in order: the name as length byte and bytes per label
with a final zero, then QTYPE and QCLASS as two bytes each,
big endian. A well formed message (see the README for the
rules) prints to bytes this parser reads back as the same
message.

## The claim

`Dns.Proofs.parse_print`: for every well formed message,
parsing its printed form gives the message back.

Well formed means: the identifier, QTYPE, and QCLASS values
fit two bytes; QR, AA, TC, RD, and RA are each 0 or 1; the
opcode and the RCODE fit four bits; the question count fits
two bytes; every label holds 1 to 63 bytes; and every name
fits the 255 byte wire bound.

That the parser accepts every message these rules allow, and
turns away every message they forbid, is not proved. The
differential tests in `tests/` check that behaviour instead.

## The command-line tool

`Main.lean` is a small front end used by the tests. It reads
one request per line and prints one answer per line. A request
is the word `parse`, then optionally one space and the message
bytes as comma-separated decimal numbers (with no numbers, the
input is empty). The answer is `ok:` and the comma-separated
codes of the canonical reprint when the message parses, or
`none` when it is turned away. A malformed request (an unknown
operation, a field that is not plain decimal digits, a code
above 255, extra spaces) prints `error`. A line may end in LF
or CR LF.
