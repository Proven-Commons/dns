# Specification: dns

A DNS wire format parser and printer in Lean, for a whole
message, following RFC 1035 sections 3, 4.1, and 4.1.4. It
reads the header, the question section, and the answer,
authority, and additional sections of resource records. It
reads name compression. It does not write compressed names,
and it does not look inside record data.

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

All counts are two byte values, big endian. Each count says
how many entries its section holds, and the sections follow
the header in the order above. The input must end with the
last entry of the last section. Leftover bytes, and any entry
cut short, turn the message away.

The data model holds the identifier and the flag fields. QR,
AA, TC, RD, and RA are held as numbers, 0 or 1 in a well formed
header. The opcode and the RCODE are held as numbers that fit
four bits. The reserved three bits are not held: the printer
writes them as zero, and reading turns the message away when
any of them is set, as the RFC asks senders to set them to
zero. The four counts are not held: the printer fills them
from the four lists.

## Names and compression

A name is a row of labels, RFC 1035 section 3.1. In the model
a name is always expanded: a list of labels, each a list of
bytes. The empty list is the root.

On the wire, reading a name at some position reads a sequence
of items:

- A length byte from 1 to 63, with both top bits clear, and
  that many label bytes. Label bytes may hold any value.
- A zero byte, which ends the name.
- A pointer: two bytes with both top bits set. The remaining
  fourteen bits are an offset, a position in the whole
  message. The name continues at that offset, and the pointer
  ends the name at the place it was read: the bytes after a
  name that ends in a pointer are the bytes after the pointer,
  not the bytes after the name the pointer aimed at.
- A length byte with exactly one top bit set is a reserved
  form. It turns the message away.

Pointer safety, enforced while reading:

- The offset is strictly less than the position of the
  pointer's first byte. A pointer can only point backwards.
  In a chain that jumps from pointer straight to pointer,
  each step's target is the next pointer's position, so the
  targets strictly decrease, step by step, toward the start
  of the message.
- The offset lies inside the message. This follows from the
  rule above, and is checked as well.
- The bytes at the offset are read by these same rules, so a
  pointer may aim at a label, at the zero byte of the root,
  or at another pointer.
- The expanded name, counted as if it were written in full
  (one length byte per label, the label bytes, and the final
  zero), stays within 255 bytes. Labels read after a jump
  count toward the same budget as labels read before it.
- A step budget, the message length plus 257, also falls at
  every item read. A reading that would walk in a circle
  spends it and is turned away.

## Questions

A question is a name, then QTYPE (two bytes, big endian), then
QCLASS (two bytes, big endian). QTYPE and QCLASS are held as
the values of those two byte fields; this layer gives them no
meaning.

## Records

A resource record is a name, then TYPE (two bytes), CLASS
(two bytes), TTL (four bytes), RDLENGTH (two bytes), and
RDLENGTH bytes of data, all big endian. TYPE, CLASS, and TTL
are held as the values of their fields. The data is held as
opaque bytes: this layer does not read names or anything
else inside it, even when the data holds bytes shaped like a
name.

## Printing

The printer writes the header with the four counts filled
from the lists, then each section in order. Every name is
written in full, as length byte and bytes per label with a
final zero. No compression is written. A record is written
as its expanded name, TYPE, CLASS, TTL, the data length, and
the data.

## The claim

`Dns.Proofs.parse_print`: for every well formed message,
parsing its printed form gives the message back, at the level
of the message value, with all four sections.

`Dns.Proofs.parse_print_question_only` states the first
slice's result as a corollary, for a message whose answer,
authority, and additional sections are empty.

Well formed means: the header fields fit their widths (the
identifier in two bytes, QR, AA, TC, RD, and RA each 0 or 1,
the opcode and the RCODE in four bits); each section count
fits two bytes; QTYPE, QCLASS, TYPE, and CLASS fit two bytes;
TTL fits four bytes; every record's data length fits two
bytes; every label of every expanded name holds 1 to 63
bytes; and every expanded name fits the 255 byte wire bound.

A note on compressed input: parsing a compressed message
yields the expanded message, and its printing is the
uncompressed form of that message. So the printed form of a
parsed message need not equal a compressed input byte for
byte, and no such claim is made. The round trip above is
about the message value.

That the parser accepts every message these rules allow, and
turns away every message they forbid, is not proved. The
differential tests in `tests/` check that behaviour instead.

## The command-line tool

`Main.lean` is a small front end used by the tests. It reads
one request per line and prints one answer per line. A
request is an operation word, then optionally one space and
the message bytes as comma-separated decimal numbers (with
no numbers, the input is empty). A malformed request (an
unknown operation, a field that is not plain decimal digits,
a code above 255, extra spaces) prints `error`. A line may
end in LF or CR LF.

Two operations:

- `parse`: the answer is `ok:` and the comma-separated codes
  of the canonical reprint (names expanded) when the message
  parses, or `none` when it is turned away.
- `sections`: the answer is `ok:` and the comma-separated
  codes of a summary text, or `none` when the message is
  turned away. The summary is plain ASCII, in this shape:

  `id=<id>;qd=<n>;an=<n>;ns=<n>;ar=<n>;q=<questions>;a=<answers>;s=<authority records>;t=<additional records>`

  The four counts come first, then the entries of the four
  sections in message order. Entries within one section are
  split by `|`. A question entry is `<name>/<qtype>/<qclass>`.
  A record entry is `<name>/<type>/<class>/<ttl>/<data>`,
  with the data as byte codes split by commas. A name is the
  word `ROOT` for the root, or its labels in order split by
  `.`, each label written as its byte codes split by `-`.
  Every name in the summary is expanded, however it was
  written on the wire.
