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
| 3 | RA (0x80), Z (0x40), AD (0x20), CD (0x10), RCODE (last four bits) |
| 4, 5 | QDCOUNT, the number of questions |
| 6, 7 | ANCOUNT, the number of answer records |
| 8, 9 | NSCOUNT, the number of authority records |
| 10, 11 | ARCOUNT, the number of additional records |

All counts are two byte values, big endian. Each count says
how many entries its section holds, and the sections follow
the header in the order above. The input must end with the
last entry of the last section. Leftover bytes, and any entry
cut short, turn the message away.

The fourth byte follows the layout in RFC 6895 section 2.
RFC 1035 reserved the three bits after RA as Z. RFC 4035
section 3.2 has since defined two of them: AD, authentic data
(0x20), and CD, checking disabled (0x10). Only Z (0x40) is
still reserved.

The data model holds the identifier and the flag fields. QR,
AA, TC, RD, RA, AD, and CD are held as numbers, 0 or 1 in a
well formed header. The opcode and the RCODE are held as
numbers that fit four bits. A message with AD or CD set is
read like any other: an RD+AD query (flag bytes `01 20`, which
dig sends by default, RFC 6840 section 5.7), an RD+CD query
(`01 10`), and a validating resolver's RA+AD response
(`81 a0`) are all read, and the printer writes both bits back.
Z is not held: the printer writes it as zero, and reading
turns the message away when it is set, as RFC 1035 asks
senders to set it to zero. The four counts are not held: the
printer fills them from the four lists.

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

Pointer safety, enforced while reading. No single rule
below is the whole story. Termination and rejection come
from the rules together:

- The offset is strictly less than the position of the
  pointer's first byte. A pointer can only point backwards.
  That rule on its own does not stop a cycle. A pointer can
  aim back at a label, and the bytes after that label can run
  forward again to the same pointer, so reading would walk
  label, pointer, label, pointer, without end if nothing
  else stopped it. Only in a chain that jumps from pointer
  straight to pointer do the targets strictly decrease, step
  by step, toward the start of the message.
- The offset lies inside the message. This follows from the
  rule above, and is checked as well.
- The bytes at the offset are read by these same rules, so a
  pointer may aim at a label, at the zero byte of the root,
  or at another pointer. It may also aim inside a label, or
  inside the name being read: no rule forbids either, and
  the bytes there are read as a name. When the byte there is
  a reserved form, the message is turned away for that.
- One name follows at most 16 pointers. A 17th turns the
  message away. dnspython uses the same limit (Go's
  `x/net/dns/dnsmessage` uses 10). The limit ends every
  cycle by the 17th pointer at the latest, the label cycle
  above included: a cycle through a four byte label is
  turned away at its 17th pointer, after 16 passes. It also
  bounds the work one name costs. Finding a pointer's
  position and its target walks the message, so each jump
  costs time linear in the message length, and one name
  costs at most 17 such walks however its pointers chain.
- The expanded name, counted as if it were written in full
  (one length byte per label, the label bytes, and the final
  zero), stays within 255 bytes. Labels read after a jump
  count toward the same budget as labels read before it. A
  cycle through long labels spends the budget before the
  pointer limit: through a 63 byte label each pass spends 64
  bytes, so the fourth pass is turned away after 3 pointers.
- A step bound of 256 also falls at every item read. No
  reading reaches it: each label spends at least 2 bytes of
  the budget, so a reading takes at most 127 label steps, 16
  pointer steps and 1 final step, 144 in all. It is there so
  that the Lean definition recurses on a number that falls.

So a pointer walk always ends, with a name or with a
rejection: the backwards rule limits where a pointer may
aim, and the pointer limit and the 255 byte budget between
them end every walk that does not finish.

## Questions

A question is a name, then QTYPE (two bytes, big endian), then
QCLASS (two bytes, big endian). QTYPE and QCLASS are held as
the values of those two byte fields; this layer gives them no
meaning.

## Records

A resource record is a name, then TYPE (two bytes), CLASS
(two bytes), TTL (four bytes), RDLENGTH (two bytes), and
RDLENGTH bytes of data, all big endian. TYPE, CLASS, and TTL
are held as the values of their fields; this layer gives
them no meaning. In particular a TTL with its top bit set is
held as read, not as 0, which RFC 2181 section 8 asks of a
reader that uses the TTL. The data is held as opaque bytes:
this layer does not read names or anything else inside it,
even when the data holds bytes shaped like a name.

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
identifier in two bytes, QR, AA, TC, RD, RA, AD, and CD each 0
or 1, the opcode and the RCODE in four bits); each section count
fits two bytes; QTYPE, QCLASS, TYPE, and CLASS fit two bytes;
TTL fits four bytes; every record's data length fits two
bytes; every label of every expanded name holds 1 to 63
bytes; and every expanded name fits the 255 byte wire bound.

The round trip is about printed messages, which hold no
compression, so it never reads a pointer. These are not
proved, and the differential tests in `tests/` check them
instead:

- That a compressed message parses to the message with its
  names expanded. `Spec.reads_rfc_4_1_4` and
  `Spec.reads_pointer_mid_label` state it for one input each;
  no theorem states it in general.
- That the parser accepts every message these rules allow,
  and turns away every message they forbid. Apart from the
  header (`Spec.parseHeader_fields`, `Spec.rejects_z_bit`),
  the refusal theorems pin one input each.

A byte for byte round trip on compressed input is not
claimed either: a parsed message prints uncompressed, so its
printed form need not equal a compressed input.

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

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean`
and proved in `Proofs/SpecProofs.lean`. The two header
theorems hold for every input. The other refusal theorems
are single inputs, one for each named rejection case in the
test harness; the tests in `tests/` cover each rule on many
more inputs.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed message gives the message back, all four sections | `Spec.parse_print` |
| Parsing the printed form of a well formed question only message gives the message back | `Spec.parse_print_question_only` |
| The RFC 1035 section 4.1.4 example, a name that ends in a pointer, parses with the name expanded (one input) | `Spec.reads_rfc_4_1_4` |
| The header fields are read from the bits the table above names, AD and CD included, for every header whose Z bit is clear | `Spec.parseHeader_fields` |
| A message with the Z bit set is refused, whatever its other bytes | `Spec.rejects_z_bit` |
| A pointer that aims at its own position is refused | `Spec.rejects_pointer_self` |
| A pointer that aims forward is refused, on an input no other rule refuses (the first question's name points at the second's) | `Spec.rejects_pointer_forward` |
| A pointer whose target lies past the end of the message is refused | `Spec.rejects_pointer_past_end` |
| A pointer whose target byte is a reserved length form is refused (here a byte inside a label) | `Spec.rejects_pointer_onto_reserved_form` |
| A pointer into the middle of a label is read like any other target when the bytes there read as a name | `Spec.reads_pointer_mid_label` |
| A reserved length form in a record name is refused | `Spec.rejects_reserved_in_record` |
| A record data length that runs past the end of the message is refused | `Spec.rejects_data_past_end` |
| An expanded name over 255 bytes, reached by chaining pointers, is refused | `Spec.rejects_chain_over_255` |
| A pointer cycle that passes through a label is refused: the 16 pointer limit turns it away | `Spec.rejects_pointer_cycle_through_label` |
| A name that follows 16 pointers, the limit, is read | `Spec.accepts_sixteen_hops` |
| A name that follows 17 pointers is refused | `Spec.rejects_seventeen_hops` |
