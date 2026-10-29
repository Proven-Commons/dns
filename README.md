# dns: a DNS wire format parser and printer, with a proved round trip

Status: in progress

A parser and printer for a whole DNS message, in Lean,
following RFC 1035 sections 3, 4.1, and 4.1.4. The
definitions are in `Dns/Value.lean` (the data model and the
printer) and `Dns/Parse.lean` (the parser). The rules are
written out in `SPEC.md`.

The first slice read the header and the question section
only. This slice adds the answer, authority, and additional
sections of resource records, and it reads name compression:
a compressed name is expanded while reading. Names in the
model are always expanded, and the printer never writes
compression.

The statements a reviewer approves are in `Spec.lean`,
with the definitions they use in `Spec/Defs.lean` and
their proofs in `Proofs/SpecProofs.lean`. No reviewer
has approved them yet, so this project is not called
verified.

## How to run it

`lake build` builds the library, the proofs, and the
command line tool. The tool reads one request per line: an
operation word, a space, and the message as comma-separated
decimal byte codes. It answers `ok:` and the byte codes of
the canonical reprint when the message parses, `none` when
the message is turned away, and `error` when the request
itself is malformed.

```
lake build
printf 'parse 0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,1\n' | .lake/build/bin/dns
```

That request is a query with the root name, QTYPE 1, and
QCLASS 1, and the answer is `ok:` with the same codes back.
A `sections` request with the same bytes answers `ok:` with
the codes of the summary text SPEC.md defines. A message
the parser turns away, such as the single code `0`, answers
`none`. See `SPEC.md` for the full protocol.

`python3 tests/run_tests.py` rebuilds the tool, runs the
fixed cases, the differential run against the harness
oracle, the mutation and whole message runs, the
compression runs and the mutations at each pointer, and the
rejection and malformed cases, and writes the outcome to
`tests/TEST-RESULTS.md`. When the Python dnspython module
can be imported (`pip install dnspython`), dnspython also
judges the answers, and the results file lists every
difference from it, each explained by a named rule; a
difference no named rule explains is a failure.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back, all four sections. | `Spec.parse_print` |
| The first slice's question-only case of that claim: a well formed header and well formed questions, with the other three sections empty. | `Spec.parse_print_question_only` |
| Every message the parser accepts has the header its first twelve bytes give, each field from the bits RFC 1035 section 4.1.1 and RFC 6895 section 2 give it (AD from 0x20 and CD from 0x10 of the fourth byte), and as many entries in each section as that section's count says. | `Spec.parse_reads_header` |
| The header reader that the parser calls first accepts every twelve header bytes whose Z bit (0x40 of the fourth byte) is clear, and reads the fields from the same bits: AD and CD are read into the header, not turned away. | `Spec.parseHeader_fields` |
| A message with the Z bit set is refused, whatever its other bytes. | `Spec.rejects_z_bit` |
| The RFC 1035 section 4.1.4 example parses, its second name, the label FOO and a pointer, expanded to FOO.F.ISI.ARPA. This is one input; no theorem says every compressed message reads to its expanded form (see below). | `Spec.reads_rfc_4_1_4` |
| A pointer that aims at its own position is refused: a target must be strictly earlier than the pointer. | `Spec.rejects_pointer_self` |
| A pointer that aims forward, at a name later in the message, is refused, on an input where no other rule refuses it: the first question's name points at the second's. | `Spec.rejects_pointer_forward` |
| A pointer whose target lies past the end of the message is refused. | `Spec.rejects_pointer_past_end` |
| A pointer whose target byte is a reserved length form is refused: here it lands inside a label, on the byte 0x62. | `Spec.rejects_pointer_onto_reserved_form` |
| A pointer into the middle of a label is read like any other target when the bytes there read as a name: here the second name reads as x. | `Spec.reads_pointer_mid_label` |
| A reserved length form in a record name is refused: a length byte with exactly one top bit set. | `Spec.rejects_reserved_in_record` |
| A record whose data length runs past the end of the message is refused. | `Spec.rejects_data_past_end` |
| An expanded name over 255 bytes, reached by chaining pointers, is refused. | `Spec.rejects_chain_over_255` |
| A pointer cycle that passes through a label is refused: the 16 pointer limit turns it away. | `Spec.rejects_pointer_cycle_through_label` |
| A name that follows 16 pointers, the limit, is read. | `Spec.accepts_sixteen_hops` |
| A name that follows 17 pointers is refused. | `Spec.rejects_seventeen_hops` |

A message is well formed when its header fields fit their
widths (the identifier in two bytes, QR, AA, TC, RD, RA, AD,
and CD each 0 or 1, the opcode and the RCODE in four bits), each
section count fits two bytes, QTYPE, QCLASS, TYPE, and CLASS
fit two bytes, TTL fits four bytes, each record's data
length fits two bytes, every label of every expanded name
holds 1 to 63 bytes, and every expanded name fits the 255
byte wire bound. The full list is in `SPEC.md`, and the
definition, `Spec.WF`, in `Spec/Defs.lean`.

The round trip theorems rest on the proofs in
`Proofs/RoundTrip.lean`, where they are
`Dns.Proofs.parse_print` and
`Dns.Proofs.parse_print_question_only`. Both check against
the standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), which a reader can confirm with
`#print axioms`, or by running
`lake env lean Proofs/Verify.lean`, which prints the axiom
list for the headline theorem. The three header theorems
hold for every input. The other theorems, refusals and
readings, are about one input each, checked in the kernel
with `decide +kernel`.
Under the round trips, the steps are proved one by one in
the same file: the two and four byte numbers both ways, the
name reader on printed names, questions and records on
their printed forms, and the header both ways.

The command line tool in `Main.lean` calls `Dns.parse`
and `Dns.print` directly, the same functions the theorems
are about.

## What is not proved

- That the parser accepts every message the rules in
  `SPEC.md` allow, and turns away every message they
  forbid. The round trips do not need either. Apart from
  the header, where `Spec.parse_reads_header`,
  `Spec.parseHeader_fields` and `Spec.rejects_z_bit`
  cover every input, the refusal theorems pin single
  inputs only, so neither holds in general as a proof.
  The differential tests in `tests/` check that
  behaviour instead, and the results
  file records the outcome, including any failure.
- That a compressed message parses to the message with
  its names expanded. The round trips cover printed
  messages, which hold no pointer, so they never read
  one. `Spec.reads_rfc_4_1_4` and
  `Spec.reads_pointer_mid_label` state it for one input
  each; the differential tests check it on many more,
  and the results file counts how many of them hold a
  pointer.
- A byte for byte round trip on compressed input. A
  parsed message prints uncompressed, so its printed form
  need not equal a compressed input. No such claim is
  made.
- Anything inside record data. Record data is opaque bytes
  at this layer; names that appear inside it, in record
  types that carry them, are not read or expanded.
- Writing compressed names. The printer writes every name
  in full.
- Text form names. This layer works on wire bytes only; the
  dotted form is neither read nor printed.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the decimal parser, the summary text.
  The tests cover them, malformed requests included. The
  summary shows each header flag by name, so the tests
  see the flags as read, not only as reprinted.
- Speed. The code works on lists of bytes, which suits
  proofs, not large data. Each pointer jump walks the
  message, and one name follows at most 16 pointers, so a
  name costs at most 17 walks of the message; no theorem
  states a cost.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, with the C compiler and linker
  shipped with it, which turns the proved definitions into
  the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies
  to trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it puts
  in place of some definitions the proofs reason about.
- The operating system the program runs on.
- That `SPEC.md` states the reading of RFC 1035 you
  intend. The proofs are about the parser and printer in
  this repo following each other exactly; the fidelity of
  the spec to the RFC is a reading, pinned in `SPEC.md`
  where the RFC leaves a choice open.
- The strict Python oracle in `tests/run_tests.py`,
  written from `SPEC.md`, and the Python dnspython module
  in the judges it runs when the module is present. Both
  are evidence, not proof. The results file names the
  dnspython version that judged the run, or says that
  none did, and lists the named differences from it: the
  Z bit, a pointer into the name being read, and a TTL
  with its top bit set.
- The line handling in `Main.lean` (splitting a request
  line, reading decimal codes, the summary text). The
  tests drive it, and no proof covers it.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the
   differential against the harness oracle, the mutation
   and whole message runs, the compression runs and the
   mutations at each pointer, and the rejection and
   malformed cases, with counts and any
   failures written to `tests/TEST-RESULTS.md`. When
   dnspython can be imported, its name reader judges the
   tool's `parse` answer for every input, and its message
   reader the tool's `sections` answer for each fixed
   case, and the results file lists the named
   differences; it says so when dnspython is absent.
3. `lake build`: the library, the proofs, and the tool
   build clean, and `lake env lean Proofs/Verify.lean`
   prints the axiom list for the headline round trip
   theorem.
4. Read `SPEC.md` against RFC 1035 and check the pinned
   readings are the ones you want.
