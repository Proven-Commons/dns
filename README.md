# dns: a DNS wire format parser and printer, with a proved round trip

A parser and printer for a whole DNS message, in Lean,
following RFC 1035 sections 3, 4.1, and 4.1.4. The
definitions are in `Dns/Value.lean` (the data model and the
printer) and `Dns/Parse.lean` (the parser). The proof is in
`Proofs/RoundTrip.lean`.

The first slice read the header and the question section
only. This slice adds the answer, authority, and additional
sections of resource records, and it reads name compression:
a compressed name is expanded while reading. Names in the
model are always expanded, and the printer never writes
compression.

## What is proved

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back, all four sections. | `Dns.Proofs.parse_print` |
| The first slice's question-only case of that claim. | `Dns.Proofs.parse_print_question_only` |

A message is well formed when its header fields fit their
widths (the identifier in two bytes, QR, AA, TC, RD, and RA
each 0 or 1, the opcode and the RCODE in four bits), each
section count fits two bytes, QTYPE, QCLASS, TYPE, and CLASS
fit two bytes, TTL fits four bytes, each record's data
length fits two bytes, every label of every expanded name
holds 1 to 63 bytes, and every expanded name fits the 255
byte wire bound. Both theorems check against the standard
axioms only (`propext`, `Classical.choice`, `Quot.sound`),
which a reader can confirm with
`#print axioms Dns.Proofs.parse_print`.

The round trip is at the level of the message value.
Parsing a compressed message yields the expanded message,
whose printing is the uncompressed form, so the printed
form of a parsed message need not equal a compressed input
byte for byte.

The command-line tool in `Main.lean` calls these functions
directly.

## What is not proved

- That the parser accepts every message the rules in
  `SPEC.md` allow, and turns away every message they forbid.
  The round trip does not need either, so neither is proved.
  The differential tests in `tests/` check that behaviour
  instead, and the results file records the outcome,
  including any failure.
- Anything inside record data. Record data is opaque bytes
  at this layer; names that appear inside it, in record
  types that carry them, are not read or expanded.
- Writing compressed names. The printer writes every name
  in full.
- Text form names. This layer works on wire bytes only; the
  dotted form is neither read nor printed.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the decimal parser, the summary text.
  The tests cover them, malformed requests included.
- Speed. The code works on lists of bytes, which suits
  proofs, not large data.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped
  with it, and the runtime, which turn the proved definitions
  into the program that runs.
- Lean's core library, including the compiled code it puts
  in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The strict Python reading of the rules in `SPEC.md`,
  written in the test harness, as the oracle in the
  differential tests. The Python `dnspython` module was not
  present in the build environment, so no cross check
  against it was run; the harness runs one when the module
  is present, and the results file says which happened.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan).
Build, then feed request lines to the tool:

```
lake build
printf 'parse 0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,1\n' | .lake/build/bin/dns
```

That request is a query with the root name, QTYPE 1, and
QCLASS 1, and the answer is `ok:` with the same codes back. A
`sections` request with the same bytes answers `ok:` with
the codes of the summary text SPEC.md defines. A message
the parser turns away, such as the single code `0`, answers
`none`. A malformed request answers `error`. See `SPEC.md`
for the full protocol.

## Re-check it

```
lake build
python3 tests/run_tests.py
```

The test run rebuilds the tool, runs the fixed cases and
the differential runs, and rewrites `tests/TEST-RESULTS.md`.
The numbers in that file are the record of the run described
there.
