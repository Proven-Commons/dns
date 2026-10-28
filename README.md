# dns: a DNS wire format parser and printer, with a proved round trip

A parser and printer for the header and question section of a
DNS message, in Lean, following RFC 1035 sections 3 and 4. The
definitions are in `Dns/Value.lean` (the data model and the
printer) and `Dns/Parse.lean` (the parser). The proof is in
`Dns/Proofs/RoundTrip.lean`. This slice reads no resource records
and no name compression.

## What is proved

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back. | `Dns.Proofs.parse_print` |

A message is well formed when its header fields fit their
widths (the identifier in two bytes, QR, AA, TC, RD, and RA
each 0 or 1, the opcode and the RCODE in four bits), its
question count fits two bytes, every QTYPE and QCLASS fits two
bytes, every label holds 1 to 63 bytes, and every name fits
the 255 byte wire bound. `parse_print` checks against the
standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), which a reader can confirm with
`#print axioms Dns.Proofs.parse_print`.

The command-line tool in `Main.lean` calls these functions
directly.

## What is not proved

- That the parser accepts every message the rules in `SPEC.md`
  allow, and turns away every message they forbid. The round
  trip does not need either, so neither is proved. The
  differential tests in `tests/` check that behaviour instead,
  and the results file records the outcome, including any
  failure.
- Anything about the answer, authority, or additional
  sections, and anything about resource records. This slice
  turns a message away when any of those counts is nonzero.
- Name compression. A length byte with a top bit set, pointer
  or reserved form, turns the message away.
- Text form names. This layer works on wire bytes only; the
  dotted form is neither read nor printed.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the decimal parser. The tests cover them,
  malformed requests included.
- Speed. The code works on lists of bytes, which suits proofs,
  not large data.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped
  with it, and the runtime, which turn the proved definitions
  into the program that runs.
- Lean's core library, including the compiled code it puts in
  place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The strict Python reading of the rules in `SPEC.md`, written
  in the test harness, as the oracle in the differential tests.
  The Python `dnspython` module was not present in the build
  environment, so no cross check against it was run; the
  results file says so.

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
message the parser turns away, such as the single code `0`,
answers `none`. A malformed request answers `error`. See
`SPEC.md` for the full protocol.

## Re-check it

```
lake build
python3 tests/run_tests.py
```

The test run rebuilds the tool, runs the fixed cases and the
differential run, and rewrites `tests/TEST-RESULTS.md`. The
numbers in that file are the record of the run described
there.
