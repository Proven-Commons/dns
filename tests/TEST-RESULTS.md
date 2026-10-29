# Test results

Written by `python3 tests/run_tests.py`, which builds the tool with
`lake build`, sends each input to it, and compares each answer with
the strict oracle's. Rerun it to check these numbers.

- Oracle: the strict reading of SPEC.md in tests/run_tests.py, on Python 3.13.17; cross-checked against dnspython 2.9.1, counted apart
- Seed: 20261026
- Inputs: 8211
- Failures: 0
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)

Inputs by section, with the answers that agree with the oracle:

  - Slice 1 fixed cases: 22 of 22
  - Slice 1 random well formed messages: 400 of 400
  - Slice 1 mutations (every truncation, every single byte flip, targeted): 66 of 66
  - Full fixed cases, parse: 8 of 8
  - Full fixed cases, sections: 8 of 8
  - Full rejections (parse and sections): 22 of 22
  - Random whole messages, parse: 300 of 300
  - Random whole messages, sections: 300 of 300
  - Compressed random and suffix messages, parse: 302 of 302
  - Compressed random and suffix messages, sections: 302 of 302
  - Mutations of the compressed messages at their pointers, parse: 6464 of 6464
  - Malformed requests, answered error: 17 of 17

In all, 8211 of 8211 answers agree.

Pointers:

  - Compressed messages holding a pointer: 259 of 302, 808 pointers in all
  - Inputs whose reading follows at least one pointer: 5194 of 8211

## Cross-check against dnspython

The oracle above is written in this project, from SPEC.md. dnspython,
written apart from it, judges the tool's answers where it can be
imported (`pip install dnspython`). Its checks are counted apart, not
in Inputs, so a run with or without it records the same Inputs.

- The name judge reads each `parse` input with dnspython's own wire
  parser and name reader, `dns.wirebase.Parser` and
  `dns.name.from_wire_parser`, in the message layout of RFC 1035
  section 4.1 written in the harness, with record data held opaque, as
  this layer holds it. Its answer is dnspython's reading, printed as
  the tool prints, or `none` when dnspython raises.
- The message judge reads the fixed and rejection cases with
  `dns.message.from_wire`, which also reads record data by type. It
  compares the identifier, the flags, the questions, and each record's
  name, type, class and TTL. It runs on those cases only, since that
  reader also refuses record data that is not well formed for its
  type, and handles OPT and TSIG records and the UPDATE opcode by
  their own rules, none of which this layer reads.

A disagreement is a named difference when the strict oracle, with the
named rules changed to read as dnspython reads, gives dnspython's
answer. Any other disagreement is a failure, counted above.

- Name judge: dnspython's wire parser and name reader on every `parse` input: 7571 judged, 7562 agree, 9 named differences, 0 unnamed
- Message judge: `dns.message.from_wire` on the fixed and rejection cases: 39 judged, 36 agree, 3 named differences, 0 unnamed
- Named differences: pointer-segment: 7 inputs; ttl-top-bit: 1 input; z-bit: 4 inputs

The named rules:

  - pointer-segment: dnspython follows a pointer only when its target lies before the start of the name part that holds the pointer (the name's start, or the previous target), and reads nothing at or after that start; this parser asks only that the target lie before the pointer, so it reads a pointer into the name being read (SPEC.md, Names and compression).
  - ttl-top-bit: dnspython's message reader reads a TTL with its top bit set as 0, as RFC 2181 section 8 asks of a TTL above 2^31 - 1; this layer holds the four byte TTL field as read and gives it no meaning (SPEC.md, Records).
  - z-bit: dnspython keeps the Z bit (0x40 of the fourth byte); this parser refuses a message with Z set, the one reserved flag bit (SPEC.md, The header).
