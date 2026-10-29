# Planted bugs

Written by `python3 tests/planted_bugs.py`. Each planted bug is a small
change to the code under proof, made in a scratch copy of the project.
For each, the script lists the statements of `Spec.lean` that are false
for the changed code, and the failures `tests/run_tests.py` records
against the changed tool. Rerun it to check these rows.

- Single-input statements checked as written: 14
- Instances of the statements over every input: 12 (a false instance refutes its statement; a true one proves nothing)
- Each check is decided both ways with `decide +kernel`: the proposition and its negation, exactly one of which must go through.
- dnspython: judges ran

| Planted bug | What changes | Statements refuted | Test failures | Unnamed dnspython differences |
|---|---|---|---|---|
| baseline | the code as it is | none | 0 of 8235 | 0 |
| forward-pointers | a pointer may aim forward | `Spec.rejects_pointer_forward` | 274 of 8235 | 137 |
| no-hop-limit | no limit on the pointers a name follows | `Spec.rejects_seventeen_hops`, `Spec.rejects_seventeen_hops_through_labels` | 8 of 8235 | 4 |
| hops-15 | the limit is 15 pointers, not 16 | `Spec.accepts_sixteen_hops`, `Spec.accepts_sixteen_hops_through_labels` | 8 of 8235 | 4 |
| hops-reset-at-label | the pointer count starts again after each label | `Spec.rejects_seventeen_hops_through_labels` | 4 of 8235 | 2 |
| budget-reset-at-jump | the 255 byte budget starts again at each pointer | `Spec.rejects_chain_over_255` | 4 of 8235 | 2 |
| ad-cd-refused | AD and CD are refused, as Z is | `Spec.parse_print`, `Spec.parse_print_question_only`, `Spec.parse_reads_header`, `Spec.parseHeader_fields` | 2240 of 8235 | 890 |
| z-accepted | a set Z bit is not refused | `Spec.rejects_z_bit` | 4 of 8235 | 0 |
| ad-cd-swapped-in-parseHeader | AD and CD swapped in the header reader and in the printer | `Spec.parse_reads_header`, `Spec.parseHeader_fields` | 310 of 8235 | 5 |
| ad-cd-swapped-in-parse | AD and CD swapped by parse after the header reader, and in the printer | `Spec.parse_reads_header` | 310 of 8235 | 5 |
| answers-authorities-swapped | the answer and authority sections swapped in parse and in the printer | `Spec.parse_reads_header` | 573 of 8235 | 4 |
