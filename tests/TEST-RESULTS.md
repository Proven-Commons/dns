# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: a strict reading of the plan rules written in the harness (Python 3.12.3), plus hand-built fixed cases from RFC 1035
- dnspython: not present in this environment, no cross check run
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Slice 1 fixed cases: 22 of 22 agreements
- Slice 1 random well formed messages: 400 of 400 agreements
- Slice 1 mutations (every truncation, every single byte flip, targeted): 66 of 66 agreements
- Full fixed cases, parse: 8 of 8 agreements
- Full fixed cases, sections: 8 of 8 agreements
- Full rejections (parse and sections): 22 of 22 agreements
- Random whole messages, parse: 300 of 300 agreements
- Random whole messages, sections: 300 of 300 agreements
- Compressed random and suffix messages, parse: 302 of 302 agreements
- Compressed random and suffix messages, sections: 302 of 302 agreements
- Malformed requests answered error: 17 of 17
- dnspython cross checks: 0 run (module absent)
- Differential inputs: 1730
- Differential agreements: 1730
- Named differences: none
- Failures: 0
