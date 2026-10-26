# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: a strict reading of the plan rules written in the harness (Python 3.12.3), plus hand-built fixed cases from RFC 1035
- dnspython: not present in this environment, no cross check run
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Fixed cases: 18 of 18 agreements
- Random well formed messages: 400 of 400 agreements
- Mutations (every truncation, every single byte flip, targeted): 64 of 64 agreements
- Malformed requests answered error: 12 of 12
- dnspython cross checks: 0 run (module absent)
- Differential inputs: 482
- Differential agreements: 482
- Named differences: none
- Failures: 0
