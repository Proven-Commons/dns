/-
  Axiom check for the headline theorem. Building this file prints
  the axioms the proof depends on. The expected output is only
  the three standard Lean axioms: `propext`, `Classical.choice`,
  `Quot.sound`, or a subset of them. Any other name here breaks
  the verified bar.
-/

import Dns.Proofs.RoundTrip

#print axioms Dns.Proofs.parse_print
