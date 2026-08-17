# Lean formalization of the Imbalance Conjecture

This repository accompanies *A Proof of the Imbalance Conjecture* by James Alexander Schreib and Yousof Yavari. It contains a machine-checked Lean 4 proof that, for every finite simple graph whose adjacent vertices have different degrees, the multiset

$$
\left(\lvert d_G(u)-d_G(v)\rvert\right)_{uv\in E(G)}
$$

is the degree multiset of a finite simple graph.

`ImbalanceConjecture.lean` formalizes the capacity bound, the parity argument, the reduction to Erdős–Gallai, and a self-contained proof of the sufficiency direction of the Erdős–Gallai theorem. The final result is `Imbalance.imbalanceConjecture`. `VerificationAudit.lean` checks the axioms used by the principal results.

## Verification

The project pins Lean 4.30.0 and mathlib v4.30.0. With [elan](https://github.com/leanprover/elan) and Git installed, run:

```sh
git clone https://github.com/jamesschreib/imbalance-conjecture.git
cd imbalance-conjecture
lake build
```

A successful build checks both the formalization and the axiom audit. GitHub Actions runs the same verification on pushes and pull requests. The source contains no `sorry` or `admit` placeholders.

## License and citation

The formalization is released under the Apache License 2.0. Citation metadata is provided in `CITATION.cff`.
