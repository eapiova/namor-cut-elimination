# NAMOR — New Agda MOdal Realization

Cubical Agda formalization of cut elimination for position-based modal sequent calculi, uniformly capturing eight normal modal logics from K to S5.

## Browsable Source

The HTML documentation is hosted at: https://eapiova.github.io/namor-cut-elimination

## Contents

- **Syntax & System**: Formula types, position-based sequents, inference rules parameterized by logic
- **Cut Elimination**: Mix lemma (82 cases), cut elimination theorem, consistency, subformula property
- **Completeness**: Weak completeness w.r.t. Hilbert axiomatizations
- **Solvers**: Verified subset solver and semilattice solver for automation

## Building

Requires Agda 2.8.0 and [agda/cubical](https://github.com/agda/cubical) v0.9.

```bash
agda NAMORIndex.agda
```

## Companion Paper

R. Borsetto. *NAMOR: Cut Elimination for Position-Based Modal Sequents in Cubical Agda*. Preprint, 2026.

A short presentation of the NAMOR library appears in:
R. Borsetto, M. Zorzi. *NAMOR: a New Agda Library for Modal Extended Sequents*. OVERLAY 2025, CEUR Workshop Proceedings, Vol. 4142. <https://ceur-ws.org/Vol-4142/paper4.pdf>
