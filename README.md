# ThetaFunctions

A Lean 4 / Mathlib formalization of multivariate theta functions, Epstein zeta functions, the
Siegel modular group, and the rank-`g` Poisson summation formula that connects them.

## Overview

The project builds up, from Mathlib's scalar Gaussian/Fourier-analysis API, the analytic machinery
behind the classical theory of Siegel modular forms:

* general (axiomatized) convergence criteria for lattice sums of a quadratic form's negative power
  (Epstein zeta) or exponential (theta functions),
* the genus-`g` Riemann theta function and its quasi-periodicity under shifting the argument by a
  period,
* the symplectic group `Sp(2g, R)` and its fractional-linear action on the Siegel upper
  half-space,
* the rank-`g` Poisson summation formula for a Gaussian — the one genuinely new piece of analysis
  this project contributes beyond what Mathlib has (Mathlib's Poisson summation is rank-1/scalar
  only).

## Contents

Files under `ZetaThetaFunctions/`, roughly in dependency order:

| File | Contents |
| --- | --- |
| `EpsteinZeta.lean` | `ZetaAbleQuadraticForm`, the axiomatic convergence package for lattice-sum zeta functions, and its instantiation `epsteinZetaAble` for a positive-definite integral quadratic form — the Epstein zeta function `ζ_q(s) = ∑'_{x≠0} (q x)^(-s)`. |
| `ThetaFunctions.lean` | `ThetaAbleQuadraticForm` (the theta-function analogue of `ZetaAbleQuadraticForm`), the genus-`n` Riemann theta function `RiemannThetaAble` and its quasi-periodicity (`tau_periodicity`), the classical Jacobi theta function as a special case, and the Mellin-transform link back to `EpsteinZeta.lean`. |
| `Sp2gR.lean` | The symplectic group `Sp(2g, R)` in the abstract: block decomposition, multiplication formulas, symplectic relations, and generators (`Tmatrix`, `GLmatrix`). No dependence on theta functions or the upper half-space. |
| `SiegelUpperHalfSpace.lean` | The bundled Siegel upper half-space `SiegelUpperHalfSpace g`, and the correspondence between symmetric matrices and real quadratic forms on `EuclideanSpace ℝ (Fin g)` (`quadraticMapOfMatrix`). |
| `SiegelModular.lean` | The fractional-linear `MulAction` of `Sp2gR (R := R) g` on `SiegelUpperHalfSpace g`, `τ ↦ (Aτ+B)(Cτ+D)⁻¹`, and the proofs that it's well-defined (preserves symmetry, positive-definiteness, invertibility of `Cτ+D`). |
| `SchurPivot.lean` | Pure matrix algebra shared by the two files below: `schurStepLast`/`pivotSqrt`, a branch-safe replacement for `(det A)^(1/2)` built from repeated one-coordinate Schur complementation (needed since the naive `Complex.cpow` branch is provably wrong for `g ≥ 3`). |
| `GaussianFourierTransform.lean` | Pure continuous analysis: the Gaussian `modulatedGaussian` on `EuclideanSpace ℝ (Fin g)`, its integrability, its Bochner Fourier transform `modulatedGaussian_fourierTransform` (proved by induction via `SchurPivot.lean`), and the `modulatedGaussianCenter` reparametrization plus the theorem that it peaks exactly at `center`. Knows nothing about lattices. |
| `PoissonSummation.lean` | The bridge file: the discrete lattice-sum identity `tsum_exp_neg_quadratic_matrix` (proved independently, by the same Schur-complement induction), and `modulatedGaussian_hasPoissonSummation`, combining it with `GaussianFourierTransform.lean`'s continuous side into the full rank-`g` Poisson summation formula. |

## Building

Requires [`elan`](https://github.com/leanprover/elan). From the project root:

```sh
lake build
```

This builds every file listed above.
