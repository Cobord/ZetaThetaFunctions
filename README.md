# ThetaFunctions

A Lean 4 / Mathlib formalization of multivariate theta functions, multivariate zeta functions, the
Siegel modular group, and the rank-`g` Poisson summation formula that connects them.

## Overview

The project builds up, from Mathlib's scalar Gaussian/Fourier-analysis API, the analytic machinery
behind the classical theory of Siegel modular forms:

* general (axiomatized) convergence criteria for lattice sums of a quadratic form's negative power
  (quadratic form zeta) or exponential (theta functions),
* the genus-`g` Riemann theta function and its quasi-periodicity under shifting the argument by a
  period,
* the symplectic group `Sp(2g, R)` and its fractional-linear action on the Siegel upper
  half-space,
* the rank-`g` Poisson summation formula for a Gaussian — the one genuinely new piece of analysis
  this project contributes beyond what Mathlib has (Mathlib's Poisson summation is rank-1/scalar
  only),
* the full Siegel modular transformation law for the genus-`g` Riemann theta function under each
  generator of `Sp(2g, ℤ)` (`T`, `GL`, `S`), with `theta_fun` on both sides of the identity.

## Contents

Files under `ZetaThetaFunctions/`, roughly in dependency order:

| File | Contents |
| --- | --- |
| `GeneralUtils.lean` | Base-level linear-map helpers with no project-specific dependencies: `intCastLinearMap`, `ofRealLinear`, `mulILinear` — the `R`-linear casts (`ℤ → ℂ`, `ℝ → ℂ`, `·*I`) used throughout to build shift/quadratic-form data. |
| `Sp2gR.lean` | The symplectic group `Sp(2g, R)` in the abstract: block decomposition, multiplication formulas, symplectic relations, and generators (`Tmatrix`, `GLmatrix`, `Smatrix`). No dependence on theta functions or the upper half-space. |
| `SchurPivot.lean` | Pure matrix algebra shared by `GaussianFourierTransform.lean`/`PoissonSummation.lean`: `schurStepLast`/`pivotSqrt`, a branch-safe replacement for `(det A)^(1/2)` built from repeated one-coordinate Schur complementation (needed since the naive `Complex.cpow` branch is provably wrong for `g ≥ 3`). |
| `LatticeUtils.lean` | The canonical embedding `latticeEmbedding : (ι → ℤ) →+ EuclideanSpace ℝ ι` of a lattice into Euclidean space (with the `Fin n`-specialized shorthand `toEuclidean_ZnRn`), `latticeNormSq`, the standard lattice submodule `stdLattice`, and the `zCoord`/`ellCoord` shift-coordinate helpers. Shared, lattice-only infrastructure with no dependence on zeta/theta-specific constructions. |
| `QuadraticFormUtils.lean` | The Gram-matrix machinery connecting lattice quadratic forms to matrices and back: `latticeGramMatrix`/`gramMatrix`/`gramMatrixR` (`ℤⁿ`-domain), `gramMatrixReal`/`quadraticMapOfMatrix` (`EuclideanSpace`-domain, mutually inverse on symmetric matrices), and the positive-definiteness transfer (`posDefR`, `exists_real_posDef_quadraticMap`) extending an integral quadratic form to a continuous one on `EuclideanSpace ℝ (Fin n)`. |
| `QuadraticFormZeta.lean` | `ZetaAbleQuadraticForm`, the axiomatic convergence package for lattice-sum zeta functions, and its instantiation `quadraticFormZetaAble` for a positive-definite integral quadratic form — the zeta function `ζ_q(s) = ∑'_{x≠0} (q x)^(-s)`. |
| `ThetaFunctions.lean` | `ThetaAbleQuadraticForm` (the theta-function analogue of `ZetaAbleQuadraticForm`), the genus-`n` Riemann theta function `RiemannThetaAble` and its quasi-periodicity (`tau_periodicity`), the classical Jacobi theta function as a special case, and the Mellin-transform link back to `QuadraticFormZeta.lean`. |
| `SiegelUpperHalfSpace.lean` | The bundled Siegel upper half-space `SiegelUpperHalfSpace g`, and the correspondence between symmetric matrices and real quadratic forms on `EuclideanSpace ℝ (Fin g)` (`quadraticMapOfMatrix`, `τ.toMatrix`, `complex_quadratic`). |
| `GaussianFourierTransform.lean` | Pure continuous analysis: the Gaussian `modulatedGaussian` on `EuclideanSpace ℝ (Fin g)`, its integrability, its Bochner Fourier transform `modulatedGaussian_fourierTransform` (proved by induction via `SchurPivot.lean`), and the `modulatedGaussianCenter` reparametrization plus the theorem that it peaks exactly at `center`. Knows nothing about lattices. |
| `PoissonSummation.lean` | The bridge file: the discrete lattice-sum identity `tsum_exp_neg_quadratic_matrix` (proved independently, by the same Schur-complement induction), and `modulatedGaussian_hasPoissonSummation`, combining it with `GaussianFourierTransform.lean`'s continuous side into the full rank-`g` Poisson summation formula. |
| `SiegelModular.lean` | The fractional-linear `MulAction` of `Sp2gR (R := R) g` on `SiegelUpperHalfSpace g`, `τ ↦ (Aτ+B)(Cτ+D)⁻¹`, and its induced action on Riemann theta data. Proves the full Siegel modular theta transformation law under each generator of `Sp(2g, ℤ)`: `theta_fun_after_Tmatrix_diagEven` and `theta_fun_after_GLmatrix_reindex` (termwise identities), and `theta_fun_after_Smatrix` (genuine Poisson resummation, via `PoissonSummation.lean`) — each stating `theta_fun` on both sides of the transformation law. |

## Building

Requires [`elan`](https://github.com/leanprover/elan). From the project root:

```sh
lake build
```

This builds every file listed above.
