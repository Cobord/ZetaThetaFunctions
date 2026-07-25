import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.ContinuousMap.Periodic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.LinearAlgebra.Matrix.Integer
import ZetaThetaFunctions.QuadraticFormZeta

/-!
# Theta Functions

This file constructs multivariate theta functions `θ(z) = ∑' x : M, exp (π I Q(x) + 2π I ⟪z, x⟫)`
for a complex quadratic form `Q = qRe + I qIm` (an analogue of a Siegel upper half-space point) and
a linear shift `z`, and connects the resulting Gaussian sums to the zeta function of
`QuadraticFormZeta.lean` via a Mellin transform.

## Sections

### `Periodicity`
`HasSum.periodic_of_addMonoidHom`: a genuine (`HasSum`, not merely `tsum`) sum of translates of a
continuous map is itself invariant under those translations.

### `GeneralThetaAble`
`ThetaAbleQuadraticForm`, the theta-function analogue of `QuadraticFormZeta.lean`'s `ZetaAbleQuadraticForm`:
packages convergence of `∑' x, exp (π I Q x + 2π I ⟪z, x⟫)`, for *every* shift `z` (no half-plane
restriction, since the quadratic term always dominates), as the existence of a summable comparison
function eventually bounding the summand. Defines `theta_fun`, its unconditional summability
(`theta_fun_summable`), and the theta constant `theta_const = theta_fun 0`.

### `TauPeriodic`
The quasi-periodicity of `theta_fun` under shifting `z` by one full period of the modulus `Q`
(`tau_operator`, built from `Q.polarBilin`): `theta_fun (z + period) = cocycle * theta_fun z`
(`tau_periodicity`), the defining transformation law of a theta function.

### `GaussianTheta`
Real-variable estimates for Gaussian bump functions on `EuclideanSpace ℝ (Fin n)`: transferring
positive-definiteness to a lower bound on the exponent (`bound_gaussian_exponent`, via
`QuadraticFormUtils.lean`'s `posDef_lower_bound`), and showing a Gaussian eventually beats any negative power of
the (recentred) radius (`gaussianVPolyDecay`), the estimate driving summability of lattice Gaussian
sums.

### `RiemannThetaAble`
`RiemannThetaAble`: the `ThetaAbleQuadraticForm` instance for the lattice `Fin n → ℤ`, for any pair
`(qRe, qIm)` of real quadratic forms on `EuclideanSpace ℝ (Fin n)` with `qIm` positive definite —
i.e. the general multivariate Riemann theta function. Convergence is obtained by completing the
square (`reExponent_le`, via `muOfShift`) to reduce the shifted sum to the unshifted Gaussian decay
estimates of `GaussianTheta`.

### `JacobiTheta`
`jacobiThetaAble`: the classical one-dimensional Jacobi theta function `θ(z; τ)`, as the
`n = 1`, `q = x²` special case of `RiemannThetaAble`, for `τ` in the upper half-plane.

### `SliceGaussianTheta`
`sliceGaussianThetaAble`: the one-complex-parameter scalar slice `Q = τ • q` of
`RiemannThetaAble` through a *fixed* positive-definite integral form `q` (from `QuadraticFormZeta.lean`),
generalizing `jacobiThetaAble` to any `q`. This is the theta function needed to relate `q`'s
zeta function to a Gaussian sum via Mellin transform.

### `ThetaZetaMellin`
The Mellin transform connecting the zeta function `ζ_q(s)` (`QuadraticFormZeta.lean`'s `zeta_fun` for
`quadraticFormZetaAble`) to the theta sum `θ(0; itq)` of `sliceGaussianThetaAble` at purely imaginary
`τ = it`: `Γ(s) π⁻ˢ ζ_q(s) = ∫₀^∞ tˢ⁻¹ (θ(0; itq) - 1) dt` (`zeta_eq_theta_mellin'`), obtained from
Mathlib's `hasSum_mellin_pi_mul` (`Mathlib.NumberTheory.LSeries.MellinEqDirichlet`) applied to `q`
(`zeta_eq_theta_mellin`).
-/

open Function Set Complex Real
open TopologicalSpace Filter MeasureTheory Asymptotics
open scoped Real Filter FourierTransform TensorProduct
open ContinuousMap

section Periodicity

variable {G X Y : Type*} [AddCommGroup G]
  [TopologicalSpace X] [AddCommGroup X] [ContinuousAdd X]
  [TopologicalSpace Y] [AddCommMonoid Y] [ContinuousAdd Y] [T2Space Y]

/-- If the translates of `f` by `ι n`, `n : G`, genuinely sum (in the sense of `HasSum`, not
merely as a possibly-junk `tsum`) to some continuous map `S`, then `S` is invariant under
precomposition with translation by any `ι k` — i.e. `S` really is periodic with respect to the
image of `ι`, not "periodic" only because both sides would silently default to `0` if the family
failed to be summable. -/
theorem HasSum.periodic_of_addMonoidHom {f : C(X, Y)} {ι : G →+ X} {S : C(X, Y)}
    (h : HasSum (fun n : G => f.comp (ContinuousMap.addRight (ι n))) S) (k : G) :
    S.comp (ContinuousMap.addRight (ι k)) = S := by
  -- precomposing with the fixed continuous map `addRight (ι k)` is a continuous additive map
  -- `C(X, Y) →+ C(X, Y)`, so it commutes with `HasSum`.
  let φ : C(X, Y) →+ C(X, Y) :=
    { toFun := fun T => T.comp (ContinuousMap.addRight (ι k))
      map_zero' := by ext x; simp
      map_add' := by intro T1 T2; ext x; simp }
  have hφcont : Continuous φ := continuous_precomp _
  have h1 : HasSum (fun n : G => (f.comp (ContinuousMap.addRight (ι n))).comp
      (ContinuousMap.addRight (ι k))) (S.comp (ContinuousMap.addRight (ι k))) := h.map φ hφcont
  have hshift :
      HasSum (fun n : G => f.comp (ContinuousMap.addRight (ι ((Equiv.addRight k) n)))) S :=
    (Equiv.addRight k).hasSum_iff.mpr h
  have heq : ∀ n : G, (f.comp (ContinuousMap.addRight (ι n))).comp
      (ContinuousMap.addRight (ι k))
      = f.comp (ContinuousMap.addRight (ι ((Equiv.addRight k) n))) := by
    intro n
    ext x
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, Equiv.coe_addRight, map_add]
    abel_nf
  rw [funext heq] at h1
  exact h1.unique hshift

end Periodicity

section GeneralThetaAble

universe u

variable {R : Type u} [cr_R : CommSemiring R] [Module R ℝ]

/-- The data needed to define a multivariate theta function

`θ(z) = ∑' x : M, exp (π * I * (qRe x + I * qIm x) + 2 * π * I * ⟪z, x⟫)`

on an `R`-module `M`: a pair of real quadratic forms `qRe`, `qIm`, thought of as the real and
imaginary parts of a complex quadratic form `Q = qRe + I • qIm` (the multivariate analogue of a
point `τ` of the Siegel upper half space), against which a shift `z : M →ₗ[R] ℂ` (an element of
`Hom_R(M, ℂ)`, rather than the complexified dual `Mᵛ ⊗[R] ℂ` — this avoids needing `M` to be
finite free, which would be required to identify the two via `dualTensorHomEquiv`) is paired by
direct application. The classical Gaussian sum `∑' x, exp (-q x * t)`
for `q` positive definite and `t > 0` is the very degenerate special case `qRe = 0`, `qIm = t • q`,
`z = 0`.

As in `ZetaAbleQuadraticForm`, convergence is not assumed directly via positive-definiteness of
`qIm` but is instead packaged as the existence (for every shift `z`) of a summable comparison
function eventually (i.e. away from a finite, possibly `z`-dependent, set of exceptions —
unlike the zeta case, there is no need to exclude `x = 0` specifically, since the summand is
perfectly well-behaved there) bounding the norm of the summand. -/
class ThetaAbleQuadraticForm {M : Type u}
  [AddCommMonoid M] [Module R M] [Module R ℂ]
where
  qRe : QuadraticMap R M ℝ
  qIm : QuadraticMap R M ℝ
  to_compare_g (z : M →ₗ[R] ℂ) : M → ℝ
  to_compare_g_summable : ∀ z, Summable (to_compare_g z)
  comparison_eventual : ∀ (z : M →ₗ[R] ℂ),
    ∀ᶠ (i : M) in Filter.cofinite,
      ‖Complex.exp (↑Real.pi * Complex.I * ((qRe i : ℂ) + Complex.I * (qIm i : ℂ))
        + 2 * ↑Real.pi * Complex.I * (z i))‖ ≤ to_compare_g z i

namespace ThetaAbleQuadraticForm

variable {M : Type u} [AddCommMonoid M] [Module R M] [Module R ℂ] [IsScalarTower R ℝ ℂ]
variable [thetaable : ThetaAbleQuadraticForm (R := R) (M := M)]

/-- The theta function `θ(z) = ∑' x : M, exp (π * I * Q x + 2 * π * I * ⟪z, x⟫)`, where
`Q x = qRe x + I * qIm x` and `z : M →ₗ[R] ℂ` is paired against `x` by direct application. -/
noncomputable def theta_fun (z : M →ₗ[R] ℂ) : ℂ :=
  ∑' x : M, Complex.exp (↑Real.pi * Complex.I *
    ((thetaable.qRe x : ℂ) + Complex.I * (thetaable.qIm x : ℂ))
    + 2 * ↑Real.pi * Complex.I * (z x))

omit [IsScalarTower R ℝ ℂ] in
/-- The theta function's defining series converges for *every* shift `z`, with no restriction
analogous to `zeta_fun_summable`'s `s.re > s_bound`: the quadratic term `Q x` always dominates the
linear shift term `2 * π * I * ⟪z, x⟫` as `x → ∞`, exactly as in Mathlib's
`Complex.tsum_exp_neg_quadratic`, where the shift `b` is unrestricted and only `a` (the analogue of
`qIm`) needs a positivity hypothesis. -/
theorem theta_fun_summable (z : M →ₗ[R] ℂ) :
    Summable
      (β := M)
      (f := fun x : M => Complex.exp (↑Real.pi * Complex.I *
        ((thetaable.qRe x : ℂ) + Complex.I * (thetaable.qIm x : ℂ))
        + 2 * ↑Real.pi * Complex.I * (z x)))
    := by
  exact Summable.of_norm_bounded_eventually
    (g := thetaable.to_compare_g z)
    (hg := thetaable.to_compare_g_summable z) (h := thetaable.comparison_eventual z)

/-- The theta constant `θ(0) = ∑' x : M, exp (π * I * Q x)`, i.e. `theta_fun` evaluated at the
zero shift. -/
noncomputable def theta_const : ℂ := theta_fun (0 : M →ₗ[R] ℂ)

def HomMRC_inc : (M →ₗ[R] R) →ₗ[R] (M →ₗ[R] ℂ) :=
  LinearMap.llcomp R M R ℂ (LinearMap.toSpanSingleton R ℂ (1 : ℂ))

omit [IsScalarTower R ℝ ℂ] in
lemma one_periodicity (z : M →ₗ[R] ℂ): ∀ m : M →ₗ[R] R,
  (∀ l : M, ∃ n: ℕ, m l • (1:ℂ) = n) -> theta_fun z = theta_fun (z + HomMRC_inc m) := by
  intro m mx_pow
  repeat rw [theta_fun]
  congr 1
  ext x
  simp
  repeat rw [mul_add]
  rw [<-add_assoc]
  set lhs_pow := (↑π * I * ↑(thetaable.qRe x) + ↑π * I * (I * ↑(thetaable.qIm x)) + 2 * ↑π * I * z x)
  set rhs_pow2 := 2 * ↑π * I * m x • 1
  rw [exp_eq_exp_iff_exists_int]
  obtain ⟨n,hn⟩ := mx_pow x
  use -n
  simp only [HomMRC_inc]
  simp
  simp only [hn]
  ring

omit [IsScalarTower R ℝ ℂ] in
private lemma hbound_eq : ∀ i : M,
      ‖Complex.exp (↑π * I * ((thetaable.qRe i : ℂ) + I * (thetaable.qIm i : ℂ))
        + 2 * ↑π * I * ((0 : M →ₗ[R] ℂ) i))‖ = Real.exp (-(π : ℝ) * thetaable.qIm i) := by
  intro i
  rw [LinearMap.zero_apply, mul_zero, add_zero, Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  repeat rw [mul_zero, zero_sub, zero_mul, one_mul, mul_one]
  ring_nf
  have x_im_zero (x : ℝ) : (x: ℂ).im = 0 := by
    simp
  have x_i_im_x (x : ℝ) : (x * I : ℂ).im = x := by
    simp
  rw [x_im_zero, zero_mul]
  rw [neg_zero, zero_add, zero_mul, zero_sub]
  rw [Complex.add_im, mul_add]
  repeat rw [x_i_im_x]
  rw [mul_comm]
  rw [mul_comm I _]
  rw [x_i_im_x, x_im_zero]
  rw [mul_zero, add_zero]
  rw [mul_comm]

omit [IsScalarTower R ℝ ℂ] in
/-- `qIm` is positive definite provided every nonzero point has an infinite `ℕ`-orbit
`{n • y : n ∈ ℕ}` — weaker than requiring all of `M` to be torsion-free/cancellative, since it is
only demanded pointwise, only for the multiples that actually witness non-positive-definiteness. -/
theorem qIm_posdef
    (horb : ∀ y : M, y ≠ 0 → (Set.range (fun n : ℕ => n • y)).Infinite) :
    thetaable.qIm.PosDef := by
  intro x hx
  have comparison_eventual_0 := thetaable.comparison_eventual (0 : M →ₗ[R] ℂ)
  -- the norm of the summand at shift `0` collapses to a pure `qIm`-Gaussian: the `qRe` part and
  -- the (vanishing) shift term only contribute a phase, which has norm `1`.
  simp only [hbound_eq] at comparison_eventual_0
  -- `comparison_eventual_0 : ∀ᶠ i in cofinite, Real.exp (-π * qIm i) ≤ to_compare_g 0 i`
  by_contra hcon
  push Not at hcon
  -- `hx : x ≠ 0`, `hcon : thetaable.qIm x ≤ 0` — contradiction to come from `comparison_eventual_0`
  -- `qIm` scales quadratically along the `ℕ`-orbit of `x`
  have hqn : ∀ n : ℕ, thetaable.qIm (n • x) = (n : ℝ) ^ 2 * thetaable.qIm x := by
    intro n
    have h1 : (n • x : M) = (n : R) • x := (Nat.cast_smul_eq_nsmul R n x).symm
    rw [h1, thetaable.qIm.map_smul]
    have h2 : ((n : R) * (n : R)) • thetaable.qIm x = (n * n) • thetaable.qIm x := by
      rw [← Nat.cast_mul]
      exact Nat.cast_smul_eq_nsmul R (n * n) (thetaable.qIm x)
    rw [h2, nsmul_eq_mul]
    push_cast
    ring
  -- so every point on the orbit still has `qIm ≤ 0`, hence its comparison bound is `≥ 1`
  have horb_ge : ∀ n : ℕ, (1 : ℝ) ≤ Real.exp (-(π : ℝ) * thetaable.qIm (n • x)) := by
    intro n
    rw [hqn n]
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (-thetaable.qIm x) :=
      mul_nonneg (sq_nonneg _) (neg_nonneg.mpr hcon)
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (-(π : ℝ) * ((n : ℝ) ^ 2 * thetaable.qIm x)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  -- but the comparison function forces the bound below `1` off a finite set
  have hgz := (thetaable.to_compare_g_summable (0 : M →ₗ[R] ℂ)).tendsto_cofinite_zero
  have hev2 : ∀ᶠ i in Filter.cofinite, thetaable.to_compare_g 0 i < 1 :=
    hgz.eventually_lt tendsto_const_nhds (by norm_num)
  have hev3 : ∀ᶠ i in Filter.cofinite, Real.exp (-(π : ℝ) * thetaable.qIm i) < 1 :=
    (comparison_eventual_0.and hev2).mono fun i h => h.1.trans_lt h.2
  have hTfin : {i : M | ¬ Real.exp (-(π : ℝ) * thetaable.qIm i) < 1}.Finite :=
    Filter.eventually_cofinite.mp hev3
  have horb_sub :
      Set.range (fun n : ℕ => n • x) ⊆ {i : M | ¬ Real.exp (-(π : ℝ) * thetaable.qIm i) < 1} := by
    rintro _ ⟨n, rfl⟩
    exact not_lt.mpr (horb_ge n)
  exact (horb x hx) (hTfin.subset horb_sub)

/-- The real ray through `x`, written in standard Euclidean coordinates. -/
noncomputable def _root_.QuadraticMap.ray {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Fin n → ℝ :=
  fun i => t * x i

/-- The coordinatewise nearest integer-lattice approximation to a Euclidean vector. -/
noncomputable def _root_.QuadraticMap.approximant {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : Fin n → ℤ :=
  fun i => round (x i)

/-- Each coordinate of `QuadraticMap.approximant x` lies within `1 / 2` of the corresponding
coordinate of `x`. -/
lemma _root_.QuadraticMap.approximant_error {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i - (QuadraticMap.approximant x i : ℝ)| ≤ 1 / 2 := by
  simpa [QuadraticMap.approximant, abs_sub_comm] using abs_sub_round (x i)

/-- The coordinatewise nearest lattice point to `QuadraticMap.ray x t`. -/
noncomputable def _root_.QuadraticMap.roundedRayPoint {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Fin n → ℤ :=
  QuadraticMap.approximant ((EuclideanSpace.equiv (Fin n) ℝ).symm (QuadraticMap.ray x t))

/-- A quadratic map on a finite-dimensional real Euclidean space is continuous. -/
private lemma _root_.QuadraticMap.continuous_euclidean {n : ℕ}
    (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) : Continuous Q := by
  let B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    { toFun := fun u => LinearMap.toContinuousLinearMap (Q.polarBilin u)
      map_add' := by
        intro u v
        ext w
        simp [QuadraticMap.polarBilin_apply_apply]
      map_smul' := by
        intro a u
        ext v
        simp [QuadraticMap.polarBilin_apply_apply] }
  let Bc : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap B
  have hBcontinuous : Continuous fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) => Bc p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((Bc.continuous.comp continuous_fst).prodMk continuous_snd)
  have hpolar : Continuous fun u : EuclideanSpace ℝ (Fin n) =>
      QuadraticMap.polar (⇑Q) u u := by
    have hdiagonal : Continuous fun u : EuclideanSpace ℝ (Fin n) => Bc u u := by
      change Continuous ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Bc p.1 p.2) ∘ fun u => (u, u))
      exact hBcontinuous.comp (continuous_id.prodMk continuous_id)
    convert hdiagonal using 1
    rfl
  have hQeq : (Q : EuclideanSpace ℝ (Fin n) → ℝ) =
      fun u => (2 : ℝ)⁻¹ * QuadraticMap.polar (⇑Q) u u := by
    funext u
    rw [QuadraticMap.polar_self, two_smul]
    ring
  rw [hQeq]
  exact continuous_const.mul hpolar

/-- A null vector of a nonnegative real quadratic map lies in its polar radical. -/
private lemma _root_.QuadraticMap.polarBilin_eq_zero_of_nonnegative {n : ℕ}
    (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQ_nonnegative : ∀ y, 0 ≤ Q y) {x : EuclideanSpace ℝ (Fin n)} (hQx : Q x = 0) :
    ∀ y, Q.polarBilin x y = 0 := by
  intro y
  have hQy : 0 ≤ Q y := hQ_nonnegative y
  have hpoly (t : ℝ) : 0 ≤ t ^ 2 * Q y + t * Q.polarBilin x y := by
    have h := hQ_nonnegative (x + t • y)
    rw [show Q (x + t • y) = Q x + Q (t • y) + Q.polarBilin x (t • y) by
      rw [QuadraticMap.polarBilin_apply_apply]
      dsimp [QuadraticMap.polar]
      ring, hQx, Q.map_smul, smul_eq_mul,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul_right, smul_eq_mul] at h
    simpa [pow_two] using h
  -- A nonnegative quadratic polynomial with zero constant term has zero linear coefficient.
  by_contra hpolar
  have hden_pos : 0 < 2 * (Q y + 1) := by positivity
  have hden_ne : 2 * (Q y + 1) ≠ 0 := hden_pos.ne'
  have h := hpoly (-(Q.polarBilin x y) / (2 * (Q y + 1)))
  have hsq_pos : 0 < (Q.polarBilin x y) ^ 2 := sq_pos_of_ne_zero hpolar
  field_simp [hden_ne] at h
  nlinarith

/-- A strictly negative real ray yields infinitely many distinct rounded lattice points whose
exponential values are not summable. -/
private lemma _root_.QuadraticMap.exists_nonSummable_roundedBadPoints_of_neg {n : ℕ}
    (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (hQx : Q x < 0) :
    ∃ ts : Set ℝ, ts.Infinite ∧ Set.InjOn (QuadraticMap.roundedRayPoint x) ts ∧
      ¬ Summable (fun t : ts => Real.exp (-(π : ℝ) * Q
        ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (QuadraticMap.roundedRayPoint x t i : ℝ)))) := by
  classical
  let ray := QuadraticMap.ray x
  let rounded := QuadraticMap.roundedRayPoint x
  have rounded_error (t : ℝ) (i : Fin n) :
      |ray t i - (rounded t i : ℝ)| ≤ 1 / 2 := by
    simpa [ray, rounded, QuadraticMap.roundedRayPoint] using
      QuadraticMap.approximant_error
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (QuadraticMap.ray x t)) i
  obtain ⟨i, hxi⟩ : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    ext j
    simp [h j]
  let t : ℕ → ℝ := fun k => k / x i
  have ray_t_i (k : ℕ) : ray (t k) i = k := by
    dsimp [ray, t, QuadraticMap.ray]
    field_simp
  have rounded_t_i (k : ℕ) : rounded (t k) i = k := by
    simp only [rounded, QuadraticMap.roundedRayPoint, QuadraticMap.approximant]
    change round (ray (t k) i) = k
    rw [ray_t_i]
    exact round_natCast k
  have ht_inj : Function.Injective t := by
    intro a b hab
    have hab' : (a : ℝ) / x i = (b : ℝ) / x i := by
      simpa [t] using hab
    have hab'' : (a : ℝ) = b := by
      calc
        (a : ℝ) = ((a : ℝ) / x i) * x i := by field_simp
        _ = ((b : ℝ) / x i) * x i := by rw [hab']
        _ = b := by field_simp
    exact_mod_cast hab''
  suffices hQx_neg : Q x < 0 by
    -- The negative quadratic term dominates the linear rounding
    -- error, so the rounded exponential values cannot be summable.
    let ts : Set ℝ := Set.range t
    have hts : ts.Infinite := by
      exact Set.infinite_range_of_injective ht_inj
    have hrounded_inj : Set.InjOn rounded ts := by
      rintro a ⟨k, rfl⟩ b ⟨l, rfl⟩ hab
      have hkl : k = l := by
        have hi : rounded (t k) i = rounded (t l) i :=
          congrArg (fun z : Fin n → ℤ => z i) hab
        rw [rounded_t_i k, rounded_t_i l] at hi
        exact_mod_cast hi
      simp [hkl]
    refine ⟨ts, hts, hrounded_inj, ?_⟩
    have hQrounded : ∀ᶠ k in Filter.atTop,
        Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (rounded (t k) j : ℝ)) ≤ 0 := by
      let rounded_real : ℕ → EuclideanSpace ℝ (Fin n) := fun k =>
        (EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (rounded (t k) j : ℝ)
      have hrounding_error (k : ℕ) (j : Fin n) :
          |rounded_real k j - t k * x j| ≤ 1 / 2 := by
        simpa [rounded_real, ray, QuadraticMap.ray, abs_sub_comm] using
          rounded_error (t k) j
      have hnormalized : Tendsto (fun k : ℕ => (t k)⁻¹ • rounded_real k)
          Filter.atTop (nhds x) := by
        have ht_inv : Tendsto (fun k : ℕ => (t k)⁻¹) Filter.atTop (nhds 0) := by
          simpa [t, inv_div] using tendsto_const_div_atTop_nhds_zero_nat (x i)
        have hcoordinate (j : Fin n) : Tendsto (fun k : ℕ =>
            ((t k)⁻¹ • rounded_real k) j) Filter.atTop (nhds (x j)) := by
          let e : ℕ → ℝ := fun k => rounded_real k j - t k * x j
          have he_bounded : IsBoundedUnder (· ≤ ·) Filter.atTop (norm ∘ e) := by
            apply isBoundedUnder_of_eventually_le (a := 1 / 2)
            exact Eventually.of_forall fun k => by
              simpa [e, Real.norm_eq_abs] using hrounding_error k j
          have he_zero : Tendsto (fun k : ℕ => (t k)⁻¹ • e k)
              Filter.atTop (nhds 0) :=
            NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded ht_inv he_bounded
          have hsum : Tendsto (fun k : ℕ => x j + (t k)⁻¹ • e k)
              Filter.atTop (nhds (x j)) := by
            simpa using tendsto_const_nhds.add he_zero
          refine hsum.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
          have htk : t k ≠ 0 := by
            exact div_ne_zero (by exact_mod_cast hk.ne') hxi
          simp only [PiLp.smul_apply, smul_eq_mul, e, mul_sub]
          rw [← mul_assoc, inv_mul_cancel₀ htk, one_mul]
          ring
        let e := EuclideanSpace.equiv (Fin n) ℝ
        have hcoordinates : Tendsto (fun k : ℕ => fun j : Fin n =>
            ((t k)⁻¹ • rounded_real k) j) Filter.atTop (nhds (e x)) := by
          rw [tendsto_pi_nhds]
          intro j
          simpa [e] using hcoordinate j
        have h := (e.symm.continuous.tendsto (e x)).comp hcoordinates
        convert h using 1 <;> ext j <;> rfl
      have hQcontinuous := Q.continuous_euclidean
      have hQneg : ∀ᶠ k in Filter.atTop, Q ((t k)⁻¹ • rounded_real k) < 0 :=
        ((hQcontinuous.tendsto x).comp hnormalized).eventually_lt_const hQx_neg
      have hrounded_factor : ∀ᶠ k in Filter.atTop,
          Q (rounded_real k) = (t k) ^ 2 * Q ((t k)⁻¹ • rounded_real k) := by
        -- Eventually `t k ≠ 0`; then recover the rounded point from its normalized form and
        -- apply quadratic homogeneity.
        filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
        have htk : t k ≠ 0 := by
          exact div_ne_zero (by exact_mod_cast hk.ne') hxi
        rw [show rounded_real k = t k • ((t k)⁻¹ • rounded_real k) by
          rw [smul_smul, mul_inv_cancel₀ htk, one_smul], Q.map_smul]
        simp only [smul_eq_mul, pow_two]
        rw [<-smul_assoc]
        congr 1
        have cancel_tk : ((t k)⁻¹ • t k) = 1 := by
          simp
          exact inv_mul_cancel₀ htk
        rw [cancel_tk]
        rw [one_smul]
      filter_upwards [hQneg, hrounded_factor] with k hk hfactor
      rw [show ((EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (rounded (t k) j : ℝ)) =
        rounded_real k by rfl, hfactor]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (t k)) hk.le
    intro hsum
    let r : ℕ → ts := fun k => ⟨t k, ⟨k, rfl⟩⟩
    have hr_inj : Function.Injective r := by
      intro a b hab
      exact ht_inj (congrArg Subtype.val hab)
    have hsum_nat : Summable (fun k : ℕ => Real.exp (-(π : ℝ) * Q
        ((EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (rounded (t k) j : ℝ)))) := by
      refine (hsum.comp_injective hr_inj).congr fun k => ?_
      simp [r, rounded]
    have hge : ∀ᶠ k in Filter.atTop,
        1 ≤ Real.exp (-(π : ℝ) * Q
          ((EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (rounded (t k) j : ℝ))) := by
      filter_upwards [hQrounded] with k hk
      apply one_le_exp
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr Real.pi_pos.le) hk
    have hnot_tendsto : ¬ Tendsto (fun k : ℕ => Real.exp (-(π : ℝ) * Q
        ((EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (rounded (t k) j : ℝ))))
        Filter.atTop (nhds 0) := by
      intro htend
      have hlt : ∀ᶠ k in Filter.atTop,
          Real.exp (-(π : ℝ) * Q
            ((EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (rounded (t k) j : ℝ))) < 1 / 2 :=
        (tendsto_order.1 htend).2 (1 / 2) (by norm_num)
      obtain ⟨k, hk, hlt⟩ := (hge.and hlt).exists
      linarith
    exact hnot_tendsto hsum_nat.tendsto_atTop_zero
  exact hQx

/-- A null real ray yields infinitely many distinct rounded lattice points whose exponential
values are not summable. -/
private lemma _root_.QuadraticMap.exists_nonSummable_roundedBadPoints_of_eq_zero {n : ℕ}
    (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (hQx : Q x = 0) :
    ∃ s : Set (Fin n → ℤ), s.Infinite ∧ ¬ Summable (fun z : s => Real.exp (-(π : ℝ) * Q
      ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z.val i : ℝ)))) := by
  -- Select simultaneous approximants whose rounding errors keep the polar cross-term under
  -- control along the null ray.
  by_cases hnegative : ∃ z : Fin n → ℤ,
      Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z i : ℝ)) < 0
  · -- Multiples of this lattice point already have strictly negative quadratic values.
    obtain ⟨z, hz⟩ := hnegative
    have hz_ne : z ≠ 0 := by
      intro hz_zero
      subst z
      have hzero : (EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun i => (((0 : Fin n → ℤ) i : ℤ) : ℝ)) = 0 := by
        apply (EuclideanSpace.equiv (Fin n) ℝ).injective
        ext i
        simp
      rw [hzero] at hz
      set_option linter.unnecessarySimpa false in
      simpa using hz
    let f : ℕ → Fin n → ℤ := fun k => k • z
    have hf_inj : Function.Injective f := by
      intro m n hmn
      change m • z = n • z at hmn
      rw [← natCast_zsmul, ← natCast_zsmul] at hmn
      simpa using smul_left_injective ℤ hz_ne hmn
    let s : Set (Fin n → ℤ) := Set.range f
    have hs : s.Infinite := Set.infinite_range_of_injective hf_inj
    refine ⟨s, hs, ?_⟩
    intro hsumm
    let r : ℕ → s := fun k => ⟨f k, ⟨k, rfl⟩⟩
    have hr_inj : Function.Injective r := by
      intro a b hab
      exact hf_inj (congrArg Subtype.val hab)
    have hQmul (k : ℕ) : Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i =>
        ((f k i : ℤ) : ℝ)) = (k : ℝ) ^ 2 * Q
          ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z i : ℝ)) := by
      have hemb : (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (f k i : ℝ)) =
          (k : ℝ) • (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (z i : ℝ)) := by
        apply (EuclideanSpace.equiv (Fin n) ℝ).injective
        ext i
        simp [f, PiLp.smul_apply, smul_eq_mul]
      rw [hemb, Q.map_smul, smul_eq_mul]
      ring
    have hsum_nat : Summable (fun k : ℕ => Real.exp (-(π : ℝ) * Q
        ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (f k i : ℝ)))) := by
      refine (hsumm.comp_injective hr_inj).congr fun k => ?_
      simp [r]
    have hge : ∀ k : ℕ, 1 ≤ Real.exp (-(π : ℝ) * Q
        ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (f k i : ℝ))) := by
      intro k
      rw [hQmul]
      apply one_le_exp
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr Real.pi_pos.le)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (k : ℝ)) hz.le)
    have hnot_tendsto : ¬ Tendsto (fun k : ℕ => Real.exp (-(π : ℝ) * Q
        ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (f k i : ℝ))))
        Filter.atTop (nhds 0) := by
      intro htend
      have hlt : ∀ᶠ k in Filter.atTop, Real.exp (-(π : ℝ) * Q
          ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (f k i : ℝ))) < 1 / 2 :=
        (tendsto_order.1 htend).2 (1 / 2) (by norm_num)
      obtain ⟨k, hk, hlt⟩ := ((Eventually.of_forall hge).and hlt).exists
      linarith
    exact hnot_tendsto hsum_nat.tendsto_atTop_zero
  · have hnonnegative : ∀ z : Fin n → ℤ,
        0 ≤ Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z i : ℝ)) := by
      intro z
      exact le_of_not_gt fun hz => hnegative ⟨z, hz⟩
    -- By density, `Q` is nonnegative on the real Euclidean space. Hence the null vector `x`
    -- lies in its radical, so rounding the ray contributes only the bounded error quadratic form.
    have hnonnegative_rat : ∀ y : Fin n → ℚ,
        0 ≤ Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (y i : ℝ)) := by
      -- Clear the finitely many coordinate denominators and apply `hnonnegative` to the resulting
      -- integer vector; quadratic homogeneity then divides back by the positive common denominator.
      intro y
      let A : Matrix (Fin n) Unit ℚ := fun i _ => y i
      let d : ℕ := Matrix.den A
      let z : Fin n → ℤ := fun i => Matrix.num A i ()
      have hd : d ≠ 0 := Matrix.den_ne_zero A
      have hcoord : ∀ i : Fin n, (y i : ℝ) = (d : ℝ)⁻¹ * (z i : ℝ) := by
        intro i
        have hrat : (z i : ℚ) / d = y i := by
          simpa [A, z, d] using Matrix.num_div_den A i ()
        have hrat_real := congrArg (fun q : ℚ => (q : ℝ)) hrat
        simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hrat_real
        simpa [div_eq_mul_inv, mul_comm] using hrat_real.symm
      have hscale : (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (y i : ℝ)) =
          (d : ℝ)⁻¹ • (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (z i : ℝ)) := by
        apply (EuclideanSpace.equiv (Fin n) ℝ).injective
        ext i
        simpa [PiLp.smul_apply, smul_eq_mul] using hcoord i
      rw [hscale, Q.map_smul, smul_eq_mul]
      exact mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg d)) (inv_nonneg.mpr (Nat.cast_nonneg d)))
        (hnonnegative z)
    let e := EuclideanSpace.equiv (Fin n) ℝ
    have hdense : DenseRange (fun y : Fin n → ℚ => e.symm fun i => (y i : ℝ)) := by
      exact e.symm.surjective.denseRange.comp
        (DenseRange.piMap fun _ => Rat.denseRange_cast) e.symm.continuous
    have hQ_nonnegative : ∀ y : EuclideanSpace ℝ (Fin n), 0 ≤ Q y := by
      intro y
      have hclosed : IsClosed (Q ⁻¹' Set.Ici 0) :=
        isClosed_Ici.preimage Q.continuous_euclidean
      have hsubset : Set.range (fun y : Fin n → ℚ => e.symm fun i => (y i : ℝ)) ⊆
          Q ⁻¹' Set.Ici 0 := by
        rintro _ ⟨y, rfl⟩
        exact hnonnegative_rat y
      have huniv : (Set.univ : Set (EuclideanSpace ℝ (Fin n))) ⊆ Q ⁻¹' Set.Ici 0 := by
        rw [← hdense.closure_eq]
        exact closure_minimal hsubset hclosed
      exact huniv (Set.mem_univ y)
    have hradical : ∀ y : EuclideanSpace ℝ (Fin n), Q.polarBilin x y = 0 :=
      Q.polarBilin_eq_zero_of_nonnegative hQ_nonnegative hQx
    have hrounding_error_bound : ∃ C : ℝ, ∀ u : EuclideanSpace ℝ (Fin n),
        (∀ i : Fin n, |u i| ≤ 1 / 2) → Q u ≤ C := by
      -- The coordinatewise rounding-error box is compact, and `Q` is continuous on it.
      let e := EuclideanSpace.equiv (Fin n) ℝ
      let box : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
      have hbox_compact : IsCompact box :=
        isCompact_univ_pi fun _ => isCompact_Icc
      have hQ_box_compact : IsCompact (Q '' (e.symm '' box)) :=
        (hbox_compact.image e.symm.continuous).image Q.continuous_euclidean
      obtain ⟨C, hC⟩ := hQ_box_compact.isBounded.subset_closedBall 0
      refine ⟨C, fun u hu => ?_⟩
      have hu_box : e u ∈ box := by
        rw [Set.mem_univ_pi]
        intro i
        simpa [e] using (abs_le.mp (hu i))
      have hu_image : u ∈ e.symm '' box := by
        refine ⟨e u, hu_box, ?_⟩
        simp [e]
      have hQu : Q u ∈ Q '' (e.symm '' box) := ⟨u, hu_image, rfl⟩
      have hCQu : Q u ∈ Metric.closedBall 0 C := hC hQu
      rw [Metric.mem_closedBall, Real.dist_eq] at hCQu
      exact le_trans (le_abs_self _) (by simpa using hCQu)
    classical
    let ray := QuadraticMap.ray x
    let rounded := QuadraticMap.roundedRayPoint x
    obtain ⟨i, hxi⟩ : ∃ i : Fin n, x i ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      apply (EuclideanSpace.equiv (Fin n) ℝ).injective
      ext j
      simp [h j]
    let t : ℕ → ℝ := fun index_in_bad_set => index_in_bad_set / x i
    have hray_t_i (index_in_bad_set : ℕ) :
        ray (t index_in_bad_set) i = index_in_bad_set := by
      dsimp [ray, t, QuadraticMap.ray]
      field_simp
    have hrounded_t_i (index_in_bad_set : ℕ) :
        rounded (t index_in_bad_set) i = index_in_bad_set := by
      simp only [rounded, QuadraticMap.roundedRayPoint, QuadraticMap.approximant]
      change round (ray (t index_in_bad_set) i) = index_in_bad_set
      rw [hray_t_i]
      exact round_natCast index_in_bad_set
    let f : ℕ → Fin n → ℤ := fun index_in_bad_set => rounded (t index_in_bad_set)
    have hf_inj : Function.Injective f := by
      intro index_in_bad_set other_index_in_bad_set hindices
      have hi : rounded (t index_in_bad_set) i = rounded (t other_index_in_bad_set) i :=
        congrArg (fun z : Fin n → ℤ => z i) hindices
      rw [hrounded_t_i index_in_bad_set, hrounded_t_i other_index_in_bad_set] at hi
      exact_mod_cast hi
    let s : Set (Fin n → ℤ) := Set.range f
    have hs : s.Infinite := Set.infinite_range_of_injective hf_inj
    refine ⟨s, hs, ?_⟩
    let z : ℕ → EuclideanSpace ℝ (Fin n) := fun index_in_bad_set =>
      (EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (f index_in_bad_set j : ℝ)
    let rounding_error : ℕ → EuclideanSpace ℝ (Fin n) := fun index_in_bad_set =>
      z index_in_bad_set - t index_in_bad_set • x
    have hz_decomposition (index_in_bad_set : ℕ) :
        z index_in_bad_set = t index_in_bad_set • x + rounding_error index_in_bad_set := by
      simp only [rounding_error]
      abel
    have hQz (index_in_bad_set : ℕ) :
        Q (z index_in_bad_set) = Q (rounding_error index_in_bad_set) := by
      have hpolar_zero : QuadraticMap.polar (⇑Q) x (rounding_error index_in_bad_set) = 0 := by
        simpa [QuadraticMap.polarBilin_apply_apply] using hradical (rounding_error index_in_bad_set)
      rw [hz_decomposition]
      rw [show Q (t index_in_bad_set • x + rounding_error index_in_bad_set) =
          Q (t index_in_bad_set • x) + Q (rounding_error index_in_bad_set) +
          Q.polarBilin (t index_in_bad_set • x) (rounding_error index_in_bad_set) by
        rw [QuadraticMap.polarBilin_apply_apply]
        dsimp [QuadraticMap.polar]
        ring]
      rw [Q.map_smul, smul_eq_mul, hQx, mul_zero, zero_add,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul_left,
        smul_eq_mul, hpolar_zero, mul_zero, add_zero]
    obtain ⟨C, hC⟩ := hrounding_error_bound
    have hrounding_error_in_box (index_in_bad_set : ℕ) (j : Fin n) :
        |rounding_error index_in_bad_set j| ≤ 1 / 2 := by
      change |(rounded (t index_in_bad_set) j : ℝ) - t index_in_bad_set * x j| ≤ 1 / 2
      simpa [rounded, QuadraticMap.roundedRayPoint, QuadraticMap.approximant,
        ray, QuadraticMap.ray, abs_sub_comm] using
        QuadraticMap.approximant_error
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (QuadraticMap.ray x (t index_in_bad_set))) j
    have hQ_bounded_on_s (point_in_bad_set : s) : Q
        ((EuclideanSpace.equiv (Fin n) ℝ).symm fun j => (point_in_bad_set.val j : ℝ)) ≤ C := by
      rcases point_in_bad_set.property with ⟨index_in_bad_set, hpoint⟩
      rw [← hpoint]
      change Q (z index_in_bad_set) ≤ C
      rw [hQz]
      exact hC (rounding_error index_in_bad_set) (hrounding_error_in_box index_in_bad_set)
    intro hsumm
    let f_as_subtype : ℕ → s := fun index_in_bad_set =>
      ⟨f index_in_bad_set, Set.mem_range_self index_in_bad_set⟩
    have hf_as_subtype_inj : Function.Injective f_as_subtype := by
      intro index_in_bad_set other_index_in_bad_set hindices
      exact hf_inj (congrArg Subtype.val hindices)
    have hsum_on_f : Summable (fun index_in_bad_set : ℕ =>
        Real.exp (-(π : ℝ) * Q (z index_in_bad_set))) := by
      refine (hsumm.comp_injective hf_as_subtype_inj).congr fun index_in_bad_set => ?_
      rfl
    let c : ℝ := Real.exp (-(π : ℝ) * C)
    have hlower_bound (index_in_bad_set : ℕ) : c ≤
        Real.exp (-(π : ℝ) * Q (z index_in_bad_set)) := by
      have hbound := hQ_bounded_on_s (f_as_subtype index_in_bad_set)
      change Q (z index_in_bad_set) ≤ C at hbound
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hnot_tendsto : ¬ Tendsto (fun index_in_bad_set : ℕ =>
        Real.exp (-(π : ℝ) * Q (z index_in_bad_set))) Filter.atTop (nhds 0) := by
      intro htend
      have hc_pos : 0 < c := Real.exp_pos _
      have hlt : ∀ᶠ index_in_bad_set in Filter.atTop,
          Real.exp (-(π : ℝ) * Q (z index_in_bad_set)) < c :=
        (tendsto_order.1 htend).2 c hc_pos
      obtain ⟨index_in_bad_set, hbound, hlt⟩ :=
        ((Eventually.of_forall hlower_bound).and hlt).exists
      linarith
    exact hnot_tendsto hsum_on_f.tendsto_atTop_zero

/-- A nonpositive real ray of a quadratic form yields infinitely many distinct rounded lattice
points whose exponential values are not summable. -/
private lemma _root_.QuadraticMap.exists_nonSummable_badLatticePoints {n : ℕ}
    (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (hQx : Q x ≤ 0) :
    ∃ s : Set (Fin n → ℤ), s.Infinite ∧ ¬ Summable (fun z : s => Real.exp (-(π : ℝ) * Q
      ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z.val i : ℝ)))) := by
  rcases eq_or_lt_of_le hQx with hQx_zero | hQx_neg
  · exact Q.exists_nonSummable_roundedBadPoints_of_eq_zero x hx hQx_zero
  · obtain ⟨ts, hts, hrounded_inj, hts_nonsummable⟩ :=
      Q.exists_nonSummable_roundedBadPoints_of_neg x hx hQx_neg
    let rounded := QuadraticMap.roundedRayPoint x
    let s : Set (Fin n → ℤ) := rounded '' ts
    have hs : s.Infinite := by
      change (rounded '' ts).Infinite
      exact hts.image hrounded_inj
    refine ⟨s, hs, ?_⟩
    intro hsumm
    apply hts_nonsummable
    let r : ts → s := fun t => ⟨rounded t, ⟨t, t.property, rfl⟩⟩
    have hr_inj : Function.Injective r := by
      intro a b hab
      apply Subtype.ext
      exact hrounded_inj a.property b.property (congrArg Subtype.val hab)
    refine (hsumm.comp_injective hr_inj).congr fun t => ?_
    simp [r, rounded, QuadraticMap.roundedRayPoint]

/-- Positive-definiteness of a real quadratic form whose restriction to the integer lattice is the
imaginary part of theta data. The proof uses the summable comparison function to rule out a real
ray on which the form is nonpositive. -/
theorem qImRe_posdef {n : ℕ}
    (thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin n → ℤ))
    (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQrestrict : ∀ z,
      Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z i : ℝ)) = thetaable.qIm z) :
    Q.PosDef := by
  intro x hx
  have comparison_eventual_0 :=
    thetaable.comparison_eventual (0 : (Fin n → ℤ) →ₗ[ℤ] ℂ)
  have hbound_eq' : ∀ z : Fin n → ℤ,
      ‖Complex.exp (↑π * I * ((thetaable.qRe z : ℂ) + I * (thetaable.qIm z : ℂ))
        + 2 * ↑π * I * ((0 : (Fin n → ℤ) →ₗ[ℤ] ℂ) z))‖
        = Real.exp (-(π : ℝ) *
          Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z i : ℝ))) := by
    have before := thetaable.hbound_eq
    intro i
    rw [before i]
    rw [hQrestrict i]
  let z_val (z : Fin n → ℝ) := Real.exp (-(π : ℝ) *
    Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z i : ℝ)))
  let z_round_val (z : Fin n → ℝ) := Real.exp (-(π : ℝ) *
    Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (round (z i) : ℤ)))
  by_contra hQx
  push Not at hQx
  have bad_collection :
      ∃ s : Set (Fin n → ℤ), s.Infinite ∧ ¬ Summable (fun z : s => Real.exp (-(π : ℝ) *
        Q ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (z.val i : ℝ)))) := by
    exact Q.exists_nonSummable_badLatticePoints x hx hQx
  obtain ⟨s, hs, s_nonsummable⟩ := bad_collection
  letI : Infinite s := hs.to_subtype
  have compare_summable :
      Summable (fun z : s => thetaable.to_compare_g 0 z) := by
    exact (thetaable.to_compare_g_summable 0).comp_injective Subtype.val_injective
  have comparison_on_s :
      ∀ᶠ z : s in Filter.cofinite,
        ‖Complex.exp (↑π * I *
          ((thetaable.qRe z : ℂ) + I * (thetaable.qIm z : ℂ))
          + 2 * ↑π * I * ((0 : (Fin n → ℤ) →ₗ[ℤ] ℂ) z))‖
          ≤ thetaable.to_compare_g 0 z := by
    exact Subtype.val_injective.tendsto_cofinite.eventually comparison_eventual_0
  have summand_summable : Summable (fun z : s => Complex.exp (↑π * I *
        ((thetaable.qRe z : ℂ) + I * (thetaable.qIm z : ℂ))
        + 2 * ↑π * I * ((0 : (Fin n → ℤ) →ₗ[ℤ] ℂ) z))) := by
    exact Summable.of_norm_bounded_eventually compare_summable comparison_on_s
  apply s_nonsummable
  exact summand_summable.norm.congr fun z => hbound_eq' z

end ThetaAbleQuadraticForm

end GeneralThetaAble

section TauPeriodic

variable {R M : Type u} [cr : CommRing R] [Module R ℝ] [AddCommGroup M] [Module R M] [Module R ℂ] [IsScalarTower R ℝ ℂ]
variable [SMulCommClass R ℂ ℂ]
variable [thetaable : ThetaAbleQuadraticForm (R := R) (M := M)]

noncomputable def tau_operator :
    M →ₗ[R] (M →ₗ[R] ℂ) :=
  have reP : M →ₗ[R] (M →ₗ[R] ℝ) := thetaable.qRe.polarBilin (R:=R) (M:=M) (N:=ℝ)
  have imP : M →ₗ[R] (M →ₗ[R] ℝ) := thetaable.qIm.polarBilin (R:=R) (M:=M) (N:=ℝ)
  (LinearMap.llcomp R M ℝ ℂ ofRealLinear).comp reP
      + (LinearMap.llcomp R M ℝ ℂ (mulILinear.comp ofRealLinear)).comp imP

/-
θ(z_before + tau_operator m_shift; Q) =
(theta_tau_cocycle m_shift z_before) * θ(z_before; Q)
  where `Q = qRe + I qIm` is the ambient (general, not yet specialized to any scalar slice)
  modulus fixed by the `thetaable` instance, and only the shift `z_before` varies.
-/
noncomputable def theta_tau_cocycle (m_shift : M) (z_before : M →ₗ[R] ℂ) : ℂ :=
  Complex.exp (-(↑π * Complex.I *
      ((thetaable.qRe m_shift : ℂ) + Complex.I * (thetaable.qIm m_shift : ℂ))
    + 2 * ↑π * Complex.I * z_before m_shift))

namespace ThetaAbleQuadraticForm

/-- The quasi-periodicity of the Riemann theta function under a shift of `z` by one full period
`(2 : ℂ)⁻¹ • tau_operator m`: shifting `z` by this amount multiplies `theta_fun` by the cocycle
`theta_tau_cocycle m z`. The halving is purely a `ℂ`-scalar operation on the codomain of
`tau_operator m : M →ₗ[R] ℂ` (using `SMulCommClass R ℂ ℂ`, already in scope, to know that this
`ℂ`-scalar action on `M →ₗ[R] ℂ` is still `R`-linear) — `2` need not be invertible in `R` at all,
since `2 ≠ 0` always in the field `ℂ`. The `1/2` is needed because `tau_operator` itself is built
from the *unnormalized* `polarBilin`, i.e. `Q (x+m) - Q x - Q m` rather than half of that, so
`tau_operator m` on its own is already *two* periods' worth of shift. -/
lemma tau_periodicity (z : M →ₗ[R] ℂ) : ∀ m : M,
  theta_fun (z + (2 : ℂ)⁻¹ • tau_operator m) =
  (theta_tau_cocycle m z) * theta_fun z := by
  intro m
  set φ : M →ₗ[R] ℂ := (2 : ℂ)⁻¹ • tau_operator m with hφ
  set E : ℂ := ↑π * Complex.I * ((thetaable.qRe m : ℂ) + Complex.I * (thetaable.qIm m : ℂ))
      + 2 * ↑π * Complex.I * z m with hE
  have hcocycle : theta_tau_cocycle m z = Complex.exp (-E) := rfl
  have htau : ∀ x : M, (tau_operator (R:=R) m) x =
      (thetaable.qRe.polarBilin m x : ℂ) + Complex.I * (thetaable.qIm.polarBilin m x : ℂ) := by
    intro x
    simp [tau_operator, ofRealLinear, mulILinear]
  have hkey : ∀ x : M,
      (thetaable.qRe.polarBilin m x : ℂ) + Complex.I * (thetaable.qIm.polarBilin m x : ℂ)
        = 2 * φ x := by
    intro x
    rw [← htau x, hφ, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_ne_zero,
      one_mul]
  have hpt : ∀ x : M,
      Complex.exp (↑π * Complex.I *
          ((thetaable.qRe (x + m) : ℂ) + Complex.I * (thetaable.qIm (x + m) : ℂ))
        + 2 * ↑π * Complex.I * z (x + m))
      = Complex.exp E * Complex.exp (↑π * Complex.I *
          ((thetaable.qRe x : ℂ) + Complex.I * (thetaable.qIm x : ℂ))
        + 2 * ↑π * Complex.I * (z + φ) x) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    have hRe : thetaable.qRe (m + x) = thetaable.qRe m + thetaable.qRe x
        + thetaable.qRe.polarBilin m x := by
      rw [QuadraticMap.map_add (f:=qRe), QuadraticMap.polarBilin_apply_apply]
    have hIm : thetaable.qIm (m + x) = thetaable.qIm m + thetaable.qIm x
        + thetaable.qIm.polarBilin m x := by
      rw [QuadraticMap.map_add (f:=qIm), QuadraticMap.polarBilin_apply_apply]
    rw [add_comm x m, hRe, hIm, map_add z m x, LinearMap.add_apply z φ x, hE]
    push_cast
    linear_combination (↑π * Complex.I) * hkey x
  have hsum_z := (theta_fun_summable z).hasSum
  have hshift : HasSum (fun x => Complex.exp (↑π * Complex.I *
      ((thetaable.qRe (x + m) : ℂ) + Complex.I * (thetaable.qIm (x + m) : ℂ))
      + 2 * ↑π * Complex.I * z (x + m))) (theta_fun z) :=
    (Equiv.addRight m).hasSum_iff.mpr hsum_z
  simp only [hpt] at hshift
  have hsum_zφ := (theta_fun_summable (z + φ)).hasSum
  have hmain : theta_fun z = Complex.exp E * theta_fun (z + φ) :=
    hshift.unique (hsum_zφ.mul_left (Complex.exp E))
  rw [hcocycle, hmain, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

end ThetaAbleQuadraticForm

end TauPeriodic

section GaussianTheta

variable {n : ℕ}

noncomputable def gaussianExponent
  (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  (hQcont : Continuous Q)
  (mu : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    C(EuclideanSpace ℝ (Fin n), ℝ) where
  toFun x := -π * Q (x - mu) + c
  continuous_toFun := by fun_prop

/-- The general multivariate Gaussian `exp (-π (x-μ)ᵗQ(x-μ) + c)` on `EuclideanSpace ℝ ι`,
for `Q : Matrix ι ι ℝ`, mean `μ`, and constant `c : ℂ`. (`Q` need not be positive definite for
this to be well-defined as a continuous function; positive-definiteness is only used later to
get lattice summability.) -/
noncomputable def gaussianFun
  (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  (hQcont : Continuous Q)
  (mu : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    C(EuclideanSpace ℝ (Fin n), ℝ) :=
  have r_exp : C(ℝ , ℝ) := {
    toFun x := rexp x
    continuous_toFun := by fun_prop
  }
  {
    toFun x := (r_exp ∘ (gaussianExponent Q hQcont mu c)) x
    continuous_toFun := by fun_prop
  }

lemma bound_gaussian_exponent
    (hn : n ≠ 0)
    (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQcont : Continuous Q)
    (hQ : Q.PosDef)
    (mu : EuclideanSpace ℝ (Fin n)) (const : ℝ)
    :
    ∃ c d : ℝ, c > 0 ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      -c * ‖x - mu‖ ^ 2 - d ≥ (gaussianExponent Q hQcont mu const x) := by
  have w := posDef_lower_bound hn Q
    hQcont hQ
  simp only [gaussianExponent]
  obtain ⟨c,hc,hw⟩ := w
  use (c*π)
  use -const
  split_ands
  · simp [hc]
    exact Real.pi_pos
  · intro x
    have hw2 := hw (x-mu)
    simp
    rw [<-add_assoc]
    have key : c * π * ‖x - mu‖ ^ 2 + -(π * Q (x - mu)) <= 0 := by
      rw [mul_comm c π]
      rw [<-neg_mul]
      simp
      rw [mul_assoc]
      rw [<-le_mul_inv_iff₀' Real.pi_pos]
      rw [mul_comm π]
      rw [mul_assoc _ π]
      simp
      exact hw2
    have const_le_const : const <= const := by
      exact le_refl const
    have key2 := add_le_add (h₁:=key) (h₂ := const_le_const)
    rw [zero_add] at key2
    exact key2



/-- The shift point `mu`, obtained from `z` by "completing the square": the unique point with
`Q_Im.polarBilin y mu = -2 * ⟪ellCoord z, y⟫` for all `y`, via inverting `Q_Im`'s (invertible,
since `Q_Im` is positive definite) Gram matrix. -/
noncomputable def muOfShift (Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    ((gramMatrixReal Q_Im)⁻¹.mulVec (fun i => -2 * ellCoord z i))

/-- The defining "completing the square" identity for `muOfShift`: pairing the lattice point
`latticeEmbedding x` against `muOfShift Q_Im z` via `Q_Im`'s polar form recovers (twice, with a
sign) the linear term `Im (z x)` contributed by the shift. -/
lemma polarBilin_latticeEmbedding_muOfShift
    (Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (hQIm : Q_Im.PosDef)
    (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) (x : Fin n → ℤ) :
    Q_Im.polarBilin (toEuclidean_ZnRn x) (muOfShift Q_Im z) =
      -2 * (z x).im := by
  set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis with hb
  have hcoord : ∀ y : EuclideanSpace ℝ (Fin n), (b.repr y : Fin n → ℝ) = fun i => y i := by
    intro y
    funext i
    rw [hb, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b, hcoord, hcoord]
  show (fun i => (toEuclidean_ZnRn x) i) ⬝ᵥ
      (gramMatrixReal Q_Im).mulVec ((EuclideanSpace.equiv (Fin n) ℝ).symm
        ((gramMatrixReal Q_Im)⁻¹.mulVec (fun i => -2 * ellCoord z i)) : Fin n → ℝ) = _
  rw [show ((EuclideanSpace.equiv (Fin n) ℝ).symm
        ((gramMatrixReal Q_Im)⁻¹.mulVec (fun i => -2 * ellCoord z i)) : Fin n → ℝ)
      = (gramMatrixReal Q_Im)⁻¹.mulVec (fun i => -2 * ellCoord z i) from rfl,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (gramMatrixReal_det_isUnit Q_Im hQIm),
    Matrix.one_mulVec]
  rw [z_im_eq_sum]
  rw [dotProduct, Finset.mul_sum]
  congr 1
  ext i
  rw [show (toEuclidean_ZnRn x) i = (x i : ℝ) from rfl]
  ring

private lemma gaussianVPolyDecayHelper
  (n pow: ℕ) (a_const : ℝ) (ha : 0 < a_const) (shift : EuclideanSpace ℝ (Fin n))
: ∀ᶠ (i : Fin n → ℤ) in cofinite,
  rexp (-a_const * (‖toEuclidean_ZnRn i‖ - ‖shift‖) ^ 2) ≤ ‖toEuclidean_ZnRn i‖ ^ (-(pow:ℤ) - 1) := by
  -- (1) the lattice embedding is proper: its norm tends to `∞` along the cofinite filter.
  have htendsto : Tendsto (fun i : Fin n → ℤ => ‖toEuclidean_ZnRn i‖) cofinite atTop := by
    rw [tendsto_atTop]
    intro b
    rw [eventually_cofinite]
    have hsub : {i : Fin n → ℤ | ¬ b ≤ ‖toEuclidean_ZnRn i‖} ⊆
        toEuclidean_ZnRn ⁻¹'
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) b ∩ (stdLattice n : Set _)) := by
      intro i hi
      simp only [not_le, Set.mem_setOf_eq] at hi
      refine ⟨?_, latticeEmbedding_mem_stdLattice i⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hi.le
    exact (Set.Finite.preimage latticeEmbedding_injective.injOn
      (ZSpan.setFinite_inter (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        Metric.isBounded_closedBall)).subset hsub
  -- (2) a Gaussian beats any negative power of the (recentred) radius, eventually as `R → ∞`.
  set C := ‖shift‖
  have hlo : (fun x : ℝ => rexp (-a_const * x ^ 2 + 2 * a_const * C * x))
      =o[atTop] (· ^ (((-(pow : ℤ) - 1 : ℤ) : ℝ))) :=
    rexp_neg_quadratic_isLittleO_rpow_atTop (by linarith) (2 * a_const * C) _
  have hbd := hlo.def (Real.exp_pos (a_const * C ^ 2))
  have hreal : ∀ᶠ R : ℝ in atTop, rexp (-a_const * (R - C) ^ 2) ≤ R ^ (-(pow : ℤ) - 1) := by
    filter_upwards [hbd, eventually_gt_atTop (0:ℝ)] with R hR hRpos
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg hRpos.le _)] at hR
    calc rexp (-a_const * (R - C) ^ 2)
        = rexp (-(a_const * C ^ 2)) * rexp (-a_const * R ^ 2 + 2 * a_const * C * R) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ rexp (-(a_const * C ^ 2)) *
          (rexp (a_const * C ^ 2) * R ^ (((-(pow:ℤ) - 1 : ℤ) : ℝ))) := by
          gcongr
      _ = R ^ (((-(pow:ℤ) - 1 : ℤ) : ℝ)) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
      _ = R ^ (-(pow : ℤ) - 1) := Real.rpow_intCast R _
  exact htendsto.eventually hreal

/-- For any fixed decay rate `a_const > 0`, recentring point `shift`, and polynomial degree `pow`,
the Gaussian `exp (-a_const * ‖((toEuclidean_ZnRn)) i - shift‖ ^ 2)` is eventually
dominated by the negative power `‖((toEuclidean_ZnRn)) i‖ ^ (-(pow : ℤ) - 1)`. -/
lemma gaussianVPolyDecay
  (n pow : ℕ) (a_const : ℝ) (a_const_pos: a_const > 0) (shift: EuclideanSpace ℝ (Fin n)):
  ∀ᶠ (i : Fin n → ℤ) in cofinite,
    ‖rexp (-a_const * ‖((toEuclidean_ZnRn)) i - shift‖ ^ 2)‖ ≤ ‖((toEuclidean_ZnRn)) i‖ ^ (-(pow : ℤ) - 1) := by
  have hnorm_exp : ∀ x : ℝ, ‖rexp x‖ = rexp x := fun x => Real.norm_of_nonneg (Real.exp_pos x).le
  simp only [hnorm_exp]
  set inclusion_matrix := ((toEuclidean_ZnRn))
  -- drop the shift: `‖i - shift‖² ≥ (‖i‖ - ‖shift‖)²` always, so the Gaussian at `i - shift`
  -- is dominated by the (shift-free) Gaussian at the recentred radius `‖i‖ - ‖shift‖`.
  have hexp_le : ∀ i : Fin n → ℤ,
      rexp (-a_const * ‖inclusion_matrix i - shift‖ ^ 2)
        ≤ rexp (-a_const * (‖inclusion_matrix i‖ - ‖shift‖) ^ 2) := by
    intro i
    have htri : (‖inclusion_matrix i‖ - ‖shift‖) ^ 2 ≤ ‖inclusion_matrix i - shift‖ ^ 2 :=
      sq_le_sq' (abs_le.mp (abs_norm_sub_norm_le (inclusion_matrix i) shift)).1
        (abs_le.mp (abs_norm_sub_norm_le (inclusion_matrix i) shift)).2
    have hmul := mul_le_mul_of_nonneg_left htri a_const_pos.le
    exact Real.exp_le_exp.mpr (by linarith)
  have hbound : ∀ᶠ i : Fin n → ℤ in cofinite,
      rexp (-a_const * (‖inclusion_matrix i‖ - ‖shift‖) ^ 2) ≤
        ‖inclusion_matrix i‖ ^ (-(pow : ℤ) - 1) := by
    exact gaussianVPolyDecayHelper n pow a_const a_const_pos shift
  exact hbound.mono fun i hi => (hexp_le i).trans hi

end GaussianTheta

section RiemannThetaAble

variable {n : ℕ}

/-- The real part of the theta exponent at a lattice point `x`, namely
`-π * qIm x - 2π * Im (z x)`, is bounded above by a downward (in `‖latticeEmbedding x - mu‖`)
quadratic plus a constant `K` (both depending on `z` only through `mu := muOfShift Q_Im z`):
this is "completing the square" using `bound_gaussian_exponent`. -/
lemma reExponent_le (hn : n ≠ 0)
    (Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQIm_cont : Continuous Q_Im) (hQIm : Q_Im.PosDef)
    (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) :
    ∃ c K : ℝ, c > 0 ∧ ∀ x : Fin n → ℤ,
      -π * (latticeQuadraticMap Q_Im) x - 2 * π * (z x).im
        ≤ -c * ‖(toEuclidean_ZnRn) x - muOfShift Q_Im z‖ ^ 2 + K := by
  obtain ⟨c, d, hc, hbound⟩ :=
    bound_gaussian_exponent hn Q_Im hQIm_cont hQIm (muOfShift Q_Im z) 0
  refine ⟨c, π * Q_Im (muOfShift Q_Im z) - d, hc, fun x => ?_⟩
  have hsq := QuadraticMap.sub_eq_add_sub_polarBilin Q_Im
    ((toEuclidean_ZnRn) x) (muOfShift Q_Im z)
  rw [polarBilin_latticeEmbedding_muOfShift Q_Im hQIm z x] at hsq
  have hb := hbound ((toEuclidean_ZnRn) x)
  simp only [gaussianExponent, ContinuousMap.coe_mk, add_zero] at hb
  rw [hsq] at hb
  rw [latticeQuadraticMap_apply]
  linarith

/-- The shifted analogue of `summable_latticeNormSq_rpow`, over the *full* lattice `Fin n → ℤ`
(no need to exclude `x = 0`) and with an arbitrary shift `mu`, via `ZLattice.summable_norm_sub_rpow`
instead of `ZLattice.summable_norm_rpow`. -/
lemma summable_latticeNormSq_sub_rpow (mu : EuclideanSpace ℝ (Fin n)) {s : ℝ}
    (hs : (n : ℝ) / 2 < s) :
    Summable (fun x : Fin n → ℤ => (‖(toEuclidean_ZnRn) x - mu‖ ^ 2) ^ (-s)) := by
  have hr : (-2 * s : ℝ) < -(Module.finrank ℤ (stdLattice n) : ℝ) := by
    rw [finrank_stdLattice]; linarith
  have hinj : Function.Injective
      (fun x : Fin n → ℤ =>
        (⟨(toEuclidean_ZnRn) x, latticeEmbedding_mem_stdLattice x⟩ : stdLattice n)) :=
    fun x y h => latticeEmbedding_injective (Subtype.ext_iff.mp h)
  have key : ∀ x : Fin n → ℤ,
      ‖(⟨(toEuclidean_ZnRn) x, latticeEmbedding_mem_stdLattice x⟩ : stdLattice n).1 - mu‖
          ^ (-2 * s) =
        (‖(toEuclidean_ZnRn) x - mu‖ ^ 2) ^ (-s) := fun x => by
    show ‖(toEuclidean_ZnRn) x - mu‖ ^ (-2 * s) = (‖(toEuclidean_ZnRn) x - mu‖ ^ 2) ^ (-s)
    rw [show (-2 * s : ℝ) = 2 * (-s) by ring, Real.rpow_mul (norm_nonneg _),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact ((ZLattice.summable_norm_sub_rpow (stdLattice n) (-2 * s) hr mu).comp_injective hinj).congr
    key

/-- The decay rate `c > 0` from `reExponent_le`, named so that `to_compare_g` and
`comparison_eventual` below refer to the exact same term. -/
noncomputable def gaussianThetaRate (hn : n ≠ 0)
    (Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQIm_cont : Continuous Q_Im) (hQIm : Q_Im.PosDef)
    (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) : ℝ :=
  (reExponent_le hn Q_Im hQIm_cont hQIm z).choose

/-- The additive constant `K` from `reExponent_le`. -/
noncomputable def gaussianThetaConst (hn : n ≠ 0)
    (Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQIm_cont : Continuous Q_Im) (hQIm : Q_Im.PosDef)
    (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) : ℝ :=
  (reExponent_le hn Q_Im hQIm_cont hQIm z).choose_spec.choose

lemma gaussianThetaRate_pos (hn : n ≠ 0)
    (Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQIm_cont : Continuous Q_Im) (hQIm : Q_Im.PosDef)
    (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) :
    0 < gaussianThetaRate hn Q_Im hQIm_cont hQIm z :=
  (reExponent_le hn Q_Im hQIm_cont hQIm z).choose_spec.choose_spec.1

lemma gaussianThetaRate_bound (hn : n ≠ 0)
    (Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQIm_cont : Continuous Q_Im) (hQIm : Q_Im.PosDef)
    (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) (x : Fin n → ℤ) :
    -π * (latticeQuadraticMap Q_Im) x - 2 * π * (z x).im
      ≤ -gaussianThetaRate hn Q_Im hQIm_cont hQIm z * ‖(toEuclidean_ZnRn) x - muOfShift Q_Im z‖ ^ 2
        + gaussianThetaConst hn Q_Im hQIm_cont hQIm z :=
  (reExponent_le hn Q_Im hQIm_cont hQIm z).choose_spec.choose_spec.2 x

/-- The Riemann theta instance: any pair `(Q_Re, Q_Im)` of real quadratic forms on
`EuclideanSpace ℝ (Fin n)` with `Q_Im` positive definite (and continuous) makes the lattice
`Fin n → ℤ` theta-able, with the comparison function `to_compare_g` itself the Gaussian
`exp K * exp (-c * ‖latticeEmbedding x - mu‖²)` coming from `reExponent_le`. -/
@[reducible]
noncomputable def RiemannThetaAble
    (hn : n ≠ 0)
    (Q_Re Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQIm_cont : Continuous Q_Im) (hQIm : Q_Im.PosDef) :
    ThetaAbleQuadraticForm (R := ℤ) (M := Fin n → ℤ) where
  qRe := latticeQuadraticMap Q_Re
  qIm := latticeQuadraticMap Q_Im
  to_compare_g z x :=
    Real.exp (gaussianThetaConst hn Q_Im hQIm_cont hQIm z) *
      Real.exp (-gaussianThetaRate hn Q_Im hQIm_cont hQIm z *
        ‖(toEuclidean_ZnRn) x - muOfShift Q_Im z‖ ^ 2)
  to_compare_g_summable z := by
    set x_independent := rexp (gaussianThetaConst hn Q_Im hQIm_cont hQIm z)
    refine Summable.mul_left (a:=x_independent) ?key
    set a_const := gaussianThetaRate hn Q_Im hQIm_cont hQIm z
    have a_const_pos : 0 < a_const := gaussianThetaRate_pos hn Q_Im hQIm_cont hQIm z
    have key (pow : ℕ): ∀ᶠ (i : Fin n → ℤ) in cofinite,
      ‖rexp (-a_const * ‖((toEuclidean_ZnRn)) i - muOfShift Q_Im z‖ ^ 2)‖ ≤ ‖((toEuclidean_ZnRn)) i‖ ^ (-(pow : ℤ) - 1) := by
      exact gaussianVPolyDecay n pow a_const a_const_pos (shift:=muOfShift Q_Im z)
    have key := key (n)
    refine Summable.of_norm_bounded_eventually
      (f:=fun x => rexp (-a_const * ‖((toEuclidean_ZnRn)) x - muOfShift Q_Im z‖ ^ 2))
      (g:=fun x => ‖((toEuclidean_ZnRn)) x‖ ^ (-(n:ℤ) - 1))
      (hg := ?pow_sum)
      (h := key)
    · have hr : (-(n:ℤ) - 1) < -(Module.finrank ℤ (stdLattice n) : ℤ) := by
        rw [finrank_stdLattice]; omega
      have hinj : Function.Injective
          (fun x : Fin n → ℤ =>
            (⟨(toEuclidean_ZnRn) x, latticeEmbedding_mem_stdLattice x⟩ : stdLattice n)) :=
        fun x y h => latticeEmbedding_injective (Subtype.ext_iff.mp h)
      have key2 : ∀ x : Fin n → ℤ,
          ‖(⟨(toEuclidean_ZnRn) x, latticeEmbedding_mem_stdLattice x⟩ : stdLattice n).1‖
              ^ (-(n:ℤ) - 1) =
            ‖((toEuclidean_ZnRn)) x‖ ^ (-(n:ℤ) - 1) := fun x => by rfl
      exact ((ZLattice.summable_norm_zpow (stdLattice n) (-(n:ℤ) - 1) hr).comp_injective hinj).congr
        key2
  comparison_eventual z := Filter.Eventually.of_forall fun x => by
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hre : (↑π * Complex.I *
          (((latticeQuadraticMap Q_Re) x : ℝ) + Complex.I * ((latticeQuadraticMap Q_Im) x : ℝ))
        + 2 * (π : ℂ) * Complex.I * (z x)).re
        = -π * (latticeQuadraticMap Q_Im) x
          - 2 * π * (z x).im := by
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      ring
    rw [hre]
    have := gaussianThetaRate_bound hn Q_Im hQIm_cont hQIm z x
    linarith

end RiemannThetaAble

section JacobiTheta

/-- The canonical identification of the 1-dimensional `EuclideanSpace ℝ (Fin 1)` with `ℝ`,
via its unique coordinate. -/
noncomputable def euclidean1Equiv : EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).toLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℝ ℝ)

noncomputable def coord1 : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℝ := euclidean1Equiv.toLinearMap

lemma coord1_continuous : Continuous coord1 :=
  euclidean1Equiv.toContinuousLinearEquiv.continuous

/-- `x ↦ c * x²` (with `x` the unique coordinate of `EuclideanSpace ℝ (Fin 1)`), as a
`QuadraticMap`. -/
noncomputable def coordSqQuad (c : ℝ) : QuadraticMap ℝ (EuclideanSpace ℝ (Fin 1)) ℝ :=
  c • (QuadraticMap.sq.comp coord1)

lemma coordSqQuad_continuous (c : ℝ) : Continuous (coordSqQuad c) := by
  show Continuous (fun x => c * (coord1 x * coord1 x))
  fun_prop [coord1_continuous]

lemma coordSqQuad_eq_linMulLin (c : ℝ) :
    coordSqQuad c = c • QuadraticMap.linMulLin coord1 coord1 := by
  rw [coordSqQuad, QuadraticMap.sq, QuadraticMap.linMulLin_comp, LinearMap.id_comp]

lemma coordSqQuad_posDef {c : ℝ} (hc : 0 < c) : (coordSqQuad c).PosDef := by
  rw [coordSqQuad_eq_linMulLin]
  refine (QuadraticMap.linMulLinSelfPosDef coord1 ?_).smul hc
  exact LinearMap.ker_eq_bot.mpr euclidean1Equiv.injective

/-- The classical 1-dimensional Jacobi theta function `θ(z; τ) = theta_fun z`, with shift
`z : (Fin 1 → ℤ) →ₗ[ℤ] ℂ` and modulus `Q x = τ x²` (i.e. `Q = τ • sq`, the `n = 1`, `q = sq` case
of the `θ(z; τq)` slice from `sliceGaussianThetaAble`) for `τ` in the upper half-plane
(`0 < τ.im`), split into its real and imaginary parts `qRe x = τ.re * x²` and
`qIm x = τ.im * x²`. -/
@[reducible]
noncomputable def jacobiThetaAble (τ : ℂ) (hτ : 0 < τ.im) :
    ThetaAbleQuadraticForm (R := ℤ) (M := Fin 1 → ℤ) :=
  RiemannThetaAble (n := 1) one_ne_zero (coordSqQuad τ.re) (coordSqQuad τ.im)
    (coordSqQuad_continuous τ.im) (coordSqQuad_posDef hτ)

end JacobiTheta

section SliceGaussianTheta

variable {n : ℕ}

/-- The Riemann theta function `θ(z; Q) = theta_fun z`, with shift `z : M →ₗ[R] ℂ` and modulus
`Q = qRe + I qIm` ranging over the full Siegel upper half-space (any `qRe`, with `qIm` positive
definite), is restricted here to the *one-complex-parameter scalar slice* `Q = τ • q` through a
*fixed* positive definite integer quadratic form `q`, for `τ` in the upper half-plane (`0 < τ.im`):
`qRe = τ.re • q`, `qIm = τ.im • q`. So write `θ(z; τq)` for `theta_fun z` at this particular
instance, to keep `q` visible — it is *not* the general Siegel-point theta `θ(z; Q)`. This
generalizes `jacobiThetaAble` (the `n = 1` case, `q = sq`) to any such `q`, and connects this
theta machinery back to the zeta function work in `QuadraticFormZeta.lean`, via
`QuadraticFormUtils.lean`'s `gramQuadraticMap`/`posDefR`.
Keeping the full `τ`-dependence here
(rather than fixing `τ.re = 0`, the very
degenerate "Gaussian sum" case flagged in `ThetaAbleQuadraticForm`'s docstring) is what makes it
possible to even *pose* questions of modularity: `θ(0; τq) = theta_const` at this instance (`z`
fixed at `0`) is a function of `τ` alone, and modularity asks how it transforms under the action
of `SL(2, ℤ)` on `τ` in the upper half-plane (`τ ↦ τ + 1`, `τ ↦ -1/τ`, ...) — a different symmetry
from `tau_periodicity`/`one_periodicity`, which instead fix `τ` (equivalently `Q`) and vary the
shift `z` in `θ(z; τq)` (under such a modular transformation, `z`, if not fixed at `0`, would
itself need to transform along, e.g. `z ↦ z/(cτ+d)`, as for a Jacobi form; that transformation
law is not built here). The zeta Mellin transform below only needs `θ(0; itq)`, the
purely imaginary specialization `τ = it`, recovering `qRe = 0`, `qIm = t • q`. -/
@[reducible]
noncomputable def sliceGaussianThetaAble
    (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) (τ : ℂ) (hτ : 0 < τ.im) :
    ThetaAbleQuadraticForm (R := ℤ) (M := Fin n → ℤ) :=
  RiemannThetaAble hn (τ.re • gramQuadraticMap q) (τ.im • gramQuadraticMap q)
    ((gramQuadraticMap_continuous q).const_smul τ.im) ((posDefR q hq).smul hτ)

lemma sliceGaussianThetaAble_qRe_apply
    (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) (τ : ℂ) (hτ : 0 < τ.im)
    (x : Fin n → ℤ) :
    (sliceGaussianThetaAble hn q hq τ hτ).qRe x = τ.re * (q x : ℝ) := by
  show latticeQuadraticMap (τ.re • gramQuadraticMap q) x = τ.re * (q x : ℝ)
  rw [latticeQuadraticMap_apply, QuadraticMap.smul_apply, smul_eq_mul,
    show (toEuclidean_ZnRn) x = toEuclidean_ZnRn x from rfl, gramQuadraticMap_apply_toEuclidean]

lemma sliceGaussianThetaAble_qIm_apply
    (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) (τ : ℂ) (hτ : 0 < τ.im)
    (x : Fin n → ℤ) :
    (sliceGaussianThetaAble hn q hq τ hτ).qIm x = τ.im * (q x : ℝ) := by
  show latticeQuadraticMap (τ.im • gramQuadraticMap q) x = τ.im * (q x : ℝ)
  rw [latticeQuadraticMap_apply, QuadraticMap.smul_apply, smul_eq_mul,
    show (toEuclidean_ZnRn) x = toEuclidean_ZnRn x from rfl, gramQuadraticMap_apply_toEuclidean]

end SliceGaussianTheta

section ThetaZetaMellin

/-- The Mellin transform formula linking the zeta function `ζ_q(s)` of `q` (`QuadraticFormZeta.lean`)
to the theta sum `∑' x ≠ 0, exp (-π (q x) t)` (i.e. `θ(0; itq) - 1`, the `sliceGaussianThetaAble`
theta function at shift `z = 0` and purely imaginary `τ = it`, see
`sliceGaussianThetaAble_qRe_apply`/`sliceGaussianThetaAble_qIm_apply`):
`Γ(s) π⁻ˢ ζ_q(s) = ∫₀^∞ tˢ⁻¹ (θ(0; itq) - 1) dt`, valid for `s.re > n/2`, the convergence threshold
already required by `quadraticFormZetaAble`. The left side is `zeta_fun ⟨s, hs⟩` for the
`quadraticFormZetaAble hn q hq` instance, written out as its defining sum to avoid threading that
instance through named-argument elaboration.

Obtained from Mathlib's `hasSum_mellin_pi_mul` (`Mathlib.NumberTheory.LSeries.MellinEqDirichlet`),
the general "Mellin transform of a Dirichlet-type series" identity, applied with the constant
coefficient `1` at each nonzero lattice point and `q` itself as the base sequence: it supplies the
term-wise Gamma integral and the `∑'`/`∫` interchange. The genuinely quadratic-form-specific inputs
it still needs are a `HasSum` (not just `Summable`) witness for the Gaussian lattice sum at each `t`
(`hF`, via `sliceGaussianThetaAble`/`theta_fun_summable`) and the real-variable zeta convergence used
for `h_sum` (via `LowerBound_of_pythagorean_exists`/`summable_latticeNormSq_rpow`, as in
`quadraticFormZetaAble` itself; the `ZetaAbleQuadraticForm` class's `zeta_fun_summable` is avoided
here since it hits a `whnf` timeout from unfolding two `@[reducible]` instances together). -/
theorem zeta_eq_theta_mellin
    {n : ℕ} (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef)
    {s : ℂ} (hs : s.re > (n : ℝ) / 2) :
    Gamma s * (↑π : ℂ) ^ (-s) * ∑' x : {x : Fin n → ℤ // x ≠ 0}, ((q x.1 : ℤ) : ℂ) ^ (-s)
      = ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (t : ℂ) ^ (s - 1) *
            ∑' x : {x : Fin n → ℤ // x ≠ 0}, (Real.exp (-(π * (q x.1 : ℝ) * t)) : ℂ) := by
  have hs0 : 0 < s.re := lt_trans (by positivity) hs
  set F : ℝ → ℂ :=
    fun t => ∑' x : {x : Fin n → ℤ // x ≠ 0}, (Real.exp (-(π * (q x.1 : ℝ) * t)) : ℂ) with hF_def
  have hp : ∀ x : {x : Fin n → ℤ // x ≠ 0}, (1 : ℂ) = 0 ∨ 0 < (q x.1 : ℝ) :=
    fun x => Or.inr (by exact_mod_cast hq x.1 x.2)
  -- for each `t > 0`, the Gaussian lattice sum is a genuine `HasSum`, not just a `tsum`.
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun x : {x : Fin n → ℤ // x ≠ 0} =>
        (1 : ℂ) * (Real.exp (-π * (q x.1 : ℝ) * t) : ℂ)) (F t) := by
    intro t ht
    have hsumm : Summable
        (fun x : {x : Fin n → ℤ // x ≠ 0} => (Real.exp (-(π * (q x.1 : ℝ) * t)) : ℂ)) := by
      letI thetaable := sliceGaussianThetaAble hn q hq (t * Complex.I) (by simpa using ht)
      have hpt : ∀ x : Fin n → ℤ,
          Complex.exp (↑π * Complex.I *
              ((thetaable.qRe x : ℂ) + Complex.I * (thetaable.qIm x : ℂ))
              + 2 * ↑π * Complex.I * ((0 : (Fin n → ℤ) →ₗ[ℤ] ℂ) x))
            = (Real.exp (-(π * (q x : ℝ) * t)) : ℂ) := by
        intro x
        have hRe : thetaable.qRe x = 0 := by rw [sliceGaussianThetaAble_qRe_apply]; simp
        have hIm : thetaable.qIm x = t * (q x : ℝ) := by
          rw [sliceGaussianThetaAble_qIm_apply]; simp
        rw [hRe, hIm, LinearMap.zero_apply, mul_zero, add_zero, Complex.ofReal_zero, zero_add,
          Complex.ofReal_exp]
        congr 1
        have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
        push_cast
        linear_combination (↑π * ↑t * ((q x : ℤ) : ℂ)) * hII
      exact (ThetaAbleQuadraticForm.theta_fun_summable
        (0 : (Fin n → ℤ) →ₗ[ℤ] ℂ) (M := Fin n → ℤ)).congr hpt |>.comp_injective
        Subtype.coe_injective
    simpa [hF_def, neg_mul] using hsumm.hasSum
  -- the real-variable zeta convergence: same comparison to `latticeNormSq` used by
  -- `quadraticFormZetaAble` itself.
  have h_sum : Summable (fun x : {x : Fin n → ℤ // x ≠ 0} =>
      ‖(1 : ℂ)‖ / (q x.1 : ℝ) ^ s.re) := by
    simp only [norm_one]
    have hrw : ∀ x : {x : Fin n → ℤ // x ≠ 0},
        (1 : ℝ) / (q x.1 : ℝ) ^ s.re = (q x.1 : ℝ) ^ (-s.re) := fun x => by
      have hx : (0 : ℝ) < (q x.1 : ℝ) := by exact_mod_cast hq x.1 x.2
      rw [Real.rpow_neg hx.le, one_div]
    simp_rw [hrw]
    obtain ⟨c, hc_pos, hc_le⟩ := LowerBound_of_pythagorean_exists hn q hq
    have hc_summable := (summable_latticeNormSq_rpow hs).mul_left (c ^ (-s.re))
    refine Summable.of_nonneg_of_le
      (fun x => Real.rpow_nonneg (by exact_mod_cast (hq x.1 x.2).le) _)
      (fun x => ?_) hc_summable
    have hx : (0 : ℝ) < (q x.1 : ℝ) := by exact_mod_cast hq x.1 x.2
    have hnsq_pos : (0 : ℝ) < latticeNormSq x.1 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp x.2
      exact Finset.sum_pos' (fun k _ => sq_nonneg _)
        ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (by exact_mod_cast hj)⟩
    rw [← Real.mul_rpow hc_pos.le hnsq_pos.le]
    have hble : c * latticeNormSq x.1 ≤ (q x.1 : ℝ) := hc_le x.1
    rw [Real.rpow_neg hx.le, Real.rpow_neg (mul_pos hc_pos hnsq_pos).le]
    gcongr
  have htsum := (hasSum_mellin_pi_mul hp hs0 hF h_sum).tsum_eq
  have hmellin : mellin F s = ∫ t : ℝ in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * F t := by
    simp [mellin, smul_eq_mul]
  rw [hmellin] at htsum
  rw [← htsum, ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  have hx : (0 : ℝ) < (q x.1 : ℝ) := by exact_mod_cast hq x.1 x.2
  rw [show ((q x.1 : ℤ) : ℂ) = ((q x.1 : ℝ) : ℂ) by push_cast; ring,
    Complex.cpow_neg, Complex.cpow_neg, mul_one, div_eq_mul_inv]
  ring

section TsumSplitPoint

variable {ι : Type*} [DecidableEq ι] {f : ι → ℂ}

/-- `ι` splits as the chosen point `a` together with everything else. -/
private def equivUnitSumSubtypeNe (a : ι) : ι ≃ Unit ⊕ {x : ι // x ≠ a} where
  toFun x := if h : x = a then Sum.inl () else Sum.inr ⟨x, h⟩
  invFun := Sum.elim (fun _ => a) Subtype.val
  left_inv x := by by_cases h : x = a <;> simp [h]
  right_inv := by
    rintro (⟨⟩ | ⟨x, hx⟩)
    · simp
    · simp [hx]

/-- Splitting a summable series off at a single point `a`: the full sum is `f a` plus the sum
over everything else. -/
theorem tsum_eq_apply_add_tsum_ne (hf : Summable f) (a : ι) :
    ∑' x, f x = f a + ∑' x : {x : ι // x ≠ a}, f x.1 := by
  rw [← Equiv.tsum_eq (equivUnitSumSubtypeNe a).symm f]
  have h1 : Summable ((fun c => f ((equivUnitSumSubtypeNe a).symm c)) ∘
      (Sum.inl : Unit → Unit ⊕ {x : ι // x ≠ a})) :=
    (hasSum_fintype (fun _ : Unit => f a)).summable
  have h2 : Summable ((fun c => f ((equivUnitSumSubtypeNe a).symm c)) ∘
      (Sum.inr : {x : ι // x ≠ a} → Unit ⊕ {x : ι // x ≠ a})) :=
    hf.comp_injective Subtype.coe_injective
  rw [Summable.tsum_sum h1 h2]
  congr 1
  rw [tsum_fintype]
  simp [equivUnitSumSubtypeNe]

end TsumSplitPoint

open ThetaAbleQuadraticForm ZetaAbleQuadraticForm

/-- `θ(0; itq) = theta_const` for `sliceGaussianThetaAble` at shift `z = 0` and the purely
imaginary modulus `τ = it` (`t > 0`), minus the constant `1` contributed by the zero lattice
point, is the same Gaussian sum over nonzero lattice points used in
`zeta_eq_theta_mellin`. -/
lemma sliceGaussianThetaAble_theta_const_sub_one
    {n : ℕ} (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) (t : ℝ) (ht : 0 < t) :
    letI thetaable := sliceGaussianThetaAble hn q hq (t * Complex.I) (by simpa using ht)
    (theta_const (R := ℤ) (M := Fin n → ℤ) - 1 : ℂ)
      = ∑' x : {x : Fin n → ℤ // x ≠ 0}, (Real.exp (-(π * (q x.1 : ℝ) * t)) : ℂ) := by
  letI thetaable := sliceGaussianThetaAble hn q hq (t * Complex.I) (by simpa using ht)
  set F : (Fin n → ℤ) → ℂ := fun x =>
    Complex.exp (↑π * Complex.I * ((thetaable.qRe x : ℂ) + Complex.I * (thetaable.qIm x : ℂ))
      + 2 * ↑π * Complex.I * ((0 : (Fin n → ℤ) →ₗ[ℤ] ℂ) x)) with hF
  have hpt : ∀ x : Fin n → ℤ, F x = (Real.exp (-(π * (q x : ℝ) * t)) : ℂ) := by
    intro x
    simp only [hF]
    have hRe : thetaable.qRe x = 0 := by rw [sliceGaussianThetaAble_qRe_apply]; simp
    have hIm : thetaable.qIm x = t * (q x : ℝ) := by rw [sliceGaussianThetaAble_qIm_apply]; simp
    rw [hRe, hIm, LinearMap.zero_apply, mul_zero, add_zero, Complex.ofReal_zero, zero_add,
      Complex.ofReal_exp]
    congr 1
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (↑π * ↑t * ((q x : ℤ) : ℂ)) * hII
  have hsum : (theta_const (R := ℤ) (M := Fin n → ℤ) : ℂ)
      = F 0 + ∑' x : {x : Fin n → ℤ // x ≠ 0}, F x.1 := by
    simp only [theta_const, theta_fun, hF]
    exact tsum_eq_apply_add_tsum_ne (theta_fun_summable (0 : (Fin n → ℤ) →ₗ[ℤ] ℂ)) 0
  rw [hsum, hpt 0]
  have hq0 : (q (0 : Fin n → ℤ) : ℝ) = 0 := by exact_mod_cast q.map_zero
  rw [hq0, mul_zero, zero_mul, neg_zero, Real.exp_zero, Complex.ofReal_one,
    tsum_congr (fun x : {x : Fin n → ℤ // x ≠ 0} => hpt x.1)]
  ring

/-- `s.re > n/2` is exactly membership in `(quadraticFormZetaAble hn q hq).domain` (whose bound is
`n/2` by definition); isolated here so the construction of `⟨s, ·⟩ : zetaable.domain` doesn't
have to be repeated at both the statement and proof of `zeta_eq_theta_mellin'`. -/
lemma quadraticFormZetaAble_mem_domain
    {n : ℕ} (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef)
    {s : ℂ} (hs : s.re > (n : ℝ) / 2) : s ∈ (quadraticFormZetaAble hn q hq).domain := by
  show s.re > (quadraticFormZetaAble hn q hq).s_bound
  rwa [show (quadraticFormZetaAble hn q hq).s_bound = (n : ℝ) / 2 from rfl]

/-- `zeta_eq_theta_mellin`, restated with `zeta_fun`/`theta_const` directly: for
`s.re > n/2`, `Γ(s) π⁻ˢ ζ_q(s) = ∫₀^∞ tˢ⁻¹ (θ(0; itq) - 1) dt` where `θ(0; itq) = theta_const` is
`sliceGaussianThetaAble` at shift `z = 0` and the purely imaginary modulus `τ = it`. The relevant
`ZetaAbleQuadraticForm`/`ThetaAbleQuadraticForm` instances are introduced via `letI` (instance
arguments cannot be supplied by name), and the theta integrand uses a `dif` to discharge the
`0 < t` side condition `sliceGaussianThetaAble` needs, pointwise on `t ∈ Set.Ioi 0`. -/
theorem zeta_eq_theta_mellin'
    {n : ℕ} (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef)
    {s : ℂ} (hs : s.re > (n : ℝ) / 2) :
    letI zetaable := quadraticFormZetaAble hn q hq
    Gamma s * (↑π : ℂ) ^ (-s) *
      zeta_fun (⟨s, quadraticFormZetaAble_mem_domain hn q hq hs⟩ : zetaable.domain) =
      ∫ t : ℝ in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) *
        if ht : 0 < t then
          letI thetaable := sliceGaussianThetaAble hn q hq (t * Complex.I) (by simpa using ht)
          (theta_const (R := ℤ) (M := Fin n → ℤ) - 1 : ℂ)
        else 0 := by
  letI zetaable := quadraticFormZetaAble hn q hq
  have hzeta : zeta_fun (⟨s, quadraticFormZetaAble_mem_domain hn q hq hs⟩ : zetaable.domain)
      = ∑' x : {x : Fin n → ℤ // x ≠ 0}, ((q x.1 : ℤ) : ℂ) ^ (-s) := rfl
  rw [hzeta, zeta_eq_theta_mellin hn q hq hs]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [dif_pos (Set.mem_Ioi.mp ht), sliceGaussianThetaAble_theta_const_sub_one hn q hq t
    (Set.mem_Ioi.mp ht)]

end ThetaZetaMellin
