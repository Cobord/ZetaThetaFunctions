import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import ZetaThetaFunctions.SiegelUpperHalfSpace

/-!
# Rank-`g` Poisson summation for a Gaussian

The matrix generalization of `Complex.tsum_exp_neg_quadratic`
(`Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`), needed as the missing analytic
ingredient behind the `S_g` Siegel modular transformation law
(`ZetaFunctions/SiegelModular.lean`, `section ThetaTransformSMatrix`) and the Epstein zeta
functional equation; see `ZetaFunctions/PoissonSummationPlan.md` for the gap analysis and the
reduction of both targets to this statement.

## The branch of `(det A)^(1/2)`

The naive `A.det ^ (1/2 : ℂ)` (`Complex.cpow`, principal branch, cut along the negative reals) is
*not* a valid choice of square root for `g ≥ 3`: writing `A = R(I + iS)R` with `R` the PosDef square
root of `Re A` and `S` real symmetric (via congruence), `arg (A.det) = ∑ arg (1 + i λₖ)` over the
eigenvalues `λₖ` of `S`, each term strictly inside `(-π/2, π/2)`. For `g ≤ 2` the sum is forced
strictly inside `(-π, π)`, so `A.det` never touches the branch cut and `cpow` is safe (this is
exactly why Mathlib's scalar `Complex.tsum_exp_neg_quadratic`, i.e. `g = 1`, needs no such care).
For `g ≥ 3` the sum can exceed `π` in absolute value (e.g. `A = (1 + it) • (1 : Matrix (Fin 3) ..)`
crosses the cut at `t = √3`, where `A.det = (1 + i√3)^3 = -8`), so `cpow` jumps by a sign relative
to the true continuously-varying square root, while the sum-side of the identity (manifestly
continuous in `A`) cannot jump — so the naive statement is genuinely false there, not merely hard.

`pivotSqrt` below fixes this: it is the product of the principal-branch square roots of the pivots
produced by repeated one-coordinate Schur complementation (`schurStepLast`), i.e. a "plain-transpose
LDL-decomposition" (not Mathlib's `Mathlib.Analysis.Matrix.LDL`, which is for `IsHermitian`/`PosDef`
matrices under `Mᴴ`, whereas `A` here is only `IsSymm`/`Mᵀ`). Each pivot individually has positive
real part (inherited from `Re A ≻ 0` via `schurStepLast_re_posDef`), so each individual `cpow` is
branch-safe by the `g = 1` argument above, and `pivotSqrt_sq` shows the product squares to `A.det` —
matching the naive `cpow` whenever that one happens to be safe (`g ≤ 2`), but remaining correct and
well-defined for all `g`.
-/

open Complex
open scoped Real

variable {g : ℕ}

/-- One step of symmetric (plain-transpose, not conjugate-transpose) Gaussian elimination: the
Schur complement of `A` with respect to its bottom-right corner `A (last) (last)`. -/
noncomputable def schurStepLast {g : ℕ} (A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  fun i j => A i.castSucc j.castSucc -
    A i.castSucc (Fin.last g) * A (Fin.last g) j.castSucc / A (Fin.last g) (Fin.last g)

/-- The correctly-branched square root of `A.det`, for `A` symmetric with `Re A ≻ 0`: the product
of the principal-branch square roots of the pivots of repeated `schurStepLast`. See the module
docstring for why this differs from (and is well-defined where) `A.det ^ (1/2 : ℂ)` is not. -/
noncomputable def pivotSqrt : (g : ℕ) → Matrix (Fin g) (Fin g) ℂ → ℂ
  | 0, _ => 1
  | g + 1, A => A (Fin.last g) (Fin.last g) ^ (1 / 2 : ℂ) * pivotSqrt g (schurStepLast A)

lemma schurStepLast_isSymm {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ} (hA : A.IsSymm) :
    (schurStepLast A).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, schurStepLast]
  rw [hA.apply i.castSucc j.castSucc, hA.apply (Fin.last g) j.castSucc,
    hA.apply i.castSucc (Fin.last g)]
  ring

/-- For `c a : ℂ` with `0 < a.re`, `(c^2/a).re ≤ c.re^2 / a.re`. The numeric core of
`schurStepLast_re_posDef`: completing the square in the *real* direction only recovers `c.re^2/a.re`
(from `Re A ≻ 0` applied to a real vector), which this shows dominates the true complex quantity
`Re(c^2/a)`; the gap is exactly the perfect square `(c.re * a.im - c.im * a.re)^2 ≥ 0`. -/
private lemma re_sq_div_le (c a : ℂ) (ha : 0 < a.re) : (c ^ 2 / a).re ≤ c.re ^ 2 / a.re := by
  have hane : a ≠ 0 := fun h => by simp [h] at ha
  have hnsq : (0 : ℝ) < Complex.normSq a := Complex.normSq_pos.mpr hane
  have hns : Complex.normSq a = a.re * a.re + a.im * a.im := Complex.normSq_apply a
  rw [sq, Complex.div_re, Complex.mul_re, Complex.mul_im, ← add_div, div_le_div_iff₀ hnsq ha]
  nlinarith [sq_nonneg (c.re * a.im - c.im * a.re), hns]

/-- The hard analytic ingredient: one-coordinate Schur complementation of a symmetric complex
matrix preserves positive-definiteness of the real part. Elementary direct proof: extend a real
test vector `x` for the Schur complement to `y = Fin.snoc x t` with `t := -(∑ v i * x i).re / a.re`
(`v` the eliminated column, `a` the pivot); `Re A ≻ 0` applied to `y` gives a real quadratic
inequality that, combined with `re_sq_div_le`, dominates the genuinely complex quantity appearing
in the Schur complement's quadratic form. -/
lemma schurStepLast_re_posDef {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ} (hA : A.IsSymm)
    (hRe : (A.map Complex.re).PosDef) :
    ((schurStepLast A).map Complex.re).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.isHermitian_iff_isSymm]
    exact (schurStepLast_isSymm hA).map _
  · intro x hx
    set a : ℂ := A (Fin.last g) (Fin.last g) with ha_def
    have hα : 0 < a.re := by
      have hdiag := hRe.diag_pos (i := Fin.last g)
      simpa [Matrix.map_apply, ha_def] using hdiag
    set v : Fin g → ℂ := fun i => A i.castSucc (Fin.last g) with hv_def
    set c : ℂ := ∑ i, v i * (x i : ℂ) with hc_def
    set t : ℝ := -c.re / a.re with ht_def
    set y : Fin (g + 1) → ℝ := Fin.snoc x t with hy_def
    have hyne : y ≠ 0 := by
      intro h
      apply hx
      funext i
      have hxi := congrFun h i.castSucc
      simpa [hy_def, Fin.snoc_castSucc] using hxi
    have hpos := hRe.dotProduct_mulVec_pos hyne
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply,
      Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hy_def] at hpos
    have hcre' : c.re = ∑ i, (A i.castSucc (Fin.last g)).re * x i := by
      rw [hc_def, Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hv_def]; simp [Complex.mul_re]
    have hsymm : ∀ j : Fin g, (A (Fin.last g) j.castSucc).re = (A j.castSucc (Fin.last g)).re :=
      fun j => by rw [hA.apply j.castSucc (Fin.last g)]
    have e1 : ∑ i : Fin g, x i * (∑ j : Fin g, (A i.castSucc j.castSucc).re * x j +
          (A i.castSucc (Fin.last g)).re * t) =
        (∑ i, ∑ j, x i * x j * (A i.castSucc j.castSucc).re) + t * c.re := by
      rw [hcre', Finset.mul_sum]
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : t * (∑ j : Fin g, (A (Fin.last g) j.castSucc).re * x j +
          (A (Fin.last g) (Fin.last g)).re * t) =
        t * c.re + t ^ 2 * a.re := by
      have hcre'' : ∑ j : Fin g, (A (Fin.last g) j.castSucc).re * x j = c.re := by
        rw [hcre']
        exact Finset.sum_congr rfl fun j _ => by rw [hsymm j]
      rw [mul_add, hcre'', ← ha_def]
      ring
    have hexpand_y : ∑ i : Fin g, x i * (∑ j : Fin g, (A i.castSucc j.castSucc).re * x j +
          (A i.castSucc (Fin.last g)).re * t) +
        t * (∑ j : Fin g, (A (Fin.last g) j.castSucc).re * x j + (A (Fin.last g)
          (Fin.last g)).re * t) =
        (∑ i, ∑ j, x i * x j * (A i.castSucc j.castSucc).re) + 2 * t * c.re + t ^ 2 * a.re := by
      rw [e1, e2]; ring
    rw [hexpand_y] at hpos
    have ht2 : 2 * t * c.re + t ^ 2 * a.re = -(c.re ^ 2 / a.re) := by
      rw [ht_def]; field_simp; ring
    rw [show ∑ i, ∑ j, x i * x j * (A i.castSucc j.castSucc).re + 2 * t * c.re + t ^ 2 * a.re
        = ∑ i, ∑ j, x i * x j * (A i.castSucc j.castSucc).re + (2 * t * c.re + t ^ 2 * a.re) from
        by ring, ht2] at hpos
    have hquad : (c ^ 2 / a).re = ∑ i, ∑ j, x i * x j * (v i * v j / a).re := by
      have hc2 : c ^ 2 = ∑ i, ∑ j, (x i : ℂ) * (x j : ℂ) * (v i * v j) := by
        rw [hc_def, sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hc2, Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (x i : ℂ) * (x j : ℂ) * (v i * v j) / a
          = ((x i * x j : ℝ) : ℂ) * (v i * v j / a) from by push_cast; ring]
      simp [Complex.mul_re]
    have hentry : ∀ i j : Fin g, x i * x j * (schurStepLast A i j).re =
        x i * x j * (A i.castSucc j.castSucc).re - x i * x j * (v i * v j / a).re := by
      intro i j
      have hij : schurStepLast A i j = A i.castSucc j.castSucc - v i * v j / a := by
        show A i.castSucc j.castSucc - A i.castSucc (Fin.last g) * A (Fin.last g) j.castSucc / a
            = A i.castSucc j.castSucc - v i * v j / a
        rw [hv_def, hA.apply j.castSucc (Fin.last g)]
      rw [hij, Complex.sub_re, mul_sub]
    have hunfold : x ⬝ᵥ ((schurStepLast A).map Complex.re).mulVec x =
        ∑ i, ∑ j, x i * x j * (schurStepLast A i j).re := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hgoal : x ⬝ᵥ ((schurStepLast A).map Complex.re).mulVec x =
        (∑ i, ∑ j, x i * x j * (A i.castSucc j.castSucc).re) - (c ^ 2 / a).re := by
      rw [hunfold]
      simp only [hentry, Finset.sum_sub_distrib]
      rw [← hquad]
    rw [star_trivial, hgoal]
    have hle := re_sq_div_le c a hα
    linarith

/-- Determinant Schur identity for one-coordinate elimination: `A.det` factors as the pivot times
the determinant of the Schur complement. Needs `A (last) (last) ≠ 0`, which in our application
follows from `schurStepLast_re_posDef`'s hypothesis via `Matrix.PosDef.diag_pos`. -/
lemma det_eq_pivot_mul_det_schurStepLast {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (ha : A (Fin.last g) (Fin.last g) ≠ 0) :
    A.det = A (Fin.last g) (Fin.last g) * (schurStepLast A).det := by
  classical
  set A₁₁ : Matrix (Fin g) (Fin g) ℂ := fun i j => A i.castSucc j.castSucc with hA₁₁
  set A₁₂ : Matrix (Fin g) (Fin 1) ℂ := fun i _ => A i.castSucc (Fin.last g) with hA₁₂
  set A₂₁ : Matrix (Fin 1) (Fin g) ℂ := fun _ j => A (Fin.last g) j.castSucc with hA₂₁
  set A₂₂ : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => A (Fin.last g) (Fin.last g) with hA₂₂
  have hcast : ∀ i : Fin g, finSumFinEquiv (Sum.inl i : Fin g ⊕ Fin 1) = i.castSucc := by
    intro i
    rw [finSumFinEquiv_apply_left]
    rfl
  have hlast : finSumFinEquiv (Sum.inr (0 : Fin 1)) = Fin.last g := by
    have h := congrArg finSumFinEquiv (finSumFinEquiv_symm_last (n := g))
    rwa [Equiv.apply_symm_apply] at h
  have hblock : A.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hA₁₁, hA₁₂, hA₂₁, hA₂₂,
        hcast, Fin.eq_zero, hlast]
  have hdetA : A.det = (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).det := by
    rw [← hblock, Matrix.det_submatrix_equiv_self]
  have hA22det : A₂₂.det = A (Fin.last g) (Fin.last g) := by
    rw [hA₂₂, Matrix.det_fin_one]
  have hA22unit : IsUnit A₂₂ := by
    rw [Matrix.isUnit_iff_isUnit_det, hA22det]
    exact ha.isUnit
  haveI : Invertible A₂₂ := hA22unit.invertible
  have hA22inv : A₂₂⁻¹ = fun _ _ => (A (Fin.last g) (Fin.last g))⁻¹ := by
    apply Matrix.inv_eq_right_inv
    ext i j
    have : (i : Fin 1) = 0 := Fin.eq_zero i
    have hj : (j : Fin 1) = 0 := Fin.eq_zero j
    simp [Matrix.mul_apply, Matrix.one_apply, this, hj, hA₂₂,
      mul_inv_cancel₀ ha]
  have hschur : A₁₁ - A₁₂ * A₂₂⁻¹ * A₂₁ = schurStepLast A := by
    rw [hA22inv]
    ext i j
    simp only [hA₁₁, hA₁₂, hA₂₁, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one,
      schurStepLast, div_eq_mul_inv]
    ring
  rw [hdetA, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv, hA22det, hschur]

/-- Block-inverse Schur identity: `A⁻¹`'s entries in terms of `(schurStepLast A)⁻¹` and the pivot.
The genuinely new ingredient (beyond `det_eq_pivot_mul_det_schurStepLast`) needed for the `S_g`
Poisson summation induction: after one 1-D Poisson summation step, the dual quadratic form must be
matched against `A⁻¹` itself, not just `A.det`. -/
lemma matrix_inv_blocks {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (ha : A (Fin.last g) (Fin.last g) ≠ 0) (hA'' : (schurStepLast A).det ≠ 0) :
    (∀ i j : Fin g, A⁻¹ i.castSucc j.castSucc = (schurStepLast A)⁻¹ i j) ∧
      (∀ i : Fin g, A⁻¹ i.castSucc (Fin.last g) =
        -(∑ l, (schurStepLast A)⁻¹ i l * A l.castSucc (Fin.last g)) /
          A (Fin.last g) (Fin.last g)) ∧
      (∀ j : Fin g, A⁻¹ (Fin.last g) j.castSucc =
        -(∑ l, A (Fin.last g) l.castSucc * (schurStepLast A)⁻¹ l j) /
          A (Fin.last g) (Fin.last g)) ∧
      A⁻¹ (Fin.last g) (Fin.last g) = 1 / A (Fin.last g) (Fin.last g) +
        (∑ i, ∑ j, A (Fin.last g) i.castSucc * (schurStepLast A)⁻¹ i j *
          A j.castSucc (Fin.last g)) / A (Fin.last g) (Fin.last g) ^ 2 := by
  classical
  set A₁₁ : Matrix (Fin g) (Fin g) ℂ := fun i j => A i.castSucc j.castSucc with hA₁₁
  set A₁₂ : Matrix (Fin g) (Fin 1) ℂ := fun i _ => A i.castSucc (Fin.last g) with hA₁₂
  set A₂₁ : Matrix (Fin 1) (Fin g) ℂ := fun _ j => A (Fin.last g) j.castSucc with hA₂₁
  set A₂₂ : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => A (Fin.last g) (Fin.last g) with hA₂₂
  have hcast : ∀ i : Fin g, finSumFinEquiv (Sum.inl i : Fin g ⊕ Fin 1) = i.castSucc := by
    intro i; rw [finSumFinEquiv_apply_left]; rfl
  have hlast : finSumFinEquiv (Sum.inr (0 : Fin 1)) = Fin.last g := by
    have h := congrArg finSumFinEquiv (finSumFinEquiv_symm_last (n := g))
    rwa [Equiv.apply_symm_apply] at h
  have hblock : A.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hA₁₁, hA₁₂, hA₂₁, hA₂₂,
        hcast, Fin.eq_zero, hlast]
  have hA22det : A₂₂.det = A (Fin.last g) (Fin.last g) := by rw [hA₂₂, Matrix.det_fin_one]
  have hA22unit : IsUnit A₂₂ := by
    rw [Matrix.isUnit_iff_isUnit_det, hA22det]; exact ha.isUnit
  haveI hA22 : Invertible A₂₂ := hA22unit.invertible
  have hA22inv : A₂₂⁻¹ = fun _ _ => (A (Fin.last g) (Fin.last g))⁻¹ := by
    apply Matrix.inv_eq_right_inv
    ext i j
    have hi : (i : Fin 1) = 0 := Fin.eq_zero i
    have hj : (j : Fin 1) = 0 := Fin.eq_zero j
    simp [Matrix.mul_apply, Matrix.one_apply, hi, hj, hA₂₂, mul_inv_cancel₀ ha]
  have hschur : A₁₁ - A₁₂ * A₂₂⁻¹ * A₂₁ = schurStepLast A := by
    rw [hA22inv]
    ext i j
    simp only [hA₁₁, hA₁₂, hA₂₁, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one,
      schurStepLast, div_eq_mul_inv]
    ring
  rw [← Matrix.invOf_eq_nonsing_inv] at hschur
  have hSchurUnit : IsUnit (A₁₁ - A₁₂ * ⅟A₂₂ * A₂₁).det := by rw [hschur]; exact hA''.isUnit
  haveI hSchurInv : Invertible (A₁₁ - A₁₂ * ⅟A₂₂ * A₂₁) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hSchurUnit |>.invertible
  haveI hFB : Invertible (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) :=
    Matrix.fromBlocks₂₂Invertible A₁₁ A₁₂ A₂₁ A₂₂
  have hinvblock := Matrix.invOf_fromBlocks₂₂_eq A₁₁ A₁₂ A₂₁ A₂₂
  rw [Matrix.invOf_eq_nonsing_inv] at hinvblock
  have hAinv_sub : A⁻¹.submatrix finSumFinEquiv finSumFinEquiv =
      (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv, hblock]
  rw [hinvblock, Matrix.invOf_eq_nonsing_inv, Matrix.invOf_eq_nonsing_inv] at hAinv_sub
  rw [Matrix.invOf_eq_nonsing_inv] at hschur
  rw [hschur] at hAinv_sub
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    have h1 := congrFun (congrFun hAinv_sub (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.submatrix_apply, hcast, Matrix.fromBlocks_apply₁₁] using h1
  · intro i
    have h1 := congrFun (congrFun hAinv_sub (Sum.inl i)) (Sum.inr 0)
    simp only [Matrix.submatrix_apply, hcast, hlast, Matrix.fromBlocks_apply₁₂] at h1
    rw [h1]
    simp only [Matrix.neg_apply, Matrix.mul_apply, hA22inv, hA₁₂, Fin.sum_univ_one, div_eq_mul_inv]
    ring
  · intro j
    have h1 := congrFun (congrFun hAinv_sub (Sum.inr 0)) (Sum.inl j)
    simp only [Matrix.submatrix_apply, hcast, hlast, Matrix.fromBlocks_apply₂₁] at h1
    rw [h1]
    simp only [Matrix.neg_apply, Matrix.mul_apply, hA22inv, hA₂₁, Fin.sum_univ_one, div_eq_mul_inv]
    rw [neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  · have h1 := congrFun (congrFun hAinv_sub (Sum.inr 0)) (Sum.inr 0)
    simp only [Matrix.submatrix_apply, hlast, Matrix.fromBlocks_apply₂₂] at h1
    rw [h1]
    simp only [Matrix.add_apply, Matrix.mul_apply, hA22inv, hA₁₂, hA₂₁, Fin.sum_univ_one,
      div_eq_mul_inv]
    have key : ∑ x, (∑ x_1, (A (Fin.last g) (Fin.last g))⁻¹ * A (Fin.last g) x_1.castSucc *
          (schurStepLast A)⁻¹ x_1 x) * A x.castSucc (Fin.last g) =
        (A (Fin.last g) (Fin.last g))⁻¹ *
          ∑ i, ∑ j, A (Fin.last g) i.castSucc * (schurStepLast A)⁻¹ i j *
            A j.castSucc (Fin.last g) := by
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x_1 _ => by ring
    rw [key]
    ring

lemma pivotSqrt_sq (g : ℕ) (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsSymm)
    (hRe : (A.map Complex.re).PosDef) :
    pivotSqrt g A ^ 2 = A.det := by
  induction g with
  | zero => simp [pivotSqrt, Matrix.det_fin_zero]
  | succ g ih =>
    have hpivotRe : 0 < (A (Fin.last g) (Fin.last g)).re := hRe.diag_pos
    have hpivot : A (Fin.last g) (Fin.last g) ≠ 0 := fun h => by simp [h] at hpivotRe
    have hA' := schurStepLast_isSymm (A := A) hA
    have hRe' := schurStepLast_re_posDef (A := A) hA hRe
    rw [pivotSqrt, mul_pow]
    have hsq : (A (Fin.last g) (Fin.last g) ^ (1 / 2 : ℂ)) ^ 2 = A (Fin.last g) (Fin.last g) := by
      have h2 : (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ := by norm_num
      rw [h2]
      exact Complex.cpow_nat_inv_pow (A (Fin.last g) (Fin.last g)) (two_ne_zero)
    rw [hsq, ih (schurStepLast A) hA' hRe', det_eq_pivot_mul_det_schurStepLast hpivot]

lemma pivotSqrt_ne_zero (g : ℕ) (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsSymm)
    (hRe : (A.map Complex.re).PosDef) :
    pivotSqrt g A ≠ 0 := by
  induction g with
  | zero => simp [pivotSqrt]
  | succ g ih =>
    have hpivotRe : 0 < (A (Fin.last g) (Fin.last g)).re := hRe.diag_pos
    have hpivot : A (Fin.last g) (Fin.last g) ≠ 0 := fun h => by simp [h] at hpivotRe
    have hA' := schurStepLast_isSymm (A := A) hA
    have hRe' := schurStepLast_re_posDef (A := A) hA hRe
    rw [pivotSqrt]
    exact mul_ne_zero ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hpivot)
      (ih (schurStepLast A) hA' hRe')

private lemma tsum_fin_zero_eq (f : (Fin 0 → ℤ) → ℂ) : ∑' n, f n = f default :=
  tsum_eq_single default fun b' hb' => (hb' (Subsingleton.elim b' default)).elim

/-- Splitting the rank-`(g+1)` quadratic form's exponent along `n = Fin.snoc n' k`: the
double sum over `Fin (g+1)` decomposes into the `Fin g`-quadratic part (in the top-left block),
a linear cross term in `k` (via the eliminated column, using `A`'s symmetry to combine the two
cross-term contributions), and the pure `k²` pivot term. Pure algebra, no analysis. -/
private lemma quadratic_exponent_split {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (hA : A.IsSymm) (n' : Fin g → ℤ) (k : ℤ) :
    ∑ i, ∑ j, A i j * ((Fin.snoc n' k : Fin (g + 1) → ℤ) i : ℂ) *
        ((Fin.snoc n' k : Fin (g + 1) → ℤ) j : ℂ) =
      (∑ i, ∑ j, A i.castSucc j.castSucc * (n' i : ℂ) * (n' j : ℂ)) +
        2 * (k : ℂ) * (∑ i, A i.castSucc (Fin.last g) * (n' i : ℂ)) +
        A (Fin.last g) (Fin.last g) * (k : ℂ) ^ 2 := by
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have hsymm : ∀ j : Fin g, A (Fin.last g) j.castSucc = A j.castSucc (Fin.last g) :=
    fun j => hA.apply j.castSucc (Fin.last g)
  simp only [hsymm, Finset.sum_add_distrib]
  have hL1 : ∑ x : Fin g, A x.castSucc (Fin.last g) * (n' x : ℂ) * (k : ℂ)
      = (k : ℂ) * ∑ x : Fin g, A x.castSucc (Fin.last g) * (n' x : ℂ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  have hL2 : ∑ x : Fin g, A x.castSucc (Fin.last g) * (k : ℂ) * (n' x : ℂ)
      = (k : ℂ) * ∑ x : Fin g, A x.castSucc (Fin.last g) * (n' x : ℂ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  rw [hL1, hL2]
  ring

/-- Splitting the rank-`(g+1)` linear shift term along `n = Fin.snoc n' k`. Pure algebra. -/
private lemma linear_split {g : ℕ} (b : Fin (g + 1) → ℂ) (n' : Fin g → ℤ) (k : ℤ) :
    ∑ i, b i * ((Fin.snoc n' k : Fin (g + 1) → ℤ) i : ℂ) =
      (∑ i, b i.castSucc * (n' i : ℂ)) + b (Fin.last g) * (k : ℂ) := by
  simp [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The Schur complement's quadratic form is the original one with the rank-one correction from
completing the square in the last coordinate subtracted off. Pure algebra (uses `hA` only to
identify the two symmetric halves of `schurStepLast`'s cross term). -/
private lemma schurStepLast_quadratic_eq {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (hA : A.IsSymm) (w : Fin g → ℂ) :
    ∑ i, ∑ j, (schurStepLast A) i j * w i * w j =
      (∑ i, ∑ j, A i.castSucc j.castSucc * w i * w j) -
        (∑ i, A i.castSucc (Fin.last g) * w i) ^ 2 / A (Fin.last g) (Fin.last g) := by
  have hentry : ∀ i j : Fin g, (schurStepLast A) i j * w i * w j =
      A i.castSucc j.castSucc * w i * w j -
        (A i.castSucc (Fin.last g) * w i) * (A j.castSucc (Fin.last g) * w j) /
          A (Fin.last g) (Fin.last g) := by
    intro i j
    have hij : schurStepLast A i j =
        A i.castSucc j.castSucc - A i.castSucc (Fin.last g) * A j.castSucc (Fin.last g) /
          A (Fin.last g) (Fin.last g) := by
      show A i.castSucc j.castSucc -
          A i.castSucc (Fin.last g) * A (Fin.last g) j.castSucc / A (Fin.last g) (Fin.last g) =
        A i.castSucc j.castSucc -
          A i.castSucc (Fin.last g) * A j.castSucc (Fin.last g) / A (Fin.last g) (Fin.last g)
      rw [hA.apply j.castSucc (Fin.last g)]
    rw [hij, sub_mul, sub_mul]
    congr 1
    field_simp
  simp_rw [hentry, Finset.sum_sub_distrib]
  congr 1
  rw [sq, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]

/-- The two-square-completion identity behind `tsum_exp_neg_quadratic_matrix`'s inductive step:
after applying `Complex.tsum_exp_neg_quadratic` to the last coordinate, expanding the resulting
`(m + I β(n'))²` and collecting terms gives exactly `-π · schurStepLast`'s quadratic form plus a
new `m`-dependent shift, leaving a pure-`m` remainder that is later consumed by
`matrix_inv_blocks`'s corner entry. Hand-derived and cross-checked twice (once via this side, once
via the block-inverse expansion of the target `RHS`) before formalizing; see
`PoissonSummationPlan.md`. -/
private lemma double_square_completion {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (hA : A.IsSymm) (ha : A (Fin.last g) (Fin.last g) ≠ 0) (b : Fin (g + 1) → ℂ)
    (n' : Fin g → ℤ) (m : ℤ) :
    -π * (∑ i, ∑ j, A i.castSucc j.castSucc * (n' i : ℂ) * (n' j : ℂ)) +
        2 * π * (∑ i, b i.castSucc * (n' i : ℂ)) -
        π / A (Fin.last g) (Fin.last g) *
          ((m : ℂ) + I * (b (Fin.last g) -
            ∑ i, A i.castSucc (Fin.last g) * (n' i : ℂ))) ^ 2 =
      (-π * (∑ i, ∑ j, (schurStepLast A) i j * (n' i : ℂ) * (n' j : ℂ)) +
        2 * π * (∑ i, (b i.castSucc + (I * (m : ℂ) - b (Fin.last g)) *
          A i.castSucc (Fin.last g) / A (Fin.last g) (Fin.last g)) * (n' i : ℂ))) +
      -π / A (Fin.last g) (Fin.last g) * ((m : ℂ) + I * b (Fin.last g)) ^ 2 := by
  rw [schurStepLast_quadratic_eq hA]
  have hlin : ∑ i, (b i.castSucc + (I * (m : ℂ) - b (Fin.last g)) *
      A i.castSucc (Fin.last g) / A (Fin.last g) (Fin.last g)) * (n' i : ℂ) =
      (∑ i, b i.castSucc * (n' i : ℂ)) +
        (I * (m : ℂ) - b (Fin.last g)) / A (Fin.last g) (Fin.last g) *
          (∑ i, A i.castSucc (Fin.last g) * (n' i : ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hlin]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The `ℤ`-linear shift `n ↦ -I * ∑ᵢ bᵢnᵢ` used to feed an arbitrary complex shift `b` into
`ThetaAbleQuadraticForm.theta_fun`'s `z : M →ₗ[R] ℂ` argument. -/
noncomputable def bShiftMap {g : ℕ} (b : Fin g → ℂ) : (Fin g → ℤ) →ₗ[ℤ] ℂ where
  toFun n := -Complex.I * ∑ i, b i * (n i : ℂ)
  map_add' n m := by
    simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
  map_smul' c n := by
    show -Complex.I * ∑ i, b i * ((c • n) i : ℂ) =
        (c : ℤ) • (-Complex.I * ∑ i, b i * (n i : ℂ))
    simp only [zsmul_eq_mul, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring

/-- A symmetric complex matrix with positive-definite real part has an inverse with
positive-definite real part. -/
private lemma nonsing_inv_re_posDef {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ)
    (hA : A.IsSymm) (hRe : (A.map Complex.re).PosDef) :
    (A⁻¹.map Complex.re).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.isHermitian_iff_isSymm]
    exact hA.inv.map _
  · intro x hx
    have hdetne : A.det ≠ 0 := by
      intro h
      have hsquare := pivotSqrt_sq g A hA hRe
      rw [h] at hsquare
      exact pivotSqrt_ne_zero g A hA hRe ((pow_eq_zero_iff two_ne_zero).mp hsquare)
    have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hdetne
    let xc : Fin g → ℂ := fun i => (x i : ℂ)
    let z : Fin g → ℂ := (A⁻¹).mulVec xc
    let u : Fin g → ℝ := fun i => (z i).re
    let v : Fin g → ℝ := fun i => (z i).im
    have hAz : A.mulVec z = xc := by
      simp only [z, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet,
        Matrix.one_mulVec]
    have hz : z ≠ 0 := by
      intro hz
      apply hx
      have : xc = 0 := by rw [← hAz, hz, Matrix.mulVec_zero]
      funext i
      have hi := congrArg Complex.re (congrFun this i)
      simpa [xc] using hi
    have huv : u ≠ 0 ∨ v ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      funext i
      apply Complex.ext
      · simpa [u] using congrFun h.1 i
      · simpa [v] using congrFun h.2 i
    have hu (i : Fin g) : u i = ∑ j, (A⁻¹ i j).re * x j := by
      simp only [u, z, Matrix.mulVec, dotProduct, xc, Complex.re_sum, Complex.mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero]
    have hreal (i : Fin g) :
        x i = ∑ j, ((A i j).re * u j - (A i j).im * v j) := by
      have hi := congrFun hAz i
      apply_fun Complex.re at hi
      simpa only [Matrix.mulVec, dotProduct, xc, Complex.re_sum, Complex.mul_re, ofReal_re,
        u, v] using hi.symm
    have himag (i : Fin g) :
        0 = ∑ j, ((A i j).re * v j + (A i j).im * u j) := by
      have hi := congrFun hAz i
      apply_fun Complex.im at hi
      simpa only [Matrix.mulVec, dotProduct, xc, Complex.im_sum, Complex.mul_im, ofReal_im,
        u, v] using hi.symm
    have hcross :
        (∑ i, u i * ∑ j, (A i j).im * v j) =
          ∑ i, v i * ∑ j, (A i j).im * u j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [hA.apply i j]
        ring
    have hzero :
        (∑ i, v i * ∑ j, ((A i j).re * v j + (A i j).im * u j)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [← himag i]
      ring
    have hquadratic :
        (∑ i, x i * u i) =
          (∑ i, u i * ∑ j, (A i j).re * u j) +
            ∑ i, v i * ∑ j, (A i j).re * v j := by
      simp_rw [hreal]
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      have hsplit :
          (∑ i, ((∑ j, (A i j).re * u j) -
              ∑ j, (A i j).im * v j) * u i) =
          (∑ i, u i * ∑ j, (A i j).re * u j) -
            ∑ i, u i * ∑ j, (A i j).im * v j := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsplit]
      rw [hcross]
      have hz' :
          (∑ i, v i * ∑ j, (A i j).im * u j) =
            -(∑ i, v i * ∑ j, (A i j).re * v j) := by
        have := hzero
        simp only [Finset.sum_add_distrib] at this
        have hzero' :
            (∑ i, v i * ∑ j, (A i j).re * v j) +
                ∑ i, v i * ∑ j, (A i j).im * u j = 0 := by
          simpa only [mul_add, Finset.sum_add_distrib] using this
        linarith
      rw [hz']
      simp only [Finset.mul_sum]
      ring
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, star_trivial]
    rw [show (∑ i, x i * ∑ j, (A⁻¹ i j).re * x j) = ∑ i, x i * u i from
      Finset.sum_congr rfl fun i _ => by rw [hu]]
    rw [hquadratic]
    rcases huv with hu0 | hv0
    · exact add_pos_of_pos_of_nonneg
        (hRe.dotProduct_mulVec_pos hu0) (hRe.posSemidef.dotProduct_mulVec_nonneg v)
    · exact add_pos_of_nonneg_of_pos
        (hRe.posSemidef.dotProduct_mulVec_nonneg u) (hRe.dotProduct_mulVec_pos hv0)

/-- The one piece of genuinely new *analytic* (not just algebraic) infrastructure needed to close
`tsum_exp_neg_quadratic_matrix`: absolute summability of the quadratic exponential lattice sum,
needed to justify `tsum`-Fubini (`Summable.tsum_prod`) when peeling off the last coordinate.
Built by instantiating `RiemannThetaAble` (`ThetaFunctions.lean`) with `Q_Im := quadraticMapOfMatrixR
(2 • Re A)`, `Q_Re := quadraticMapOfMatrixR (-2 • Im A)`, `z := bShiftMap b`, chosen so that
`π I (qRe + I qIm) + 2π I z` matches this file's `-π ∑ A n n + 2π ∑ b n` exactly (checked via
`SiegelUpperHalfSpace.complex_quadratic`-style expansion, not reproduced verbatim here since that
lemma lives in the unimported `SiegelModular.lean`). -/
private lemma summable_quadratic_exp {g : ℕ} (hg : g ≠ 0) (A : Matrix (Fin g) (Fin g) ℂ)
    (hRe : (A.map Complex.re).PosDef) (b : Fin g → ℂ) :
    Summable (fun n : Fin g → ℤ =>
      exp (-π * ∑ i, ∑ j, A i j * (n i : ℂ) * (n j : ℂ) + 2 * π * ∑ i, b i * (n i : ℂ))) := by
  have hQIm : (quadraticMapOfMatrix ((2 : ℝ) • (A.map Complex.re))).PosDef :=
    quadraticMapOfMatrix_posDef hRe
  have hQImCont : Continuous (quadraticMapOfMatrix ((2 : ℝ) • (A.map Complex.re))) :=
    quadraticMapOfMatrix_continuous _
  letI := RiemannThetaAble hg (quadraticMapOfMatrix ((-2 : ℝ) • (A.map Complex.im)))
    (quadraticMapOfMatrix ((2 : ℝ) • (A.map Complex.re))) hQImCont hQIm
  have hsummable := ThetaAbleQuadraticForm.theta_fun_summable (R := ℤ) (M := Fin g → ℤ)
    (bShiftMap b)
  refine hsummable.congr fun n => ?_
  have hle : ∀ i : Fin g, (latticeEmbedding (Fin g) n) i = (n i : ℝ) := fun i => rfl
  have hq_im : (latticeQuadraticMap (quadraticMapOfMatrix ((2 : ℝ) • (A.map Complex.re)))) n
      = ∑ i, ∑ j, (A.map Complex.re) i j * ((n i : ℝ) * (n j : ℝ)) := by
    rw [latticeQuadraticMap_apply, quadraticMapOfMatrix_apply]
    simp only [Algebra.algebraMap_self_apply, Matrix.smul_apply, smul_eq_mul, hle]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 : (⅟(2 : ℝ)) = (2 : ℝ)⁻¹ := invOf_eq_inv 2
    rw [h2]; ring
  have hq_re : (latticeQuadraticMap (quadraticMapOfMatrix ((-2 : ℝ) • (A.map Complex.im)))) n
      = -∑ i, ∑ j, (A.map Complex.im) i j * ((n i : ℝ) * (n j : ℝ)) := by
    rw [latticeQuadraticMap_apply, quadraticMapOfMatrix_apply]
    simp only [Algebra.algebraMap_self_apply, Matrix.smul_apply, smul_eq_mul, hle]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 : (⅟(2 : ℝ)) = (2 : ℝ)⁻¹ := invOf_eq_inv 2
    rw [h2]; ring
  show Complex.exp (↑π * I *
      ((latticeQuadraticMap (quadraticMapOfMatrix ((-2 : ℝ) • (A.map Complex.im))) n : ℝ) +
        I * (latticeQuadraticMap (quadraticMapOfMatrix ((2 : ℝ) • (A.map Complex.re))) n : ℝ)) +
      2 * ↑π * I * (bShiftMap b n)) = _
  rw [hq_im, hq_re]
  congr 1
  show (π : ℂ) * I * ((-(∑ i, ∑ j, (A.map Complex.im) i j * ((n i:ℝ)*(n j:ℝ))) : ℝ) +
        I * ((∑ i, ∑ j, (A.map Complex.re) i j * ((n i:ℝ)*(n j:ℝ))) : ℝ)) +
      2 * (π : ℂ) * I * (-Complex.I * ∑ i, b i * (n i : ℂ)) =
    -(π : ℂ) * ∑ i, ∑ j, A i j * (n i : ℂ) * (n j : ℂ) + 2 * (π : ℂ) * ∑ i, b i * (n i : ℂ)
  push_cast
  have hAij : ∀ i j : Fin g, (A i j : ℂ) =
      ((A.map Complex.re) i j : ℂ) + Complex.I * ((A.map Complex.im) i j : ℂ) := by
    intro i j
    simp only [Matrix.map_apply]
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im (A i j)).symm
  simp_rw [hAij]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    show ((A.map Complex.re) i j + Complex.I * (A.map Complex.im) i j : ℂ) *
        (n i : ℂ) * (n j : ℂ) = (A.map Complex.re) i j * ((n i:ℂ)*(n j:ℂ)) +
        Complex.I * ((A.map Complex.im) i j * ((n i:ℂ)*(n j:ℂ))) from by ring]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Rank-`g` Poisson summation for a Gaussian: for `A : Matrix (Fin g) (Fin g) ℂ` symmetric with
`Re A` positive definite and `b : Fin g → ℂ`, resumming the quadratic exponential lattice sum
against its Fourier dual. Specializes to `Complex.tsum_exp_neg_quadratic` at `g = 1`. -/
theorem tsum_exp_neg_quadratic_matrix (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsSymm)
    (hRe : (A.map Complex.re).PosDef) (b : Fin g → ℂ) :
    (∑' n : Fin g → ℤ, exp (-π * ∑ i, ∑ j, A i j * (n i : ℂ) * (n j : ℂ)
        + 2 * π * ∑ i, b i * (n i : ℂ))) =
      1 / pivotSqrt g A *
        ∑' n : Fin g → ℤ, exp
          (-π * ∑ i, ∑ j, A⁻¹ i j * ((n i : ℂ) + I * b i) * ((n j : ℂ) + I * b j)) := by
  induction g with
  | zero =>
    rw [tsum_fin_zero_eq, tsum_fin_zero_eq]
    simp [pivotSqrt]
  | succ g ih =>
    set a : ℂ := A (Fin.last g) (Fin.last g) with ha_def
    have hpivotRe : 0 < a.re := hRe.diag_pos
    have hpivot : a ≠ 0 := fun h => by simp [h] at hpivotRe
    have hA' : (schurStepLast A).IsSymm := schurStepLast_isSymm hA
    have hRe' : ((schurStepLast A).map Complex.re).PosDef := schurStepLast_re_posDef hA hRe
    have hA''ne : (schurStepLast A).det ≠ 0 := by
      intro h
      apply pivotSqrt_ne_zero g (schurStepLast A) hA' hRe'
      have hsq := pivotSqrt_sq g (schurStepLast A) hA' hRe'
      rw [h] at hsq
      exact pow_eq_zero_iff two_ne_zero |>.mp hsq
    set v : Fin g → ℂ := fun i => A i.castSucc (Fin.last g) with hv_def
    set e : (Fin g → ℤ) × ℤ ≃ (Fin (g + 1) → ℤ) :=
      (Equiv.prodComm (Fin g → ℤ) ℤ).trans (Fin.snocEquiv (fun _ => ℤ)) with he_def
    have he_apply : ∀ n' k, e (n', k) = Fin.snoc n' k := fun n' k => rfl
    set F : (Fin (g + 1) → ℤ) → ℂ := fun n => exp (-π * ∑ i, ∑ j, A i j * (n i : ℂ) * (n j : ℂ)
        + 2 * π * ∑ i, b i * (n i : ℂ)) with hF_def
    have hFsum : Summable F := summable_quadratic_exp (Nat.succ_ne_zero g) A hRe b
    have hFesum : Summable (fun p : (Fin g → ℤ) × ℤ => F (e p)) :=
      (Equiv.summable_iff e).mpr hFsum
    have hLHS : ∑' n, F n = ∑' n' : Fin g → ℤ, ∑' k : ℤ, F (Fin.snoc n' k) := by
      rw [(Equiv.tsum_eq e F).symm, hFesum.tsum_prod]
      exact tsum_congr fun n' => tsum_congr fun k => by rw [he_apply]
    have hinner (n' : Fin g → ℤ) :
        (∑' k : ℤ, F (Fin.snoc n' k)) =
          1 / a ^ (1 / 2 : ℂ) * ∑' m : ℤ,
            exp ((-π * (∑ i, ∑ j, A i.castSucc j.castSucc * (n' i : ℂ) * (n' j : ℂ)) +
                2 * π * (∑ i, b i.castSucc * (n' i : ℂ))) -
              π / a * ((m : ℂ) + I * (b (Fin.last g) -
                ∑ i, A i.castSucc (Fin.last g) * (n' i : ℂ))) ^ 2) := by
      have hsplit : (∑' k : ℤ, F (Fin.snoc n' k)) =
          exp (-π * (∑ i, ∑ j, A i.castSucc j.castSucc * (n' i : ℂ) * (n' j : ℂ)) +
              2 * π * (∑ i, b i.castSucc * (n' i : ℂ))) *
            ∑' k : ℤ, exp (-π * a * (k : ℂ) ^ 2 +
              2 * π * (b (Fin.last g) -
                ∑ i, A i.castSucc (Fin.last g) * (n' i : ℂ)) * (k : ℂ)) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        simp only [hF_def]
        rw [quadratic_exponent_split hA, linear_split, ha_def]
        rw [← exp_add]
        congr 1
        ring
      rw [hsplit, Complex.tsum_exp_neg_quadratic hpivotRe]
      calc
        _ = 1 / a ^ (1 / 2 : ℂ) *
            (exp (-π * (∑ i, ∑ j, A i.castSucc j.castSucc * (n' i : ℂ) * (n' j : ℂ)) +
                2 * π * (∑ i, b i.castSucc * (n' i : ℂ))) *
              ∑' m : ℤ, exp (-π / a * ((m : ℂ) + I * (b (Fin.last g) -
                ∑ i, A i.castSucc (Fin.last g) * (n' i : ℂ))) ^ 2)) := by ring
        _ = 1 / a ^ (1 / 2 : ℂ) * ∑' m : ℤ,
            exp (-π * (∑ i, ∑ j, A i.castSucc j.castSucc * (n' i : ℂ) * (n' j : ℂ)) +
                2 * π * (∑ i, b i.castSucc * (n' i : ℂ))) *
              exp (-π / a * ((m : ℂ) + I * (b (Fin.last g) -
                ∑ i, A i.castSucc (Fin.last g) * (n' i : ℂ))) ^ 2) := by
              rw [tsum_mul_left]
        _ = _ := by
          congr 1
          refine tsum_congr fun m => ?_
          rw [← exp_add]
          congr 1
          ring
    let p1 (n' : Fin g -> ℤ) :=
      -↑π * ∑ (i : Fin g), ∑ (j : Fin g), A i.castSucc j.castSucc * (n' i : ℂ) * (n' j : ℂ)
      + 2 * ↑π * ∑ i, b i.castSucc * (n' i : ℂ)
    let p2 (n' : Fin g -> ℤ) (m : ℤ) := ↑π / a * (↑m + I * (b (Fin.last g) - ∑ (i : Fin g), A i.castSucc (Fin.last g) * ↑(n' i))) ^ 2
    have split_cexp_inner (n' : Fin g -> ℤ) (m : ℤ) :
      cexp (p1 n' - p2 n' m) = cexp (p1 n') * cexp (- p2 n' m)  := by
      rw [Complex.exp_sub]
      rw [Complex.exp_neg]
      ring
    have htransformed_summable : Summable (Function.uncurry fun n' m =>
        cexp (p1 n' - p2 n' m)) := by
      let B : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ := fun i j => Fin.lastCases
        (Fin.lastCases (1 / a) (fun j => -I * v j / a) j)
        (fun i => Fin.lastCases (-I * v i / a) (fun j => schurStepLast A i j) j) i
      let d : Fin (g + 1) → ℂ := fun i => Fin.lastCases
        (-I * b (Fin.last g) / a)
        (fun i => b i.castSucc - b (Fin.last g) * v i / a) i
      let c₀ : ℂ := π * b (Fin.last g) ^ 2 / a
      have hB : ((B.map Complex.re)).PosDef := by
        refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
        · rw [Matrix.isHermitian_iff_isSymm]
          ext i j
          refine Fin.lastCases ?_ (fun i => ?_) i <;>
            refine Fin.lastCases ?_ (fun j => ?_) j
          · simp [B]
          · simp [B]
          · simp [B]
          · simp only [Matrix.transpose_apply, Matrix.map_apply, B,
              Fin.lastCases_castSucc]
            rw [hA'.apply i j]
        · intro x hx
          set y : Fin g → ℝ := fun i => x i.castSucc with hy_def
          set t : ℝ := x (Fin.last g) with ht_def
          set c : ℂ := ∑ i, v i * (y i : ℂ) with hc_def
          set q : ℂ := ∑ i, ∑ j,
            A i.castSucc j.castSucc * (y i : ℂ) * (y j : ℂ) with hq_def
          have hquad :
              star x ⬝ᵥ (B.map Complex.re).mulVec x =
                (q + ((t : ℂ) - I * c) ^ 2 / a).re := by
            have hBcomplex :
                (∑ i, (x i : ℂ) * ∑ j, B i j * (x j : ℂ)) =
                  q + ((t : ℂ) - I * c) ^ 2 / a := by
              have hB_cc : ∀ i j : Fin g, B i.castSucc j.castSucc = schurStepLast A i j :=
                fun i j => by simp [B]
              have hB_cl : ∀ i : Fin g, B i.castSucc (Fin.last g) = -I * v i / a :=
                fun i => by simp [B]
              have hB_lc : ∀ j : Fin g, B (Fin.last g) j.castSucc = -I * v j / a :=
                fun j => by simp [B]
              have hB_ll : B (Fin.last g) (Fin.last g) = 1 / a := by simp [B]
              simp only [Fin.sum_univ_castSucc, hB_cc, hB_cl, hB_lc, hB_ll, mul_add,
                Finset.mul_sum, Finset.sum_add_distrib]
              show (∑ i : Fin g, ∑ j : Fin g,
                    (y i : ℂ) * (schurStepLast A i j * (y j : ℂ))) +
                  (∑ i : Fin g, (t : ℂ) * (-I * v i / a * (y i : ℂ))) +
                  ((∑ i : Fin g, (y i : ℂ) * (-I * v i / a * (t : ℂ))) +
                    (t : ℂ) * (1 / a * (t : ℂ))) =
                q + ((t : ℂ) - I * c) ^ 2 / a
              have hTerm1 :
                  (∑ i : Fin g, ∑ j : Fin g,
                      (y i : ℂ) * (schurStepLast A i j * (y j : ℂ))) =
                    q - c ^ 2 / a := by
                have hschur : ∑ i, ∑ j, schurStepLast A i j * (y i : ℂ) * (y j : ℂ) =
                    q - c ^ 2 / a :=
                  schurStepLast_quadratic_eq hA (fun i => (y i : ℂ))
                rw [← hschur]
                exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
              have hSum_v : (∑ i : Fin g, v i * (y i : ℂ)) = c := hc_def.symm
              have hTerm2 :
                  (∑ i : Fin g, (t : ℂ) * (-I * v i / a * (y i : ℂ))) =
                    -I * (t : ℂ) * c / a := by
                have hfactor : (∑ i : Fin g, (t : ℂ) * (-I * v i / a * (y i : ℂ))) =
                    -I * (t : ℂ) / a * ∑ i : Fin g, v i * (y i : ℂ) := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun i _ => by ring
                rw [hfactor, hSum_v]; ring
              have hTerm3 :
                  (∑ i : Fin g, (y i : ℂ) * (-I * v i / a * (t : ℂ))) =
                    -I * (t : ℂ) * c / a := by
                have hfactor : (∑ i : Fin g, (y i : ℂ) * (-I * v i / a * (t : ℂ))) =
                    -I * (t : ℂ) / a * ∑ i : Fin g, v i * (y i : ℂ) := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun i _ => by ring
                rw [hfactor, hSum_v]; ring
              rw [hTerm1, hTerm2, hTerm3]
              field_simp
              ring_nf
              rw [Complex.I_sq]
              ring
            rw [← hBcomplex, Complex.re_sum]
            simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply,
              Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Complex.re_sum]
            exact Finset.sum_congr rfl fun j _ => by simp [Complex.mul_re]
          rw [hquad]
          have hnorm : 0 < Complex.normSq a := Complex.normSq_pos.mpr hpivot
          have hcomplete :
              (q + ((t : ℂ) - I * c) ^ 2 / a).re =
                q.re - c.re ^ 2 / a.re + a.re / Complex.normSq a *
                  (t + c.im - a.im * c.re / a.re) ^ 2 := by
            rw [Complex.add_re, Complex.div_re]
            simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
              Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
              Complex.I_im, zero_mul, one_mul, zero_sub, Complex.normSq_apply]
            field_simp
            ring
          rw [hcomplete]
          by_cases hy0 : y = 0
          · have hc0 : c = 0 := by simp [hc_def, hy0]
            have hq0 : q = 0 := by simp [hq_def, hy0]
            have ht0 : t ≠ 0 := by
              intro ht
              apply hx
              funext i
              refine Fin.lastCases ?_ (fun j => ?_) i
              · simpa [ht_def] using ht
              · have := congrFun hy0 j
                simpa [hy_def] using this
            rw [hc0, hq0]
            convert mul_pos (div_pos hpivotRe hnorm) (sq_pos_of_ne_zero ht0) using 1 ; norm_num
          · set z : Fin (g + 1) → ℝ := Fin.snoc y (-c.re / a.re) with hz_def
            have hz0 : z ≠ 0 := by
              intro hz
              apply hy0
              funext i
              have := congrFun hz i.castSucc
              simpa [hz_def, Fin.snoc_castSucc] using this
            have hzpos := hRe.dotProduct_mulVec_pos hz0
            have hbase : 0 < q.re - c.re ^ 2 / a.re := by
              have hzcomplex :
                  (∑ i, (z i : ℂ) * ∑ j, A i j * (z j : ℂ)) =
                    q + 2 * ((-c.re / a.re : ℝ) : ℂ) * c +
                      a * ((-c.re / a.re : ℝ) : ℂ) ^ 2 := by
                have hcol : ∀ j : Fin g,
                    A (Fin.last g) j.castSucc = A j.castSucc (Fin.last g) := fun j => by
                  rw [hA.apply j.castSucc (Fin.last g)]
                simp only [Fin.sum_univ_castSucc, hz_def, Fin.snoc_castSucc, Fin.snoc_last,
                  mul_add, Finset.sum_add_distrib, Finset.mul_sum]
                have hTerm1 :
                    (∑ i : Fin g, ∑ j : Fin g,
                        (y i : ℂ) * (A i.castSucc j.castSucc * (y j : ℂ))) = q := by
                  rw [hq_def]
                  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
                have hTerm2 :
                    (∑ i : Fin g, ((-c.re / a.re : ℝ) : ℂ) *
                        (A (Fin.last g) i.castSucc * (y i : ℂ))) =
                      ((-c.re / a.re : ℝ) : ℂ) * c := by
                  have hfactor :
                      (∑ i : Fin g, ((-c.re / a.re : ℝ) : ℂ) *
                          (A (Fin.last g) i.castSucc * (y i : ℂ))) =
                        ((-c.re / a.re : ℝ) : ℂ) * ∑ i : Fin g, v i * (y i : ℂ) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [hcol i]
                  rw [hfactor, ← hc_def]
                have hTerm3 :
                    (∑ i : Fin g, (y i : ℂ) *
                        (A i.castSucc (Fin.last g) * ((-c.re / a.re : ℝ) : ℂ))) =
                      ((-c.re / a.re : ℝ) : ℂ) * c := by
                  have hfactor :
                      (∑ i : Fin g, (y i : ℂ) *
                          (A i.castSucc (Fin.last g) * ((-c.re / a.re : ℝ) : ℂ))) =
                        ((-c.re / a.re : ℝ) : ℂ) * ∑ i : Fin g, v i * (y i : ℂ) := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun i _ => by rw [hv_def]; ring
                  rw [hfactor, ← hc_def]
                rw [hTerm1, hTerm2, hTerm3, ← ha_def]
                ring
              have hzreal :
                  star z ⬝ᵥ (A.map Complex.re).mulVec z =
                    (q + 2 * ((-c.re / a.re : ℝ) : ℂ) * c +
                      a * ((-c.re / a.re : ℝ) : ℂ) ^ 2).re := by
                rw [← hzcomplex, Complex.re_sum]
                simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply,
                  Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                rw [Complex.re_sum]
                exact Finset.sum_congr rfl fun j _ => by simp [Complex.mul_re]
              rw [hzreal] at hzpos
              convert hzpos using 1
              · rfl
              · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
                  Complex.ofReal_im, zero_mul, sub_zero, pow_two]
                field_simp
                norm_num
                ring
            have hsquare : 0 ≤ a.re / Complex.normSq a *
                (t + c.im - a.im * c.re / a.re) ^ 2 :=
              mul_nonneg (le_of_lt (div_pos hpivotRe hnorm)) (sq_nonneg _)
            linarith
      have hbase := summable_quadratic_exp (Nat.succ_ne_zero g) B hB d
      have hshift : Summable (fun n : Fin (g + 1) → ℤ =>
          cexp c₀ * cexp (-π * ∑ i, ∑ j, B i j * (n i : ℂ) * (n j : ℂ) +
            2 * π * ∑ i, d i * (n i : ℂ))) := hbase.mul_left _
      have hreindexed : Summable (fun p : (Fin g → ℤ) × ℤ =>
          cexp c₀ * cexp (-π * ∑ i, ∑ j, B i j * ((e p) i : ℂ) * ((e p) j : ℂ) +
            2 * π * ∑ i, d i * ((e p) i : ℂ))) :=
        by
          refine ((Equiv.summable_iff e).mpr hshift).congr fun p => ?_
          rfl
      refine hreindexed.congr fun p => ?_
      rcases p with ⟨n', m⟩
      simp only [Function.uncurry_apply_pair]
      rw [he_apply, ← Complex.exp_add]
      apply congrArg cexp
      simp only [p1, p2, B, d, c₀, hv_def, ha_def, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, Fin.lastCases_castSucc, Fin.lastCases_last, schurStepLast]
      have hcol : ∀ j : Fin g,
          A (Fin.last g) j.castSucc = A j.castSucc (Fin.last g) := fun j => by
        rw [hA.apply j.castSucc (Fin.last g)]
      simp_rw [hcol]
      simp only [← ha_def, sub_mul, mul_add, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum]
      simp only [← Finset.mul_sum]
      set Q : ℂ := ∑ i : Fin g, ∑ j : Fin g, A i.castSucc j.castSucc * (n' i : ℂ) * (n' j : ℂ)
        with hQ_def
      set S : ℂ := ∑ i : Fin g, A i.castSucc (Fin.last g) * (n' i : ℂ) with hS_def
      set L : ℂ := ∑ i : Fin g, b i.castSucc * (n' i : ℂ) with hL_def
      set bl : ℂ := b (Fin.last g) with hbl_def
      have hS2 :
          (∑ i : Fin g, ∑ j : Fin g,
              A i.castSucc (Fin.last g) * A j.castSucc (Fin.last g) / a *
                (n' i : ℂ) * (n' j : ℂ)) =
            S ^ 2 / a := by
        rw [hS_def, sq, Finset.sum_mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hSm1 :
          (∑ i : Fin g, -I * A i.castSucc (Fin.last g) / a * (n' i : ℂ) * (m : ℂ)) =
            -I * S * (m : ℂ) / a := by
        have hfactor :
            (∑ i : Fin g, -I * A i.castSucc (Fin.last g) / a * (n' i : ℂ) * (m : ℂ)) =
              -I * (m : ℂ) / a * ∑ i : Fin g, A i.castSucc (Fin.last g) * (n' i : ℂ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hfactor, ← hS_def]; ring
      have hSm2 :
          (∑ i : Fin g, -I * A i.castSucc (Fin.last g) / a * (m : ℂ) * (n' i : ℂ)) =
            -I * S * (m : ℂ) / a := by
        have hfactor :
            (∑ i : Fin g, -I * A i.castSucc (Fin.last g) / a * (m : ℂ) * (n' i : ℂ)) =
              -I * (m : ℂ) / a * ∑ i : Fin g, A i.castSucc (Fin.last g) * (n' i : ℂ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hfactor, ← hS_def]; ring
      have hblS :
          (∑ x : Fin g, bl * A x.castSucc (Fin.last g) / a * (n' x : ℂ)) = bl * S / a := by
        have hfactor :
            (∑ x : Fin g, bl * A x.castSucc (Fin.last g) / a * (n' x : ℂ)) =
              bl / a * ∑ x : Fin g, A x.castSucc (Fin.last g) * (n' x : ℂ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hfactor, ← hS_def]; ring
      rw [hS2, hSm1, hSm2, hblS]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    have hFubini :
        (∑' n' : Fin g → ℤ, ∑' m : ℤ, cexp (p1 n' - p2 n' m)) =
          ∑' m : ℤ, ∑' n' : Fin g → ℤ, cexp (p1 n' - p2 n' m) := by
      exact htransformed_summable.tsum_comm.symm
    let b' (m : ℤ) (i : Fin g) : ℂ :=
      b i.castSucc + (I * (m : ℂ) - b (Fin.last g)) *
        A i.castSucc (Fin.last g) / A (Fin.last g) (Fin.last g)
    let p3 (n' : Fin g → ℤ) (m : ℤ) : ℂ :=
      (-π * (∑ i, ∑ j, (schurStepLast A) i j * (n' i : ℂ) * (n' j : ℂ)) +
        2 * π * ∑ i, b' m i * (n' i : ℂ)) +
      -π / A (Fin.last g) (Fin.last g) * ((m : ℂ) + I * b (Fin.last g)) ^ 2
    let q (n' : Fin g → ℤ) (m : ℤ) : ℂ :=
      -π * (∑ i, ∑ j, (schurStepLast A) i j * (n' i : ℂ) * (n' j : ℂ)) +
        2 * π * ∑ i, b' m i * (n' i : ℂ)
    let r (m : ℤ) : ℂ :=
      -π / A (Fin.last g) (Fin.last g) * ((m : ℂ) + I * b (Fin.last g)) ^ 2
    have hsquare (n' : Fin g → ℤ) (m : ℤ) : p1 n' - p2 n' m = p3 n' m := by
      simp only [p1, p2, p3, b']
      rw [ha_def]
      exact double_square_completion hA hpivot b n' m
    have hp3_split (n' : Fin g → ℤ) (m : ℤ) : p3 n' m = q n' m + r m := by
      rfl
    have hcompleted_summable : Summable (Function.uncurry fun n' m => cexp (p3 n' m)) :=
      htransformed_summable.congr fun x => by
        rcases x with ⟨n', m⟩
        change cexp (p1 n' - p2 n' m) = cexp (p3 n' m)
        rw [hsquare n' m]
    have hcompleted_fubini :
        (∑' n' : Fin g → ℤ, ∑' m : ℤ, cexp (p3 n' m)) =
          ∑' m : ℤ, ∑' n' : Fin g → ℤ, cexp (p3 n' m) := by
      exact hcompleted_summable.tsum_comm.symm
    rw [hLHS]
    rw [show (∑' n' : Fin g → ℤ, ∑' k : ℤ, F (Fin.snoc n' k)) =
        ∑' n' : Fin g → ℤ, 1 / a ^ (1 / 2 : ℂ) *
          ∑' m : ℤ, cexp (p1 n' - p2 n' m) from
      tsum_congr fun n' => by simpa [p1, p2] using hinner n']
    rw [tsum_mul_left]
    conv_lhs =>
      enter [2, 1, n']
      conv =>
        enter [1, m]
        rw [hsquare n' m]
    rw [hcompleted_fubini]
    conv_lhs =>
      enter [2, 1, m]
      conv =>
        enter [1, n']
        rw [hp3_split n' m, Complex.exp_add]
      rw [tsum_mul_right]
    conv_lhs =>
      enter [2, 1, m]
      rw [show (∑' n' : Fin g → ℤ, cexp (q n' m)) =
          1 / pivotSqrt g (schurStepLast A) *
            ∑' n' : Fin g → ℤ, cexp
              (-π * ∑ i, ∑ j, (schurStepLast A)⁻¹ i j *
                ((n' i : ℂ) + I * b' m i) * ((n' j : ℂ) + I * b' m j)) from by
        simpa only [q] using ih (schurStepLast A) hA' hRe' (b' m)]
    let dualExponent (n' : Fin g → ℤ) (m : ℤ) : ℂ :=
      -π * ∑ i, ∑ j, (schurStepLast A)⁻¹ i j *
          ((n' i : ℂ) + I * b' m i) * ((n' j : ℂ) + I * b' m j) + r m
    let targetDual (n : Fin (g + 1) → ℤ) : ℂ :=
      cexp (-π * ∑ i, ∑ j, A⁻¹ i j *
        ((n i : ℂ) + I * b i) * ((n j : ℂ) + I * b j))
    have hdualExponent (n' : Fin g → ℤ) (m : ℤ) :
        dualExponent n' m =
          -π * ∑ i, ∑ j, A⁻¹ i j *
            (((Fin.snoc n' m : Fin (g + 1) → ℤ) i : ℂ) + I * b i) *
            (((Fin.snoc n' m : Fin (g + 1) → ℤ) j : ℂ) + I * b j) := by
      obtain ⟨h11, h12, h21, h22⟩ := matrix_inv_blocks hpivot hA''ne
      simp only [dualExponent, b', r, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last]
      simp_rw [h11, h12, h21, h22]
      set α : ℂ := A (Fin.last g) (Fin.last g)
      set S : Matrix (Fin g) (Fin g) ℂ := (schurStepLast A)⁻¹
      set y : Fin g → ℂ := (fun i => (n' i : ℂ) + I * b i.castSucc) with hy_def
      set w : Fin g → ℂ := (fun i => A i.castSucc (Fin.last g)) with hw_def
      set t : ℂ := (m : ℂ) + I * b (Fin.last g)
      have hα : α ≠ 0 := by rw [← ha_def]; exact hpivot
      have hbshift (i : Fin g) :
          (n' i : ℂ) + I * (b i.castSucc + (I * (m : ℂ) - b (Fin.last g)) *
              A i.castSucc (Fin.last g) / A (Fin.last g) (Fin.last g)) =
            y i - t * w i / α := by
        simp only [y, t, w, α]
        field_simp [hα]
        ring_nf
        rw [Complex.I_sq]
        ring
      have hshift_sum :
          (∑ i, ∑ j, S i j *
              ((n' i : ℂ) + I * (b i.castSucc + (I * (m : ℂ) - b (Fin.last g)) *
                w i / α)) *
              ((n' j : ℂ) + I * (b j.castSucc + (I * (m : ℂ) - b (Fin.last g)) *
                w j / α))) =
            ∑ i, ∑ j, S i j * (y i - t * w i / α) * (y j - t * w j / α) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [show w i = A i.castSucc (Fin.last g) from rfl,
          show w j = A j.castSucc (Fin.last g) from rfl, hbshift i, hbshift j]
      rw [hshift_sum]
      have hrow (i : Fin g) : A (Fin.last g) i.castSucc = A i.castSucc (Fin.last g) :=
        hA.apply i.castSucc (Fin.last g)
      simp_rw [hrow]
      change
        -π * (∑ i, ∑ j, S i j * (y i - t * w i / α) * (y j - t * w j / α)) +
            -π / α * t ^ 2 =
          -π *
            ((∑ i, ((∑ j, S i j * y i * y j) +
                (-∑ l, S i l * w l) / α * y i * t)) +
              ((∑ j, ((-∑ l, w l * S l j) / α * t * y j)) +
                (1 / α + (∑ i, ∑ j, w i * S i j * w j) / α ^ 2) * t * t))
      field_simp [hα]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      ring_nf
      abel_nf
      congr 1
      have hsimplifySummand (i j : Fin g) :
          α *
              (α * S i j * t ^ 2 * w i * w j * (α ^ 2)⁻¹ +
                (-(α ^ 2 * S i j * y i * t * w j * (α ^ 2)⁻¹) +
                  (-(α ^ 2 * S i j * t * w i * y j * (α ^ 2)⁻¹) +
                    α ^ 3 * S i j * y i * y j * (α ^ 2)⁻¹))) =
            S i j * t ^ 2 * w i * w j -
                α * S i j * y i * t * w j -
              α * S i j * t * w i * y j +
            α ^ 2 * S i j * y i * y j := by
        field_simp [hα]
        ring
      conv_lhs =>
        norm_num
        rw [Finset.mul_sum]
        enter [1, 2, i]
        rw [Finset.mul_sum]
        enter [2, j]
        rw [hsimplifySummand i j]
      conv_lhs =>
        rw [← Finset.sum_neg_distrib]
        enter [2, i]
        rw [← Finset.sum_neg_distrib]
      have hαcancel : α ^ 2 * α⁻¹ = α := by
        field_simp [hα]
      have hcross :
          (∑ i, α * ∑ j, t * w j * S j i * y i) =
            ∑ i, α * ∑ j, S i j * t * w i * y j := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      conv_rhs =>
        norm_num
        rw [hαcancel]
        rw [hcross]
        conv =>
          enter [1, 1]
          rw [Finset.mul_sum]
        conv =>
          enter [1]
          rw [← Finset.sum_neg_distrib]
        conv =>
          enter [2, 1]
          rw [← Finset.sum_neg_distrib]
        conv =>
          enter [2]
          rw [← Finset.sum_add_distrib]
        rw [← Finset.sum_add_distrib]
        enter [2, i]
        simp only [Finset.mul_sum, ← Finset.sum_neg_distrib,
          ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hdual_summable : Summable (Function.uncurry fun n' m => cexp (dualExponent n' m)) := by
      let d : Fin (g + 1) → ℂ := fun i =>
        -I * ∑ j, A⁻¹ i j * b j
      let c : ℂ := π * ∑ i, ∑ j, A⁻¹ i j * b i * b j
      have hbase : Summable (fun n : Fin (g + 1) → ℤ =>
          cexp (-π * ∑ i, ∑ j, A⁻¹ i j * (n i : ℂ) * (n j : ℂ) +
            2 * π * ∑ i, d i * (n i : ℂ))) :=
        summable_quadratic_exp (Nat.succ_ne_zero g) A⁻¹
          (nonsing_inv_re_posDef A hA hRe) d
      have htarget : Summable targetDual := by
        refine (hbase.mul_left (cexp c)).congr fun n => ?_
        simp only [targetDual]
        rw [← Complex.exp_add]
        congr 1
        have hcrossDual :
            (∑ i, ∑ j, A⁻¹ i j * (n i : ℂ) * b j) =
              ∑ i, ∑ j, A⁻¹ i j * b i * (n j : ℂ) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
            rw [hA.inv.apply i j]
            ring
        have hlinear :
            2 * π * ∑ i, (-I * ∑ j, A⁻¹ i j * b j) * (n i : ℂ) =
              -π * ((∑ i, ∑ j, A⁻¹ i j * (I * b i) * (n j : ℂ)) +
                ∑ i, ∑ j, A⁻¹ i j * (n i : ℂ) * (I * b j)) := by
          calc
            _ = -2 * π * I *
                (∑ i, ∑ j, A⁻¹ i j * (n i : ℂ) * b j) := by
              simp only [Finset.mul_sum, Finset.sum_mul]
              ring_nf
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = -π * I *
                ((∑ i, ∑ j, A⁻¹ i j * b i * (n j : ℂ)) +
                  ∑ i, ∑ j, A⁻¹ i j * (n i : ℂ) * b j) := by
              rw [hcrossDual]
              ring
            _ = _ := by
              have hfirst :
                  (∑ i, ∑ j, A⁻¹ i j * (I * b i) * (n j : ℂ)) =
                    (∑ i, ∑ j, A⁻¹ i j * b i * (n j : ℂ)) * I := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun j _ => by ring
              have hsecond :
                  (∑ i, ∑ j, A⁻¹ i j * (n i : ℂ) * (I * b j)) =
                    (∑ i, ∑ j, A⁻¹ i j * (n i : ℂ) * b j) * I := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun j _ => by ring
              rw [hfirst, hsecond]
              ring
        simp only [d, c]
        simp_rw [mul_add, add_mul]
        simp only [Finset.sum_add_distrib]
        rw [hlinear]
        ring_nf
        rw [Complex.I_sq]
        have hcrossOrder :
            (∑ i, ∑ j, A⁻¹ i j * I * b i * (n j : ℂ)) =
              ∑ i, ∑ j, I * A⁻¹ i j * b i * (n j : ℂ) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        have hnegOrder :
            (∑ i, ∑ j, (-1 : ℂ) * A⁻¹ i j * b i * b j) =
              -(∑ i, ∑ j, A⁻¹ i j * b i * b j) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
        rw [hcrossOrder, hnegOrder]
        ring
      have hreindexed : Summable (fun p : (Fin g → ℤ) × ℤ => targetDual (e p)) :=
        by
          refine ((Equiv.summable_iff e).mpr htarget).congr fun p => ?_
          rfl
      refine hreindexed.congr fun p => ?_
      rcases p with ⟨n', m⟩
      simp only [Function.uncurry_apply_pair]
      rw [hdualExponent n' m, he_apply]
    have hdual_iterated :
        (∑' m : ℤ, ∑' n' : Fin g → ℤ, cexp (dualExponent n' m)) =
          ∑' p : (Fin g → ℤ) × ℤ, cexp (dualExponent p.1 p.2) := by
      calc
        _ = ∑' n' : Fin g → ℤ, ∑' m : ℤ, cexp (dualExponent n' m) :=
          hdual_summable.tsum_comm
        _ = ∑' p : (Fin g → ℤ) × ℤ,
            Function.uncurry (fun n' m => cexp (dualExponent n' m)) p :=
          hdual_summable.tsum_prod.symm
        _ = _ := tsum_congr fun p => by rcases p with ⟨n', m⟩; rfl
    rw [show (∑' m : ℤ,
          (1 / pivotSqrt g (schurStepLast A) *
              ∑' n' : Fin g → ℤ, cexp
                (-π * ∑ i, ∑ j, (schurStepLast A)⁻¹ i j *
                  ((n' i : ℂ) + I * b' m i) * ((n' j : ℂ) + I * b' m j))) *
            cexp (r m)) =
        1 / pivotSqrt g (schurStepLast A) *
          ∑' m : ℤ, ∑' n' : Fin g → ℤ, cexp (dualExponent n' m) from by
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      rw [mul_assoc, ← tsum_mul_right]
      congr 1
      refine tsum_congr fun n' => ?_
      simp only [dualExponent, Complex.exp_add]]
    rw [hdual_iterated]
    rw [show (∑' p : (Fin g → ℤ) × ℤ, cexp (dualExponent p.1 p.2)) =
        ∑' p : (Fin g → ℤ) × ℤ, targetDual (e p) from
      tsum_congr fun p => by
        rw [he_apply]
        simp only [targetDual]
        rw [hdualExponent p.1 p.2]]
    rw [Equiv.tsum_eq e targetDual]
    simp only [targetDual, pivotSqrt]
    ring

/-! ## An abstract Poisson-summation predicate on `EuclideanSpace ℝ (Fin g) → ℂ` -/

open scoped FourierTransform RealInnerProductSpace

/-- The point `n ∈ ℤ^g ⊆ ℝ^g`, viewed in `EuclideanSpace ℝ (Fin g)`. -/
noncomputable def latticePoint (n : Fin g → ℤ) : EuclideanSpace ℝ (Fin g) :=
  (EuclideanSpace.equiv (Fin g) ℝ).symm fun i => (n i : ℝ)

/-- `f` has a Fourier transform (`f` is integrable, so Mathlib's `𝓕 f` — the Fourier transform on
the real inner product space `EuclideanSpace ℝ (Fin g)`, `Mathlib.Analysis.Fourier.FourierTransform`
— is genuinely the Fourier transform of `f` rather than a junk `0`) and Poisson summation holds for
`f` against it: the lattice sums of `f` and of `𝓕 f` over `ℤ^g` both converge, and to the same
value. -/
def HasPoissonSummation (f : EuclideanSpace ℝ (Fin g) → ℂ) : Prop :=
  MeasureTheory.Integrable f ∧
    Summable (fun n : Fin g → ℤ => f (latticePoint n)) ∧
    Summable (fun n : Fin g → ℤ => 𝓕 f (latticePoint n)) ∧
    ∑' n : Fin g → ℤ, f (latticePoint n) = ∑' n : Fin g → ℤ, 𝓕 f (latticePoint n)

private lemma summable_finsetSum {ι α : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] (s : Finset ι) (h : ι → (Fin g → ℤ) → α)
    (hh : ∀ i ∈ s, Summable (h i)) : Summable (fun n => ∑ i ∈ s, h i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hh a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

/-- `HasPoissonSummation` is closed under finite `ℂ`-linear combinations. -/
lemma HasPoissonSummation.finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → EuclideanSpace ℝ (Fin g) → ℂ) (hf : ∀ i ∈ s, HasPoissonSummation (f i)) :
    HasPoissonSummation (fun x => ∑ i ∈ s, c i • f i x) := by
  have hIntegrable : ∀ i ∈ s, MeasureTheory.Integrable (fun x => c i • f i x) :=
    fun i hi => ((hf i hi).1).smul (c i)
  have hFourier : ∀ w, 𝓕 (fun x => ∑ i ∈ s, c i • f i x) w = ∑ i ∈ s, c i • 𝓕 (f i) w := by
    intro w
    simp only [Real.fourier_eq]
    rw [show (fun v => 𝐞 (-⟪v, w⟫) • ∑ i ∈ s, c i • f i v) =
        fun v => ∑ i ∈ s, c i • (𝐞 (-⟪v, w⟫) • f i v) from
      funext fun v => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [Circle.smul_def, mul_left_comm]]
    have hsplit :
        (∫ v, ∑ i ∈ s, c i • (𝐞 (-⟪v, w⟫) • f i v)) =
          ∑ i ∈ s, ∫ v, c i • (𝐞 (-⟪v, w⟫) • f i v) :=
      MeasureTheory.integral_finsetSum s fun i hi =>
        ((Real.fourierIntegral_convergent_iff w).mpr (hf i hi).1).smul (c i)
    rw [hsplit]
    exact Finset.sum_congr rfl fun i _ => by rw [MeasureTheory.integral_smul]
  refine ⟨MeasureTheory.integrable_finsetSum s hIntegrable,
    summable_finsetSum s (fun i n => c i • f i (latticePoint n))
      (fun i hi => ((hf i hi).2.1).const_smul (c i)),
    ?_, ?_⟩
  · refine (summable_finsetSum s (fun i n => c i • 𝓕 (f i) (latticePoint n))
      (fun i hi => ((hf i hi).2.2.1).const_smul (c i))).congr fun n => ?_
    rw [hFourier]
  · simp_rw [hFourier]
    rw [tsum_congr fun n => rfl,
      Summable.tsum_finsetSum fun i hi => ((hf i hi).2.1).const_smul (c i),
      Summable.tsum_finsetSum fun i hi => ((hf i hi).2.2.1).const_smul (c i)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [tsum_const_smul'' (c i), tsum_const_smul'' (c i), (hf i hi).2.2.2]

/-! `HasPoissonSummation.finsetSum` above is restricted to *finite* linear combinations. Extending
it to a genuine infinite series `fun x => ∑' i, c i • f i x` (`c : ι → ℂ`, `ι` countable) needs a
domination hypothesis on `(c i)` against per-`i` bounds on `f i` — e.g. `M N : ι → ℝ` with
`∫ x, ‖f i x‖ ≤ M i`, `∑' n, ‖f i (latticePoint n)‖ ≤ N i`, and `Summable (‖c ·‖ * M ·)`,
`Summable (‖c ·‖ * N ·)` — to run three interchanges: `MeasureTheory.integral_tsum_of_
summable_integral_norm` swaps `∫` past `∑'`; `𝓕` commutes with an L¹-convergent series via
`Lp.fourierTransformCLM : Lp E 1 →L[ℂ] V →ᵇ E` and `ContinuousLinearMap.map_tsum`; and
`Summable.tsum_comm` swaps the lattice `tsum` past the `∑' i`, given joint summability over
`ι × (Fin g → ℤ)` from the domination hypothesis. All three lemmas already exist in Mathlib; none
of this is written yet. -/

/-- The Gaussian on `EuclideanSpace ℝ (Fin g)` with covariance `A` and phase/shift `b`, matching
the exponent `tsum_exp_neg_quadratic_matrix` resums over the lattice `ℤ^g`. -/
noncomputable def modulatedGaussian (A : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ)
    (x : EuclideanSpace ℝ (Fin g)) : ℂ :=
  exp (-π * ∑ i, ∑ j, A i j * (x.ofLp i : ℂ) * (x.ofLp j : ℂ) +
    2 * π * ∑ i, b i * (x.ofLp i : ℂ))

/-- The modulated Gaussian satisfies `HasPoissonSummation`: it has a Fourier transform (the
classical `1 / pivotSqrt g A * exp(-π ∑∑ A⁻¹ (ξ + I b) (ξ + I b))`, matching
`tsum_exp_neg_quadratic_matrix`'s right-hand side) and Poisson summation holds for it. -/
theorem modulatedGaussian_hasPoissonSummation (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsSymm)
    (hRe : (A.map Complex.re).PosDef) (b : Fin g → ℂ) :
    HasPoissonSummation (modulatedGaussian A b) := by
  sorry
