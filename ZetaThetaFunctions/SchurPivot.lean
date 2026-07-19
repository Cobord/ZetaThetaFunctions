import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Schur complement / pivot square root for complex symmetric matrices

Pure matrix algebra, shared by both the discrete lattice-sum identity (`PoissonSummation.lean`)
and the continuous Gaussian Fourier transform (`GaussianFourierTransform.lean`): neither lattices
(`Fin g → ℤ`) nor `EuclideanSpace` appear anywhere in this file.

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

section SchurStepDef

variable {g : ℕ}

/-- One step of symmetric (plain-transpose, not conjugate-transpose) Gaussian elimination: the
Schur complement of `A` with respect to its bottom-right corner `A (last) (last)`. -/
noncomputable def schurStepLast {R : Type*} [Ring R] [Div R] {g : ℕ} (A : Matrix (Fin (g + 1)) (Fin (g + 1)) R) :
    Matrix (Fin g) (Fin g) R :=
  fun i j => A i.castSucc j.castSucc -
    A i.castSucc (Fin.last g) * A (Fin.last g) j.castSucc / A (Fin.last g) (Fin.last g)

lemma schurStepLast_isSymm
  {R : Type*} [CommRing R] [Div R]
  {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) R} (hA : A.IsSymm) :
    (schurStepLast A).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, schurStepLast]
  rw [hA.apply i.castSucc j.castSucc, hA.apply (Fin.last g) j.castSucc,
    hA.apply i.castSucc (Fin.last g)]
  ring_nf

/-- The Schur complement's quadratic form is the original one with the rank-one correction from
completing the square in the last coordinate subtracted off. Pure algebra (uses `hA` only to
identify the two symmetric halves of `schurStepLast`'s cross term). -/
lemma schurStepLast_quadratic_eq
  {R : Type*} [Field R]
  {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) R}
    (hA : A.IsSymm) (w : Fin g → R) :
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

end SchurStepDef

section PivotSqrt

/-- The correctly-branched square root of `A.det`, for `A` symmetric with `Re A ≻ 0`: the product
of the principal-branch square roots of the pivots of repeated `schurStepLast`. See the module
docstring for why this differs from (and is well-defined where) `A.det ^ (1/2 : ℂ)` is not. -/
noncomputable def pivotSqrt :
  (g : ℕ) → Matrix (Fin g) (Fin g) ℂ → ℂ
  | 0, _ => 1
  | g + 1, A => A (Fin.last g) (Fin.last g) ^ (1 / 2 : ℂ) * pivotSqrt g (schurStepLast A)

end PivotSqrt

section BlockBookkeeping

/-! ### Shared Schur-block bookkeeping

The `2×2` block decomposition of `A` around its last coordinate (`blockA₁₁, blockA₁₂, blockA₂₁,
blockA₂₂`), and the `finSumFinEquiv` reindexing lemmas relating it back to `A`, are used
identically by `det_eq_pivot_mul_det_schurStepLast`, `matrix_inv_blocks`, and (later) the
continuous Fourier-transform induction — factored out once here rather than duplicated. -/

private noncomputable def blockA₁₁ {g : ℕ} (A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ) :
    Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => A i.castSucc j.castSucc

private noncomputable def blockA₁₂ {g : ℕ} (A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ) :
    Matrix (Fin g) (Fin 1) ℂ := Matrix.of fun i _ => A i.castSucc (Fin.last g)

private noncomputable def blockA₂₁ {g : ℕ} (A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ) :
    Matrix (Fin 1) (Fin g) ℂ := Matrix.of fun _ j => A (Fin.last g) j.castSucc

private noncomputable def blockA₂₂ {g : ℕ} (A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ) :
    Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => A (Fin.last g) (Fin.last g)

private lemma finSumFinEquiv_castSucc {g : ℕ} (i : Fin g) :
    finSumFinEquiv (Sum.inl i : Fin g ⊕ Fin 1) = i.castSucc := by
  rw [finSumFinEquiv_apply_left]; rfl

private lemma finSumFinEquiv_last {g : ℕ} :
    finSumFinEquiv (Sum.inr (0 : Fin 1) : Fin g ⊕ Fin 1) = Fin.last g := by
  have h := congrArg finSumFinEquiv (finSumFinEquiv_symm_last (n := g))
  rwa [Equiv.apply_symm_apply] at h

private lemma submatrix_eq_fromBlocks {g : ℕ} (A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ) :
    A.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (blockA₁₁ A) (blockA₁₂ A) (blockA₂₁ A) (blockA₂₂ A) := by
  ext (i | i) (j | j) <;>
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, blockA₁₁, blockA₁₂,
      blockA₂₁, blockA₂₂, finSumFinEquiv_castSucc, Fin.eq_zero, finSumFinEquiv_last]

private lemma blockA₂₂_det {g : ℕ} (A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ) :
    (blockA₂₂ A).det = A (Fin.last g) (Fin.last g) := by
  rw [blockA₂₂, Matrix.det_fin_one, Matrix.of_apply]

private lemma blockA₂₂_isUnit {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (ha : A (Fin.last g) (Fin.last g) ≠ 0) : IsUnit (blockA₂₂ A) := by
  rw [Matrix.isUnit_iff_isUnit_det, blockA₂₂_det]
  exact ha.isUnit

private lemma blockA₂₂_inv {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (ha : A (Fin.last g) (Fin.last g) ≠ 0) :
    (blockA₂₂ A)⁻¹ = Matrix.of fun _ _ => (A (Fin.last g) (Fin.last g))⁻¹ := by
  apply Matrix.inv_eq_right_inv
  ext i j
  have hi : (i : Fin 1) = 0 := Fin.eq_zero i
  have hj : (j : Fin 1) = 0 := Fin.eq_zero j
  simp [Matrix.mul_apply, Matrix.one_apply, hi, hj, blockA₂₂, Matrix.of_apply, mul_inv_cancel₀ ha]

private lemma blockA₁₁_sub_eq_schurStepLast {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (ha : A (Fin.last g) (Fin.last g) ≠ 0) :
    blockA₁₁ A - blockA₁₂ A * (blockA₂₂ A)⁻¹ * blockA₂₁ A = schurStepLast A := by
  rw [blockA₂₂_inv ha]
  ext i j
  simp only [blockA₁₁, blockA₁₂, blockA₂₁, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one,
    schurStepLast, div_eq_mul_inv, Matrix.of_apply]
  ring

end BlockBookkeeping

section DeterminantIdentity

/-- Determinant Schur identity for one-coordinate elimination: `A.det` factors as the pivot times
the determinant of the Schur complement. Needs `A (last) (last) ≠ 0`, which in our application
follows from `schurStepLast_re_posDef`'s hypothesis via `Matrix.PosDef.diag_pos`. -/
lemma det_eq_pivot_mul_det_schurStepLast {g : ℕ} {A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ}
    (ha : A (Fin.last g) (Fin.last g) ≠ 0) :
    A.det = A (Fin.last g) (Fin.last g) * (schurStepLast A).det := by
  classical
  haveI : Invertible (blockA₂₂ A) := (blockA₂₂_isUnit ha).invertible
  have hdetA : A.det = (Matrix.fromBlocks (blockA₁₁ A) (blockA₁₂ A) (blockA₂₁ A) (blockA₂₂ A)).det := by
    rw [← submatrix_eq_fromBlocks, Matrix.det_submatrix_equiv_self]
  rw [hdetA, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv, blockA₂₂_det,
    blockA₁₁_sub_eq_schurStepLast ha]

end DeterminantIdentity

section InverseIdentity

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
  haveI hA22 : Invertible (blockA₂₂ A) := (blockA₂₂_isUnit ha).invertible
  have hschur : blockA₁₁ A - blockA₁₂ A * (blockA₂₂ A)⁻¹ * blockA₂₁ A = schurStepLast A :=
    blockA₁₁_sub_eq_schurStepLast ha
  rw [← Matrix.invOf_eq_nonsing_inv] at hschur
  have hSchurUnit : IsUnit (blockA₁₁ A - blockA₁₂ A * ⅟(blockA₂₂ A) * blockA₂₁ A).det := by
    rw [hschur]; exact hA''.isUnit
  haveI hSchurInv : Invertible (blockA₁₁ A - blockA₁₂ A * ⅟(blockA₂₂ A) * blockA₂₁ A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hSchurUnit |>.invertible
  haveI hFB : Invertible (Matrix.fromBlocks (blockA₁₁ A) (blockA₁₂ A) (blockA₂₁ A) (blockA₂₂ A)) :=
    Matrix.fromBlocks₂₂Invertible (blockA₁₁ A) (blockA₁₂ A) (blockA₂₁ A) (blockA₂₂ A)
  have hinvblock :=
    Matrix.invOf_fromBlocks₂₂_eq (blockA₁₁ A) (blockA₁₂ A) (blockA₂₁ A) (blockA₂₂ A)
  rw [Matrix.invOf_eq_nonsing_inv] at hinvblock
  have hAinv_sub : A⁻¹.submatrix finSumFinEquiv finSumFinEquiv =
      (Matrix.fromBlocks (blockA₁₁ A) (blockA₁₂ A) (blockA₂₁ A) (blockA₂₂ A))⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv, submatrix_eq_fromBlocks]
  rw [hinvblock, Matrix.invOf_eq_nonsing_inv, Matrix.invOf_eq_nonsing_inv] at hAinv_sub
  rw [Matrix.invOf_eq_nonsing_inv] at hschur
  rw [hschur] at hAinv_sub
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    have h1 := congrFun (congrFun hAinv_sub (Sum.inl i)) (Sum.inl j)
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁] at h1
    rwa [finSumFinEquiv_castSucc, finSumFinEquiv_castSucc] at h1
  · intro i
    have h1 := congrFun (congrFun hAinv_sub (Sum.inl i)) (Sum.inr 0)
    simp only [Matrix.submatrix_apply, finSumFinEquiv_castSucc, finSumFinEquiv_last,
      Matrix.fromBlocks_apply₁₂] at h1
    rw [h1]
    simp only [Matrix.neg_apply, Matrix.mul_apply, blockA₂₂_inv ha, blockA₁₂, Fin.sum_univ_one,
      div_eq_mul_inv, Matrix.of_apply]
    ring
  · intro j
    have h1 := congrFun (congrFun hAinv_sub (Sum.inr 0)) (Sum.inl j)
    simp only [Matrix.submatrix_apply, finSumFinEquiv_castSucc, finSumFinEquiv_last,
      Matrix.fromBlocks_apply₂₁] at h1
    rw [h1]
    simp only [Matrix.neg_apply, Matrix.mul_apply, blockA₂₂_inv ha, blockA₂₁, Fin.sum_univ_one,
      div_eq_mul_inv, Matrix.of_apply]
    rw [neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  · have h1 := congrFun (congrFun hAinv_sub (Sum.inr 0)) (Sum.inr 0)
    simp only [Matrix.submatrix_apply, finSumFinEquiv_last, Matrix.fromBlocks_apply₂₂] at h1
    rw [h1]
    simp only [Matrix.add_apply, Matrix.mul_apply, blockA₂₂_inv ha, blockA₁₂, blockA₂₁,
      Fin.sum_univ_one, div_eq_mul_inv, Matrix.of_apply]
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

end InverseIdentity

section PivotProperties

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

end PivotProperties

section InverseProperties

/-- A symmetric complex matrix with positive-definite real part has an inverse with
positive-definite real part. -/
lemma nonsing_inv_re_posDef {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ)
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

end InverseProperties
