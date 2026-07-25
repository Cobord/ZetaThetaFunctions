import Mathlib.LinearAlgebra.SymplecticGroup
import ZetaThetaFunctions.ThetaFunctions
import ZetaThetaFunctions.Sp2gR
import ZetaThetaFunctions.SiegelUpperHalfSpace
import ZetaThetaFunctions.PoissonSummation

/-!
# Siegel Modular Group

The classical fractional-linear `MulAction` of the symplectic group `Sp2gR (R := R) g`
(`ZetaThetaFunctions/Sp2gR.lean`) on the Siegel upper half-space `SiegelUpperHalfSpace g`
(`ZetaThetaFunctions/SiegelUpperHalfSpace.lean`, imported not defined here), `τ ↦ (Aτ+B)(Cτ+D)⁻¹`,
and its induced action on Riemann theta data (`ZetaThetaFunctions/ThetaFunctions.lean`). The same
construction, specialized to `R := ℝ` and `R := ℤ` (abbreviated `Sp2gZ`), covers both the real and
the integral (Siegel modular) symplectic groups uniformly.

## Main definitions

* `siegelMatrixAction`/`siegelSMul`/the `MulAction (Sp2gR (R := R) g) (SiegelUpperHalfSpace g)`
  instance: the fractional-linear action, built from the block decomposition of a symplectic
  matrix (cast entrywise into `ℂ` via the ring hom `(algebraMap R ℂ).mapMatrix`) and `τ`'s Gram
  matrix `τ.toMatrix = Q_Re + I Q_Im`.
* `Sp2gZ g := Sp2gR (R := ℤ) g`: the integral (Siegel modular) group.
* `RiemannThetaAble_siegelSMul`: the induced action of `Sp2gR (R := R) g` on
  `ThetaAbleQuadraticForm`-bundled Riemann theta data, and the theta transformation laws under the
  classical `T`/`GL`/`S` generators (`section ThetaTransform`).

## Sections

* `SymplecticBlocks`: block projections and Hermitian-transpose-vs-plain-transpose lemmas for
  `(algebraMap R ℂ)`-cast blocks.
* `FractionalLinearMatrixAction`: the matrix-level action `siegelMatrixAction` and preservation of
  the Siegel conditions (symmetry, `CZ+D` invertible, `Im` stays positive definite), including the
  `T`/`GL`/`S`-generator block matrices (`Sp2gR.Tmatrix`/`GLmatrix`/`Smatrix`) and identity case.
* `BundledSiegelAction`: the induced `MulAction (Sp2gR (R := R) g) (SiegelUpperHalfSpace g)`
  instance on bundled Siegel points, and the cocycle identity behind `mul_smul`.
* `IntegralSiegel`: the integral group `Sp2gZ`.
* `ThetaTransform`: `RiemannThetaAble_siegelSMul` and the theta transformation law under each
  generator — `ThetaTransformTMatrix`/`ThetaTransformGLMatrix` (termwise identities,
  `theta_fun_after_Tmatrix_diagEven`/`theta_fun_after_GLmatrix_reindex`) and `ThetaTransformSMatrix`
  (genuine Poisson resummation via `PoissonSummation.lean`, `theta_fun_after_Smatrix`).

-/

variable {R : Type*} [CommRing R] [Algebra R ℝ] [Algebra R ℂ] [IsScalarTower R ℝ ℂ]
variable {g : ℕ}

-- `SiegelUpperHalfSpace` and its extensionality lemma now live in `SiegelUpperHalfSpace.lean`.

section SymplecticBlocks

/-- `(algebraMap R ℂ)`-cast values are fixed by complex conjugation: `IsScalarTower R ℝ ℂ` forces
`algebraMap R ℂ` to factor through `ℝ`. -/
private lemma algebraMap_star_eq (x : R) : star (algebraMap R ℂ x) = algebraMap R ℂ x := by
  rw [IsScalarTower.algebraMap_apply R ℝ ℂ]
  simp

/-- `(algebraMap R ℂ)`-cast blocks are Hermitian-transpose-equal to plain-transpose (their entries
are real, so conjugation does nothing). -/
private lemma algebraMap_conjTranspose_eq_transpose (X : Matrix (Fin g) (Fin g) R) :
    ((algebraMap R ℂ).mapMatrix X).conjTranspose = ((algebraMap R ℂ).mapMatrix X).transpose := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, algebraMap_star_eq]

end SymplecticBlocks

-- `SiegelUpperHalfSpace.toMatrix`, `quadraticMapOfMatrix`, and the round-trip lemmas connecting
-- them to `gramMatrixReal` now live in `SiegelUpperHalfSpace.lean`.

section FractionalLinearMatrixAction

/-- The numerator `AZ + B` of the Siegel fractional-linear transformation, with blocks cast into
`ℂ` via the bundled ring hom `(algebraMap R ℂ).mapMatrix` (rather than a bare `Matrix.map`), so
that `map_one`/`map_zero`/`map_add`/`map_mul` are available for free when relating this to the
blocks of a product `M * N`. -/
noncomputable def siegelNum
  (M : Sp2gR (R:=R) g)
  (Z : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (algebraMap R ℂ).mapMatrix (Sp2gR.blockA M) * Z + (algebraMap R ℂ).mapMatrix (Sp2gR.blockB M)

/-- The denominator `CZ + D` of the Siegel fractional-linear transformation; see `siegelNum` for
why the blocks are cast via `(algebraMap R ℂ).mapMatrix`. -/
noncomputable def siegelDenom
  (M : Sp2gR (R:=R) g)
  (Z : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (algebraMap R ℂ).mapMatrix (Sp2gR.blockC M) * Z + (algebraMap R ℂ).mapMatrix (Sp2gR.blockD M)

/-- The Siegel fractional-linear action of `M ∈ Sp(2g, ℝ)` on a complex symmetric matrix `Z`:
`Z ↦ (AZ + B)(CZ + D)⁻¹`. Junk-valued (via `Matrix.inv`'s convention on non-invertible matrices)
away from the Siegel upper half-space; see `siegelDenom_isUnit` for where it is genuinely
invertible. -/
noncomputable def siegelMatrixAction (M : Sp2gR (R:=R) g) (Z : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  siegelNum M Z * (siegelDenom M Z)⁻¹

section TMatrix_Sp2gR

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelNum_Tmatrix (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelNum (Sp2gR.Tmatrix B hB) Z = Z + (algebraMap R ℂ).mapMatrix B := by
  rw [siegelNum, Sp2gR.blockA_Tmatrix, Sp2gR.blockB_Tmatrix, map_one, Matrix.one_mul]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelDenom_Tmatrix (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelDenom (Sp2gR.Tmatrix B hB) Z = 1 := by
  rw [siegelDenom, Sp2gR.blockC_Tmatrix, Sp2gR.blockD_Tmatrix, map_zero, map_one,
    Matrix.zero_mul, zero_add]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelMatrixAction_Tmatrix (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelMatrixAction (Sp2gR.Tmatrix B hB) Z = Z + (algebraMap R ℂ).mapMatrix B := by
  rw [siegelMatrixAction, siegelNum_Tmatrix, siegelDenom_Tmatrix, inv_one, Matrix.mul_one]

end TMatrix_Sp2gR

section GL_Sp2gR

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelNum_GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelNum (Sp2gR.GLmatrix U hU) Z = (algebraMap R ℂ).mapMatrix U * Z := by
  rw [siegelNum, Sp2gR.blockA_GLmatrix, Sp2gR.blockB_GLmatrix, map_zero, add_zero]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelDenom_GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelDenom (Sp2gR.GLmatrix U hU) Z = (algebraMap R ℂ).mapMatrix (U.transpose)⁻¹ := by
  rw [siegelDenom, Sp2gR.blockC_GLmatrix, Sp2gR.blockD_GLmatrix, map_zero, Matrix.zero_mul,
    zero_add]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
/-- `(algebraMap R ℂ)`-cast, applied to `(Uᵀ)⁻¹`, inverts back to the cast of `Uᵀ`: cast the
two-sided-inverse identity `(Uᵀ)⁻¹ * Uᵀ = 1` and use uniqueness of matrix inverses. -/
lemma algebraMap_inv_transpose_GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U) :
    ((algebraMap R ℂ).mapMatrix (U.transpose)⁻¹)⁻¹ = (algebraMap R ℂ).mapMatrix U.transpose := by
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have hUTdet : IsUnit (U.transpose).det := by rwa [Matrix.det_transpose]
  apply Matrix.inv_eq_right_inv
  rw [← map_mul, Matrix.nonsing_inv_mul U.transpose hUTdet, map_one]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
/-- The `GL(g, ℤ)`-action generator acts on the Siegel upper half-space by `Z ↦ U Z Uᵀ`, matching
the classical congruence action on the modulus matrix. -/
lemma siegelMatrixAction_GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelMatrixAction (Sp2gR.GLmatrix U hU) Z
      = (algebraMap R ℂ).mapMatrix U * Z * ((algebraMap R ℂ).mapMatrix U).transpose := by
  have hmap_transpose : (algebraMap R ℂ).mapMatrix U.transpose
      = ((algebraMap R ℂ).mapMatrix U).transpose := by
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  rw [siegelMatrixAction, siegelNum_GLmatrix, siegelDenom_GLmatrix,
    algebraMap_inv_transpose_GLmatrix U hU, hmap_transpose]

end GL_Sp2gR

section SMatrix_Sp2gR

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelNum_Smatrix (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelNum (Sp2gR.Smatrix (R := R) (g := g)) Z = -1 := by
  rw [siegelNum, Sp2gR.blockA_Smatrix, Sp2gR.blockB_Smatrix, map_zero, map_neg, map_one,
    Matrix.zero_mul, zero_add]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelDenom_Smatrix (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelDenom (Sp2gR.Smatrix (R := R) (g := g)) Z = Z := by
  rw [siegelDenom, Sp2gR.blockC_Smatrix, Sp2gR.blockD_Smatrix, map_one, map_zero,
    Matrix.one_mul]
  exact add_zero (M := Matrix (Fin g) (Fin g) ℂ) Z

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelMatrixAction_Smatrix (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelMatrixAction (Sp2gR.Smatrix (R := R) (g := g)) Z = -Z⁻¹ := by
  rw [siegelMatrixAction, siegelNum_Smatrix, siegelDenom_Smatrix]
  simp

end SMatrix_Sp2gR

section IdentitySp2gR

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelNum_one (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelNum (1 : Sp2gR (R := R) g) Z = Z := by
  rw [siegelNum, Sp2gR.blockA_one, Sp2gR.blockB_one, map_one, map_zero, add_zero, Matrix.one_mul]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelDenom_one (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelDenom (1 : Sp2gR (R := R) g) Z = 1 := by
  rw [siegelDenom, Sp2gR.blockC_one, Sp2gR.blockD_one, map_zero, map_one, Matrix.zero_mul, zero_add]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
lemma siegelMatrixAction_one (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelMatrixAction (1 : Sp2gR (R := R) g) Z = Z := by
  rw [siegelMatrixAction, siegelNum_one, siegelDenom_one, inv_one, Matrix.mul_one]

end IdentitySp2gR

/-- `τ.toMatrix` is symmetric (`gramMatrixReal` is always symmetric, since it comes from a
*symmetric* bilinear form `Q.polarBilin`). -/
theorem SiegelUpperHalfSpace.toMatrix_isSymm (τ : SiegelUpperHalfSpace g) :
    τ.toMatrix.IsSymm := by
  show τ.toMatrix.transpose = τ.toMatrix
  ext i j
  rw [Matrix.transpose_apply, SiegelUpperHalfSpace.toMatrix, SiegelUpperHalfSpace.toMatrix,
    gramMatrixReal_symm τ.Q_Re j i, gramMatrixReal_symm τ.Q_Im j i]

private lemma dotProduct_conjTranspose_mulVec (A : Matrix (Fin g) (Fin g) ℂ) (v u : Fin g → ℂ) :
    star v ⬝ᵥ A.conjTranspose.mulVec u = star (A.mulVec v) ⬝ᵥ u := by
  rw [Matrix.mulVec_conjTranspose, Matrix.star_dotProduct_star, ← Matrix.dotProduct_mulVec,
    Matrix.star_dotProduct, star_star]

/-- A real positive definite matrix, cast entrywise into `ℂ`, gives a positive-definite Hermitian
form on `ℂ^g`: `v ↦ star v ⬝ᵥ (S.map ofReal).mulVec v` equals a strictly positive real (cast into
`ℂ`) for `v ≠ 0`. Splits `v = a + Ib` into real/imaginary parts; the cross terms `a ⬝ᵥ Sb` and
`b ⬝ᵥ Sa` cancel (`S` symmetric), leaving `(a ⬝ᵥ Sa) + (b ⬝ᵥ Sb) > 0`. -/
private lemma dotProduct_ofReal_mulVec_pos {S : Matrix (Fin g) (Fin g) ℝ} (hS : S.PosDef)
    {v : Fin g → ℂ} (hv : v ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ star v ⬝ᵥ (S.map Complex.ofReal).mulVec v = (r : ℂ) := by
  set a : Fin g → ℝ := fun i => (v i).re with ha
  set b : Fin g → ℝ := fun i => (v i).im with hb
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨ha0, hb0⟩ := h
    exact hv (funext fun i => Complex.ext (congrFun ha0 i) (congrFun hb0 i))
  have hSsymm : ∀ i j : Fin g, S i j = S j i := by
    intro i j
    have h := congrFun (congrFun hS.1 i) j
    rw [Matrix.conjTranspose_apply] at h
    exact h.symm
  have hvi : ∀ i, v i = (a i : ℂ) + Complex.I * (b i : ℂ) := by
    intro i
    rw [mul_comm]
    exact (Complex.re_add_im (v i)).symm
  have hstar : ∀ i, star (v i) = (a i : ℂ) - Complex.I * (b i : ℂ) := by
    intro i
    rw [hvi i, Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  have hexpand : ∀ i j : Fin g,
      star (v i) * ((S.map Complex.ofReal) i j * v j)
      = (S i j : ℂ) * ((a i : ℂ) * a j + (b i : ℂ) * b j) +
        Complex.I * ((S i j : ℂ) * ((a i : ℂ) * b j - (b i : ℂ) * a j)) := by
    intro i j
    rw [hvi j, hstar i, Matrix.map_apply]
    linear_combination (-(S i j : ℂ) * (b i : ℂ) * (b j : ℂ)) * Complex.I_mul_I
  have hcrossC : ∑ i, ∑ j, (S i j : ℂ) * ((a i : ℂ) * b j - (b i : ℂ) * a j) = 0 := by
    have hswap : ∑ i, ∑ j, (S i j : ℂ) * ((b i : ℂ) * a j)
        = ∑ i, ∑ j, (S i j : ℂ) * ((a i : ℂ) * b j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hSsymm j i]
      ring
    simp only [mul_sub, Finset.sum_sub_distrib, hswap, sub_self]
  have haa : ∑ i, ∑ j, (S i j : ℂ) * ((a i : ℂ) * a j) = ((a ⬝ᵥ S.mulVec a : ℝ) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hbb : ∑ i, ∑ j, (S i j : ℂ) * ((b i : ℂ) * b j) = ((b ⬝ᵥ S.mulVec b : ℝ) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : star v ⬝ᵥ (S.map Complex.ofReal).mulVec v
      = ((a ⬝ᵥ S.mulVec a + b ⬝ᵥ S.mulVec b : ℝ) : ℂ) := by
    show ∑ i, star (v i) * ∑ j, (S.map Complex.ofReal) i j * v j = _
    simp_rw [Finset.mul_sum, hexpand, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcrossC, mul_zero, add_zero, haa, hbb]
    push_cast
    ring
  refine ⟨a ⬝ᵥ S.mulVec a + b ⬝ᵥ S.mulVec b, ?_, hval⟩
  rcases hab with ha0 | hb0
  · have h1 : 0 < a ⬝ᵥ S.mulVec a := hS.dotProduct_mulVec_pos ha0
    have h2 : 0 ≤ b ⬝ᵥ S.mulVec b := by
      rcases eq_or_ne b 0 with hb0 | hb0
      · simp [hb0]
      · exact (hS.dotProduct_mulVec_pos hb0).le
    linarith
  · have h1 : 0 < b ⬝ᵥ S.mulVec b := hS.dotProduct_mulVec_pos hb0
    have h2 : 0 ≤ a ⬝ᵥ S.mulVec a := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · simp [ha0]
      · exact (hS.dotProduct_mulVec_pos ha0).le
    linarith

private lemma dotProduct_ofReal_mulVec_ne_zero {S : Matrix (Fin g) (Fin g) ℝ} (hS : S.PosDef)
    {v : Fin g → ℂ} (hv : v ≠ 0) :
    star v ⬝ᵥ (S.map Complex.ofReal).mulVec v ≠ 0 := by
  obtain ⟨r, hr, heq⟩ := dotProduct_ofReal_mulVec_pos hS hv
  rw [heq]
  exact_mod_cast hr.ne'

/-- The key Hermitian identity behind both `siegelDenom_isUnit` and
`siegelMatrixAction_im_posDef`: `Wᴴ*Num - Numᴴ*W = 2i•Y`, where `W := siegelDenom M Z`,
`Num := siegelNum M Z`, `Y := Im Z` (as a real matrix cast into `ℂ`), for `Z := τ.toMatrix`. Derived
purely from the symplectic block relations and `Z`'s symmetry — no invertibility needed yet. -/
private lemma siegelDenom_conjTranspose_key (M : Sp2gR (R:=R) g) (τ : SiegelUpperHalfSpace g) :
    (siegelDenom M τ.toMatrix).conjTranspose * siegelNum M τ.toMatrix
      - (siegelNum M τ.toMatrix).conjTranspose * siegelDenom M τ.toMatrix
    = (2 * Complex.I) • (gramMatrixReal τ.Q_Im).map Complex.ofReal := by
  have hZsymm : τ.toMatrix.transpose = τ.toMatrix := τ.toMatrix_isSymm
  have hZconj : τ.toMatrix.map star
      = τ.toMatrix - (2 * Complex.I) • (gramMatrixReal τ.Q_Im).map Complex.ofReal := by
    ext i j
    show star (τ.toMatrix i j)
        = τ.toMatrix i j - 2 * Complex.I * ((gramMatrixReal τ.Q_Im).map Complex.ofReal i j)
    simp only [SiegelUpperHalfSpace.toMatrix, Matrix.map_apply, Complex.star_def]
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal]
    ring
  set AMat := (algebraMap R ℂ).mapMatrix M.blockA with hAMat
  set BMat := (algebraMap R ℂ).mapMatrix M.blockB with hBMat
  set CMat := (algebraMap R ℂ).mapMatrix M.blockC with hCMat
  set DMat := (algebraMap R ℂ).mapMatrix M.blockD with hDMat
  set Z := τ.toMatrix with hZ
  have hZconjT : Z.conjTranspose = Z.map star := by
    show (Z.map star).transpose = Z.map star
    rw [← Matrix.transpose_map, hZsymm]
  obtain ⟨r1, r2, r3, r4⟩ := Sp2gR.block_relations_complex M
  have hAconjT := algebraMap_conjTranspose_eq_transpose M.blockA
  have hBconjT := algebraMap_conjTranspose_eq_transpose M.blockB
  have hCconjT := algebraMap_conjTranspose_eq_transpose M.blockC
  have hDconjT := algebraMap_conjTranspose_eq_transpose M.blockD
  have hkey0 : (siegelDenom M Z).conjTranspose * siegelNum M Z
      - (siegelNum M Z).conjTranspose * siegelDenom M Z = Z - Z.conjTranspose := by
    show (CMat * Z + DMat).conjTranspose * (AMat * Z + BMat)
        - (AMat * Z + BMat).conjTranspose * (CMat * Z + DMat) = Z - Z.conjTranspose
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hCconjT, hDconjT, hAconjT, hBconjT]
    linear_combination (norm := noncomm_ring) -Z.conjTranspose * r1 * Z - Z.conjTranspose * r3
      + r4 * Z - r2
  rw [hkey0, hZconjT, hZconj]
  abel

/-- `CZ + D` is invertible whenever `Z` is the matrix of a genuine Siegel point (`Q_Im` positive
definite). The classical argument: `Wᴴ*Num - Numᴴ*W = 2i•Y` (`siegelDenom_conjTranspose_key`);
pairing with any `v` in the kernel of `W` against `star v` kills both terms on the left, forcing
`star v ⬝ᵥ Y.mulVec v = 0`, contradicting `Y`'s positive-definiteness
(`dotProduct_ofReal_mulVec_ne_zero`) unless `v = 0`. -/
theorem siegelDenom_isUnit (M : Sp2gR (R:=R) g) (τ : SiegelUpperHalfSpace g) :
    IsUnit (siegelDenom M τ.toMatrix).det := by
  have hkey := siegelDenom_conjTranspose_key M τ
  have hkernel : ∀ v : Fin g → ℂ, (siegelDenom M τ.toMatrix).mulVec v = 0 → v = 0 := by
    intro v hv
    by_contra hvne
    have hL : star v ⬝ᵥ ((siegelDenom M τ.toMatrix).conjTranspose * siegelNum M τ.toMatrix
        - (siegelNum M τ.toMatrix).conjTranspose * siegelDenom M τ.toMatrix).mulVec v = 0 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hv, Matrix.mulVec_zero, dotProduct_zero, sub_zero,
        dotProduct_conjTranspose_mulVec, hv, star_zero, zero_dotProduct]
    rw [hkey, Matrix.smul_mulVec, dotProduct_smul] at hL
    have h2I : (2 * Complex.I : ℂ) ≠ 0 := by simp
    exact dotProduct_ofReal_mulVec_ne_zero (gramMatrixReal_posDef τ.Q_Im τ.hQIm) hvne
      ((mul_eq_zero.mp hL).resolve_left h2I)
  have hinj : Function.Injective (siegelDenom M τ.toMatrix).mulVec := by
    intro v w hvw
    have h0 : (siegelDenom M τ.toMatrix).mulVec (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hkernel _ h0)
  have hMunit : IsUnit (siegelDenom M τ.toMatrix) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact (Matrix.isUnit_iff_isUnit_det _).mp hMunit

/-- The Siegel fractional-linear action preserves matrix symmetry: `(AZ+B)(CZ+D)⁻¹` is again
symmetric whenever `Z` is and `!![A,B;C,D]` is symplectic. Needed to identify
`(siegelSMul M τ).toMatrix` with `siegelMatrixAction M τ.toMatrix` (`quadraticMapOfMatrix` only
inverts `gramMatrixReal` on *symmetric* matrices, `quadraticMapOfMatrix_gramMatrixReal`), which in
turn is needed for `mul_smul`'s cocycle identity `(M*N)•τ = M•(N•τ)`. -/
theorem siegelMatrixAction_isSymm (M : Sp2gR (R:=R) g) (τ : SiegelUpperHalfSpace g) :
    (siegelMatrixAction M τ.toMatrix).IsSymm := by
  unfold Matrix.IsSymm
  unfold siegelMatrixAction
  unfold siegelNum
  unfold siegelDenom
  set AMat := (algebraMap R ℂ).mapMatrix M.blockA with hAMat
  set BMat := (algebraMap R ℂ).mapMatrix M.blockB with hBMat
  set CMat := (algebraMap R ℂ).mapMatrix M.blockC with hCMat
  set DMat := (algebraMap R ℂ).mapMatrix M.blockD with hDMat
  set tau := τ.toMatrix with htau
  have hZsymm : tau.transpose = tau := τ.toMatrix_isSymm
  have hWunit : IsUnit (CMat * tau + DMat).det := siegelDenom_isUnit M τ
  set W := CMat * tau + DMat with hW
  set Num := AMat * tau + BMat with hNum
  have hmap_transpose : ∀ X : Matrix (Fin g) (Fin g) R,
      (algebraMap R ℂ).mapMatrix X.transpose = ((algebraMap R ℂ).mapMatrix X).transpose := by
    intro X
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  obtain ⟨r1, r2, r3, r4⟩ := Sp2gR.block_relations M
  have r1' : AMat.transpose * CMat = CMat.transpose * AMat := by
    rw [hAMat, hCMat, ← hmap_transpose, ← hmap_transpose, ← map_mul, ← map_mul, r1]
  have r2' : BMat.transpose * DMat = DMat.transpose * BMat := by
    rw [hBMat, hDMat, ← hmap_transpose, ← hmap_transpose, ← map_mul, ← map_mul, r2]
  have r3' : AMat.transpose * DMat - CMat.transpose * BMat = 1 := by
    rw [hAMat, hDMat, hCMat, hBMat, ← hmap_transpose, ← hmap_transpose, ← map_mul, ← map_mul,
      ← map_sub, r3, map_one]
  have r4' : DMat.transpose * AMat - BMat.transpose * CMat = 1 := by
    rw [hDMat, hAMat, hBMat, hCMat, ← hmap_transpose, ← hmap_transpose, ← map_mul, ← map_mul,
      ← map_sub, r4, map_one]
  -- the key symmetric-cocycle identity: `Wᵀ * Num = Numᵀ * W`
  have hkey : W.transpose * Num = Num.transpose * W := by
    rw [hW, hNum, Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_mul, hZsymm]
    linear_combination (norm := noncomm_ring) -tau * r1' * tau - tau * r3' + r4' * tau - r2'
  have hWTunit : IsUnit W.transpose.det := by rw [Matrix.det_transpose]; exact hWunit
  have hstep : Num = W.transpose⁻¹ * Num.transpose * W := by
    have h2 := congrArg (fun X => W.transpose⁻¹ * X) hkey
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul W.transpose hWTunit, Matrix.one_mul,
      ← Matrix.mul_assoc] at h2
    exact h2
  have hfinal : Num * W⁻¹ = W.transpose⁻¹ * Num.transpose := by
    conv_lhs => rw [hstep]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv W hWunit, Matrix.mul_one]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  exact hfinal.symm

/-- For any complex matrix `X`, `X - X.map star = 2i • Im(X)` entrywise (`z - conj z = 2i • z.im`
for each entry). The general fact underlying `siegelDenom_conjTranspose_key`'s `Z`-specific
version, here applied to the *transformed* matrix `Z'` (not yet known to be a `toMatrix` of some
`SiegelUpperHalfSpace`, so the `gramMatrixReal`-based derivation doesn't apply directly). -/
private lemma matrix_sub_map_star (X : Matrix (Fin g) (Fin g) ℂ) :
    X - X.map star = (2 * Complex.I) • (X.map Complex.im).map Complex.ofReal := by
  ext i j
  show X i j - star (X i j) = 2 * Complex.I * ((X i j).im : ℂ)
  rw [Complex.star_def, Complex.sub_conj]
  push_cast
  ring

private lemma real_cast_dotProduct_mulVec (S : Matrix (Fin g) (Fin g) ℝ) (x : Fin g → ℝ) :
    star (fun i => (x i : ℂ)) ⬝ᵥ (S.map Complex.ofReal).mulVec (fun i => (x i : ℂ))
      = ((x ⬝ᵥ S.mulVec x : ℝ) : ℂ) := by
  have hstarreal : star (fun i => (x i : ℂ)) = fun i => (x i : ℂ) := by
    funext i
    rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [hstarreal]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The transformed imaginary part stays positive definite — the standard fact that
`Sp(2g, ℝ)` preserves the Siegel upper half-space. The classical identity
`Im Z' = (CZ+D)⁻¹ᴴ ⬝ Im Z ⬝ (CZ+D)⁻¹` for `Z' := (AZ+B)(CZ+D)⁻¹`, derived from
`siegelDenom_conjTranspose_key` by the same left/right-multiply-by-inverse manipulation as
`siegelMatrixAction_isSymm`, then paired with `dotProduct_ofReal_mulVec_pos` (`Im Z` positive
definite) via `(CZ+D)⁻¹`'s injectivity. -/
theorem siegelMatrixAction_im_posDef (M : Sp2gR (R:=R) g) (τ : SiegelUpperHalfSpace g) :
    (quadraticMapOfMatrix ((siegelMatrixAction M τ.toMatrix).map Complex.im)).PosDef := by
  set Z := τ.toMatrix with hZ
  set W := siegelDenom M Z with hW
  set Num := siegelNum M Z with hNum
  set Y := (gramMatrixReal τ.Q_Im).map Complex.ofReal with hY
  set Z' := siegelMatrixAction M Z with hZ'
  have hZ'eq : Z' = Num * W⁻¹ := rfl
  have hWunit : IsUnit W.det := siegelDenom_isUnit M τ
  have hWHunit : IsUnit W.conjTranspose.det := by
    rw [Matrix.det_conjTranspose]; exact hWunit.star
  have hkey := siegelDenom_conjTranspose_key M τ
  rw [← hW, ← hNum, ← hY] at hkey
  have hstep : Num - W.conjTranspose⁻¹ * Num.conjTranspose * W
      = (2 * Complex.I) • (W.conjTranspose⁻¹ * Y) := by
    have h2 := congrArg (fun X => W.conjTranspose⁻¹ * X) hkey
    simp only [mul_sub] at h2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul W.conjTranspose hWHunit,
      Matrix.one_mul, mul_smul_comm] at h2
    exact h2
  have hfinal : Num * W⁻¹ - W.conjTranspose⁻¹ * Num.conjTranspose
      = (2 * Complex.I) • (W.conjTranspose⁻¹ * Y * W⁻¹) := by
    have h2 := congrArg (fun X => X * W⁻¹) hstep
    simp only [sub_mul] at h2
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv W hWunit, Matrix.mul_one,
      smul_mul_assoc] at h2
    exact h2
  have hZ'conjT : Z'.conjTranspose = W.conjTranspose⁻¹ * Num.conjTranspose := by
    rw [hZ'eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  have hZsymm' : Z'.transpose = Z' := siegelMatrixAction_isSymm M τ
  have hZ'starT : Z'.conjTranspose = Z'.map star := by
    show (Z'.map star).transpose = Z'.map star
    rw [← Matrix.transpose_map, hZsymm']
  have hcombine : (2 * Complex.I) • ((Z'.map Complex.im).map Complex.ofReal)
      = (2 * Complex.I) • (W.conjTranspose⁻¹ * Y * W⁻¹) := by
    rw [← matrix_sub_map_star, ← hZ'starT, hZ'conjT, hZ'eq]
    exact hfinal
  have h2Ine : (2 * Complex.I : ℂ) ≠ 0 := by simp
  have hcong : (Z'.map Complex.im).map Complex.ofReal = W.conjTranspose⁻¹ * Y * W⁻¹ := by
    have h3 := congrArg (fun A => (2 * Complex.I : ℂ)⁻¹ • A) hcombine
    simpa [smul_smul, inv_mul_cancel₀ h2Ine] using h3
  intro x hx
  set v : Fin g → ℂ := fun i => (x i : ℂ) with hv
  have hxne : v ≠ 0 := by
    intro h
    apply hx
    ext i
    have h2 := congrFun h i
    simp only [hv, Pi.zero_apply] at h2
    exact_mod_cast h2
  set u : Fin g → ℂ := W⁻¹.mulVec v with hu
  have hLHS : star v ⬝ᵥ ((Z'.map Complex.im).map Complex.ofReal).mulVec v
      = ((x ⬝ᵥ (Z'.map Complex.im).mulVec x : ℝ) : ℂ) := real_cast_dotProduct_mulVec _ x
  have huW : u ≠ 0 := by
    intro h0
    apply hxne
    have h1 := congrArg W.mulVec h0
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hWunit, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h1
  obtain ⟨r, hr, hreq⟩ := dotProduct_ofReal_mulVec_pos (gramMatrixReal_posDef τ.Q_Im τ.hQIm) huW
  have hRHS : star v ⬝ᵥ (W.conjTranspose⁻¹ * Y * W⁻¹).mulVec v = (r : ℂ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.mulVec_mulVec,
      dotProduct_conjTranspose_mulVec, ← hu, hY]
    exact hreq
  rw [hcong, hRHS] at hLHS
  have hval : x ⬝ᵥ (Z'.map Complex.im).mulVec x = r := by exact_mod_cast hLHS.symm
  rw [quadraticMapOfMatrix_apply]
  have hqv : ∑ i, ∑ j, algebraMap ℝ ℝ ((Z'.map Complex.im) i j) * (x i * x j)
      = x ⬝ᵥ (Z'.map Complex.im).mulVec x := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Algebra.algebraMap_self_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hqv, hval]
  have h2inv : (0 : ℝ) < ⅟(2 : ℝ) := by
    rw [invOf_eq_inv]; norm_num
  exact mul_pos h2inv hr

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
/-- The transformed imaginary part is continuous, being built (via `quadraticMapOfMatrix`) from a
finite sum of continuous bilinear terms. -/
theorem siegelMatrixAction_im_continuous (M : Sp2gR (R:=R) g) (τ : SiegelUpperHalfSpace g) :
    Continuous (quadraticMapOfMatrix ((siegelMatrixAction M τ.toMatrix).map Complex.im)) :=
  quadraticMapOfMatrix_continuous _

end FractionalLinearMatrixAction

section BundledSiegelAction

/-- The Siegel action of `M ∈ Sp(2g, ℝ)` on a Siegel point `τ`, via the classical fractional
linear formula `τ ↦ (AZ+B)(CZ+D)⁻¹` applied to the underlying matrix `Z = τ.toMatrix`, split back
into real/imaginary parts. -/
noncomputable def siegelSMul (M : Sp2gR (R:=R) g) (τ : SiegelUpperHalfSpace g) :
    SiegelUpperHalfSpace g where
  Q_Re := quadraticMapOfMatrix ((siegelMatrixAction M τ.toMatrix).map Complex.re)
  Q_Im := quadraticMapOfMatrix ((siegelMatrixAction M τ.toMatrix).map Complex.im)
  hQIm_cont := siegelMatrixAction_im_continuous M τ
  hQIm := siegelMatrixAction_im_posDef M τ

/-- `(siegelSMul M τ).toMatrix = siegelMatrixAction M τ.toMatrix`: the underlying complex matrix
of the constructed Siegel point really is the matrix computed by `siegelMatrixAction`. Needs
`siegelMatrixAction_isSymm` (so `quadraticMapOfMatrix` genuinely inverts `gramMatrixReal` on the
real/imaginary parts, `gramMatrixReal_quadraticMapOfMatrix` — that lemma needs symmetry). -/
lemma siegelSMul_toMatrix (M : Sp2gR (R:=R) g) (τ : SiegelUpperHalfSpace g) :
    (siegelSMul M τ).toMatrix = siegelMatrixAction M τ.toMatrix := by
  have hZ'symm : (siegelMatrixAction M τ.toMatrix).transpose = siegelMatrixAction M τ.toMatrix :=
    siegelMatrixAction_isSymm M τ
  have hreSymm : ((siegelMatrixAction M τ.toMatrix).map Complex.re).IsSymm := by
    show ((siegelMatrixAction M τ.toMatrix).map Complex.re).transpose
      = (siegelMatrixAction M τ.toMatrix).map Complex.re
    rw [← Matrix.transpose_map, hZ'symm]
  have himSymm : ((siegelMatrixAction M τ.toMatrix).map Complex.im).IsSymm := by
    show ((siegelMatrixAction M τ.toMatrix).map Complex.im).transpose
      = (siegelMatrixAction M τ.toMatrix).map Complex.im
    rw [← Matrix.transpose_map, hZ'symm]
  ext i j
  show (gramMatrixReal (siegelSMul M τ).Q_Re i j : ℂ)
      + Complex.I * (gramMatrixReal (siegelSMul M τ).Q_Im i j : ℂ)
    = siegelMatrixAction M τ.toMatrix i j
  rw [show (siegelSMul M τ).Q_Re
        = quadraticMapOfMatrix ((siegelMatrixAction M τ.toMatrix).map Complex.re) from rfl,
      show (siegelSMul M τ).Q_Im
        = quadraticMapOfMatrix ((siegelMatrixAction M τ.toMatrix).map Complex.im) from rfl,
      gramMatrixReal_quadraticMapOfMatrix hreSymm, gramMatrixReal_quadraticMapOfMatrix himSymm]
  show ((siegelMatrixAction M τ.toMatrix i j).re : ℂ)
      + Complex.I * ((siegelMatrixAction M τ.toMatrix i j).im : ℂ)
    = siegelMatrixAction M τ.toMatrix i j
  rw [mul_comm]
  exact Complex.re_add_im _

private lemma matrix_inv_cocycle {a b c : Matrix (Fin g) (Fin g) ℂ} (hb : IsUnit b.det) :
    (a * b) * (c * b)⁻¹ = a * c⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_assoc a b (b⁻¹ * c⁻¹), ← Matrix.mul_assoc b b⁻¹ c⁻¹,
    Matrix.mul_nonsing_inv b hb, one_mul]

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
/-- The block-matrix cocycle identity behind `mul_smul`: `siegelNum`/`siegelDenom` of `M*N` at `Z`
agree with `siegelNum`/`siegelDenom` of `M` at `N•Z`, composed with `siegelDenom N Z` on the right
— the algebraic content of `(AZ+B)` and `(CZ+D)` for the *product* `M*N` factoring through the
single fractional-linear step for `N`. -/
private lemma siegel_cocycle_helper (M N : Sp2gR (R:=R) g) (Z : Matrix (Fin g) (Fin g) ℂ)
    (hNinv : IsUnit (siegelDenom N Z).det) :
    siegelNum M (siegelMatrixAction N Z) * siegelDenom N Z = siegelNum (M * N) Z ∧
    siegelDenom M (siegelMatrixAction N Z) * siegelDenom N Z = siegelDenom (M * N) Z := by
  have hcancel : siegelNum N Z * (siegelDenom N Z)⁻¹ * siegelDenom N Z = siegelNum N Z :=
    Matrix.nonsing_inv_mul_cancel_right (A := siegelDenom N Z) (siegelNum N Z) hNinv
  have hMatN : siegelMatrixAction N Z = siegelNum N Z * (siegelDenom N Z)⁻¹ := rfl
  have hnumMN : siegelNum (M * N) Z
      = (algebraMap R ℂ).mapMatrix M.blockA * (algebraMap R ℂ).mapMatrix N.blockA * Z
        + (algebraMap R ℂ).mapMatrix M.blockA * (algebraMap R ℂ).mapMatrix N.blockB
        + (algebraMap R ℂ).mapMatrix M.blockB * (algebraMap R ℂ).mapMatrix N.blockC * Z
        + (algebraMap R ℂ).mapMatrix M.blockB * (algebraMap R ℂ).mapMatrix N.blockD := by
    show (algebraMap R ℂ).mapMatrix (Sp2gR.blockA (M * N)) * Z
        + (algebraMap R ℂ).mapMatrix (Sp2gR.blockB (M * N)) = _
    rw [Sp2gR.blockA_mul, Sp2gR.blockB_mul, map_add, map_add, map_mul, map_mul, map_mul, map_mul]
    noncomm_ring
  have hdenomMN : siegelDenom (M * N) Z
      = (algebraMap R ℂ).mapMatrix M.blockC * (algebraMap R ℂ).mapMatrix N.blockA * Z
        + (algebraMap R ℂ).mapMatrix M.blockC * (algebraMap R ℂ).mapMatrix N.blockB
        + (algebraMap R ℂ).mapMatrix M.blockD * (algebraMap R ℂ).mapMatrix N.blockC * Z
        + (algebraMap R ℂ).mapMatrix M.blockD * (algebraMap R ℂ).mapMatrix N.blockD := by
    show (algebraMap R ℂ).mapMatrix (Sp2gR.blockC (M * N)) * Z
        + (algebraMap R ℂ).mapMatrix (Sp2gR.blockD (M * N)) = _
    rw [Sp2gR.blockC_mul, Sp2gR.blockD_mul, map_add, map_add, map_mul, map_mul, map_mul, map_mul]
    noncomm_ring
  refine ⟨?_, ?_⟩
  · show ((algebraMap R ℂ).mapMatrix M.blockA * siegelMatrixAction N Z
        + (algebraMap R ℂ).mapMatrix M.blockB) * siegelDenom N Z = siegelNum (M * N) Z
    rw [hMatN, add_mul, Matrix.mul_assoc, hcancel, hnumMN]
    show (algebraMap R ℂ).mapMatrix M.blockA * siegelNum N Z
        + (algebraMap R ℂ).mapMatrix M.blockB * siegelDenom N Z = _
    rw [show siegelNum N Z = (algebraMap R ℂ).mapMatrix N.blockA * Z
          + (algebraMap R ℂ).mapMatrix N.blockB from rfl,
        show siegelDenom N Z = (algebraMap R ℂ).mapMatrix N.blockC * Z
          + (algebraMap R ℂ).mapMatrix N.blockD from rfl]
    noncomm_ring
  · show ((algebraMap R ℂ).mapMatrix M.blockC * siegelMatrixAction N Z
        + (algebraMap R ℂ).mapMatrix M.blockD) * siegelDenom N Z = siegelDenom (M * N) Z
    rw [hMatN, add_mul, Matrix.mul_assoc, hcancel, hdenomMN]
    show (algebraMap R ℂ).mapMatrix M.blockC * siegelNum N Z
        + (algebraMap R ℂ).mapMatrix M.blockD * siegelDenom N Z = _
    rw [show siegelNum N Z = (algebraMap R ℂ).mapMatrix N.blockA * Z
          + (algebraMap R ℂ).mapMatrix N.blockB from rfl,
        show siegelDenom N Z = (algebraMap R ℂ).mapMatrix N.blockC * Z
          + (algebraMap R ℂ).mapMatrix N.blockD from rfl]
    noncomm_ring

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
/-- The Siegel fractional-linear action is a genuine cocycle at the matrix level:
`(M*N) • Z = M • (N • Z)`, given only that `siegelDenom N Z` is invertible (invertibility of
`siegelDenom M (N • Z)` is *not* needed for this algebraic identity — `Matrix.inv`'s junk value on
non-invertible matrices behaves consistently on both sides). -/
lemma siegelMatrixAction_mul (M N : Sp2gR (R:=R) g) (Z : Matrix (Fin g) (Fin g) ℂ)
    (hNinv : IsUnit (siegelDenom N Z).det) :
    siegelMatrixAction (M * N) Z = siegelMatrixAction M (siegelMatrixAction N Z) := by
  obtain ⟨claimA, claimB⟩ := siegel_cocycle_helper M N Z hNinv
  show siegelNum (M * N) Z * (siegelDenom (M * N) Z)⁻¹
      = siegelNum M (siegelMatrixAction N Z) * (siegelDenom M (siegelMatrixAction N Z))⁻¹
  rw [← claimA, ← claimB]
  exact matrix_inv_cocycle hNinv

/-- `Sp(2g, R)` acts on the genus-`g` Siegel upper half-space by fractional-linear
transformations `τ ↦ (Aτ+B)(Cτ+D)⁻¹`. -/
noncomputable instance : MulAction (Sp2gR (R:=R) g) (SiegelUpperHalfSpace g) where
  smul := siegelSMul
  one_smul τ := by
    have hRe : quadraticMapOfMatrix
        ((siegelMatrixAction (1 : Sp2gR (R := R) g) τ.toMatrix).map Complex.re) = τ.Q_Re := by
      rw [siegelMatrixAction_one, τ.toMatrix_map_re, quadraticMapOfMatrix_gramMatrixReal]
    have hIm : quadraticMapOfMatrix
        ((siegelMatrixAction (1 : Sp2gR (R := R) g) τ.toMatrix).map Complex.im) = τ.Q_Im := by
      rw [siegelMatrixAction_one, τ.toMatrix_map_im, quadraticMapOfMatrix_gramMatrixReal]
    exact SiegelUpperHalfSpace.ext hRe hIm
  mul_smul M N τ := by
    have hNinv : IsUnit (siegelDenom N τ.toMatrix).det := siegelDenom_isUnit N τ
    have hmatcocycle : siegelMatrixAction (M * N) τ.toMatrix
        = siegelMatrixAction M (siegelMatrixAction N τ.toMatrix) :=
      siegelMatrixAction_mul M N τ.toMatrix hNinv
    have hNtau : (siegelSMul N τ).toMatrix = siegelMatrixAction N τ.toMatrix :=
      siegelSMul_toMatrix N τ
    have hRe : quadraticMapOfMatrix ((siegelMatrixAction (M * N) τ.toMatrix).map Complex.re)
        = quadraticMapOfMatrix
          ((siegelMatrixAction M (siegelSMul N τ).toMatrix).map Complex.re) := by
      rw [hNtau, hmatcocycle]
    have hIm : quadraticMapOfMatrix ((siegelMatrixAction (M * N) τ.toMatrix).map Complex.im)
        = quadraticMapOfMatrix
          ((siegelMatrixAction M (siegelSMul N τ).toMatrix).map Complex.im) := by
      rw [hNtau, hmatcocycle]
    show siegelSMul (M * N) τ = siegelSMul M (siegelSMul N τ)
    exact SiegelUpperHalfSpace.ext hRe hIm

end BundledSiegelAction

section SiegelActionHom

/-- The Siegel action of `Sp(2g, R)` on `SiegelUpperHalfSpace g`, packaged as a group
homomorphism into the permutation group of the Siegel upper half-space
(`MulAction.toPermHom` applied to the `MulAction` instance above). -/
noncomputable def siegelMatrixActionHom :
    Sp2gR (R := R) g →* Equiv.Perm (SiegelUpperHalfSpace g) :=
  MulAction.toPermHom (Sp2gR (R := R) g) (SiegelUpperHalfSpace g)

lemma siegelMatrixActionHom_apply (M : Sp2gR (R := R) g) (τ : SiegelUpperHalfSpace g) :
    siegelMatrixActionHom M τ = M • τ := rfl

omit [Algebra R ℝ] [IsScalarTower R ℝ ℂ] in
/-- Any central `M ∈ Sp(2g, R)` acts as the identity on the Siegel fractional-linear formula:
`Sp2gR.blocks_of_mem_center` identifies `M`'s blocks as `A = D = c • I`, `B = C = 0` for a unit
`c : Rˣ`, which collapses the fractional-linear formula `(c•Z)*(c•1)⁻¹` to `Z`. -/
lemma siegelMatrixAction_of_mem_center {M : Sp2gR (R := R) g}
    (hM : M ∈ Subgroup.center (Sp2gR (R := R) g)) (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelMatrixAction M Z = Z := by
  obtain ⟨hB, hC, c, hA, hD⟩ := Sp2gR.blocks_of_mem_center hM
  have hkunit : IsUnit (algebraMap R ℂ (c : R)) := c.isUnit.map (algebraMap R ℂ)
  have hmapc1 : (algebraMap R ℂ).mapMatrix ((c : R) • (1 : Matrix (Fin g) (Fin g) R))
      = algebraMap R ℂ (c : R) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> simp
  have hnum : siegelNum M Z = algebraMap R ℂ (c : R) • Z := by
    rw [siegelNum, hA, hB, hmapc1, map_zero, add_zero, Matrix.smul_mul, Matrix.one_mul]
  have hdenom : siegelDenom M Z = algebraMap R ℂ (c : R) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    rw [siegelDenom, hC, hD, hmapc1, map_zero, Matrix.zero_mul, zero_add]
  have hdenom_inv : (algebraMap R ℂ (c : R) • (1 : Matrix (Fin g) (Fin g) ℂ))⁻¹
      = (algebraMap R ℂ (c : R))⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hkunit.ne_zero, one_smul]
  rw [siegelMatrixAction, hnum, hdenom, hdenom_inv, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, mul_inv_cancel₀ hkunit.ne_zero, one_smul]

/-- The center of `Sp(2g, R)` lies in the kernel of the Siegel action
(`siegelMatrixAction_of_mem_center`), so the action factors through `PSp2gR`. -/
lemma center_le_ker_siegelMatrixActionHom :
    Subgroup.center (Sp2gR (R := R) g) ≤ (siegelMatrixActionHom (R := R) (g := g)).ker := by
  intro M hM
  rw [MonoidHom.mem_ker]
  ext τ
  rw [siegelMatrixActionHom_apply]
  show siegelSMul M τ = τ
  have hZ' : siegelMatrixAction M τ.toMatrix = τ.toMatrix := siegelMatrixAction_of_mem_center hM _
  have hRe : quadraticMapOfMatrix ((siegelMatrixAction M τ.toMatrix).map Complex.re) = τ.Q_Re := by
    rw [hZ', τ.toMatrix_map_re, quadraticMapOfMatrix_gramMatrixReal]
  have hIm : quadraticMapOfMatrix ((siegelMatrixAction M τ.toMatrix).map Complex.im) = τ.Q_Im := by
    rw [hZ', τ.toMatrix_map_im, quadraticMapOfMatrix_gramMatrixReal]
  exact SiegelUpperHalfSpace.ext hRe hIm

/-- The Siegel action, as a group homomorphism from the projective symplectic group `PSp2gR` into
the permutation group of the Siegel upper half-space; it factors through `PSp2gR` because the
center acts trivially (`center_le_ker_siegelMatrixActionHom`). -/
noncomputable def psiegelMatrixActionHom :
    PSp2gR (R := R) g →* Equiv.Perm (SiegelUpperHalfSpace g) :=
  QuotientGroup.lift _ siegelMatrixActionHom center_le_ker_siegelMatrixActionHom

end SiegelActionHom

section IntegralSiegel

/-- The integral symplectic (Siegel modular) group `Sp(2g, ℤ)`, the same `Sp2gR` construction
specialized to `R := ℤ`. It acts on `SiegelUpperHalfSpace g` via the very same `MulAction`
instance above (no separate embedding into `Sp2gR (R := ℝ) g` is needed). -/
abbrev Sp2gZ (g : ℕ) : Type := Sp2gR (R := ℤ) g

noncomputable example (g : ℕ) : MulAction (Sp2gZ g) (SiegelUpperHalfSpace g) := inferInstance

end IntegralSiegel

section ThetaTransform

/-- A symplectic matrix `M : Sp(2g, R)` transforms Riemann theta data by transforming the
underlying quadratic data: `θ(z; Q) ↦ θ(z; M • Q)`. `Q_Re`/`Q_Im` are extracted from `thetaable`'s
own `qRe`/`qIm` (each a `QuadraticMap ℤ (Fin g → ℤ) ℝ`, i.e. real-valued *on the lattice*) via
`latticeQuadToEuclidean`, which builds the real Gram matrix and puts it back as a genuine
`EuclideanSpace`-domain quadratic form (`gramMatrixLattice`/`quadraticMapOfMatrix`). Continuity
(`hQIm_cont`) is then automatic. Establishing positive-definiteness (`hQIm`) from the stronger
summability data in `thetaable` requires an additional analytic argument; lattice positivity alone
would not suffice (see `latticeQuadToEuclidean`'s docstring). From there: bundle
`(Q_Re, Q_Im)` into a Siegel point `τ`, apply the fractional-linear action `M • τ`, and feed the
transformed point's `Q_Re`/`Q_Im` back into `RiemannThetaAble` — the positive-definiteness needed
for the *transformed* side, `(M • τ).hQIm`, comes for free from `siegelMatrixAction_im_posDef` via
the `MulAction` instance. -/
@[reducible]
noncomputable def RiemannThetaAble_siegelSMul (hg : g ≠ 0) (M : Sp2gR (R:=R) g)
    (thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ)) :
    ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ) :=
  have infinite_multiples : (∀ (y : Fin g → ℤ), y ≠ 0 → (Set.range fun n => n • y).Infinite) := by
    intro y hy
    apply Set.infinite_range_of_injective
    intro m n hmn
    change m • y = n • y at hmn
    rw [← natCast_zsmul, ← natCast_zsmul] at hmn
    simpa using smul_left_injective ℤ hy hmn
  have hQIm_pre := thetaable.qIm_posdef infinite_multiples
  have hQrestrict : ∀ (z : Fin g → ℤ),
    (latticeQuadToEuclidean ThetaAbleQuadraticForm.qIm) ((EuclideanSpace.equiv (Fin g) ℝ).symm fun i => ↑(z i)) =
      ThetaAbleQuadraticForm.qIm z :=
    latticeQuadToEuclidean_restrict thetaable.qIm
  have hQIm : (latticeQuadToEuclidean thetaable.qIm).PosDef := thetaable.qImRe_posdef
    (Q := latticeQuadToEuclidean thetaable.qIm)
    hQrestrict
  -- The pre-transformation summand, as a chain of equal complex numbers (`Q := qRe + I qIm`,
  -- a *quadratic form*; `τ.toMatrix`, a *matrix*, related by `complex_quadratic`):
  --   exp (π I Q(x) + 2 π I ⟪z, x⟫)
  --     = exp (π I (qRe(x) + I qIm(x)) + 2 π I ⟪z, x⟫)
  --     = exp (π I * (2:ℂ)⁻¹ * ∑ i, ∑ j, τ.toMatrix i j * x i * x j + 2 π I ⟪z, x⟫)
  -- `M • τ` transforms the *matrix* `τ.toMatrix` by the classical fractional-linear action
  -- That action does not directly transform `Q`.
  let qim := latticeQuadToEuclidean thetaable.qIm
  let qim_half := (2:ℝ)⁻¹ • qim
  let qre := latticeQuadToEuclidean thetaable.qRe
  let qre_half := (2:ℝ)⁻¹ • qre
  have hQIm_half_cont : Continuous qim_half :=
    (latticeQuadToEuclidean_continuous thetaable.qIm).const_smul (2:ℝ)⁻¹
  have hQIm_half_posdef : qim_half.PosDef :=
    hQIm.smul (by norm_num)
  let τ : SiegelUpperHalfSpace g := ⟨qre_half, qim_half, hQIm_half_cont, hQIm_half_posdef⟩
  let τ' : SiegelUpperHalfSpace g := M • τ
  have hQIm'_cont : Continuous ((2:ℝ) • τ'.Q_Im) := τ'.hQIm_cont.const_smul (2:ℝ)
  have hQIm' : ((2:ℝ) • τ'.Q_Im).PosDef := τ'.hQIm.smul (by norm_num)
  RiemannThetaAble hg ((2:ℝ) • τ'.Q_Re) ((2:ℝ) • τ'.Q_Im) hQIm'_cont hQIm'

/-- The `x_summand` term of the theta series after applying `M` to `old_thetaable`.

Writing `M = !![A, B; C, D]` and
`τ_after = (A * τ + B) * (C * τ + D)⁻¹`, its mathematical formula is

`exp (π I * Q_after(x_summand) + 2 π I * z x_summand)`

with

`Q_after(x_summand) = 1 / 2 * x_summandᵀ * τ_after * x_summand`.

Thus the equivalent matrix expression is

`exp (π I / 2 * x_summandᵀ * τ_after * x_summand + 2 π I * z x_summand)`. -/
noncomputable def theta_summand_after
  (g: ℕ) (hg : g ≠ 0) (x_summand : Fin g -> ℤ)
  (M : Sp2gR (R:=R) g)
  (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
  (z : (Fin g → ℤ) →ₗ[ℤ] ℂ)
  : ℂ :=
  let thetaable := RiemannThetaAble_siegelSMul (R:=R)
    hg M old_thetaable
  Complex.exp (↑Real.pi * Complex.I *
    ((thetaable.qRe x_summand : ℂ) + Complex.I * (thetaable.qIm x_summand : ℂ))
    + 2 * ↑Real.pi * Complex.I * (z x_summand))

section ThetaTransformTMatrix

private lemma tau_operator_Tmatrix
  (g : ℕ) (hg : g ≠ 0)
  (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
  (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm)
  (x y : Fin g → ℤ) :
    (tau_operator (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := R) hg (Sp2gR.Tmatrix B hB)
        old_thetaable) x) y =
    (tau_operator (R := ℤ) (thetaable := old_thetaable) x) y +
      2 * ∑ i, ∑ j, (algebraMap R ℂ (B i j)) * (x i : ℂ) * (y j : ℂ) := by
  set old_tau_re := latticeQuadToEuclidean old_thetaable.qRe
  set old_tau_im := latticeQuadToEuclidean old_thetaable.qIm
  have old_tau_im_posdef : old_tau_im.PosDef := by
    apply old_thetaable.qImRe_posdef old_tau_im
    intro u
    change old_tau_im (toEuclidean_ZnRn u) = old_thetaable.qIm u
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm u
  let old_tau : SiegelUpperHalfSpace g :=
    ⟨old_tau_re, old_tau_im, by
      simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm,
      old_tau_im_posdef⟩
  have old_tau_half_cont : Continuous ((2:ℝ)⁻¹ • old_tau_im) :=
    (by simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm :
      Continuous old_tau_im).const_smul (2:ℝ)⁻¹
  have old_tau_half_posdef : ((2:ℝ)⁻¹ • old_tau_im).PosDef := old_tau_im_posdef.smul (by norm_num)
  let old_tau_half : SiegelUpperHalfSpace g :=
    ⟨(2:ℝ)⁻¹ • old_tau_re, (2:ℝ)⁻¹ • old_tau_im, old_tau_half_cont, old_tau_half_posdef⟩
  change
    (tau_operator (R := ℤ)
      (thetaable := RiemannThetaAble hg
        ((2:ℝ) • ((Sp2gR.Tmatrix B hB) • old_tau_half).Q_Re)
        ((2:ℝ) • ((Sp2gR.Tmatrix B hB) • old_tau_half).Q_Im)
        (((Sp2gR.Tmatrix B hB) • old_tau_half).hQIm_cont.const_smul (2:ℝ))
        (((Sp2gR.Tmatrix B hB) • old_tau_half).hQIm.smul (by norm_num))) x) y = _
  unfold tau_operator
  change
    (((RiemannThetaAble hg
        ((2:ℝ) • ((Sp2gR.Tmatrix B hB) • old_tau_half).Q_Re)
        ((2:ℝ) • ((Sp2gR.Tmatrix B hB) • old_tau_half).Q_Im)
        (((Sp2gR.Tmatrix B hB) • old_tau_half).hQIm_cont.const_smul (2:ℝ))
        (((Sp2gR.Tmatrix B hB) • old_tau_half).hQIm.smul (by norm_num))).qRe.polarBilin x y : ℝ) : ℂ) +
        Complex.I *
          (((RiemannThetaAble hg
              ((2:ℝ) • ((Sp2gR.Tmatrix B hB) • old_tau_half).Q_Re)
              ((2:ℝ) • ((Sp2gR.Tmatrix B hB) • old_tau_half).Q_Im)
              (((Sp2gR.Tmatrix B hB) • old_tau_half).hQIm_cont.const_smul (2:ℝ))
              (((Sp2gR.Tmatrix B hB) • old_tau_half).hQIm.smul (by norm_num))).qIm.polarBilin x y
            : ℝ) : ℂ) =
      (old_thetaable.qRe.polarBilin x y : ℂ) +
        Complex.I * (old_thetaable.qIm.polarBilin x y : ℂ) +
          2 * ∑ i, ∑ j, (algebraMap R ℂ (B i j)) * (x i : ℂ) * (y j : ℂ)
  have lattice_polar (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ)
      (u v : Fin g → ℤ) :
      (latticeQuadraticMap Q).polarBilin u v =
        Q.polarBilin (toEuclidean_ZnRn u) (toEuclidean_ZnRn v) := by
    rw [QuadraticMap.polarBilin_apply_apply]
    change Q (toEuclidean_ZnRn (u + v)) - Q (toEuclidean_ZnRn u) -
      Q (toEuclidean_ZnRn v) = _
    rw [map_add]
    rfl
  change
    (((latticeQuadraticMap
        ((2:ℝ) • ((Sp2gR.Tmatrix B hB) • old_tau_half).Q_Re)).polarBilin x y : ℝ) : ℂ) +
      Complex.I *
        (((latticeQuadraticMap
            ((2:ℝ) • ((Sp2gR.Tmatrix B hB) • old_tau_half).Q_Im)).polarBilin x y : ℝ) : ℂ) =
      (old_thetaable.qRe.polarBilin x y : ℂ) +
        Complex.I * (old_thetaable.qIm.polarBilin x y : ℂ) +
          2 * ∑ i, ∑ j, (algebraMap R ℂ (B i j)) * (x i : ℂ) * (y j : ℂ)
  rw [lattice_polar, lattice_polar]
  set B_quad := quadraticMapOfMatrix B
  have hqm_add : ∀ S T : Matrix (Fin g) (Fin g) ℝ,
      quadraticMapOfMatrix (S + T) = quadraticMapOfMatrix S + quadraticMapOfMatrix T := by
    intro S T
    apply QuadraticMap.ext
    intro v
    simp only [QuadraticMap.add_apply, quadraticMapOfMatrix_apply, Matrix.add_apply,
      Algebra.algebraMap_self_apply]
    rw [← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hqm_cast : quadraticMapOfMatrix (B.map (algebraMap R ℝ)) = B_quad := by
    apply QuadraticMap.ext
    intro v
    rw [quadraticMapOfMatrix_apply, quadraticMapOfMatrix_apply]
    simp only [Matrix.map_apply, Algebra.algebraMap_self_apply]
  have halg : ∀ r : ℝ, algebraMap ℝ ℂ r = (r : ℂ) := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one]
  -- `gramMatrixReal_smul`/`quadraticMapOfMatrix_smul` (`QuadraticFormUtils.lean`) push the outer
  -- `(2:ℝ) •` through `old_tau_half`'s internal `(2:ℝ)⁻¹ •` so they cancel.
  have hhalf_toMatrix_re : old_tau_half.toMatrix.map Complex.re
      = (2:ℝ)⁻¹ • old_tau.toMatrix.map Complex.re := by
    rw [SiegelUpperHalfSpace.toMatrix_map_re,
      show old_tau_half.Q_Re = (2:ℝ)⁻¹ • old_tau.Q_Re from rfl, gramMatrixReal_smul,
      SiegelUpperHalfSpace.toMatrix_map_re]
  have hhalf_toMatrix_im : old_tau_half.toMatrix.map Complex.im
      = (2:ℝ)⁻¹ • old_tau.toMatrix.map Complex.im := by
    rw [SiegelUpperHalfSpace.toMatrix_map_im,
      show old_tau_half.Q_Im = (2:ℝ)⁻¹ • old_tau.Q_Im from rfl, gramMatrixReal_smul,
      SiegelUpperHalfSpace.toMatrix_map_im]
  have b_act_tau_re : (2:ℝ) • (Sp2gR.Tmatrix B hB • old_tau_half).Q_Re
      = old_tau.Q_Re + (2:ℝ) • B_quad := by
    show (2:ℝ) • quadraticMapOfMatrix
        ((siegelMatrixAction (Sp2gR.Tmatrix B hB) old_tau_half.toMatrix).map Complex.re)
      = old_tau.Q_Re + (2:ℝ) • B_quad
    rw [siegelMatrixAction_Tmatrix]
    have hsplit : (old_tau_half.toMatrix + (algebraMap R ℂ).mapMatrix B).map Complex.re
        = old_tau_half.toMatrix.map Complex.re + B.map (algebraMap R ℝ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Complex.add_re, RingHom.mapMatrix_apply,
        IsScalarTower.algebraMap_apply R ℝ ℂ, halg, Complex.ofReal_re]
    rw [hsplit, hhalf_toMatrix_re, hqm_add, quadraticMapOfMatrix_smul,
      SiegelUpperHalfSpace.toMatrix_map_re, quadraticMapOfMatrix_gramMatrixReal, hqm_cast,
      smul_add, smul_smul]
    norm_num
  have b_act_tau_im : (2:ℝ) • (Sp2gR.Tmatrix B hB • old_tau_half).Q_Im = old_tau.Q_Im := by
    show (2:ℝ) • quadraticMapOfMatrix
        ((siegelMatrixAction (Sp2gR.Tmatrix B hB) old_tau_half.toMatrix).map Complex.im)
      = old_tau.Q_Im
    rw [siegelMatrixAction_Tmatrix]
    have hsplit : (old_tau_half.toMatrix + (algebraMap R ℂ).mapMatrix B).map Complex.im
        = old_tau_half.toMatrix.map Complex.im := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Complex.add_im, RingHom.mapMatrix_apply,
        IsScalarTower.algebraMap_apply R ℝ ℂ, halg, Complex.ofReal_im, add_zero]
    rw [hsplit, hhalf_toMatrix_im, quadraticMapOfMatrix_smul, SiegelUpperHalfSpace.toMatrix_map_im,
      quadraticMapOfMatrix_gramMatrixReal, smul_smul]
    norm_num
  rw [b_act_tau_re, b_act_tau_im]
  have polar_add (Q₁ Q₂ : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ)
      (u v : EuclideanSpace ℝ (Fin g)) :
      (Q₁ + Q₂).polarBilin u v = Q₁.polarBilin u v + Q₂.polarBilin u v := by
    rw [QuadraticMap.polarBilin_apply_apply]
    change (Q₁ (u + v) + Q₂ (u + v)) - (Q₁ u + Q₂ u) - (Q₁ v + Q₂ v) =
      (Q₁ (u + v) - Q₁ u - Q₁ v) + (Q₂ (u + v) - Q₂ u - Q₂ v)
    ring
  have polar_smul (c : ℝ) (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ)
      (u v : EuclideanSpace ℝ (Fin g)) :
      (c • Q).polarBilin u v = c * Q.polarBilin u v := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    show (c • Q) (u + v) - (c • Q) u - (c • Q) v = c * (Q (u + v) - Q u - Q v)
    simp only [QuadraticMap.smul_apply, smul_eq_mul]
    ring
  rw [polar_add, polar_smul]
  have old_tau_re_restrict : latticeQuadraticMap old_tau.Q_Re = old_thetaable.qRe := by
    apply QuadraticMap.ext
    intro u
    change old_tau_re (toEuclidean_ZnRn u) = old_thetaable.qRe u
    simpa [old_tau_re] using latticeQuadToEuclidean_restrict old_thetaable.qRe u
  have old_tau_im_restrict : latticeQuadraticMap old_tau.Q_Im = old_thetaable.qIm := by
    apply QuadraticMap.ext
    intro u
    change old_tau_im (toEuclidean_ZnRn u) = old_thetaable.qIm u
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm u
  have hold_re : old_tau.Q_Re.polarBilin (toEuclidean_ZnRn x)
      (toEuclidean_ZnRn y) = old_thetaable.qRe.polarBilin x y := by
    rw [← lattice_polar old_tau.Q_Re x y, old_tau_re_restrict]
  have hold_im : old_tau.Q_Im.polarBilin (toEuclidean_ZnRn x)
      (toEuclidean_ZnRn y) = old_thetaable.qIm.polarBilin x y := by
    rw [← lattice_polar old_tau.Q_Im x y, old_tau_im_restrict]
  rw [hold_re, hold_im]
  ring_nf
  set term0 := (old_thetaable.qRe.polarBilin x) y
  set term1 := (old_thetaable.qIm.polarBilin x) y
  set term2 := (B_quad.polarBilin (toEuclidean_ZnRn x)) (toEuclidean_ZnRn y)
  set term3 := ∑ x_1, ∑ x_2, (algebraMap R ℂ) (B x_1 x_2) * ↑(x x_1) * ↑(y x_2)
  norm_num
  rw [mul_comm Complex.I]
  ring_nf
  repeat rw [add_assoc]
  simp
  rw [add_comm]
  simp
  have hBreal : (B.map (algebraMap R ℝ)).IsSymm := by
    show (B.map (algebraMap R ℝ)).transpose = B.map (algebraMap R ℝ)
    rw [← Matrix.transpose_map, hB.eq]
  have hB_quad : B_quad = quadraticMapOfMatrix (B.map (algebraMap R ℝ)) := by
    change quadraticMapOfMatrix B = quadraticMapOfMatrix (B.map (algebraMap R ℝ))
    apply QuadraticMap.ext
    intro u
    rw [quadraticMapOfMatrix_apply, quadraticMapOfMatrix_apply]
    rfl
  have hgram : gramMatrixReal B_quad = B.map (algebraMap R ℝ) := by
    rw [hB_quad]
    exact gramMatrixReal_quadraticMapOfMatrix hBreal
  have hpolar := polarBilin_eq_gramMatrixReal_sum B_quad
    (toEuclidean_ZnRn x) (toEuclidean_ZnRn y)
  rw [hgram] at hpolar
  change (B_quad.polarBilin (toEuclidean_ZnRn x) (toEuclidean_ZnRn y) : ℂ) = _
  rw [hpolar]
  have hterm3 : term3 = ∑ i, ∑ j, (algebraMap R ℂ) (B i j) * (x i : ℂ) * (y j : ℂ) := rfl
  rw [hterm3]
  have hlat : ∀ (z : Fin g → ℤ) (i : Fin g), (toEuclidean_ZnRn z).ofLp i = (z i : ℝ) := by
    intro z i
    simp [latticeEmbedding, pre_latticeEmbedding]
  simp only [hlat]
  push_cast
  simp_rw [IsScalarTower.algebraMap_apply R ℝ ℂ]
  have halg : ∀ r : ℝ, algebraMap ℝ ℂ r = (r : ℂ) := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one]
  simp only [halg, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma theta_summand_after_Tanalog
  (g: ℕ) (hg : g ≠ 0) (x_summand : Fin g -> ℤ)
  (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
  (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm)
  (z : (Fin g → ℤ) →ₗ[ℤ] ℂ)
  : theta_summand_after g hg (x_summand := x_summand) (M:=Sp2gR.Tmatrix B hB) (old_thetaable:=old_thetaable) (z:=z) =
    Complex.exp (↑Real.pi * Complex.I *
      ((old_thetaable.qRe x_summand +
          ∑ i, ∑ j,
            (algebraMap R ℝ (B i j)) * (x_summand i : ℝ) * (x_summand j : ℝ) : ℝ) +
        Complex.I * (old_thetaable.qIm x_summand : ℂ)) +
      2 * ↑Real.pi * Complex.I * (z x_summand)) := by
  unfold theta_summand_after
  generalize hthetaable : RiemannThetaAble_siegelSMul (R := R) hg
    (Sp2gR.Tmatrix B hB) old_thetaable = thetaable
  letI : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ) := thetaable
  have htau : (tau_operator (R := ℤ) x_summand) x_summand =
      (thetaable.qRe.polarBilin x_summand x_summand : ℂ) +
        Complex.I * (thetaable.qIm.polarBilin x_summand x_summand : ℂ) := by
    simp [tau_operator, ofRealLinear, mulILinear]
  have hqRe : thetaable.qRe.polarBilin x_summand x_summand =
      2 * thetaable.qRe x_summand := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    ring
  have hqIm : thetaable.qIm.polarBilin x_summand x_summand =
      2 * thetaable.qIm x_summand := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    ring
  have hquadratic :
      ((thetaable.qRe x_summand : ℂ) + Complex.I * (thetaable.qIm x_summand : ℂ)) =
        (2 : ℂ)⁻¹ * (tau_operator (R := ℤ) x_summand) x_summand := by
    rw [htau, hqRe, hqIm]
    push_cast
    ring
  have hold_tau :
      (tau_operator (R := ℤ) (thetaable := old_thetaable) x_summand) x_summand =
        (old_thetaable.qRe.polarBilin x_summand x_summand : ℂ) +
          Complex.I * (old_thetaable.qIm.polarBilin x_summand x_summand : ℂ) := by
    simp [tau_operator, ofRealLinear, mulILinear]
  have hold_qRe : old_thetaable.qRe.polarBilin x_summand x_summand =
      2 * old_thetaable.qRe x_summand := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    ring
  have hold_qIm : old_thetaable.qIm.polarBilin x_summand x_summand =
      2 * old_thetaable.qIm x_summand := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    ring
  have hold_quadratic :
      ((old_thetaable.qRe x_summand : ℂ) + Complex.I * (old_thetaable.qIm x_summand : ℂ)) =
        (2 : ℂ)⁻¹ *
          (tau_operator (R := ℤ) (thetaable := old_thetaable) x_summand) x_summand := by
    rw [hold_tau, hold_qRe, hold_qIm]
    push_cast
    ring
  have hold_quadratic_with_B :
      ((old_thetaable.qRe x_summand +
          ∑ i, ∑ j,
            (algebraMap R ℝ (B i j)) * (x_summand i : ℝ) * (x_summand j : ℝ) : ℝ) : ℂ) +
          Complex.I * (old_thetaable.qIm x_summand : ℂ) =
        (2 : ℂ)⁻¹ *
          (tau_operator (R := ℤ) (thetaable := old_thetaable) x_summand) x_summand +
            (∑ i, ∑ j,
              (algebraMap R ℝ (B i j)) * (x_summand i : ℝ) * (x_summand j : ℝ) : ℝ) := by
    push_cast
    linear_combination hold_quadratic
  dsimp only
  rw [hquadratic]
  rw [hold_quadratic_with_B]
  congr 1
  rw [add_right_cancel_iff]
  change
    ↑Real.pi * Complex.I *
        ((2 : ℂ)⁻¹ * (tau_operator (R := ℤ) (thetaable := thetaable) x_summand) x_summand) =
      ↑Real.pi * Complex.I *
        ((2 : ℂ)⁻¹ *
            (tau_operator (R := ℤ) (thetaable := old_thetaable) x_summand) x_summand +
          (∑ i, ∑ j,
            (algebraMap R ℝ (B i j)) * (x_summand i : ℝ) * (x_summand j : ℝ) : ℝ))
  rw [← hthetaable]
  rw [tau_operator_Tmatrix]
  simp
  ring_nf
  rw [add_left_cancel_iff]
  simp_rw [IsScalarTower.algebraMap_apply R ℝ ℂ]
  congr 1

/-- The sum of a symmetric, zero-on-the-diagonal `Fin g`-indexed integer array is even: pairing
each off-diagonal `(i,j)` with `(j,i)` doubles it. Proved by induction on the index set, tracking
that inserting a new index `k` into an already-summed set `s` changes the (symmetric) double sum by
`2 * ∑ i ∈ s, f i k` (using `f k k = 0` and `f i k = f k i`), an even increment. -/
private lemma even_sum_sum_of_symm_zero_diag {g : ℕ} (f : Fin g → Fin g → ℤ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    Even (∑ i, ∑ j, f i j) := by
  suffices h : ∀ s : Finset (Fin g), Even (∑ i ∈ s, ∑ j ∈ s, f i j) by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have hexpand : ∑ i ∈ insert k s, ∑ j ∈ insert k s, f i j
        = 2 * (∑ i ∈ s, f k i) + ∑ i ∈ s, ∑ j ∈ s, f i j := by
      rw [Finset.sum_insert hk]
      simp_rw [Finset.sum_insert hk]
      rw [hdiag k, zero_add]
      have hik : ∑ i ∈ s, f i k = ∑ i ∈ s, f k i :=
        Finset.sum_congr rfl fun i _ => hsymm i k
      rw [Finset.sum_add_distrib, hik]
      ring
    rw [hexpand]
    exact (even_two_mul _).add ih

private lemma theta_summand_after_zero
    (g : ℕ) (hg : g ≠ 0) (x : Fin g → ℤ)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    theta_summand_after g hg (x_summand := x)
        (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
        (old_thetaable := old_thetaable) (z := z) =
      Complex.exp (↑Real.pi * Complex.I *
        ((old_thetaable.qRe x : ℂ) + Complex.I * (old_thetaable.qIm x : ℂ))
        + 2 * ↑Real.pi * Complex.I * (z x)) := by
  rw [theta_summand_after_Tanalog (R := ℤ) g hg x old_thetaable
    (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero z]
  norm_num

/-- The theta transformation law for the integral T-shift `M := Sp2gR.Tmatrix B hB`, for `B` with
*even diagonal* only (off-diagonal entries unconstrained): `θ(z; M • old_thetaable) = θ(z;
old_thetaable)`, no shift needed. `theta_fun`'s exponent uses `Q(x) := qRe(x)`, and after
`RiemannThetaAble_siegelSMul`'s convention fix `qRe` carries the *full* (not Gram-halved)
`B`-contribution `∑∑Bᵢⱼxᵢxⱼ`. This splits into an off-diagonal part that is always even (pairing
`(i,j)` with `(j,i)`, `B` symmetric) and a diagonal part `∑Bᵢᵢxᵢ²` that is even whenever each `Bᵢᵢ`
is, so `exp(πI·∑∑Bᵢⱼxᵢxⱼ) = 1` and the two summands agree exactly, at the same `z`. -/
theorem theta_summand_after_Tmatrix_diagEven
    (g : ℕ) (hg : g ≠ 0) (x : Fin g → ℤ)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (B : Matrix (Fin g) (Fin g) ℤ) (hB : B.IsSymm) (hBdiag : ∀ i, Even (B i i))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    theta_summand_after g hg (x_summand := x) (M := Sp2gR.Tmatrix B hB)
        (old_thetaable := old_thetaable) (z := z) =
      theta_summand_after g hg (x_summand := x)
        (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
        (old_thetaable := old_thetaable) (z := z) := by
  rw [theta_summand_after_Tanalog (R := ℤ) g hg x old_thetaable B hB z, theta_summand_after_zero]
  have hBsymm : ∀ i j, B i j = B j i := by
    intro i j
    have h := congrFun (congrFun hB i) j
    rw [Matrix.transpose_apply] at h
    exact h.symm
  set f : Fin g → Fin g → ℤ := fun i j => if i = j then 0 else B i j * x i * x j with hf
  have hfsymm : ∀ i j, f i j = f j i := by
    intro i j
    simp only [hf]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [hBsymm i j]; ring
  have hfdiag : ∀ i, f i i = 0 := fun i => by simp [hf]
  have hfeven := even_sum_sum_of_symm_zero_diag f hfsymm hfdiag
  have hfsum : ∀ i, ∑ j, f i j = (∑ j, B i j * x i * x j) - B i i * x i * x i := by
    intro i
    have hpointwise : ∀ j, f i j = B i j * x i * x j - (if i = j then B i j * x i * x j else 0) := by
      intro j
      simp only [hf]
      split_ifs <;> ring
    simp_rw [hpointwise]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  have hSSsum : ∑ i, ∑ j, f i j
      = (∑ i, ∑ j, B i j * x i * x j) - ∑ i, B i i * x i * x i := by
    simp_rw [hfsum]
    rw [Finset.sum_sub_distrib]
  rw [hSSsum] at hfeven
  have hdiagEven : Even (∑ i, B i i * x i * x i) := by
    rw [even_iff_two_dvd]
    apply Finset.dvd_sum
    intro i _
    rw [← even_iff_two_dvd]
    exact ((hBdiag i).mul_right (x i)).mul_right (x i)
  have hSeven : Even (∑ i, ∑ j, B i j * x i * x j) := by
    have hsum := hfeven.add hdiagEven
    have heq : ((∑ i, ∑ j, B i j * x i * x j) - ∑ i, B i i * x i * x i) +
        ∑ i, B i i * x i * x i = ∑ i, ∑ j, B i j * x i * x j := by ring
    rwa [heq] at hsum
  obtain ⟨K, hK⟩ := hSeven
  conv_lhs =>
    rw [mul_add]
    enter [1]
    norm_num
    rw [mul_add (↑Real.pi * Complex.I)]
  conv_rhs =>
    rw [mul_add]
  set term0 := ↑Real.pi * Complex.I * (old_thetaable.qRe x : ℂ)
  set term1 : ℂ := ↑Real.pi * Complex.I * ∑ x_1, ∑ x_2, (B x_1 x_2 : ℂ) * (x x_1 : ℂ) * (x x_2 : ℂ)
  set term2 := ↑Real.pi * Complex.I * (Complex.I * old_thetaable.qIm x : ℂ)
  set term3 := 2 * ↑Real.pi * Complex.I * z x
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨K, ?_⟩
  have hterm1 : term1 = ↑Real.pi * Complex.I * ((K + K : ℤ) : ℂ) := by
    show ↑Real.pi * Complex.I * ∑ x_1, ∑ x_2, (B x_1 x_2 : ℂ) * (x x_1 : ℂ) * (x x_2 : ℂ) = _
    rw [show (∑ x_1 : Fin g, ∑ x_2 : Fin g, (B x_1 x_2 : ℂ) * (x x_1 : ℂ) * (x x_2 : ℂ))
        = ((∑ i, ∑ j, B i j * x i * x j : ℤ) : ℂ) by push_cast; ring_nf, hK]
  rw [hterm1]
  push_cast
  ring

/-- The theta transformation law for the integral T-shift `M := Sp2gR.Tmatrix B hB`, for `B` with
even diagonal (`hBdiag`): `θ(z; M • old_thetaable) = θ(z; old_thetaable)`, no shift needed. The
series-level statement, obtained by summing `theta_summand_after_Tmatrix_diagEven` (see there for
why only the diagonal needs to be even) over `x` via `tsum_congr`. -/
theorem theta_fun_after_Tmatrix_diagEven
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (B : Matrix (Fin g) (Fin g) ℤ) (hB : B.IsSymm) (hBdiag : ∀ i, Even (B i i))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    ThetaAbleQuadraticForm.theta_fun (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.Tmatrix B hB) old_thetaable) z =
    ThetaAbleQuadraticForm.theta_fun (R := ℤ) (thetaable := old_thetaable) z := by
  have hL : ThetaAbleQuadraticForm.theta_fun (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.Tmatrix B hB) old_thetaable) z
      = ∑' x, theta_summand_after g hg (x_summand := x) (M := Sp2gR.Tmatrix B hB)
          (old_thetaable := old_thetaable) (z := z) := rfl
  have hR : ThetaAbleQuadraticForm.theta_fun (R := ℤ) (thetaable := old_thetaable) z
      = ∑' x, theta_summand_after g hg (x_summand := x)
          (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
          (old_thetaable := old_thetaable) (z := z) :=
    tsum_congr fun x => (theta_summand_after_zero g hg x old_thetaable z).symm
  rw [hL, hR]
  exact tsum_congr fun x =>
    theta_summand_after_Tmatrix_diagEven g hg x old_thetaable B hB hBdiag z

end ThetaTransformTMatrix

section ThetaTransformGLMatrix

/-- The lattice reindexing associated to the congruence action
`τ ↦ U * τ * Uᵀ`: the transformed summand indexed by `x` is compared with the old summand
indexed by `Uᵀ x`. -/
noncomputable def GLmatrix_reindex (U : Matrix (Fin g) (Fin g) ℤ) :
    (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ) :=
  U.transpose.mulVecLin

/-- The inverse lattice reindexing, defined when `U` is a unit matrix over `ℤ`. -/
noncomputable def GLmatrix_reindexInv (U : Matrix (Fin g) (Fin g) ℤ) (_hUT : IsUnit U.transpose) :
    (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ) :=
  (U.transpose)⁻¹.mulVecLin

lemma GLmatrix_reindexInv_reindex (U : Matrix (Fin g) (Fin g) ℤ) (hUT : IsUnit U.transpose)
    (x : Fin g → ℤ) :
    GLmatrix_reindexInv U hUT (GLmatrix_reindex U x) = x := by
  change (U.transpose)⁻¹.mulVec (U.transpose.mulVec x) = x
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul U.transpose
    ((Matrix.isUnit_iff_isUnit_det _).mp hUT), Matrix.one_mulVec]

lemma GLmatrix_reindex_reindexInv (U : Matrix (Fin g) (Fin g) ℤ) (hUT : IsUnit U.transpose)
    (x : Fin g → ℤ) :
    GLmatrix_reindex U (GLmatrix_reindexInv U hUT x) = x := by
  change U.transpose.mulVec ((U.transpose)⁻¹.mulVec x) = x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv U.transpose
    ((Matrix.isUnit_iff_isUnit_det _).mp hUT), Matrix.one_mulVec]

lemma GLmatrix_reindex_bijective (U : Matrix (Fin g) (Fin g) ℤ) (hUT : IsUnit U.transpose) :
    Function.Bijective (GLmatrix_reindex U) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg (GLmatrix_reindexInv U hUT) hxy
    simpa [GLmatrix_reindexInv_reindex] using this
  · intro x
    exact ⟨GLmatrix_reindexInv U hUT x, GLmatrix_reindex_reindexInv U hUT x⟩

/-- The shift functional on the old theta series after reindexing a transformed summand by
`x ↦ Uᵀ x`. Thus `GLmatrix_reindexShift U hUT z y = z ((Uᵀ)⁻¹ y)`. -/
noncomputable def GLmatrix_reindexShift
    (U : Matrix (Fin g) (Fin g) ℤ) (hUT : IsUnit U.transpose)
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    (Fin g → ℤ) →ₗ[ℤ] ℂ :=
  z.comp (GLmatrix_reindexInv U hUT)


/-- The GL congruence law for the full complex quadratic form: its real and imaginary parts are
stored separately in `ThetaAbleQuadraticForm`, but the matrix action transforms their combination
at once. -/
private lemma qReIm_RiemannThetaAble_siegelSMul_GLmatrix
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (U : Matrix (Fin g) (Fin g) ℤ) (hU : IsUnit U) (x : Fin g → ℤ) :
    ((RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.GLmatrix U hU) old_thetaable).qRe x : ℂ) +
        Complex.I *
          ((RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.GLmatrix U hU) old_thetaable).qIm x : ℂ) =
      (old_thetaable.qRe (GLmatrix_reindex U x) : ℂ) +
        Complex.I * (old_thetaable.qIm (GLmatrix_reindex U x) : ℂ) := by
  set old_tau_re := latticeQuadToEuclidean old_thetaable.qRe
  set old_tau_im := latticeQuadToEuclidean old_thetaable.qIm
  have old_tau_im_posdef : old_tau_im.PosDef := by
    apply old_thetaable.qImRe_posdef old_tau_im
    intro u
    change old_tau_im (toEuclidean_ZnRn u) = old_thetaable.qIm u
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm u
  let old_tau : SiegelUpperHalfSpace g :=
    ⟨old_tau_re, old_tau_im, by
      simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm,
      old_tau_im_posdef⟩
  have old_tau_half_cont : Continuous ((2:ℝ)⁻¹ • old_tau_im) :=
    (by simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm :
      Continuous old_tau_im).const_smul (2:ℝ)⁻¹
  have old_tau_half_posdef : ((2:ℝ)⁻¹ • old_tau_im).PosDef := old_tau_im_posdef.smul (by norm_num)
  let old_tau_half : SiegelUpperHalfSpace g :=
    ⟨(2:ℝ)⁻¹ • old_tau_re, (2:ℝ)⁻¹ • old_tau_im, old_tau_half_cont, old_tau_half_posdef⟩
  -- bridge: `RiemannThetaAble_siegelSMul` builds `τ` from `old_thetaable`'s `qRe/qIm` *halved*,
  -- then *doubles* the transformed output. Since the GL congruence action `Z ↦ AZAᵀ` is linear in
  -- `Z`, this halving/doubling commutes straight through it (no extra factor, unlike `T`'s shift).
  have hhalf_toMatrix_re : old_tau_half.toMatrix.map Complex.re
      = (2:ℝ)⁻¹ • old_tau.toMatrix.map Complex.re := by
    rw [SiegelUpperHalfSpace.toMatrix_map_re,
      show old_tau_half.Q_Re = (2:ℝ)⁻¹ • old_tau.Q_Re from rfl, gramMatrixReal_smul,
      SiegelUpperHalfSpace.toMatrix_map_re]
  have hhalf_toMatrix_im : old_tau_half.toMatrix.map Complex.im
      = (2:ℝ)⁻¹ • old_tau.toMatrix.map Complex.im := by
    rw [SiegelUpperHalfSpace.toMatrix_map_im,
      show old_tau_half.Q_Im = (2:ℝ)⁻¹ • old_tau.Q_Im from rfl, gramMatrixReal_smul,
      SiegelUpperHalfSpace.toMatrix_map_im]
  have hhalf_toMatrix : old_tau_half.toMatrix = (2:ℂ)⁻¹ • old_tau.toMatrix := by
    ext i j
    have hre := congrFun (congrFun hhalf_toMatrix_re i) j
    have him := congrFun (congrFun hhalf_toMatrix_im i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hre him
    apply Complex.ext
    · simpa using hre
    · simpa using him
  have hRe_smul : ∀ W : Matrix (Fin g) (Fin g) ℂ,
      ((2:ℂ)⁻¹ • W).map Complex.re = (2:ℝ)⁻¹ • (W.map Complex.re) := by
    intro W
    ext i j
    show ((2:ℂ)⁻¹ * W i j).re = (2:ℝ)⁻¹ * (W i j).re
    rw [show (2:ℂ)⁻¹ = ((2:ℝ)⁻¹ : ℝ) by norm_num, Complex.re_ofReal_mul]
  have hIm_smul : ∀ W : Matrix (Fin g) (Fin g) ℂ,
      ((2:ℂ)⁻¹ • W).map Complex.im = (2:ℝ)⁻¹ • (W.map Complex.im) := by
    intro W
    ext i j
    show ((2:ℂ)⁻¹ * W i j).im = (2:ℝ)⁻¹ * (W i j).im
    rw [show (2:ℂ)⁻¹ = ((2:ℝ)⁻¹ : ℝ) by norm_num, Complex.im_ofReal_mul]
  have bRe : (2:ℝ) • ((Sp2gR.GLmatrix U hU) • old_tau_half).Q_Re
      = ((Sp2gR.GLmatrix U hU) • old_tau).Q_Re := by
    show (2:ℝ) • quadraticMapOfMatrix
        ((siegelMatrixAction (Sp2gR.GLmatrix U hU) old_tau_half.toMatrix).map Complex.re)
      = quadraticMapOfMatrix
        ((siegelMatrixAction (Sp2gR.GLmatrix U hU) old_tau.toMatrix).map Complex.re)
    rw [hhalf_toMatrix, siegelMatrixAction_GLmatrix, siegelMatrixAction_GLmatrix,
      mul_smul_comm, smul_mul_assoc, hRe_smul, quadraticMapOfMatrix_smul, smul_smul]
    norm_num
  have bIm : (2:ℝ) • ((Sp2gR.GLmatrix U hU) • old_tau_half).Q_Im
      = ((Sp2gR.GLmatrix U hU) • old_tau).Q_Im := by
    show (2:ℝ) • quadraticMapOfMatrix
        ((siegelMatrixAction (Sp2gR.GLmatrix U hU) old_tau_half.toMatrix).map Complex.im)
      = quadraticMapOfMatrix
        ((siegelMatrixAction (Sp2gR.GLmatrix U hU) old_tau.toMatrix).map Complex.im)
    rw [hhalf_toMatrix, siegelMatrixAction_GLmatrix, siegelMatrixAction_GLmatrix,
      mul_smul_comm, smul_mul_assoc, hIm_smul, quadraticMapOfMatrix_smul, smul_smul]
    norm_num
  have hGLmatrix : ((Sp2gR.GLmatrix U hU) • old_tau).toMatrix =
      (algebraMap ℤ ℂ).mapMatrix U * old_tau.toMatrix *
        ((algebraMap ℤ ℂ).mapMatrix U).transpose := by
    change (siegelSMul (Sp2gR.GLmatrix U hU) old_tau).toMatrix = _
    rw [siegelSMul_toMatrix, siegelMatrixAction_GLmatrix]
  change
    (((latticeQuadraticMap ((2:ℝ) • ((Sp2gR.GLmatrix U hU) • old_tau_half).Q_Re)) x : ℝ) : ℂ) +
      Complex.I *
        (((latticeQuadraticMap ((2:ℝ) • ((Sp2gR.GLmatrix U hU) • old_tau_half).Q_Im)) x : ℝ) : ℂ) =
      (old_thetaable.qRe (GLmatrix_reindex U x) : ℂ) +
        Complex.I * (old_thetaable.qIm (GLmatrix_reindex U x) : ℂ)
  rw [bRe, bIm]
  have old_tau_re_restrict : latticeQuadraticMap old_tau.Q_Re = old_thetaable.qRe := by
    apply QuadraticMap.ext
    intro u
    change old_tau_re (toEuclidean_ZnRn u) = old_thetaable.qRe u
    simpa [old_tau_re] using latticeQuadToEuclidean_restrict old_thetaable.qRe u
  have old_tau_im_restrict : latticeQuadraticMap old_tau.Q_Im = old_thetaable.qIm := by
    apply QuadraticMap.ext
    intro u
    change old_tau_im (toEuclidean_ZnRn u) = old_thetaable.qIm u
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm u
  rw [← old_tau_re_restrict, ← old_tau_im_restrict]
  simp_rw [latticeQuadraticMap_apply]
  rw [SiegelUpperHalfSpace.complex_quadratic ((Sp2gR.GLmatrix U hU) • old_tau),
    SiegelUpperHalfSpace.complex_quadratic old_tau]
  rw [hGLmatrix]
  have hlat : ∀ (z : Fin g → ℤ) (i : Fin g),
      (toEuclidean_ZnRn z).ofLp i = (z i : ℝ) := by
    intro z i
    simp [latticeEmbedding, pre_latticeEmbedding]
  simp only [hlat]
  let A : Matrix (Fin g) (Fin g) ℂ := (algebraMap ℤ ℂ).mapMatrix U
  let xc : Fin g → ℂ := fun i => (x i : ℂ)
  have hreindex : A.transpose.mulVec xc = fun i => ((GLmatrix_reindex U x i : ℤ) : ℂ) := by
    ext i
    simp [A, xc, GLmatrix_reindex, Matrix.mulVec, dotProduct]
    change ∑ j, (U j i : ℂ) * (x j : ℂ) = ↑(∑ j, x j * U j i)
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    ring
  have quadratic_as_dot (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ) :
      ∑ i, ∑ j, M i j * v i * v j = dotProduct v (M.mulVec v) := by
    rw [Matrix.dot_mulVec_eq_sum_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (2 : ℂ)⁻¹ * (∑ i, ∑ j, (A * old_tau.toMatrix * A.transpose) i j * xc i * xc j) =
    (2 : ℂ)⁻¹ * (∑ i, ∑ j, old_tau.toMatrix i j *
      ((GLmatrix_reindex U x i : ℤ) : ℂ) * ((GLmatrix_reindex U x j : ℤ) : ℂ))
  rw [quadratic_as_dot, quadratic_as_dot, ← hreindex]
  congr 1
  let AT := A.transpose
  have ATT : A = A.transpose.transpose := by
    simp
  conv_lhs =>
    repeat rw [<-Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    rw [ATT]
    rw [Matrix.vecMul_transpose]
  rw [<-ATT]

/-- The real part of `qReIm_RiemannThetaAble_siegelSMul_GLmatrix`. -/
private lemma qRe_RiemannThetaAble_siegelSMul_GLmatrix
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (U : Matrix (Fin g) (Fin g) ℤ) (hU : IsUnit U) (x : Fin g → ℤ) :
    (RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.GLmatrix U hU) old_thetaable).qRe x =
      old_thetaable.qRe (GLmatrix_reindex U x) := by
  have h := congrArg Complex.re
    (qReIm_RiemannThetaAble_siegelSMul_GLmatrix g hg old_thetaable U hU x)
  simpa [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] using h

/-- The imaginary part of `qReIm_RiemannThetaAble_siegelSMul_GLmatrix`. -/
private lemma qIm_RiemannThetaAble_siegelSMul_GLmatrix
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (U : Matrix (Fin g) (Fin g) ℤ) (hU : IsUnit U) (x : Fin g → ℤ) :
    (RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.GLmatrix U hU) old_thetaable).qIm x =
      old_thetaable.qIm (GLmatrix_reindex U x) := by
  have h := congrArg Complex.im
    (qReIm_RiemannThetaAble_siegelSMul_GLmatrix g hg old_thetaable U hU x)
  simpa [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im] using h

private lemma theta_summand_after_GLmatrix_reindex
    (g : ℕ) (hg : g ≠ 0) (x : Fin g → ℤ)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (U : Matrix (Fin g) (Fin g) ℤ) (hU : IsUnit U) (hUT : IsUnit U.transpose)
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    theta_summand_after g hg (x_summand := x) (M := Sp2gR.GLmatrix U hU)
      (old_thetaable := old_thetaable) (z := z) =
      theta_summand_after g hg (x_summand := GLmatrix_reindex U x)
        (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
        (old_thetaable := old_thetaable) (z := GLmatrix_reindexShift U hUT z) := by
  rw [theta_summand_after_zero]
  unfold theta_summand_after
  change
    Complex.exp (↑Real.pi * Complex.I *
      (((RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.GLmatrix U hU) old_thetaable).qRe x : ℂ) +
        Complex.I *
          ((RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.GLmatrix U hU) old_thetaable).qIm x : ℂ)) +
      2 * ↑Real.pi * Complex.I * z x) = _
  rw [qReIm_RiemannThetaAble_siegelSMul_GLmatrix]
  have hshift : GLmatrix_reindexShift U hUT z (GLmatrix_reindex U x) = z x := by
    unfold GLmatrix_reindexShift
    rw [LinearMap.comp_apply, GLmatrix_reindexInv_reindex]
  rw [hshift]

/-- The theta transformation law for the integral GL-generator
`M := !![U, 0; 0, (Uᵀ)⁻¹]`: its action on the modulus is absorbed by reindexing the lattice
through `x ↦ Uᵀ x` and pulling the shift functional back through `(Uᵀ)⁻¹`. -/
theorem theta_fun_after_GLmatrix_reindex
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (U : Matrix (Fin g) (Fin g) ℤ) (hU : IsUnit U) (hUT : IsUnit U.transpose)
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    ThetaAbleQuadraticForm.theta_fun (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.GLmatrix U hU) old_thetaable) z =
    ThetaAbleQuadraticForm.theta_fun (R := ℤ) (thetaable := old_thetaable)
      (GLmatrix_reindexShift U hUT z) := by
  have hL : ThetaAbleQuadraticForm.theta_fun (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.GLmatrix U hU) old_thetaable) z
      = ∑' x, theta_summand_after g hg (x_summand := x) (M := Sp2gR.GLmatrix U hU)
          (old_thetaable := old_thetaable) (z := z) := rfl
  have hR : ThetaAbleQuadraticForm.theta_fun (R := ℤ) (thetaable := old_thetaable)
      (GLmatrix_reindexShift U hUT z) =
      ∑' x, theta_summand_after g hg (x_summand := x)
        (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
        (old_thetaable := old_thetaable) (z := GLmatrix_reindexShift U hUT z) :=
    tsum_congr fun x =>
      (theta_summand_after_zero g hg x old_thetaable (GLmatrix_reindexShift U hUT z)).symm
  rw [hL, hR]
  let e : (Fin g → ℤ) ≃ (Fin g → ℤ) :=
    Equiv.ofBijective (GLmatrix_reindex U) (GLmatrix_reindex_bijective U hUT)
  calc
    ∑' x, theta_summand_after g hg (x_summand := x) (M := Sp2gR.GLmatrix U hU)
        (old_thetaable := old_thetaable) (z := z) =
      ∑' x, theta_summand_after g hg (x_summand := GLmatrix_reindex U x)
        (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
        (old_thetaable := old_thetaable) (z := GLmatrix_reindexShift U hUT z) :=
      tsum_congr fun x => theta_summand_after_GLmatrix_reindex g hg x old_thetaable U hU hUT z
    _ = ∑' x, theta_summand_after g hg (x_summand := x)
        (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
        (old_thetaable := old_thetaable) (z := GLmatrix_reindexShift U hUT z) := by
      simpa [e] using e.tsum_eq
        (fun x => theta_summand_after g hg (x_summand := x)
          (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
          (old_thetaable := old_thetaable) (z := GLmatrix_reindexShift U hUT z))

end ThetaTransformGLMatrix

section ThetaTransformSMatrix

/-! ### The target `theta_fun` identity under `S_g` (Poisson resummation)

`x_summand_quadratic_after_Smatrix`/`theta_summand_after_Smatrix` below compute only the
*summand*-level content of the `S_g` transformation (term `n` of the exponent, rewritten in terms
of the new modulus `-τ⁻¹`) — genuinely relating the two full series `θ(·; τ)` and `θ(·; -τ⁻¹)`
needs an actual Poisson resummation, since (unlike the `T`/`GL` generators) the terms do not match
up termwise. The rank-`g` Poisson summation identity needed for this is
`tsum_exp_neg_quadratic_matrix` (`PoissonSummation.lean`):

`∑' (n : Fin g → ℤ), exp (-π * ∑ i, ∑ j, A i j * n i * n j + 2 * π * ∑ i, b i * n i) =
  1 / pivotSqrt g A *
    ∑' (n : Fin g → ℤ), exp (-π * ∑ i, ∑ j, A⁻¹ i j * (n i + I * b i) * (n j + I * b j))`

for `A : Matrix (Fin g) (Fin g) ℂ` symmetric with `Re A` positive definite and `b : Fin g → ℂ`. -/

/-- Under the Fourier generator `S_g`, the lattice index is unchanged at the level of the
transformed quadratic exponent; its modulus matrix becomes `-τ⁻¹`. Summing these terms is the
separate Poisson-resummation step. -/
lemma x_summand_quadratic_after_Smatrix
    (τ : SiegelUpperHalfSpace g) (x_summand : Fin g → ℤ) :
    ((siegelSMul (Sp2gR.Smatrix (R := R) (g := g)) τ).Q_Re
        (toEuclidean_ZnRn x_summand) : ℂ) +
      Complex.I *
        ((siegelSMul (Sp2gR.Smatrix (R := R) (g := g)) τ).Q_Im
          (toEuclidean_ZnRn x_summand) : ℂ) =
      -(2 : ℂ)⁻¹ * ∑ i, ∑ j, τ.toMatrix⁻¹ i j *
        ((toEuclidean_ZnRn x_summand) i : ℂ) *
        ((toEuclidean_ZnRn x_summand) j : ℂ) := by
  rw [SiegelUpperHalfSpace.complex_quadratic, siegelSMul_toMatrix,
    siegelMatrixAction_Smatrix]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  congr 1
  ext i
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  congr 1
  ext j
  set i_Vec := ((toEuclidean_ZnRn x_summand).ofLp i)
  set j_Vec := ((toEuclidean_ZnRn x_summand).ofLp j)
  ring_nf
  rw [mul_comm _ (i_Vec : ℂ)]
  by_cases hiVec : i_Vec = 0
  · rw [hiVec]
    simp
  · have hiVecC : (i_Vec : ℂ)⁻¹ ≠ 0 := by
      apply inv_ne_zero
      exact_mod_cast hiVec
    conv_lhs => repeat rw [mul_assoc (i_Vec : ℂ)]
    conv_rhs => repeat rw [mul_assoc (i_Vec : ℂ)]
    apply mul_left_cancel₀ hiVecC
    repeat rw [<-mul_assoc (i_Vec : ℂ)⁻¹]
    rw [inv_mul_cancel₀ ?invetbile]
    · repeat rw [one_mul]
      rw [mul_comm _ (j_Vec : ℂ)]
      by_cases hjVec : (j_Vec : ℂ)  = 0
      · rw [hjVec]
        simp
      · repeat rw [mul_assoc (j_Vec : ℂ)]
        apply mul_left_cancel₀ (a:=(j_Vec : ℂ)⁻¹) ?invetbile_j
        · repeat rw [<-mul_assoc]
          rw [inv_mul_cancel₀ hjVec]
          · repeat rw [one_mul]
            simp
            ring_nf
        · simp
          exact_mod_cast hjVec
    · simp
      exact hiVec

/-- The `g × g` complex matrix `qRe + I qIm` underlying a `ThetaAbleQuadraticForm`, in the
standard orthonormal basis after transporting to `EuclideanSpace` via `latticeQuadToEuclidean` —
the `ThetaAbleQuadraticForm` analogue of `SiegelUpperHalfSpace.toMatrix`. -/
noncomputable def thetaableToMatrix
    (thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ)) :
    Matrix (Fin g) (Fin g) ℂ :=
  fun i j => (gramMatrixReal (latticeQuadToEuclidean thetaable.qRe) i j : ℂ) +
    Complex.I * (gramMatrixReal (latticeQuadToEuclidean thetaable.qIm) i j : ℂ)

/-- The summand after applying `S_g`: the transformed quadratic exponent is governed by
`-old_thetaable.toMatrix⁻¹`, via `x_summand_quadratic_after_Smatrix`. Unlike the `T`/`GL`
generators, this is *not* a termwise identity with any single summand of the un-transformed
series (that correspondence only appears after the separate Poisson-resummation step) — it is a
genuine computation of the transformed exponent, not a restatement of the definition. -/
lemma theta_summand_after_Smatrix
    (g : ℕ) (hg : g ≠ 0) (x_summand : Fin g → ℤ)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    theta_summand_after g hg (x_summand := x_summand)
      (M := Sp2gR.Smatrix (R := ℤ) (g := g))
      (old_thetaable := old_thetaable) (z := z) =
    Complex.exp (↑Real.pi * Complex.I *
      (-(2 : ℂ) * ∑ i, ∑ j, (thetaableToMatrix old_thetaable)⁻¹ i j *
        (x_summand i : ℂ) * (x_summand j : ℂ))
      + 2 * ↑Real.pi * Complex.I * (z x_summand)) := by
  simp only [theta_summand_after]
  set old_tau_re := latticeQuadToEuclidean old_thetaable.qRe
  set old_tau_im := latticeQuadToEuclidean old_thetaable.qIm
  have old_tau_im_posdef : old_tau_im.PosDef := by
    apply old_thetaable.qImRe_posdef old_tau_im
    intro u
    change old_tau_im (toEuclidean_ZnRn u) = old_thetaable.qIm u
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm u
  let old_tau : SiegelUpperHalfSpace g :=
    ⟨old_tau_re, old_tau_im, by
      simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm,
      old_tau_im_posdef⟩
  have old_tau_half_cont : Continuous ((2:ℝ)⁻¹ • old_tau_im) :=
    (by simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm :
      Continuous old_tau_im).const_smul (2:ℝ)⁻¹
  have old_tau_half_posdef : ((2:ℝ)⁻¹ • old_tau_im).PosDef := old_tau_im_posdef.smul (by norm_num)
  let old_tau_half : SiegelUpperHalfSpace g :=
    ⟨(2:ℝ)⁻¹ • old_tau_re, (2:ℝ)⁻¹ • old_tau_im, old_tau_half_cont, old_tau_half_posdef⟩
  have hmatrix : thetaableToMatrix old_thetaable = old_tau.toMatrix := rfl
  rw [hmatrix]
  -- bridge: `old_tau_half.toMatrix = (2:ℂ)⁻¹ • old_tau.toMatrix`, exactly as for `T`/`GL`.
  have hhalf_toMatrix_re : old_tau_half.toMatrix.map Complex.re
      = (2:ℝ)⁻¹ • old_tau.toMatrix.map Complex.re := by
    rw [SiegelUpperHalfSpace.toMatrix_map_re,
      show old_tau_half.Q_Re = (2:ℝ)⁻¹ • old_tau.Q_Re from rfl, gramMatrixReal_smul,
      SiegelUpperHalfSpace.toMatrix_map_re]
  have hhalf_toMatrix_im : old_tau_half.toMatrix.map Complex.im
      = (2:ℝ)⁻¹ • old_tau.toMatrix.map Complex.im := by
    rw [SiegelUpperHalfSpace.toMatrix_map_im,
      show old_tau_half.Q_Im = (2:ℝ)⁻¹ • old_tau.Q_Im from rfl, gramMatrixReal_smul,
      SiegelUpperHalfSpace.toMatrix_map_im]
  have hhalf_toMatrix : old_tau_half.toMatrix = (2:ℂ)⁻¹ • old_tau.toMatrix := by
    ext i j
    have hre := congrFun (congrFun hhalf_toMatrix_re i) j
    have him := congrFun (congrFun hhalf_toMatrix_im i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hre him
    apply Complex.ext
    · simpa using hre
    · simpa using him
  have hunit : IsUnit old_tau.toMatrix.det :=
    siegelDenom_Smatrix (R := ℤ) (g := g) old_tau.toMatrix ▸
      siegelDenom_isUnit (Sp2gR.Smatrix (R := ℤ) (g := g)) old_tau
  have hinv_smul : old_tau_half.toMatrix⁻¹ = (2:ℂ) • old_tau.toMatrix⁻¹ := by
    rw [hhalf_toMatrix]
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul, Matrix.mul_nonsing_inv old_tau.toMatrix hunit]
    norm_num
  change
    Complex.exp (↑Real.pi * Complex.I *
      (((latticeQuadraticMap
          ((2:ℝ) • ((Sp2gR.Smatrix (R := ℤ) (g := g)) • old_tau_half).Q_Re)) x_summand : ℝ) +
        Complex.I *
          ((latticeQuadraticMap
              ((2:ℝ) • ((Sp2gR.Smatrix (R := ℤ) (g := g)) • old_tau_half).Q_Im)) x_summand : ℝ))
      + 2 * ↑Real.pi * Complex.I * (z x_summand)) = _
  rw [latticeQuadraticMap_apply, latticeQuadraticMap_apply]
  have hAB := x_summand_quadratic_after_Smatrix (R := ℤ) old_tau_half x_summand
  rw [hinv_smul] at hAB
  have hsum_smul : (∑ i, ∑ j, ((2:ℂ) • old_tau.toMatrix⁻¹) i j *
        ((toEuclidean_ZnRn x_summand) i : ℂ) * ((toEuclidean_ZnRn x_summand) j : ℂ))
      = (2:ℂ) * ∑ i, ∑ j, old_tau.toMatrix⁻¹ i j *
        ((toEuclidean_ZnRn x_summand) i : ℂ) * ((toEuclidean_ZnRn x_summand) j : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hsum_smul] at hAB
  have hstep : ((((2:ℝ) • ((Sp2gR.Smatrix (R := ℤ) (g := g)) • old_tau_half).Q_Re)
        (toEuclidean_ZnRn x_summand) : ℝ) : ℂ) +
      Complex.I *
        ((((2:ℝ) • ((Sp2gR.Smatrix (R := ℤ) (g := g)) • old_tau_half).Q_Im)
          (toEuclidean_ZnRn x_summand) : ℝ) : ℂ) =
      -(2:ℂ) * ∑ i, ∑ j, old_tau.toMatrix⁻¹ i j *
        ((toEuclidean_ZnRn x_summand) i : ℂ) * ((toEuclidean_ZnRn x_summand) j : ℂ) := by
    rw [show (Sp2gR.Smatrix (R := ℤ) (g := g)) • old_tau_half
        = siegelSMul (Sp2gR.Smatrix (R := ℤ) (g := g)) old_tau_half from rfl,
      QuadraticMap.smul_apply, QuadraticMap.smul_apply, smul_eq_mul, smul_eq_mul]
    push_cast
    linear_combination (2 : ℂ) * hAB
  rw [hstep]
  have hlat : ∀ (i : Fin g), (toEuclidean_ZnRn x_summand).ofLp i = (x_summand i : ℝ) := by
    intro i
    simp [latticeEmbedding, pre_latticeEmbedding]
  simp only [hlat]
  push_cast
  ring_nf

/-- `theta_summand_after_Smatrix`, restated with its RHS as a `modulatedGaussian` evaluated at the
lattice point `toEuclidean_ZnRn x_summand` — the form needed to feed into
`tsum_exp_neg_quadratic_matrix`/`modulatedGaussian_hasPoissonSummation` (`PoissonSummation.lean`)
for the Poisson-resummation step. `A := (2 * I) • (thetaableToMatrix old_thetaable)⁻¹` carries the
quadratic part; `b i := I * zCoord z i` carries the shift, via `z x_summand = ∑ i, x_summand i *
zCoord z i` (`z_eq_sum`, `LatticeUtils.lean`). -/
private lemma theta_summand_after_Smatrix_modulatedGaussian
    (g : ℕ) (hg : g ≠ 0) (x_summand : Fin g → ℤ)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    theta_summand_after g hg (x_summand := x_summand)
      (M := Sp2gR.Smatrix (R := ℤ) (g := g))
      (old_thetaable := old_thetaable) (z := z) =
    modulatedGaussian ((2 * Complex.I) • (thetaableToMatrix old_thetaable)⁻¹)
      (fun i => Complex.I * zCoord z i) (toEuclidean_ZnRn x_summand) := by
  rw [theta_summand_after_Smatrix, modulatedGaussian]
  have hlat : ∀ (i : Fin g), (toEuclidean_ZnRn x_summand).ofLp i = (x_summand i : ℝ) := by
    intro i
    simp [latticeEmbedding, pre_latticeEmbedding]
  simp only [hlat, Matrix.smul_apply, smul_eq_mul]
  have hz : (z x_summand : ℂ) = ∑ i, (x_summand i : ℂ) * zCoord z i := z_eq_sum z x_summand
  rw [hz]
  push_cast
  congr 1
  have hquad : (∑ i, ∑ j, 2 * Complex.I * (thetaableToMatrix old_thetaable)⁻¹ i j *
        (x_summand i : ℂ) * (x_summand j : ℂ))
      = 2 * Complex.I * ∑ i, ∑ j, (thetaableToMatrix old_thetaable)⁻¹ i j *
          (x_summand i : ℂ) * (x_summand j : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlin : (∑ i, Complex.I * zCoord z i * (x_summand i : ℂ))
      = Complex.I * ∑ i, (x_summand i : ℂ) * zCoord z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hquad, hlin]
  ring

/-- `old_thetaable`'s own (untransformed) summand, restated as a `modulatedGaussian` at
`A := (-I/2) • thetaableToMatrix old_thetaable` — the same `A` that
`theta_fun_after_Smatrix_poisson_Minv`'s dual sum lands on. Direct from `complex_quadratic` on
`old_tau` (no matrix inverse involved, unlike `theta_summand_after_Smatrix_modulatedGaussian`). -/
private lemma theta_summand_after_zero_modulatedGaussian
    (g : ℕ) (hg : g ≠ 0) (x : Fin g → ℤ)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    theta_summand_after g hg (x_summand := x)
        (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
        (old_thetaable := old_thetaable) (z := z) =
    modulatedGaussian ((-Complex.I / 2) • thetaableToMatrix old_thetaable)
      (fun i => Complex.I * zCoord z i) (toEuclidean_ZnRn x) := by
  rw [theta_summand_after_zero, modulatedGaussian]
  set old_tau_re := latticeQuadToEuclidean old_thetaable.qRe
  set old_tau_im := latticeQuadToEuclidean old_thetaable.qIm
  have old_tau_im_posdef : old_tau_im.PosDef := by
    apply old_thetaable.qImRe_posdef old_tau_im
    intro u
    change old_tau_im (toEuclidean_ZnRn u) = old_thetaable.qIm u
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm u
  let old_tau : SiegelUpperHalfSpace g :=
    ⟨old_tau_re, old_tau_im, by
      simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm,
      old_tau_im_posdef⟩
  have hmatrix : thetaableToMatrix old_thetaable = old_tau.toMatrix := rfl
  rw [hmatrix]
  have hre : old_tau.Q_Re (toEuclidean_ZnRn x) = old_thetaable.qRe x := by
    change old_tau_re (toEuclidean_ZnRn x) = old_thetaable.qRe x
    simpa [old_tau_re] using latticeQuadToEuclidean_restrict old_thetaable.qRe x
  have him : old_tau.Q_Im (toEuclidean_ZnRn x) = old_thetaable.qIm x := by
    change old_tau_im (toEuclidean_ZnRn x) = old_thetaable.qIm x
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm x
  have hquad := SiegelUpperHalfSpace.complex_quadratic old_tau (toEuclidean_ZnRn x)
  rw [hre, him] at hquad
  rw [hquad]
  have hlat : ∀ (i : Fin g), (toEuclidean_ZnRn x).ofLp i = (x i : ℝ) := by
    intro i
    simp [latticeEmbedding, pre_latticeEmbedding]
  simp only [hlat]
  have hz : (z x : ℂ) = ∑ i, (x i : ℂ) * zCoord z i := z_eq_sum z x
  rw [hz]
  push_cast
  congr 1
  have hquadsum : (∑ i, ∑ j, ((-Complex.I / 2) • old_tau.toMatrix) i j *
        (x i : ℂ) * (x j : ℂ))
      = (-Complex.I / 2) * ∑ i, ∑ j, old_tau.toMatrix i j * (x i : ℂ) * (x j : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hlin : (∑ i, Complex.I * zCoord z i * (x i : ℂ))
      = Complex.I * ∑ i, (x i : ℂ) * zCoord z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hquadsum, hlin]
  ring

/-- Positive real scalars preserve `Matrix.PosDef` for real matrices. -/
lemma posDef_smul {c : ℝ} (hc : 0 < c) {S : Matrix (Fin g) (Fin g) ℝ} (hS : S.PosDef) :
    (c • S).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [Matrix.isHermitian_iff_isSymm]
    show (c • S).transpose = c • S
    rw [Matrix.transpose_smul, Matrix.isHermitian_iff_isSymm.mp hS.isHermitian]
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hc (hS.dotProduct_mulVec_pos hx)

/-- `thetaableToMatrix old_thetaable` is invertible: it is `old_tau.toMatrix` for the
`SiegelUpperHalfSpace` point built from `old_thetaable`, and `siegelDenom (Sp2gR.Smatrix) Z = Z`
(`siegelDenom_Smatrix`) turns `siegelDenom_isUnit` into invertibility of `Z` itself. -/
lemma thetaableToMatrix_det_isUnit
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ)) :
    IsUnit (thetaableToMatrix old_thetaable).det := by
  set old_tau_re := latticeQuadToEuclidean old_thetaable.qRe
  set old_tau_im := latticeQuadToEuclidean old_thetaable.qIm
  have old_tau_im_posdef : old_tau_im.PosDef := by
    apply old_thetaable.qImRe_posdef old_tau_im
    intro u
    change old_tau_im (toEuclidean_ZnRn u) = old_thetaable.qIm u
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm u
  let old_tau : SiegelUpperHalfSpace g :=
    ⟨old_tau_re, old_tau_im, by
      simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm,
      old_tau_im_posdef⟩
  have hmatrix : thetaableToMatrix old_thetaable = old_tau.toMatrix := rfl
  rw [hmatrix]
  exact siegelDenom_Smatrix (R := ℤ) (g := g) old_tau.toMatrix ▸
    siegelDenom_isUnit (Sp2gR.Smatrix (R := ℤ) (g := g)) old_tau

/-- The `A := (2 * I) • (thetaableToMatrix old_thetaable)⁻¹` used in
`theta_summand_after_Smatrix_modulatedGaussian` is symmetric and has positive-definite real part —
the two hypotheses `modulatedGaussian_hasPoissonSummation` needs. `Re(A) = -2 • Im(M⁻¹)` (`M :=
thetaableToMatrix old_thetaable`), and `Im(-M⁻¹) = Im(siegelMatrixAction Smatrix M)` is
positive-definite by `siegelMatrixAction_im_posDef` (the standard fact that `S_g` preserves the
Siegel upper half-space). -/
lemma Smatrix_A_symm_and_posDef
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ)) :
    ((2 * Complex.I) • (thetaableToMatrix old_thetaable)⁻¹).IsSymm ∧
      ((((2 * Complex.I) • (thetaableToMatrix old_thetaable)⁻¹)).map Complex.re).PosDef := by
  set old_tau_re := latticeQuadToEuclidean old_thetaable.qRe
  set old_tau_im := latticeQuadToEuclidean old_thetaable.qIm
  have old_tau_im_posdef : old_tau_im.PosDef := by
    apply old_thetaable.qImRe_posdef old_tau_im
    intro u
    change old_tau_im (toEuclidean_ZnRn u) = old_thetaable.qIm u
    simpa [old_tau_im] using latticeQuadToEuclidean_restrict old_thetaable.qIm u
  let old_tau : SiegelUpperHalfSpace g :=
    ⟨old_tau_re, old_tau_im, by
      simpa [old_tau_im] using latticeQuadToEuclidean_continuous old_thetaable.qIm,
      old_tau_im_posdef⟩
  have hmatrix : thetaableToMatrix old_thetaable = old_tau.toMatrix := rfl
  rw [hmatrix]
  have hMinv_symm : old_tau.toMatrix⁻¹.IsSymm := old_tau.toMatrix_isSymm.inv
  have hMinv_ij : ∀ i j, old_tau.toMatrix⁻¹ i j = old_tau.toMatrix⁻¹ j i := fun i j => by
    have h := congrFun (congrFun hMinv_symm i) j
    rw [Matrix.transpose_apply] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · ext i j
    rw [Matrix.transpose_apply]
    show (2 * Complex.I) * old_tau.toMatrix⁻¹ j i = (2 * Complex.I) * old_tau.toMatrix⁻¹ i j
    rw [hMinv_ij j i]
  have hZsymm : (siegelMatrixAction (Sp2gR.Smatrix (R := ℤ) (g := g)) old_tau.toMatrix).IsSymm :=
    siegelMatrixAction_isSymm (Sp2gR.Smatrix (R := ℤ) (g := g)) old_tau
  have hZeq : siegelMatrixAction (Sp2gR.Smatrix (R := ℤ) (g := g)) old_tau.toMatrix =
      -old_tau.toMatrix⁻¹ := siegelMatrixAction_Smatrix old_tau.toMatrix
  have hYsymm : ((-old_tau.toMatrix⁻¹).map Complex.im).IsSymm := by
    rw [← hZeq]
    show (_ : Matrix (Fin g) (Fin g) ℝ).transpose = _
    rw [← Matrix.transpose_map, hZsymm]
  have hYposdef : ((-old_tau.toMatrix⁻¹).map Complex.im).PosDef := by
    have h1 := siegelMatrixAction_im_posDef (Sp2gR.Smatrix (R := ℤ) (g := g)) old_tau
    rw [hZeq] at h1
    have h2 := gramMatrixReal_posDef _ h1
    rwa [gramMatrixReal_quadraticMapOfMatrix hYsymm] at h2
  have hneg : (-old_tau.toMatrix⁻¹).map Complex.im = -(old_tau.toMatrix⁻¹.map Complex.im) := by
    ext i j
    simp [Complex.neg_im]
  rw [hneg] at hYposdef
  have hre : ((2 * Complex.I) • old_tau.toMatrix⁻¹).map Complex.re
      = (2 : ℝ) • (-(old_tau.toMatrix⁻¹.map Complex.im)) := by
    ext i j
    show ((2 * Complex.I) * old_tau.toMatrix⁻¹ i j).re
        = (2 : ℝ) * (-(old_tau.toMatrix⁻¹ i j).im)
    set w := old_tau.toMatrix⁻¹ i j
    rw [show (2 * Complex.I) * w = -2 * w.im + Complex.I * (2 * w.re) by
        conv_lhs => rw [← Complex.re_add_im w]
        ring_nf
        rw [Complex.I_sq]
        ring]
    simp
  rw [hre]
  exact posDef_smul (by norm_num) hYposdef

/-- The Poisson-resummed `S_g` theta identity, summed over the lattice: applying
`modulatedGaussian_hasPoissonSummation` to `theta_summand_after_Smatrix_modulatedGaussian` and
rewriting the Fourier-transformed side back into a `modulatedGaussian`
(`modulatedGaussian_fourierTransform_eq_modulatedGaussian`) turns `θ(z; S_g • old_thetaable)` into
a rescaled sum over a *dual* `modulatedGaussian`, at `A⁻¹ = (-I/2) • thetaableToMatrix old_thetaable`
(computed directly, rather than left as a double inverse, via `(2I)⁻¹ = -I/2`). -/
theorem theta_fun_after_Smatrix_poisson
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    ThetaAbleQuadraticForm.theta_fun (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.Smatrix (R := ℤ) (g := g))
        old_thetaable) z =
    1 / pivotSqrt g ((2 * Complex.I) • (thetaableToMatrix old_thetaable)⁻¹) *
      Complex.exp (↑Real.pi * ∑ i, ∑ j,
        ((-Complex.I / 2) • thetaableToMatrix old_thetaable) i j *
          (Complex.I * zCoord z i) * (Complex.I * zCoord z j)) *
      ∑' n : Fin g → ℤ, modulatedGaussian
        ((-Complex.I / 2) • thetaableToMatrix old_thetaable)
        (fun i => -Complex.I * ∑ j,
          ((-Complex.I / 2) • thetaableToMatrix old_thetaable) i j * (Complex.I * zCoord z j))
        (toEuclidean_ZnRn n) := by
  set A : Matrix (Fin g) (Fin g) ℂ := (2 * Complex.I) • (thetaableToMatrix old_thetaable)⁻¹ with hA_def
  set b : Fin g → ℂ := fun i => Complex.I * zCoord z i with hb_def
  obtain ⟨hAsymm, hAre⟩ := Smatrix_A_symm_and_posDef old_thetaable
  have hMunit : IsUnit (thetaableToMatrix old_thetaable).det :=
    thetaableToMatrix_det_isUnit old_thetaable
  have hAinv : A⁻¹ = (-Complex.I / 2) • thetaableToMatrix old_thetaable := by
    rw [hA_def]
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul, Matrix.nonsing_inv_mul (thetaableToMatrix old_thetaable) hMunit]
    rw [show (2 * Complex.I) * (-Complex.I / 2) = 1 by
      linear_combination (-1 : ℂ) * Complex.I_mul_I]
    exact one_smul ℂ 1
  have hL : ThetaAbleQuadraticForm.theta_fun (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.Smatrix (R := ℤ) (g := g))
        old_thetaable) z
      = ∑' x, theta_summand_after g hg (x_summand := x) (M := Sp2gR.Smatrix (R := ℤ) (g := g))
          (old_thetaable := old_thetaable) (z := z) := rfl
  rw [hL]
  have hcongr : ∀ x, theta_summand_after g hg (x_summand := x)
        (M := Sp2gR.Smatrix (R := ℤ) (g := g)) (old_thetaable := old_thetaable) (z := z)
      = modulatedGaussian A b (toEuclidean_ZnRn x) :=
    fun x => theta_summand_after_Smatrix_modulatedGaussian g hg x old_thetaable z
  simp_rw [hcongr]
  have hPoisson := modulatedGaussian_hasPoissonSummation hg A hAsymm hAre b
  rw [hPoisson.2.2.2]
  simp_rw [modulatedGaussian_fourierTransform_eq_modulatedGaussian hg A hAsymm hAre b, hAinv]
  rw [tsum_mul_left]

/-- The shift `n ↦ -2I ∑ᵢ (M⁻¹ z)ᵢ nᵢ` (`M := thetaableToMatrix old_thetaable`), built from `z` via
`M⁻¹` with an extra `-2I` compensating factor: `zCoord (zMinvShift old_thetaable z) i =
-2 * ∑ⱼ M⁻¹ i j * zCoord z j` (`zCoord_zMinvShift`). The `-2` is exactly what
`theta_fun_after_Smatrix_poisson_Minv` needs to land its RHS `theta_fun` on the *plain* `z`,
rather than a rescaled shift. -/
noncomputable def zMinvShift (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) : (Fin g → ℤ) →ₗ[ℤ] ℂ :=
  bShiftMap (fun i => -2 * Complex.I * ∑ j, (thetaableToMatrix old_thetaable)⁻¹ i j * zCoord z j)

lemma zCoord_zMinvShift (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) (i : Fin g) :
    zCoord (zMinvShift old_thetaable z) i =
      -2 * ∑ j, (thetaableToMatrix old_thetaable)⁻¹ i j * zCoord z j := by
  show (zMinvShift old_thetaable z) (Pi.single i 1) = _
  unfold zMinvShift bShiftMap
  show -Complex.I * ∑ k,
      (-2 * Complex.I * ∑ j, (thetaableToMatrix old_thetaable)⁻¹ k j * zCoord z j) *
      ((Pi.single i 1 : Fin g → ℤ) k : ℂ) = _
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ i) h)]
  simp only [if_pos, mul_one, Int.cast_one]
  rw [show (-Complex.I) * (-2 * Complex.I *
        ∑ j, (thetaableToMatrix old_thetaable)⁻¹ i j * zCoord z j)
      = 2 * (Complex.I * Complex.I) *
        ∑ j, (thetaableToMatrix old_thetaable)⁻¹ i j * zCoord z j from by ring]
  rw [Complex.I_mul_I]
  ring

/-- `theta_fun_after_Smatrix_poisson`, instantiated at the shift `zMinvShift old_thetaable z`
(`M⁻¹` composed with an extra `-2I`) instead of a bare `z`, with the resulting `M * M⁻¹`/`M⁻¹ * M`
pairs (`M := thetaableToMatrix old_thetaable`) cancelled: the exp argument's
`∑∑ M (M⁻¹v) (M⁻¹v)` collapses to `∑∑ M⁻¹ v v` (`v i := zCoord z i`), and the `modulatedGaussian`
shift's `∑ M (M⁻¹v)` collapses to `v` itself — the `-2I` in `zMinvShift` is exactly what makes the
shift come out as the *plain* `I • v`, matching `theta_fun_eq_modulatedGaussian_tsum` on the nose. -/
theorem theta_fun_after_Smatrix_poisson_Minv
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    ThetaAbleQuadraticForm.theta_fun (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.Smatrix (R := ℤ) (g := g))
        old_thetaable) (zMinvShift old_thetaable z) =
    1 / pivotSqrt g ((2 * Complex.I) • (thetaableToMatrix old_thetaable)⁻¹) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ∑ i, ∑ j,
        (thetaableToMatrix old_thetaable)⁻¹ i j * zCoord z i * zCoord z j) *
      ∑' n : Fin g → ℤ, modulatedGaussian
        ((-Complex.I / 2) • thetaableToMatrix old_thetaable)
        (fun i => Complex.I * zCoord z i)
        (toEuclidean_ZnRn n) := by
  rw [theta_fun_after_Smatrix_poisson g hg old_thetaable (zMinvShift old_thetaable z)]
  simp_rw [zCoord_zMinvShift]
  set M := thetaableToMatrix old_thetaable with hM_def
  set v : Fin g → ℂ := fun i => zCoord z i with hv_def
  have hMunit : IsUnit M.det := thetaableToMatrix_det_isUnit old_thetaable
  have hcancelB : ∀ i : Fin g, (∑ j, M i j * (∑ k, M⁻¹ j k * v k)) = v i := by
    intro i
    have h : (∑ j, M i j * (∑ k, M⁻¹ j k * v k)) = (M.mulVec (M⁻¹.mulVec v)) i := rfl
    rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMunit, Matrix.one_mulVec]
  have hcancelA : (∑ i, ∑ j, M i j * (∑ k, M⁻¹ i k * v k) * (∑ k, M⁻¹ j k * v k))
      = ∑ i, ∑ j, M⁻¹ i j * v i * v j := by
    have hswap : (∑ i, ∑ j, M i j * (∑ k, M⁻¹ i k * v k) * (∑ k, M⁻¹ j k * v k))
        = ∑ i, (∑ k, M⁻¹ i k * v k) * (∑ j, M i j * (∑ k, M⁻¹ j k * v k)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hswap]
    simp_rw [hcancelB]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hgoal_re : (fun i => -Complex.I * ∑ j, ((-Complex.I / 2) • M) i j *
        (Complex.I * (-2 * ∑ k, M⁻¹ j k * v k)))
      = fun i => Complex.I * v i := by
    funext i
    have hstep : ∑ j, ((-Complex.I / 2) • M) i j * (Complex.I * (-2 * ∑ k, M⁻¹ j k * v k))
        = (-Complex.I / 2) * Complex.I * (-2) * (∑ j, M i j * (∑ k, M⁻¹ j k * v k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hstep, hcancelB]
    rw [show (-Complex.I) * ((-Complex.I / 2) * Complex.I * (-2) * v i)
        = (-1 : ℂ) * (Complex.I * Complex.I) * Complex.I * v i from by ring]
    rw [Complex.I_mul_I]
    ring
  have hgoal_quad : ∑ i, ∑ j, ((-Complex.I / 2) • M) i j *
        (Complex.I * (-2 * ∑ k, M⁻¹ i k * v k)) * (Complex.I * (-2 * ∑ k, M⁻¹ j k * v k))
      = 2 * Complex.I * ∑ i, ∑ j, M⁻¹ i j * v i * v j := by
    have hpointwise : ∀ i j, ((-Complex.I / 2) • M) i j *
          (Complex.I * (-2 * ∑ k, M⁻¹ i k * v k)) * (Complex.I * (-2 * ∑ k, M⁻¹ j k * v k))
        = 2 * Complex.I * (M i j * (∑ k, M⁻¹ i k * v k) * (∑ k, M⁻¹ j k * v k)) := by
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [show (-Complex.I / 2 * M i j) * (Complex.I * (-2 * ∑ k, M⁻¹ i k * v k)) *
            (Complex.I * (-2 * ∑ k, M⁻¹ j k * v k))
          = (-2 : ℂ) * (Complex.I * Complex.I) * Complex.I *
            (M i j * (∑ k, M⁻¹ i k * v k) * (∑ k, M⁻¹ j k * v k)) from by ring]
      rw [Complex.I_mul_I]
      ring
    simp_rw [hpointwise]
    rw [show (∑ i, ∑ j, 2 * Complex.I * (M i j * (∑ k, M⁻¹ i k * v k) * (∑ k, M⁻¹ j k * v k)))
        = 2 * Complex.I * (∑ i, ∑ j, M i j * (∑ k, M⁻¹ i k * v k) * (∑ k, M⁻¹ j k * v k)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]]
    rw [hcancelA]
  rw [hgoal_re, hgoal_quad]
  simp only [hv_def]
  ring_nf

/-- `old_thetaable`'s own `theta_fun`, restated as a lattice sum of `modulatedGaussian`s at
`A := (-I/2) • thetaableToMatrix old_thetaable` — obtained by summing
`theta_summand_after_zero_modulatedGaussian` over the lattice. -/
private lemma theta_fun_eq_modulatedGaussian_tsum
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    ThetaAbleQuadraticForm.theta_fun (R := ℤ) (thetaable := old_thetaable) z =
    ∑' n : Fin g → ℤ, modulatedGaussian ((-Complex.I / 2) • thetaableToMatrix old_thetaable)
      (fun i => Complex.I * zCoord z i) (toEuclidean_ZnRn n) := by
  have hR : ThetaAbleQuadraticForm.theta_fun (R := ℤ) (thetaable := old_thetaable) z
      = ∑' x, theta_summand_after g hg (x_summand := x)
          (M := Sp2gR.Tmatrix (0 : Matrix (Fin g) (Fin g) ℤ) Matrix.transpose_zero)
          (old_thetaable := old_thetaable) (z := z) :=
    tsum_congr fun x => (theta_summand_after_zero g hg x old_thetaable z).symm
  rw [hR]
  exact tsum_congr fun x => theta_summand_after_zero_modulatedGaussian g hg x old_thetaable z

/-- The full `S_g` Poisson-resummation theta identity, `theta_fun` on both sides — the analogue of
`theta_fun_after_Tmatrix_diagEven`/`theta_fun_after_GLmatrix_reindex` for the `S` generator. The
`-2I` baked into `zMinvShift` makes `theta_fun_after_Smatrix_poisson_Minv`'s dual-Gaussian sum land
*exactly* on `theta_fun_eq_modulatedGaussian_tsum`'s shift (`I • zCoord z`, no rescaling), so
`old_thetaable`'s `theta_fun` on the RHS is at the plain `z`. -/
theorem theta_fun_after_Smatrix
    (g : ℕ) (hg : g ≠ 0)
    (old_thetaable : ThetaAbleQuadraticForm (R := ℤ) (M := Fin g → ℤ))
    (z : (Fin g → ℤ) →ₗ[ℤ] ℂ) :
    ThetaAbleQuadraticForm.theta_fun (R := ℤ)
      (thetaable := RiemannThetaAble_siegelSMul (R := ℤ) hg (Sp2gR.Smatrix (R := ℤ) (g := g))
        old_thetaable) (zMinvShift old_thetaable z) =
    1 / pivotSqrt g ((2 * Complex.I) • (thetaableToMatrix old_thetaable)⁻¹) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ∑ i, ∑ j,
        (thetaableToMatrix old_thetaable)⁻¹ i j * zCoord z i * zCoord z j) *
      ThetaAbleQuadraticForm.theta_fun (R := ℤ) (thetaable := old_thetaable) z := by
  rw [theta_fun_after_Smatrix_poisson_Minv g hg old_thetaable z,
    ← theta_fun_eq_modulatedGaussian_tsum g hg old_thetaable z]

end ThetaTransformSMatrix

end ThetaTransform
