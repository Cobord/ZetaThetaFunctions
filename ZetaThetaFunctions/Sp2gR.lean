import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-!
# The symplectic group `Sp(2g, R)`

This file is purely about the abstract group `Sp2gR (R := R) g := Matrix.symplecticGroup (Fin g) R`
— block decomposition, multiplication formulas, symplectic relations, and the three classical
families of generators (`Tmatrix`/upper-unipotent translations, `GLmatrix`/the `GL(g, ℤ)` action,
and `Smatrix`/the Fourier long-Weyl element) — with no dependence on the Siegel upper half-space or
theta functions. Those live in `SiegelModular.lean`, which imports this file.

## Main definitions

* `Sp2gR (R := R) g`: `Sp(2g, R)`, via `Matrix.symplecticGroup (Fin g) R`.
* `Sp2gR.blockA/B/C/D`: the block decomposition `!![A, B; C, D]` of a symplectic matrix.
* `Sp2gR.Tmatrix B hB`: the upper-unipotent generator `!![1, B; 0, 1]` for symmetric `B`.
* `Sp2gR.GLmatrix U hU`: the block-diagonal `GL(g, ℤ)`-action generator `!![U, 0; 0, (Uᵀ)⁻¹]`.
* `Sp2gR.Smatrix`: the Fourier long-Weyl generator `!![0, -1; 1, 0]`.
* `Sp2gR.block_relations`/`_complex`: the symplectic relations `AᵀC=CᵀA`, `BᵀD=DᵀB`,
  `AᵀD-CᵀB=1`, `DᵀA-BᵀC=1` for the blocks of a symplectic matrix.

## Sections

* `SL2Embedding`: fixed-block embeddings `SL(2, R) ↪ Sp(2g, R)` (`Sp2gR.SL2blockMatrix`) built from
  four fixed `g × g` matrices `A, B, C, D`, plus the standard `SL(2, R)` generators
  (`SL2upper`/`SL2lower`/`SL2rotation`) used to recover `Tmatrix`/`Smatrix`-style relations from the
  `g = 1` case.

-/

variable {R : Type*} [CommRing R]
variable {g : ℕ}

/-- The real symplectic group `Sp(2g, ℝ)`, realized as `2g × 2g` matrices indexed by
`Fin g ⊕ Fin g` (so the block decomposition `!![A, B; C, D]` used in the Siegel action lines up
with `Matrix.toBlocks₁₁` etc.), via Mathlib's general `Matrix.symplecticGroup`. -/
@[reducible] def Sp2gR {R: Type u} [CommRing R] (g : ℕ) : Type u := Matrix.symplecticGroup (Fin g) R

section Blocks

/-- The upper-left `g × g` block `A` of a symplectic matrix. -/
noncomputable def Sp2gR.blockA (M : Sp2gR (R:=R) g) : Matrix (Fin g) (Fin g) R :=
  (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R).toBlocks₁₁

/-- The upper-right `g × g` block `B` of a symplectic matrix. -/
noncomputable def Sp2gR.blockB (M : Sp2gR (R:=R) g) : Matrix (Fin g) (Fin g) R :=
  (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R).toBlocks₁₂

/-- The lower-left `g × g` block `C` of a symplectic matrix. -/
noncomputable def Sp2gR.blockC (M : Sp2gR (R:=R) g) : Matrix (Fin g) (Fin g) R :=
  (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R).toBlocks₂₁

/-- The lower-right `g × g` block `D` of a symplectic matrix. -/
noncomputable def Sp2gR.blockD (M : Sp2gR (R:=R) g) : Matrix (Fin g) (Fin g) R :=
  (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R).toBlocks₂₂

end Blocks

section Identity

/-- The identity symplectic matrix has blocks `A = 1`, `B = 0`, `C = 0`, `D = 1`. -/
lemma Sp2gR.blockA_one : Sp2gR.blockA (1 : Sp2gR (R := R) g) = 1 := by
  simp [Sp2gR.blockA, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

lemma Sp2gR.blockB_one : Sp2gR.blockB (1 : Sp2gR (R := R) g) = 0 := by
  simp [Sp2gR.blockB, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]

lemma Sp2gR.blockC_one : Sp2gR.blockC (1 : Sp2gR (R := R) g) = 0 := by
  simp [Sp2gR.blockC, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]

lemma Sp2gR.blockD_one : Sp2gR.blockD (1 : Sp2gR (R := R) g) = 1 := by
  simp [Sp2gR.blockD, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]

end Identity

section TMatrix

/-- The upper-unipotent symplectic matrix `!![1, B; 0, 1]` associated to a symmetric matrix `B`. -/
noncomputable def Sp2gR.Tmatrix (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm) :
    Sp2gR (R := R) g :=
  ⟨Matrix.fromBlocks 1 B 0 1, by
    change Matrix.fromBlocks 1 B 0 1 * Matrix.J (Fin g) R *
        (Matrix.fromBlocks 1 B 0 1).transpose = Matrix.J (Fin g) R
    rw [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply]
    simp
    have btrans : B.transpose = B := by
      exact hB.eq
    rw [btrans]
    simp
    ⟩

@[simp] lemma Sp2gR.blockA_Tmatrix (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm) :
    Sp2gR.blockA (Sp2gR.Tmatrix B hB) = 1 := by
  simp [Sp2gR.Tmatrix, Sp2gR.blockA, Matrix.toBlocks_fromBlocks₁₁]

@[simp] lemma Sp2gR.blockB_Tmatrix (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm) :
    Sp2gR.blockB (Sp2gR.Tmatrix B hB) = B := by
  simp [Sp2gR.Tmatrix, Sp2gR.blockB, Matrix.toBlocks_fromBlocks₁₂]

@[simp] lemma Sp2gR.blockC_Tmatrix (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm) :
    Sp2gR.blockC (Sp2gR.Tmatrix B hB) = 0 := by
  simp [Sp2gR.Tmatrix, Sp2gR.blockC, Matrix.toBlocks_fromBlocks₂₁]

@[simp] lemma Sp2gR.blockD_Tmatrix (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm) :
    Sp2gR.blockD (Sp2gR.Tmatrix B hB) = 1 := by
  simp [Sp2gR.Tmatrix, Sp2gR.blockD, Matrix.toBlocks_fromBlocks₂₂]

end TMatrix

section Product

/-- The underlying matrix of a product of symplectic matrices is the matrix product. -/
lemma Sp2gR.coe_mul (M N : Sp2gR (R := R) g) :
    ((M * N : Sp2gR (R := R) g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R)
      = (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R)
        * (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) :=
  rfl

/-- The block decomposition of a product of symplectic matrices, via `Matrix.fromBlocks_multiply`
applied to `M = fromBlocks (blockA M) (blockB M) (blockC M) (blockD M)` (`Matrix.fromBlocks_toBlocks`)
and likewise for `N`. -/
lemma Sp2gR.blockA_mul (M N : Sp2gR (R := R) g) :
    Sp2gR.blockA (M * N) = Sp2gR.blockA M * Sp2gR.blockA N + Sp2gR.blockB M * Sp2gR.blockC N := by
  show (((M * N : Sp2gR (R := R) g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R)).toBlocks₁₁ = _
  rw [Sp2gR.coe_mul, ← Matrix.fromBlocks_toBlocks (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    ← Matrix.fromBlocks_toBlocks (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
  rfl

lemma Sp2gR.blockB_mul (M N : Sp2gR (R := R) g) :
    Sp2gR.blockB (M * N) = Sp2gR.blockA M * Sp2gR.blockB N + Sp2gR.blockB M * Sp2gR.blockD N := by
  show (((M * N : Sp2gR (R := R) g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R)).toBlocks₁₂ = _
  rw [Sp2gR.coe_mul, ← Matrix.fromBlocks_toBlocks (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    ← Matrix.fromBlocks_toBlocks (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂]
  rfl

lemma Sp2gR.blockC_mul (M N : Sp2gR (R := R) g) :
    Sp2gR.blockC (M * N) = Sp2gR.blockC M * Sp2gR.blockA N + Sp2gR.blockD M * Sp2gR.blockC N := by
  show (((M * N : Sp2gR (R := R) g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R)).toBlocks₂₁ = _
  rw [Sp2gR.coe_mul, ← Matrix.fromBlocks_toBlocks (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    ← Matrix.fromBlocks_toBlocks (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]
  rfl

lemma Sp2gR.blockD_mul (M N : Sp2gR (R := R) g) :
    Sp2gR.blockD (M * N) = Sp2gR.blockC M * Sp2gR.blockB N + Sp2gR.blockD M * Sp2gR.blockD N := by
  show (((M * N : Sp2gR (R := R) g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R)).toBlocks₂₂ = _
  rw [Sp2gR.coe_mul, ← Matrix.fromBlocks_toBlocks (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    ← Matrix.fromBlocks_toBlocks (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]
  rfl

end Product

/-- `B ↦ Sp2gR.Tmatrix B` is a monoid homomorphism from `(Matrix (Fin g) (Fin g) R, IsSymm, +)`
into `Sp2gR (R := R) g`: `Tmatrix B₁ * Tmatrix B₂ = Tmatrix (B₁ + B₂)`, matching the matrix identity
`!![1,B₁;0,1] * !![1,B₂;0,1] = !![1,B₁+B₂;0,1]`. This is what makes the even-diagonal-symmetric-
integer-matrix T-shifts a genuine *subgroup* of `Sp(2g, ℤ)`, consistent with
`SiegelModular.lean`'s `theta_fun_after_Tmatrix_diagEven`: composing two T-shifts composes their
theta-series multipliers accordingly. -/
lemma Sp2gR.Tmatrix_mul (B₁ B₂ : Matrix (Fin g) (Fin g) R) (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    Sp2gR.Tmatrix B₁ hB₁ * Sp2gR.Tmatrix B₂ hB₂
      = Sp2gR.Tmatrix (B₁ + B₂)
          (show (B₁ + B₂).transpose = B₁ + B₂ by rw [Matrix.transpose_add, hB₁.eq, hB₂.eq]) := by
  apply Subtype.ext
  rw [Sp2gR.coe_mul]
  show Matrix.fromBlocks 1 B₁ 0 1 * Matrix.fromBlocks 1 B₂ 0 1
      = Matrix.fromBlocks 1 (B₁ + B₂) 0 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]
  rw [add_comm]

section GLMatrix

/-- The block-diagonal symplectic matrix `!![U, 0; 0, (Uᵀ)⁻¹]` associated to a unit `U : Matrix
(Fin g) (Fin g) R` — the classical `GL(g, ℤ)`-action generator of `Sp(2g, ℤ)`. -/
noncomputable def Sp2gR.GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U) :
    Sp2gR (R := R) g :=
  ⟨Matrix.fromBlocks U 0 0 (U.transpose)⁻¹, by
    change Matrix.fromBlocks U 0 0 (U.transpose)⁻¹ * Matrix.J (Fin g) R *
        (Matrix.fromBlocks U 0 0 (U.transpose)⁻¹).transpose = Matrix.J (Fin g) R
    have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
    have hUTdet : IsUnit (U.transpose).det := by rwa [Matrix.det_transpose]
    rw [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_zero]
    rw [Matrix.mul_nonsing_inv U hUdet, Matrix.nonsing_inv_mul U.transpose hUTdet]⟩

@[simp] lemma Sp2gR.blockA_GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U) :
    Sp2gR.blockA (Sp2gR.GLmatrix U hU) = U := by
  simp [Sp2gR.GLmatrix, Sp2gR.blockA, Matrix.toBlocks_fromBlocks₁₁]

@[simp] lemma Sp2gR.blockB_GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U) :
    Sp2gR.blockB (Sp2gR.GLmatrix U hU) = 0 := by
  simp [Sp2gR.GLmatrix, Sp2gR.blockB, Matrix.toBlocks_fromBlocks₁₂]

@[simp] lemma Sp2gR.blockC_GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U) :
    Sp2gR.blockC (Sp2gR.GLmatrix U hU) = 0 := by
  simp [Sp2gR.GLmatrix, Sp2gR.blockC, Matrix.toBlocks_fromBlocks₂₁]

@[simp] lemma Sp2gR.blockD_GLmatrix (U : Matrix (Fin g) (Fin g) R) (hU : IsUnit U) :
    Sp2gR.blockD (Sp2gR.GLmatrix U hU) = (U.transpose)⁻¹ := by
  simp [Sp2gR.GLmatrix, Sp2gR.blockD, Matrix.toBlocks_fromBlocks₂₂]

end GLMatrix

section SMatrix

/-- The Fourier (long-Weyl) symplectic matrix
`S_g = !![0, -1; 1, 0]`. Together with the Siegel parabolic generators, it generates the full
symplectic group. -/
noncomputable def Sp2gR.Smatrix : Sp2gR (R := R) g :=
  ⟨Matrix.fromBlocks 0 (-1) 1 0, by
    change Matrix.fromBlocks 0 (-1) 1 0 * Matrix.J (Fin g) R *
        (Matrix.fromBlocks 0 (-1) 1 0).transpose = Matrix.J (Fin g) R
    rw [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply]
    simp⟩

@[simp] lemma Sp2gR.blockA_Smatrix : Sp2gR.blockA (Sp2gR.Smatrix (R := R) (g := g)) = 0 := by
  simp [Sp2gR.Smatrix, Sp2gR.blockA, Matrix.toBlocks_fromBlocks₁₁]

@[simp] lemma Sp2gR.blockB_Smatrix : Sp2gR.blockB (Sp2gR.Smatrix (R := R) (g := g)) = -1 := by
  simp [Sp2gR.Smatrix, Sp2gR.blockB, Matrix.toBlocks_fromBlocks₁₂]

@[simp] lemma Sp2gR.blockC_Smatrix : Sp2gR.blockC (Sp2gR.Smatrix (R := R) (g := g)) = 1 := by
  simp [Sp2gR.Smatrix, Sp2gR.blockC, Matrix.toBlocks_fromBlocks₂₁]

@[simp] lemma Sp2gR.blockD_Smatrix : Sp2gR.blockD (Sp2gR.Smatrix (R := R) (g := g)) = 0 := by
  simp [Sp2gR.Smatrix, Sp2gR.blockD, Matrix.toBlocks_fromBlocks₂₂]

end SMatrix

section BlockRelations

/-- The symplectic relations `AᵀC = CᵀA`, `BᵀD = DᵀB`, `AᵀD - CᵀB = 1`, `DᵀA - BᵀC = 1` for the
blocks of a symplectic matrix, derived from `Mᵀ * J * M = J` (`SymplecticGroup.mem_iff'`) via
`Matrix.fromBlocks_multiply`/`Matrix.fromBlocks_inj`. -/
lemma Sp2gR.block_relations (M : Sp2gR (R := R) g) :
    (Sp2gR.blockA M).transpose * Sp2gR.blockC M = (Sp2gR.blockC M).transpose * Sp2gR.blockA M ∧
    (Sp2gR.blockB M).transpose * Sp2gR.blockD M = (Sp2gR.blockD M).transpose * Sp2gR.blockB M ∧
    (Sp2gR.blockA M).transpose * Sp2gR.blockD M - (Sp2gR.blockC M).transpose * Sp2gR.blockB M
      = 1 ∧
    (Sp2gR.blockD M).transpose * Sp2gR.blockA M - (Sp2gR.blockB M).transpose * Sp2gR.blockC M
      = 1 := by
  have hmem : (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R).transpose * Matrix.J (Fin g) R *
      (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) = Matrix.J (Fin g) R :=
    SymplecticGroup.mem_iff'.mp M.2
  rw [Matrix.J, ← Matrix.fromBlocks_toBlocks (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R),
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hmem
  obtain ⟨h11, h12, h21, h22⟩ := hmem
  simp only [Sp2gR.blockA, Sp2gR.blockB, Sp2gR.blockC, Sp2gR.blockD]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := noncomm_ring) -h11
  · linear_combination (norm := noncomm_ring) -h22
  · linear_combination (norm := noncomm_ring) -h12
  · linear_combination (norm := noncomm_ring) h21

variable [Algebra R ℂ] in
/-- `Sp2gR.block_relations`, cast into `ℂ` via `(algebraMap R ℂ).mapMatrix`. -/
lemma Sp2gR.block_relations_complex (M : Sp2gR (R := R) g) :
    ((algebraMap R ℂ).mapMatrix M.blockA).transpose * (algebraMap R ℂ).mapMatrix M.blockC
      = ((algebraMap R ℂ).mapMatrix M.blockC).transpose * (algebraMap R ℂ).mapMatrix M.blockA ∧
    ((algebraMap R ℂ).mapMatrix M.blockB).transpose * (algebraMap R ℂ).mapMatrix M.blockD
      = ((algebraMap R ℂ).mapMatrix M.blockD).transpose * (algebraMap R ℂ).mapMatrix M.blockB ∧
    ((algebraMap R ℂ).mapMatrix M.blockA).transpose * (algebraMap R ℂ).mapMatrix M.blockD
      - ((algebraMap R ℂ).mapMatrix M.blockC).transpose * (algebraMap R ℂ).mapMatrix M.blockB
      = 1 ∧
    ((algebraMap R ℂ).mapMatrix M.blockD).transpose * (algebraMap R ℂ).mapMatrix M.blockA
      - ((algebraMap R ℂ).mapMatrix M.blockB).transpose * (algebraMap R ℂ).mapMatrix M.blockC
      = 1 := by
  have hmap_transpose : ∀ X : Matrix (Fin g) (Fin g) R,
      (algebraMap R ℂ).mapMatrix X.transpose = ((algebraMap R ℂ).mapMatrix X).transpose := by
    intro X
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  obtain ⟨r1, r2, r3, r4⟩ := Sp2gR.block_relations M
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmap_transpose, ← hmap_transpose, ← map_mul, ← map_mul, r1]
  · rw [← hmap_transpose, ← hmap_transpose, ← map_mul, ← map_mul, r2]
  · rw [← hmap_transpose, ← hmap_transpose, ← map_mul, ← map_mul, ← map_sub, r3, map_one]
  · rw [← hmap_transpose, ← hmap_transpose, ← map_mul, ← map_mul, ← map_sub, r4, map_one]

end BlockRelations

section SL2Embedding

/-- The block-matrix candidate associated to four fixed `g × g` matrices. For
`m = ![![a, b], ![c, d]]`, this is `!![aA, bB; cC, dD]`. -/
noncomputable def Sp2gR.SL2blockMatrix
    (A B C D : Matrix (Fin g) (Fin g) R) (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R :=
  Matrix.fromBlocks (m 0 0 • A) (m 0 1 • B) (m 1 0 • C) (m 1 1 • D)

/-- The upper unipotent element of `SL(2, R)`. -/
noncomputable def Sp2gR.SL2upper : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- The lower unipotent element of `SL(2, R)`. -/
noncomputable def Sp2gR.SL2lower : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

/-- The rotation element of `SL(2, R)`. -/
noncomputable def Sp2gR.SL2rotation : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

/-- If the fixed-block `SL(2, R)` construction preserves the identity, its diagonal blocks are
`I_g`. The off-diagonal blocks do not occur at the identity. -/
lemma Sp2gR.SL2blockMatrix_one_diagonal
    (A B C D : Matrix (Fin g) (Fin g) R)
    (h_one : Sp2gR.SL2blockMatrix A B C D 1 = 1) : A = 1 ∧ D = 1 := by
  rw [Sp2gR.SL2blockMatrix, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h_one
  exact ⟨by simpa using h_one.1, by simpa using h_one.2.2.2⟩

/-- The upper-unipotent image is symplectic only when its fixed upper-right block is symmetric. -/
private lemma Sp2gR.SL2blockMatrix_B_isSymm
    (A B C D : Matrix (Fin g) (Fin g) R) (hD : D = 1)
    (hupper : Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2upper ∈
      Matrix.symplecticGroup (Fin g) R) : B.IsSymm := by
  let upper : Sp2gR (R := R) g :=
    ⟨Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2upper, hupper⟩
  obtain ⟨_, hB, _, _⟩ := Sp2gR.block_relations upper
  change B.transpose = B
  simpa [upper, Sp2gR.SL2blockMatrix, Sp2gR.SL2upper, Sp2gR.blockB, Sp2gR.blockD, hD] using hB

/-- The lower-unipotent image is symplectic only when its fixed lower-left block is symmetric. -/
private lemma Sp2gR.SL2blockMatrix_C_isSymm
    (A B C D : Matrix (Fin g) (Fin g) R) (hA : A = 1)
    (hlower : Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2lower ∈
      Matrix.symplecticGroup (Fin g) R) : C.IsSymm := by
  let lower : Sp2gR (R := R) g :=
    ⟨Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2lower, hlower⟩
  obtain ⟨hC, _, _, _⟩ := Sp2gR.block_relations lower
  change C.transpose = C
  simpa [lower, Sp2gR.SL2blockMatrix, Sp2gR.SL2lower, Sp2gR.blockA, Sp2gR.blockC, hA] using
    hC.symm

/-- The rotation image, through the third symplectic block relation, relates the two fixed
off-diagonal blocks. -/
private lemma Sp2gR.SL2blockMatrix_cross_relation
    (A B C D : Matrix (Fin g) (Fin g) R)
    (hrotation : Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2rotation ∈
      Matrix.symplecticGroup (Fin g) R) : C.transpose * B = 1 := by
  let rotation : Sp2gR (R := R) g :=
    ⟨Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2rotation, hrotation⟩
  obtain ⟨_, _, hcross, _⟩ := Sp2gR.block_relations rotation
  simpa [rotation, Sp2gR.SL2blockMatrix, Sp2gR.SL2rotation, Sp2gR.blockA,
    Sp2gR.blockB, Sp2gR.blockC, Sp2gR.blockD] using hcross

/-- A homomorphism `SL(2, R) →* Sp(2g, R)` having the fixed block form
`![![a, b], ![c, d]] ↦ !![aA, bB; cC, dD]` is necessarily of the form
`!![a I_g, bB; cB⁻¹, dI_g]` for a symmetric invertible matrix `B`. -/
private theorem Sp2gR.SL2blockHom_classification_of_blocks
    (f : Matrix.SpecialLinearGroup (Fin 2) R →* Sp2gR (R := R) g)
    (A B C D : Matrix (Fin g) (Fin g) R)
    (hblocks : ∀ m, (f m : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) =
      Sp2gR.SL2blockMatrix A B C D m) :
    A = 1 ∧ D = 1 ∧ B.IsSymm ∧ IsUnit B.det ∧ C = B⁻¹ := by
  have h_one : Sp2gR.SL2blockMatrix A B C D 1 = 1 := by
    rw [← hblocks]
    exact congrArg (fun M : Sp2gR (R := R) g =>
      (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R)) f.map_one
  obtain ⟨hA, hD⟩ := Sp2gR.SL2blockMatrix_one_diagonal A B C D h_one
  have hupper : Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2upper ∈
      Matrix.symplecticGroup (Fin g) R := by
    rw [← hblocks]
    exact (f Sp2gR.SL2upper).property
  have hlower : Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2lower ∈
      Matrix.symplecticGroup (Fin g) R := by
    rw [← hblocks]
    exact (f Sp2gR.SL2lower).property
  have hrotation : Sp2gR.SL2blockMatrix A B C D Sp2gR.SL2rotation ∈
      Matrix.symplecticGroup (Fin g) R := by
    rw [← hblocks]
    exact (f Sp2gR.SL2rotation).property
  have hB : B.IsSymm := Sp2gR.SL2blockMatrix_B_isSymm A B C D hD hupper
  have hC : C.IsSymm := Sp2gR.SL2blockMatrix_C_isSymm A B C D hA hlower
  have hcross : C.transpose * B = 1 :=
    Sp2gR.SL2blockMatrix_cross_relation A B C D hrotation
  have hCB : C * B = 1 := by simpa [hC.eq] using hcross
  have hdet_eq : C.det * B.det = 1 := by
    rw [← Matrix.det_mul, hCB, Matrix.det_one]
  have hBdet : IsUnit B.det :=
    IsUnit.of_mul_eq_one C.det (by simpa [mul_comm] using hdet_eq)
  have hCeq : C = B⁻¹ := by
    rw [← Matrix.mul_one C, ← Matrix.mul_nonsing_inv B hBdet, ← Matrix.mul_assoc, hCB,
      Matrix.one_mul]
  exact ⟨hA, hD, hB, hBdet, hCeq⟩

/-- The fixed-block symplectic representation of `SL(2, R)` attached to a symmetric invertible
matrix `B`: `![![a,b],[c,d]]` acts by `!![a I_g, b B; c B⁻¹, d I_g]`. -/
noncomputable def Sp2gR.SL2blockHom (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm)
    (hBdet : IsUnit B.det) :
    Matrix.SpecialLinearGroup (Fin 2) R →* Sp2gR (R := R) g where
  toFun m := ⟨Sp2gR.SL2blockMatrix 1 B B⁻¹ 1 m, by
    have hdet : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using m.2
    change Matrix.fromBlocks (m 0 0 • 1) (m 0 1 • B) (m 1 0 • B⁻¹) (m 1 1 • 1) *
        Matrix.J (Fin g) R *
        (Matrix.fromBlocks (m 0 0 • 1) (m 0 1 • B) (m 1 0 • B⁻¹) (m 1 1 • 1)).transpose =
      Matrix.J (Fin g) R
    rw [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    simp [Matrix.transpose_smul, Matrix.transpose_one, hB.eq, Matrix.transpose_nonsing_inv,
      Matrix.mul_nonsing_inv B hBdet, Matrix.nonsing_inv_mul B hBdet]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← mul_smul, ← mul_smul, mul_comm (m 0 0) (m 0 1)]
      exact add_neg_cancel _
    · have hdet_neg : m 1 0 * m 0 1 - m 1 1 * m 0 0 = -1 := by
        linear_combination -hdet
      rw [← mul_smul, ← mul_smul, ← sub_eq_add_neg, ← sub_smul, hdet_neg, neg_one_smul]
    · rw [← mul_smul, ← mul_smul, ← sub_eq_add_neg, ← sub_smul, hdet, one_smul]
    · rw [← mul_smul, ← mul_smul, mul_comm (m 1 0) (m 1 1)]
      exact add_neg_cancel _⟩
  map_one' := by
    apply Subtype.ext
    simp [Sp2gR.SL2blockMatrix, ← Matrix.fromBlocks_one]
  map_mul' := by
    intro m n
    apply Subtype.ext
    rw [Sp2gR.coe_mul]
    change Matrix.fromBlocks ((m * n) 0 0 • 1) ((m * n) 0 1 • B)
      ((m * n) 1 0 • B⁻¹) ((m * n) 1 1 • 1) =
      Matrix.fromBlocks (m 0 0 • 1) (m 0 1 • B) (m 1 0 • B⁻¹) (m 1 1 • 1) *
        Matrix.fromBlocks (n 0 0 • 1) (n 0 1 • B) (n 1 0 • B⁻¹) (n 1 1 • 1)
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_nonsing_inv B hBdet,
      Matrix.nonsing_inv_mul B hBdet]
    split_ands
    · rw [add_smul]
      rw [mul_comm]
      rw [mul_smul, mul_smul]
      rw [add_left_cancel_iff]
      rw [<-mul_smul, <-mul_smul, mul_comm]
    · rw [add_smul]
      rw [mul_comm (m 0 1), mul_comm (m 0 0)]
      rw [mul_smul, mul_smul]
    · rw [add_smul]
      rw [mul_comm (m 1 0), mul_comm (m 1 1)]
      rw [mul_smul, mul_smul]
    · rw [add_smul]
      rw [mul_comm (m 1 0), mul_comm (m 1 1)]
      rw [mul_smul, mul_smul]

/-- Any fixed-block homomorphism `SL(2, R) →* Sp(2g, R)` is the representation attached to a
symmetric invertible matrix `B`. -/
theorem Sp2gR.SL2blockHom_classification
    (f : Matrix.SpecialLinearGroup (Fin 2) R →* Sp2gR (R := R) g)
    (hblocks : ∃ A B C D : Matrix (Fin g) (Fin g) R, ∀ m,
      (f m : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) =
        Sp2gR.SL2blockMatrix A B C D m) :
    ∃ (B : Matrix (Fin g) (Fin g) R) (hB : B.IsSymm) (hBdet : IsUnit B.det),
      f = Sp2gR.SL2blockHom B hB hBdet := by
  obtain ⟨A, B, C, D, hblocks⟩ := hblocks
  obtain ⟨hA, hD, hB, hBdet, hCeq⟩ :=
    Sp2gR.SL2blockHom_classification_of_blocks f A B C D hblocks
  refine ⟨B, hB, hBdet, ?_⟩
  apply MonoidHom.ext
  intro m
  apply Subtype.ext
  change (f m : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) =
    Sp2gR.SL2blockMatrix 1 B B⁻¹ 1 m
  rw [hblocks m, hA, hD, hCeq]

end SL2Embedding
