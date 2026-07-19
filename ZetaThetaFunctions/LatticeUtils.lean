import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Matrix.Order

import ZetaThetaFunctions.GeneralUtils

/-!
# Lattice utilities

Shared, lattice-only infrastructure used across `QuadraticFormZeta.lean`, `ThetaFunctions.lean`,
`QuadraticFormUtils.lean`, and `PoissonSummation.lean`: embedding a finite-rank lattice `ι → R`
into `EuclideanSpace ℝ ι` (`latticeEmbedding`), the squared norm of a lattice point
(`latticeNormSq`), and the standard lattice as a submodule (`stdLattice`). Nothing here is
specific to any one of those files' further constructions (zeta functions, theta functions, Gram
matrices).
-/

variable {n : ℕ}

section Embedding

/-- The standard embedding of the lattice `ι → R` into `EuclideanSpace ℝ ι`, coordinatewise along
a ring hom `f : R →+* ℝ`. -/
noncomputable def pre_latticeEmbedding (ι R : Type*) [Fintype ι] [Ring R] (f : RingHom R ℝ) :
    (ι → R) →+ EuclideanSpace ℝ ι where
  toFun x := (EuclideanSpace.equiv ι ℝ).symm (fun i => (f (x i) : ℝ))
  map_zero' := by
    apply (EuclideanSpace.equiv ι ℝ).injective
    ext i
    simp
  map_add' := by
    intro x y
    apply (EuclideanSpace.equiv ι ℝ).injective
    ext i
    simp

/-- The standard embedding `ℤ^ι ↪ EuclideanSpace ℝ ι` of a lattice point into Euclidean space. -/
noncomputable def latticeEmbedding (ι : Type*) [Fintype ι] : (ι → ℤ) →+ EuclideanSpace ℝ ι :=
  pre_latticeEmbedding ι (R := ℤ) (f := Int.castRingHom ℝ)

lemma latticeEmbeddingInjective (R : Type*) [Ring R] (f : RingHom R ℝ) (hf : Function.Injective f) :
    Function.Injective ⇑(pre_latticeEmbedding (Fin n) R f) := by
  rw [pre_latticeEmbedding]
  intro a1 a2 fa1a2
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at fa1a2
  funext x
  have fa1a2 := congrFun ((EuclideanSpace.equiv (Fin n) ℝ).symm.injective fa1a2) x
  exact hf fa1a2

lemma latticeEmbedding_injective : Function.Injective (latticeEmbedding (Fin n)) :=
  latticeEmbeddingInjective ℤ (Int.castRingHom ℝ) Int.cast_injective

lemma latticeEmbedding_apply (x : Fin n → ℤ) (j : Fin n) :
    latticeEmbedding (Fin n) x j = (x j : ℝ) := rfl

/-- The standard lattice embedding `(Fin n → R) →ₗ[ℤ] EuclideanSpace ℝ (Fin n)`, as a `ℤ`-linear
map (every `AddMonoidHom` between `ℤ`-modules is automatically `ℤ`-linear). -/
noncomputable def pre_latticeEmbeddingLinear (R : Type*) [Ring R] (f : RingHom R ℝ) (n : ℕ) :
    (Fin n → R) →ₗ[ℤ] EuclideanSpace ℝ (Fin n) :=
  (pre_latticeEmbedding (Fin n) (R := R) (f := f)).toIntLinearMap

noncomputable abbrev toEuclidean_ZnRn := latticeEmbedding (Fin n)

end Embedding

section NormSquared

/-- `‖x‖²`, the finite sum over the `Fin n` coordinates of a single lattice point `x` (as opposed
to the infinite `tsum`/`Summable` sums over the lattice itself). -/
noncomputable def latticeNormSq (x : Fin n → ℤ) : ℝ :=
  ∑ j, (x j : ℝ) ^ 2


/-- `‖latticeEmbedding x‖² = latticeNormSq x`: the embedding into Euclidean space is an isometry
onto the standard lattice, so the Euclidean norm agrees exactly with `latticeNormSq`. -/
lemma norm_sq_latticeEmbedding (x : Fin n → ℤ) :
    ‖latticeEmbedding (Fin n) x‖ ^ 2 = latticeNormSq x := by
  rw [EuclideanSpace.real_norm_sq_eq, latticeNormSq]
  simp_rw [latticeEmbedding_apply]

end NormSquared

section AsSubModule

/-- The standard lattice `ℤⁿ ⊆ ℝⁿ`, as the `ℤ`-span of the standard orthonormal basis (stated via
`.toBasis` so that `instIsZLatticeRealSpan` / `DiscreteTopology` fire). -/
noncomputable abbrev stdLattice (n : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)

lemma latticeEmbedding_mem_stdLattice (x : Fin n → ℤ) : latticeEmbedding (Fin n) x ∈ stdLattice n := by
  rw [stdLattice, (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.mem_span_iff_repr_mem (R := ℤ)]
  intro j
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    latticeEmbedding_apply]
  exact ⟨x j, by simp⟩

lemma latticeEmbedding_preimage_stdLattice (x : stdLattice n) :
  ∃! y : Fin n -> ℤ, toEuclidean_ZnRn y = x := by
  set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis with hb
  choose y hy using (b.mem_span_iff_repr_mem (R := ℤ) (x : EuclideanSpace ℝ (Fin n))).mp x.2
  have hcoord : ∀ j, (toEuclidean_ZnRn y) j = (x : EuclideanSpace ℝ (Fin n)) j := fun j => by
    have hrepr : (x : EuclideanSpace ℝ (Fin n)) j = b.repr (x : EuclideanSpace ℝ (Fin n)) j := by
      rw [hb, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    rw [latticeEmbedding_apply, hrepr, ← hy j, eq_intCast]
  have hxy : toEuclidean_ZnRn y = x := by
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    funext j
    exact hcoord j
  refine ⟨y, hxy, fun y' hy' => latticeEmbedding_injective (hy'.trans hxy.symm)⟩

lemma finrank_stdLattice : Module.finrank ℤ (stdLattice n) = n := by
  rw [ZLattice.rank ℝ, finrank_euclideanSpace_fin]

end AsSubModule

section DotImag

/-- The standard basis decomposition `x = ∑ i, xᵢ • eᵢ`. -/
lemma std_basis_sum (x : Fin n → ℤ) : x = ∑ i, x i • Pi.single i (1 : ℤ) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply, Finset.mem_univ]

variable {R : Type u} [cr : CommRing R] [Module R ℝ] [Module R ℂ] [IsScalarTower R ℝ ℂ]
variable [SMulCommClass R ℂ ℂ]

/-- The coordinate `zᵢ ∈ R2` of a shift `z` against the `i`-th standard basis vector of the
lattice `Fin n → R1`. -/
noncomputable def zCoord {R1 R2 : Type} [Ring R1] [Ring R2] [Module R1 R2] (z : (Fin n → R1) →ₗ[R1] R2) (i : Fin n) : R2 :=
  z (Pi.single i 1)

lemma zCoord_smul (c : ℂ) (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) (i : Fin n) :
    zCoord (c • z) i = c * zCoord z i := by
  show (c • z) (Pi.single i 1) = c * z (Pi.single i 1)
  rw [LinearMap.smul_apply, smul_eq_mul]

/-- The imaginary part of `zCoord z`, the real linear functional whose Gram-matrix Riesz
representative (w.r.t. a positive definite `qIm`) is the shift point `mu` used to complete the
square. -/
noncomputable def ellCoord {R : Type} [Ring R] [Module R ℂ] (z : (Fin n → R) →ₗ[R] ℂ) (i : Fin n) : ℝ :=
  (zCoord z i).im

lemma z_eq_sum (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) (x : Fin n → ℤ) :
    z x = ∑ i, (x i : ℂ) * zCoord z i := by
  conv_lhs => rw [std_basis_sum x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul, zCoord]

lemma z_im_eq_sum (z : (Fin n → ℤ) →ₗ[ℤ] ℂ) (x : Fin n → ℤ) :
    (z x).im = ∑ i, (x i : ℝ) * ellCoord z i := by
  conv_lhs => rw [std_basis_sum x, map_sum]
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  show (((x i : ℤ) : ℂ) * zCoord z i).im = (x i : ℝ) * ellCoord z i
  rw [Complex.mul_im]
  simp [ellCoord]

end DotImag
