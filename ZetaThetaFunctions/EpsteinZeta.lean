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

/-!
# Epstein Zeta Functions

This file constructs the Epstein zeta function `ζ_q(s) = ∑'_{x ≠ 0} (q x)^(-s)` of a
positive-definite integral quadratic form `q` on `ℤⁿ`, converging for `Re(s) > n / 2`.

## `ZetaAbleQuadraticForm`

The general axiomatic package underlying `zeta_fun`: given a quadratic form `q : M → S`, rather
than assuming convergence directly (e.g. via positive-definiteness of `q`), convergence of
`∑'_{x ≠ 0} (q x)^(-s)` on the half-plane `{s | Re s > s_bound}` is packaged as the existence of a
summable comparison function `to_compare_g s` that eventually (away from a cofinite set of
exceptions) dominates the norm of the summand. This lets the same machinery be reused for other
quadratic-form zeta functions without re-deriving a bespoke convergence criterion each time.

## Epstein zeta

The bulk of the file builds the `ZetaAbleQuadraticForm` instance `epsteinZetaAble` for a
positive-definite `q : QuadraticMap ℤ (Fin n → ℤ) ℤ`:

* `latticeNormSq`/`toEuclidean_ZnRn`/`stdLattice` embed `ℤⁿ` into `EuclideanSpace ℝ (Fin n)` as the
  standard lattice, so that `ZLattice.summable_norm_rpow` gives the `p`-series convergence
  criterion `summable_latticeNormSq_rpow` for `∑'_{x≠0} ‖x‖^(-2s)`.
* `gramMatrix`/`gramMatrixR` extract the Gram matrix of `q`, and `gramQuadraticMap` uses it to
  extend `q` to a continuous real quadratic form on `EuclideanSpace ℝ (Fin n)` agreeing with `q` on
  integer points (`gramQuadraticMap_apply_toEuclidean`).
* Positive-definiteness transfers from `ℤ` to `ℝ` (`posDefR`) by first proving it on `ℚⁿ`
  (`gramQuadraticMap_rat_pos`, by clearing denominators) and then extending to `ℝⁿ` by continuity
  and density of `ℚⁿ` (`gramMatrixR_dotProduct_nonneg`), combined with anisotropy transferred via
  the (integral, hence rational-kernel) Gram matrix (`gramQuadraticMap_anisotropic`).
* A compactness argument on the unit sphere (`posDef_lower_bound`) turns positive-definiteness of
  the continuous extension into a uniform lower bound `Q x ≥ c * ‖x‖²`, which pulls back along the
  lattice embedding to `epsteinLowerBound_exists`.
* `epsteinZetaAble` assembles all of the above into the `ZetaAbleQuadraticForm` instance for
  `q`, with comparison function `to_compare_g s x = (c * ‖x‖²)^(-Re s)`.
-/

section GeneralZetaAble

universe u

variable {R : Type u} [cr_R: CommSemiring R]

class ZetaAbleQuadraticForm {M S}
  [SeminormedAddCommGroup S] [Module R S] [CompleteSpace S]
  [HPow S ℂ S]
  [AddCommMonoid M] [Module R M]
where
  q : QuadraticMap R M S
  s_bound: ℝ
  to_compare_g (s : ℂ): {x : M // x ≠ 0} -> ℝ
  to_compare_g_summable: ∀ (s : ℂ), s.re > s_bound -> Summable (to_compare_g s)
  comparison_eventual : ∀ (s : ℂ), s.re > s_bound -> ∀ᶠ (i : {i : M // i ≠ 0}) in Filter.cofinite,
    ‖(q i)^(-s)‖ ≤ to_compare_g s i

namespace ZetaAbleQuadraticForm

variable {S : Type u}
  [s_snacm: SeminormedAddCommGroup S] [s_mod: Module R S] [s_cs: CompleteSpace S]
  [HPow S ℂ S]
variable {M : Type u} [AddCommMonoid M] [Module R M]
variable [zetaable : ZetaAbleQuadraticForm (R:=R) (M:=M) (S:=S)]

def domain : Set ℂ := {s : ℂ | s.re > zetaable.s_bound}

noncomputable def zeta_fun (s : zetaable.domain) : S:=
  ∑' x: {x : M // x ≠ 0}, ((zetaable.q x) : S)^(-(s : ℂ))

theorem zeta_fun_summable (s : ℂ) (hs : s.re > zetaable.s_bound) :
    Summable
      (α:=S) (β:={x : M // x ≠ 0})
      (f:=fun x : {x : M // x ≠ 0} => (zetaable.q x)^(-s))
    := by
  exact Summable.of_norm_bounded_eventually
    (f := (fun x : {x : M // x ≠ 0} => (zetaable.q x)^(-s)))
    (g := (zetaable.to_compare_g s))
    (hg:=zetaable.to_compare_g_summable s hs) (h:=zetaable.comparison_eventual s hs)

def zeta_fun_ext
  (s : zetaable.domain)
: HasSum
  (f := fun x : {x : M // x ≠ 0} => (zetaable.q x)^(-(s: ℂ)))
  (a := zeta_fun s) :=
  (zeta_fun_summable s s.2).hasSum

end ZetaAbleQuadraticForm

end GeneralZetaAble

section EpsteinZeta

variable {n : ℕ}

noncomputable def intCastLinearMap : ℤ →ₗ[ℤ] ℂ :=
  (Int.castRingHom ℂ).toAddMonoidHom.toIntLinearMap

-- `‖x‖²`, the finite sum over the `Fin n` coordinates of a single lattice point `x`
-- (as opposed to the infinite `tsum`/`Summable` sums over the lattice itself)
noncomputable def latticeNormSq (x : Fin n → ℤ) : ℝ :=
  ∑ j, (x j : ℝ) ^ 2

-- the standard embedding `ℤⁿ ↪ ℝⁿ` of a lattice point into Euclidean space
noncomputable def toEuclidean_ZnRn (x : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => (x j : ℝ))

lemma toEuclidean_apply (x : Fin n → ℤ) (j : Fin n) : toEuclidean_ZnRn x j = (x j : ℝ) := rfl

lemma toEuclidean_injective : Function.Injective (toEuclidean_ZnRn (n := n)) := fun x y h => by
  funext j
  exact_mod_cast congrFun ((EuclideanSpace.equiv (Fin n) ℝ).symm.injective h) j

-- `‖toEuclidean x‖² = ‖x‖²`: the embedding into Euclidean space is an isometry onto the
-- standard lattice, so the Euclidean norm agrees exactly with `latticeNormSq`
lemma norm_sq_toEuclidean (x : Fin n → ℤ) : ‖toEuclidean_ZnRn x‖ ^ 2 = latticeNormSq x := by
  rw [EuclideanSpace.real_norm_sq_eq, latticeNormSq]
  simp_rw [toEuclidean_apply]

-- the standard lattice `ℤⁿ ⊆ ℝⁿ`, as the `ℤ`-span of the standard orthonormal basis
-- (stated via `.toBasis` so that `instIsZLatticeRealSpan` / `DiscreteTopology` fire)
noncomputable abbrev stdLattice (n : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)

lemma toEuclidean_mem_stdLattice (x : Fin n → ℤ) : toEuclidean_ZnRn x ∈ stdLattice n := by
  rw [stdLattice, (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.mem_span_iff_repr_mem (R := ℤ)]
  intro j
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, toEuclidean_apply]
  exact ⟨x j, by simp⟩

lemma finrank_stdLattice : Module.finrank ℤ (stdLattice n) = n := by
  rw [ZLattice.rank ℝ, finrank_euclideanSpace_fin]

-- the key analytic input: `∑'_{x≠0} (‖x‖²)^(-s)` converges for `s > n/2`, via the
-- general `ℤ`-lattice `p`-series convergence criterion `ZLattice.summable_norm_rpow`
lemma summable_latticeNormSq_rpow {s : ℝ} (hs : (n : ℝ) / 2 < s) :
    Summable (fun x : {x : Fin n → ℤ // x ≠ 0} => (latticeNormSq x.1) ^ (-s)) := by
  have hr : (-2 * s : ℝ) < -(Module.finrank ℤ (stdLattice n) : ℝ) := by
    rw [finrank_stdLattice]; linarith
  have hinj : Function.Injective
      (fun x : {x : Fin n → ℤ // x ≠ 0} =>
        (⟨toEuclidean_ZnRn x.1, toEuclidean_mem_stdLattice x.1⟩ : stdLattice n)) :=
    fun x y h => Subtype.ext (toEuclidean_injective (Subtype.ext_iff.mp h))
  have key : ∀ x : {x : Fin n → ℤ // x ≠ 0},
      ‖toEuclidean_ZnRn x.1‖ ^ (-2 * s) = (latticeNormSq x.1) ^ (-s) := fun x => by
    rw [show (-2 * s : ℝ) = 2 * (-s) by ring, Real.rpow_mul (norm_nonneg _),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, norm_sq_toEuclidean]
  exact ((ZLattice.summable_norm_rpow (stdLattice n) (-2 * s) hr).comp_injective hinj).congr key

-- the Gram matrix of `q`: `Mᵢⱼ = polar q eᵢ eⱼ`, where `eᵢ` is the `i`-th standard basis
-- vector of `Fin n → ℤ`
noncomputable def gramMatrix (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => q.polarBilin (Pi.single i 1) (Pi.single j 1)

noncomputable def gramMatrixR (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.map (m := Fin n) (n:=Fin n) (α := ℤ) (β := ℝ) (M:=gramMatrix q) (f:=fun entry => (entry : ℝ))

lemma gramMatrix_symm (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) :
    gramMatrix q = (gramMatrix q).transpose := by
  ext i j
  simp only [gramMatrix, Matrix.transpose_apply, QuadraticMap.polarBilin_apply_apply]
  exact QuadraticMap.polar_comm q _ _

lemma gramMatrixR_symm (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) :
    gramMatrixR q = (gramMatrixR q).transpose := by
  simp only [gramMatrixR, ← Matrix.transpose_map, ← gramMatrix_symm]

-- the standard basis decomposition `x = ∑ i, xᵢ • eᵢ`
lemma std_basis_sum (x : Fin n → ℤ) : x = ∑ i, x i • Pi.single i (1 : ℤ) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply, Finset.mem_univ]

-- bilinear expansion of `polarBilin` in the standard basis, via the Gram matrix
lemma polarBilin_eq_sum (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (a b : Fin n → ℤ) :
    q.polarBilin a b = ∑ i, ∑ j, (a i * b j) * gramMatrix q i j := by
  conv_lhs => rw [std_basis_sum a, std_basis_sum b]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    gramMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  ring

-- polarization identity: `2 * q x` is the Gram quadratic form evaluated at `x`
lemma two_mul_eq_gramMatrix_sum (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (x : Fin n → ℤ) :
    2 * q x = ∑ i, ∑ j, (x i * x j) * gramMatrix q i j := by
  rw [← polarBilin_eq_sum, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
    nsmul_eq_mul]
  norm_num

-- the real quadratic form on `EuclideanSpace ℝ (Fin n)` built from the real Gram matrix of
-- `q`, as `½ ∑ᵢⱼ Mᵢⱼ xᵢxⱼ`
noncomputable def gramQuadraticMap (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) :
    QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ :=
  (2 : ℝ)⁻¹ • ∑ i, ∑ j, (gramMatrix q i j : ℝ) •
    QuadraticMap.linMulLin (EuclideanSpace.projₗ i) (EuclideanSpace.projₗ j)

-- `gramQuadraticMap q` agrees with `q` on integer lattice points
lemma gramQuadraticMap_apply_toEuclidean (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (x : Fin n → ℤ) :
    gramQuadraticMap q (toEuclidean_ZnRn x) = (q x : ℝ) := by
  have hcast : (∑ i, ∑ j, ((x i : ℝ) * (x j : ℝ)) * (gramMatrix q i j : ℝ)) = 2 * (q x : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_eq_gramMatrix_sum q x)
    push_cast at h
    exact h.symm
  simp only [gramQuadraticMap, QuadraticMap.smul_apply, QuadraticMap.sum_apply,
    QuadraticMap.linMulLin_apply, EuclideanSpace.projₗ, PiLp.projₗ_apply, toEuclidean_apply,
    smul_eq_mul]
  rw [show (∑ i, ∑ j, (gramMatrix q i j : ℝ) * ((x i : ℝ) * (x j : ℝ)))
        = ∑ i, ∑ j, ((x i : ℝ) * (x j : ℝ)) * (gramMatrix q i j : ℝ) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _,
    hcast, ← mul_assoc, inv_mul_cancel₀ (two_ne_zero), one_mul]

-- `gramQuadraticMap q` is continuous: it is a finite sum of scalar multiples of products
-- of the coordinate projections, which are continuous since they are linear maps on a
-- finite-dimensional space
lemma gramQuadraticMap_continuous (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) :
    Continuous (gramQuadraticMap q) := by
  have heq : (gramQuadraticMap q : EuclideanSpace ℝ (Fin n) → ℝ) =
      fun x => (2 : ℝ)⁻¹ * ∑ i, ∑ j, (gramMatrix q i j : ℝ) * (x i * x j) := by
    funext x
    simp [gramQuadraticMap, QuadraticMap.smul_apply, QuadraticMap.sum_apply,
      QuadraticMap.linMulLin_apply, EuclideanSpace.projₗ, PiLp.projₗ_apply, smul_eq_mul]
  rw [heq]
  refine continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_const.mul ?_)
  exact continuous_mul.comp
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) i).prodMk
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) j))

lemma polarization_gram
(q : QuadraticMap ℤ (Fin n → ℤ) ℤ)
(x : (EuclideanSpace ℝ (Fin n)))
:
(gramQuadraticMap q) x = (2 : ℝ)⁻¹ * (x ⬝ᵥ (gramMatrixR q).mulVec x) := by
  simp only [gramQuadraticMap, QuadraticMap.smul_apply, QuadraticMap.sum_apply,
    QuadraticMap.linMulLin_apply, EuclideanSpace.projₗ, PiLp.projₗ_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec, gramMatrixR, Matrix.map_apply, Finset.mul_sum]
  congr 1
  ext j
  congr 1
  ext i
  ring

-- every rational vector can be written as an integer vector divided by a common
-- (positive) denominator
lemma rat_common_denominator (x : EuclideanSpace ℚ (Fin n)) :
    ∃ (common_denom : ℕ), 0 < common_denom ∧
      ∃ (xz : Fin n → ℤ), ∀ i, x.ofLp i = (xz i : ℚ) / (common_denom : ℚ) := by
  set d : Fin n → ℕ := fun i => (x.ofLp i).den with hd
  refine ⟨∏ i, d i, Finset.prod_pos (fun i _ => (x.ofLp i).pos),
    fun i => (x.ofLp i).num * ∏ j ∈ Finset.univ.erase i, (d j : ℤ), fun i => ?_⟩
  have hprod : (∏ i, d i : ℚ) = (d i : ℚ) * ∏ j ∈ Finset.univ.erase i, (d j : ℚ) :=
    (Finset.mul_prod_erase Finset.univ (fun j => (d j : ℚ)) (Finset.mem_univ i)).symm
  push_cast
  rw [hprod, mul_div_mul_right _ _
    (show (∏ j ∈ Finset.univ.erase i, (d j : ℚ)) ≠ 0 by positivity)]
  exact (Rat.num_div_den _).symm

-- the rational version of `posDefR`: clearing denominators reduces positivity of the
-- (rationalized) Gram quadratic form on `EuclideanSpace ℚ (Fin n)` to positivity of `q`
-- on nonzero integer vectors
lemma gramQuadraticMap_rat_pos
    (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef)
    (x : EuclideanSpace ℚ (Fin n)) (hx : x ≠ 0) :
    0 < 2⁻¹ * x.ofLp ⬝ᵥ ((gramMatrix q).map fun entry => ↑entry).mulVec x.ofLp := by
  obtain ⟨common_denom, hcd_pos, xz, hxz⟩ := rat_common_denominator x
  have hxz_ne : xz ≠ 0 := by
    intro h
    apply hx
    rw [← WithLp.ofLp_eq_zero]
    funext i
    rw [hxz i, h]
    simp
  have hqxz : 0 < q xz := hq xz hxz_ne
  have h2 : (2 : ℚ) * (q xz : ℚ) = ∑ i, ∑ j, ((xz i : ℚ) * (xz j : ℚ)) * (gramMatrix q i j : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (two_mul_eq_gramMatrix_sum q xz)
    push_cast at h
    exact h
  have key : x.ofLp ⬝ᵥ ((gramMatrix q).map fun entry => (entry : ℚ)).mulVec x.ofLp
      = 2 * (common_denom : ℚ)⁻¹ ^ 2 * (q xz : ℚ) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
    rw [show (∑ i, ∑ j, x.ofLp i * ((gramMatrix q i j : ℚ) * x.ofLp j))
          = (common_denom : ℚ)⁻¹ ^ 2 *
            ∑ i, ∑ j, ((xz i : ℚ) * (xz j : ℚ)) * (gramMatrix q i j : ℚ) from ?_,
        ← h2]
    · ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hxz i, hxz j]
      ring
  rw [key]
  have hcd_pos' : (0 : ℚ) < (common_denom : ℚ) := by exact_mod_cast hcd_pos
  have hq_cast : (0 : ℚ) < (q xz : ℚ) := by exact_mod_cast hqxz
  have hfin : (2 : ℚ)⁻¹ * (2 * (common_denom : ℚ)⁻¹ ^ 2 * (q xz : ℚ))
      = (common_denom : ℚ)⁻¹ ^ 2 * (q xz : ℚ) := by ring
  rw [hfin]
  positivity

-- the Gram bilinear form, evaluated on a rational vector, casts to its real counterpart
-- evaluated on the coordinatewise cast of that vector
lemma gramMatrixR_dotProduct_ratCast (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (y : Fin n → ℚ) :
    ((y ⬝ᵥ ((gramMatrix q).map fun e => (e : ℚ)).mulVec y : ℚ) : ℝ)
      = (fun i => (y i : ℝ)) ⬝ᵥ (gramMatrixR q).mulVec (fun i => (y i : ℝ)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, gramMatrixR, Finset.mul_sum]
  push_cast
  rfl

-- `vᵗMv ≥ 0` for the real Gram matrix `M`, for every `v : Fin n → ℝ`: positivity on `ℚⁿ`
-- (via `gramQuadraticMap_rat_pos`) extends to all of `ℝⁿ` by continuity, since `ℚⁿ` is dense
lemma gramMatrixR_dotProduct_nonneg (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef)
    (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ (gramMatrixR q).mulVec v := by
  have hcont : Continuous (fun v : Fin n → ℝ => v ⬝ᵥ (gramMatrixR q).mulVec v) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_apply i).mul (continuous_const.mul (continuous_apply j))
  have hdense : DenseRange (fun y : Fin n → ℚ => (fun i => (y i : ℝ) : Fin n → ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hsub : Set.range (fun y : Fin n → ℚ => (fun i => (y i : ℝ) : Fin n → ℝ))
      ⊆ (fun v : Fin n → ℝ => v ⬝ᵥ (gramMatrixR q).mulVec v) ⁻¹' Set.Ici 0 := by
    rintro _ ⟨y, rfl⟩
    simp only [Set.mem_preimage, Set.mem_Ici]
    rcases eq_or_ne y 0 with hy | hy
    · simp [hy]
    · have hy' : (WithLp.toLp 2 y : EuclideanSpace ℚ (Fin n)) ≠ 0 := by
        intro h
        apply hy
        have h' := congrArg WithLp.ofLp h
        rwa [WithLp.ofLp_toLp, WithLp.ofLp_zero] at h'
      have h2 := gramQuadraticMap_rat_pos q hq (WithLp.toLp 2 y) hy'
      rw [WithLp.ofLp_toLp] at h2
      have hc : (0 : ℚ) < y ⬝ᵥ ((gramMatrix q).map fun e => (e : ℚ)).mulVec y := by linarith
      rw [← gramMatrixR_dotProduct_ratCast q y]
      exact_mod_cast hc.le
  have huniv : (Set.univ : Set (Fin n → ℝ))
      ⊆ (fun v : Fin n → ℝ => v ⬝ᵥ (gramMatrixR q).mulVec v) ⁻¹' Set.Ici 0 := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub (isClosed_Ici.preimage hcont)
  exact huniv (Set.mem_univ v)

-- `gramQuadraticMap q` is nonnegative on all of `ℝⁿ`
lemma gramQuadraticMap_nonneg (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ gramQuadraticMap q x := by
  rw [polarization_gram q x]
  exact mul_nonneg (by norm_num) (gramMatrixR_dotProduct_nonneg q hq x)

lemma gramMatrix_det_ne_zero (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.Anisotropic) :
    (gramMatrix q).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hz_ne, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hdot : z ⬝ᵥ (gramMatrix q).mulVec z = 0 := by
    simp [hz]
  have hsum : (∑ i, ∑ j, (z i * z j) * gramMatrix q i j) = 0 := by
    rw [← hdot]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 1
    ext i
    congr 1
    ext j
    ring
  have hqz_zero : q z = 0 := by
    have htwo : 2 * q z = 0 := by
      rw [two_mul_eq_gramMatrix_sum q z, hsum]
    nlinarith
  exact hz_ne (hq z hqz_zero)

lemma gramMatrixR_det_ne_zero (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.Anisotropic) :
    (gramMatrixR q).det ≠ 0 := by
  intro hdet
  exact gramMatrix_det_ne_zero q hq (by
    have hcast : ((gramMatrix q).det : ℝ) = (gramMatrixR q).det := by
      rw [Int.cast_det]
      rfl
    have hdet_cast : ((gramMatrix q).det : ℝ) = 0 := by
      rw [hcast, hdet]
    exact_mod_cast hdet_cast)

lemma gramMatrixR_posSemidef (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) :
    (gramMatrixR q).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.isHermitian_iff_isSymm]
    exact (gramMatrixR_symm q).symm
  · intro x
    simpa using gramMatrixR_dotProduct_nonneg q hq x

lemma gramQuadraticMap_anisotropic (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) :
    (gramQuadraticMap q).Anisotropic := by
  unfold QuadraticMap.Anisotropic
  intro x hx
  have hq_anisotropic : q.Anisotropic := hq.anisotropic
  have hdot : x ⬝ᵥ (gramMatrixR q).mulVec x = 0 := by
    have h := congrArg (fun t : ℝ => (2 : ℝ) * t) hx
    rw [polarization_gram q x] at h
    simpa [mul_assoc] using h
  have hmul : (gramMatrixR q).mulVec x = 0 :=
    ((gramMatrixR_posSemidef q hq).dotProduct_mulVec_zero_iff x).mp (by
      simpa using hdot)
  rw [← WithLp.ofLp_eq_zero]
  exact Matrix.eq_zero_of_mulVec_eq_zero (gramMatrixR_det_ne_zero q hq_anisotropic) hmul

lemma posDefR
  (q : QuadraticMap ℤ (Fin n → ℤ) ℤ)
  (hq : q.PosDef)
: (gramQuadraticMap q).PosDef :=
  QuadraticMap.posDef_of_nonneg (gramQuadraticMap_nonneg q hq) (gramQuadraticMap_anisotropic q hq)

-- extending `q` to a continuous positive definite quadratic form `Q` on `ℝⁿ` that agrees
-- with `q` on integer points, via `gramQuadraticMap`. The hard part is transferring `PosDef`
-- from `ℤ` to `ℝ`: writing `M` for the Gram matrix of `q` (so `q x = ½ xᵗMx`), positivity of
-- `xᵗMx` for all nonzero integer `x` extends by continuity to all `x ∈ ℝⁿ` with `xᵗMx ≥ 0`;
-- and if some nonzero real `x₀` had `x₀ᵗMx₀ = 0` then (since `M` has integer entries) `ker M`
-- is a rational subspace, hence contains a nonzero integer vector `x`, giving `q x = 0` and
-- contradicting `hq.anisotropic`.
lemma exists_real_posDef_quadraticMap (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) :
    ∃ Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ, Continuous Q ∧ Q.PosDef ∧
      ∀ x : Fin n → ℤ, Q (toEuclidean_ZnRn x) = (q x : ℝ) :=
  ⟨gramQuadraticMap q, gramQuadraticMap_continuous q, posDefR q hq, gramQuadraticMap_apply_toEuclidean q⟩

-- a continuous positive definite real quadratic form on `EuclideanSpace ℝ (Fin n)`
-- (with `n ≠ 0`) is bounded below by a positive multiple of the squared norm: take `c`
-- to be the minimum of `Q` on the unit sphere, attained by compactness (EVT), and use
-- homogeneity `Q (r • x) = r² • Q x` to rescale an arbitrary `x` onto the sphere
lemma posDef_lower_bound (hn : n ≠ 0) (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQcont : Continuous Q) (hQ : Q.PosDef) :
    ∃ c : ℝ, c > 0 ∧ ∀ x : EuclideanSpace ℝ (Fin n), c * ‖x‖ ^ 2 ≤ Q x := by
  obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hsphere_nonempty : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    ⟨EuclideanSpace.basisFun (Fin n) ℝ i0,
      mem_sphere_zero_iff_norm.mpr ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i0)⟩
  have hsphere_compact : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_sphere _ _
  obtain ⟨x0, hx0_mem, hx0_min⟩ :=
    hsphere_compact.exists_isMinOn hsphere_nonempty hQcont.continuousOn
  have hx0_ne : x0 ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [mem_sphere_zero_iff_norm.mp hx0_mem]; norm_num)
  set c := Q x0 with hc_def
  have hc_pos : 0 < c := hQ x0 hx0_ne
  refine ⟨c, hc_pos, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx_ne
  · simp [Q.map_zero]
  · have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    set y := ‖x‖⁻¹ • x with hy_def
    have hy_mem : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [mem_sphere_zero_iff_norm, hy_def, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hnorm_pos), inv_mul_cancel₀ hnorm_pos.ne']
    have hxy : x = ‖x‖ • y := by
      rw [hy_def, smul_smul, mul_inv_cancel₀ hnorm_pos.ne', one_smul]
    have hQx : Q x = ‖x‖ ^ 2 * Q y := by
      conv_lhs => rw [hxy]
      rw [Q.map_smul, smul_eq_mul, pow_two]
    rw [hQx]
    calc c * ‖x‖ ^ 2 ≤ Q y * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (isMinOn_iff.mp hx0_min y hy_mem) (sq_nonneg _)
      _ = ‖x‖ ^ 2 * Q y := mul_comm _ _

-- a constant `c > 0` with `q x ≥ c * ‖x‖²` for all `x`, obtained by transferring `q` to a
-- continuous positive definite real quadratic form (`exists_real_posDef_quadraticMap`) and
-- applying the compactness-based lower bound (`posDef_lower_bound`)
lemma epsteinLowerBound_exists (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) :
  ∃ c : ℝ, c > 0 ∧ ∀ (x : Fin n -> ℤ), c * latticeNormSq x ≤ (q x : ℝ) := by
  obtain ⟨Q, hQcont, hQ, hQeq⟩ := exists_real_posDef_quadraticMap q hq
  obtain ⟨c, hc_pos, hc⟩ := posDef_lower_bound hn Q hQcont hQ
  refine ⟨c, hc_pos, fun x => ?_⟩
  have h := hc (toEuclidean_ZnRn x)
  rwa [norm_sq_toEuclidean, hQeq x] at h

-- the Epstein zeta function of a rank-`n` lattice with positive definite form `q`,
-- with the classical convergence threshold `Re(s) > n / 2`
@[reducible]
noncomputable def epsteinZetaAble
    (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) :
    ZetaAbleQuadraticForm (R := ℤ) (M := Fin n → ℤ) (S := ℂ) :=
  let c := (epsteinLowerBound_exists hn q hq).choose
  {
    q := intCastLinearMap.compQuadraticMap q
    s_bound := (n : ℝ) / 2
    to_compare_g := fun s x => (c * latticeNormSq x.1) ^ (-s.re)
    -- `(c * ‖x‖²)^(-s.re) = c^(-s.re) * (‖x‖²)^(-s.re)`, and `∑_{x≠0} (‖x‖²)^(-s.re)`
    -- converges for `s.re > n/2` by `summable_latticeNormSq_rpow`
    to_compare_g_summable := fun s hs => by
      obtain ⟨c_pos, _⟩ := (epsteinLowerBound_exists hn q hq).choose_spec
      refine ((summable_latticeNormSq_rpow hs).mul_left (c ^ (-s.re))).congr (fun x => ?_)
      exact (Real.mul_rpow c_pos.le (Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
    comparison_eventual := fun s hs => Filter.Eventually.of_forall fun i => by
      obtain ⟨c_pos, hc_le⟩ := (epsteinLowerBound_exists hn q hq).choose_spec
      have hsum_pos : (0 : ℝ) < latticeNormSq i.1 := by
        obtain ⟨j, hj⟩ := Function.ne_iff.mp i.2
        exact Finset.sum_pos' (fun k _ => sq_nonneg _)
          ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (by exact_mod_cast hj)⟩
      have hcsum_pos : 0 < c * latticeNormSq i.1 := mul_pos c_pos hsum_pos
      have hq_pos : (0 : ℝ) < (q i.1 : ℝ) := by exact_mod_cast hq i.1 i.2
      have hsre_nonneg : 0 ≤ s.re :=
        le_of_lt <| lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg n) (by norm_num)) hs
      show ‖((q i.1 : ℤ) : ℂ) ^ (-s)‖ ≤ (c * latticeNormSq i.1) ^ (-s.re)
      rw [show ((q i.1 : ℤ) : ℂ) = ((q i.1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hq_pos, Complex.neg_re]
      exact Real.rpow_le_rpow_of_nonpos hcsum_pos (hc_le i.1) (neg_nonpos.mpr hsre_nonneg)
  }

end EpsteinZeta
