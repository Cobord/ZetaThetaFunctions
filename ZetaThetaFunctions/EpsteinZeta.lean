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

import ZetaThetaFunctions.LatticeUtils
import ZetaThetaFunctions.QuadraticFormUtils

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

The file builds the `ZetaAbleQuadraticForm` instance `epsteinZetaAble` for a positive-definite
`q : QuadraticMap ℤ (Fin n → ℤ) ℤ`, on top of the shared lattice/quadratic-form infrastructure in
`LatticeUtils.lean` (`latticeEmbedding`, `latticeNormSq`, `stdLattice`) and
`QuadraticFormUtils.lean` (`gramMatrix`/`gramMatrixR`, `gramQuadraticMap`, `posDef_lower_bound`,
and the `ℤ → ℝ` positive-definiteness transfer `posDefR`):

* `summable_latticeNormSq_rpow`: `ZLattice.summable_norm_rpow` applied to `stdLattice n`, giving
  the `p`-series convergence criterion for `∑'_{x≠0} ‖x‖^(-2s)`.
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

lemma zeta_fun_ext
  (s : zetaable.domain)
: HasSum
  (f := fun x : {x : M // x ≠ 0} => (zetaable.q x)^(-(s: ℂ)))
  (a := zeta_fun s) :=
  (zeta_fun_summable s s.2).hasSum

end ZetaAbleQuadraticForm

end GeneralZetaAble

section EpsteinZeta

variable {n : ℕ}

-- the key analytic input: `∑'_{x≠0} (‖x‖²)^(-s)` converges for `s > n/2`, via the
-- general `ℤ`-lattice `p`-series convergence criterion `ZLattice.summable_norm_rpow`
lemma summable_latticeNormSq_rpow {s : ℝ} (hs : (n : ℝ) / 2 < s) :
    Summable (fun x : {x : Fin n → ℤ // x ≠ 0} => (latticeNormSq x.1) ^ (-s)) := by
  have hr : (-2 * s : ℝ) < -(Module.finrank ℤ (stdLattice n) : ℝ) := by
    rw [finrank_stdLattice]; linarith
  have hinj : Function.Injective
      (fun x : {x : Fin n → ℤ // x ≠ 0} =>
        (⟨toEuclidean_ZnRn x.1, latticeEmbedding_mem_stdLattice x.1⟩ : stdLattice n)) :=
    fun x y h => Subtype.ext (latticeEmbedding_injective (Subtype.ext_iff.mp h))
  have key : ∀ x : {x : Fin n → ℤ // x ≠ 0},
      ‖toEuclidean_ZnRn x.1‖ ^ (-2 * s) = (latticeNormSq x.1) ^ (-s) := fun x => by
    rw [show (-2 * s : ℝ) = 2 * (-s) by ring, Real.rpow_mul (norm_nonneg _),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, norm_sq_latticeEmbedding]
  exact ((ZLattice.summable_norm_rpow (stdLattice n) (-2 * s) hr).comp_injective hinj).congr key

-- the Epstein zeta function of a rank-`n` lattice with positive definite form `q`,
-- with the classical convergence threshold `Re(s) > n / 2`
@[reducible]
noncomputable def epsteinZetaAble
    (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) :
    ZetaAbleQuadraticForm (R := ℤ) (M := Fin n → ℤ) (S := ℂ) :=
  let c := (LowerBound_of_pythagorean_exists hn q hq).choose
  {
    q := intCastLinearMap.compQuadraticMap q
    s_bound := (n : ℝ) / 2
    to_compare_g := fun s x => (c * latticeNormSq x.1) ^ (-s.re)
    -- `(c * ‖x‖²)^(-s.re) = c^(-s.re) * (‖x‖²)^(-s.re)`, and `∑_{x≠0} (‖x‖²)^(-s.re)`
    -- converges for `s.re > n/2` by `summable_latticeNormSq_rpow`
    to_compare_g_summable := fun s hs => by
      obtain ⟨c_pos, _⟩ := (LowerBound_of_pythagorean_exists hn q hq).choose_spec
      refine ((summable_latticeNormSq_rpow hs).mul_left (c ^ (-s.re))).congr (fun x => ?_)
      exact (Real.mul_rpow c_pos.le (Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
    comparison_eventual := fun s hs => Filter.Eventually.of_forall fun i => by
      obtain ⟨c_pos, hc_le⟩ := (LowerBound_of_pythagorean_exists hn q hq).choose_spec
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
