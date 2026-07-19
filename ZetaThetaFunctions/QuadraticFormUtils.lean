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

section GramMatrix

variable {n: ℕ}

/-- The Gram matrix of a lattice quadratic form `Q : QuadraticMap ℤ (Fin n → ℤ) S`, at the
standard basis of `Fin n → ℤ`: `Mᵢⱼ = polar Q eᵢ eⱼ`. Generic in the codomain `S` — shared by
`EpsteinZeta.lean`'s `gramMatrix` (`S := ℤ`) and `SiegelModular.lean`'s `gramMatrixLattice`
(`S := ℝ`). -/
noncomputable def latticeGramMatrix {S : Type*} [CommRing S] (Q : QuadraticMap ℤ (Fin n → ℤ) S) :
    Matrix (Fin n) (Fin n) S :=
  fun i j => Q.polarBilin (Pi.single i 1) (Pi.single j 1)

lemma latticeGramMatrix_symm {S : Type*} [CommRing S] (Q : QuadraticMap ℤ (Fin n → ℤ) S) :
    latticeGramMatrix Q = (latticeGramMatrix Q).transpose := by
  ext i j
  simp only [latticeGramMatrix, Matrix.transpose_apply, QuadraticMap.polarBilin_apply_apply]
  exact QuadraticMap.polar_comm Q _ _

/-- Bilinear expansion of `Q.polarBilin` in the standard basis, via `latticeGramMatrix`. -/
lemma polarBilin_eq_latticeGramMatrix_sum {S : Type*} [CommRing S]
    (Q : QuadraticMap ℤ (Fin n → ℤ) S) (a b : Fin n → ℤ) :
    Q.polarBilin a b = ∑ i, ∑ j, (a i * b j) • latticeGramMatrix Q i j := by
  conv_lhs => rw [std_basis_sum a, std_basis_sum b]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    latticeGramMatrix, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

/-- The Gram matrix of `q`, at `S := ℤ`. -/
noncomputable def gramMatrix (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  latticeGramMatrix q

noncomputable def gramMatrixR (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.map (m := Fin n) (n:=Fin n) (α := ℤ) (β := ℝ) (M:=gramMatrix q) (f:=fun entry => (entry : ℝ))

/-- The Gram matrix of an already-`ℝ`-valued lattice quadratic form, at `S := ℝ`. Unlike
`gramMatrixR` (which casts the `ℤ`-valued `gramMatrix`), this applies directly to a
`QuadraticMap ℤ (Fin n → ℤ) ℝ` — used by `SiegelModular.lean`'s `latticeQuadToEuclidean`. -/
noncomputable abbrev gramMatrixLattice (Q : QuadraticMap ℤ (Fin n → ℤ) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  latticeGramMatrix Q

lemma gramMatrix_symm (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) :
    gramMatrix q = (gramMatrix q).transpose :=
  latticeGramMatrix_symm q

lemma gramMatrixR_symm (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) :
    gramMatrixR q = (gramMatrixR q).transpose := by
  simp only [gramMatrixR, ← Matrix.transpose_map, ← gramMatrix_symm]

-- bilinear expansion of `polarBilin` in the standard basis, via the Gram matrix
lemma polarBilin_eq_sum (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (a b : Fin n → ℤ) :
    q.polarBilin a b = ∑ i, ∑ j, (a i * b j) * gramMatrix q i j := by
  rw [polarBilin_eq_latticeGramMatrix_sum q a b]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => smul_eq_mul _ _

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
    QuadraticMap.linMulLin_apply, EuclideanSpace.projₗ, PiLp.projₗ_apply, latticeEmbedding_apply,
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

end GramMatrix

section RationalVectorSpace

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

end RationalVectorSpace

section RealVectorSpace

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

end RealVectorSpace

section Bounds

variable {n : ℕ}

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
lemma LowerBound_of_pythagorean_exists (hn : n ≠ 0) (q : QuadraticMap ℤ (Fin n → ℤ) ℤ) (hq : q.PosDef) :
  ∃ c : ℝ, c > 0 ∧ ∀ (x : Fin n -> ℤ), c * latticeNormSq x ≤ (q x : ℝ) := by
  obtain ⟨Q, hQcont, hQ, hQeq⟩ := exists_real_posDef_quadraticMap q hq
  obtain ⟨c, hc_pos, hc⟩ := posDef_lower_bound hn Q hQcont hQ
  refine ⟨c, hc_pos, fun x => ?_⟩
  have h := hc (toEuclidean_ZnRn x)
  rwa [norm_sq_latticeEmbedding, hQeq x] at h

end Bounds


section QuadraticMapIdentities

/-- `Q (x - y) = Q x + Q y - Q.polarBilin x y`, the "completing the square" identity for a
general quadratic map. -/
theorem QuadraticMap.sub_eq_add_sub_polarBilin
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (Q : QuadraticMap R M N) (x y : M) :
    Q (x - y) = Q x + Q y - Q.polarBilin x y := by
  have e1 : QuadraticMap.polar (⇑Q) x (-y) = Q (x + -y) - Q x - Q (-y) := rfl
  rw [Q.map_neg, ← sub_eq_add_neg, ← Q.polarBilin_apply_apply, map_neg] at e1
  linear_combination (norm := abel1) -e1

end QuadraticMapIdentities

section EuclideanGramMatrix

/-- A real quadratic form `Q` on `EuclideanSpace ℝ (Fin n)`, pulled back to a `ℤ`-valued
(real-valued) quadratic form on the lattice `Fin n → ℤ` via the standard embedding. -/
noncomputable def latticeQuadraticMap (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) :
    QuadraticMap ℤ (Fin n → ℤ) ℝ :=
  (Q.restrictScalars (S := ℤ)).comp (pre_latticeEmbeddingLinear (R:=ℤ) (f:=Int.castRingHom ℝ) n)

@[simp]
lemma latticeQuadraticMap_apply (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (x : Fin n → ℤ) :
    latticeQuadraticMap Q x = Q (toEuclidean_ZnRn x) := rfl

/-- The Gram matrix of a real quadratic form `Q` on `EuclideanSpace ℝ (Fin n)`, with respect to
the standard orthonormal basis: `gramMatrixReal Q i j = Q.polarBilin (e i) (e j)`. -/
noncomputable def gramMatrixReal (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.BilinForm.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Q.polarBilin

lemma gramMatrixReal_apply (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (i j : Fin n) :
    gramMatrixReal Q i j =
      Q.polarBilin (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  rw [gramMatrixReal, LinearMap.BilinForm.toMatrix_apply]
  simp

/-- `gramMatrixReal` commutes with real scalar multiplication of the quadratic form. -/
lemma gramMatrixReal_smul (c : ℝ) (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) :
    gramMatrixReal (c • Q) = c • gramMatrixReal Q := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, gramMatrixReal_apply, gramMatrixReal_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  set a := EuclideanSpace.basisFun (Fin n) ℝ i
  set b := EuclideanSpace.basisFun (Fin n) ℝ j
  show (c • Q) (a + b) - (c • Q) a - (c • Q) b = c * (Q (a + b) - Q a - Q b)
  simp only [QuadraticMap.smul_apply, smul_eq_mul]
  ring

/-- `gramMatrixReal Q` is symmetric: `Q.polarBilin` is a symmetric bilinear form
(`QuadraticMap.polar_comm`). -/
lemma gramMatrixReal_symm (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (i j : Fin n) :
    gramMatrixReal Q i j = gramMatrixReal Q j i := by
  simp [gramMatrixReal_apply, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

/-- The Gram matrix of a positive definite real quadratic form is itself positive definite,
via the basis-dependent equivalence between positive-definiteness of a symmetric bilinear form
(here `2 • Q = Q.polarBilin.toQuadraticMap`) and positive-definiteness of its Gram matrix. -/
lemma gramMatrixReal_posDef (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (hQ : Q.PosDef) :
    (gramMatrixReal Q).PosDef := by
  have hsymm : LinearMap.BilinForm.IsSymm Q.polarBilin := by
    constructor
    intro x y
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  rw [gramMatrixReal, ← LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix _ _ hsymm,
    QuadraticMap.toQuadraticMap_polarBilin]
  intro x hx
  have hQx := hQ x hx
  rw [QuadraticMap.smul_apply, nsmul_eq_mul]
  push_cast
  linarith

lemma gramMatrixReal_det_isUnit (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (hQ : Q.PosDef) :
    IsUnit (gramMatrixReal Q).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (gramMatrixReal_posDef Q hQ).isUnit

end EuclideanGramMatrix

variable {R : Type*} [CommRing R] [Algebra R ℝ] [Algebra R ℂ] [IsScalarTower R ℝ ℂ]
variable {g : ℕ}

section QuadFromMatrix

/-- The real quadratic form on `EuclideanSpace ℝ (Fin g)` with Gram matrix `S` in the standard
orthonormal basis, `Q x = ⅟2 ∑ᵢⱼ Sᵢⱼ xᵢxⱼ` — inverse to `gramMatrixReal` on symmetric `S`
(the general-matrix analogue of `EpsteinZeta.lean`'s `gramQuadraticMap`, which is specialized to
integral matrices). Phrased via `⅟(2 : ℝ)` (`Invertible`), not `(2 : ℝ)⁻¹`: the polarization
argument behind the round-trip lemmas below only ever needs `2` invertible, not that `ℝ` is a
field — `ℝ`'s field structure is a red herring here, `Invertible (2 : ℝ)` is the actual
hypothesis in play (and is available as a global instance regardless). -/
noncomputable def quadraticMapOfMatrix (S : Matrix (Fin g) (Fin g) R) :
    QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ :=
  ⅟(2 : ℝ) • ∑ i, ∑ j, (algebraMap R ℝ (S i j)) •
    QuadraticMap.linMulLin (EuclideanSpace.projₗ i) (EuclideanSpace.projₗ j)

omit [Algebra R ℂ] [IsScalarTower R ℝ ℂ] in
/-- `quadraticMapOfMatrix` unfolded at a point, for an arbitrary coefficient matrix `S` over the
ambient ring `R` (not just `ℝ`) — the general-matrix analogue of `EpsteinZeta.lean`'s
`gramQuadraticMap_apply_toEuclidean`. -/
lemma quadraticMapOfMatrix_apply (S : Matrix (Fin g) (Fin g) R) (x : EuclideanSpace ℝ (Fin g)) :
    quadraticMapOfMatrix S x = ⅟(2 : ℝ) * ∑ i, ∑ j, (algebraMap R ℝ (S i j)) * (x i * x j) := by
  simp [quadraticMapOfMatrix, QuadraticMap.smul_apply, QuadraticMap.sum_apply,
    QuadraticMap.linMulLin_apply, EuclideanSpace.projₗ, PiLp.projₗ_apply, Algebra.smul_def]

/-- `quadraticMapOfMatrix` commutes with real scalar multiplication of a real coefficient
matrix. -/
lemma quadraticMapOfMatrix_smul (c : ℝ) (S : Matrix (Fin g) (Fin g) ℝ) :
    quadraticMapOfMatrix (R := ℝ) (c • S) = c • quadraticMapOfMatrix (R := ℝ) S := by
  apply QuadraticMap.ext
  intro v
  rw [QuadraticMap.smul_apply, quadraticMapOfMatrix_apply, quadraticMapOfMatrix_apply,
    smul_eq_mul]
  repeat rw [Finset.mul_sum]
  congr 1
  ext i
  repeat rw [Finset.mul_sum]
  congr 1
  ext j
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, Algebra.algebraMap_self_apply]
  ring

omit [Algebra R ℂ] [IsScalarTower R ℝ ℂ] in
/-- `quadraticMapOfMatrix S` is continuous: it is a finite sum of scalar multiples of products of
coordinate projections. Mirrors `EpsteinZeta.lean`'s `gramQuadraticMap_continuous`. -/
lemma quadraticMapOfMatrix_continuous (S : Matrix (Fin g) (Fin g) R) :
    Continuous (quadraticMapOfMatrix S) := by
  have heq : (quadraticMapOfMatrix S : EuclideanSpace ℝ (Fin g) → ℝ) =
      fun x => ⅟(2 : ℝ) * ∑ i, ∑ j, (algebraMap R ℝ (S i j)) * (x i * x j) := by
    funext x
    exact quadraticMapOfMatrix_apply S x
  rw [heq]
  refine continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_const.mul ?_)
  exact continuous_mul.comp
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin g => ℝ) i).prodMk
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin g => ℝ) j))

/-- `quadraticMapOfMatrix` is `PosDef` when its Gram matrix, scaled by `2` (to offset this
definition's `⅟2` normalization), is `PosDef` as a plain `Matrix.PosDef`. Needed to build a
`SiegelUpperHalfSpace`/`RiemannThetaAble` instance directly from a bare complex symmetric matrix
with positive-definite real or imaginary part (as opposed to from a `(Q_Re, Q_Im)` pair already
known to be `PosDef`), e.g. in `PoissonSummation.lean`'s summability bridge. -/
lemma quadraticMapOfMatrix_posDef {S : Matrix (Fin g) (Fin g) ℝ} (hS : S.PosDef) :
    (quadraticMapOfMatrix ((2 : ℝ) • S) : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ).PosDef := by
  intro x hx
  rw [quadraticMapOfMatrix_apply]
  have hx' : x.ofLp ≠ 0 := fun h => hx (by ext i; exact congrFun h i)
  have hpos := hS.dotProduct_mulVec_pos (x := x.ofLp) hx'
  simp only [dotProduct, Matrix.mulVec, star_trivial, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self_apply] at hpos ⊢
  rw [show ⅟(2 : ℝ) * ∑ i, ∑ j, (2 * S i j) * (x i * x j) = ∑ i, x i * ∑ j, S i j * x j from ?_]
  · exact hpos
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 : (⅟(2 : ℝ)) = (2 : ℝ)⁻¹ := invOf_eq_inv 2
    rw [h2]; ring

omit [Algebra R ℝ] [Algebra R ℂ] [IsScalarTower R ℝ ℂ] in
/-- `gramMatrixReal` inverts `quadraticMapOfMatrix` on *symmetric* real matrices — the reverse
direction of `quadraticMapOfMatrix_gramMatrixReal`. Symmetry is essential: in general
`gramMatrixReal (quadraticMapOfMatrix S) = (S + Sᵀ) / 2`, the symmetrization of `S`. Again only
`Invertible (2 : ℝ)` is used, not `ℝ`'s field structure (`invOf_eq_inv` converts `⅟2` to `2⁻¹`
right before the final `ring` normalization, the one place a field fact is genuinely convenient
rather than essential). -/
lemma gramMatrixReal_quadraticMapOfMatrix {S : Matrix (Fin g) (Fin g) ℝ} (hS : S.IsSymm) :
    gramMatrixReal (quadraticMapOfMatrix S) = S := by
  set e := EuclideanSpace.basisFun (Fin g) ℝ with he
  have hcoord : ∀ a i : Fin g, e a i = if i = a then (1 : ℝ) else 0 := by
    intro a i
    rw [he, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have hcollapse : ∀ a b : Fin g, ∑ i, ∑ j, S i j * (e a i * e b j) = S a b := by
    intro a b
    simp only [hcoord]
    simp [Finset.sum_ite_eq']
  have hSlk : ∀ i j : Fin g, S j i = S i j := by
    intro i j
    have h := congrFun (congrFun hS j) i
    rw [Matrix.transpose_apply] at h
    exact h.symm
  ext k l
  rw [gramMatrixReal_apply, QuadraticMap.polarBilin_apply_apply]
  show QuadraticMap.polar (quadraticMapOfMatrix S) (e k) (e l) = S k l
  unfold QuadraticMap.polar
  rw [quadraticMapOfMatrix_apply, quadraticMapOfMatrix_apply, quadraticMapOfMatrix_apply]
  simp only [Algebra.algebraMap_self_apply, PiLp.add_apply]
  have hexpand : ∀ i j : Fin g,
      S i j * ((e k i + e l i) * (e k j + e l j)) - S i j * (e k i * e k j)
        - S i j * (e l i * e l j)
      = S i j * (e k i * e l j) + S i j * (e l i * e k j) := by
    intro i j; ring
  rw [← mul_sub, ← mul_sub]
  simp_rw [← Finset.sum_sub_distrib, hexpand, Finset.sum_add_distrib]
  rw [hcollapse k l, hcollapse l k, hSlk l k, invOf_eq_inv]
  ring

end QuadFromMatrix


section IntMatrixPosDefTransfer

/-- A positive-definite *integer* matrix stays positive-definite after casting into `ℝ`. This is
genuinely not formal: `Matrix.PosDef` over `ℤ` only quantifies over `x : Fin g → ℤ`, while over `ℝ`
it quantifies over the whole continuum `Fin g → ℝ`. The argument: (1) clear denominators
(`rat_common_denominator`, from `EpsteinZeta.lean`) to get positivity on `Fin g → ℚ`, then extend to
all of `Fin g → ℝ` by continuity and density of `ℚ^g` in `ℝ^g`, giving `PosSemidef` over `ℝ`; (2)
`S.det ≠ 0` over `ℤ` (else `Matrix.exists_mulVec_eq_zero_iff`, valid since `ℤ` is a domain, gives an
integer kernel vector `z ≠ 0` with `z ⬝ᵥ S.mulVec z = 0`, contradicting strict positivity at `z`),
transported to `(S.map cast).det ≠ 0` over `ℝ` via `Int.cast_det` and injectivity of the cast, which
rules out a real zero of the semidefinite form (`PosSemidef.dotProduct_mulVec_zero_iff` +
`Matrix.eq_zero_of_mulVec_eq_zero`), upgrading (1) to strict `PosDef`. This is genuinely specific to
`S` having *integer* entries — see `latticeQuadToEuclidean`'s docstring below for why the analogous
claim is false for an arbitrary `ℝ`-valued lattice quadratic form. -/
theorem Matrix.PosDef.int_cast_posDef {g : ℕ} {S : Matrix (Fin g) (Fin g) ℤ} (hS : S.PosDef) :
    (S.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hSsymm : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp hS.isHermitian
  have hSmapSymm : (S.map (Int.cast : ℤ → ℝ)).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    show (S.map _).transpose = S.map _
    rw [← Matrix.transpose_map, hSsymm]
  have hrat_pos : ∀ x : EuclideanSpace ℚ (Fin g), x ≠ 0 →
      0 < x.ofLp ⬝ᵥ ((S.map fun e => (e : ℚ)).mulVec x.ofLp) := by
    intro x hx
    obtain ⟨N, hNpos, xz, hxz⟩ := rat_common_denominator x
    have hxzne : xz ≠ 0 := by
      intro h
      apply hx
      rw [← WithLp.ofLp_eq_zero]
      funext i
      rw [hxz i, h]
      simp
    have hSxz : 0 < (xz ⬝ᵥ S.mulVec xz : ℤ) := hS.dotProduct_mulVec_pos hxzne
    have hNne : (N : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hkey : x.ofLp ⬝ᵥ ((S.map fun e => (e : ℚ)).mulVec x.ofLp)
        = (N : ℚ)⁻¹ ^ 2 * (xz ⬝ᵥ S.mulVec xz : ℤ) := by
      have hL : x.ofLp ⬝ᵥ ((S.map fun e => (e : ℚ)).mulVec x.ofLp)
          = ∑ i, ∑ j, x.ofLp i * ((S i j : ℚ) * x.ofLp j) := by
        simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
      have hR : ((xz ⬝ᵥ S.mulVec xz : ℤ) : ℚ)
          = ∑ i, ∑ j, (xz i : ℚ) * ((S i j : ℚ) * (xz j : ℚ)) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        push_cast
        rfl
      rw [hL, hR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hxz i, hxz j]
      field_simp
    rw [hkey]
    have hNpos' : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
    have hSxz' : (0 : ℚ) < (xz ⬝ᵥ S.mulVec xz : ℤ) := by exact_mod_cast hSxz
    positivity
  have hSemiR : ∀ v : Fin g → ℝ, 0 ≤ v ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)).mulVec v := by
    intro v
    have hcont : Continuous (fun v : Fin g → ℝ => v ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)).mulVec v) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (continuous_apply i).mul (continuous_const.mul (continuous_apply j))
    have hdense : DenseRange (fun y : Fin g → ℚ => (fun i => (y i : ℝ) : Fin g → ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    have hsub : Set.range (fun y : Fin g → ℚ => (fun i => (y i : ℝ) : Fin g → ℝ))
        ⊆ (fun v : Fin g → ℝ => v ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)).mulVec v) ⁻¹' Set.Ici 0 := by
      rintro _ ⟨y, rfl⟩
      simp only [Set.mem_preimage, Set.mem_Ici]
      rcases eq_or_ne y 0 with hy | hy
      · simp [hy]
      · have hy' : (WithLp.toLp 2 y : EuclideanSpace ℚ (Fin g)) ≠ 0 := by
          intro h
          apply hy
          have h' := congrArg WithLp.ofLp h
          rwa [WithLp.ofLp_toLp, WithLp.ofLp_zero] at h'
        have h2 := hrat_pos (WithLp.toLp 2 y) hy'
        rw [WithLp.ofLp_toLp] at h2
        have hcastrat : ((y ⬝ᵥ ((S.map fun e => (e : ℚ)).mulVec y) : ℚ) : ℝ)
            = (fun i => (y i : ℝ)) ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)).mulVec (fun i => (y i : ℝ)) := by
          simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
          push_cast
          rfl
        rw [← hcastrat]
        exact_mod_cast h2.le
    have huniv : (Set.univ : Set (Fin g → ℝ))
        ⊆ (fun v : Fin g → ℝ => v ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)).mulVec v) ⁻¹' Set.Ici 0 := by
      rw [← hdense.closure_eq]
      exact closure_minimal hsub (isClosed_Ici.preimage hcont)
    exact huniv (Set.mem_univ v)
  have hSemi : (S.map (Int.cast : ℤ → ℝ)).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hSmapSymm hSemiR
  have hdetS : S.det ≠ 0 := by
    intro hdet
    obtain ⟨z, hzne, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hSz : 0 < (z ⬝ᵥ S.mulVec z : ℤ) := hS.dotProduct_mulVec_pos hzne
    rw [hz, dotProduct_zero] at hSz
    exact lt_irrefl 0 hSz
  have hdetR : (S.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    intro hdet
    apply hdetS
    have hcast : ((S.det : ℤ) : ℝ) = (S.map (Int.cast : ℤ → ℝ)).det := Int.cast_det S
    rw [hdet] at hcast
    exact_mod_cast hcast
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hSmapSymm fun v hv => ?_
  rcases (hSemi.dotProduct_mulVec_nonneg v).lt_or_eq with h | h
  · simpa using h
  · exfalso
    apply hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hdetR ((hSemi.dotProduct_mulVec_zero_iff v).mp h.symm)

end IntMatrixPosDefTransfer

section IntegralQuadraticFormExtension

/-- A lattice quadratic form `Q : QuadraticMap ℤ (Fin g → ℤ) ℝ`, "put back" into a genuine real
quadratic form on `EuclideanSpace ℝ (Fin g)` via its Gram matrix (`gramMatrixLattice`) and
`quadraticMapOfMatrix`. Continuity is automatic (`quadraticMapOfMatrix_continuous`); *positive*-
definiteness is **not** automatic from `Q`'s positivity on the lattice alone (unlike the integral,
`ℤ`-valued case handled by `EpsteinZeta.posDefR`) — an `ℝ`-valued lattice quadratic form positive at
every nonzero lattice point can still fail to be positive-definite on the real span (e.g. a rank-one
form vanishing along an irrational direction, which therefore never meets the lattice) — so callers
must supply that fact separately. -/
noncomputable def latticeQuadToEuclidean (Q : QuadraticMap ℤ (Fin g → ℤ) ℝ) :
    QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ :=
  quadraticMapOfMatrix (gramMatrixLattice Q)

lemma latticeQuadToEuclidean_continuous (Q : QuadraticMap ℤ (Fin g → ℤ) ℝ) :
    Continuous (latticeQuadToEuclidean Q) :=
  quadraticMapOfMatrix_continuous _

lemma latticeQuadToEuclidean_restrict (Q : QuadraticMap ℤ (Fin g → ℤ) ℝ)
    (z : Fin g → ℤ) :
    latticeQuadToEuclidean Q (toEuclidean_ZnRn z) = Q z := by
  have hgram_symm : (gramMatrixLattice Q).IsSymm := by
    ext i j
    simp only [gramMatrixLattice, Matrix.transpose_apply]
    exact QuadraticMap.polar_comm Q _ _
  have hgram_round_trip : gramMatrixReal (latticeQuadToEuclidean Q) =
      gramMatrixLattice Q := by
    exact gramMatrixReal_quadraticMapOfMatrix hgram_symm
  have hrestrict_round_trip : latticeQuadraticMap (latticeQuadToEuclidean Q) = Q := by
    have hpolar (u : Fin g → ℤ) : Q.polarBilin u u =
        ∑ i, ∑ j, ((u i : ℝ) * (u j : ℝ)) * gramMatrixLattice Q i j := by
      conv_lhs => rw [std_basis_sum u, std_basis_sum u]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        gramMatrixLattice]
      rw [← std_basis_sum u]
      simp only [zsmul_eq_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [latticeGramMatrix]
      ring
    have hsum (u : Fin g → ℤ) :
        ∑ i, ∑ j, ((u i : ℝ) * (u j : ℝ)) * gramMatrixLattice Q i j = 2 * Q u := by
      rw [← hpolar u, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
      ring
    apply QuadraticMap.ext
    intro u
    change latticeQuadToEuclidean Q (toEuclidean_ZnRn u) = Q u
    rw [latticeQuadToEuclidean, quadraticMapOfMatrix_apply]
    change ⅟(2 : ℝ) * ∑ i, ∑ j,
      gramMatrixLattice Q i j * ((u i : ℝ) * (u j : ℝ)) = Q u
    rw [show (∑ i, ∑ j, gramMatrixLattice Q i j * ((u i : ℝ) * (u j : ℝ))) =
        ∑ i, ∑ j, ((u i : ℝ) * (u j : ℝ)) * gramMatrixLattice Q i j from
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _, hsum u,
      invOf_eq_inv]
    ring
  simpa [latticeQuadraticMap_apply] using congrArg (fun q => q z) hrestrict_round_trip

end IntegralQuadraticFormExtension
