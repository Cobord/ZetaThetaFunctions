import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.LinearCombination

/-!
# Projectively invariant products of pairwise brackets

This file constructs products of scalar powers of pairwise brackets for configurations on a
projective line over a general commutative ring. The exponent matrix is symmetric and neutral at
each point. These conditions make the product independent of the chosen representatives and
invariant under the special linear action.

`R` is kept a fully general `CommRing` (not a field/division ring), so Mathlib's
`Projectivization` (which requires a `DivisionRing`) cannot be reused; `ProjectiveLine R` below is
a from-scratch construction of the projective line `P¹(R)` in that generality, as pairs generating
the unit ideal of `R` modulo scaling by units of `R`.

## Main definitions

* `ProjLineRep R`: a representative `v : Fin 2 → R` of a point of `P¹(R)`, i.e. `IsCoprime (v 0) (v 1)`.
* `ProjectiveLine R`: `P¹(R)`, the quotient of `ProjLineRep R` by the `Rˣ`-scaling action.
* `bracket v w := v 0 * w 1 - v 1 * w 0`: the 2×2-determinant "cross bracket" of two representatives.
-/

variable {R : Type*} [CommRing R]

section ProjLineRep

/-- A representative of a point of the projective line `P¹(R)`: a pair `(v 0, v 1)` generating
the unit ideal of `R` (`IsCoprime (v 0) (v 1)`, i.e. `∃ a b, a * v 0 + b * v 1 = 1`). -/
@[reducible] def ProjLineRep (R : Type*) [CommRing R] : Type _ :=
  {v : Fin 2 → R // IsCoprime (v 0) (v 1)}

namespace ProjLineRep

/-- Scaling a coprime pair by a unit of `R` keeps it coprime: if `a*x+b*y=1`, then
`(a*u⁻¹)*(u*x) + (b*u⁻¹)*(u*y) = 1` too. -/
private lemma isCoprime_smul {x y : R} (h : IsCoprime x y) (u : Rˣ) :
    IsCoprime ((u : R) * x) ((u : R) * y) := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a * (↑u⁻¹ : R), b * (↑u⁻¹ : R), ?_⟩
  have hu : (↑u⁻¹ * ↑u : R) = 1 := u.inv_mul
  linear_combination (a * x + b * y) * hu + hab

instance : SMul Rˣ (ProjLineRep R) where
  smul u v := ⟨(u : R) • v.1, isCoprime_smul v.2 u⟩

@[simp] lemma coe_smul (u : Rˣ) (v : ProjLineRep R) :
    (u • v).1 = (u : R) • v.1 := rfl

instance : MulAction Rˣ (ProjLineRep R) where
  one_smul v := by
    apply Subtype.ext
    show ((1 : Rˣ) : R) • v.1 = v.1
    simp
  mul_smul u₁ u₂ v := by
    apply Subtype.ext
    show ((u₁ * u₂ : Rˣ) : R) • v.1 = (u₁ : R) • (((u₂ : Rˣ) : R) • v.1)
    funext i
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- A `ProjLineRep`'s underlying vector is never zero (needs `R` nontrivial). -/
lemma ne_zero [Nontrivial R] (v : ProjLineRep R) : v.1 ≠ 0 := by
  intro hv
  obtain ⟨a, b, hab⟩ := v.2
  have h0 : v.1 0 = 0 := by rw [hv, Pi.zero_apply]
  have h1 : v.1 1 = 0 := by rw [hv, Pi.zero_apply]
  rw [h0, h1, mul_zero, mul_zero, add_zero] at hab
  exact zero_ne_one hab

end ProjLineRep

/-- The projective line `P¹(R)`: `ProjLineRep R` modulo scaling by units of `R`. -/
@[reducible] def ProjectiveLine (R : Type*) [CommRing R] : Type _ :=
  Quotient (MulAction.orbitRel Rˣ (ProjLineRep R))

end ProjLineRep

section Bracket

/-- The cross bracket of two (representatives of) points of `P¹(R)`: the 2×2 determinant
`v 0 * w 1 - v 1 * w 0`. Well-defined on representatives; its behaviour under rescaling a
representative or applying a linear map is recorded in `bracket_smul_left`/`_right` and
`bracket_mulVec` below. -/
def bracket (v w : Fin 2 → R) : R := v 0 * w 1 - v 1 * w 0

lemma bracket_antisymm (v w : Fin 2 → R) : bracket w v = -bracket v w := by
  unfold bracket; ring

lemma bracket_smul_left (u : R) (v w : Fin 2 → R) :
    bracket (u • v) w = u * bracket v w := by
  simp only [bracket, Pi.smul_apply, smul_eq_mul]; ring

lemma bracket_smul_right (v : Fin 2 → R) (u : R) (w : Fin 2 → R) :
    bracket v (u • w) = u * bracket v w := by
  simp only [bracket, Pi.smul_apply, smul_eq_mul]; ring

/-- The cross bracket is equivariant under `2×2` matrices up to the determinant:
`⟪Av, Aw⟫ = det(A) * ⟪v, w⟫`. For `A ∈ SL(2,R)` this makes the bracket of images literally equal
to the bracket of the originals (`Matrix.SpecialLinearGroup.det_coe`). -/
lemma bracket_mulVec (A : Matrix (Fin 2) (Fin 2) R) (v w : Fin 2 → R) :
    bracket (A.mulVec v) (A.mulVec w) = A.det * bracket v w := by
  simp only [bracket, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

end Bracket

section SL2Action

/-- `SL(2,R)` acts on `ProjLineRep R` by matrix-vector multiplication: preservation of
`IsCoprime` is `Matrix.SpecialLinearGroup.IsCoprime.mulVecSL`. -/
instance : SMul (Matrix.SpecialLinearGroup (Fin 2) R) (ProjLineRep R) where
  smul A v := ⟨A.1.mulVec v.1, v.2.mulVecSL A⟩

@[simp] lemma ProjLineRep.coe_SL2_smul (A : Matrix.SpecialLinearGroup (Fin 2) R)
    (v : ProjLineRep R) : (A • v).1 = A.1.mulVec v.1 := rfl

instance : MulAction (Matrix.SpecialLinearGroup (Fin 2) R) (ProjLineRep R) where
  one_smul v := by
    apply Subtype.ext
    show (1 : Matrix.SpecialLinearGroup (Fin 2) R).1.mulVec v.1 = v.1
    simp
  mul_smul A B v := by
    apply Subtype.ext
    show ((A * B : Matrix.SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).mulVec v.1
        = A.1.mulVec (B.1.mulVec v.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

/-- The `SL(2,R)` action on representatives commutes with the `Rˣ`-scaling action, so it
descends to the quotient `ProjectiveLine R`. -/
lemma ProjLineRep.SL2_smul_units_smul (A : Matrix.SpecialLinearGroup (Fin 2) R) (u : Rˣ)
    (v : ProjLineRep R) : A • (u • v) = u • (A • v) := by
  apply Subtype.ext
  show A.1.mulVec ((u : R) • v.1) = (u : R) • A.1.mulVec v.1
  rw [Matrix.mulVec_smul]

/-- The induced `SL(2,R)` action on `ProjectiveLine R := ProjLineRep R ⧸ Rˣ`. -/
instance : SMul (Matrix.SpecialLinearGroup (Fin 2) R) (ProjectiveLine R) where
  smul A := Quotient.map (A • ·) (fun v w hvw => by
    obtain ⟨u, hu⟩ := hvw
    exact ⟨u, by rw [← hu, ProjLineRep.SL2_smul_units_smul]⟩)

@[simp] lemma ProjectiveLine.SL2_smul_mk (A : Matrix.SpecialLinearGroup (Fin 2) R)
    (v : ProjLineRep R) :
    A • (Quotient.mk (MulAction.orbitRel Rˣ (ProjLineRep R)) v)
      = Quotient.mk (MulAction.orbitRel Rˣ (ProjLineRep R)) (A • v) := rfl

instance : MulAction (Matrix.SpecialLinearGroup (Fin 2) R) (ProjectiveLine R) where
  one_smul x := by
    induction x using Quotient.ind with
    | _ v => rw [ProjectiveLine.SL2_smul_mk, one_smul]
  mul_smul A B x := by
    induction x using Quotient.ind with
    | _ v => simp only [ProjectiveLine.SL2_smul_mk, mul_smul]

/-- Every central element of `SL(2,R)` is a scalar `r • I` with `r * r = 1`
(`Matrix.SpecialLinearGroup.mem_center_iff`), so acts on a representative `v` by the same `r`
scaled — i.e. by an honest unit of `R` — hence fixes the projective point of `v`. -/
lemma ProjectiveLine.center_smul_eq (z : Matrix.SpecialLinearGroup (Fin 2) R)
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) R)) (x : ProjectiveLine R) :
    z • x = x := by
  induction x using Quotient.ind with
  | _ v =>
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    rw [ProjectiveLine.SL2_smul_mk]
    have hrr : r * r = 1 := by simpa [sq, Fintype.card_fin] using hr
    have hru : IsUnit r := IsUnit.of_mul_eq_one r hrr
    have hzv : (z • v).1 = (hru.unit : R) • v.1 := by
      rw [ProjLineRep.coe_SL2_smul, ← hrz]
      ext i
      fin_cases i <;> simp [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    show Quotient.mk _ (z • v) = Quotient.mk _ v
    rw [Quotient.eq]
    exact ⟨hru.unit, Subtype.ext hzv.symm⟩

/-- The `SL(2,R)`-action on `ProjectiveLine R` descends to the projective symplectic group
`PSL(2,R) := Matrix.ProjectiveSpecialLinearGroup (Fin 2) R`, since the center acts trivially
(`ProjectiveLine.center_smul_eq`). -/
noncomputable instance : MulAction (Matrix.ProjectiveSpecialLinearGroup (Fin 2) R)
    (ProjectiveLine R) :=
  MulAction.compHom (ProjectiveLine R)
    (QuotientGroup.lift _ (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) R)
      (ProjectiveLine R))
      (fun z hz => by
        rw [MonoidHom.mem_ker]
        ext x
        show z • x = x
        exact ProjectiveLine.center_smul_eq z hz x))

end SL2Action

section FieldCompatibility

/-!
### Compatibility with Mathlib's `Projectivization` when `R` is a field

For `F` a field, Mathlib's `Projectivization F (Fin 2 → F)` (defined for any `DivisionRing`) and
this file's from-scratch `ProjectiveLine F` agree: `IsCoprime x y ↔ x ≠ 0 ∨ y ≠ 0` over a field, so
the "generates the unit ideal" and "nonzero" representative conditions coincide, and both quotient
by the same `Fˣ`-scaling relation. This section builds the `SL(2,F)`/`PSL(2,F)`-equivariant
bijection between the two, as a sanity check that the general-`CommRing` construction above
specializes correctly.
-/

variable {F : Type*} [Field F]

lemma isCoprime_iff_ne_zero_or_ne_zero {x y : F} : IsCoprime x y ↔ x ≠ 0 ∨ y ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hx, hy⟩ := hc
    obtain ⟨a, b, hab⟩ := h
    rw [hx, hy, mul_zero, mul_zero, add_zero] at hab
    exact zero_ne_one hab
  · rintro (hx | hy)
    · exact ⟨x⁻¹, 0, by rw [inv_mul_cancel₀ hx, zero_mul, add_zero]⟩
    · exact ⟨0, y⁻¹, by rw [zero_mul, inv_mul_cancel₀ hy, zero_add]⟩

private lemma ne_zero_iff_fin_two {v : Fin 2 → F} : v ≠ 0 ↔ v 0 ≠ 0 ∨ v 1 ≠ 0 := by
  simp only [ne_eq, funext_iff, Fin.forall_fin_two, Pi.zero_apply, not_and_or]

/-- Forward direction of the bijection: forget the "generates the unit ideal" witness in favour
of Mathlib's `Projectivization.mk`. -/
noncomputable def ProjectiveLine.toProjectivization :
    ProjectiveLine F → Projectivization F (Fin 2 → F) :=
  Quotient.lift (fun v : ProjLineRep F => Projectivization.mk F v.1 v.ne_zero)
    (fun v w ⟨u, hu⟩ =>
      (Projectivization.mk_eq_mk_iff' (K := F) v.1 w.1 v.ne_zero w.ne_zero).mpr
        ⟨(u : F), by rw [← hu, ProjLineRep.coe_smul]⟩)

/-- Backward direction, via a canonical (noncomputable) representative. -/
noncomputable def ProjectiveLine.ofProjectivization :
    Projectivization F (Fin 2 → F) → ProjectiveLine F :=
  fun p => Quotient.mk (MulAction.orbitRel Fˣ (ProjLineRep F))
    ⟨p.rep, isCoprime_iff_ne_zero_or_ne_zero.mpr (ne_zero_iff_fin_two.mp p.rep_nonzero)⟩

/-- The two constructions of the projective line over a field agree. -/
noncomputable def ProjectiveLine.equivProjectivization :
    ProjectiveLine F ≃ Projectivization F (Fin 2 → F) where
  toFun := ProjectiveLine.toProjectivization
  invFun := ProjectiveLine.ofProjectivization
  left_inv x := by
    induction x using Quotient.ind with
    | _ v =>
      set p := ProjectiveLine.toProjectivization (Quotient.mk (MulAction.orbitRel Fˣ (ProjLineRep F)) v)
        with hp
      show Quotient.mk (MulAction.orbitRel Fˣ (ProjLineRep F))
          (⟨p.rep, isCoprime_iff_ne_zero_or_ne_zero.mpr (ne_zero_iff_fin_two.mp p.rep_nonzero)⟩ :
            ProjLineRep F)
        = Quotient.mk (MulAction.orbitRel Fˣ (ProjLineRep F)) v
      rw [Quotient.eq]
      have hpv : p = Projectivization.mk F v.1 v.ne_zero := hp
      have hrep : Projectivization.mk F p.rep p.rep_nonzero
          = Projectivization.mk F v.1 v.ne_zero := by rw [Projectivization.mk_rep, hpv]
      rw [Projectivization.mk_eq_mk_iff'] at hrep
      obtain ⟨c, hc⟩ := hrep
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact p.rep_nonzero hc.symm
      exact ⟨Units.mk0 c hc0, Subtype.ext hc⟩
  right_inv p := by
    show ProjectiveLine.toProjectivization
      (Quotient.mk (MulAction.orbitRel Fˣ (ProjLineRep F))
        ⟨p.rep, isCoprime_iff_ne_zero_or_ne_zero.mpr (ne_zero_iff_fin_two.mp p.rep_nonzero)⟩) = p
    show Projectivization.mk F p.rep _ = p
    exact Projectivization.mk_rep p

/-- The bijection intertwines the `SL(2,F)`-actions. -/
lemma ProjectiveLine.equivProjectivization_SL2_smul
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (x : ProjectiveLine F) :
    ProjectiveLine.equivProjectivization (A • x)
      = A • ProjectiveLine.equivProjectivization x := by
  induction x using Quotient.ind with
  | _ v =>
    show ProjectiveLine.toProjectivization (Quotient.mk _ (A • v))
        = A • ProjectiveLine.toProjectivization (Quotient.mk _ v)
    show Projectivization.mk F (A • v).1 _ = A • Projectivization.mk F v.1 v.ne_zero
    rw [Projectivization.matrixSpecialLinearGroup_smul_def, Projectivization.smul_mk]
    rfl

/-- The bijection intertwines the `PSL(2,F)`-actions. -/
lemma ProjectiveLine.equivProjectivization_PSL2_smul
    (A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (x : ProjectiveLine F) :
    ProjectiveLine.equivProjectivization (A • x)
      = A • ProjectiveLine.equivProjectivization x := by
  induction A using QuotientGroup.induction_on with
  | _ A => exact ProjectiveLine.equivProjectivization_SL2_smul A x

/-- The multiplicative map underlying a ring homomorphism from a general commutative ring to a
field. -/
def fieldCoefficientHom {K : Type*} [Field K] (f : R →+* K) : R →*₀ K :=
  f.toMonoidWithZeroHom

/-- An injective field-valued ring homomorphism preserves nonzeroness, as required for scalar
powers of pairwise brackets. -/
lemma fieldCoefficientHom_ne_zero {K : Type*} [Field K] (f : R →+* K)
    (hf : Function.Injective f) {x : R} (hx : x ≠ 0) :
    fieldCoefficientHom f x ≠ 0 := by
  intro h
  apply hx
  apply hf
  simpa [fieldCoefficientHom] using h

end FieldCompatibility

section ScalarExponentCase

/-!
### Scalar exponents via a multiplicative map `R →*₀ S`

The nonzero elements of `S`, viewed additively, form a module over the exponent ring. Scalar
powers are only applied to nonzero elements. Taking the exponent ring to be `ℚ` gives rational
exponents; taking it to be `ℤ` gives integer exponents for any abelian multiplicative group.
-/

variable {S : Type*} [CommGroupWithZero S]
variable {𝕜 : Type*} [CommRing 𝕜] [Module 𝕜 (Additive Sˣ)]

/-- Scalar power of a nonzero element, induced by the module structure on `Sˣ`. -/
noncomputable def scalarPow (x : S) (hx : x ≠ 0) (q : 𝕜) : S :=
  ↑(Additive.toMul (q • Additive.ofMul (Units.mk0 x hx)))

lemma scalarPow_zero (x : S) (hx : x ≠ 0) :
    scalarPow (𝕜 := 𝕜) x hx (0 : 𝕜) = 1 := by
  simp [scalarPow]

lemma scalarPow_add {x : S} (hx : x ≠ 0) (p q : 𝕜) :
    scalarPow x hx (p + q) = scalarPow x hx p * scalarPow x hx q := by
  simp only [scalarPow, add_smul]
  rfl

lemma scalarPow_mul (x y : S) (hx : x ≠ 0) (hy : y ≠ 0) (q : 𝕜) :
    scalarPow (x * y) (mul_ne_zero hx hy) q =
      scalarPow x hx q * scalarPow y hy q := by
  have hu : Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy := by
    ext
    rfl
  simp only [scalarPow, hu]
  have ha : Additive.ofMul (Units.mk0 x hx * Units.mk0 y hy) =
      Additive.ofMul (Units.mk0 x hx) + Additive.ofMul (Units.mk0 y hy) := rfl
  rw [ha, smul_add]
  rfl

variable (habs : R →*₀ S)
variable (habs_ne_zero : ∀ {x : R}, x ≠ 0 → habs x ≠ 0)
variable {n : ℕ} (s : Fin n → Fin n → 𝕜)
variable (hsymm : ∀ i j, s i j = s j i)

/-- `bracket` scaled by a unit in the left slot. -/
lemma bracket_units_smul_left (u : Rˣ) (v w : ProjLineRep R) :
    bracket (u • v).1 w.1 = (u : R) * bracket v.1 w.1 := by
  rw [ProjLineRep.coe_smul, bracket_smul_left]

/-- `bracket` scaled by a unit in the right slot. -/
lemma bracket_units_smul_right (v : ProjLineRep R) (u : Rˣ) (w : ProjLineRep R) :
    bracket v.1 (u • w).1 = (u : R) * bracket v.1 w.1 := by
  rw [ProjLineRep.coe_smul, bracket_smul_right]

private lemma unit_mul_ne_zero (u : Rˣ) {x : R} (hx : x ≠ 0) : (u : R) * x ≠ 0 := by
  intro h
  apply hx
  calc
    x = ((u⁻¹ : Rˣ) : R) * ((u : R) * x) := by simp
    _ = 0 := by rw [h, mul_zero]

/-- A tuple of projective-line representatives with pairwise nonzero brackets. -/
structure ProjLineConfigurationLift (R : Type*) [CommRing R] (n : ℕ) where
  toFun : Fin n → ProjLineRep R
  bracket_ne_zero : ∀ i j, i ≠ j → bracket (toFun i).1 (toFun j).1 ≠ 0

@[ext] lemma ProjLineConfigurationLift.ext
    {P Q : ProjLineConfigurationLift R n} (h : P.toFun = Q.toFun) : P = Q := by
  cases P
  cases Q
  simp_all

instance : CoeFun (ProjLineConfigurationLift R n) (fun _ => Fin n → ProjLineRep R) :=
  ⟨ProjLineConfigurationLift.toFun⟩

/-- Rescaling one representative preserves pairwise nonvanishing of brackets. -/
def ProjLineConfigurationLift.update (P : ProjLineConfigurationLift R n) (k : Fin n) (u : Rˣ) :
    ProjLineConfigurationLift R n where
  toFun := Function.update P.toFun k (u • P k)
  bracket_ne_zero i j hij := by
    by_cases hik : i = k
    · subst i
      rw [Function.update_self, Function.update_of_ne hij.symm, bracket_units_smul_left]
      exact unit_mul_ne_zero u (P.bracket_ne_zero k j hij)
    · by_cases hjk : j = k
      · subst j
        rw [Function.update_of_ne hik, Function.update_self, bracket_units_smul_right]
        exact unit_mul_ne_zero u (P.bracket_ne_zero i k hij)
      · rw [Function.update_of_ne hik, Function.update_of_ne hjk]
        exact P.bracket_ne_zero i j hij

/-- The `SL₂` action preserves pairwise nonvanishing of brackets. -/
def ProjLineConfigurationLift.sl2SMul (A : Matrix.SpecialLinearGroup (Fin 2) R)
    (P : ProjLineConfigurationLift R n) : ProjLineConfigurationLift R n where
  toFun i := A • P i
  bracket_ne_zero i j hij := by
    rw [ProjLineRep.coe_SL2_smul, ProjLineRep.coe_SL2_smul, bracket_mulVec, A.2, one_mul]
    exact P.bracket_ne_zero i j hij

lemma ProjLineConfigurationLift.sl2SMul_update
    (A : Matrix.SpecialLinearGroup (Fin 2) R) (P : ProjLineConfigurationLift R n)
    (k : Fin n) (u : Rˣ) :
    (P.update k u).sl2SMul A = (P.sl2SMul A).update k u := by
  ext i
  by_cases hi : i = k
  · subst i
    simp [ProjLineConfigurationLift.sl2SMul, ProjLineConfigurationLift.update,
      ProjLineRep.SL2_smul_units_smul]
  · simp [ProjLineConfigurationLift.sl2SMul, ProjLineConfigurationLift.update, hi]

/-- The scalar power attached to an off-diagonal pair in a configuration. -/
noncomputable def configurationPow (P : ProjLineConfigurationLift R n)
    (i j : Fin n) (q : 𝕜) : S := by
  classical
  exact if hij : i = j then 1 else
    scalarPow (habs (bracket (P i).1 (P j).1))
      (habs_ne_zero (P.bracket_ne_zero i j hij)) q

/-- The scalar-exponent point-pair product `∏_{i<j} |⟪P i, P j⟫|^{s i j}`. -/
noncomputable def phiProductLift (P : ProjLineConfigurationLift R n) : S :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, configurationPow habs habs_ne_zero P i j (s i j)

/-- Scalar powers turn a finite sum of exponents into a finite product for a nonzero base. -/
lemma scalarPow_sum_eq_prod
    {x : S} (hx : x ≠ 0) {ι : Type*} [DecidableEq ι] (t : Finset ι) (e : ι → 𝕜) :
    scalarPow x hx (∑ i ∈ t, e i) = ∏ i ∈ t, scalarPow x hx (e i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp [scalarPow_zero x hx]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, scalarPow_add hx, ih]

/-- `SL(2,R)` invariance on lifts: the bracket of images under `A ∈ SL(2,R)` is *literally*
equal to the bracket of the originals (`bracket_mulVec`, `A.det = 1`), so `phiProduct` is
unconditionally unchanged — no neutrality hypothesis on `s` is needed for this step. -/
theorem phiProductLift_SL2_smul_eq (A : Matrix.SpecialLinearGroup (Fin 2) R)
    (P : ProjLineConfigurationLift R n) :
    phiProductLift habs habs_ne_zero s (P.sl2SMul A) =
      phiProductLift habs habs_ne_zero s P := by
  unfold phiProductLift
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp [configurationPow, ProjLineConfigurationLift.sl2SMul, ProjLineRep.coe_SL2_smul,
    bracket_mulVec, A.2]

/-- The row-`k` term of `phiProduct` splits off from the rest (`i ≠ k`). -/
lemma phiProduct_eq_row_mul_rest (P : ProjLineConfigurationLift R n) (k : Fin n) :
    phiProductLift habs habs_ne_zero s P =
      (∏ j ∈ Finset.Ioi k, configurationPow habs habs_ne_zero P k j (s k j)) *
        ∏ i ∈ Finset.univ.erase k, ∏ j ∈ Finset.Ioi i,
          configurationPow habs habs_ne_zero P i j (s i j) := by
  exact (Finset.mul_prod_erase Finset.univ
    (fun i => ∏ j ∈ Finset.Ioi i, configurationPow habs habs_ne_zero P i j (s i j))
    (Finset.mem_univ k)).symm

variable [Nontrivial R]

/-- For `i ≠ k`, the `i`-th inner product picks up a correction factor `|u|^{s i k}` exactly when
`i < k` (i.e. `k ∈ Finset.Ioi i`) from rescaling `P k` by `u`, and is otherwise unchanged. -/
private lemma inner_prod_update
    (k : Fin n) (u : Rˣ) (P : ProjLineConfigurationLift R n) (i : Fin n) (hik : i ≠ k) :
    ∏ j ∈ Finset.Ioi i, configurationPow habs habs_ne_zero (P.update k u) i j (s i j)
      = (if i < k then scalarPow (habs (u : R))
          (habs_ne_zero (Units.ne_zero u)) (s i k) else 1) *
        ∏ j ∈ Finset.Ioi i, configurationPow habs habs_ne_zero P i j (s i j) := by
  by_cases hik2 : i < k
  · have hkmem : k ∈ Finset.Ioi i := Finset.mem_Ioi.mpr hik2
    rw [if_pos hik2,
      ← Finset.prod_erase_mul (Finset.Ioi i)
        (fun j => configurationPow habs habs_ne_zero (P.update k u) i j (s i j)) hkmem,
      ← Finset.prod_erase_mul (Finset.Ioi i)
        (fun j => configurationPow habs habs_ne_zero P i j (s i j)) hkmem]
    have herase : ∏ j ∈ (Finset.Ioi i).erase k,
        configurationPow habs habs_ne_zero (P.update k u) i j (s i j)
        = ∏ j ∈ (Finset.Ioi i).erase k,
          configurationPow habs habs_ne_zero P i j (s i j) :=
      Finset.prod_congr rfl fun j hj => by
        have hjk := Finset.ne_of_mem_erase hj
        simp [configurationPow, ProjLineConfigurationLift.update, hik2.ne, hjk]
    have hk : configurationPow habs habs_ne_zero (P.update k u) i k (s i k)
        = scalarPow (habs (u : R)) (habs_ne_zero (Units.ne_zero u)) (s i k) *
          configurationPow habs habs_ne_zero P i k (s i k) := by
      simp only [configurationPow, dif_neg hik2.ne, ProjLineConfigurationLift.update,
        Function.update_of_ne hik2.ne, Function.update_self, bracket_units_smul_right, map_mul]
      apply scalarPow_mul
    rw [herase, hk, mul_left_comm]
  · rw [if_neg hik2]
    have hknotmem : k ∉ Finset.Ioi i := fun h => hik2 (Finset.mem_Ioi.mp h)
    rw [one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := fun h => hknotmem (h ▸ hj)
    simp [configurationPow, ProjLineConfigurationLift.update, hik, hjk]

private lemma Iio_union_Ioi_eq_erase (k : Fin n) :
    Finset.Iio k ∪ Finset.Ioi k = Finset.univ.erase k := by
  ext i
  simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi, Finset.mem_erase, Finset.mem_univ,
    and_true]
  exact ⟨fun h => h.elim (·.ne) (·.ne'), fun h => lt_or_gt_of_ne h⟩

private lemma sum_erase_eq_sum_Iio_add_sum_Ioi (k : Fin n) (e : Fin n → 𝕜) :
    ∑ i ∈ Finset.univ.erase k, e i = (∑ i ∈ Finset.Iio k, e i) + ∑ i ∈ Finset.Ioi k, e i := by
  rw [← Iio_union_Ioi_eq_erase,
    Finset.sum_union (Finset.disjoint_left.mpr fun x hx1 hx2 =>
      lt_asymm (Finset.mem_Iio.mp hx1) (Finset.mem_Ioi.mp hx2))]

/-- Rescaling a single point `P k` by a unit `u` changes `phiProduct` by exactly
`(∏ i ∈ Iio k, |u|^{s k i}) * (∏ j ∈ Ioi k, |u|^{s k j})` — the row-`k` factors change directly
(`hrow`, via `bracket_units_smul_left`), and each `i < k` row's `j = k` entry changes too
(`hrest`, via `inner_prod_update`), reindexed through `hsymm` to `s k i`. -/
theorem phiProduct_update_eq
    (hsymm : ∀ i j, s i j = s j i) (k : Fin n) (u : Rˣ)
    (P : ProjLineConfigurationLift R n) :
    phiProductLift habs habs_ne_zero s (P.update k u)
      = ((∏ i ∈ Finset.Iio k,
          scalarPow (habs (u : R)) (habs_ne_zero (Units.ne_zero u)) (s k i)) *
          ∏ j ∈ Finset.Ioi k,
            scalarPow (habs (u : R)) (habs_ne_zero (Units.ne_zero u)) (s k j)) *
        phiProductLift habs habs_ne_zero s P := by
  rw [phiProduct_eq_row_mul_rest habs habs_ne_zero s (P.update k u) k,
    phiProduct_eq_row_mul_rest habs habs_ne_zero s P k]
  have hrow : ∏ j ∈ Finset.Ioi k,
      configurationPow habs habs_ne_zero (P.update k u) k j (s k j)
      = (∏ j ∈ Finset.Ioi k,
          scalarPow (habs (u : R)) (habs_ne_zero (Units.ne_zero u)) (s k j)) *
        ∏ j ∈ Finset.Ioi k, configurationPow habs habs_ne_zero P k j (s k j) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := (Finset.mem_Ioi.mp hj).ne'
    simp only [configurationPow, dif_neg hjk.symm, ProjLineConfigurationLift.update,
      Function.update_self, Function.update_of_ne hjk, bracket_units_smul_left, map_mul]
    apply scalarPow_mul
  have hrest : ∏ i ∈ Finset.univ.erase k, ∏ j ∈ Finset.Ioi i,
      configurationPow habs habs_ne_zero (P.update k u) i j (s i j)
      = (∏ i ∈ Finset.Iio k,
          scalarPow (habs (u : R)) (habs_ne_zero (Units.ne_zero u)) (s k i)) *
        ∏ i ∈ Finset.univ.erase k, ∏ j ∈ Finset.Ioi i,
          configurationPow habs habs_ne_zero P i j (s i j) := by
    have hstep : ∏ i ∈ Finset.univ.erase k, ∏ j ∈ Finset.Ioi i,
        configurationPow habs habs_ne_zero (P.update k u) i j (s i j)
        = (∏ i ∈ Finset.univ.erase k, if i < k then
            scalarPow (habs (u : R)) (habs_ne_zero (Units.ne_zero u)) (s i k) else 1) *
          ∏ i ∈ Finset.univ.erase k, ∏ j ∈ Finset.Ioi i,
            configurationPow habs habs_ne_zero P i j (s i j) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      exact inner_prod_update habs habs_ne_zero s k u P i (Finset.mem_erase.mp hi).1
    rw [hstep]
    have hfilter : (Finset.univ.erase k).filter (· < k) = Finset.Iio k := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Iio]
      exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
    have hif : ∏ i ∈ Finset.univ.erase k, (if i < k then
        scalarPow (habs (u : R)) (habs_ne_zero (Units.ne_zero u)) (s i k) else (1 : S))
        = ∏ i ∈ Finset.Iio k,
          scalarPow (habs (u : R)) (habs_ne_zero (Units.ne_zero u)) (s k i) := by
      rw [← Finset.prod_filter, hfilter]
      exact Finset.prod_congr rfl fun i _ => by rw [hsymm]
    rw [hif]
  rw [hrow, hrest]
  ac_rfl

include hsymm in
/-- Replacing `P k` by `u • P k` (a different representative of
the same projective point) leaves `phiProduct` unchanged, provided the exponents are "neutral" at
`k` (`∑_{j ≠ k} s k j = 0`). Combined with `phiProductLift_SL2_smul_eq` (1b), this is what makes
`phiProduct`, under the neutrality hypothesis, a genuine `PSL(2,R)`-invariant function of the
*projective points* `Fin n → ProjectiveLine R`, not just of chosen representatives. -/
theorem phiProduct_units_smul_eq
    (k : Fin n)
    (hneutral : ∑ j ∈ Finset.univ.erase k, s k j = 0) (u : Rˣ)
    (P : ProjLineConfigurationLift R n) :
    phiProductLift habs habs_ne_zero s (P.update k u) =
      phiProductLift habs habs_ne_zero s P := by
  have habsu : habs (u : R) ≠ 0 := habs_ne_zero (Units.ne_zero u)
  rw [phiProduct_update_eq habs habs_ne_zero s hsymm k u P,
    ← scalarPow_sum_eq_prod habsu, ← scalarPow_sum_eq_prod habsu,
    ← scalarPow_add habsu, ← sum_erase_eq_sum_Iio_add_sum_Ioi k (s k), hneutral,
    scalarPow_zero _ habsu, one_mul]

/-- Remove the point indexed by `k` from a configuration of lifts. -/
def ProjLineConfigurationLift.erase (P : ProjLineConfigurationLift R (n + 1))
    (k : Fin (n + 1)) : ProjLineConfigurationLift R n where
  toFun i := P (k.succAbove i)
  bracket_ne_zero i j hij :=
    P.bracket_ne_zero (k.succAbove i) (k.succAbove j)
      (fun h => hij (Fin.succAbove_right_injective h))

/-- One elementary change of lift: rescale a single representative by a unit. -/
def ProjLineConfigurationRel (P Q : ProjLineConfigurationLift R n) : Prop :=
  ∃ (k : Fin n) (u : Rˣ), Q = P.update k u

/-- A configuration of projective points, presented independently of any chosen lifts. -/
def ProjLineConfiguration (R : Type*) [CommRing R] (n : ℕ) : Type _ :=
  Quotient (Relation.EqvGen.setoid (ProjLineConfigurationRel (R := R) (n := n)))

/-- The projective configuration represented by a configuration of lifts. -/
def ProjLineConfiguration.mk (P : ProjLineConfigurationLift R n) :
    ProjLineConfiguration R n :=
  Quotient.mk _ P

/-- The `SL₂` action on configurations is independent of all choices of lifts. -/
instance : SMul (Matrix.SpecialLinearGroup (Fin 2) R) (ProjLineConfiguration R n) where
  smul A :=
    Quotient.map (fun P : ProjLineConfigurationLift R n => P.sl2SMul A) (fun P Q h => by
      induction h with
      | rel P₁ P₂ hP₁P₂ =>
          obtain ⟨k, u, rfl⟩ := hP₁P₂
          apply Relation.EqvGen.rel
          exact ⟨k, u, ProjLineConfigurationLift.sl2SMul_update A P₁ k u⟩
      | refl P₁ =>
          show Relation.EqvGen (ProjLineConfigurationRel (R := R) (n := n))
            (P₁.sl2SMul A) (P₁.sl2SMul A)
          exact Relation.EqvGen.refl _
      | symm P₁ P₂ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans P₁ P₂ P₃ _ _ ih₁₂ ih₂₃ => exact Relation.EqvGen.trans _ _ _ ih₁₂ ih₂₃)

omit [Nontrivial R] in
@[simp] lemma ProjLineConfiguration.sl2_smul_mk
    (A : Matrix.SpecialLinearGroup (Fin 2) R) (P : ProjLineConfigurationLift R n) :
    A • ProjLineConfiguration.mk P = ProjLineConfiguration.mk (P.sl2SMul A) := rfl

/-- Remove the point indexed by `k` from a projective configuration. -/
def ProjLineConfiguration.erase (P : ProjLineConfiguration R (n + 1))
    (k : Fin (n + 1)) : ProjLineConfiguration R n :=
  Quotient.map (fun Q : ProjLineConfigurationLift R (n + 1) => Q.erase k) (fun P Q h => by
    induction h with
    | rel P₁ P₂ hP₁P₂ =>
        obtain ⟨l, u, rfl⟩ := hP₁P₂
        by_cases hl : l = k
        · subst l
          have heq : P₁.erase k = (P₁.update k u).erase k := by
            ext i
            simp [ProjLineConfigurationLift.erase, ProjLineConfigurationLift.update,
              Fin.succAbove_ne]
          rw [← heq]
        · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hl
          subst l
          apply Relation.EqvGen.rel
          exact ⟨i, u, by
            apply ProjLineConfigurationLift.ext
            funext j
            exact Function.update_apply_of_injective P₁.toFun
              Fin.succAbove_right_injective i (u • P₁ (k.succAbove i)) j⟩
    | refl P₁ =>
        show Relation.EqvGen (ProjLineConfigurationRel (R := R) (n := n))
          (P₁.erase k) (P₁.erase k)
        exact Relation.EqvGen.refl _
    | symm P₁ P₂ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans P₁ P₂ P₃ _ _ ih₁₂ ih₂₃ => exact Relation.EqvGen.trans _ _ _ ih₁₂ ih₂₃) P

omit [Nontrivial R] in
@[simp] lemma ProjLineConfiguration.erase_mk
    (P : ProjLineConfigurationLift R (n + 1)) (k : Fin (n + 1)) :
    (ProjLineConfiguration.mk P).erase k = ProjLineConfiguration.mk (P.erase k) := rfl

include hsymm in
/-- The point-pair product as a genuine function on projective configurations.

The neutrality assumption at every point makes the value independent of all choices of lifts. -/
noncomputable def phiProduct
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, s k j = 0) :
    ProjLineConfiguration R n → S :=
  Quotient.lift (phiProductLift habs habs_ne_zero s) (fun P Q h => by
    induction h with
    | rel P₁ P₂ hP₁P₂ =>
        obtain ⟨k, u, rfl⟩ := hP₁P₂
        exact
          (phiProduct_units_smul_eq habs habs_ne_zero s hsymm k (hneutral k) u P₁).symm
    | refl P₁ => rfl
    | symm P₁ P₂ _ ih => exact ih.symm
    | trans P₁ P₂ P₃ _ _ ih₁₂ ih₂₃ => exact ih₁₂.trans ih₂₃)

@[simp] lemma phiProduct_mk
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, s k j = 0)
    (P : ProjLineConfigurationLift R n) :
    phiProduct habs habs_ne_zero s hsymm hneutral (ProjLineConfiguration.mk P) =
      phiProductLift habs habs_ne_zero s P := rfl

include hsymm in
/-- The point-pair product on projective configurations is invariant under `SL(2,R)`. -/
theorem phiProduct_SL2_smul_eq
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, s k j = 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) R) (P : ProjLineConfiguration R n) :
    phiProduct habs habs_ne_zero s hsymm hneutral (A • P) =
      phiProduct habs habs_ne_zero s hsymm hneutral P := by
  induction P using Quotient.ind with
  | _ P =>
      change phiProduct habs habs_ne_zero s hsymm hneutral
          (A • ProjLineConfiguration.mk P) =
        phiProduct habs habs_ne_zero s hsymm hneutral (ProjLineConfiguration.mk P)
      rw [ProjLineConfiguration.sl2_smul_mk, phiProduct_mk, phiProduct_mk]
      exact phiProductLift_SL2_smul_eq habs habs_ne_zero s A P

end ScalarExponentCase

section InsertionDeletion

/-!
### Insertion–deletion factorization

The next structural operation is exact factorization under insertion or deletion of a point.  If
`P.erase k` is obtained by deleting the `k`-th lift, then the full product separates into the
product for the remaining configuration and the factors involving `P k`:

`phiProductLift s P =
  phiProductLift (s.erase k) (P.erase k) *
    (∏ i < k, pairPow s P i k) * ∏ j > k, pairPow s P k j`.

Unlike passage to a logarithmic derivative, this identity retains the value of the product.  Its
iteration reconstructs the entire product from successive insertions.

The primary statement belongs at the lift level.  Deleting an exponent row and column does not in
general preserve neutrality, so descent of either factor to `ProjLineConfiguration` requires the
appropriate additional neutrality hypotheses.  The intended API consists of:

* deletion and insertion operations on exponent matrices;
* insertion of a lift whose brackets with all existing lifts are nonzero;
* an interaction product containing exactly the factors incident to the inserted point;
* exact `phiProductLift` insertion and deletion formulas;
* descended formulas when the restricted exponent data remain neutral.
-/

end InsertionDeletion

section ExponentSpecializations

variable {S : Type*} [CommGroupWithZero S]
variable (habs : R →*₀ S) (habs_ne_zero : ∀ {x : R}, x ≠ 0 → habs x ≠ 0)
variable {n : ℕ}

/-- The lift-level product with rational exponents. -/
noncomputable abbrev rationalPhiProductLift [Module ℚ (Additive Sˣ)]
    (sij : Fin n → Fin n → ℚ) : ProjLineConfigurationLift R n → S :=
  phiProductLift habs habs_ne_zero sij

/-- The lift-level product with integer exponents. Every abelian group has its canonical
`ℤ`-module structure, so this requires no divisibility hypothesis on `Sˣ`. -/
noncomputable abbrev integerPhiProductLift
    (nij : Fin n → Fin n → ℤ) : ProjLineConfigurationLift R n → S :=
  phiProductLift habs habs_ne_zero nij

/-- The rational-exponent product on projective configurations. -/
noncomputable abbrev rationalPhiProduct [Nontrivial R] [Module ℚ (Additive Sˣ)]
    (sij : Fin n → Fin n → ℚ) (hsymm : ∀ i j, sij i j = sij j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, sij k j = 0) :
    ProjLineConfiguration R n → S :=
  phiProduct habs habs_ne_zero sij hsymm hneutral

/-- The integer-exponent product on projective configurations. -/
noncomputable abbrev integerPhiProduct [Nontrivial R]
    (nij : Fin n → Fin n → ℤ) (hnymm : ∀ i j, nij i j = nij j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, nij k j = 0) :
    ProjLineConfiguration R n → S :=
  phiProduct habs habs_ne_zero nij hnymm hneutral

end ExponentSpecializations

section FieldCoefficientProducts

variable {K : Type*} [Field K]
variable (f : R →+* K) (hf : Function.Injective f)
variable {𝕜 : Type*} [CommRing 𝕜] [Module 𝕜 (Additive Kˣ)]
variable {n : ℕ}

/-- The lift-level scalar-exponent product associated to an injective ring homomorphism from `R`
to a field `K`. -/
noncomputable abbrev fieldPhiProductLift
    (s : Fin n → Fin n → 𝕜) : ProjLineConfigurationLift R n → K :=
  phiProductLift (fieldCoefficientHom f) (fieldCoefficientHom_ne_zero f hf) s

/-- The scalar-exponent product on projective configurations associated to an injective
field-valued ring homomorphism. -/
noncomputable abbrev fieldPhiProduct [Nontrivial R]
    (s : Fin n → Fin n → 𝕜) (hsymm : ∀ i j, s i j = s j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, s k j = 0) :
    ProjLineConfiguration R n → K :=
  phiProduct (fieldCoefficientHom f) (fieldCoefficientHom_ne_zero f hf) s hsymm hneutral

end FieldCoefficientProducts

section NNRealRationalPowers

/-!
### Rational powers of nonnegative reals

The module structure below identifies rational scalar multiplication on `Additive NNRealˣ` with
the canonical `NNReal.rpow`.  It is independent of the source ring and can therefore be used with
any nonzero-preserving multiplicative map `R →*₀ NNReal`, including algebraic notions of absolute
value that require no topology on `R`.
-/

@[instance_reducible] noncomputable def nnrealUnitsRatSMul :
    SMul ℚ (Additive NNRealˣ) where
  smul q x := Additive.ofMul (Units.mk0 (NNReal.rpow (x.toMul : NNReal) (q : ℝ)) (by
    intro h
    exact x.toMul.ne_zero (NNReal.rpow_eq_zero_iff.mp h).1))

noncomputable instance : SMul ℚ (Additive NNRealˣ) := nnrealUnitsRatSMul

/-- The multiplicative rational action on positive nonnegative reals induced by `NNReal.rpow`. -/
noncomputable instance : MulAction ℚ (Additive NNRealˣ) where
  one_smul x := by
    change @SMul.smul ℚ (Additive NNRealˣ) nnrealUnitsRatSMul 1 x = x
    apply Additive.toMul.injective
    apply Units.ext
    change NNReal.rpow (x.toMul : NNReal) ((1 : ℚ) : ℝ) = x.toMul
    norm_num
  mul_smul q r x := by
    apply Additive.toMul.injective
    apply Units.ext
    change NNReal.rpow (x.toMul : NNReal) ((q * r : ℚ) : ℝ) =
      NNReal.rpow (NNReal.rpow (x.toMul : NNReal) (r : ℝ)) (q : ℝ)
    convert NNReal.rpow_mul (x.toMul : NNReal) (r : ℝ) (q : ℝ) using 1
    · congr 1
      norm_num
      exact mul_comm _ _
    · rfl

noncomputable instance : DistribMulAction ℚ (Additive NNRealˣ) where
  smul_zero q := by
    apply Additive.toMul.injective
    apply Units.ext
    change NNReal.rpow 1 (q : ℝ) = 1
    exact NNReal.one_rpow _
  smul_add q x y := by
      apply Additive.toMul.injective
      apply Units.ext
      dsimp [nnrealUnitsRatSMul]
      exact NNReal.mul_rpow

/-- The rational module structure on positive nonnegative reals induced by `NNReal.rpow`. -/
noncomputable instance : Module ℚ (Additive NNRealˣ) where
  add_smul q r x := by
    apply Additive.toMul.injective
    apply Units.ext
    change NNReal.rpow (x.toMul : NNReal) ((q + r : ℚ) : ℝ) =
      NNReal.rpow (x.toMul : NNReal) (q : ℝ) * NNReal.rpow (x.toMul : NNReal) (r : ℝ)
    convert NNReal.rpow_add x.toMul.ne_zero (q : ℝ) (r : ℝ) using 1 <;> norm_num
  zero_smul x := by
    apply Additive.toMul.injective
    apply Units.ext
    change NNReal.rpow (x.toMul : NNReal) ((0 : ℚ) : ℝ) = 1
    norm_num

end NNRealRationalPowers

section RealComplexInterpretation

/-!
### Real and complex interpretations

This section separates two independent choices: the base field may be `ℝ` or `ℂ`, and the
coefficient map may be the identity or the nonnegative norm. Integer powers are available with
either coefficient map. Rational powers are canonical after applying the norm; without it, roots
in the base field are not uniquely determined and may not define the required rational module
structure on the nonzero elements.

In the literature, *Koba–Nielsen factor* covers several related analytic realizations rather than
one choice in this list. Open-string formulas use powers of differences on an ordered real
configuration (and may equivalently display absolute values there); closed-string formulas use
single-valued combinations involving absolute values; chiral formulas use branch-dependent
holomorphic powers of complex differences. What makes these Koba–Nielsen factors is the additional
string-theoretic exponent data, domain, and branch or single-valuedness prescription. The
general construction in this file covers all of these algebraic choices by varying the base ring
`R`, the coefficient map `habs : R →*₀ S`, the target group-with-zero `S`, and the exponent ring.
The definitions below merely name convenient real and complex instances; they do not introduce a
new construction, and the Koba–Nielsen interpretation does not enter the general proofs.
-/

section RationalPowers

/-!
#### Rational powers through absolute value
-/

private lemma nnnormHom_ne_zero {F : Type*} [NormedDivisionRing F] {x : F} (hx : x ≠ 0) :
    nnnormHom x ≠ 0 := by simpa using hx

/-- The complex absolute-value rational product, obtained by specializing the general product. -/
noncomputable abbrev complexAbsRationalPhiProductLift {n}
    (sij : Fin n → Fin n → ℚ) : ProjLineConfigurationLift ℂ n → NNReal :=
  rationalPhiProductLift (nnnormHom : ℂ →*₀ NNReal) nnnormHom_ne_zero sij

/-- The real absolute-value rational product, obtained by specializing the general product. -/
noncomputable abbrev realAbsRationalPhiProductLift {n}
    (sij : Fin n → Fin n → ℚ) : ProjLineConfigurationLift ℝ n → NNReal :=
  rationalPhiProductLift (nnnormHom : ℝ →*₀ NNReal) nnnormHom_ne_zero sij

/-- The complex absolute-value rational product on projective configurations. -/
noncomputable abbrev complexAbsRationalPhiProduct
    (sij : Fin n → Fin n → ℚ) (hsymm : ∀ i j, sij i j = sij j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, sij k j = 0) :
    ProjLineConfiguration ℂ n → NNReal :=
  rationalPhiProduct (nnnormHom : ℂ →*₀ NNReal) nnnormHom_ne_zero
    sij hsymm hneutral

/-- The real absolute-value rational product on projective configurations. -/
noncomputable abbrev realAbsRationalPhiProduct
    (sij : Fin n → Fin n → ℚ) (hsymm : ∀ i j, sij i j = sij j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, sij k j = 0) :
    ProjLineConfiguration ℝ n → NNReal :=
  rationalPhiProduct (nnnormHom : ℝ →*₀ NNReal) nnnormHom_ne_zero
    sij hsymm hneutral

end RationalPowers

section IntegerPowers

/-!
#### Integer powers in the base field

Integer powers require no choice of roots, so the products retain their real or complex values.
They may also be composed with the nonnegative norm when a norm-valued product is wanted.
-/

/-- The norm-valued complex integer-exponent product. -/
noncomputable abbrev complexAbsIntegerPhiProduct
    (nij : Fin n → Fin n → ℤ) (hnymm : ∀ i j, nij i j = nij j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, nij k j = 0) :
    ProjLineConfiguration ℂ n → NNReal :=
  integerPhiProduct (nnnormHom : ℂ →*₀ NNReal) nnnormHom_ne_zero
    nij hnymm hneutral

/-- The norm-valued real integer-exponent product. -/
noncomputable abbrev realAbsIntegerPhiProduct
    (nij : Fin n → Fin n → ℤ) (hnymm : ∀ i j, nij i j = nij j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, nij k j = 0) :
    ProjLineConfiguration ℝ n → NNReal :=
  integerPhiProduct (nnnormHom : ℝ →*₀ NNReal) nnnormHom_ne_zero
    nij hnymm hneutral

/-- The norm-valued complex lift-level integer-exponent product. -/
noncomputable abbrev complexAbsIntegerPhiProductLift
    (nij : Fin n → Fin n → ℤ) : ProjLineConfigurationLift ℂ n → NNReal :=
  integerPhiProductLift (nnnormHom : ℂ →*₀ NNReal) nnnormHom_ne_zero nij

/-- The norm-valued real lift-level integer-exponent product. -/
noncomputable abbrev realAbsIntegerPhiProductLift
    (nij : Fin n → Fin n → ℤ) : ProjLineConfigurationLift ℝ n → NNReal :=
  integerPhiProductLift (nnnormHom : ℝ →*₀ NNReal) nnnormHom_ne_zero nij

/-- The complex-valued integer-exponent product. -/
noncomputable abbrev complexIntegerPhiProduct
    (nij : Fin n → Fin n → ℤ) (hnymm : ∀ i j, nij i j = nij j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, nij k j = 0) :
    ProjLineConfiguration ℂ n → ℂ :=
  fieldPhiProduct (RingHom.id ℂ) Function.injective_id nij hnymm hneutral

/-- The complex-valued lift-level integer-exponent product. -/
noncomputable abbrev complexIntegerPhiProductLift
    (nij : Fin n → Fin n → ℤ) : ProjLineConfigurationLift ℂ n → ℂ :=
  fieldPhiProductLift (RingHom.id ℂ) Function.injective_id nij

/-- The real-valued integer-exponent product. -/
noncomputable abbrev realIntegerPhiProduct
    (nij : Fin n → Fin n → ℤ) (hnymm : ∀ i j, nij i j = nij j i)
    (hneutral : ∀ k : Fin n, ∑ j ∈ Finset.univ.erase k, nij k j = 0) :
    ProjLineConfiguration ℝ n → ℝ :=
  fieldPhiProduct (RingHom.id ℝ) Function.injective_id nij hnymm hneutral

/-- The real-valued lift-level integer-exponent product. -/
noncomputable abbrev realIntegerPhiProductLift
    (nij : Fin n → Fin n → ℤ) : ProjLineConfigurationLift ℝ n → ℝ :=
  fieldPhiProductLift (RingHom.id ℝ) Function.injective_id nij

end IntegerPowers

end RealComplexInterpretation
