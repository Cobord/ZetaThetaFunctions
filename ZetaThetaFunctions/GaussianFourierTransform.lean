import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import ZetaThetaFunctions.SchurPivot
import ZetaThetaFunctions.SiegelUpperHalfSpace

/-!
# The continuous Gaussian Fourier transform

Pure continuous analysis: the Gaussian `modulatedGaussian` on `EuclideanSpace ℝ (Fin g)`, its
integrability (`modulatedGaussian_integrable`, fully proved via domination by an isotropic
Gaussian), and its Bochner Fourier transform.
-/

open Complex
open scoped Real FourierTransform RealInnerProductSpace

variable {g : ℕ}

/-- Peel the last coordinate off an integral over `EuclideanSpace ℝ (Fin (g+1))`, turning it into
an iterated integral over `EuclideanSpace ℝ (Fin g)` (outer) and `ℝ` (inner), via
`MeasurableEquiv.piFinSuccAbove` at `Fin.last g` (a *measure*-preserving coordinate split — no
metric isometry needed, since this is purely about substitution + Fubini in `𝓕`'s defining
integral). `Fin.insertNth_last` identifies `piFinSuccAbove.symm` with `Fin.snoc`. The `ℝ`
coordinate is kept innermost so the induction can integrate it out via `integral_cexp_quadratic`
before recursing into the `EuclideanSpace ℝ (Fin g)` factor via the induction hypothesis. -/
private lemma integral_euclideanSpace_succ (F : EuclideanSpace ℝ (Fin (g + 1)) → ℂ)
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × (Fin g → ℝ) => F (WithLp.toLp 2 (Fin.snoc p.2 p.1 : Fin (g + 1) → ℝ)))) :
    ∫ v : EuclideanSpace ℝ (Fin (g + 1)), F v =
      ∫ y : EuclideanSpace ℝ (Fin g), ∫ t : ℝ,
        F (WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) t : Fin (g + 1) → ℝ)) := by
  have step1 : ∫ v : EuclideanSpace ℝ (Fin (g + 1)), F v =
      ∫ x : Fin (g + 1) → ℝ, F (WithLp.toLp 2 x) := by
    rw [(PiLp.volume_preserving_toLp (Fin (g + 1))).integral_comp
      (MeasurableEquiv.toLp 2 (Fin (g + 1) → ℝ)).measurableEmbedding F]
  have hsymm : ∀ p : ℝ × (Fin g → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (g + 1) => ℝ) (Fin.last g)).symm p =
        (Fin.snoc p.2 p.1 : Fin (g + 1) → ℝ) := by
    intro ⟨t, y⟩
    show (Fin.last g).insertNth t y = (Fin.snoc y t : Fin (g + 1) → ℝ)
    simp
  have step2 : ∫ x : Fin (g + 1) → ℝ, F (WithLp.toLp 2 x) =
      ∫ p : ℝ × (Fin g → ℝ), F (WithLp.toLp 2 (Fin.snoc p.2 p.1 : Fin (g + 1) → ℝ)) := by
    have h := (MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (g + 1) => ℝ) (Fin.last g)).integral_comp'
      (fun p : ℝ × (Fin g → ℝ) => F (WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (g + 1) => ℝ) (Fin.last g)).symm p)))
    simp only [MeasurableEquiv.symm_apply_apply] at h
    rw [h]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun p => by simp only [hsymm])
  have step3 : ∫ p : ℝ × (Fin g → ℝ), F (WithLp.toLp 2 (Fin.snoc p.2 p.1 : Fin (g + 1) → ℝ)) =
      ∫ y : Fin g → ℝ, ∫ t : ℝ, F (WithLp.toLp 2 (Fin.snoc y t : Fin (g + 1) → ℝ)) := by
    rw [show (MeasureTheory.volume : MeasureTheory.Measure (ℝ × (Fin g → ℝ))) =
      MeasureTheory.volume.prod MeasureTheory.volume from
      MeasureTheory.Measure.volume_eq_prod ℝ (Fin g → ℝ)] at hF
    exact MeasureTheory.integral_prod_symm _ hF
  have step4 : ∫ y : Fin g → ℝ, ∫ t : ℝ, F (WithLp.toLp 2 (Fin.snoc y t : Fin (g + 1) → ℝ)) =
      ∫ y : EuclideanSpace ℝ (Fin g), ∫ t : ℝ,
        F (WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) t : Fin (g + 1) → ℝ)) := by
    rw [(PiLp.volume_preserving_toLp (Fin g)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin g → ℝ)).measurableEmbedding
      (fun y : EuclideanSpace ℝ (Fin g) => ∫ t : ℝ,
        F (WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) t : Fin (g + 1) → ℝ)))]
  rw [step1, step2, step3, step4]

/-- Transfers integrability of `F` across the same coordinate split used by
`integral_euclideanSpace_succ`, via `MeasurePreserving.integrable_comp_of_integrable` applied to
the composite of `PiLp.volume_preserving_toLp` and `MeasureTheory.volume_preserving_piFinSuccAbove`
(needed to justify Fubini, i.e. the `hF` hypothesis of `integral_euclideanSpace_succ` itself). -/
private lemma integrable_euclideanSpace_succ (F : EuclideanSpace ℝ (Fin (g + 1)) → ℂ)
    (hF : MeasureTheory.Integrable F) :
    MeasureTheory.Integrable
      (fun p : ℝ × (Fin g → ℝ) => F (WithLp.toLp 2 (Fin.snoc p.2 p.1 : Fin (g + 1) → ℝ))) := by
  have hg1 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (g + 1) => ℝ) (Fin.last g)).symm
      MeasureTheory.volume MeasureTheory.volume :=
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (g + 1) => ℝ) (Fin.last g)).symm
  have hg2 : MeasureTheory.MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (g + 1) → ℝ))
      MeasureTheory.volume MeasureTheory.volume := PiLp.volume_preserving_toLp (Fin (g + 1))
  have hcomb := hg1.trans hg2
  have hint := hcomb.integrable_comp_of_integrable hF
  refine hint.congr (Filter.Eventually.of_forall fun p => ?_)
  have hsymm : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (g + 1) => ℝ) (Fin.last g)).symm p =
      (Fin.snoc p.2 p.1 : Fin (g + 1) → ℝ) := by
    show (Fin.last g).insertNth p.1 p.2 = (Fin.snoc p.2 p.1 : Fin (g + 1) → ℝ)
    simp
  show F ((MeasurableEquiv.toLp 2 (Fin (g + 1) → ℝ))
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (g + 1) => ℝ) (Fin.last g)).symm p)) = _
  rw [hsymm]
  rfl

/-- Splitting the rank-`(n+1)` quadratic form's exponent along `x = Fin.snoc y t`, for a real
`(y, t)` pair (the continuous analog of `PoissonSummation.lean`'s `quadratic_exponent_split`,
lattice-free since `y i`/`t` are real, not integers). Pure algebra. -/
private lemma quadratic_split_real {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsSymm) (y : Fin n → ℝ) (t : ℝ) :
    ∑ i, ∑ j, A i j * ((Fin.snoc y t : Fin (n + 1) → ℝ) i : ℂ) *
        ((Fin.snoc y t : Fin (n + 1) → ℝ) j : ℂ) =
      (∑ i, ∑ j, A i.castSucc j.castSucc * (y i : ℂ) * (y j : ℂ)) +
        2 * (t : ℂ) * (∑ i, A i.castSucc (Fin.last n) * (y i : ℂ)) +
        A (Fin.last n) (Fin.last n) * (t : ℂ) ^ 2 := by
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have hsymm : ∀ j : Fin n, A (Fin.last n) j.castSucc = A j.castSucc (Fin.last n) :=
    fun j => hA.apply j.castSucc (Fin.last n)
  simp only [hsymm, Finset.sum_add_distrib]
  have hL1 : ∑ x : Fin n, A x.castSucc (Fin.last n) * (y x : ℂ) * (t : ℂ)
      = (t : ℂ) * ∑ x : Fin n, A x.castSucc (Fin.last n) * (y x : ℂ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  have hL2 : ∑ x : Fin n, A x.castSucc (Fin.last n) * (t : ℂ) * (y x : ℂ)
      = (t : ℂ) * ∑ x : Fin n, A x.castSucc (Fin.last n) * (y x : ℂ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  rw [hL1, hL2]
  ring

/-- Splitting the rank-`(n+1)` linear shift term along `x = Fin.snoc y t`. Pure algebra. -/
private lemma linear_split_real {n : ℕ} (b : Fin (n + 1) → ℂ) (y : Fin n → ℝ) (t : ℝ) :
    ∑ i, b i * ((Fin.snoc y t : Fin (n + 1) → ℝ) i : ℂ) =
      (∑ i, b i.castSucc * (y i : ℂ)) + b (Fin.last n) * (t : ℂ) := by
  simp [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The pivot factor produced by `integral_cexp_quadratic`'s `(π / -b)^(1/2)` matches
`pivotSqrt`'s `1 / a ^ (1/2)` convention: for `0 < a.re`, `(π / (π * a)) ^ (1/2) = 1 / a ^ (1/2)`.
Same branch-safety argument as `fourier_gaussian_pi'` (Mathlib): `a.re > 0` rules out `a` lying on
the `cpow` branch cut. -/
private lemma pi_div_pi_mul_cpow_half {a : ℂ} (ha : 0 < a.re) :
    ((π : ℂ) / ((π : ℂ) * a)) ^ (1 / 2 : ℂ) = 1 / a ^ (1 / 2 : ℂ) := by
  rw [← div_div, div_self (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_div,
    Complex.inv_cpow, ← one_div]
  rw [Ne, Complex.arg_eq_pi_iff, not_and_or, not_lt]
  exact Or.inl ha.le

/-- The Gaussian on `EuclideanSpace ℝ (Fin g)` with covariance `A` and phase/shift `b`, matching
the exponent `tsum_exp_neg_quadratic_matrix` resums over the lattice `ℤ^g`. -/
noncomputable def modulatedGaussian (A : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ)
    (x : EuclideanSpace ℝ (Fin g)) : ℂ :=
  exp (-π * ∑ i, ∑ j, A i j * (x.ofLp i : ℂ) * (x.ofLp j : ℂ) +
    2 * π * ∑ i, b i * (x.ofLp i : ℂ))

/-- `modulatedGaussian`, parametrized by a real center in `x`-space *and* a real center in
`ξ`-space instead of the raw complex shift `b`.

`center` is the location where the *real* Gaussian envelope `|modulatedGaussian A b|` peaks,
recovered via `Re(b) = (Re A) • center` (completing the square in
`-π xᵀ(Re A)x + 2π (Re b)·x`).

`centerXi` is where `𝓕 (modulatedGaussian A b)` peaks in `ξ`-space -/
noncomputable def modulatedGaussianCenter (A : Matrix (Fin g) (Fin g) ℂ)
    (center centerXi : EuclideanSpace ℝ (Fin g)) : EuclideanSpace ℝ (Fin g) → ℂ :=
  modulatedGaussian A (fun i => ((A.map Complex.re).mulVec (WithLp.ofLp center) i : ℂ) +
    I * (WithLp.ofLp centerXi i))

/-- `modulatedGaussian A b` is integrable: it is dominated by a constant times the isotropic
Gaussian `exp(-(π c / 2) ‖x‖²)`, where `c` is `Q := quadraticMapOfMatrix (2 • Re A)`'s
`posDef_lower_bound` decay rate. The linear shift term is absorbed via a per-coordinate AM-GM
("complete the square") estimate, halving the quadratic decay rate to make room for it. -/
lemma modulatedGaussian_integrable (hg : g ≠ 0) (A : Matrix (Fin g) (Fin g) ℂ)
    (hRe : (A.map Complex.re).PosDef) (b : Fin g → ℂ) :
    MeasureTheory.Integrable (modulatedGaussian A b) := by
  set Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ :=
    quadraticMapOfMatrix ((2 : ℝ) • (A.map Complex.re)) with hQ_def
  have hQPosDef : Q.PosDef := quadraticMapOfMatrix_posDef hRe
  obtain ⟨c, hc_pos, hc⟩ := posDef_lower_bound hg Q (quadraticMapOfMatrix_continuous _) hQPosDef
  have hcne : c ≠ 0 := hc_pos.ne'
  have hQ_eq : ∀ x : EuclideanSpace ℝ (Fin g),
      Q x = ∑ i, ∑ j, (A.map Complex.re) i j * x i * x j := by
    intro x
    rw [hQ_def, quadraticMapOfMatrix_apply]
    have h2 : (⅟(2 : ℝ)) = (2 : ℝ)⁻¹ := invOf_eq_inv 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self_apply, h2]
    ring
  set w : Fin g → ℝ := fun i => (b i).re with hw_def
  have hterm : ∀ (i : Fin g) (x : EuclideanSpace ℝ (Fin g)),
      2 * π * (w i * x i) ≤ (π * c / 2) * (x i) ^ 2 + (2 * π / c) * (w i) ^ 2 := by
    intro i x
    have hs1 : Real.sqrt (π * c / 2) ^ 2 = π * c / 2 := Real.sq_sqrt (by positivity)
    have hs2 : Real.sqrt (2 * π / c) ^ 2 = 2 * π / c := Real.sq_sqrt (by positivity)
    have hprod : Real.sqrt (π * c / 2) * Real.sqrt (2 * π / c) = π := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show π * c / 2 * (2 * π / c) = π ^ 2 by field_simp]
      exact Real.sqrt_sq Real.pi_pos.le
    have hsq : (0 : ℝ) ≤ (Real.sqrt (π * c / 2) * x i - Real.sqrt (2 * π / c) * w i) ^ 2 :=
      sq_nonneg _
    have hexpand : (Real.sqrt (π * c / 2) * x i - Real.sqrt (2 * π / c) * w i) ^ 2 =
        (π * c / 2) * (x i) ^ 2 - 2 * π * (x i * w i) + (2 * π / c) * (w i) ^ 2 := by
      have hring : (Real.sqrt (π * c / 2) * x i - Real.sqrt (2 * π / c) * w i) ^ 2 =
          Real.sqrt (π * c / 2) ^ 2 * (x i) ^ 2 -
            2 * (Real.sqrt (π * c / 2) * Real.sqrt (2 * π / c)) * (x i * w i) +
            Real.sqrt (2 * π / c) ^ 2 * (w i) ^ 2 := by ring
      rw [hring, hs1, hs2, hprod]
    rw [hexpand] at hsq
    nlinarith [hsq]
  have hlin_bound : ∀ x : EuclideanSpace ℝ (Fin g),
      2 * π * ∑ i, w i * x i ≤ (π * c / 2) * ‖x‖ ^ 2 + (2 * π / c) * ∑ i, (w i) ^ 2 := by
    intro x
    calc 2 * π * ∑ i, w i * x i = ∑ i, 2 * π * (w i * x i) := by rw [Finset.mul_sum]
      _ ≤ ∑ i, ((π * c / 2) * (x i) ^ 2 + (2 * π / c) * (w i) ^ 2) :=
          Finset.sum_le_sum fun i _ => hterm i x
      _ = (π * c / 2) * ∑ i, (x i) ^ 2 + (2 * π / c) * ∑ i, (w i) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = (π * c / 2) * ‖x‖ ^ 2 + (2 * π / c) * ∑ i, (w i) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          congr 2
          exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  set K : ℝ := (2 * π / c) * ∑ i, (w i) ^ 2 with hK_def
  have hnorm_eq : ∀ x : EuclideanSpace ℝ (Fin g),
      ‖modulatedGaussian A b x‖ = Real.exp (-π * Q x + 2 * π * ∑ i, w i * x i) := by
    intro x
    rw [modulatedGaussian, Complex.norm_exp]
    congr 1
    rw [hQ_eq]
    simp [Complex.re_sum, Matrix.map_apply]
    unfold w
    rfl
  have hbound : ∀ x : EuclideanSpace ℝ (Fin g),
      ‖modulatedGaussian A b x‖ ≤ Real.exp K * Real.exp (-(π * c / 2) * ‖x‖ ^ 2) := by
    intro x
    rw [hnorm_eq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := hlin_bound x
    have h2 : π * c * ‖x‖ ^ 2 ≤ π * Q x := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hc x) Real.pi_pos.le
    linarith [h1, h2]
  have hCont : Continuous (modulatedGaussian A b) := by
    unfold modulatedGaussian
    fun_prop
  have hb_pos : (0 : ℝ) < (((π * c / 2 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; positivity
  have hgauss_int := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin g)) hb_pos (0 : ℂ) (0 : EuclideanSpace ℝ (Fin g))
  simp only [zero_mul, add_zero] at hgauss_int
  refine MeasureTheory.Integrable.mono' ((hgauss_int.norm).const_mul (Real.exp K))
    hCont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Complex.norm_exp]
  have hre : (-(((π * c / 2 : ℝ) : ℂ)) * (‖x‖ : ℂ) ^ 2).re = -(π * c / 2) * ‖x‖ ^ 2 := by
    rw [show (-(((π * c / 2 : ℝ) : ℂ)) * (‖x‖ : ℂ) ^ 2) =
        ((-(π * c / 2) * ‖x‖ ^ 2 : ℝ) : ℂ) from by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hre]
  exact hbound x

/-- The oscillatory Fourier kernel `𝐞(-⟪v,ξ⟫)` absorbs directly into `modulatedGaussian`'s shift:
`-2πi⟪v,ξ⟫ = 2π∑(-iξ_i)v_i`, so the Fourier transform of a Gaussian is literally the *bare
integral* of another Gaussian with shift `b - iξ`. This is what turns the Fourier-transform
computation into the same kind of "peel off a coordinate, complete the square" induction already
used for the discrete sum, without needing `Real.fourier_eq` at every step of the induction. -/
private lemma fourier_modulatedGaussian_eq_integral (A : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ)
    (ξ : EuclideanSpace ℝ (Fin g)) :
    𝓕 (modulatedGaussian A b) ξ =
      ∫ v : EuclideanSpace ℝ (Fin g),
        modulatedGaussian A (fun i => b i - I * (ξ.ofLp i : ℂ)) v := by
  rw [Real.fourier_eq']
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [modulatedGaussian, smul_eq_mul, ← Complex.exp_add]
  congr 1
  have hip : (⟪v, ξ⟫ : ℝ) = ∑ i, (ξ.ofLp i) * (v.ofLp i) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  have hrhs : 2 * (π : ℂ) * ∑ x, (b x - I * (ξ.ofLp x : ℂ)) * (v.ofLp x : ℂ) =
      2 * π * ∑ x, b x * (v.ofLp x : ℂ) - 2 * π * I * ∑ x, (ξ.ofLp x : ℂ) * (v.ofLp x : ℂ) := by
    have step : ∀ x : Fin g, 2 * (π : ℂ) * ((b x - I * (ξ.ofLp x : ℂ)) * (v.ofLp x : ℂ)) =
        2 * π * (b x * (v.ofLp x : ℂ)) - 2 * π * I * ((ξ.ofLp x : ℂ) * (v.ofLp x : ℂ)) :=
      fun x => by ring
    rw [Finset.mul_sum]
    simp_rw [step]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hrhs, hip]
  push_cast
  ring

/-- The Bochner Fourier transform (`Mathlib.Analysis.Fourier.FourierTransform`) of
`modulatedGaussian A b` is the classical Gaussian-Fourier dual formula
`1 / pivotSqrt g A * exp(-π ∑∑ A⁻¹ (ξ + I b) (ξ + I b))`, matching `fourier_gaussian_pi'`'s
scalar `g = 1` case (`Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`) exactly when
specialized to `g = 1`. -/
lemma modulatedGaussian_fourierTransform (hg : g ≠ 0) (A : Matrix (Fin g) (Fin g) ℂ)
    (hA : A.IsSymm) (hRe : (A.map Complex.re).PosDef) (b : Fin g → ℂ) :
    ∀ ξ : EuclideanSpace ℝ (Fin g), 𝓕 (modulatedGaussian A b) ξ =
      1 / pivotSqrt g A * exp (-π * ∑ i, ∑ j,
        A⁻¹ i j * ((ξ.ofLp i : ℂ) + I * b i) * ((ξ.ofLp j : ℂ) + I * b j)) := by
  obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hg
  clear hg
  induction g with
  | zero =>
    intro ξ
    set A00 : ℂ := A 0 0 with hA00
    set b0 : ℂ := b 0 with hb0
    rw [fourier_modulatedGaussian_eq_integral]
    change (∫ v : EuclideanSpace ℝ (Fin 1),
      modulatedGaussian A (fun i => b i - I * (ξ.ofLp i : ℂ)) v) = _
    have step1 : (∫ v : EuclideanSpace ℝ (Fin 1),
        modulatedGaussian A (fun i => b i - I * (ξ.ofLp i : ℂ)) v) =
        ∫ x : Fin 1 → ℝ, modulatedGaussian A (fun i => b i - I * (ξ.ofLp i : ℂ))
          (WithLp.toLp 2 x) := by
      rw [(PiLp.volume_preserving_toLp (Fin 1)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurableEmbedding
        (fun v : EuclideanSpace ℝ (Fin 1) =>
          modulatedGaussian A (fun i => b i - I * (ξ.ofLp i : ℂ)) v)]
    rw [step1]
    have step2 : (∫ x : Fin 1 → ℝ,
        modulatedGaussian A (fun i => b i - I * (ξ.ofLp i : ℂ)) (WithLp.toLp 2 x)) =
        ∫ t : ℝ, modulatedGaussian A (fun i => b i - I * (ξ.ofLp i : ℂ))
          (WithLp.toLp 2 ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm t)) := by
      exact (((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm).integral_comp
        (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
        (fun x : Fin 1 → ℝ => modulatedGaussian A
          (fun i => b i - I * (ξ.ofLp i : ℂ)) (WithLp.toLp 2 x))).symm
    rw [step2]
    have hA00_pos : 0 < A00.re := by
      rw [hA00]
      exact hRe.diag_pos
    have step3 : (∫ t : ℝ, modulatedGaussian A
        (fun i => b i - I * (ξ.ofLp i : ℂ))
        (WithLp.toLp 2 ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm t))) =
        ∫ t : ℝ, exp (- (π * A00 * (t : ℂ) ^ 2) +
          2 * π * (b0 - I * (ξ.ofLp 0 : ℂ)) * (t : ℂ)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [modulatedGaussian, Fin.sum_univ_one]
      congr 1
      simp [hA00, hb0]
      ring
    rw [step3]
    have hscalar := congrFun (fourier_gaussian_pi' hA00_pos
      (b0 - I * (ξ.ofLp 0 : ℂ))) 0
    rw [Real.fourier_eq'] at hscalar
    simp at hscalar
    refine hscalar.trans ?_
    have hpivot : pivotSqrt 1 A = A00 ^ (1 / 2 : ℂ) := by
      change A 0 0 ^ (1 / 2 : ℂ) * 1 = A00 ^ (1 / 2 : ℂ)
      rw [← hA00, mul_one]
    have hinv : A⁻¹ 0 0 = A00⁻¹ := by
      rw [Matrix.inv_subsingleton]
      simp [Ring.inverse_eq_inv, ← hA00]
    simp only [Fin.sum_univ_one]
    rw [hpivot, hinv, ← hb0]
    simp only [one_div]
    congr 1
    apply congrArg exp
    have hi : I * (b0 - I * (ξ.ofLp 0 : ℂ)) = (ξ.ofLp 0 : ℂ) + I * b0 := by
      rw [mul_sub, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [hi]
    simp only [div_eq_mul_inv]
    ring
  | succ g ih =>
    intro ξ
    set bshift : Fin (g + 1 + 1) → ℂ := fun i => b i - I * (ξ.ofLp i : ℂ) with hbshift_def
    rw [fourier_modulatedGaussian_eq_integral]
    change (∫ v : EuclideanSpace ℝ (Fin (g + 1 + 1)), modulatedGaussian A bshift v) = _
    set a : ℂ := A (Fin.last (g + 1)) (Fin.last (g + 1)) with ha_def
    have hpivotRe : 0 < a.re := hRe.diag_pos
    have hpivot : a ≠ 0 := fun h => by simp [h] at hpivotRe
    have hA' : (schurStepLast A).IsSymm := schurStepLast_isSymm hA
    have hRe' : ((schurStepLast A).map Complex.re).PosDef := schurStepLast_re_posDef hA hRe
    have hA''ne : (schurStepLast A).det ≠ 0 := by
      intro h
      apply pivotSqrt_ne_zero (g + 1) (schurStepLast A) hA' hRe'
      have hsq := pivotSqrt_sq (g + 1) (schurStepLast A) hA' hRe'
      rw [h] at hsq
      exact pow_eq_zero_iff two_ne_zero |>.mp hsq
    have hFint : MeasureTheory.Integrable (modulatedGaussian A bshift) :=
      modulatedGaussian_integrable (Nat.succ_ne_zero (g + 1)) A hRe bshift
    have hF : MeasureTheory.Integrable
        (fun p : ℝ × (Fin (g + 1) → ℝ) => modulatedGaussian A bshift
          (WithLp.toLp 2 (Fin.snoc p.2 p.1 : Fin (g + 1 + 1) → ℝ))) :=
      integrable_euclideanSpace_succ (modulatedGaussian A bshift) hFint
    rw [integral_euclideanSpace_succ (modulatedGaussian A bshift) hF]
    set bshiftLast : ℂ := bshift (Fin.last (g + 1)) with hbshiftLast_def
    set w : Fin (g + 1) → ℂ := fun i => A i.castSucc (Fin.last (g + 1)) with hw_def
    set bY : Fin (g + 1) → ℂ := fun i => bshift i.castSucc - bshiftLast * w i / a with hbY_def
    have hcomplete_square : ∀ yc : Fin (g + 1) → ℂ,
        (-(π : ℂ) * (∑ i, ∑ j, A i.castSucc j.castSucc * yc i * yc j) +
          2 * (π : ℂ) * ∑ i, bshift i.castSucc * yc i) +
          (π : ℂ) * (bshiftLast - ∑ i, w i * yc i) ^ 2 / a =
        (-(π : ℂ) * ∑ i, ∑ j, (schurStepLast A) i j * yc i * yc j +
          2 * (π : ℂ) * ∑ i, bY i * yc i) + (π : ℂ) * bshiftLast ^ 2 / a := by
      intro yc
      rw [schurStepLast_quadratic_eq hA yc, ← ha_def]
      have hbY_sum : ∑ i, bY i * yc i =
          (∑ i, bshift i.castSucc * yc i) - bshiftLast / a * ∑ i, w i * yc i := by
        have hterm : ∀ i, bY i * yc i = bshift i.castSucc * yc i - bshiftLast / a * (w i * yc i) := by
          intro i
          simp only [hbY_def]
          ring
        simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hbY_sum]
      field_simp
      ring
    have hinner : ∀ y : EuclideanSpace ℝ (Fin (g + 1)),
        (∫ t : ℝ, modulatedGaussian A bshift
          (WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) t : Fin (g + 1 + 1) → ℝ))) =
        1 / a ^ (1 / 2 : ℂ) * exp (π * bshiftLast ^ 2 / a) *
          modulatedGaussian (schurStepLast A) bY y := by
      intro y
      have hb2 : (-(π : ℂ) * a).re < 0 := by
        simpa only [neg_mul, neg_re, re_ofReal_mul, neg_lt_zero] using mul_pos Real.pi_pos hpivotRe
      have hpt : (fun t : ℝ => modulatedGaussian A bshift
          (WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) t : Fin (g + 1 + 1) → ℝ))) =
          (fun t : ℝ => cexp ((-(π : ℂ) * a) * (t : ℂ) ^ 2 +
            (2 * (π : ℂ) * (bshiftLast - ∑ i, w i * (WithLp.ofLp y i : ℂ))) * (t : ℂ) +
            (-(π : ℂ) * (∑ i, ∑ j, A i.castSucc j.castSucc * (WithLp.ofLp y i : ℂ) *
                (WithLp.ofLp y j : ℂ)) +
              2 * (π : ℂ) * ∑ i, bshift i.castSucc * (WithLp.ofLp y i : ℂ)))) := by
        funext t
        unfold modulatedGaussian
        rw [quadratic_split_real hA (WithLp.ofLp y) t, linear_split_real bshift (WithLp.ofLp y) t]
        congr 1
        ring
      rw [hpt, integral_cexp_quadratic hb2,
        show -(-(π : ℂ) * a) = (π : ℂ) * a from by ring, pi_div_pi_mul_cpow_half hpivotRe]
      have hRHS : modulatedGaussian (schurStepLast A) bY y =
          cexp (-(π : ℂ) * ∑ i, ∑ j, (schurStepLast A) i j * (WithLp.ofLp y i : ℂ) *
              (WithLp.ofLp y j : ℂ) +
            2 * (π : ℂ) * ∑ i, bY i * (WithLp.ofLp y i : ℂ)) := rfl
      rw [hRHS]
      conv_rhs => rw [mul_assoc, ← Complex.exp_add]
      congr 1
      congr 1
      have hC2 : (2 * (π : ℂ) * (bshiftLast - ∑ i, w i * (WithLp.ofLp y i : ℂ))) ^ 2 /
          (4 * (-(π : ℂ) * a)) =
          -(π : ℂ) * (bshiftLast - ∑ i, w i * (WithLp.ofLp y i : ℂ)) ^ 2 / a := by
        field_simp
        ring
      linear_combination hcomplete_square (fun i => (WithLp.ofLp y i : ℂ)) - hC2
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)]
    rw [MeasureTheory.integral_const_mul]
    have hYint : (∫ y : EuclideanSpace ℝ (Fin (g + 1)), modulatedGaussian (schurStepLast A) bY y) =
        𝓕 (modulatedGaussian (schurStepLast A) bY) (0 : EuclideanSpace ℝ (Fin (g + 1))) := by
      rw [fourier_modulatedGaussian_eq_integral (schurStepLast A) bY 0]
      congr 1
      funext i
      simp
    rw [hYint, ih (schurStepLast A) hA' hRe' bY 0]
    simp only [WithLp.ofLp_zero, Pi.zero_apply, Complex.ofReal_zero, zero_add]
    have hpivot_rec : pivotSqrt (g + 1 + 1) A = a ^ (1 / 2 : ℂ) * pivotSqrt (g + 1) (schurStepLast A) :=
      rfl
    rw [hpivot_rec]
    set z : Fin (g + 1 + 1) → ℂ := fun i => (ξ.ofLp i : ℂ) + I * b i with hz_def
    have hfinal : ∑ i, ∑ j, A⁻¹ i j * z i * z j =
        (∑ i, ∑ j, (schurStepLast A)⁻¹ i j * (I * bY i) * (I * bY j)) - bshiftLast ^ 2 / a := by
      obtain ⟨h11, h12, h21, h22⟩ := matrix_inv_blocks hpivot hA''ne
      have hrow : ∀ i : Fin (g + 1), A (Fin.last (g + 1)) i.castSucc = w i := fun i =>
        hA.apply i.castSucc (Fin.last (g + 1))
      have hcol : ∀ i : Fin (g + 1), A i.castSucc (Fin.last (g + 1)) = w i := fun _ => rfl
      have hzLast : z (Fin.last (g + 1)) = I * bshiftLast := by
        simp only [hz_def, hbshiftLast_def, hbshift_def]
        ring_nf
        rw [Complex.I_sq]
        ring
      have hIbY : ∀ i : Fin (g + 1), I * bY i =
          z i.castSucc - z (Fin.last (g + 1)) / a * w i := by
        intro i
        rw [hzLast]
        simp only [hbY_def, hz_def, hbshift_def]
        field_simp
        ring_nf
        rw [Complex.I_sq]
        ring
      have hsplit : ∑ i : Fin (g + 1 + 1), ∑ j : Fin (g + 1 + 1), A⁻¹ i j * z i * z j =
          ((∑ i : Fin (g + 1), ∑ j : Fin (g + 1),
              A⁻¹ i.castSucc j.castSucc * z i.castSucc * z j.castSucc) +
            (∑ i : Fin (g + 1), A⁻¹ i.castSucc (Fin.last (g + 1)) * z i.castSucc *
              z (Fin.last (g + 1)))) +
          ((∑ j : Fin (g + 1), A⁻¹ (Fin.last (g + 1)) j.castSucc * z (Fin.last (g + 1)) *
              z j.castSucc) +
            A⁻¹ (Fin.last (g + 1)) (Fin.last (g + 1)) * z (Fin.last (g + 1)) *
              z (Fin.last (g + 1))) := by
        rw [Fin.sum_univ_castSucc (fun i => ∑ j : Fin (g + 1 + 1), A⁻¹ i j * z i * z j)]
        congr 1
        · rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ =>
            Fin.sum_univ_castSucc (fun j => A⁻¹ i.castSucc j * z i.castSucc * z j)
        · exact Fin.sum_univ_castSucc (fun j => A⁻¹ (Fin.last (g + 1)) j * z (Fin.last (g + 1)) * z j)
      rw [hsplit]
      simp only [h11, h12, h21, h22, hrow, hcol, ← ha_def]
      set S : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ := (schurStepLast A)⁻¹ with hS_def
      set t : ℂ := z (Fin.last (g + 1)) with ht_def
      have hSsymm : ∀ i j : Fin (g + 1), S i j = S j i := fun i j => (hA'.inv.apply i j).symm
      have ht2 : t ^ 2 / a = -bshiftLast ^ 2 / a := by
        rw [hzLast]
        ring_nf
        rw [Complex.I_sq]
        ring
      simp only [hIbY]
      have hD2 : ∀ i : Fin (g + 1), (-∑ j, S i j * w j) / a * z i.castSucc * t =
          ∑ j, -(S i j * w j * z i.castSucc * t) / a := by
        intro i
        rw [show (-∑ j, S i j * w j) / a * z i.castSucc * t =
            (∑ j, S i j * w j) * (-(z i.castSucc * t) / a) from by ring, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hD3 : ∀ i : Fin (g + 1), (-∑ j, w j * S j i) / a * t * z i.castSucc =
          ∑ j, -(S i j * w j * z i.castSucc * t) / a := by
        intro i
        rw [show (-∑ j, w j * S j i) / a * t * z i.castSucc =
            (∑ j, w j * S j i) * (-(t * z i.castSucc) / a) from by ring, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hSsymm j i]
        ring
      have hD4 : (1 / a + (∑ i, ∑ j, w i * S i j * w j) / a ^ 2) * t * t =
          (∑ i, ∑ j, S i j * w i * w j * t ^ 2 / a ^ 2) + t ^ 2 / a := by
        have hswap : (∑ i, ∑ j, w i * S i j * w j) = ∑ i, ∑ j, S i j * w i * w j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        have hfactor : (∑ i, ∑ j, S i j * w i * w j) * t ^ 2 / a ^ 2 =
            ∑ i, ∑ j, S i j * w i * w j * t ^ 2 / a ^ 2 := by
          simp_rw [Finset.sum_mul, Finset.sum_div]
        rw [hswap, ← hfactor]
        ring
      have hexpand : ∀ i j : Fin (g + 1),
          S i j * (z i.castSucc - t / a * w i) * (z j.castSucc - t / a * w j) =
            S i j * z i.castSucc * z j.castSucc - S i j * w j * z i.castSucc * t / a -
              S i j * w i * t * z j.castSucc / a + S i j * w i * w j * t ^ 2 / a ^ 2 := by
        intro i j; ring
      have hstep1 : ∀ i : Fin (g + 1), ∑ j, (S i j * (z i.castSucc - t / a * w i) *
          (z j.castSucc - t / a * w j)) =
          (∑ j, S i j * z i.castSucc * z j.castSucc) -
            (∑ j, S i j * w j * z i.castSucc * t / a) -
            (∑ j, S i j * w i * t * z j.castSucc / a) +
            (∑ j, S i j * w i * w j * t ^ 2 / a ^ 2) := by
        intro i
        simp_rw [hexpand]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      simp_rw [hstep1]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      have hD2' : ∑ i, (-∑ j, S i j * w j) / a * z i.castSucc * t =
          ∑ i, ∑ j, -(S i j * w j * z i.castSucc * t) / a :=
        Finset.sum_congr rfl fun i _ => hD2 i
      have hD3' : ∑ i, (-∑ j, w j * S j i) / a * t * z i.castSucc =
          ∑ i, ∑ j, -(S i j * w j * z i.castSucc * t) / a :=
        Finset.sum_congr rfl fun i _ => hD3 i
      have hPQ : (∑ i, ∑ j, -(S i j * w j * z i.castSucc * t) / a) =
          -(∑ x, ∑ j, S x j * w j * z x.castSucc * t / a) := by
        simp_rw [neg_div, Finset.sum_neg_distrib]
      have hRQ : (∑ x, ∑ j, S x j * w x * t * z j.castSucc / a) =
          ∑ x, ∑ j, S x j * w j * z x.castSucc * t / a := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hSsymm j i]
        ring
      rw [hD2', hD3', hD4]
      linear_combination ht2 + 2 * hPQ + hRQ
    have hexp_eq : (-(π : ℂ) * ∑ i, ∑ j, A⁻¹ i j * z i * z j) =
        (π * bshiftLast ^ 2 / a) +
          (-(π : ℂ) * ∑ i, ∑ j, (schurStepLast A)⁻¹ i j * (I * bY i) * (I * bY j)) := by
      rw [hfinal]; ring
    rw [hexp_eq, Complex.exp_add]
    ring

/-- `modulatedGaussian_fourierTransform`, restated so the `ξ`-dependent part of the RHS is itself
a `modulatedGaussian` (in `A⁻¹`, with the dual linear shift `-I • A⁻¹.mulVec b`), rather than a
bare `exp`: the Fourier transform of a Gaussian is again a Gaussian, up to the `pivotSqrt`
amplitude and a `b`-only phase/scaling prefactor `exp(π · bᵀA⁻¹b)` that does not depend on `ξ`.
Pure algebra from `modulatedGaussian_fourierTransform`: expand `(ξ + I b)ᵀA⁻¹(ξ + I b)` and use
`A⁻¹`'s symmetry (`hA.inv`) to combine the two cross terms into `2 · (-I • A⁻¹b) · ξ`. -/
lemma modulatedGaussian_fourierTransform_eq_modulatedGaussian (hg : g ≠ 0)
    (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsSymm) (hRe : (A.map Complex.re).PosDef)
    (b : Fin g → ℂ) :
    ∀ ξ : EuclideanSpace ℝ (Fin g), 𝓕 (modulatedGaussian A b) ξ =
      1 / pivotSqrt g A * exp (π * ∑ i, ∑ j, A⁻¹ i j * b i * b j) *
        modulatedGaussian A⁻¹ (fun i => -I * ∑ j, A⁻¹ i j * b j) ξ := by
  intro ξ
  rw [modulatedGaussian_fourierTransform hg A hA hRe b ξ]
  unfold modulatedGaussian
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hsymm : ∀ i j : Fin g, A⁻¹ i j = A⁻¹ j i := fun i j => hA.inv.apply j i
  have hcross : ∑ i, ∑ j, A⁻¹ i j * b i * (ξ.ofLp j : ℂ) =
      ∑ i, ∑ j, A⁻¹ i j * (ξ.ofLp i : ℂ) * b j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i]
    ring
  have hterm : ∀ i j : Fin g,
      A⁻¹ i j * ((ξ.ofLp i : ℂ) + I * b i) * ((ξ.ofLp j : ℂ) + I * b j) =
        A⁻¹ i j * (ξ.ofLp i : ℂ) * (ξ.ofLp j : ℂ) +
          I * (A⁻¹ i j * (ξ.ofLp i : ℂ) * b j) + I * (A⁻¹ i j * b i * (ξ.ofLp j : ℂ)) -
          A⁻¹ i j * b i * b j := by
    intro i j
    ring_nf
    rw [Complex.I_sq]
    ring
  have hexpand :
      ∑ i, ∑ j, A⁻¹ i j * ((ξ.ofLp i : ℂ) + I * b i) * ((ξ.ofLp j : ℂ) + I * b j) =
      (∑ i, ∑ j, A⁻¹ i j * (ξ.ofLp i : ℂ) * (ξ.ofLp j : ℂ)) +
        2 * I * (∑ i, ∑ j, A⁻¹ i j * (ξ.ofLp i : ℂ) * b j) -
        ∑ i, ∑ j, A⁻¹ i j * b i * b j := by
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hcross]
    ring
  have hshift : ∑ i, (-I * ∑ j, A⁻¹ i j * b j) * (ξ.ofLp i : ℂ) =
      -I * ∑ i, ∑ j, A⁻¹ i j * (ξ.ofLp i : ℂ) * b j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [show -(π : ℂ) * ∑ i, ∑ j, A⁻¹ i j * ((ξ.ofLp i : ℂ) + I * b i) * ((ξ.ofLp j : ℂ) + I * b j) =
      -(π : ℂ) * (∑ i, ∑ j, A⁻¹ i j * (ξ.ofLp i : ℂ) * (ξ.ofLp j : ℂ)) +
        2 * (π : ℂ) * (∑ i, (-I * ∑ j, A⁻¹ i j * b j) * (ξ.ofLp i : ℂ)) +
        π * ∑ i, ∑ j, A⁻¹ i j * b i * b j from by
    rw [hshift, hexpand]; ring]
  ring

section CenterMax

/-- `modulatedGaussianCenter A center centerXi` peaks, in norm, strictly at `x = center` among
all `x ≠ center`: the real envelope `‖modulatedGaussianCenter A center centerXi x‖` is uniquely
maximized there, since `center` is exactly the vertex of the real quadratic
`-π xᵀ(Re A)x + 2π(Re b)·x` by construction (`Re b = (Re A) • center`).

Proved via the 1-D restriction to the segment `center → x` rather than the general multivariate
"complete the square": along `γ t := center + t • (x - center)`, the real exponent
`ψ t := Re(exponent)(γ t)` is *exactly* the downward parabola `ψ 0 - π • Q(x - center) • t ^ 2`
(`Q` the quadratic form of `Re A`) — the linear-in-`t` term cancels identically using `A`'s
symmetry, which is exactly the statement that `center` is a critical point of `ψ` (`ψ`'s
derivative at `t = 0` vanishes). Since `Re A` is positive definite, `Q(x - center) > 0` for
`x ≠ center`, so `ψ 1 < ψ 0`, i.e. `x` (at `t = 1`) has strictly smaller envelope than `center`
(at `t = 0`). -/
theorem modulatedGaussianCenter_norm_lt_of_ne (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsSymm)
    (hRe : (A.map Complex.re).PosDef) (center centerXi : EuclideanSpace ℝ (Fin g))
    {x : EuclideanSpace ℝ (Fin g)} (hx : x ≠ center) :
    ‖modulatedGaussianCenter A center centerXi x‖ <
      ‖modulatedGaussianCenter A center centerXi center‖ := by
  set v : Fin g → ℝ := fun i => x.ofLp i - center.ofLp i with hv_def
  set L : Fin g → ℝ := fun i => (A.map Complex.re).mulVec (WithLp.ofLp center) i with hLdef
  set ψ : ℝ → ℝ := fun t => -π * ∑ i, ∑ j, (A.map Complex.re) i j *
      (center.ofLp i + t * v i) * (center.ofLp j + t * v j) +
      2 * π * ∑ i, L i * (center.ofLp i + t * v i) with hψ_def
  set Qv : ℝ := ∑ i, ∑ j, (A.map Complex.re) i j * v i * v j with hQv_def
  have hnorm_path : ∀ t : ℝ,
      ‖modulatedGaussianCenter A center centerXi (center + t • (x - center))‖ =
        Real.exp (ψ t) := by
    intro t
    unfold modulatedGaussianCenter modulatedGaussian
    rw [Complex.norm_exp]
    congr 1
    have hpt : ∀ i, (WithLp.ofLp (center + t • (x - center)) i : ℝ) = center.ofLp i + t * v i := by
      intro i
      simp [hv_def]
    simp [Complex.re_sum, Matrix.map_apply, hpt, hψ_def, hLdef]
  have hAre_symm : (A.map Complex.re).IsSymm := hA.map _
  have hswap : ∀ y z : Fin g → ℝ, ∑ i, ∑ j, (A.map Complex.re) i j * y i * z j =
      ∑ i, ∑ j, (A.map Complex.re) i j * z i * y j := by
    intro y z
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hAre_symm.apply j i]
    ring
  have hL : ∀ i, L i = ∑ j, (A.map Complex.re) i j * center.ofLp j := fun _ => rfl
  have hLv : ∑ i, L i * v i = ∑ i, ∑ j, (A.map Complex.re) i j * center.ofLp i * v j := by
    have h1 : ∑ i, L i * v i = ∑ i, ∑ j, (A.map Complex.re) i j * v i * center.ofLp j := by
      simp_rw [hL, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1, hswap v center]
  have hQexpand : ∀ t : ℝ, ∑ i, ∑ j, (A.map Complex.re) i j *
      (center.ofLp i + t * v i) * (center.ofLp j + t * v j) =
      (∑ i, ∑ j, (A.map Complex.re) i j * center.ofLp i * center.ofLp j) +
        t * (2 * (∑ i, ∑ j, (A.map Complex.re) i j * center.ofLp i * v j)) +
        t ^ 2 * Qv := by
    intro t
    have hterm : ∀ i j : Fin g, (A.map Complex.re) i j *
        (center.ofLp i + t * v i) * (center.ofLp j + t * v j) =
        (A.map Complex.re) i j * center.ofLp i * center.ofLp j +
          t * ((A.map Complex.re) i j * center.ofLp i * v j) +
          t * (v i * ((A.map Complex.re) i j * center.ofLp j)) +
          t ^ 2 * (v i * ((A.map Complex.re) i j * v j)) := by
      intro i j; ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e3 : ∑ i, v i * ∑ j, (A.map Complex.re) i j * center.ofLp j =
        ∑ i, ∑ j, (A.map Complex.re) i j * center.ofLp i * v j := by
      have h1 : ∑ i, v i * ∑ j, (A.map Complex.re) i j * center.ofLp j =
          ∑ i, ∑ j, (A.map Complex.re) i j * v i * center.ofLp j := by
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h1, hswap v center]
    have e4 : ∑ i, v i * ∑ j, (A.map Complex.re) i j * v j = Qv := by
      rw [hQv_def]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e3, e4]
    ring
  have hψ0 : ψ 0 = -π * (∑ i, ∑ j, (A.map Complex.re) i j * center.ofLp i * center.ofLp j) +
      2 * π * ∑ i, L i * center.ofLp i := by
    have hψ0' : ψ 0 = -π * ∑ i, ∑ j, (A.map Complex.re) i j *
        (center.ofLp i + (0:ℝ) * v i) * (center.ofLp j + (0:ℝ) * v j) +
        2 * π * ∑ i, L i * (center.ofLp i + (0:ℝ) * v i) := rfl
    rw [hψ0']
    norm_num
  have hclosed : ∀ t : ℝ, ψ t = ψ 0 - π * Qv * t ^ 2 := by
    intro t
    have hψt : ψ t = -π * ∑ i, ∑ j, (A.map Complex.re) i j *
        (center.ofLp i + t * v i) * (center.ofLp j + t * v j) +
        2 * π * ∑ i, L i * (center.ofLp i + t * v i) := rfl
    have hLsplit : ∑ i, L i * (center.ofLp i + t * v i) =
        (∑ i, L i * center.ofLp i) + t * (∑ i, L i * v i) := by
      have hterm : ∀ i, L i * (center.ofLp i + t * v i) = L i * center.ofLp i + t * (L i * v i) := by
        intro i; ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hψt, hQexpand t, hψ0, hLsplit, hLv]
    ring
  have hQv_pos : 0 < Qv := by
    have hxv : (WithLp.ofLp x - WithLp.ofLp center : Fin g → ℝ) ≠ 0 := by
      intro h
      apply hx
      ext i
      have := congrFun h i
      simpa using sub_eq_zero.mp this
    have hpos := hRe.dotProduct_mulVec_pos hxv
    simp only [star_trivial, dotProduct, Matrix.mulVec, Pi.sub_apply] at hpos
    have heq : ∑ i, (x.ofLp i - center.ofLp i) * ∑ j, (A.map Complex.re) i j *
        (x.ofLp j - center.ofLp j) = Qv := by
      rw [hQv_def]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hv_def]; ring
    rwa [heq] at hpos
  have hcenter : center + (0:ℝ) • (x - center) = center := by simp
  have hx_eq : center + (1:ℝ) • (x - center) = x := by simp
  have h1 := hnorm_path 1
  have h0 := hnorm_path 0
  rw [hx_eq] at h1
  rw [hcenter] at h0
  rw [h1, h0]
  apply Real.exp_lt_exp.mpr
  rw [hclosed 1]
  nlinarith [hQv_pos, Real.pi_pos]

end CenterMax
