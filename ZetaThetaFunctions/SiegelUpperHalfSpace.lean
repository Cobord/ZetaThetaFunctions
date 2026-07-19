import ZetaThetaFunctions.ThetaFunctions

/-!
# The Siegel upper half-space and matrix quadratic forms

The bundled genus-`g` Siegel upper half-space `SiegelUpperHalfSpace g` and the conversion between
symmetric matrices and real quadratic forms on `EuclideanSpace ℝ (Fin g)` (`quadraticMapOfMatrix`,
inverse to `gramMatrixReal`). Split out of `SiegelModular.lean` (which needs `Sp2gR`/
`Matrix.symplecticGroup` for the group action) so that files needing only this matrix/quadratic-form
layer — e.g. `PoissonSummation.lean`, which `SiegelModular.lean` will eventually depend on for the
`S_g` transformation law — can import it without a circular dependency.

## Main definitions

* `SiegelUpperHalfSpace g`: a Siegel point, bundled exactly as the data `RiemannThetaAble`
  (`ThetaFunctions.lean`) consumes: `Q_Re`, `Q_Im`, `hQIm_cont`, `hQIm`.
* `quadraticMapOfMatrix`: the real quadratic form `x ↦ ⅟2 ∑ᵢⱼ Sᵢⱼxᵢxⱼ` on `EuclideanSpace ℝ (Fin g)`
  with Gram matrix `S`, inverse to `gramMatrixReal` on symmetric matrices
  (`quadraticMapOfMatrix_gramMatrixReal`, `gramMatrixReal_quadraticMapOfMatrix`).

-/

variable {R : Type*} [CommRing R] [Algebra R ℝ] [Algebra R ℂ] [IsScalarTower R ℝ ℂ]
variable {g : ℕ}

section UpperHalfSpace

/-- A point of the genus-`g` Siegel upper half-space, bundled exactly as the data
`RiemannThetaAble` consumes: a pair `(Q_Re, Q_Im)` of real quadratic forms on
`EuclideanSpace ℝ (Fin g)` (the real and imaginary parts of the modulus `Q = Q_Re + I Q_Im`),
together with the continuity and positive-definiteness of `Q_Im` that make `Q` a genuine Siegel
point. -/
structure SiegelUpperHalfSpace (g : ℕ) where
  /-- The real part `Q_Re` of the modulus `Q = Q_Re + I Q_Im`. -/
  Q_Re : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ
  /-- The imaginary part `Q_Im` of the modulus `Q = Q_Re + I Q_Im`. -/
  Q_Im : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ
  hQIm_cont : Continuous Q_Im
  hQIm : Q_Im.PosDef

/-- Two Siegel points agreeing on `Q_Re` and `Q_Im` are equal: `hQIm_cont`/`hQIm` are `Prop`-valued,
so once the data fields match they agree automatically by proof irrelevance. Avoids the dependent
`rw`/`motive is not type correct` failure that a direct `rw` into a `SiegelUpperHalfSpace` literal
runs into (rewriting `Q_Im` also changes the *type* of the `hQIm_cont`/`hQIm` fields). -/
lemma SiegelUpperHalfSpace.ext {τ σ : SiegelUpperHalfSpace g}
    (hRe : τ.Q_Re = σ.Q_Re) (hIm : τ.Q_Im = σ.Q_Im) : τ = σ := by
  cases τ; cases σ
  subst hRe; subst hIm
  rfl

end UpperHalfSpace

section MatrixQuadraticForms

/-- The complex symmetric `g × g` matrix `Q_Re + I Q_Im` underlying a Siegel point, in the
standard orthonormal basis (via `gramMatrixReal`). -/
noncomputable def SiegelUpperHalfSpace.toMatrix (τ : SiegelUpperHalfSpace g) :
    Matrix (Fin g) (Fin g) ℂ :=
  fun i j => (gramMatrixReal τ.Q_Re i j : ℂ) + Complex.I * (gramMatrixReal τ.Q_Im i j : ℂ)

/-- The real part of `τ.toMatrix`, entrywise, is exactly `τ.Q_Re`'s Gram matrix. -/
lemma SiegelUpperHalfSpace.toMatrix_map_re (τ : SiegelUpperHalfSpace g) :
    τ.toMatrix.map Complex.re = gramMatrixReal τ.Q_Re := by
  ext i j
  simp [SiegelUpperHalfSpace.toMatrix, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- The imaginary part of `τ.toMatrix`, entrywise, is exactly `τ.Q_Im`'s Gram matrix. -/
lemma SiegelUpperHalfSpace.toMatrix_map_im (τ : SiegelUpperHalfSpace g) :
    τ.toMatrix.map Complex.im = gramMatrixReal τ.Q_Im := by
  ext i j
  simp [SiegelUpperHalfSpace.toMatrix, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- The polar bilinear form of `Q`, expanded in the standard orthonormal basis via its Gram
matrix: `Q.polarBilin a b = ∑ᵢⱼ aᵢ bⱼ (gramMatrixReal Q)ᵢⱼ`. Mirrors `EpsteinZeta.lean`'s
`polarBilin_eq_sum`, for `EuclideanSpace ℝ (Fin g)` directly rather than through a lattice
embedding. -/
lemma polarBilin_eq_gramMatrixReal_sum (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ)
    (a b : EuclideanSpace ℝ (Fin g)) :
    Q.polarBilin a b = ∑ i, ∑ j, (a i * b j) * gramMatrixReal Q i j := by
  set e := EuclideanSpace.basisFun (Fin g) ℝ with he
  have ha : a = ∑ i, a i • e i := by
    conv_lhs => rw [← e.sum_repr a]
    simp [he, EuclideanSpace.basisFun_repr]
  have hb : b = ∑ j, b j • e j := by
    conv_lhs => rw [← e.sum_repr b]
    simp [he, EuclideanSpace.basisFun_repr]
  conv_lhs => rw [ha, hb]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    gramMatrixReal_apply, he, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `quadraticMapOfMatrix` inverts `gramMatrixReal`: rebuilding the quadratic form from its own
Gram matrix recovers the original form. The general-matrix analogue of `EpsteinZeta.lean`'s
`gramQuadraticMap_apply_toEuclidean`. Only `Invertible (2 : ℝ)` is used (via `invOf_mul_self`),
not `ℝ`'s field structure. -/
lemma quadraticMapOfMatrix_gramMatrixReal (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin g)) ℝ) :
    quadraticMapOfMatrix (gramMatrixReal Q) = Q := by
  apply QuadraticMap.ext
  intro x
  have hpolar : Q.polarBilin x x = ∑ i, ∑ j, (x i * x j) * gramMatrixReal Q i j :=
    polarBilin_eq_gramMatrixReal_sum Q x x
  have h2Q : Q.polarBilin x x = 2 * Q x := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    ring
  rw [quadraticMapOfMatrix_apply]
  simp only [Algebra.algebraMap_self_apply]
  rw [show (∑ i, ∑ j, gramMatrixReal Q i j * (x i * x j))
        = ∑ i, ∑ j, (x i * x j) * gramMatrixReal Q i j from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _,
    ← hpolar, h2Q, ← mul_assoc, invOf_mul_self, one_mul]

/-- The complex quadratic form of a Siegel point is one half of its matrix quadratic form. -/
lemma SiegelUpperHalfSpace.complex_quadratic (τ : SiegelUpperHalfSpace g)
    (v : EuclideanSpace ℝ (Fin g)) :
    (τ.Q_Re v : ℂ) + Complex.I * (τ.Q_Im v : ℂ) =
      (2 : ℂ)⁻¹ * ∑ i, ∑ j, τ.toMatrix i j * (v i : ℂ) * (v j : ℂ) := by
  rw [← quadraticMapOfMatrix_gramMatrixReal τ.Q_Re,
    ← quadraticMapOfMatrix_gramMatrixReal τ.Q_Im,
    quadraticMapOfMatrix_apply, quadraticMapOfMatrix_apply]
  simp only [Algebra.algebraMap_self_apply]
  simp_rw [SiegelUpperHalfSpace.toMatrix]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [<-Finset.sum_add_distrib]
  conv_rhs => rw [Finset.mul_sum]
  congr 1
  funext i
  refine mul_left_cancel₀ ?two_nonzero (a:=2) ?rest
  · simp
  · conv_lhs =>
      rw [mul_add]
      repeat rw [<-mul_assoc (a:=2)]
      simp
      rw [<-mul_assoc (2 * Complex.I)]
      rw [mul_comm 2]
      rw [mul_assoc _ 2]
      simp
      rw [Finset.mul_sum (a:=Complex.I)]
      rw [<-Finset.sum_add_distrib]
    conv_rhs =>
      rw [<-mul_assoc 2]
      simp
    congr 1
    ext j
    conv_rhs =>
      rw [mul_assoc]
      rw [add_mul]
    ring_nf

/-- The linear shift `n ↦ ∑ᵢ bᵢ nᵢ` in the standard lattice coordinates. -/
noncomputable def SiegelUpperHalfSpace.shiftLinear (b : Fin g → ℂ) :
    (Fin g → ℤ) →ₗ[ℤ] ℂ where
  toFun n := ∑ i, b i * (n i : ℂ)
  map_add' n m := by
    simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
  map_smul' c n := by
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    simp only [id_eq]
    ring

/-- Absolute summability of the standard Riemann theta series attached to a Siegel matrix:
`exp (π I nᵀ A n + 2π I bᵀn)`. The factor `2` used to instantiate
`RiemannThetaAble` compensates for `quadraticMapOfMatrix`'s half-Gram normalization. -/
theorem SiegelUpperHalfSpace.summable_cexp_matrix (hg : g ≠ 0)
    (τ : SiegelUpperHalfSpace g) (b : Fin g → ℂ) :
    Summable (fun n : Fin g → ℤ => Complex.exp
      (↑Real.pi * Complex.I *
          (∑ i, ∑ j, τ.toMatrix i j * (n i : ℂ) * (n j : ℂ)) +
        2 * ↑Real.pi * Complex.I * ∑ i, b i * (n i : ℂ))) := by
  letI := RiemannThetaAble hg ((2 : ℝ) • τ.Q_Re) ((2 : ℝ) • τ.Q_Im)
    (by
      change Continuous (fun x => (2 : ℝ) • τ.Q_Im x)
      exact τ.hQIm_cont.const_smul (2 : ℝ))
    (τ.hQIm.smul (by norm_num))
  have hs := ThetaAbleQuadraticForm.theta_fun_summable
    (R := ℤ) (M := Fin g → ℤ) (SiegelUpperHalfSpace.shiftLinear b)
  refine hs.congr fun n => ?_
  apply congrArg Complex.exp
  change
    ↑Real.pi * Complex.I *
          ((↑(((2 : ℝ) • τ.Q_Re) (toEuclidean_ZnRn n)) : ℂ) +
            Complex.I * (↑(((2 : ℝ) • τ.Q_Im) (toEuclidean_ZnRn n)) : ℂ)) +
        2 * ↑Real.pi * Complex.I * (SiegelUpperHalfSpace.shiftLinear b) n = _
  have hquad := τ.complex_quadratic (toEuclidean_ZnRn n)
  rw [QuadraticMap.smul_apply, QuadraticMap.smul_apply]
  simp only [smul_eq_mul]
  push_cast
  rw [show
    (2 : ℂ) * (↑(τ.Q_Re (toEuclidean_ZnRn n)) : ℂ) +
        Complex.I * ((2 : ℂ) * (↑(τ.Q_Im (toEuclidean_ZnRn n)) : ℂ)) =
      ∑ i, ∑ j, τ.toMatrix i j * (n i : ℂ) * (n j : ℂ) by
    calc
      _ = (2 : ℂ) *
          ((↑(τ.Q_Re (toEuclidean_ZnRn n)) : ℂ) +
            Complex.I * (↑(τ.Q_Im (toEuclidean_ZnRn n)) : ℂ)) := by ring
      _ = _ := by
        rw [hquad]
        have hle : ∀ i : Fin g,
            ((toEuclidean_ZnRn n).ofLp i : ℂ) = (n i : ℂ) := fun i => rfl
        simp_rw [hle]
        ring]
  rw [show SiegelUpperHalfSpace.shiftLinear b n = ∑ i, b i * (n i : ℂ) from rfl]

end MatrixQuadraticForms
