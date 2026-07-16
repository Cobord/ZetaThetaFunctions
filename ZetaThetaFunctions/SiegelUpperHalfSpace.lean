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
  (`ZetaFunctions/ThetaFunctions.lean`) consumes: `Q_Re`, `Q_Im`, `hQIm_cont`, `hQIm`.
* `quadraticMapOfMatrix`: the real quadratic form `x ↦ ⅟2 ∑ᵢⱼ Sᵢⱼxᵢxⱼ` on `EuclideanSpace ℝ (Fin g)`
  with Gram matrix `S`, inverse to `gramMatrixReal` on symmetric matrices
  (`quadraticMapOfMatrix_gramMatrixReal`, `gramMatrixReal_quadraticMapOfMatrix`).

## Status

Fully proved, no gaps.
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
          ((↑(((2 : ℝ) • τ.Q_Re) (latticeEmbedding (Fin g) n)) : ℂ) +
            Complex.I * (↑(((2 : ℝ) • τ.Q_Im) (latticeEmbedding (Fin g) n)) : ℂ)) +
        2 * ↑Real.pi * Complex.I * (SiegelUpperHalfSpace.shiftLinear b) n = _
  have hquad := τ.complex_quadratic (latticeEmbedding (Fin g) n)
  rw [QuadraticMap.smul_apply, QuadraticMap.smul_apply]
  simp only [smul_eq_mul]
  push_cast
  rw [show
    (2 : ℂ) * (↑(τ.Q_Re (latticeEmbedding (Fin g) n)) : ℂ) +
        Complex.I * ((2 : ℂ) * (↑(τ.Q_Im (latticeEmbedding (Fin g) n)) : ℂ)) =
      ∑ i, ∑ j, τ.toMatrix i j * (n i : ℂ) * (n j : ℂ) by
    calc
      _ = (2 : ℂ) *
          ((↑(τ.Q_Re (latticeEmbedding (Fin g) n)) : ℂ) +
            Complex.I * (↑(τ.Q_Im (latticeEmbedding (Fin g) n)) : ℂ)) := by ring
      _ = _ := by
        rw [hquad]
        have hle : ∀ i : Fin g,
            ((latticeEmbedding (Fin g) n).ofLp i : ℂ) = (n i : ℂ) := fun i => rfl
        simp_rw [hle]
        ring]
  rw [show SiegelUpperHalfSpace.shiftLinear b n = ∑ i, b i * (n i : ℂ) from rfl]

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

end MatrixQuadraticForms
