import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.ContinuousMap.Periodic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.LinearAlgebra.Matrix.Integer

open Function Complex Real
open TopologicalSpace Filter MeasureTheory Asymptotics
open scoped Real Filter FourierTransform TensorProduct
open ContinuousMap

noncomputable def intCastLinearMap : ℤ →ₗ[ℤ] ℂ :=
  (Int.castRingHom ℂ).toAddMonoidHom.toIntLinearMap

variable {R : Type u} [cr : CommRing R] [Module R ℝ] [Module R ℂ] [IsScalarTower R ℝ ℂ]
variable [SMulCommClass R ℂ ℂ]

/-- Casting `ℝ → ℂ` is `R`-linear: `IsScalarTower R ℝ ℂ` gives
`(r • s : ℝ) • (1 : ℂ) = r • (s • (1 : ℂ))`, and `t • (1 : ℂ) = (t : ℂ)` for any `t : ℝ`
(`Complex.real_smul`). -/
noncomputable def ofRealLinear : ℝ →ₗ[R] ℂ where
  toFun s := (s : ℂ)
  map_add' := by intro a b; push_cast; ring
  map_smul' r s := by
    show ((r • s : ℝ) : ℂ) = r • ((s : ℝ) : ℂ)
    have h1 : ((r • s : ℝ) : ℂ) = (r • s) • (1 : ℂ) := by rw [Complex.real_smul, mul_one]
    have h2 : ((s : ℝ) : ℂ) = s • (1 : ℂ) := by rw [Complex.real_smul, mul_one]
    rw [h1, h2, smul_assoc]

/-- Multiplication by `I` is `R`-linear: this is exactly what `SMulCommClass R ℂ ℂ` buys us. -/
noncomputable def mulILinear : ℂ →ₗ[R] ℂ where
  toFun z := Complex.I * z
  map_add' := by intro a b; ring
  map_smul' r z := by
    show Complex.I * (r • z) = r • (Complex.I * z)
    rw [← smul_eq_mul, ← smul_eq_mul, ← smul_comm r Complex.I z]
