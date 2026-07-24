import Lake
open Lake DSL

package «ThetaFunctions» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "79d0395a1825a6264ad5d269e35e60537518955e"

@[default_target] lean_lib ZetaThetaFunctions.QuadraticFormZeta {}
@[default_target] lean_lib ZetaThetaFunctions.GaussianFourierTransform {}
@[default_target] lean_lib ZetaThetaFunctions.GeneralUtils {}
@[default_target] lean_lib ZetaThetaFunctions.LatticeUtils {}
@[default_target] lean_lib ZetaThetaFunctions.PoissonSummation {}
@[default_target] lean_lib ZetaThetaFunctions.QuadraticFormUtils {}
@[default_target] lean_lib ZetaThetaFunctions.SchurPivot {}
@[default_target] lean_lib ZetaThetaFunctions.SiegelModular {}
@[default_target] lean_lib ZetaThetaFunctions.SiegelUpperHalfSpace {}
@[default_target] lean_lib ZetaThetaFunctions.Sp2gR {}
@[default_target] lean_lib ZetaThetaFunctions.ThetaFunctions {}
@[default_target] lean_lib ZetaThetaFunctions.MobiusInvariantProduct {}
