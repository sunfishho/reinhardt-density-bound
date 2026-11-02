import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
example : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
#print axioms Real.sq_sqrt
