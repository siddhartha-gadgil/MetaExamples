import LeanAideCore
import Mathlib

open LeanAide
universe u v w u_1 u_2 u_3 u₁ u₂ u₃
@[default_instance]
instance : Add ℤ := inferInstance
@[default_instance]
instance : Semiring ℤ := inferInstance

#leanaide_connect

#eval LeanAidePipe.response <| json% {"task": "echo"}

#eval KernelM.translateThm "There are infinitely many odd numbers."

#theorem : "There are infinitely many odd numbers."
