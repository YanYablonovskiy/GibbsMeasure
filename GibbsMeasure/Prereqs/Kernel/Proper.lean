import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Probability.Kernel.Proper

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

open MeasureTheory ENNReal NNReal Set
open scoped ProbabilityTheory
 
namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ≥0∞} {x₀ : X}

#check MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part

variable (f1 g1 : X → ℝ)

lemma IsProper.integral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f g : X → ℝ) (x₀ : X)
    (hf : Integrable[𝓧] f (π x₀)) (hg : Integrable[𝓑] (f * g) (@Measure.map _ _ 𝓧 𝓑 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  --Integrable.induction
  rw [MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part]
  . sorry
  . have: (f * g) =  (fun x ↦ f x * g x)  := by dsimp



end ProbabilityTheory.Kernel
