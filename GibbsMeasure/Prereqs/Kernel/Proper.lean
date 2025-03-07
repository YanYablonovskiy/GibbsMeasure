import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Probability.Kernel.Proper
import GibbsMeasure.Specification

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
#check (f * g)
#check Measure.map id
variable (f1 g1 : X → ℝ)
#check MemLp
#check  IsProper.lintegral_mul
#check Integrable.comp_measurable
#check IntegrableOn.restrict_toMeasurable
#check toMeasurable
#check Measurable.aestronglyMeasurable
#check Integrable
#check Integrable.induction
#check IsClosed

lemma IsProper.integral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f g : X → ℝ) (x₀ : X)
    (hf : Integrable[𝓧] f (π x₀)) (hg : Integrable[𝓑] (f * g) (@Measure.map _ _ 𝓧 𝓑 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
      apply  Integrable.induction (α:=X) (E:=ℝ) (μ:=(π x₀)) ( fun _ ↦ ∫ x, f x * g x ∂(π x₀) 
      = g x₀ * ∫ x, f x ∂(π x₀))
      ·  intro x s hms bd
         sorry
      ·  simp
      ·  sorry -- closure
      ·  simp
      ·  simpa



/-
  rw [MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part]
  . rw [IsProper.lintegral_mul hπ h𝓑𝓧 hf.1]
  . have: (f * g) =  (fun x ↦ f x * g x)  := by rfl
    rw [←this]
    have: Measure.map id (π x₀) = (π x₀) := by exact Measure.map_id
    rw [←this]
    sorry
-/
#check IsProper.integral_mul

end ProbabilityTheory.Kernel
