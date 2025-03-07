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


lemma IsProper.integral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f g : X → ℝ) (x₀ : X)
    (hf : Integrable[𝓧] f (π x₀)) (hg : Integrable[𝓑] (f * g) (@Measure.map _ _ 𝓧 𝓑 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
      apply  Integrable.induction (α:=X) (E:=ℝ) (μ:=(π x₀)) ( fun h ↦ Integrable[𝓧] h (π x₀) →
      ∫ x, h x * g x ∂(π x₀) = g x₀ * ∫ x, h x ∂(π x₀))
      · intro c S hmS bT hInt
        rw [integral_indicator hmS,integral_const];simp
        sorry
      · intro h1 h2 hdjSup hih1 hih2 h1imul h2imul hAddimul
        simp
        rw [integral_add hih1 hih2,mul_add]
        rw [←h1imul hih1,←h2imul hih2]
        rw [←integral_add]
        · congr
          ext v
          group
        · sorry
        · sorry
      · sorry        
      · intro h1 h2 h1aeh2 hih1 imulh1 hih2
        have := (Filter.eventuallyLE_antisymm_iff.mp h1aeh2).1
        have := (integral_eq_iff_of_ae_le hih1 hih2 this).mpr h1aeh2
        rw [←this]
        have :  h1 * g =ᶠ[ae (π x₀)] h2 * g := by
          sorry
        sorry
        --have := (integral_eq_iff_of_ae_le hih1 hih2)

      repeat simpa

end ProbabilityTheory.Kernel
