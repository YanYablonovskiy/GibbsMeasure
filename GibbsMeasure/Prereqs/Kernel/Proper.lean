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
       Integrable[𝓑] (h * g) (@Measure.map _ _ 𝓧 𝓑 id (π x₀)) → 
       ∫ x, h x * g x ∂(π x₀) = g x₀ * ∫ x, h x ∂(π x₀))
      · intro c S hmS bT hInt hIntp
        rw [integral_indicator_const c hmS]
        have: ∀(y:X),S.indicator (fun x ↦ c) y * g y = S.indicator (fun x ↦ (g x) * c) y := by
          intro a
          by_cases hp:a ∈ S <;> rw [indicator,indicator] <;> simp <;> rw [mul_comm]
        conv in S.indicator (fun x ↦ c) _ * g _   =>
         rw [this]
        rw [integral_indicator hmS]
        conv in (((π x₀) S).toReal • c) =>
         simp
        rw [←mul_assoc,mul_comm] 
        rw [integral_mul_right,mul_comm]
        congr
        rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part]
        have: ∀(y:X), ENNReal.ofReal (g y) = ENNReal.ofReal (g y) * 1 := by
         simp
        conv in ENNReal.ofReal (g _) =>
         rw [this a]
        --rw [IsProper.lintegral_mul hπ h𝓑𝓧 (x₀ := x₀) (g:= fun k ↦ ENNReal.ofReal (g k)) (f:= fun _ ↦ 1)]
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
