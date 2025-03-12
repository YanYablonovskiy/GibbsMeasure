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


lemma IsProper.integral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
 (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) : (∫ x, (B.indicator 1 x * A.indicator 1 x) ∂(π x₀)
  = ((B.indicator 1 x₀) * (∫ x, A.indicator 1 x ∂(π x₀)) :ℝ))  := by
      rw [integral_eq_lintegral_of_nonneg_ae]
      conv_lhs =>
        rhs
        rhs
        intro a
        rw [←inter_indicator_mul (M₀:=ℝ) (s:=B) (t:=A) 1 1]
      simp
      have:∀a,ENNReal.ofReal ((B ∩ A).indicator (fun j ↦ 1) a) = (B ∩ A).indicator 1 a := by
       intro a
       by_cases h: a ∈ (B ∩ A) <;> simp [h]
      conv_lhs =>
        rhs
        rhs
        intro a
        rw [this a]
      have pmul := IsProper.lintegral_mul hπ h𝓑𝓧 (g:= fun x ↦ B.indicator 1 x) (f:= fun x ↦ A.indicator 1 x)
       (by apply Measurable.indicator <;> measurability ) (by
         apply Measurable.indicator;exact @measurable_one ℝ≥0∞ X (inferInstance) 𝓑  (inferInstance);exact hB) x₀

      have: (fun j:X ↦ (1:X →  ℝ≥0∞) j * (1:X →  ℝ≥0∞) j) = 1 := by ext j ; simp
      conv_lhs =>
       rhs
       rhs
       intro a
       rw [←this]
       rw [inter_indicator_mul (M₀:=ℝ≥0∞) (s:=B) (t:=A) 1 1 a]
      rw [pmul]
      rw [lintegral_indicator_one hA,integral_indicator_one hA]
      rw [ENNReal.toReal_mul]
      congr
      by_cases hxB: x₀ ∈ B
      · simp [hxB]
      · simp [hxB]
      · filter_upwards
        intro a
        by_cases h: a ∈ (B ∩ A) ; simp [h.1,h.2] ; simp; simp [indicator_nonneg,mul_nonneg]
      . measurability


#check IsProper.integral_indicator_mul_indicator

--@indicator X ℝ≥0∞ instENNRealZero (B ∩ A) : (X → ℝ≥0∞) → X → ℝ≥0∞

private lemma IsProper.integral_indicator_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Integrable[𝓧] f (π x₀)) (hB : MeasurableSet[𝓑] B):
      ∫ x, (B.indicator 1 x) * (f x) ∂(π x₀) = B.indicator 1 x₀ * ∫ x, f x ∂(π x₀) := by
        sorry


#check Disjoint.inter_right'



#check integral_mul_left

#check integrable_add_of_disjoint
#check integrable_of_integrable_trim
#check Function.support_mul
#check integral_add
#check Function.comp_apply
lemma IsProper.integral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f g : X → ℝ) (x₀ : X)
    (hf : Integrable[𝓧] f (π x₀)) (hg : Integrable[𝓑] (g * f) (@Measure.map _ _ 𝓧 𝓑 id (π x₀))):
    ∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
      apply @Integrable.induction (α:=X) (E:=ℝ) 𝓑 (inferInstance) (μ:=(@Measure.map _ _ 𝓧 𝓑 id (π x₀))) ( fun h ↦ Integrable[𝓑] (h * f) (@Measure.map _ _ 𝓧 𝓑 id (π x₀)) →
       ∫ x, h x * f x ∂(π x₀) = h x₀ * ∫ x, f x ∂(π x₀))
      · intro c S hmS bT hInt
        simp_rw [← smul_indicator_one_apply, smul_mul_assoc, smul_eq_mul]
        rw [integral_mul_left]
        congr
        apply IsProper.integral_indicator_mul hπ h𝓑𝓧 hf hmS
      · intro g1 g2 hDisj hIntg1 hIntg2 hIntg1f hIntg2f hIntAdd
        conv at hIntAdd in  ((g1 + g2)*f) =>
         rw [add_mul]
        have:  Disjoint (Function.support (g1*f)) (Function.support (g2*f)) := by
          have h1 : Function.support (g1*f) = Function.support g1 ∩ Function.support f := by
            exact Function.support_mul (M₀ := ℝ) g1 f
          have h2 : Function.support (g2*f) = Function.support g2 ∩ Function.support f := by
            exact Function.support_mul (M₀ := ℝ) g2 f
          simp_rw [h1,h2]
          refine Disjoint.inter_left (Function.support f) ?_
          refine Disjoint.inter_right (Function.support f) ?_
          exact hDisj
        have := (@integrable_add_of_disjoint _ _ 𝓑 _ _ _ this (μ := @Measure.map _ _ 𝓧 𝓑 id (π x₀)) ?_ ?_).mp hIntAdd
        simp
        rw [add_mul]
        conv_lhs =>
         rhs
         intro x
         rw [add_mul]
        rw [←hIntg1f this.1,←hIntg2f this.2]
        have fmul: ∀x,g1 x * f x + g2 x * f x = (g1 * f) x + (g2 * f) x := by exact fun x ↦ rfl
        conv_lhs =>
          rhs
          intro x
          rw [fmul x]
        refine integral_add ?_ ?_
        simp_all
        ·


      · sorry
      · sorry
        sorry





end ProbabilityTheory.Kernel
