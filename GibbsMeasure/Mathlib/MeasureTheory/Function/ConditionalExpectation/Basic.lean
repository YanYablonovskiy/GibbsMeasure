module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

public section

open Set TopologicalSpace MeasureTheory.Lp Filter
open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory
variable {α F F' 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']

variable {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → F'} {s : Set α}

-- /-- **Uniqueness of the conditional expectation**
-- If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
-- as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
-- theorem toReal_ae_eq_condExp_toReal_of_forall_setLIntegral_eq (hm : m ≤ m0)
--     [SigmaFinite (μ.trim hm)] {f g : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
--     (hf : ∫⁻ a, f a ∂μ ≠ ⊤)
--     (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ a in s, g a ∂μ ≠ ⊤)
--     (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, f x ∂μ)
--     (hgm : AEStronglyMeasurable[m] g μ) :
--     (fun a ↦ (g a).toReal) =ᵐ[μ] μ[fun a ↦ (f a).toReal|m] := by
--   refine ae_eq_condExp_of_forall_setIntegral_eq hm
--     (integrable_toReal_of_lintegral_ne_top hf_meas hf)
--     (fun s hs hs_fin ↦ integrable_toReal_of_lintegral_ne_top _ _) _ _

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α} (hs₀ : MeasurableSet s) (hs : μ s ≠ ⊤)
    (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
    (hg_eq : ∀ t : Set α, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ = μ (s ∩ t))
    (hgm : AEStronglyMeasurable[m] g μ) : (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] := by
  have h_int_ind : Integrable (s.indicator fun _ : α => (1 : ℝ)) μ := by
    refine (integrable_indicator_iff hs₀).2 ?_
    rw [IntegrableOn]
    have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs
    exact integrable_const (μ := μ.restrict s) (c := (1 : ℝ))
  refine ae_eq_condExp_of_forall_setIntegral_eq hm h_int_ind ?_ ?_ ?_
  · intro t ht hμt
    refine integrable_toReal_of_lintegral_ne_top (hgm.mono hm).aemeasurable.restrict ?_
    simpa [Measure.restrict_restrict (hm _ ht)] using hg_int_finite t ht hμt
  · intro t ht hμt
    have ht0 : MeasurableSet t := hm _ ht
    have hg_ae : ∀ᵐ x ∂μ.restrict t, g x < ∞ :=
      ae_lt_top' (AEMeasurable.restrict (hgm.mono hm).aemeasurable)
        (by simpa [Measure.restrict_restrict (hm _ ht)] using hg_int_finite t ht hμt)
    calc
      ∫ x in t, (g x).toReal ∂μ = (∫⁻ x in t, g x ∂μ).toReal := by
        rw [← integral_toReal (AEMeasurable.restrict (hgm.mono hm).aemeasurable) hg_ae]
      _ = (μ (s ∩ t)).toReal := by rw [hg_eq t ht hμt]
      _ = μ.real (s ∩ t) := measureReal_def _ _
      _ = μ.real (t ∩ s) := congr_arg μ.real (inter_comm s t)
      _ = ∫ x in t ∩ s, (1 : ℝ) ∂μ := by
            rw [setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ x in t, (s.indicator fun _ : α => (1 : ℝ)) x ∂μ := by
            rw [← setIntegral_indicator hs₀]
  · have hmk_toReal : AEStronglyMeasurable[m] (fun x => (hgm.mk g x).toReal) μ :=
      (stronglyMeasurable_iff_measurable.2
        (Measurable.ennreal_toReal hgm.stronglyMeasurable_mk.measurable)).aestronglyMeasurable
    exact hmk_toReal.congr (EventuallyEq.fun_comp hgm.ae_eq_mk ENNReal.toReal).symm

lemma toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α} (hs₀ : MeasurableSet s) (hs : μ s ≠ ⊤)
    (hgm : AEStronglyMeasurable[m] g μ) (hae : ∀ᵐ x ∂μ, g x < ∞) :
    (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] ↔
      ∀ t, MeasurableSet[m] t → μ (s ∩ t) = ∫⁻ a in t, g a ∂μ := by
  let S : ℕ → Set α := spanningSets (μ.trim hm)
  have hSmeas (i : ℕ) : MeasurableSet[m] (S i) := measurableSet_spanningSets (μ := μ.trim hm) i
  have hSfin (i : ℕ) : μ (S i) < ∞ := by
    rw [← trim_measurableSet_eq hm (hSmeas i)]
    exact measure_spanningSets_lt_top (μ.trim hm) i
  have h_int_ind : Integrable (s.indicator fun _ : α => (1 : ℝ)) μ := by
    refine (integrable_indicator_iff hs₀).2 ?_
    rw [IntegrableOn]
    have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs
    exact integrable_const (μ := μ.restrict s) (c := (1 : ℝ))
  have hintg (h : (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m]) :
      Integrable (fun a ↦ (g a).toReal) μ :=
    (integrable_congr h).mpr
      (integrable_condExp (μ := μ) (m := m) (m₀ := m0) (f := s.indicator fun _ : α => (1 : ℝ)))
  constructor
  · intro h t ht
    have ht0 : MeasurableSet t := hm _ ht
    have hunion : ⋃ i : ℕ, t ∩ S i = t := by
      rw [← inter_iUnion, iUnion_spanningSets (μ := μ.trim hm), inter_univ]
    have hdir : Directed (· ⊆ ·) fun i : ℕ => t ∩ S i := by
      intro i j
      refine ⟨max i j, ?_, ?_⟩
      · exact inter_subset_inter_right t (spanningSets_mono (μ := μ.trim hm) (le_max_left i j))
      · exact inter_subset_inter_right t (spanningSets_mono (μ := μ.trim hm) (le_max_right i j))
    have mono_sts : Monotone fun i : ℕ => s ∩ t ∩ S i := fun i j hij =>
      inter_subset_inter_right (s ∩ t) (spanningSets_mono (μ := μ.trim hm) hij)
    have h_fin (u : Set α) (hum : MeasurableSet[m] u) (hμu : μ u < ∞) :
        μ (s ∩ u) = ∫⁻ a in u, g a ∂μ := by
      have hu0 : MeasurableSet u := hm _ hum
      have hμ_inter_ne : μ (s ∩ u) ≠ ∞ :=
        ne_top_of_le_ne_top hμu.ne (measure_mono inter_subset_right)
      have h1 : ∫ x in u, (g x).toReal ∂μ = μ.real (s ∩ u) := by
        calc
          ∫ x in u, (g x).toReal ∂μ
              = ∫ x in u, μ[s.indicator 1|m] x ∂μ :=
                setIntegral_congr_ae hu0 (h.mono fun x hx _ => hx)
          _ = ∫ x in u, (s.indicator fun _ : α => (1 : ℝ)) x ∂μ :=
                setIntegral_condExp hm h_int_ind hum
          _ = μ.real (s ∩ u) := by
                rw [setIntegral_indicator hs₀, setIntegral_const, smul_eq_mul, mul_one]
                exact congr_arg μ.real (inter_comm u s)
      have hint_u : Integrable (fun a ↦ (g a).toReal) (μ.restrict u) :=
        (hintg h).restrict (s := u)
      have h2 := ofReal_integral_eq_lintegral_ofReal hint_u
          (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      rw [h1, ofReal_measureReal hμ_inter_ne] at h2
      have h3 : ∫⁻ x in u, ENNReal.ofReal ((g x).toReal) ∂μ = ∫⁻ x in u, g x ∂μ := by
        refine setLIntegral_congr_fun_ae hu0 ?_
        filter_upwards [hae] with x hx
        intro hxu
        exact ENNReal.ofReal_toReal (LT.lt.ne_top hx)
      rw [h3] at h2
      exact h2
    calc
      μ (s ∩ t) = μ (⋃ i : ℕ, s ∩ (t ∩ S i)) := by
            rw [← inter_iUnion, hunion]
      _ = μ (⋃ i : ℕ, s ∩ t ∩ S i) := by simp_rw [← inter_assoc]
      _ = ⨆ i : ℕ, μ (s ∩ t ∩ S i) := mono_sts.measure_iUnion
      _ = ⨆ i : ℕ, ∫⁻ a in t ∩ S i, g a ∂μ :=
            iSup_congr fun i =>
              (inter_assoc s t (S i)).symm ▸
                h_fin (t ∩ S i) (ht.inter (hSmeas i))
                  ((measure_mono inter_subset_right).trans_lt (hSfin i))
      _ = ∫⁻ a in ⋃ i : ℕ, t ∩ S i, g a ∂μ := (setLIntegral_iUnion_of_directed g hdir).symm
      _ = ∫⁻ a in t, g a ∂μ := by rw [hunion]
  · intro hfg
    refine toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq hm hs₀ hs
      (fun t ht hμt => ?_) ?_ hgm
    · rw [← hfg t ht]
      exact ((measure_mono inter_subset_right).trans_lt hμt).ne
    · intro t ht hμt
      rw [hfg t ht]

end MeasureTheory
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

public section

open Set TopologicalSpace MeasureTheory.Lp Filter
open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory
variable {α F F' 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']

variable {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → F'} {s : Set α}

-- /-- **Uniqueness of the conditional expectation**
-- If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
-- as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
-- theorem toReal_ae_eq_condExp_toReal_of_forall_setLIntegral_eq (hm : m ≤ m0)
--     [SigmaFinite (μ.trim hm)] {f g : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
--     (hf : ∫⁻ a, f a ∂μ ≠ ⊤)
--     (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ a in s, g a ∂μ ≠ ⊤)
--     (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, f x ∂μ)
--     (hgm : AEStronglyMeasurable[m] g μ) :
--     (fun a ↦ (g a).toReal) =ᵐ[μ] μ[fun a ↦ (f a).toReal|m] := by
--   refine ae_eq_condExp_of_forall_setIntegral_eq hm
--     (integrable_toReal_of_lintegral_ne_top hf_meas hf)
--     (fun s hs hs_fin ↦ integrable_toReal_of_lintegral_ne_top _ _) _ _

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α} (hs₀ : MeasurableSet s) (hs : μ s ≠ ⊤)
    (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
    (hg_eq : ∀ t : Set α, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ = μ (s ∩ t))
    (hgm : AEStronglyMeasurable[m] g μ) : (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] := by
  have h_int_ind : Integrable (s.indicator fun _ : α => (1 : ℝ)) μ := by
    refine (integrable_indicator_iff hs₀).2 ?_
    rw [IntegrableOn]
    have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs
    exact integrable_const (μ := μ.restrict s) (c := (1 : ℝ))
  refine ae_eq_condExp_of_forall_setIntegral_eq hm h_int_ind ?_ ?_ ?_
  · intro t ht hμt
    refine integrable_toReal_of_lintegral_ne_top (hgm.mono hm).aemeasurable.restrict ?_
    simpa [Measure.restrict_restrict (hm _ ht)] using hg_int_finite t ht hμt
  · intro t ht hμt
    have ht0 : MeasurableSet t := hm _ ht
    have hg_ae : ∀ᵐ x ∂μ.restrict t, g x < ∞ :=
      ae_lt_top' (AEMeasurable.restrict (hgm.mono hm).aemeasurable)
        (by simpa [Measure.restrict_restrict (hm _ ht)] using hg_int_finite t ht hμt)
    calc
      ∫ x in t, (g x).toReal ∂μ = (∫⁻ x in t, g x ∂μ).toReal := by
        rw [← integral_toReal (AEMeasurable.restrict (hgm.mono hm).aemeasurable) hg_ae]
      _ = (μ (s ∩ t)).toReal := by rw [hg_eq t ht hμt]
      _ = μ.real (s ∩ t) := measureReal_def _ _
      _ = μ.real (t ∩ s) := congr_arg μ.real (inter_comm s t)
      _ = ∫ x in t ∩ s, (1 : ℝ) ∂μ := by
            rw [setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ x in t, (s.indicator fun _ : α => (1 : ℝ)) x ∂μ := by
            rw [← setIntegral_indicator hs₀]
  · have hmk_toReal : AEStronglyMeasurable[m] (fun x => (hgm.mk g x).toReal) μ :=
      (stronglyMeasurable_iff_measurable.2
        (Measurable.ennreal_toReal hgm.stronglyMeasurable_mk.measurable)).aestronglyMeasurable
    exact hmk_toReal.congr (EventuallyEq.fun_comp hgm.ae_eq_mk ENNReal.toReal).symm

lemma toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α} (hs₀ : MeasurableSet s) (hs : μ s ≠ ⊤)
    (hgm : AEStronglyMeasurable[m] g μ) (hae : ∀ᵐ x ∂μ, g x < ∞) :
    (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] ↔
      ∀ t, MeasurableSet[m] t → μ (s ∩ t) = ∫⁻ a in t, g a ∂μ := by
  let S : ℕ → Set α := spanningSets (μ.trim hm)
  have hSmeas (i : ℕ) : MeasurableSet[m] (S i) := measurableSet_spanningSets (μ := μ.trim hm) i
  have hSfin (i : ℕ) : μ (S i) < ∞ := by
    rw [← trim_measurableSet_eq hm (hSmeas i)]
    exact measure_spanningSets_lt_top (μ.trim hm) i
  have h_int_ind : Integrable (s.indicator fun _ : α => (1 : ℝ)) μ := by
    refine (integrable_indicator_iff hs₀).2 ?_
    rw [IntegrableOn]
    have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs
    exact integrable_const (μ := μ.restrict s) (c := (1 : ℝ))
  have hintg (h : (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m]) :
      Integrable (fun a ↦ (g a).toReal) μ :=
    (integrable_congr h).mpr
      (integrable_condExp (μ := μ) (m := m) (m₀ := m0) (f := s.indicator fun _ : α => (1 : ℝ)))
  constructor
  · intro h t ht
    have ht0 : MeasurableSet t := hm _ ht
    have hunion : ⋃ i : ℕ, t ∩ S i = t := by
      rw [← inter_iUnion, iUnion_spanningSets (μ := μ.trim hm), inter_univ]
    have hdir : Directed (· ⊆ ·) fun i : ℕ => t ∩ S i := by
      intro i j
      refine ⟨max i j, ?_, ?_⟩
      · exact inter_subset_inter_right t (spanningSets_mono (μ := μ.trim hm) (le_max_left i j))
      · exact inter_subset_inter_right t (spanningSets_mono (μ := μ.trim hm) (le_max_right i j))
    have mono_sts : Monotone fun i : ℕ => s ∩ t ∩ S i := fun i j hij =>
      inter_subset_inter_right (s ∩ t) (spanningSets_mono (μ := μ.trim hm) hij)
    have h_fin (u : Set α) (hum : MeasurableSet[m] u) (hμu : μ u < ∞) :
        μ (s ∩ u) = ∫⁻ a in u, g a ∂μ := by
      have hu0 : MeasurableSet u := hm _ hum
      have hμ_inter_ne : μ (s ∩ u) ≠ ∞ :=
        ne_top_of_le_ne_top hμu.ne (measure_mono inter_subset_right)
      have h1 : ∫ x in u, (g x).toReal ∂μ = μ.real (s ∩ u) := by
        calc
          ∫ x in u, (g x).toReal ∂μ
              = ∫ x in u, μ[s.indicator 1|m] x ∂μ :=
                setIntegral_congr_ae hu0 (h.mono fun x hx _ => hx)
          _ = ∫ x in u, (s.indicator fun _ : α => (1 : ℝ)) x ∂μ :=
                setIntegral_condExp hm h_int_ind hum
          _ = μ.real (s ∩ u) := by
                rw [setIntegral_indicator hs₀, setIntegral_const, smul_eq_mul, mul_one]
                exact congr_arg μ.real (inter_comm u s)
      have hint_u : Integrable (fun a ↦ (g a).toReal) (μ.restrict u) :=
        (hintg h).restrict (s := u)
      have h2 := ofReal_integral_eq_lintegral_ofReal hint_u
          (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      rw [h1, ofReal_measureReal hμ_inter_ne] at h2
      have h3 : ∫⁻ x in u, ENNReal.ofReal ((g x).toReal) ∂μ = ∫⁻ x in u, g x ∂μ := by
        refine setLIntegral_congr_fun_ae hu0 ?_
        filter_upwards [hae] with x hx
        intro hxu
        exact ENNReal.ofReal_toReal (LT.lt.ne_top hx)
      rw [h3] at h2
      exact h2
    calc
      μ (s ∩ t) = μ (⋃ i : ℕ, s ∩ (t ∩ S i)) := by
            rw [← inter_iUnion, hunion]
      _ = μ (⋃ i : ℕ, s ∩ t ∩ S i) := by simp_rw [← inter_assoc]
      _ = ⨆ i : ℕ, μ (s ∩ t ∩ S i) := mono_sts.measure_iUnion
      _ = ⨆ i : ℕ, ∫⁻ a in t ∩ S i, g a ∂μ :=
            iSup_congr fun i =>
              (inter_assoc s t (S i)).symm ▸
                h_fin (t ∩ S i) (ht.inter (hSmeas i))
                  ((measure_mono inter_subset_right).trans_lt (hSfin i))
      _ = ∫⁻ a in ⋃ i : ℕ, t ∩ S i, g a ∂μ := (setLIntegral_iUnion_of_directed g hdir).symm
      _ = ∫⁻ a in t, g a ∂μ := by rw [hunion]
  · intro hfg
    refine toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq hm hs₀ hs
      (fun t ht hμt => ?_) ?_ hgm
    · rw [← hfg t ht]
      exact ((measure_mono inter_subset_right).trans_lt hμt).ne
    · intro t ht hμt
      rw [hfg t ht]

end MeasureTheory
