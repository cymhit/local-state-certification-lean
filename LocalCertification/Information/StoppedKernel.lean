import LocalCertification.Information.SingularFiniteKL
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/- Stopping labels and stopped kernels. The joint entropy bound includes the singular case without assuming conditional absolute continuity. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal Classical
namespace LocalCertification.Information
universe u v
section Labels

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]

theorem klDiv_map_retract (F : X → Y) (G : Y → X)
    (hF : Measurable F) (hG : Measurable G)
    (hGF : Function.LeftInverse G F) :
    klDiv (P.map F) (Q.map F) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q hF)
  have hP : (P.map F).map G = P := by
    rw [Measure.map_map hG hF, show G ∘ F = id from funext hGF, Measure.map_id]
  have hQ : (Q.map F).map G = Q := by
    rw [Measure.map_map hG hF, show G ∘ F = id from funext hGF, Measure.map_id]
  have h := klDiv_map_le (P.map F) (Q.map F) hG
  simpa [hP, hQ] using h

theorem klDiv_add_common_label (label : X → Y) (hl : Measurable label) :
    klDiv (P.map (fun x => (x, label x)))
      (Q.map (fun x => (x, label x))) = klDiv P Q :=
  klDiv_map_retract P Q _ Prod.fst (measurable_id.prodMk hl)
    measurable_fst (fun _ => rfl)

theorem common_initial_flag_kl (μ : Measure X) [IsFiniteMeasure μ]
    (flag : X → Y) (hf : Measurable flag) :
    klDiv (μ.map (fun x => (x, flag x)))
      (μ.map (fun x => (x, flag x))) = 0 := by
  rw [klDiv_add_common_label μ μ flag hf, klDiv_self]

end Labels

variable {O : Type u} [MeasurableSpace O] [Fintype O]
  [MeasurableSingletonClass O] [Nonempty O]

/-- The finite stopped-record space has the full sigma algebra, only when this scope is opened. -/
scoped instance optionMeasurableSpace (O : Type u) [Fintype O] : MeasurableSpace (Option O) := ⊤

theorem klDiv_map_some (P Q : Measure O)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    klDiv (P.map Option.some) (Q.map Option.some) = klDiv P Q := by
  classical
  exact klDiv_map_retract P Q Option.some
    (fun x : Option O => x.getD (Classical.choice inferInstance))
    (measurable_of_countable _) (measurable_of_countable _) (fun _ => rfl)

variable {H : Type v} [MeasurableSpace H]

def stopContinue (s : Set H) (hs : MeasurableSet s) (κ : Kernel H O) :
    Kernel H (Option O) := by
  classical
  exact Kernel.piecewise hs (κ.map Option.some)
    (Kernel.const H (Measure.dirac none))

instance stopContinue_isMarkov (s : Set H) (hs : MeasurableSet s)
    (κ : Kernel H O) [IsMarkovKernel κ] :
    IsMarkovKernel (stopContinue s hs κ) := by
  let := Kernel.IsMarkovKernel.map κ (measurable_of_countable Option.some)
  unfold stopContinue
  infer_instance

omit [Nonempty O] in
theorem stopContinue_apply (s : Set H) (hs : MeasurableSet s)
    (κ : Kernel H O) (h : H) :
    stopContinue s hs κ h =
      if h ∈ s then (κ h).map Option.some else Measure.dirac none := by
  classical
  simp only [stopContinue, Kernel.piecewise_apply,
    Kernel.map_apply _ (measurable_of_countable Option.some), Kernel.const_apply]

theorem stopContinue_kl (s : Set H) (hs : MeasurableSet s)
    (κ η : Kernel H O) [IsMarkovKernel κ] [IsMarkovKernel η] (h : H) :
    klDiv (stopContinue s hs κ h) (stopContinue s hs η h) =
      s.indicator (fun h => klDiv (κ h) (η h)) h := by
  classical
  by_cases hh : h ∈ s
  · simp [stopContinue_apply, hh, klDiv_map_some]
  · simp [stopContinue_apply, hh, klDiv_self]

omit [Nonempty O] in
theorem stopContinue_ac (s : Set H) (hs : MeasurableSet s)
    (κ η : Kernel H O) (μ : Measure H)
    (hAC : ∀ᵐ h ∂μ, h ∈ s → κ h ≪ η h) :
    ∀ᵐ h ∂μ, stopContinue s hs κ h ≪ stopContinue s hs η h := by
  classical
  filter_upwards [hAC] with h hh
  by_cases hmem : h ∈ s
  · simp only [stopContinue_apply, ite_eq_left hmem]
    exact (hh hmem).map (measurable_of_countable Option.some)
  · simp only [stopContinue_apply, ite_eq_right hmem]
    exact Measure.AbsolutelyContinuous.rfl

theorem stopped_joint_klDiv_le (s : Set H) (hs : MeasurableSet s)
    (κ η : Kernel H O) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure H) [IsProbabilityMeasure μ] (L : ℝ≥0∞)
    (hL : ∀ᵐ h ∂μ, h ∈ s → klDiv (κ h) (η h) ≤ L) :
    klDiv (μ ⊗ₘ stopContinue s hs κ) (μ ⊗ₘ stopContinue s hs η) ≤ L * μ s := by
  rw [joint_klDiv_eq_lintegral_full]
  calc
    (∫⁻ h, klDiv (stopContinue s hs κ h) (stopContinue s hs η h) ∂μ) ≤
        ∫⁻ h, s.indicator (fun _ => L) h ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hL] with h hh
      rw [stopContinue_kl]
      by_cases hmem : h ∈ s
      · simpa [hmem] using hh hmem
      · simp [hmem]
    _ = L * μ s := lintegral_indicator_const hs L

end LocalCertification.Information
