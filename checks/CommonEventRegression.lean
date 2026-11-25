import LocalCertification.Paper
import LocalCertification.Quantum.MeasurableNearCriticalEvent

open MeasureTheory Matrix Metric Set Filter LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal ComplexOrder Topology
noncomputable section
namespace NearCriticalEventExamples

def uniformInterval : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
instance : IsProbabilityMeasure uniformInterval where
  measure_univ := by simp [uniformInterval]
def locals (n : ℕ) : Fin n → MeasurablePOVM ℝ (Fin 2) :=
  fun _ => MeasurablePOVM.ofProbability uniformInterval

-- The lower adjacent degree is truly zero when j=1; the same nonfinite product measurement is used.
example : ∃ Cj Cp : ℝ, 0 < Cj ∧ 0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
    ∃ (hNj : (quditDualCertificate (by decide : 2 ≤ 2) 1).maxNode ≤ n)
      (hNp : (quditDualCertificate (by decide : 2 ≤ 2) 0).maxNode ≤ n)
      (good : Set (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex 2 n)) 1)),
    IsCompact good ∧ ∀ ψ ∈ good,
      ∃ (hlj : uncalibratedLowFidelity (by decide : 2 ≤ 2) 1 (spherePureVector ψ) hNj < (1/2:ℝ))
        (hlp : uncalibratedLowFidelity (by decide : 2 ≤ 2) 0 (spherePureVector ψ) hNp < (1/2:ℝ)),
      (∫ s, ((MeasurablePOVM.product (locals n)).bornDensity
        (calibratedHighState (by decide : 2 ≤ 2) 0 (spherePureVector ψ) hNp (1/2) (by norm_num) (by norm_num)) s -
        (MeasurablePOVM.product (locals n)).bornDensity
        (calibratedLowState (by decide : 2 ≤ 2) 0 (spherePureVector ψ) hNp (1/2) (by norm_num) (by norm_num) hlp) s)^2
        ∂(MeasurablePOVM.product (locals n)).traceReference) ≤ Cp/(n:ℝ) := by
  obtain ⟨Cj,Cp,hCj,hCp,h⟩ := measurableNearCritical_positive_eventually
    (by decide : 2 ≤ 2) 1 (by decide) (1/2) (by norm_num) (by norm_num)
  refine ⟨Cj,Cp,hCj,hCp,?_⟩
  filter_upwards [h] with n hn
  obtain ⟨hNj,hNp,good,hcompact,_,hp⟩ := hn
  refine ⟨hNj,hNp,good,hcompact,?_⟩
  intro ψ hψ
  obtain ⟨hlj,hlp,hinfo⟩ := hp ψ hψ
  exact ⟨hlj,hlp,by simpa only [pow_one] using (hinfo (fun _ => ℝ) (locals n)).2⟩

-- Zero degree supplies pure-minus-one, not the degree-zero residual kernel.
example : ∃ C0 Cp : ℝ, 0 < C0 ∧ 0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
    ∃ (good : Set (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex 2 n)) 1)),
    IsCompact good ∧ ∀ ψ ∈ good,
      (∫ s, ((MeasurablePOVM.product (locals n)).bornDensity (spherePureVector ψ).state s-1)^2
        ∂(MeasurablePOVM.product (locals n)).traceReference) ≤ Cp := by
  obtain ⟨C0,Cp,hC0,hCp,h⟩ := measurableNearCritical_zero_eventually
    (by decide : 2 ≤ 2) (1/2) (by norm_num) (by norm_num)
  refine ⟨C0,Cp,hC0,hCp,?_⟩
  filter_upwards [h] with n hn
  obtain ⟨hN,good,hcompact,_,hp⟩ := hn
  refine ⟨good,hcompact,?_⟩
  intro ψ hψ
  obtain ⟨hlb,hinfo⟩ := hp ψ hψ
  exact (hinfo (fun _ => ℝ) (locals n)).2

example : Tendsto (fun n : ℕ => ENNReal.ofReal (measurableNearCriticalFailure 2 0 n)) atTop (nhds 0) :=
  measurableNearCriticalFailure_ofReal_tendsto (by decide : 2 ≤ 2) 0
end NearCriticalEventExamples

#eval IO.println "CommonEventRegression_PASS"
