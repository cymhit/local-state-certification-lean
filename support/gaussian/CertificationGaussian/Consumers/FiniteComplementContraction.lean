import CertificationGaussian.FiniteComplementContraction

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace CertificationGaussian.Consumers

/-- Arbitrary signed kernels over the real product Haar records, with every analytic hypothesis supplied. -/
theorem actual_haar_finite_complement {S K : Type*} [Fintype S] [DecidableEq S] [Fintype K]
    (d : ℕ) [NeZero d] (hd : 3≤d) (r : ℕ)
    (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementGaussianFourthIntegrand d id A c x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => haarBasisRecords d)))‖ ≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (∑ k,|c k|)^8*(haarLocalKappa d)^(Fintype.card S-8*r) :=
  finiteComplementHaarGaussianFourthIntegral_bound d hd r A hA c

/-- Repeated complements and a zero coefficient are retained as separate labelled terms. -/
def repeatedComplements : Fin 3 → Finset (Fin 8) := ![{0},{0},{1}]
def signedComplementWeights : Fin 3 → ℝ := ![-2,3,0]

theorem repeatedComplements_order (k : Fin 3) : (repeatedComplements k).card≤1 := by
  fin_cases k <;> simp [repeatedComplements]

theorem signedComplementWeights_mass : (∑ k,|signedComplementWeights k|)=5 := by
  norm_num [signedComplementWeights,Fin.sum_univ_succ]

/-- Actual signed/zero/repeated coefficient consumer at n=8r, under the six-record product ensemble. -/
theorem actual_signed_repeated_pauli :
    ‖((2:ℂ)^8)^4*(∫ x,finiteComplementGaussianFourthIntegrand 2 pauliFullRecord
      repeatedComplements signedComplementWeights x
        ∂fourReadoutLaw (Measure.pi (fun _ : Fin 8 => pauliBasisRecords)))‖ ≤
      (Nat.factorial 8:ℝ)*(16:ℝ)^8*5^8 := by
  have h := finiteComplementPauliGaussianFourthIntegral_bound 1 repeatedComplements
    repeatedComplements_order signedComplementWeights
  simpa only [Fintype.card_fin,signedComplementWeights_mass,show 8*1=8 by decide,
    Nat.sub_self,pow_zero,mul_one] using h

/-- With no physical sites the true global coordinate space is still one-dimensional, and the normalized bound remains valid. -/
theorem empty_physical_sites :
    ‖(∫ x,finiteComplementGaussianFourthIntegrand 3 id
      (fun _ : Fin 1 => (∅ : Finset (Fin 0))) (fun _ => 1) x
        ∂fourReadoutLaw (Measure.pi (fun _ : Fin 0 => haarBasisRecords 3)))‖≤(Nat.factorial 8:ℝ) := by
  have h := finiteComplementHaarGaussianFourthIntegral_bound 3 (by decide) 0
    (fun _ : Fin 1 => (∅ : Finset (Fin 0))) (by simp) (fun _ => 1)
  simpa using h

/-- An empty coefficient family gives zero actual Gaussian/readout contraction, not merely a vacuous local premise. -/
theorem empty_coefficient_family :
    (∫ x,finiteComplementGaussianFourthIntegrand 2 pauliFullRecord
      (fun k : Fin 0 => k.elim0) (fun k : Fin 0 => k.elim0) x
        ∂fourReadoutLaw (Measure.pi (fun _ : Fin 2 => pauliBasisRecords)))=0 := by
  have h := finiteComplementPauliGaussianFourthIntegral_bound 0
    (fun k : Fin 0 => (k.elim0 : Finset (Fin 2))) (fun k => k.elim0)
    (fun k : Fin 0 => k.elim0)
  norm_num at h
  apply norm_eq_zero.mp
  apply le_antisymm
  · linarith
  · exact norm_nonneg _

end CertificationGaussian.Consumers
