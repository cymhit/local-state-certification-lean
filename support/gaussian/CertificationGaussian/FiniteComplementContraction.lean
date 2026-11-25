import CertificationGaussian.FiniteComplementExpansion

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace CertificationGaussian
variable {S K : Type*} [Fintype S] [DecidableEq S] [Fintype K]

/-- Every actual Haar Wick integral of the signed finite-complement kernel has the exact eighth-power coefficient cost. -/
theorem finiteComplementHaarWickIntegral_bound (d : ℕ) [NeZero d] (hd : 3≤d)
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π∈fourBlockDerangements) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementWickIntegrand d id A c π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => haarBasisRecords d)))‖ ≤
      (∑ k,|c k|)^8*(((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (haarLocalKappa d)^(Fintype.card S-8*r)) :=
  finiteComplementWickIntegral_bound (haarBasisRecords d) d id continuous_id A c π _
    (fun q => haarProductRecordWickContraction_uniform d hd r (fun t => A (q t))
      (fun t => hA (q t)) π hπ)

/-- Every actual Pauli Wick integral of the signed finite-complement kernel uses the same fixed six-record law. -/
theorem finiteComplementPauliWickIntegral_bound
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π∈fourBlockDerangements) :
    ‖((2:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementWickIntegrand 2 pauliFullRecord A c π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => pauliBasisRecords)))‖ ≤
      (∑ k,|c k|)^8*((16:ℝ)^(8*r)*pauliLocalKappa^(Fintype.card S-8*r)) :=
  finiteComplementWickIntegral_bound pauliBasisRecords 2 pauliFullRecord continuous_of_discreteTopology A c π _
    (fun q => pauliProductRecordWickContraction_uniform r (fun t => A (q t))
      (fun t => hA (q t)) π hπ)

/-- The genuine Gaussian/readout contraction for full Haar product records satisfies the paper's finite-complement bound.
This statement keeps the Gaussian expectation inside the four-record integral; the Z^4/Fubini identification is separate. -/
theorem finiteComplementHaarGaussianFourthIntegral_bound (d : ℕ) [NeZero d] (hd : 3≤d)
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementGaussianFourthIntegrand d id A c x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => haarBasisRecords d)))‖ ≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (∑ k,|c k|)^8*(haarLocalKappa d)^(Fintype.card S-8*r) := by
  rw [finiteComplementGaussianFourthIntegral_eq_sum (haarBasisRecords d) d id continuous_id]
  have hκ := haarLocalKappa_pos d (by omega)
  have hE : 0≤(∑ k,|c k|)^8*(((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
      (haarLocalKappa d)^(Fintype.card S-8*r)) := by positivity
  have h := fourBlockWick_sum_norm_le _ _ hE
    (fun π hπ => finiteComplementHaarWickIntegral_bound d hd r A hA c π hπ)
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- The same genuine Gaussian/readout contraction satisfies the qubit Pauli bound with C2=16 and strict κ2. -/
theorem finiteComplementPauliGaussianFourthIntegral_bound
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    ‖((2:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementGaussianFourthIntegrand 2 pauliFullRecord A c x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => pauliBasisRecords)))‖ ≤
      (Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)*(∑ k,|c k|)^8*
        pauliLocalKappa^(Fintype.card S-8*r) := by
  have he := finiteComplementGaussianFourthIntegral_eq_sum pauliBasisRecords 2 pauliFullRecord
    continuous_of_discreteTopology A c
  norm_num only [Nat.cast_ofNat] at he
  rw [he]
  have hκ := pauliLocalKappa_pos
  have hE : 0≤(∑ k,|c k|)^8*((16:ℝ)^(8*r)*pauliLocalKappa^(Fintype.card S-8*r)) := by positivity
  have h := fourBlockWick_sum_norm_le _ _ hE
    (fun π hπ => finiteComplementPauliWickIntegral_bound r A hA c π hπ)
  calc
    _ ≤ _ := h
    _ = _ := by ring

end CertificationGaussian
