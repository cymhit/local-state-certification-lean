import CertificationGaussian.CompleteMUBReadoutControl
import CertificationGaussian.ReadoutRemainderAsymptotics

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {d : ℕ} [NeZero d] (B : CompleteMUB d)
variable {S K : Type*} [Fintype S] [DecidableEq S] [Fintype K]

theorem completeMUBProductRecordWickContraction_le (hd : 2≤d)
    (A : Fin 4 × Fin 2 → Finset S) (π : Equiv.Perm (Fin 4 × Fin 2))
    (hπ : π∈fourBlockDerangements) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,productRecordWickIntegrand d (completeMUBFullRecord B) A π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => completeMUBRecords d)))‖≤
      ((d:ℝ)^4*((d:ℝ)-1)^8)^(eightComplementUnion A).card*
        (completeMUBLocalKappa d)^(Fintype.card S-(eightComplementUnion A).card) := by
  rw [productRecordWickIntegral_eq_prod]
  apply finite_site_cost_bound (eightComplementUnion A)
  intro s
  split_ifs with hs
  · exact completeMUBChangedSiteContraction_le B hd _ π
  · rw [eightComplementUnion_outside A s hs]
    exact completeMUBUnchangedSiteContraction_le B hd π hπ

theorem completeMUBProductRecordWickContraction_uniform (hd : 2≤d)
    (r : ℕ) (A : Fin 4 × Fin 2 → Finset S) (hA : ∀ t,(A t).card≤r)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π∈fourBlockDerangements) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,productRecordWickIntegrand d (completeMUBFullRecord B) A π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => completeMUBRecords d)))‖≤
      ((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*(completeMUBLocalKappa d)^(Fintype.card S-8*r) := by
  have hdR : (2:ℝ)≤d := by exact_mod_cast hd
  have hC1 : (1:ℝ)≤(d:ℝ)^4 := one_le_pow₀ (by linarith)
  have hC2 : (1:ℝ)≤((d:ℝ)-1)^8 := one_le_pow₀ (by linarith)
  have hC : (1:ℝ)≤(d:ℝ)^4*((d:ℝ)-1)^8 := one_le_mul_of_one_le_of_one_le hC1 hC2
  exact (completeMUBProductRecordWickContraction_le B hd A π hπ).trans
    (finite_site_cost_le_uniform _ _ hC completeMUBLocalKappa_pos.le
      (completeMUBLocalKappa_lt_one hd).le _ _ _ (eightComplementUnion_card_le A r hA))

theorem finiteComplementMUBWickIntegral_bound (hd : 2≤d)
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π∈fourBlockDerangements) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementWickIntegrand d (completeMUBFullRecord B) A c π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => completeMUBRecords d)))‖≤
      (∑ k,|c k|)^8*(((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (completeMUBLocalKappa d)^(Fintype.card S-8*r)) :=
  finiteComplementWickIntegral_bound (completeMUBRecords d) d (completeMUBFullRecord B)
    continuous_of_discreteTopology A c π _
    (fun q => completeMUBProductRecordWickContraction_uniform B hd r (fun t => A (q t))
      (fun t => hA (q t)) π hπ)

theorem finiteComplementMUBGaussianFourthIntegral_bound (hd : 2≤d)
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementGaussianFourthIntegrand d (completeMUBFullRecord B) A c x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => completeMUBRecords d)))‖≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (∑ k,|c k|)^8*(completeMUBLocalKappa d)^(Fintype.card S-8*r) := by
  rw [finiteComplementGaussianFourthIntegral_eq_sum (completeMUBRecords d) d
    (completeMUBFullRecord B) continuous_of_discreteTopology]
  have hκ := completeMUBLocalKappa_pos (d:=d)
  have hE : 0≤(∑ k,|c k|)^8*(((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
      (completeMUBLocalKappa d)^(Fintype.card S-8*r)) := by positivity
  have h := fourBlockWick_sum_norm_le _ _ hE
    (fun π hπ => finiteComplementMUBWickIntegral_bound B hd r A hA c π hπ)
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- The actual Z, with the Gaussian expectation now outside its true full-record Bochner integral. -/
theorem finiteComplementMUB_remainder_norm_bound (hd : 2≤d)
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    ‖∫ z,Matrix.trace ((finiteComplementRemainder d (completeMUBRecords d) (completeMUBFullRecord B)
      A c (complexCoordinate z))^4)∂pairedGaussian (S → Fin d)‖≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (∑ k,|c k|)^8*(completeMUBLocalKappa d)^(Fintype.card S-8*r) := by
  rw [finiteComplementRemainder_fourth_expectation d (completeMUBRecords d)
    (completeMUBFullRecord B) continuous_of_discreteTopology]
  exact finiteComplementMUBGaussianFourthIntegral_bound B hd r A hA c

theorem finiteComplementMUB_remainder_bound (hd : 2≤d)
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    (∫ z,(Matrix.trace ((finiteComplementRemainder d (completeMUBRecords d) (completeMUBFullRecord B)
      A c (complexCoordinate z))^4)).re∂pairedGaussian (S → Fin d))≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (∑ k,|c k|)^8*(completeMUBLocalKappa d)^(Fintype.card S-8*r) := by
  exact (integral_re (finiteComplementRemainder_fourth_integrable d (completeMUBRecords d)
    (completeMUBFullRecord B) continuous_of_discreteTopology A c)).trans_le
      ((Complex.re_le_norm _).trans (finiteComplementMUB_remainder_norm_bound B hd r A hA c))

/-- Original cardinality coefficients, including their signed Lambda mass, on the actual MUB records. -/
theorem cardinalityMUB_remainder_bound (hd : 2≤d) (r : ℕ) (lam : ℕ → ℝ) :
    (∫ z,(Matrix.trace ((cardinalityReadoutRemainder (S:=S) d (completeMUBRecords d)
      (completeMUBFullRecord B) r lam (complexCoordinate z))^4)).re∂pairedGaussian (S → Fin d))≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (complementLambda d (Fintype.card S) r lam)^8*
          (completeMUBLocalKappa d)^(Fintype.card S-8*r) := by
  have h := finiteComplementMUB_remainder_bound B hd r (cardinalityComplementSet (S:=S) (r:=r))
    cardinalityComplementSet_order (cardinalityComplementWeight lam)
  apply h.trans
  have hm := cardinalityComplement_mass_le_Lambda (S:=S) d hd r lam
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hm 8
  have hκ := completeMUBLocalKappa_pos (d:=d)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)

theorem cardinalityMUB_remainder_tail (hd : 2≤d) (n r : ℕ) (lam : ℕ → ℝ) (t : ℝ) (ht : 0<t) :
    pairedGaussian (QuditIndex d n) {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B)
        r lam (complexCoordinate x))‖}≤
      ENNReal.ofReal ((Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (complementLambda d n r lam)^8*(completeMUBLocalKappa d)^(n-8*r)/t^4) := by
  let : IsProbabilityMeasure (pairedGaussian (QuditIndex d n)) := by unfold pairedGaussian; infer_instance
  have h := hermitian_fourth_trace_markov (pairedGaussian (QuditIndex d n)) _
    (fun x => cardinalityReadoutRemainder_isHermitian d (completeMUBRecords d) (completeMUBFullRecord B)
      continuous_of_discreteTopology r lam (complexCoordinate x))
    (finiteComplementRemainder_fourth_integrable d (completeMUBRecords d) (completeMUBFullRecord B)
      continuous_of_discreteTopology (cardinalityComplementSet (S:=Fin n) (r:=r))
        (cardinalityComplementWeight lam)).re t ht
  exact h.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (by simpa only [Fintype.card_fin] using
      cardinalityMUB_remainder_bound (S:=Fin n) B hd r lam) (by positivity)))

theorem cardinalityMUB_remainder_tail_n_inv_three (hd : 2≤d) (n r : ℕ) (hn : 0<n)
    (lam : ℕ → ℝ) :
    pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B)
        r lam (complexCoordinate x))‖}≤
      ENNReal.ofReal ((n:ℝ)^12*(Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (complementLambda d n r lam)^8*(completeMUBLocalKappa d)^(n-8*r)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := cardinalityMUB_remainder_tail B hd n r lam ((n:ℝ)^3)⁻¹ (by positivity)
  convert h using 1
  congr 1
  rw [div_eq_mul_inv,← inv_pow,inv_inv,← pow_mul]
  norm_num
  ring

/-- No moment or contraction hypothesis remains: the same actual remainder event decays exponentially. -/
theorem cardinalityMUB_remainder_eventually_exponential (hd : 2≤d) (r : ℕ) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
    pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B)
        r lam (complexCoordinate x))‖}≤
      ENNReal.ofReal (Real.exp ((Real.log (completeMUBLocalKappa d)/2)*n)) := by
  have hp := eventually_remainder_prefactor d r (by omega) lam
    (C:=(Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)) (by positivity)
    completeMUBLocalKappa_pos (completeMUBLocalKappa_lt_one hd)
  filter_upwards [hp,eventually_ge_atTop 1] with n hn hn1
  exact (cardinalityMUB_remainder_tail_n_inv_three B hd n r (by omega) lam).trans
    (ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using hn))

end CertificationGaussian
