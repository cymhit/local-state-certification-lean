import CertificationGaussian.CompleteMUBGraphIntegrals

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian
variable {d : ℕ} [NeZero d]

def completeMUBAmplitude (d : ℕ) : ℝ := (Real.sqrt d)⁻¹

omit [NeZero d] in
theorem completeMUBAmplitude_sq :
    completeMUBAmplitude d^2=(d:ℝ)⁻¹ := by
  rw [completeMUBAmplitude,inv_pow,Real.sq_sqrt (Nat.cast_nonneg d)]

omit [NeZero d] in
theorem completeMUBAmplitude_sixth :
    completeMUBAmplitude d^6=((d:ℝ)⁻¹)^3 := by
  calc
    _ = (completeMUBAmplitude d^2)^3 := by ring
    _ = _ := by rw [completeMUBAmplitude_sq]

/-- The original strict-loss constant in a factorized, manifestly positive form. -/
def completeMUBStrictLoss (d : ℕ) : ℝ :=
  ((d:ℝ)^2+1)*(1-completeMUBAmplitude d)/((d:ℝ)^3*(d+1))

def completeMUBLocalKappa (d : ℕ) : ℝ :=
  1-completeMUBStrictLoss d/((d:ℝ)^2*(d+1)^3)

theorem completeMUBAmplitude_pos : 0<completeMUBAmplitude d := by
  unfold completeMUBAmplitude
  exact inv_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos d))

omit [NeZero d] in
theorem completeMUBAmplitude_lt_one (hd : 2≤d) : completeMUBAmplitude d<1 := by
  have hdR : (1:ℝ)<d := by exact_mod_cast (show 1<d by omega)
  have hs : 1<Real.sqrt (d:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),Real.sqrt_nonneg (d:ℝ)]
  exact (inv_lt_one₀ (lt_trans zero_lt_one hs)).2 hs

theorem completeMUBStrictLoss_pos (hd : 2≤d) : 0<completeMUBStrictLoss d := by
  have hp := completeMUBAmplitude_lt_one hd
  have hdR : (0:ℝ)<d := by exact_mod_cast NeZero.pos d
  unfold completeMUBStrictLoss
  positivity

theorem completeMUBStrictLoss_original :
    completeMUBStrictLoss d=((d:ℝ)⁻¹)^2-
      (completeMUBAmplitude d+completeMUBAmplitude d^5+(d-1:ℝ)*((d:ℝ)⁻¹)^2)/
        ((d:ℝ)*(d+1)) := by
  have hd : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
  have hq : (d+1:ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero d
  have ht5 : completeMUBAmplitude d^5=completeMUBAmplitude d*((d:ℝ)⁻¹)^2 := by
    calc
      _ = completeMUBAmplitude d*(completeMUBAmplitude d^2)^2 := by ring
      _ = _ := by rw [completeMUBAmplitude_sq]
  rw [ht5]
  unfold completeMUBStrictLoss
  field_simp
  ring

theorem completeMUBStrictLoss_lt_second : completeMUBStrictLoss d<((d:ℝ)⁻¹)^2 := by
  rw [completeMUBStrictLoss_original]
  have hp := completeMUBAmplitude_pos (d:=d)
  have hd : (1:ℝ)≤d := by exact_mod_cast NeZero.pos d
  have hpos : 0<(completeMUBAmplitude d+completeMUBAmplitude d^5+
      (d-1:ℝ)*((d:ℝ)⁻¹)^2)/((d:ℝ)*(d+1)) := by positivity
  linarith

def completeMUBMixedSixth (B : CompleteMUB d) (a b : CompleteMUBRecord d) (k : ℕ) : ℝ :=
  ∫ s,recordOverlap (completeMUBUnitVector B) s a^(6-k)*
    recordOverlap (completeMUBUnitVector B) s b^k∂completeMUBRecords d

theorem completeMUBMixedSixth_formula (B : CompleteMUB d)
    (a b : CompleteMUBRecord d) (hab : a.1≠b.1) (k : ℕ) (hk : 1≤k) (hk5 : k≤5) :
    completeMUBMixedSixth B a b k=
      (completeMUBAmplitude d^k+completeMUBAmplitude d^(6-k)+
        (d-1:ℝ)*((d:ℝ)⁻¹)^2)/((d:ℝ)*(d+1)) := by
  have hk0 : k≠0 := by omega
  have hk60 : 6-k≠0 := by omega
  have hs (c : Fin (d+1)) :
      (∑ j : Fin d,recordOverlap (completeMUBUnitVector B) (c,j) a^(6-k)*
        recordOverlap (completeMUBUnitVector B) (c,j) b^k)=
        if c=a.1 then completeMUBAmplitude d^k else
        if c=b.1 then completeMUBAmplitude d^(6-k) else ((d:ℝ)⁻¹)^2 := by
    simp_rw [completeMUB_overlap]
    by_cases hca : c=a.1
    · subst c
      simp [hab,hk60,completeMUBAmplitude]
    · by_cases hcb : c=b.1
      · subst c
        simp [Ne.symm hab,hk0,completeMUBAmplitude]
      · simp only [hca,hcb,ite_false]
        have he : (Real.sqrt (d:ℝ))⁻¹^(6-k)*(Real.sqrt (d:ℝ))⁻¹^k=
            ((d:ℝ)⁻¹)^3 := by
          rw [← pow_add,Nat.sub_add_cancel (by omega)]
          exact completeMUBAmplitude_sixth
        rw [he]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hd0 : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
        field_simp
  unfold completeMUBMixedSixth
  rw [completeMUBRecords_integral]
  simp_rw [hs]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a.1)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b.1⟩)]
  have her : (∑ c∈(Finset.univ.erase a.1).erase b.1,
      if c=a.1 then completeMUBAmplitude d^k else
      if c=b.1 then completeMUBAmplitude d^(6-k) else ((d:ℝ)⁻¹)^2)=
      (d-1:ℝ)*((d:ℝ)⁻¹)^2 := by
    calc
      _ = ∑ c∈(Finset.univ.erase a.1).erase b.1,((d:ℝ)⁻¹)^2 := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [ite_eq_right (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)),
          ite_eq_right (Finset.ne_of_mem_erase hc)]
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_erase.mpr
          ⟨Ne.symm hab,Finset.mem_univ b.1⟩),Finset.card_erase_of_mem (Finset.mem_univ a.1),
          Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel,nsmul_eq_mul]
        rw [Nat.cast_sub (NeZero.pos d)]
        norm_num
  rw [her]
  simp only [eq_self,ite_true,ite_eq_right (Ne.symm hab)]
  ring


theorem completeMUBMixedSixth_strict_loss (B : CompleteMUB d) (hd : 2≤d)
    (a b : CompleteMUBRecord d) (hab : a.1≠b.1) (k : ℕ) (hk : 1≤k) (hk5 : k≤5) :
    completeMUBMixedSixth B a b k≤((d:ℝ)⁻¹)^2-completeMUBStrictLoss d := by
  let t := completeMUBAmplitude d
  have ht0 : 0≤t := (completeMUBAmplitude_pos (d:=d)).le
  have ht1 : t≤1 := (completeMUBAmplitude_lt_one hd).le
  have ht3 : t^3≤1 := pow_le_one₀ ht0 ht1
  have h2 : t^2+t^4≤t+t^5 := by
    nlinarith [mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sub_nonneg.mpr ht3)]
  have h3 : 2*t^3≤t+t^5 := by
    nlinarith [mul_nonneg ht0 (sq_nonneg (1-t^2))]
  have hp : t^k+t^(6-k)≤t+t^5 := by
    interval_cases k <;> norm_num <;> linarith
  have hden : 0<(d:ℝ)*(d+1) := by
    have hdR : (0:ℝ)<d := by exact_mod_cast NeZero.pos d
    positivity
  calc
    _ = (t^k+t^(6-k)+(d-1:ℝ)*((d:ℝ)⁻¹)^2)/((d:ℝ)*(d+1)) :=
      completeMUBMixedSixth_formula B a b hab k hk hk5
    _ ≤ (t+t^5+(d-1:ℝ)*((d:ℝ)⁻¹)^2)/((d:ℝ)*(d+1)) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    _ = _ := by rw [completeMUBStrictLoss_original]; ring

theorem completeMUBLocalKappa_pos : 0<completeMUBLocalKappa d := by
  have hd : (1:ℝ)≤d := by exact_mod_cast NeZero.pos d
  have hdi : 0≤(d:ℝ)⁻¹ := inv_nonneg.2 (by linarith)
  have hdi1 : (d:ℝ)⁻¹≤1 := (inv_le_one₀ (by linarith)).2 hd
  have hsecond : ((d:ℝ)⁻¹)^2≤1 := pow_le_one₀ hdi hdi1
  have h2 : (1:ℝ)≤(d:ℝ)^2 := one_le_pow₀ hd
  have h3 : (1:ℝ)≤(d+1:ℝ)^3 := one_le_pow₀ (by linarith)
  have hden : 0<(d:ℝ)^2*(d+1)^3 := by positivity
  have hl : completeMUBStrictLoss d<(d:ℝ)^2*(d+1)^3 := by
    have hb := completeMUBStrictLoss_lt_second (d:=d)
    nlinarith [mul_le_mul h2 h3 (by norm_num) (by positivity)]
  unfold completeMUBLocalKappa
  have hh := (div_lt_one hden).2 hl
  linarith

theorem completeMUBLocalKappa_lt_one (hd : 2≤d) : completeMUBLocalKappa d<1 := by
  have hb := completeMUBStrictLoss_pos hd
  have hdR : (0:ℝ)<d := by exact_mod_cast NeZero.pos d
  have hh : 0<completeMUBStrictLoss d/((d:ℝ)^2*(d+1)^3) := by positivity
  unfold completeMUBLocalKappa
  linarith


end CertificationGaussian
