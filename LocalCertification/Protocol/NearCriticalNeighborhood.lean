import LocalCertification.Protocol.UniformNearCriticalHierarchy

/-! The open neighborhood and the two cost regimes of Corollary 2. The
threshold pair may be chosen anew at every size, after the Haar target
family, constants, and size cutoff have all been fixed. -/

set_option autoImplicit false
open MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum
open LocalCertification.Extremal LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

/-- Excess of the threshold gap over its degree-`j` critical value. -/
def criticalExcess (d j : ℕ) (x : ℝ × ℝ) : ℝ :=
  (x.1 - x.2)/(1 - x.2) - gamma ((d:ℝ)+1) j

/-- The two-sided crossover scale stated in the main text. -/
def nearCriticalCostOrder (n j : ℕ) (ε : ℝ) : ℝ :=
  if 0 < ε then min ((n:ℝ)^j / ε^2) ((n:ℝ)^(j+1)) else (n:ℝ)^(j+1)

theorem nearCriticalScale_compare_costOrder (n j : ℕ) (hn : 1 ≤ n) (ε : ℝ) :
    nearCriticalScale n j ε ≤ nearCriticalCostOrder n j ε ∧
    nearCriticalCostOrder n j ε ≤ 2 * nearCriticalScale n j ε := by
  have hx : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold nearCriticalScale nearCriticalCostOrder
  by_cases he : 0 < ε
  · rw [ite_eq_left he, max_eq_left he.le]
    let x : ℝ := n
    change x^(j+1)/(1+x*ε^2) ≤ min (x^j/ε^2) (x^(j+1)) ∧
      min (x^j/ε^2) (x^(j+1)) ≤ 2*(x^(j+1)/(1+x*ε^2))
    have hx' : 0 < x := hx
    have hpow := pow_nonneg hx'.le j
    have hs := sq_pos_of_pos he
    have hden : 0 < 1+x*ε^2 := by positivity
    constructor
    · apply le_min
      · apply (div_le_div_iff₀ hden hs).mpr
        rw [pow_succ x j]
        nlinarith only [hpow]
      · exact div_le_self (pow_nonneg hx'.le _) (by nlinarith [mul_nonneg hx'.le hs.le])
    · rw [← mul_div_assoc]
      by_cases hcross : 1 ≤ x*ε^2
      · refine (min_le_left _ _).trans ((div_le_div_iff₀ hs hden).mpr ?_)
        have h := mul_le_mul_of_nonneg_left hcross hpow
        rw [pow_succ x j]
        nlinarith only [h]
      · refine (min_le_right _ _).trans ((le_div_iff₀ hden).mpr ?_)
        have h := mul_le_mul_of_nonneg_left (le_of_not_ge hcross) (pow_nonneg hx'.le (j+1))
        nlinarith only [h]
  · rw [ite_eq_right he, max_eq_right (le_of_not_gt he)]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, div_one]
    exact ⟨le_rfl, by nlinarith [pow_nonneg hx.le (j+1)]⟩

/-- Strict rectangle in `(b,ε)`, expressed in the two fidelity thresholds. -/
def nearCriticalNeighborhood (d j : ℕ) (bmin bmax η : ℝ) : Set (ℝ × ℝ) :=
  {x | x.2 ∈ Ioo bmin bmax ∧ criticalExcess d j x ∈ Ioo (-η) η}

theorem isOpen_nearCriticalNeighborhood (d j : ℕ) (bmin bmax η : ℝ) (hmax : bmax < 1) :
    IsOpen (nearCriticalNeighborhood d j bmin bmax η) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  intro x hx
  obtain ⟨hb, he⟩ := hx
  have hden : (1:ℝ) - x.2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hb.2.trans hmax))
  have hg : ContinuousAt (criticalExcess d j) x :=
    ((continuous_fst.continuousAt.sub continuous_snd.continuousAt).div
      (continuousAt_const.sub continuous_snd.continuousAt) hden).sub continuousAt_const
  exact inter_mem (continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hb))
    (hg.preimage_mem_nhds (isOpen_Ioo.mem_nhds he))

private theorem critical_gaps_pos (d j : ℕ) (hd : 2 ≤ d) :
    0 < min
      ((if j = 0 then 1 else gamma ((d:ℝ)+1) (j-1)) - gamma ((d:ℝ)+1) j)
      (gamma ((d:ℝ)+1) j - gamma ((d:ℝ)+1) (j+1)) := by
  have hq : 1 < (d:ℝ)+1 := by exact_mod_cast (show 1 < d+1 by omega)
  apply lt_min
  · split_ifs with hj
    · exact sub_pos.mpr ((gamma_le_inverse _ hq _).trans_lt (inv_lt_one_of_one_lt₀ hq))
    · exact sub_pos.mpr (gamma_strictAnti _ hq (show j-1 < j by omega))
  · exact sub_pos.mpr (gamma_strictAnti _ hq (Nat.lt_succ_self j))

/-- Both thresholds and the confidence may vary on one open neighborhood of
the critical pair. Only the lower constant depends on the confidence cutoff. -/
theorem qudit_nearCritical_product_neighborhood_confidence (d j : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a₀ b₀ : ℝ) (hb₀ : 0 < b₀) (hb₁ : b₀ < 1)
    (hcritical : (a₀-b₀)/(1-b₀) = gamma ((d:ℝ)+1) j) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (a₀,b₀) ∈ U ∧
    (∀ x ∈ U, 0 < x.2 ∧ x.2 < x.1 ∧ x.1 < 1) ∧
    ∃ H : ℝ, 0 < H ∧
    ∃ G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      CompactHaarTypical d G ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ δstar : ℝ, 0 < δstar → δstar < 1/2 → ∃ L : ℝ, 0 < L ∧
      ∀ n, N ≤ n → ∀ ψ ∈ G n, ∀ x ∈ U, ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
        NearCriticalBudgetBounds.{u} (spherePureVector ψ) x.1 x.2 δ
          (L * nearCriticalCostOrder n j (criticalExcess d j x) * Real.log (1/δ))
          (H * nearCriticalCostOrder n j (criticalExcess d j x) * Real.log (1/δ)) := by
  let bmin := b₀/2
  let bmax := (1+b₀)/2
  have hlo : 0 < bmin := by dsimp [bmin]; linarith
  have hmid1 : bmin < b₀ := by dsimp [bmin]; linarith
  have hmid2 : b₀ < bmax := by dsimp [bmax]; linarith
  have hhi : bmax < 1 := by dsimp [bmax]; linarith
  let q : ℝ := (d:ℝ)+1
  let prev := if j = 0 then 1 else gamma q (j-1)
  let gap := min (prev - gamma q j) (gamma q j - gamma q (j+1))
  let η := gap/4
  have hg : 0 < gap := critical_gaps_pos d j hd
  have hη : 0 < η := by dsimp only [η]; positivity
  have hw : η < (1/2:ℝ)*gap := by dsimp only [η]; linarith
  let U := nearCriticalNeighborhood d j bmin bmax η
  have hx0 : (a₀,b₀) ∈ U := by
    refine ⟨⟨hmid1, hmid2⟩, ?_⟩
    simpa [criticalExcess, hcritical] using (show (0:ℝ) ∈ Ioo (-η) η from ⟨by linarith, hη⟩)
  have hq : 1 < q := by dsimp [q]; exact_mod_cast (show 1 < d+1 by omega)
  have hprev : prev ≤ 1 := by
    dsimp only [prev]
    split_ifs
    · exact le_rfl
    · exact (gamma_le_inverse _ hq _).trans (inv_le_one_of_one_le₀ hq.le)
  have hleft : gap ≤ prev-gamma q j := min_le_left _ _
  have hright : gap ≤ gamma q j-gamma q (j+1) := min_le_right _ _
  have heq (x : ℝ × ℝ) (hx : x ∈ U) :
      x.2 + (1-x.2)*(gamma q j+criticalExcess d j x) = x.1 := by
    have hne : (1:ℝ)-x.2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hx.1.2.trans hhi))
    dsimp only [criticalExcess, q]
    field_simp
    ring
  refine ⟨U, isOpen_nearCriticalNeighborhood d j bmin bmax η hhi, hx0, ?_, ?_⟩
  · intro x hx
    have hpos := gamma_pos q hq (j+1)
    have hlow : 0 < gamma q j + criticalExcess d j x := by linarith [hx.2.1]
    have hupp : gamma q j + criticalExcess d j x < 1 := by linarith [hx.2.2]
    have hb := hx.1.2.trans hhi
    have he := heq x hx
    exact ⟨hlo.trans hx.1.1, by nlinarith [mul_pos (sub_pos.mpr hb) hlow],
      by nlinarith [mul_pos (sub_pos.mpr hb) (sub_pos.mpr hupp)]⟩
  · obtain ⟨H, hH, G, hG, N, hN, cutoffs⟩ :=
      qudit_nearCritical_product_confidence_uniform.{u} d j hd bmin bmax η hlo
        (hmid1.trans hmid2).le hhi hη hw
    refine ⟨H, hH, G, hG, N, hN, ?_⟩
    intro δstar hstar hhalf
    obtain ⟨c, hc, hall⟩ := cutoffs δstar hstar hhalf
    refine ⟨c / 2, half_pos hc, ?_⟩
    intro n hn ψ hψ x hx δ hδ hcut
    have hbounds := hall n hn ψ hψ x.2 hx.1.1.le hx.1.2.le (criticalExcess d j x)
      hx.2.1.le hx.2.2.le δ hδ hcut
    change NearCriticalBudgetBounds.{u} _ (x.2 + (1-x.2)*(gamma q j+criticalExcess d j x))
      x.2 δ _ _ at hbounds
    rw [heq x hx] at hbounds
    have ⟨hle, hge⟩ := nearCriticalScale_compare_costOrder n j (hN.trans hn) (criticalExcess d j x)
    have hlog : 0 ≤ Real.log (1/δ) :=
      Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
    apply hbounds.mono
    · apply mul_le_mul_of_nonneg_right _ hlog
      nlinarith only [mul_le_mul_of_nonneg_left hge hc.le]
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hH.le) hlog

/-- With fixed confidence the logarithm is absorbed into the two constants. -/
theorem qudit_nearCritical_product_neighborhood (d j : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a₀ b₀ δ : ℝ) (hb₀ : 0 < b₀) (hb₁ : b₀ < 1)
    (hcritical : (a₀-b₀)/(1-b₀) = gamma ((d:ℝ)+1) j)
    (hδ : 0 < δ) (hhalf : δ < 1/2) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (a₀,b₀) ∈ U ∧
    (∀ x ∈ U, 0 < x.2 ∧ x.2 < x.1 ∧ x.1 < 1) ∧
    ∃ L H : ℝ, 0 < L ∧ 0 < H ∧
    ∃ G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      CompactHaarTypical d G ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n, N ≤ n → ∀ ψ ∈ G n, ∀ x ∈ U,
        NearCriticalBudgetBounds.{u} (spherePureVector ψ) x.1 x.2 δ
          (L * nearCriticalCostOrder n j (criticalExcess d j x))
          (H * nearCriticalCostOrder n j (criticalExcess d j x)) := by
  obtain ⟨U, hU, hcenter, hvalid, H, hH, G, hG, N, hN, cutoffs⟩ :=
    qudit_nearCritical_product_neighborhood_confidence.{u} d j hd a₀ b₀ hb₀ hb₁ hcritical
  obtain ⟨L, hL, hall⟩ := cutoffs δ hδ hhalf
  have hlog := Real.log_pos ((lt_div_iff₀ hδ).mpr (show 1*δ < 1 by linarith))
  refine ⟨U, hU, hcenter, hvalid, L * Real.log (1/δ), H * Real.log (1/δ),
    mul_pos hL hlog, mul_pos hH hlog, G, hG, N, hN, ?_⟩
  intro n hn ψ hψ x hx
  apply (hall n hn ψ hψ x hx δ hδ le_rfl).mono <;> apply le_of_eq <;> ring

end LocalCertification.Protocol.MeasurableExecution
