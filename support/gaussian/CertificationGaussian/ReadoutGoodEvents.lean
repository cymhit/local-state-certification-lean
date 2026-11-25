import CertificationGaussian.ReadoutMomentError
import CertificationGaussian.ReadoutRemainderAsymptotics

noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

/-- A fixed linear exponential plus a fixed cubic exponential is eventually below every fixed inverse polynomial. -/
theorem eventually_exp_pair_le_inverse_power {a b : ℝ} (ha : 0<a) (hb : 0<b) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-a*n)+Real.exp (-b*(n:ℝ)^3)≤((n:ℝ)^k)⁻¹ := by
  let c := min a b
  have hc : 0<c := lt_min ha hb
  filter_upwards [eventually_polynomial_le_exp 2 k hc,eventually_ge_atTop 1] with n hp hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by linarith
  have hcube : (n:ℝ)≤(n:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1≤3 by decide)
  have h1 : Real.exp (-a*n)≤Real.exp (-c*n) := Real.exp_le_exp.mpr (by
    have h := mul_le_mul_of_nonneg_right (min_le_left a b) hnp.le
    dsimp [c]; linarith)
  have h2 : Real.exp (-b*(n:ℝ)^3)≤Real.exp (-c*n) := Real.exp_le_exp.mpr (by
    have h := (mul_le_mul_of_nonneg_right (min_le_right a b) hnp.le).trans
      (mul_le_mul_of_nonneg_left hcube hb.le)
    dsimp [c]; linarith)
  calc
    _ ≤ 2*Real.exp (-c*n) := by linarith
    _ ≤ _ := by
      rw [show -c*(n:ℝ)= -(c*n) by ring,Real.exp_neg,← div_eq_mul_inv,← one_div]
      apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos hnp k)).mpr
      simpa only [one_mul] using hp

/-- The actual Haar remainder and the single common-radius event are controlled jointly by a union bound. -/
theorem cardinalityHaar_remainder_radius_eventually_bound (d r : ℕ) [NeZero d]
    (hd : 3≤d) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      pairedGaussian (QuditIndex d n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖ ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|} ≤
      ENNReal.ofReal (Real.exp ((Real.log (haarLocalKappa d)/2)*n)+
        Real.exp (-(Real.log d/4)*(n:ℝ)^3)) := by
  filter_upwards [cardinalityHaar_remainder_eventually_exponential d r hd lam,
    quditRadius_power_eventually_cubic (by omega : 2≤d) (r+4)] with n hZ ht
  calc
    _ ≤ pairedGaussian (QuditIndex d n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖}+
        pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp ((Real.log (haarLocalKappa d)/2)*n))+
        ENNReal.ofReal (Real.exp (-(Real.log d/4)*(n:ℝ)^3)) :=
      add_le_add hZ ((measure_mono (show {x | ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|} ⊆
        {x | ((n:ℝ)^(r+4))⁻¹≤|gaussianRadius (QuditIndex d n) x-1|} from by
        intro x hx
        change ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1| at hx
        change ((n:ℝ)^(r+4))⁻¹≤|gaussianRadius (QuditIndex d n) x-1|
        exact hx.le)).trans ht)
    _ = _ := (ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)).symm

/-- The same joint actual bad event for finite Pauli records, with no independence premise. -/
theorem cardinalityPauli_remainder_radius_eventually_bound (r : ℕ) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      pairedGaussian (QuditIndex 2 n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖ ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 2 n) x-1|} ≤
      ENNReal.ofReal (Real.exp ((Real.log pauliLocalKappa/2)*n)+
        Real.exp (-(Real.log 2/4)*(n:ℝ)^3)) := by
  filter_upwards [cardinalityPauli_remainder_eventually_exponential r lam,
    quditRadius_power_eventually_cubic (by decide : 2≤2) (r+4)] with n hZ ht
  calc
    _ ≤ pairedGaussian (QuditIndex 2 n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖}+
        pairedGaussian (QuditIndex 2 n) {x | ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 2 n) x-1|} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp ((Real.log pauliLocalKappa/2)*n))+
        ENNReal.ofReal (Real.exp (-(Real.log 2/4)*(n:ℝ)^3)) :=
      add_le_add hZ ((measure_mono (show {x | ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 2 n) x-1|} ⊆
        {x | ((n:ℝ)^(r+4))⁻¹≤|gaussianRadius (QuditIndex 2 n) x-1|} from by
        intro x hx
        change ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 2 n) x-1| at hx
        change ((n:ℝ)^(r+4))⁻¹≤|gaussianRadius (QuditIndex 2 n) x-1|
        exact hx.le)).trans ht)
    _ = _ := (ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)).symm

/-- The same actual Haar joint failure is eventually below n^(-k) for every fixed k. -/
theorem cardinalityHaar_remainder_radius_inverse_power (d r k : ℕ) [NeZero d]
    (hd : 3≤d) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      pairedGaussian (QuditIndex d n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖ ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|} ≤
      ENNReal.ofReal (((n:ℝ)^k)⁻¹) := by
  have ha : 0< -(Real.log (haarLocalKappa d)/2) := by
    have h := Real.log_neg (haarLocalKappa_pos d (by omega)) (haarLocalKappa_lt_one d hd)
    linarith
  have hb : 0<Real.log d/4 := div_pos (Real.log_pos (by exact_mod_cast (show 1<d by omega))) (by norm_num)
  filter_upwards [cardinalityHaar_remainder_radius_eventually_bound d r hd lam,
    eventually_exp_pair_le_inverse_power ha hb k] with n hn hp
  exact hn.trans (ENNReal.ofReal_le_ofReal (by simpa only [neg_neg] using hp))

/-- The genuine Pauli joint failure also decays faster than every fixed inverse power. -/
theorem cardinalityPauli_remainder_radius_inverse_power (r k : ℕ) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      pairedGaussian (QuditIndex 2 n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖ ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 2 n) x-1|} ≤
      ENNReal.ofReal (((n:ℝ)^k)⁻¹) := by
  have ha : 0< -(Real.log pauliLocalKappa/2) := by
    have h := Real.log_neg pauliLocalKappa_pos pauliLocalKappa_lt_one
    linarith
  have hb : 0<Real.log 2/4 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [cardinalityPauli_remainder_radius_eventually_bound r lam,
    eventually_exp_pair_le_inverse_power ha hb k] with n hn hp
  exact hn.trans (ENNReal.ofReal_le_ofReal (by simpa only [neg_neg] using hp))

end CertificationGaussian
