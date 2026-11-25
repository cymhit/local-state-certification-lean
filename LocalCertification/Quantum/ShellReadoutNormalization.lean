import LocalCertification.Quantum.ShellReadout

open scoped BigOperators ComplexOrder
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

/-- Exact normalization of the combinatorial shell coefficient. -/
theorem shell_coefficient_normalized {d n j k : ℕ} (hd : 2 ≤ d) (hj : j ≤ n) (hk : k ≤ j) :
    (((Nat.choose n j * (d^2-1)^j : ℕ) : ℝ)⁻¹ * shellReadoutCoefficient d n j k) =
      (((d : ℝ)+1)⁻¹)^j * (Nat.choose j k : ℝ) * (d : ℝ)^k /
        ((Nat.choose n k : ℝ) * ((d-1 : ℕ) : ℝ)^k) := by
  have hd1 : 1 ≤ d := by omega
  have hdsq : 1 ≤ d^2 := by nlinarith
  have hdR : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
  have hdm : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by rw [Nat.cast_sub hd1, Nat.cast_one]
  have hdq : ((d^2-1 : ℕ) : ℝ) = ((d : ℝ)-1)*((d : ℝ)+1) := by
    rw [Nat.cast_sub hdsq, Nat.cast_pow, Nat.cast_one]
    ring
  have hnj : (Nat.choose n j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos hj))
  have hnk : (Nat.choose n k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos (hk.trans hj)))
  have hm : (d : ℝ)-1 ≠ 0 := ne_of_gt (sub_pos.mpr hdR)
  have hq : (d : ℝ)+1 ≠ 0 := by linarith
  have hc : (Nat.choose n j : ℝ) * (Nat.choose j k : ℝ) =
      (Nat.choose n k : ℝ) * (Nat.choose (n-k) (j-k) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := n) (k := j) (s := k) hk)
  have hp : ((d : ℝ)-1)^j = ((d : ℝ)-1)^(j-k) * ((d : ℝ)-1)^k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  simp only [shellReadoutCoefficient, ite_eq_left hk, Nat.cast_mul, Nat.cast_pow,
    hdq, hdm, mul_pow, inv_pow]
  field_simp
  rw [hp]
  linear_combination -((d : ℝ)-1)^(j-k) * ((d : ℝ)-1)^k * hc

/-- Entrywise identification with the existing normalized d-ary Hamming averages. -/
theorem shell_coefficient_hamming {d n j : ℕ} [NeZero d] (hd : 2 ≤ d) (hj : j ≤ n)
    (x y : CertificationGaussian.QuditIndex d n) :
    ((weylShell d n j).card : ℝ)⁻¹ *
        shellReadoutCoefficient d n j (CertificationGaussian.hammingDistance x y) =
      (((d : ℝ)+1)⁻¹)^j * ∑ k ∈ Finset.range (j+1),
        (Nat.choose j k : ℝ) * (d : ℝ)^k * CertificationGaussian.distanceAverage d n k x y := by
  by_cases hk : CertificationGaussian.hammingDistance x y ≤ j
  · have hs : (∑ k ∈ Finset.range (j+1),
        (Nat.choose j k : ℝ) * (d : ℝ)^k * CertificationGaussian.distanceAverage d n k x y) =
        (Nat.choose j (CertificationGaussian.hammingDistance x y) : ℝ) *
          (d : ℝ)^(CertificationGaussian.hammingDistance x y) *
            CertificationGaussian.distanceAverage d n (CertificationGaussian.hammingDistance x y) x y := by
      apply Finset.sum_eq_single (CertificationGaussian.hammingDistance x y)
      · intro k hkr hne
        simp [CertificationGaussian.distanceAverage, Ne.symm hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
    rw [hs, weylShell_card]
    simp only [CertificationGaussian.distanceAverage, ite_true]
    simpa only [div_eq_mul_inv, mul_assoc] using shell_coefficient_normalized hd hj hk
  · have hs : (∑ k ∈ Finset.range (j+1),
        (Nat.choose j k : ℝ) * (d : ℝ)^k * CertificationGaussian.distanceAverage d n k x y) = 0 := by
      apply Finset.sum_eq_zero
      intro k hkr
      have hne : CertificationGaussian.hammingDistance x y ≠ k := by
        have : k < j+1 := Finset.mem_range.mp hkr
        omega
      simp [CertificationGaussian.distanceAverage, hne]
    simp [shellReadoutCoefficient, hk, hs]

/-- Complete shell readout for every actual mixed state and every product unitary basis. -/
theorem productBorn_shell_readout {d n : ℕ} [NeZero d] (hd : 2 ≤ d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : ℕ) (hj : j ≤ n)
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U (weylShellState hd ρ j hj) x =
      (((d : ℝ)+1)⁻¹)^j * ∑ k ∈ Finset.range (j+1), (Nat.choose j k : ℝ) * (d : ℝ)^k *
        (CertificationGaussian.distanceAverage d n k).mulVec (productBorn d n U ρ) x := by
  rw [productBorn_shell_coefficient hd ρ j hj U x]
  calc
    _ = ∑ y, (((weylShell d n j).card : ℝ)⁻¹ *
        shellReadoutCoefficient d n j (CertificationGaussian.hammingDistance x y)) * productBorn d n U ρ y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := by
      simp_rw [shell_coefficient_hamming hd hj x]
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro y hy
      ring

/-- Pure-target formula in the U-dagger coordinates used by the uniform product-basis score bound. -/
theorem pureTargetShell_readout {d n : ℕ} [NeZero d] (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (j : ℕ) (hj : j ≤ n)
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U (pureTargetShell hd ψ j hj) x =
      (((d : ℝ)+1)⁻¹)^j * ∑ k ∈ Finset.range (j+1), (Nat.choose j k : ℝ) * (d : ℝ)^k *
        (CertificationGaussian.distanceAverage d n k).mulVec
          (fun y => Complex.normSq ((tensorBasis d n (qitProductBasis d n U)).conjTranspose.mulVec ψ.amp y)) x := by
  have hp : productBorn d n U ψ.state =
      (fun y => Complex.normSq ((tensorBasis d n (qitProductBasis d n U)).conjTranspose.mulVec ψ.amp y)) := by
    funext y
    exact productBorn_pure d n U ψ y
  simpa only [pureTargetShell, hp] using
    productBorn_shell_readout hd ψ.state j hj U x

end LocalCertification.Quantum
