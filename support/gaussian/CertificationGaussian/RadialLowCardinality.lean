import CertificationGaussian.RadialHighWeights
import CertificationGaussian.HammingKernel

noncomputable section
open scoped BigOperators
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Actual label words transported to the fixed Hamming counting model; no zero-preserving enumeration is assumed. -/
def radialLabelWordEquiv (K : Type*) [Fintype K] (n : ℕ) :
    (Fin n → K) ≃ QuditIndex (Fintype.card K) n :=
  Equiv.piCongrRight (fun _ : Fin n => Fintype.equivFin K)

/-- The actual nonidentity support is the difference from the actual image of the constant reference word. -/
theorem radialBellSupport_differenceSupport (n : ℕ) (k0 : K) (w : Fin n → K) :
    radialBellSupport k0 w=differenceSupport
      (radialLabelWordEquiv K n (fun _ => k0)) (radialLabelWordEquiv K n w) := by
  ext s
  simp only [radialBellSupport,differenceSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    radialLabelWordEquiv,Equiv.piCongrRight_apply]
  exact not_congr (by simp [eq_comm])

/-- True shell cardinality for arbitrary finite local labels, including n=0 and j>n. -/
theorem radialBellSupport_shell_card (n j : ℕ) (k0 : K) :
    (Finset.univ.filter (fun w : Fin n → K => (radialBellSupport k0 w).card=j)).card=
      n.choose j*(Fintype.card K-1)^j := by
  let e := (radialLabelWordEquiv K n).subtypeEquiv
    (p := fun w => (radialBellSupport k0 w).card=j)
    (q := fun y => hammingDistance (radialLabelWordEquiv K n (fun _ => k0)) y=j)
    (fun w => by rw [radialBellSupport_differenceSupport,card_differenceSupport])
  rw [← Fintype.card_subtype,Fintype.card_congr e,Fintype.card_subtype,hamming_sphere_card]

/-- Exact cardinality of the actual low-label set with the original cutoff. -/
theorem radialLowLabels_card (d r n : ℕ) (k0 : K) :
    (radialLowLabels (S:=Fin n) d r k0).card=
      ∑ j∈Finset.range (radialWeightCutoff d r n+1),n.choose j*(Fintype.card K-1)^j := by
  have h := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (Fin n → K))
    (Finset.range (radialWeightCutoff d r n+1)) (fun w => (radialBellSupport k0 w).card) (fun _ => (1:ℕ))
  simp only [Finset.sum_const,smul_eq_mul,mul_one,Finset.mem_range,Nat.lt_succ_iff] at h
  calc
    _ = ∑ j∈Finset.range (radialWeightCutoff d r n+1),
        (Finset.univ.filter (fun w : Fin n → K => (radialBellSupport k0 w).card=j)).card := by
      simpa only [radialLowLabels,Fintype.card_fin] using h.symm
    _ = _ := by simp_rw [radialBellSupport_shell_card]

/-- A crude finite counting bound sufficient for the logarithmic-squared growth estimate. -/
theorem radialLowLabels_card_le_power (d r n : ℕ) (k0 : K) :
    (radialLowLabels (S:=Fin n) d r k0).card ≤
      (radialWeightCutoff d r n+1)*(n*(Fintype.card K-1)+1)^(radialWeightCutoff d r n) := by
  rw [radialLowLabels_card]
  calc
    _ ≤ ∑ _j∈Finset.range (radialWeightCutoff d r n+1),
        (n*(Fintype.card K-1)+1)^(radialWeightCutoff d r n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjL : j≤radialWeightCutoff d r n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      calc
        n.choose j*(Fintype.card K-1)^j ≤ n^j*(Fintype.card K-1)^j :=
          Nat.mul_le_mul_right _ (Nat.choose_le_pow n j)
        _ = (n*(Fintype.card K-1))^j := (mul_pow _ _ _).symm
        _ ≤ (n*(Fintype.card K-1)+1)^j := Nat.pow_le_pow_left (by omega) j
        _ ≤ _ := pow_le_pow_right₀ (show 1≤n*(Fintype.card K-1)+1 by omega) hjL
    _ = _ := by simp

/-- Once the cutoff exceeds n, the actual low set is the complete label set. -/
theorem radialLowLabels_eq_univ (d r n : ℕ) (k0 : K) (h : n≤radialWeightCutoff d r n) :
    radialLowLabels (S:=Fin n) d r k0=Finset.univ := by
  apply Finset.filter_eq_self.mpr
  intro w _
  have hw : (radialBellSupport k0 w).card≤n := by simpa using Finset.card_le_univ (radialBellSupport k0 w)
  simpa only [Fintype.card_fin] using hw.trans h

end CertificationGaussian
