import LocalCertification.Quantum.WeylSupport
import LocalCertification.Quantum.WeylGaussianChaos
import CertificationGaussian.Consumers.GramPolarCorrection

set_option autoImplicit false
open Matrix MeasureTheory Metric Set CertificationGaussian Classical
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

/-- The actual low-weight canonical Weyl labels, retaining the identity label. -/
abbrev LowWeylIndex (d n L : ℕ) := {u : WeylLabel d n // weylWeight u ≤ L}

/-- A distinguished identity column, independent of an arbitrary enumeration. -/
def lowWeylIdentity (d n L : ℕ) : LowWeylIndex d n L :=
  ⟨0, by rw [(weylWeight_eq_zero (0 : WeylLabel d n)).mpr rfl]; exact Nat.zero_le L⟩

def lowWeylFamily (d n L : ℕ) [NeZero d] (u : LowWeylIndex d n L) :
    Matrix (QuditIndex d n) (QuditIndex d n) ℂ := quditWeyl u.val

/-- Exact cardinality, also for cutoffs beyond n and for the empty tensor power. -/
theorem lowWeylIndex_card (L : ℕ) :
    Fintype.card (LowWeylIndex d n L) =
      ∑ j ∈ Finset.range (L+1), Nat.choose n j * (d^2-1)^j := by
  have h := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (WeylLabel d n))
    (Finset.range (L+1)) weylWeight (fun _ => (1:ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.mem_range, Nat.lt_succ_iff] at h
  rw [Fintype.card_subtype]
  calc
    _ = ∑ j ∈ Finset.range (L+1), (weylShell d n j).card := h.symm
    _ = _ := by simp_rw [weylShell_card]

@[simp] theorem lowWeylFamily_identity (L : ℕ) :
    lowWeylFamily d n L (lowWeylIdentity d n L) = 1 := quditWeyl_zero

theorem lowWeylFamily_unitary (L : ℕ) (u : LowWeylIndex d n L) :
    lowWeylFamily d n L u ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :=
  quditWeyl_unitary u.val

theorem lowWeylFamily_hilbertSchmidt (L : ℕ) (u v : LowWeylIndex d n L) :
    ((lowWeylFamily d n L u)ᴴ * lowWeylFamily d n L v).trace =
      if u=v then (Fintype.card (QuditIndex d n):ℂ) else 0 := by
  simpa only [lowWeylFamily, Subtype.ext_iff] using quditWeyl_hilbertSchmidt_card u.val v.val

/-- The distinguished column is the original target, not just a phase multiple. -/
theorem lowWeylOrbit_identity_column (L : ℕ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (i : QuditIndex d n) :
    unitaryOrbitMatrix (lowWeylFamily d n L) ψ i (lowWeylIdentity d n L) = ψ i := by
  simp [unitaryOrbitMatrix]

/-- The literal Gram error has the exact Haar Frobenius-square expectation. -/
theorem lowWeylOrbit_haar_square_moment (L : ℕ)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :
    (∫ U, unitaryOrbitGramSquareSum (lowWeylFamily d n L)
      (complexUnitarySphereAction (QuditIndex d n) U ψ₀) ∂complexUnitaryHaar (QuditIndex d n)) =
      (Fintype.card (LowWeylIndex d n L):ℝ) * ((Fintype.card (LowWeylIndex d n L):ℝ)-1) /
        ((d:ℝ)^n+1) := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  simpa only [qudit_card, Nat.cast_pow] using unitaryOrbitGramSquareSum_haar_moment
    (lowWeylFamily d n L) (lowWeylFamily_unitary L) (lowWeylFamily_hilbertSchmidt L) ψ₀

/-- The paper's exact low-weight orbit tail for every positive threshold and every initial target. -/
theorem lowWeylOrbit_haar_tail (L : ℕ) (t : ℝ) (ht : 0<t)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :
    complexUnitaryHaar (QuditIndex d n)
      {U | t < ‖Matrix.toEuclideanCLM (n := LowWeylIndex d n L) (𝕜 := ℂ)
        (unitaryOrbitGramError (lowWeylFamily d n L)
          (complexUnitarySphereAction (QuditIndex d n) U ψ₀))‖} ≤
      ENNReal.ofReal ((Fintype.card (LowWeylIndex d n L):ℝ) *
        ((Fintype.card (LowWeylIndex d n L):ℝ)-1) / (((d:ℝ)^n+1)*t^2)) := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  simpa only [qudit_card, Nat.cast_pow] using unitaryOrbitGram_haar_tail
    (lowWeylFamily d n L) (lowWeylFamily_unitary L) (lowWeylFamily_hilbertSchmidt L) t ht ψ₀

/-- On the same actual Gram event, the CFC correction is an isometry and controls every complex sandwich. -/
theorem lowWeylOrbit_polar (L : ℕ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (t : ℝ) (ht : t<1)
    (hg : ‖Matrix.toEuclideanCLM (n := LowWeylIndex d n L) (𝕜 := ℂ)
      (unitaryOrbitGramError (lowWeylFamily d n L) ψ)‖ ≤ t) :
    let V := unitaryOrbitMatrix (lowWeylFamily d n L) ψ
    let Q := matrixPolarCorrection V
    Qᴴ*Q=1 ∧ ‖rectangularEuclideanCLM (V-Q)‖ ≤ t ∧
      (∀ x : EuclideanSpace ℂ (LowWeylIndex d n L), ‖rectangularEuclideanCLM Q x‖=‖x‖) ∧
      (∀ A : Matrix (LowWeylIndex d n L) (LowWeylIndex d n L) ℂ,
        ‖V*A*Vᴴ-Q*A*Qᴴ‖ ≤ 3*‖A‖*t) :=
  CertificationGaussian.Consumers.unitaryOrbit_polar_on_good_event (lowWeylFamily d n L) ψ t ht hg

/-- Probability and deterministic orthogonalization refer to one measurable, literal Weyl Gram event. -/
theorem lowWeylOrbit_haar_polar (L : ℕ) (t : ℝ) (ht0 : 0<t) (ht1 : t<1)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :
    complexUnitaryHaar (QuditIndex d n)
      {U | t < ‖Matrix.toEuclideanCLM (n := LowWeylIndex d n L) (𝕜 := ℂ)
        (unitaryOrbitGramError (lowWeylFamily d n L)
          (complexUnitarySphereAction (QuditIndex d n) U ψ₀))‖} ≤
      ENNReal.ofReal ((Fintype.card (LowWeylIndex d n L):ℝ) *
        ((Fintype.card (LowWeylIndex d n L):ℝ)-1) / (((d:ℝ)^n+1)*t^2)) ∧
    ∀ U, ‖Matrix.toEuclideanCLM (n := LowWeylIndex d n L) (𝕜 := ℂ)
      (unitaryOrbitGramError (lowWeylFamily d n L)
        (complexUnitarySphereAction (QuditIndex d n) U ψ₀))‖ ≤ t →
      let V := unitaryOrbitMatrix (lowWeylFamily d n L)
        (complexUnitarySphereAction (QuditIndex d n) U ψ₀)
      (matrixPolarCorrection V)ᴴ*matrixPolarCorrection V=1 ∧
        ‖rectangularEuclideanCLM (V-matrixPolarCorrection V)‖ ≤ t := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  simpa only [qudit_card, Nat.cast_pow] using CertificationGaussian.Consumers.unitaryOrbit_haar_polar_good_event
    (lowWeylFamily d n L) (lowWeylFamily_unitary L) (lowWeylFamily_hilbertSchmidt L) t ht0 ht1 ψ₀

end LocalCertification.Quantum
