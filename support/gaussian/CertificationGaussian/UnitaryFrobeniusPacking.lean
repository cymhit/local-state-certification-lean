import CertificationGaussian.UnitaryNet
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Order.Lattice.Nat
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
noncomputable section
open MeasureTheory Metric Set Module
open scoped BigOperators ENNReal
open Classical
namespace CertificationGaussian
/-- The ambient-volume bound, with arbitrary radius and separation. -/
theorem separated_card_le_ball_volume_ratio {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (1+2*R/ε)^finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε/2
  let ρ : ℝ := R+ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball (c : E) δ
  have D : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball c δ) (ball d δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep c hc d hd hcd using 1 <;> dsimp [δ] <;> ring
  have A_subset : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    dsimp [δ, ρ]
    linarith [hs x hx]
  have I :
      (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^finrank ℝ E)*μ (ball 0 1) ≤
        ENNReal.ofReal (ρ^finrank ℝ E)*μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ c ∈ s, ball c δ from rfl, measure_biUnion_finset D (fun c _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0:E) ρ) := measure_mono A_subset
      _ = _ := by rw [μ.addHaar_ball_of_pos _ hρ]
  have J : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^finrank ℝ E) ≤ ENNReal.ofReal (ρ^finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).mp I
  have K : (s.card : ℝ)*δ^finrank ℝ E ≤ ρ^finrank ℝ E := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
  have H := (le_div_iff₀ (pow_pos hδ _)).mpr K
  rw [← div_pow] at H
  have he : ρ/δ = 1+2*R/ε := by dsimp [ρ, δ]; field_simp; ring
  simpa only [he] using H

/-- A maximal finite separated subset of a bounded injective Euclidean model is a net. -/
theorem exists_maximal_separated_net {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : α → E) (hf : Function.Injective f) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hbound : ∀ a, ‖f a‖ ≤ R) :
    ∃ s : Finset α,
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → ε ≤ ‖f a-f b‖) ∧
      (∀ a, ∃ b ∈ s, ‖f a-f b‖ ≤ ε) ∧
      (s.card : ℝ) ≤ (1+2*R/ε)^finrank ℝ E := by
  let good := fun s : Finset α => ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ε ≤ ‖f a-f b‖
  have hc (s : Finset α) (hs : good s) :
      (s.card : ℝ) ≤ (1+2*R/ε)^finrank ℝ E := by
    have H := separated_card_le_ball_volume_ratio (s.image f) hR hε
      (by intro c hc; obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc; exact hbound a)
      (by
        intro c hc d hd hcd
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
        exact hs a ha b hb (fun he => hcd (congrArg f he)))
    simpa only [Finset.card_image_of_injective _ hf] using H
  let sizes : Set Nat := {k | ∃ s : Finset α, good s ∧ s.card = k}
  have hnonempty : sizes.Nonempty := ⟨0, ∅, by simp [good], rfl⟩
  have hbounded : BddAbove sizes := by
    refine ⟨Nat.ceil ((1+2*R/ε)^finrank ℝ E), ?_⟩
    rintro k ⟨s, hs, rfl⟩
    exact Nat.cast_le.mp ((hc s hs).trans (Nat.le_ceil _))
  obtain ⟨s, hs, hcard⟩ := Nat.sSup_mem hnonempty hbounded
  refine ⟨s, hs, ?_, hc s hs⟩
  intro a
  by_contra! hbad
  have ha : a ∉ s := by
    intro ha
    have := hbad a ha
    simp only [sub_self, norm_zero] at this
    linarith
  have hgood : good (insert a s) := by
    intro b hb c hcc hbc
    rcases Finset.mem_insert.mp hb with rfl | hbs
    · rcases Finset.mem_insert.mp hcc with rfl | hcc
      · exact False.elim (hbc rfl)
      · exact (hbad c hcc).le
    · rcases Finset.mem_insert.mp hcc with rfl | hcc
      · rw [norm_sub_rev]
        exact (hbad b hbs).le
      · exact hs b hbs c hcc hbc
  have H := le_csSup hbounded (show (insert a s).card ∈ sizes from ⟨_, hgood, rfl⟩)
  rw [Finset.card_insert_of_notMem ha, ← hcard] at H
  omega

/-- Complex matrices are embedded with their Frobenius norm. -/
def unitaryFrobeniusVector {d : Nat} (U : LocalUnitary d) :
    EuclideanSpace ℂ (Fin d × Fin d) := WithLp.toLp 2 (fun ij => U.1 ij.1 ij.2)

theorem unitaryFrobeniusVector_injective (d : Nat) :
    Function.Injective (@unitaryFrobeniusVector d) := by
  intro U V h
  apply Subtype.ext
  ext i j
  exact congrArg (fun a : EuclideanSpace ℂ (Fin d × Fin d) => a (i,j)) h

theorem unitaryFrobeniusVector_norm_sq {d : Nat} (U : LocalUnitary d) :
    ‖unitaryFrobeniusVector U‖^2 = d := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hcol (j : Fin d) : ∑ i, ‖U.1 i j‖^2 = 1 := by
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A j j).re) U.2.1
    simpa [Matrix.mul_apply, Complex.sq_norm, Complex.normSq_apply,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.star_def] using h
  change (∑ i, ∑ j, ‖U.1 i j‖^2) = _
  rw [Finset.sum_comm]
  simp_rw [hcol]
  simp

theorem unitaryFrobeniusVector_norm {d : Nat} (U : LocalUnitary d) :
    ‖unitaryFrobeniusVector U‖ = Real.sqrt d := by
  rw [← unitaryFrobeniusVector_norm_sq U, Real.sqrt_sq (norm_nonneg _)]

theorem unitaryFrobeniusVector_sub_norm_sq {d : Nat} (U V : LocalUnitary d) :
    ‖unitaryFrobeniusVector U-unitaryFrobeniusVector V‖^2 =
      ∑ i, ∑ j, ‖U.1 i j-V.1 i j‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem unitaryFrobenius_real_dimension (d : Nat) :
    finrank ℝ (EuclideanSpace ℂ (Fin d × Fin d)) = 2*d^2 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ]
  simp [Complex.finrank_real_complex, finrank_euclideanSpace, pow_two]

theorem exists_unitary_frobenius_packing_net (d : Nat) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (LocalUnitary d),
      (∀ U ∈ s, ∀ V ∈ s, U ≠ V →
        ε ≤ ‖unitaryFrobeniusVector U-unitaryFrobeniusVector V‖) ∧
      (∀ U : LocalUnitary d, ∃ V ∈ s, ∑ i, ∑ j, ‖U.1 i j-V.1 i j‖^2 ≤ ε^2) ∧
      (s.card : ℝ) ≤ (1+2*Real.sqrt d/ε)^(2*d^2) := by
  obtain ⟨s, hs, hcover, hcard⟩ := exists_maximal_separated_net
    (@unitaryFrobeniusVector d) (unitaryFrobeniusVector_injective d)
    (Real.sqrt_nonneg d) hε (fun U => (unitaryFrobeniusVector_norm U).le)
  refine ⟨s, hs, ?_, ?_⟩
  · intro U
    obtain ⟨V, hV, hd⟩ := hcover U
    refine ⟨V, hV, ?_⟩
    rw [← unitaryFrobeniusVector_sub_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) hε.le).mpr hd
  · simpa only [unitaryFrobenius_real_dimension] using hcard


def unitaryPackingNet (d : Nat) (ε : ℝ) (hε : 0 < ε) : Finset (LocalUnitary d) :=
  (exists_unitary_frobenius_packing_net d hε).choose

theorem unitaryPackingNet_separated {d : Nat} {ε : ℝ} (hε : 0 < ε) :
    ∀ U ∈ unitaryPackingNet d ε hε, ∀ V ∈ unitaryPackingNet d ε hε, U ≠ V →
      ε ≤ ‖unitaryFrobeniusVector U-unitaryFrobeniusVector V‖ :=
  (exists_unitary_frobenius_packing_net d hε).choose_spec.1

theorem unitaryPackingNet_covers_sq {d : Nat} {ε : ℝ} (hε : 0 < ε) (U : LocalUnitary d) :
    ∃ V ∈ unitaryPackingNet d ε hε, ∑ i, ∑ j, ‖U.1 i j-V.1 i j‖^2 ≤ ε^2 :=
  (exists_unitary_frobenius_packing_net d hε).choose_spec.2.1 U

theorem unitaryPackingNet_card {d : Nat} {ε : ℝ} (hε : 0 < ε) :
    ((unitaryPackingNet d ε hε).card : ℝ) ≤ (1+2*Real.sqrt d/ε)^(2*d^2) :=
  (exists_unitary_frobenius_packing_net d hε).choose_spec.2.2

theorem unitaryPackingNet_covers_operator {d : Nat} {ε : ℝ} (hε : 0 < ε) (U : LocalUnitary d) :
    ∃ V ∈ unitaryPackingNet d ε hε,
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (U.1-V.1)‖ ≤ ε := by
  obtain ⟨V, hV, he⟩ := unitaryPackingNet_covers_sq hε U
  refine ⟨V, hV, (matrix_operator_norm_le_entry_sqrt _).trans ?_⟩
  exact (Real.sqrt_le_sqrt he).trans_eq (Real.sqrt_sq hε.le)

end CertificationGaussian
