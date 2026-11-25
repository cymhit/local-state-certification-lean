import CertificationGaussian.ProjectorComplementMoments

/-! # Cardinality-normalized signed complement kernels

The physical subset expansion has the exact binomial normalization and variance
scale used by the original finite dual. Outcome spaces remain arbitrary.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

abbrev ProjectorCardinalityIndex (S : Type*) (J : Finset ℕ) :=
  (k : J) × {A : Finset S // A.card = k.val}

def projectorCardinalitySubset (J : Finset ℕ) (a : ProjectorCardinalityIndex S J) : Finset S :=
  a.2.val

def projectorCardinalityWeight (J : Finset ℕ) (θ : ℕ → ℝ)
    (a : ProjectorCardinalityIndex S J) : ℝ :=
  θ a.1.val / (((Fintype.card S).choose a.1.val : ℝ) *
    ((Fintype.card I - 1 : ℕ) : ℝ)^a.1.val)

def cardinalityProjectorKernel (P : S → Matrix I I ℂ) (J : Finset ℕ) (θ : ℕ → ℝ) :
    Matrix (S → I) (S → I) ℂ :=
  signedProjectorComplementKernel P (projectorCardinalitySubset J)
    (projectorCardinalityWeight (I := I) J θ)

omit [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I] in
theorem projectorCardinalitySubset_injective (J : Finset ℕ) :
    Function.Injective (projectorCardinalitySubset (S := S) J) := by
  rintro ⟨j, A⟩ ⟨k, B⟩ h
  change A.val = B.val at h
  have hj : j = k := Subtype.ext (A.property.symm.trans ((congrArg Finset.card h).trans B.property))
  subst k
  have hab : A = B := Subtype.ext h
  subst B
  rfl

theorem cardinalityProjectorKernel_formula (P : S → Matrix I I ℂ) (J : Finset ℕ) (θ : ℕ → ℝ) :
    cardinalityProjectorKernel P J θ =
      ∑ k ∈ J, ((θ k / (((Fintype.card S).choose k : ℝ) *
        ((Fintype.card I - 1 : ℕ) : ℝ)^k) : ℝ) : ℂ) •
          ∑ A : {A : Finset S // A.card = k}, projectorSubsetFactor P A.val := by
  simp only [cardinalityProjectorKernel, signedProjectorComplementKernel,
    Fintype.sum_sigma, projectorCardinalitySubset, projectorCardinalityWeight,
    ← Finset.smul_sum]
  exact Finset.sum_coe_sort J (fun k =>
    ((θ k / (((Fintype.card S).choose k : ℝ) *
      ((Fintype.card I - 1 : ℕ) : ℝ)^k) : ℝ) : ℂ) •
        ∑ A : {A : Finset S // A.card = k}, projectorSubsetFactor P A.val)

theorem cardinalityProjectorKernel_zero (P : S → Matrix I I ℂ) (θ : ℕ → ℝ) :
    cardinalityProjectorKernel P {0} θ = (θ 0 : ℂ) • wickTensorMatrix P := by
  rw [cardinalityProjectorKernel_formula]
  simp only [Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, div_one]
  have he (A : {A : Finset S // A.card = 0}) : A.val = ∅ := Finset.card_eq_zero.mp A.property
  simp only [he, projectorSubsetFactor_empty, Finset.sum_const, Finset.card_univ,
    Fintype.card_finset_len, Nat.choose_zero_right, one_nsmul]

omit [DecidableEq S] [DecidableEq I] in
private theorem cardinality_mass_sum (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    (∑ a : ProjectorCardinalityIndex S J,
      (projectorCardinalityWeight (I := I) J θ a : ℂ) *
        ((Fintype.card I : ℂ) - 1)^(projectorCardinalitySubset J a).card) =
      ((∑ k ∈ J, θ k : ℝ) : ℂ) := by
  have hq : ((Fintype.card I - 1 : ℕ) : ℂ) = (Fintype.card I : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Fintype.sum_sigma, projectorCardinalityWeight, projectorCardinalitySubset]
  rw [← Finset.sum_coe_sort J θ, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hc : ((Fintype.card S).choose k.val : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hJ k.val k.property)).ne'
  have hq0 : (Fintype.card I : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (by omega : Fintype.card I ≠ 1))
  have ha (A : {A : Finset S // A.card = k.val}) : A.val.card = k.val := A.property
  simp only [ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_finset_len,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow, hq]
  field_simp

omit [DecidableEq S] [DecidableEq I] in
private theorem cardinality_square_mass_sum (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    (∑ a : ProjectorCardinalityIndex S J,
      (((projectorCardinalityWeight (I := I) J θ a)^2 : ℝ) : ℂ) *
        ((Fintype.card I : ℂ) - 1)^(projectorCardinalitySubset J a).card) =
      (kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ : ℂ) := by
  have hq : ((Fintype.card I - 1 : ℕ) : ℂ) = (Fintype.card I : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Fintype.sum_sigma, projectorCardinalityWeight, projectorCardinalitySubset,
    kernelVarianceScale]
  rw [← Finset.sum_coe_sort J (fun k => θ k ^ 2 /
    (((Fintype.card S).choose k : ℝ) * ((Fintype.card I - 1 : ℕ) : ℝ)^k)), Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hc : ((Fintype.card S).choose k.val : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hJ k.val k.property)).ne'
  have hq0 : (Fintype.card I : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (by omega : Fintype.card I ≠ 1))
  have ha (A : {A : Finset S // A.card = k.val}) : A.val.card = k.val := A.property
  simp only [ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_finset_len,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow, hq]
  field_simp

theorem cardinalityProjectorKernel_trace (P : S → Matrix I I ℂ)
    (ht : ∀ s, (P s).trace = 1) (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    (cardinalityProjectorKernel P J θ).trace = ((∑ k ∈ J, θ k : ℝ) : ℂ) := by
  rw [cardinalityProjectorKernel, signedProjectorComplementKernel_trace P ht]
  exact cardinality_mass_sum hd J θ hJ

theorem cardinalityProjectorKernel_trace_square (P : S → Matrix I I ℂ)
    (hp : ∀ s, P s * P s = P s) (ht : ∀ s, (P s).trace = 1)
    (hd : 2 ≤ Fintype.card I) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    ((cardinalityProjectorKernel P J θ)^2).trace =
      (kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ : ℂ) := by
  rw [cardinalityProjectorKernel, signedProjectorComplementKernel_trace_square P hp ht _
    (projectorCardinalitySubset_injective J)]
  simpa only [Complex.ofReal_pow] using cardinality_square_mass_sum hd J θ hJ

theorem cardinalityProjectorKernel_hermitian (P : S → Matrix I I ℂ)
    (hh : ∀ s, (P s).IsHermitian) (J : Finset ℕ) (θ : ℕ → ℝ) :
    (cardinalityProjectorKernel P J θ).IsHermitian :=
  signedProjectorComplementKernel_hermitian P hh _ _

theorem cardinalityProjectorKernel_hilbertSchmidt_sq (P : S → Matrix I I ℂ)
    (hh : ∀ s, (P s).IsHermitian) (hp : ∀ s, P s * P s = P s)
    (ht : ∀ s, (P s).trace = 1) (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    ‖matrixHilbertSchmidt (cardinalityProjectorKernel P J θ)‖^2 =
      kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ := by
  rw [matrixHilbertSchmidt_norm_sq _ (cardinalityProjectorKernel_hermitian P hh J θ),
    cardinalityProjectorKernel_trace_square P hp ht hd J θ hJ, Complex.ofReal_re]

section Moments
variable {Ω : S → Type*} [∀ s, MeasurableSpace (Ω s)]
  (ν : (s : S) → Measure (Ω s)) [∀ s, IsProbabilityMeasure (ν s)]

theorem cardinalityProjectorKernel_integrable (P : (s : S) → Ω s → Matrix I I ℂ)
    (hP : ∀ s, Integrable (P s) (ν s)) (J : Finset ℕ) (θ : ℕ → ℝ) :
    Integrable (fun ω : (s : S) → Ω s => cardinalityProjectorKernel (fun s => P s (ω s)) J θ)
      (Measure.pi ν) := signedProjectorComplementKernel_integrable ν P hP _ _

theorem cardinalityProjectorKernel_integral (P : (s : S) → Ω s → Matrix I I ℂ)
    (hP : ∀ s, Integrable (P s) (ν s)) (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, P s t ∂ν s) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    (∫ ω : (s : S) → Ω s, cardinalityProjectorKernel (fun s => P s (ω s)) J θ ∂Measure.pi ν) =
      (((∑ k ∈ J, θ k : ℝ) : ℂ) / (Fintype.card I : ℂ)^(Fintype.card S)) • 1 := by
  simp only [cardinalityProjectorKernel, signedProjectorComplementKernel_integral ν P hP hd hmean,
    cardinality_mass_sum hd J θ hJ]

theorem cardinalityProjectorKernel_integral_square (P : (s : S) → Ω s → Matrix I I ℂ)
    (hP : ∀ s, Integrable (P s) (ν s)) (hp : ∀ s t, P s t * P s t = P s t)
    (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, P s t ∂ν s) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    (∫ ω : (s : S) → Ω s, (cardinalityProjectorKernel (fun s => P s (ω s)) J θ)^2 ∂Measure.pi ν) =
      ((kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ : ℂ) /
        (Fintype.card I : ℂ)^(Fintype.card S)) • 1 := by
  simp only [cardinalityProjectorKernel, signedProjectorComplementKernel_integral_square ν P hP hp
    hd hmean _ (projectorCardinalitySubset_injective J), cardinality_square_mass_sum hd J θ hJ]

/-- All four S16 moment identities for the actual normalized signed kernel. -/
theorem cardinalityProjectorKernel_moments (P : (s : S) → Ω s → Matrix I I ℂ)
    (hm : ∀ s, AEStronglyMeasurable (P s) (ν s))
    (hh : ∀ s t, (P s t).IsHermitian) (hp : ∀ s t, P s t * P s t = P s t)
    (ht : ∀ s t, (P s t).trace = 1) (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, P s t ∂ν s) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (hθ : ∑ k ∈ J, θ k = 1) :
    let B := fun ω : (s : S) → Ω s => cardinalityProjectorKernel (fun s => P s (ω s)) J θ
    (∀ ω, (B ω).trace = 1 ∧ ((B ω)^2).trace =
      (kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ : ℂ)) ∧
    (∫ ω, B ω ∂Measure.pi ν) = (Fintype.card I : ℂ)^(-(Fintype.card S : ℤ)) • 1 ∧
    (∫ ω, (B ω)^2 ∂Measure.pi ν) =
      ((kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ : ℂ) /
        (Fintype.card I : ℂ)^(Fintype.card S)) • 1 := by
  have hi (s : S) := measurableProjector_integrable (ν s) (P s) (hm s)
    (Filter.Eventually.of_forall (hh s)) (Filter.Eventually.of_forall (hp s))
    (Filter.Eventually.of_forall (ht s))
  refine ⟨fun ω => ⟨?_, cardinalityProjectorKernel_trace_square _ (fun s => hp s (ω s))
    (fun s => ht s (ω s)) hd J θ hJ⟩, ?_, cardinalityProjectorKernel_integral_square ν P hi hp hd hmean J θ hJ⟩
  · simp only [cardinalityProjectorKernel_trace _ (fun s => ht s (ω s)) hd J θ hJ, hθ, Complex.ofReal_one]
  · simpa only [hθ, Complex.ofReal_one, one_div, _root_.zpow_neg, zpow_natCast] using
      cardinalityProjectorKernel_integral ν P hi hd hmean J θ hJ

end Moments
end CertificationGaussian
