import CertificationGaussian.CanonicalProductFrameWitness
import CertificationGaussian.ProductFrameNet
import CertificationGaussian.KernelCoveringAsymptotics
import CertificationGaussian.MeasurableFrameSphereTransfer

/-! # A common event for every product measurement frame

The event is defined by the entire product of the compact local-frame closures.
Every net center has an actual isotropic probability ensemble. Its tail bound,
the finite covering, and the one common radius event therefore yield a genuine
canonical-sphere bound, uniformly before any measurement or outcome space is
chosen. The same event has the identical full-unitary Haar probability.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ENNReal
namespace CertificationGaussian

/-- The all-frame event is closed, including its uncountable quantification. -/
theorem productFrame_good_isClosed (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ) :
    IsClosed {ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 |
      ∀ T ∈ signedProductFrameFamily (S := Fin n) (I := Fin d) J θ,
        gaussianFrameSphereScore T ψ ≤ (1+6/(n:ℝ))*kernelVarianceScale d n J θ} :=
  isClosed_gaussianFrameSphereScore_uniform_sublevel _ _

/-- Compactness is unconditional in the system size and kernel coefficients. -/
theorem productFrame_good_isCompact (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ) :
    IsCompact {ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 |
      ∀ T ∈ signedProductFrameFamily (S := Fin n) (I := Fin d) J θ,
        gaussianFrameSphereScore T ψ ≤ (1+6/(n:ℝ))*kernelVarianceScale d n J θ} :=
  (productFrame_good_isClosed d n J θ).isCompact

/-- All actual product POVMs belong to this single event; the cutoff does not
depend on their outcome spaces, probability witnesses, or local effects. -/
theorem productFrame_common_sphere_eventually {d : Nat} (hd : 2 ≤ d)
    (J : Finset Nat) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : Nat in atTop,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        {ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 |
          ∀ T ∈ signedProductFrameFamily (S := Fin n) (I := Fin d) J θ,
            gaussianFrameSphereScore T ψ ≤ (1+6/(n:ℝ))*kernelVarianceScale d n J θ}ᶜ ≤
          ENNReal.ofReal (Real.exp (-(Real.log d/16)*(n:ℝ)^3)) := by
  classical
  have neZeroD : NeZero d := ⟨by omega⟩
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  have hlog : 0 < Real.log (d:ℝ) := Real.log_pos hdR
  have ha4 : 0 < Real.log (d:ℝ)/4 := by positivity
  have ha8 : 0 < Real.log (d:ℝ)/8 := by positivity
  obtain ⟨A, _, hA⟩ := kernelCovering_eventually_quadratic hd J θ hθ
  filter_upwards [canonicalProductFrame_eventually_cubic hd J θ hθ,
    hA, eventually_quadratic_exp_mul_cubic ha4 A, quditRadius_eventually_cubic hd,
    eventually_two_mul_exp_cubic ha8, eventually_ge_atTop (max 2 (J.sup id))]
    with n htail hcardAsymp hnetAsymp hrad htwo hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hJ : ∀ k ∈ J, k ≤ n := fun k hk =>
    (Finset.le_sup (f := id) hk).trans ((le_max_right _ _).trans hn)
  have hv := kernelVarianceScale_pos hd J hJ θ hθ
  have hL := kernelWeightL1_pos J θ hθ
  have hdi : 2 ≤ Fintype.card (Fin d) := by simpa only [Fintype.card_fin] using hd
  have hni : 0 < Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using (show 0<n by omega)
  obtain ⟨net, hcenters, hcover, hcard⟩ :=
    signedProductFrameFamily_exists_scaled_net (S := Fin n) (I := Fin d)
      hdi hni J θ hL (kernelVarianceScale d n J θ) hv
  have hcard' : (net.card:ℝ) ≤ Real.exp (A*(n:ℝ)^2) := by
    apply le_trans _ hcardAsymp
    simpa only [Fintype.card_fin, kernelWeightL1] using hcard
  have hsymm : ∀ W ∈ net, ∀ X Y, inner ℝ X (W Y) = inner ℝ (W X) Y := by
    intro W hW X Y
    obtain ⟨U,rfl⟩ := hcenters W hW
    exact canonicalProductFrame_symmetric U J θ X Y
  have hidentity : ∀ W ∈ net,
      W (matrixHilbertSchmidt (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) =
        (Fintype.card (QuditIndex d n):ℝ)⁻¹ • matrixHilbertSchmidt 1 := by
    intro W hW
    obtain ⟨U,rfl⟩ := hcenters W hW
    exact canonicalProductFrame_identity U hdi J θ
      (by simpa only [Fintype.card_fin] using hJ) hθ
  have hcover' : ∀ T ∈ signedProductFrameFamily (S := Fin n) (I := Fin d) J θ,
      ∃ W ∈ net, (Fintype.card (QuditIndex d n):ℝ)^2 * ‖T-W‖ ≤
        kernelVarianceScale d n J θ/(n:ℝ) := by
    intro T hT
    obtain ⟨W,hW,hclose⟩ := hcover T hT
    refine ⟨W,hW,?_⟩
    simpa only [QuditIndex, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hclose
  have hcenterTail : ∀ W ∈ net,
      pairedGaussian (QuditIndex d n)
        {x | kernelVarianceScale d n J θ/n ≤
          |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
            (W (matrixHilbertSchmidt (gaussianCenteredProjector x)))-kernelVarianceScale d n J θ|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log d/4)*(n:ℝ)^3)) := by
    intro W hW
    obtain ⟨U,rfl⟩ := hcenters W hW
    exact htail U
  let bad := {x : Fin 2 × QuditIndex d n → ℝ | ∃ W ∈ net,
    kernelVarianceScale d n J θ/n ≤
      |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
        (W (matrixHilbertSchmidt (gaussianCenteredProjector x)))-kernelVarianceScale d n J θ|}
  have hbad : pairedGaussian (QuditIndex d n) bad ≤
      ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := by
    have he : bad = ⋃ W ∈ net,
        {x | kernelVarianceScale d n J θ/n ≤
          |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
            (W (matrixHilbertSchmidt (gaussianCenteredProjector x)))-kernelVarianceScale d n J θ|} := by
      ext x
      constructor
      · rintro ⟨W,hW,hx⟩
        exact Set.mem_iUnion.mpr ⟨W,Set.mem_iUnion.mpr ⟨hW,hx⟩⟩
      · intro hx
        obtain ⟨W,hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hW,hx⟩ := Set.mem_iUnion.mp hx
        exact ⟨W,hW,hx⟩
    rw [he]
    calc
      _ ≤ ∑ W ∈ net, pairedGaussian (QuditIndex d n)
          {x | kernelVarianceScale d n J θ/n ≤
            |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
              (W (matrixHilbertSchmidt (gaussianCenteredProjector x)))-kernelVarianceScale d n J θ|} :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ _W ∈ net, ENNReal.ofReal (Real.exp (-(Real.log d/4)*(n:ℝ)^3)) :=
        Finset.sum_le_sum hcenterTail
      _ = ENNReal.ofReal ((net.card:ℝ)*Real.exp (-(Real.log d/4)*(n:ℝ)^3)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h := (mul_le_mul_of_nonneg_right hcard' (Real.exp_nonneg _)).trans hnetAsymp
        convert h using 1
        congr 1
        ring
  have hrad' : pairedGaussian (QuditIndex d n)
      {x | ((n:ℝ)^2)⁻¹ ≤ |gaussianRadius (QuditIndex d n) x-1|} ≤
        ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := by
    apply hrad.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hnonneg := mul_nonneg hlog.le (show 0 ≤ (n:ℝ)^3 by positivity)
    nlinarith
  have hsphere := gaussianFrame_common_sphere_failure_le
    (signedProductFrameFamily (S := Fin n) (I := Fin d) J θ) net
    hsymm hidentity hnR hv.le hcover'
  refine hsphere.trans ((measure_union_le _ _).trans ((add_le_add hbad hrad').trans ?_))
  calc
    _ = ENNReal.ofReal (2*Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _), two_mul]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      convert htwo using 1
      congr 1
      ring

/-- Genuine Haar orbits of all initial unit vectors obey the same all-frame
bound, with one cutoff chosen before the initial vector or measurement. -/
theorem productFrame_common_haar_eventually {d : Nat} (hd : 2 ≤ d)
    (J : Finset Nat) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : Nat in atTop,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
        complexUnitaryHaar (QuditIndex d n)
          {U | ¬ ∀ T ∈ signedProductFrameFamily (S := Fin n) (I := Fin d) J θ,
            gaussianFrameSphereScore T (complexUnitarySphereAction (QuditIndex d n) U ψ) ≤
              (1+6/(n:ℝ))*kernelVarianceScale d n J θ} ≤
            ENNReal.ofReal (Real.exp (-(Real.log d/16)*(n:ℝ)^3)) := by
  have : NeZero d := ⟨by omega⟩
  filter_upwards [productFrame_common_sphere_eventually hd J θ hθ] with n hn
  intro ψ
  rw [gaussianFrame_common_haar_failure_eq]
  exact hn

end CertificationGaussian
