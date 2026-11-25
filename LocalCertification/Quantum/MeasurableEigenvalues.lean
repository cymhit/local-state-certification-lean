import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Instances.Matrix

/-! # Ordered eigenvalues of a measurable Hermitian matrix

The values of the characteristic polynomial at the natural numbers determine
its ordered list of real roots with multiplicities. These evaluations form a
Borel embedding of the space of ordered real tuples. The measurable inverse
therefore applies to a matrix-valued function on any measurable space.
-/

set_option autoImplicit false
open MeasureTheory Matrix Polynomial
noncomputable section
namespace LocalCertification.Quantum

private def spectralSamples {m : ℕ} (v : Fin m → ℝ) (k : ℕ) : ℂ :=
  ∏ i, ((k : ℂ) - (v i : ℂ))

private def spectrumPolynomial {m : ℕ} (v : Fin m → ℝ) : Polynomial ℂ :=
  ∏ i, (X - C (v i : ℂ))

private theorem sorted_spectrum_roots {m : ℕ} (v : Fin m → ℝ) (hv : Antitone v) :
    ((spectrumPolynomial v).roots.map Complex.re).sort (· ≥ ·) = List.ofFn v := by
  classical
  have hf : (spectrumPolynomial v).roots = Finset.univ.val.map (fun i => (v i : ℂ)) := by
    rw [spectrumPolynomial, roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero]
  rw [hf, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Multiset.coe_sort]
  simp only [Function.comp_def, Complex.ofReal_re]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hv.sortedGE_ofFn

private theorem spectralSamples_injective (m : ℕ) :
    Function.Injective (fun v : {v : Fin m → ℝ // Antitone v} => spectralSamples v.val) := by
  intro v w h
  have hp : spectrumPolynomial v.val = spectrumPolynomial w.val := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).mono
    rintro _ ⟨k, rfl⟩
    simpa [spectrumPolynomial, spectralSamples, eval_prod] using congrFun h k
  apply Subtype.ext
  rw [← List.ofFn_inj, ← sorted_spectrum_roots _ v.property,
    ← sorted_spectrum_roots _ w.property, hp]

/-- Ordered eigenvalues are measurable even when the outcome space does not
carry any topology. Repeated values are listed with their multiplicities. -/
theorem measurable_ordered_eigenvalues {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (A : Ω → Matrix I I ℂ) (hA : Measurable A)
    (hherm : ∀ s, (A s).IsHermitian) :
    Measurable (fun s => (hherm s).eigenvalues₀) := by
  classical
  let m := Fintype.card I
  let S := {v : Fin m → ℝ | Antitone v}
  have hclosed : IsClosed S := by
    change IsClosed {v : Fin m → ℝ | ∀ ⦃i j⦄, i ≤ j → v j ≤ v i}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply j) (continuous_apply i)
  let : PolishSpace S := hclosed.polishSpace
  let f : S → ℕ → ℂ := fun v => spectralSamples v.val
  have hf : Continuous f := by
    apply continuous_pi
    intro k
    unfold f spectralSamples
    exact continuous_finsetProd _ fun i _ => continuous_const.sub
      (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val))
  have he := hf.measurableEmbedding (spectralSamples_injective m)
  let v : Ω → S := fun s => ⟨(hherm s).eigenvalues₀, (hherm s).eigenvalues₀_antitone⟩
  suffices h : Measurable v from measurable_subtype_coe.comp h
  apply he.measurable_comp_iff.mp
  apply Measurable.of_eval
  intro k
  have hdet : Measurable (fun s => (A s).charpoly.eval (k : ℂ)) := by
    simp only [Matrix.eval_charpoly]
    apply (continuous_id.matrix_det).measurable.comp
    apply Measurable.of_eval_matrix
    intro i j
    exact measurable_const.sub (hA.eval_matrix (i := i) (j := j))
  convert hdet using 1
  funext s
  change (∏ i, ((k : ℂ) - ((hherm s).eigenvalues₀ i : ℂ))) = _
  rw [(hherm s).charpoly_eq, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  symm
  exact Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun i => (k : ℂ) - ((hherm s).eigenvalues₀ i : ℂ))

end LocalCertification.Quantum
