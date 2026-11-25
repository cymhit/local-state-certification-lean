import LocalCertification.Protocol.NearCriticalUpper
import LocalCertification.Protocol.MeasurableExecutionProductTransport

/-! The near-critical capped construction is admissible in every
universe of arbitrary-measurable local-product protocols. -/
set_option autoImplicit false
open MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum
open LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u
/-- The every-path cap and both optimal-cost upper bounds hold uniformly on the rectangle. -/
theorem qudit_nearCritical_product_upper_uniform (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (blo bhi η : ℝ)
    (hlo : 0 < blo) (hbounds : blo ≤ bhi) (hhi : bhi < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    ∃ C : ℝ, 0 < C ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
        atTop (nhds 1) ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ ψ ∈ good n,
        ∀ b : ℝ, blo ≤ b → b ≤ bhi → ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
          ∃ m : ℕ,
            ProductBudget.capFeasible.{u} (spherePureVector ψ)
              (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ m ∧
            (m : ℝ) ≤ C * ((n : ℝ)^(j+1) / (1 + (n : ℝ) * (max ε 0)^2)) * Real.log (1/δ) ∧
            ProductBudget.expectedBudget.{u} (spherePureVector ψ)
                (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ ≤
              ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ)
                (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ) ∧
            ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ)
                (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ) ≤
              ENNReal.ofReal (C * ((n : ℝ)^(j+1) / (1 + (n : ℝ) * (max ε 0)^2)) * Real.log (1/δ)) := by
  obtain ⟨C, hC, good, hcompact, hprob, N, hN, hprotocol⟩ :=
    qudit_nearCritical_basis_upper_uniform d j hd blo bhi η hlo hbounds hhi hη hwindow
  refine ⟨C, hC, good, hcompact, hprob, N, hN, ?_⟩
  intro n hn ψ hψ b hblo hbhi ε hε₀ hε₁ δ hδ₀ hδ₁
  obtain ⟨m, Q, hv, hc, hm⟩ := hprotocol n hn ψ hψ b hblo hbhi ε hε₀ hε₁ δ hδ₀ hδ₁
  have hf := ProductBudget.basis_capFeasible_universe.{u} Q.toRaw (spherePureVector ψ)
    (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ hv m hc
  refine ⟨m, hf, hm, ProductBudget.expectedBudget_le_maximumBudget _ _ _ _, ?_⟩
  calc
    _ ≤ ENat.toENNReal (m : ℕ∞) :=
      ENat.toENNReal_mono (ProductBudget.maximumBudget_le_of_feasible _ _ _ _ m hf)
    _ = (m : ℝ≥0∞) := ENat.toENNReal_coe m
    _ = ENNReal.ofReal (m : ℝ) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hm

theorem qudit_nearCritical_product_upper (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (b η : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    ∃ C : ℝ, 0 < C ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
        atTop (nhds 1) ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ ψ ∈ good n,
        ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
          ∃ m : ℕ,
            ProductBudget.capFeasible.{u} (spherePureVector ψ)
              (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ m ∧
            (m : ℝ) ≤ C * ((n : ℝ)^(j+1) / (1 + (n : ℝ) * (max ε 0)^2)) * Real.log (1/δ) ∧
            ProductBudget.expectedBudget.{u} (spherePureVector ψ)
                (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ ≤
              ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ)
                (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ) ∧
            ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ)
                (b + (1-b) * (gamma ((d : ℝ)+1) j + ε)) b δ) ≤
              ENNReal.ofReal (C * ((n : ℝ)^(j+1) / (1 + (n : ℝ) * (max ε 0)^2)) * Real.log (1/δ)) := by
  obtain ⟨C, hC, good, hc, hp, N, hN, h⟩ :=
    qudit_nearCritical_product_upper_uniform.{u} d j hd b b η hb0 le_rfl hb1 hη hwindow
  exact ⟨C, hC, good, hc, hp, N, hN, fun n hn ψ hψ => h n hn ψ hψ b le_rfl le_rfl⟩

end LocalCertification.Protocol.MeasurableExecution