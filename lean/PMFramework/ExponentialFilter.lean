import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The exponential filter (§4.1)

* `survival_hasDerivAt`: for a continuous hazard `h`, `P(T) = exp(−∫₀ᵀ h)` satisfies the hazard
  equation `P' = −h P`, with `P(0) = 1` (`survival_zero`). This is eq. (survival_prob).
* `cost_proportional`: with `h = β Z_net`, `P(T) = exp(−β S)` where `S = ∫₀ᵀ Z_net` is the
  accumulated operational action.
* `survival_mul`: survival over consecutive intervals multiplies.
* `discrete_survival`: `N` updates, each survived with probability `q ∈ (0,1]` and costing `c₀`,
  give `q^N = exp(−β S)` with `S = N c₀` and `β = −ln q / c₀` (eq. discrete_survival).
-/

open Real intervalIntegral

namespace PMFramework.ExponentialFilter

/-- Survival to time `T` under a hazard `h`. -/
noncomputable def survival (h : ℝ → ℝ) (T : ℝ) : ℝ := exp (-∫ t in (0)..T, h t)

theorem survival_zero (h : ℝ → ℝ) : survival h 0 = 1 := by simp [survival]

theorem survival_pos (h : ℝ → ℝ) (T : ℝ) : 0 < survival h T := exp_pos _

/-- **The hazard equation.** `P' = −h P`. -/
theorem survival_hasDerivAt {h : ℝ → ℝ} (hc : Continuous h) (T : ℝ) :
    HasDerivAt (survival h) (-h T * survival h T) T := by
  have hI : HasDerivAt (fun T => ∫ t in (0)..T, h t) (h T) T :=
    integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  have := (hI.neg).exp
  unfold survival
  convert this using 1
  simp only [Pi.neg_apply]; ring

/-- With a cost-proportional hazard the filter is exponential in accumulated action. -/
theorem cost_proportional (Z : ℝ → ℝ) (β T : ℝ) :
    survival (fun t => β * Z t) T = exp (-β * ∫ t in (0)..T, Z t) := by
  unfold survival
  rw [intervalIntegral.integral_const_mul]; ring_nf

/-- Survival over consecutive intervals multiplies. -/
theorem survival_mul {h : ℝ → ℝ} (hc : Continuous h) (T₁ T₂ : ℝ) :
    survival h T₂ = survival h T₁ * exp (-∫ t in T₁..T₂, h t) := by
  unfold survival
  rw [← exp_add, ← integral_add_adjacent_intervals (hc.intervalIntegrable 0 T₁)
    (hc.intervalIntegrable T₁ T₂)]
  ring_nf

/-- **The discrete filter.** -/
theorem discrete_survival {q c₀ : ℝ} (hq : 0 < q) (hc : 0 < c₀) (N : ℕ) :
    q ^ N = exp (-((-log q / c₀) * (N * c₀))) := by
  have : -((-log q / c₀) * (N * c₀)) = N * log q := by field_simp
  rw [this, ← log_pow, exp_log (pow_pos hq N)]

end PMFramework.ExponentialFilter
