import PMFramework.ExponentialFilter
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Why the hazard is proportional to operational cost (§4.1)

§4.1 takes the hazard to be `β Z_net` with one `β` for every history. Here that form is derived
from three qualitative premises about a survival function `F` of accumulated operational cost:

1. **One currency.** A history's survival depends on it only through its accumulated cost `S`:
   `P = F(S)`, one function `F` for every history. Cost is counted in primitive transitions, and
   nothing fails except through a transition.
2. **No memory of exposure.** Survival over consecutive stretches multiplies:
   `F(a + b) = F(a) F(b)`.
3. **Exposure never helps.** More accumulated cost never raises survival: `F` is antitone.

* `discrete_form`: when cost counts transitions (`S ∈ ℕ`), premises 1–2 alone give
  `F(n) = q^n = exp(−β n)` with `q = F(1)` and `β = −ln q`: every transition carries the same
  survival probability.
* `continuous_form`: for real-valued cost, premises 1–3 give `F(S) = exp(−β S)` for a single
  `β ≥ 0` (`additive_monotone_linear`: an additive, monotone function on `[0, ∞)` is linear).
* `hazard_proportional`: then a history with cost rate `Z` has survival
  `ExponentialFilter.survival (β Z)`, so its hazard is `β Z` (`ExponentialFilter.survival_hasDerivAt`),
  with the same `β` for every history.

The remaining inputs are the three premises, not a chosen functional form.
-/

open Real

namespace PMFramework.HazardForm

/-- **Discrete cost.** A multiplicative positive survival function of transition counts is
geometric: each transition is survived with the same probability `F 1`. -/
theorem discrete_form (F : ℕ → ℝ) (hpos : ∀ n, 0 < F n)
    (hmul : ∀ m n, F (m + n) = F m * F n) : ∀ n, F n = exp (-(-log (F 1)) * n) := by
  have h0 : F 0 = 1 := by
    have := hmul 0 0
    simp only [add_zero] at this
    have hp := hpos 0
    field_simp at this
    nlinarith [this]
  have hpow : ∀ n, F n = F 1 ^ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [hmul n 1, ih, pow_succ]
  intro n
  rw [hpow, neg_neg, mul_comm, ← log_pow, exp_log (pow_pos (hpos 1) n)]

/-- An additive, monotone function on `[0, ∞)` is linear. -/
theorem additive_monotone_linear (g : ℝ → ℝ)
    (hadd : ∀ a b, 0 ≤ a → 0 ≤ b → g (a + b) = g a + g b)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g a ≤ g b) : ∀ x, 0 ≤ x → g x = g 1 * x := by
  have g0 : g 0 = 0 := by have := hadd 0 0 le_rfl le_rfl; simp at this; linarith
  have gn : ∀ (n : ℕ) (x : ℝ), 0 ≤ x → g (n * x) = n * g x := by
    intro n x hx
    induction n with
    | zero => simp [g0]
    | succ n ih =>
      push_cast
      rw [add_mul, one_mul, hadd _ _ (by positivity) hx, ih]; ring
  have gdiv : ∀ (q : ℕ) (x : ℝ), 0 < q → 0 ≤ x → g (x / q) = g x / q := by
    intro q x hq hx
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have := gn q (x / q) (by positivity)
    rw [mul_div_cancel₀ _ hq'.ne'] at this
    rw [this]; field_simp
  have grat : ∀ (m q : ℕ), 0 < q → g (m / q) = g 1 * (m / q) := by
    intro m q hq
    rw [gdiv q m hq (by positivity), show (m : ℝ) = m * 1 by ring, gn m 1 zero_le_one]
    ring
  set c := g 1
  have hc : 0 ≤ c := by have := hmono 0 1 le_rfl zero_le_one; rw [g0] at this; exact this
  intro x hx
  -- for every q, c⌊xq⌋/q ≤ g x ≤ c(⌊xq⌋+1)/q
  have key : ∀ q : ℕ, 0 < q → |g x - c * x| ≤ c / q := by
    intro q hq
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    set m := ⌊x * q⌋₊
    have hm1 : (m : ℝ) ≤ x * q := Nat.floor_le (by positivity)
    have hm2 : x * q < m + 1 := Nat.lt_floor_add_one _
    have hlo : (m : ℝ) / q ≤ x := by rw [div_le_iff₀ hq']; exact hm1
    have hhi : x ≤ ((m + 1 : ℕ) : ℝ) / q := by
      rw [le_div_iff₀ hq']; push_cast; linarith
    have g1 := hmono _ _ (by positivity) hlo
    have g2 := hmono _ _ hx hhi
    rw [grat m q hq] at g1
    rw [grat (m + 1) q hq] at g2
    push_cast at g2
    have e : c * ((m + 1) / q) - c * (m / q) = c / q := by field_simp; ring
    have hhi' : x ≤ ((m : ℝ) + 1) / q := by push_cast at hhi; exact hhi
    have l1 : c * x ≤ c * ((m + 1) / q) := mul_le_mul_of_nonneg_left hhi' hc
    have l2 : c * (m / q) ≤ c * x := mul_le_mul_of_nonneg_left hlo hc
    rw [abs_le]
    constructor <;> linarith
  by_contra hne
  have hd : 0 < |g x - c * x| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨q, hq⟩ := exists_nat_gt (c / |g x - c * x|)
  have hqpos : (0 : ℝ) < q := lt_of_le_of_lt (div_nonneg hc hd.le) hq
  have hk := key q (by exact_mod_cast hqpos)
  rw [div_lt_iff₀ hd] at hq
  rw [le_div_iff₀ hqpos] at hk
  linarith

/-- **Continuous cost.** A positive, multiplicative, antitone survival function of accumulated
cost is `exp(−β S)` for a single `β ≥ 0`. -/
theorem continuous_form (F : ℝ → ℝ) (hpos : ∀ s, 0 ≤ s → 0 < F s)
    (hmul : ∀ a b, 0 ≤ a → 0 ≤ b → F (a + b) = F a * F b)
    (hanti : ∀ a b, 0 ≤ a → a ≤ b → F b ≤ F a) :
    ∃ β, 0 ≤ β ∧ ∀ s, 0 ≤ s → F s = exp (-β * s) := by
  set g : ℝ → ℝ := fun s => -log (F s)
  have hadd : ∀ a b, 0 ≤ a → 0 ≤ b → g (a + b) = g a + g b := by
    intro a b ha hb
    simp only [g, hmul a b ha hb, log_mul (hpos a ha).ne' (hpos b hb).ne']; ring
  have hmono : ∀ a b, 0 ≤ a → a ≤ b → g a ≤ g b := by
    intro a b ha hab
    simp only [g, neg_le_neg_iff]
    exact log_le_log (hpos b (ha.trans hab)) (hanti a b ha hab)
  have hlin := additive_monotone_linear g hadd hmono
  have g0 : g 0 = 0 := by have := hadd 0 0 le_rfl le_rfl; simp at this; linarith
  refine ⟨g 1, ?_, fun s hs => ?_⟩
  · have := hmono 0 1 le_rfl zero_le_one; rw [g0] at this; exact this
  · have h := hlin s hs
    simp only [g] at h
    rw [show -(-log (F 1)) * s = -(-log (F s)) by rw [h]; ring, neg_neg, exp_log (hpos s hs)]

/-- **The hazard is proportional to the cost rate, with a common `β`.** If every history's
survival is the same function `F` of its accumulated cost `S(T) = ∫₀ᵀ Z`, with `F` multiplicative
and antitone, then each history survives as `exp(−∫ β Z)`: its hazard is `β Z`
(`ExponentialFilter.survival_hasDerivAt`), and `β` does not depend on the history. -/
theorem hazard_proportional (F : ℝ → ℝ) (hpos : ∀ s, 0 ≤ s → 0 < F s)
    (hmul : ∀ a b, 0 ≤ a → 0 ≤ b → F (a + b) = F a * F b)
    (hanti : ∀ a b, 0 ≤ a → a ≤ b → F b ≤ F a) :
    ∃ β, 0 ≤ β ∧ ∀ (Z : ℝ → ℝ) (T : ℝ), 0 ≤ ∫ t in (0)..T, Z t →
      F (∫ t in (0)..T, Z t) = ExponentialFilter.survival (fun t => β * Z t) T := by
  obtain ⟨β, hβ, hF⟩ := continuous_form F hpos hmul hanti
  refine ⟨β, hβ, fun Z T hS => ?_⟩
  rw [hF _ hS, ExponentialFilter.cost_proportional]

end PMFramework.HazardForm
