import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.Monoid

/-!
# The Selection Principle (§4.2–4.4)

A finite family of candidate histories `i` with positive initial weights `p i`, a common
coefficient `β > 0`, and accumulated actions `S i T`.

* `survivor`: the distribution conditional on survival, eq. (survivor_distribution).
* `survivor_sum`: it is a probability distribution.
* `survivor_odds`: relative representation, eq. (severity): initial odds times
  `exp(−β(S_i − S_j))`.
* `selection`: **Proposition (Selection by Operational Action).** If `S i T = s i T + o(T)`,
  every candidate whose asymptotic rate exceeds the least rate `s*` has survivor share tending
  to zero, and the candidates at `s*` together tend to one (`selection_principle`).
* `selection_timescale`: for constant rates with gap `Δs > 0` the odds fall by `e` over
  `τ = 1/(βΔs)`, eq. (selection_timescale).

The cost-proportional hazard and the common `β` are the modelling assumption stated in §4.1;
they enter here as the form of `survivor`.
-/

open Real Filter Topology Finset

namespace PMFramework.Selection

variable {ι : Type*} [Fintype ι]

/-- Representation conditional on survival. -/
noncomputable def survivor (p : ι → ℝ) (β : ℝ) (S : ι → ℝ) (i : ι) : ℝ :=
  p i * exp (-β * S i) / ∑ j, p j * exp (-β * S j)

omit [Fintype ι] in
lemma weight_pos {p : ι → ℝ} (hp : ∀ i, 0 < p i) (β : ℝ) (S : ι → ℝ) (i : ι) :
    0 < p i * exp (-β * S i) := mul_pos (hp i) (exp_pos _)

lemma total_pos [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) (β : ℝ) (S : ι → ℝ) :
    0 < ∑ j, p j * exp (-β * S j) :=
  sum_pos (fun j _ => weight_pos hp β S j) univ_nonempty

theorem survivor_nonneg [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) (β : ℝ) (S : ι → ℝ)
    (i : ι) : 0 ≤ survivor p β S i :=
  (div_pos (weight_pos hp β S i) (total_pos hp β S)).le

theorem survivor_sum [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) (β : ℝ) (S : ι → ℝ) :
    ∑ i, survivor p β S i = 1 := by
  unfold survivor
  rw [← sum_div, div_self (total_pos hp β S).ne']

/-- **Relative representation**, eq. (severity). -/
theorem survivor_odds [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) (β : ℝ) (S : ι → ℝ)
    (i j : ι) : survivor p β S i / survivor p β S j = p i / p j * exp (-β * (S i - S j)) := by
  unfold survivor
  have hT := (total_pos hp β S).ne'
  have hj := (hp j).ne'
  rw [div_div_div_cancel_right₀ hT, show -β * (S i - S j) = -β * S i - -β * S j by ring, exp_sub]
  field_simp

/-- A survivor share is at most its odds against any other candidate. -/
lemma survivor_le_odds [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) (β : ℝ) (S : ι → ℝ)
    (i j : ι) : survivor p β S i ≤ p i / p j * exp (-β * (S i - S j)) := by
  rw [← survivor_odds hp β S i j]
  have hj : 0 < survivor p β S j := div_pos (weight_pos hp β S j) (total_pos hp β S)
  have hle : survivor p β S j ≤ 1 := by
    rw [← survivor_sum hp β S]
    exact single_le_sum (fun k _ => survivor_nonneg hp β S k) (mem_univ j)
  rw [le_div_iff₀ hj]
  exact mul_le_of_le_one_right (survivor_nonneg hp β S i) hle

/-- **Selection.** A candidate with a larger asymptotic cost rate than some other candidate
vanishes from the surviving ensemble. -/
theorem selection [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) {β : ℝ} (hβ : 0 < β)
    (S : ι → ℝ → ℝ) (s : ι → ℝ)
    (hS : ∀ i, Tendsto (fun T => (S i T - s i * T) / T) atTop (𝓝 0))
    {i j : ι} (hij : s j < s i) :
    Tendsto (fun T => survivor p β (fun k => S k T) i) atTop (𝓝 0) := by
  set δ := s i - s j with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- (S i T − S j T)/T → δ
  have hlim : Tendsto (fun T => (S i T - S j T) / T - δ) atTop (𝓝 0) := by
    have := (hS i).sub (hS j)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with T hT
    field_simp; ring
  have hev : ∀ᶠ T in atTop, δ / 2 * T ≤ S i T - S j T := by
    have h1 := (hlim.eventually (Ioo_mem_nhds (by linarith : -(δ / 2) < 0)
      (by linarith : (0 : ℝ) < δ / 2)))
    filter_upwards [h1, eventually_gt_atTop 0] with T hT hTpos
    obtain ⟨hlo, -⟩ := hT
    have : δ / 2 < (S i T - S j T) / T := by linarith
    rw [lt_div_iff₀ hTpos] at this
    linarith
  have hbound : ∀ᶠ T in atTop, survivor p β (fun k => S k T) i ≤
      p i / p j * exp (-(β * (δ / 2)) * T) := by
    filter_upwards [hev] with T hT
    refine (survivor_le_odds hp β _ i j).trans ?_
    apply mul_le_mul_of_nonneg_left _ (div_pos (hp i) (hp j)).le
    apply exp_le_exp.mpr
    nlinarith
  have hzero : Tendsto (fun T => p i / p j * exp (-(β * (δ / 2)) * T)) atTop (𝓝 0) := by
    have hk : 0 < β * (δ / 2) := by positivity
    have h := (tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hk))
    have := h.const_mul (p i / p j)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun T => ?_)
    simp [Function.comp, neg_mul]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Eventually.of_forall fun T => survivor_nonneg hp β _ i) hbound

/-- **Proposition (Selection by Operational Action).** The candidates with the least asymptotic
cost rate take over the distribution conditional on survival. -/
theorem selection_principle [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) {β : ℝ} (hβ : 0 < β)
    (S : ι → ℝ → ℝ) (s : ι → ℝ)
    (hS : ∀ i, Tendsto (fun T => (S i T - s i * T) / T) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ i ∈ univ.filter (fun i => s i = univ.inf' univ_nonempty s),
      survivor p β (fun k => S k T) i) atTop (𝓝 1) := by
  classical
  obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι)) s
  set m := univ.inf' univ_nonempty s
  have hrest : Tendsto (fun T => ∑ i ∈ univ.filter (fun i => ¬ s i = m),
      survivor p β (fun k => S k T) i) atTop (𝓝 0) := by
    have := tendsto_finsetSum (univ.filter (fun i => ¬ s i = m))
      (fun i hi => selection hp hβ S s hS (i := i) (j := j) (by
        have h1 : m ≤ s i := inf'_le _ (mem_univ i)
        have h2 : s i ≠ m := (mem_filter.mp hi).2
        rw [← hj]; exact lt_of_le_of_ne h1 (Ne.symm h2)))
    simpa using this
  have hsplit : ∀ T, ∑ i ∈ univ.filter (fun i => s i = m), survivor p β (fun k => S k T) i =
      1 - ∑ i ∈ univ.filter (fun i => ¬ s i = m), survivor p β (fun k => S k T) i := by
    intro T
    rw [← survivor_sum hp β (fun k => S k T), ← sum_filter_add_sum_filter_not univ
      (fun i => s i = m)]
    ring
  simp_rw [hsplit]
  simpa using hrest.const_sub 1

/-- **Selection timescale.** For constant rates with gap `Δs > 0` the relative odds fall by a
factor `e` over `τ = 1/(βΔs)`. -/
theorem selection_timescale [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) {β : ℝ} (hβ : 0 < β)
    (s : ι → ℝ) {i j : ι} (hij : s j < s i) (T : ℝ) :
    survivor p β (fun k => s k * (T + 1 / (β * (s i - s j)))) i /
        survivor p β (fun k => s k * (T + 1 / (β * (s i - s j)))) j =
      exp (-1) * (survivor p β (fun k => s k * T) i / survivor p β (fun k => s k * T) j) := by
  rw [survivor_odds hp, survivor_odds hp]
  have hd : β * (s i - s j) ≠ 0 := (mul_pos hβ (sub_pos.2 hij)).ne'
  have : -β * (s i * (T + 1 / (β * (s i - s j))) - s j * (T + 1 / (β * (s i - s j)))) =
      -1 + -β * (s i * T - s j * T) := by
    have hτ : β * (s i - s j) * (1 / (β * (s i - s j))) = 1 := mul_one_div_cancel hd
    linear_combination (-1) * hτ
  rw [this, exp_add]; ring

end PMFramework.Selection
