import PMFramework.Selection
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Which event law persists

Apply the Selection Principle to candidate *event laws* on a finite label set `Ω`. A defect
referenced to label `ω` survives a step with probability `p ω` (it returns to its reference).
Two readings of a law's long-run cost rate:

* `averageRate p = −(1/|Ω|) Σ log p ω`: the reference visits every label equally often (as a
  clock that advances through all its states does), so a full visit is survived with
  probability `Π p ω`.
* `worstRate p = −log (min p)`: the reference is the law's least-favoured label, the defect
  that fails first.

* `averageRate_ge`, `averageRate_eq_iff`: every law has `averageRate ≥ log |Ω|`, with equality
  exactly for the uniform law (`log x ≤ x − 1`, the AM–GM inequality).
* `worstRate_ge`, `worstRate_eq_iff`: the same for the worst-case rate.
* `law_selection`: in any finite family of candidate laws containing the uniform law, with
  positive initial weights and actions of either rate up to `o(T)`, the surviving ensemble
  concentrates on the uniform law (`selected_uniform_average`, `selected_uniform_worst`).

Both readings select the same law, so the conclusion does not depend on which describes how a
defect's reference moves.
-/

open Real Finset Filter Topology

namespace PMFramework.LawSelection

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- A strictly positive probability law. -/
def PosLaw (p : Ω → ℝ) : Prop := (∀ ω, 0 < p ω) ∧ ∑ ω, p ω = 1

noncomputable def uniform : Ω → ℝ := fun _ => 1 / Fintype.card Ω

lemma card_pos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos

theorem uniform_law : PosLaw (uniform (Ω := Ω)) := by
  refine ⟨fun _ => by unfold uniform; exact div_pos one_pos card_pos, ?_⟩
  simp only [uniform, sum_const, card_univ, nsmul_eq_mul]
  field_simp [card_pos.ne']

/-- Long-run cost rate when the reference visits every label equally often. -/
noncomputable def averageRate (p : Ω → ℝ) : ℝ := -(∑ ω, log (p ω)) / Fintype.card Ω

/-- Cost rate when the reference is the least-favoured label. -/
noncomputable def worstRate (p : Ω → ℝ) : ℝ := -log (univ.inf' univ_nonempty p)

lemma log_eq_sub_one {x : ℝ} (hx : 0 < x) (h : log x = x - 1) : x = 1 := by
  by_contra hne
  have := log_lt_sub_one_of_pos hx hne
  linarith

lemma gap_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ x - 1 - log x := by
  have := log_le_sub_one_of_pos hx; linarith

lemma sum_scaled {p : Ω → ℝ} (hp : PosLaw p) :
    ∑ ω, (Fintype.card Ω * p ω - 1 - log (Fintype.card Ω * p ω)) =
      -(Fintype.card Ω * log (Fintype.card Ω) + ∑ ω, log (p ω)) := by
  have hn := card_pos (Ω := Ω)
  simp only [sum_sub_distrib, ← mul_sum, hp.2, sum_const, card_univ, nsmul_eq_mul, mul_one]
  rw [sum_congr rfl fun ω _ => log_mul hn.ne' (hp.1 ω).ne', sum_add_distrib, sum_const,
    card_univ, nsmul_eq_mul]
  ring

theorem averageRate_ge {p : Ω → ℝ} (hp : PosLaw p) : log (Fintype.card Ω) ≤ averageRate p := by
  have hn := card_pos (Ω := Ω)
  have h := sum_nonneg fun ω (_ : ω ∈ univ) => gap_nonneg (mul_pos hn (hp.1 ω))
  rw [sum_scaled hp] at h
  unfold averageRate
  rw [le_div_iff₀ hn]; nlinarith

theorem uniform_averageRate : averageRate (uniform (Ω := Ω)) = log (Fintype.card Ω) := by
  have hn := card_pos (Ω := Ω)
  simp only [averageRate, uniform, sum_const, card_univ, nsmul_eq_mul, one_div, log_inv]
  field_simp

theorem averageRate_eq_iff {p : Ω → ℝ} (hp : PosLaw p) :
    averageRate p = log (Fintype.card Ω) ↔ p = uniform := by
  constructor
  · intro h
    have hn := card_pos (Ω := Ω)
    have hz : ∑ ω, (Fintype.card Ω * p ω - 1 - log (Fintype.card Ω * p ω)) = 0 := by
      rw [sum_scaled hp]
      unfold averageRate at h
      rw [div_eq_iff hn.ne'] at h
      linarith
    have := (sum_eq_zero_iff_of_nonneg fun ω _ => gap_nonneg (mul_pos hn (hp.1 ω))).mp hz
    funext ω
    have h1 := log_eq_sub_one (mul_pos hn (hp.1 ω)) (by linarith [this ω (mem_univ ω)])
    simp only [uniform]
    field_simp; linarith
  · rintro rfl; exact uniform_averageRate

lemma inf_le {p : Ω → ℝ} (hp : PosLaw p) : univ.inf' univ_nonempty p ≤ 1 / Fintype.card Ω := by
  have h : ∑ _ω : Ω, univ.inf' univ_nonempty p ≤ ∑ ω, p ω :=
    sum_le_sum fun ω _ => inf'_le _ (mem_univ ω)
  rw [sum_const, card_univ, nsmul_eq_mul, hp.2] at h
  rw [le_div_iff₀ card_pos]; linarith

lemma inf_pos {p : Ω → ℝ} (hp : PosLaw p) : 0 < univ.inf' univ_nonempty p := by
  obtain ⟨ω, -, h⟩ := exists_mem_eq_inf' (univ_nonempty (α := Ω)) p
  rw [h]; exact hp.1 ω

theorem worstRate_ge {p : Ω → ℝ} (hp : PosLaw p) : log (Fintype.card Ω) ≤ worstRate p := by
  unfold worstRate
  have := log_le_log (inf_pos hp) (inf_le hp)
  rw [one_div, log_inv] at this; linarith

theorem worstRate_eq_iff {p : Ω → ℝ} (hp : PosLaw p) :
    worstRate p = log (Fintype.card Ω) ↔ p = uniform := by
  have hn := card_pos (Ω := Ω)
  constructor
  · intro h
    have hinf : univ.inf' univ_nonempty p = 1 / Fintype.card Ω := by
      unfold worstRate at h
      have h' : log (univ.inf' univ_nonempty p) = log (1 / Fintype.card Ω) := by
        rw [one_div, log_inv]; linarith
      exact log_injOn_pos (inf_pos hp) (by simp only [Set.mem_Ioi]; positivity) h'
    have hlow : ∀ ω, 1 / Fintype.card Ω ≤ p ω := fun ω => hinf ▸ inf'_le _ (mem_univ ω)
    have hz : ∑ ω, (p ω - 1 / Fintype.card Ω) = 0 := by
      rw [sum_sub_distrib, hp.2, sum_const, card_univ, nsmul_eq_mul]
      field_simp; ring
    have := (sum_eq_zero_iff_of_nonneg fun ω _ => sub_nonneg.2 (hlow ω)).mp hz
    funext ω; simp only [uniform]; linarith [this ω (mem_univ ω)]
  · rintro rfl
    unfold worstRate uniform
    rw [inf'_const, one_div, log_inv, neg_neg]

omit [Nonempty Ω] in
open Classical in
/-- **Law selection.** In a finite family of candidate laws containing the uniform law, scored by
any rate that the uniform law uniquely minimizes, the survivors concentrate on the uniform law. -/
theorem law_selection {ι : Type*} [Fintype ι] [Nonempty ι] (L : ι → Ω → ℝ)
    (hL : ∀ i, PosLaw (L i)) (rate : (Ω → ℝ) → ℝ)
    (hmin : ∀ p, PosLaw p → rate uniform ≤ rate p)
    (huniq : ∀ p, PosLaw p → (rate p = rate uniform ↔ p = uniform))
    (hu : ∃ i, L i = uniform) {w : ι → ℝ} (hw : ∀ i, 0 < w i) {β : ℝ} (hβ : 0 < β)
    (S : ι → ℝ → ℝ) (hS : ∀ i, Tendsto (fun T => (S i T - rate (L i) * T) / T) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ i ∈ univ.filter (fun i => L i = uniform),
      Selection.survivor w β (fun k => S k T) i) atTop (𝓝 1) := by
  have h := Selection.selection_principle hw hβ S (fun i => rate (L i)) hS
  have hm : univ.inf' univ_nonempty (fun i => rate (L i)) = rate uniform := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := hu
      exact (inf'_le _ (mem_univ i)).trans (by rw [hi])
    · exact le_inf' _ _ fun i _ => hmin _ (hL i)
  have hf : univ.filter (fun i => rate (L i) = univ.inf' univ_nonempty (fun i => rate (L i))) =
      univ.filter (fun i => L i = uniform) := by
    ext i; simp only [mem_filter, mem_univ, true_and, hm]; exact huniq _ (hL i)
  rw [hf] at h
  exact h

open Classical in
theorem selected_uniform_average {ι : Type*} [Fintype ι] [Nonempty ι] (L : ι → Ω → ℝ)
    (hL : ∀ i, PosLaw (L i)) (hu : ∃ i, L i = uniform) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {β : ℝ} (hβ : 0 < β) (S : ι → ℝ → ℝ)
    (hS : ∀ i, Tendsto (fun T => (S i T - averageRate (L i) * T) / T) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ i ∈ univ.filter (fun i => L i = uniform),
      Selection.survivor w β (fun k => S k T) i) atTop (𝓝 1) :=
  law_selection L hL averageRate
    (fun p hp => uniform_averageRate (Ω := Ω) ▸ averageRate_ge hp)
    (fun p hp => by rw [uniform_averageRate]; exact averageRate_eq_iff hp) hu hw hβ S hS

open Classical in
theorem selected_uniform_worst {ι : Type*} [Fintype ι] [Nonempty ι] (L : ι → Ω → ℝ)
    (hL : ∀ i, PosLaw (L i)) (hu : ∃ i, L i = uniform) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {β : ℝ} (hβ : 0 < β) (S : ι → ℝ → ℝ)
    (hS : ∀ i, Tendsto (fun T => (S i T - worstRate (L i) * T) / T) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ i ∈ univ.filter (fun i => L i = uniform),
      Selection.survivor w β (fun k => S k T) i) atTop (𝓝 1) := by
  have hu' : worstRate (uniform (Ω := Ω)) = log (Fintype.card Ω) :=
    (worstRate_eq_iff uniform_law).mpr rfl
  exact law_selection L hL worstRate (fun p hp => hu' ▸ worstRate_ge hp)
    (fun p hp => by rw [hu']; exact worstRate_eq_iff hp) hu hw hβ S hS

end PMFramework.LawSelection
