import PMFramework.Selection
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Finite Gibbs survival weights and their concentration

The survival filter `exp(−β S)` on a finite family of histories with equal prior weight
(moved here from Paper II's `Survival` and `Concentration`, which now import it).

* `weight_add`, `survival_ratio`, `weight_order`: weights multiply over consecutive costs, ratios
  depend only on cost differences, and lower cost survives better.
* `finite_penalty_survives`: a finite penalty suppresses a history but does not eliminate it.
* `probabilities_sum_one`, `probability_pos`: the normalized weights are a positive probability
  distribution; `probability_eq_survivor` identifies them with `Selection.survivor` at equal prior
  weights.
* `probability_limit`: as `β → ∞` the distribution concentrates uniformly on the minimum-cost
  histories, ties sharing equally.

The exponential law is the modelling input of §4.1; its consequences are proved here.
-/

noncomputable section
namespace PMFramework.Gibbs
open Finset Filter
open scoped Topology

def weight (β action : ℝ) : ℝ := Real.exp (-β * action)

theorem weight_pos (β action : ℝ) : 0 < weight β action := Real.exp_pos _

theorem weight_add (β a b : ℝ) : weight β (a+b) = weight β a * weight β b := by
  simp only [weight, ← Real.exp_add]
  congr 1
  ring

theorem survival_ratio (β a b : ℝ) : weight β b / weight β a = weight β (b-a) := by
  rw [weight, weight, ← Real.exp_sub, weight]
  congr 1
  ring

theorem weight_order {β a b : ℝ} (hβ : 0 < β) :
    weight β b ≤ weight β a ↔ a ≤ b := by
  simp only [weight, Real.exp_le_exp]
  constructor <;> intro h <;> nlinarith

/-- A finite action penalty suppresses a history but does not eliminate it. -/
theorem finite_penalty_survives (β a δ : ℝ) :
    0 < weight β (a+δ) / weight β a := div_pos (weight_pos _ _) (weight_pos _ _)

def partition {ι : Type*} [Fintype ι] (β : ℝ) (S : ι → ℝ) : ℝ := ∑ i, weight β (S i)

def probability {ι : Type*} [Fintype ι] (β : ℝ) (S : ι → ℝ) (i : ι) : ℝ :=
  weight β (S i) / partition β S

theorem partition_pos {ι : Type*} [Fintype ι] [Nonempty ι] (β : ℝ) (S : ι → ℝ) :
    0 < partition β S := by
  exact sum_pos (fun _ _ => weight_pos _ _) univ_nonempty

theorem probabilities_sum_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (S : ι → ℝ) : ∑ i, probability β S i = 1 := by
  simp only [probability, ← sum_div]
  exact div_self (ne_of_gt (partition_pos β S))

theorem probability_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (S : ι → ℝ) (i : ι) : 0 < probability β S i :=
  div_pos (weight_pos _ _) (partition_pos _ _)

/-- At equal prior weights the Gibbs distribution is the survivor distribution of `Selection`. -/
theorem probability_eq_survivor {ι : Type*} [Fintype ι] (β : ℝ) (S : ι → ℝ) (i : ι) :
    probability β S i = Selection.survivor (fun _ => 1) β S i := by
  simp only [probability, partition, weight, Selection.survivor, one_mul]

section Concentration
theorem penalty_vanishes {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun β : ℝ => weight β δ) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hδ)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun β => by dsimp [weight]; congr 1; ring)

variable {X : Type*} [Fintype X] [DecidableEq X]

def minima (S : X → ℝ) (g : X) : Finset X := univ.filter (fun i => S i = S g)

omit [DecidableEq X] in
theorem minima_nonempty (S : X → ℝ) (g : X) : (minima S g).Nonempty :=
  ⟨g, by simp [minima]⟩

omit [Fintype X] [DecidableEq X] in
theorem relative_limit (S : X → ℝ) (g : X) (hmin : ∀ i, S g ≤ S i) (i : X) :
    Tendsto (fun β : ℝ => weight β (S i - S g)) atTop
      (𝓝 (if S i = S g then 1 else 0)) := by
  by_cases hi : S i = S g
  · simp [hi, weight]
  · simpa [hi] using penalty_vanishes (lt_of_le_of_ne (hmin i) (Ne.symm hi) |> sub_pos.mpr)

omit [DecidableEq X] in
theorem probability_shift (β : ℝ) (S : X → ℝ) (g i : X) :
    probability β S i = probability β (fun j => S j - S g) i := by
  have hf : ∀ j, weight β (S j) = weight β (S g) * weight β (S j - S g) := by
    intro j
    rw [← weight_add]
    congr 1; ring
  change weight β (S i) / (∑ j, weight β (S j)) = _
  rw [hf i, show (∑ j, weight β (S j)) =
    weight β (S g) * (∑ j, weight β (S j - S g)) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => hf j)]
  exact mul_div_mul_left _ _ (ne_of_gt (weight_pos β (S g)))

omit [DecidableEq X] in
/-- The complete finite-ensemble zero-temperature limit, including ties. -/
theorem probability_limit (S : X → ℝ) (g : X) (hmin : ∀ i, S g ≤ S i) (i : X) :
    Tendsto (fun β : ℝ => probability β S i) atTop
      (𝓝 (if S i = S g then 1 / (minima S g).card else 0)) := by
  have hsum : Tendsto (fun β : ℝ => ∑ j, weight β (S j - S g)) atTop
      (𝓝 ((minima S g).card : ℝ)) := by
    convert tendsto_finsetSum univ (fun j _ => relative_limit S g hmin j) using 1
    simp [minima, Finset.sum_boole]
  have hn : ((minima S g).card : ℝ) ≠ 0 := by
    exact_mod_cast (minima_nonempty S g).card_pos.ne'
  have h := (relative_limit S g hmin i).div hsum hn
  have heq : (fun β : ℝ => probability β S i) =
      (fun β : ℝ => weight β (S i - S g) / ∑ j, weight β (S j - S g)) := by
    funext β; exact probability_shift β S g i
  rw [heq]
  convert h using 1
  split_ifs <;> simp

end Concentration

end PMFramework.Gibbs
