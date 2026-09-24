import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2758_1

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(x - n) ^ 2)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ (l x : ℝ), 0 < l → x ∈ Set.Ioo (-l) l →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro l x hl hx
  have hsq : Tendsto (fun n : ℕ => -(x - (n : ℝ)) ^ 2) atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro b
    obtain ⟨N, hN⟩ :=
      exists_nat_gt (x + Real.sqrt (max (-b) 0))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hncast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    have hlarge : x + Real.sqrt (max (-b) 0) < (n : ℝ) :=
      lt_of_lt_of_le hN hncast
    have hsqrt_nonneg : 0 ≤ Real.sqrt (max (-b) 0) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (max (-b) 0)) ^ 2 = max (-b) 0 :=
      Real.sq_sqrt (le_max_right _ _)
    have hprod :
        0 ≤ (((n : ℝ) - x) - Real.sqrt (max (-b) 0)) *
          (((n : ℝ) - x) + Real.sqrt (max (-b) 0)) := by
      apply mul_nonneg
      · linarith
      · linarith
    have hmax : -b ≤ max (-b) 0 := le_max_left _ _
    nlinarith [hprod]
  change Tendsto (fun n : ℕ => Real.exp (-(x - (n : ℝ)) ^ 2)) atTop (𝓝 0)
  simpa only [Function.comp_apply] using Real.tendsto_exp_atBot.comp hsq

theorem gap2 :
    ∀ (l x : ℝ), 0 < l → x ∈ Set.Ioo (-l) l → (0 : ℝ) = 0 := by
  intro l x hl hx
  rfl

theorem gap3 :
    ∀ (l x : ℝ), 0 < l → x ∈ Set.Ioo (-l) l →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro l x hl hx
  exact gap1 l x hl hx

theorem gap4 :
    ∀ (l x : ℝ) (n : ℕ), 0 < l → x ∈ Set.Ioo (-l) l →
      l < (n : ℝ) → |term n x| = Real.exp (-(x - n) ^ 2) := by
  intro l x n hl hx hn
  simp [term, abs_of_pos (Real.exp_pos _)]

theorem gap5 :
    ∀ (l x : ℝ) (n : ℕ), 0 < l → x ∈ Set.Ioo (-l) l →
      l < (n : ℝ) →
        Real.exp (-(x - n) ^ 2) ≤ Real.exp (-((n : ℝ) - l) ^ 2) := by
  intro l x n hl hx hn
  apply Real.exp_le_exp.mpr
  have hnl : 0 ≤ (n : ℝ) - l := by linarith
  have hnx : 0 ≤ (n : ℝ) - x := by linarith [hx.2]
  have hprod :
      0 ≤ (((n : ℝ) - x) - ((n : ℝ) - l)) *
        (((n : ℝ) - x) + ((n : ℝ) - l)) := by
    apply mul_nonneg
    · linarith [hx.2]
    · linarith
  nlinarith [hprod]

theorem gap6 :
    ∀ (l x : ℝ) (n : ℕ), 0 < l → x ∈ Set.Ioo (-l) l →
      l < (n : ℝ) → |term n x| ≤ Real.exp (-((n : ℝ) - l) ^ 2) := by
  intro l x n hl hx hn
  calc
    |term n x| = Real.exp (-(x - n) ^ 2) := gap4 l x n hl hx hn
    _ ≤ Real.exp (-((n : ℝ) - l) ^ 2) := gap5 l x n hl hx hn

theorem gap7 :
    ∀ (l x ε : ℝ) (n : ℕ), 0 < l → x ∈ Set.Ioo (-l) l →
      0 < ε → ε < 1 → l < (n : ℝ) →
      Real.exp (-((n : ℝ) - l) ^ 2) < ε → |term n x| < ε := by
  intro l x ε n hl hx hε hε1 hn hexp
  exact lt_of_le_of_lt (gap6 l x n hl hx hn) hexp

theorem gap8 :
    ∀ (l ε : ℝ) (n : ℕ), 0 < l → 0 < ε → ε < 1 →
      l + Real.sqrt (Real.log (1 / ε)) < (n : ℝ) →
        l < (n : ℝ) ∧ Real.exp (-((n : ℝ) - l) ^ 2) < ε := by
  intro l ε n hl hε hε1 hn
  have hinv : 1 < 1 / ε := by
    apply (lt_div_iff₀ hε).2
    simpa using hε1
  have hlogpos : 0 < Real.log (1 / ε) := Real.log_pos hinv
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log (1 / ε)) := Real.sqrt_nonneg _
  have hsqrt_sq :
      (Real.sqrt (Real.log (1 / ε))) ^ 2 = Real.log (1 / ε) :=
    Real.sq_sqrt (le_of_lt hlogpos)
  have hdist : Real.sqrt (Real.log (1 / ε)) < (n : ℝ) - l := by
    linarith
  have hprod :
      0 < (((n : ℝ) - l) - Real.sqrt (Real.log (1 / ε))) *
        (((n : ℝ) - l) + Real.sqrt (Real.log (1 / ε))) := by
    apply mul_pos
    · linarith
    · nlinarith
  have hsq : Real.log (1 / ε) < ((n : ℝ) - l) ^ 2 := by
    nlinarith [hprod]
  have hlog : Real.log (1 / ε) = -Real.log ε := by
    rw [one_div, Real.log_inv]
  constructor
  · linarith
  · calc
      Real.exp (-((n : ℝ) - l) ^ 2) < Real.exp (Real.log ε) := by
        apply Real.exp_lt_exp.mpr
        nlinarith [hsq]
      _ = ε := Real.exp_log hε

theorem gap9 :
    ∀ (l x ε : ℝ) (n : ℕ), 0 < l → x ∈ Set.Ioo (-l) l →
      0 < ε → ε < 1 →
      l + Real.sqrt (Real.log (1 / ε)) < (n : ℝ) →
        |term n x| < ε := by
  intro l x ε n hl hx hε hε1 hn
  obtain ⟨hnl, hexp⟩ := gap8 l ε n hl hε hε1 hn
  exact gap7 l x ε n hl hx hε hε1 hnl hexp

theorem gap10 :
    ∀ l : ℝ, 0 < l →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N < n →
          ∀ x ∈ Set.Ioo (-l) l, |term n x| < ε := by
  intro l hl ε hε
  let δ : ℝ := min ε (1 / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hε (by norm_num)
  have hδ1 : δ < 1 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right ε (1 / 2)) (by norm_num)
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (l + Real.sqrt (Real.log (1 / δ)))
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hncast : (N : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hthreshold :
      l + Real.sqrt (Real.log (1 / δ)) < (n : ℝ) :=
    lt_trans hN hncast
  have hbound := gap9 l x δ n hl hx hδ hδ1 hthreshold
  exact lt_of_lt_of_le hbound (min_le_left ε (1 / 2))

theorem gap11 :
    ∀ l : ℝ, 0 < l →
      UniformlyConvergesOn term (fun _ => 0) (Set.Ioo (-l) l) := by
  intro l hl
  unfold UniformlyConvergesOn
  intro ε hε
  obtain ⟨N, hN⟩ := gap10 l hl ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa using hN n hn x hx

theorem gap12 :
    ∀ l : ℝ, 0 < l →
      UniformlyConvergesOn term (fun _ => 0) (Set.Ioo (-l) l) := by
  intro l hl
  exact gap11 l hl

end

end ProofGap.Exercise2758_1
