import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

namespace ProofGap.Exercise2746

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n

def pointwiseLimit (x : ℝ) : ℝ :=
  if x = 1 then 1 else 0

def cutoff (ε : ℝ) : ℕ :=
  Nat.floor (Real.log (1 / ε) / Real.log 2) + 1

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  simpa [term] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hx.1
      (lt_of_le_of_lt hx.2 (by norm_num : (1 / 2 : ℝ) < 1)))

theorem gap2 :
    ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), pointwiseLimit x = 0 := by
  intro x hx
  have hxne : x ≠ 1 := by
    intro h
    rw [h] at hx
    norm_num at hx
  simp [pointwiseLimit, hxne]

theorem gap3 :
    ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (pointwiseLimit x)) := by
  intro x hx
  rw [gap2 x hx]
  exact gap1 x hx

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) (1 / 2) →
      |term n x - pointwiseLimit x| = |x| ^ n := by
  intro n x hx
  simp only [term, gap2 x hx, sub_zero, abs_pow]

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) (1 / 2) →
      |x| ^ n ≤ (1 / 2 : ℝ) ^ n := by
  intro n x hx
  rw [abs_of_nonneg hx.1]
  gcongr
  · exact hx.1
  · exact hx.2

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) (1 / 2) →
      |term n x - pointwiseLimit x| ≤ (1 / 2 : ℝ) ^ n := by
  intro n x hx
  calc
    |term n x - pointwiseLimit x| = |x| ^ n := gap4 n x hx
    _ ≤ (1 / 2 : ℝ) ^ n := gap5 n x hx

theorem gap7 :
    ∀ (n : ℕ) (x ε : ℝ), x ∈ Set.Icc (0 : ℝ) (1 / 2) →
      (1 / 2 : ℝ) ^ n < ε → |term n x - pointwiseLimit x| < ε := by
  intro n x ε hx hn
  exact lt_of_le_of_lt (gap6 n x hx) hn

theorem gap8 :
    ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      Real.log (1 / ε) / Real.log 2 < (n : ℝ) →
        (1 / 2 : ℝ) ^ n < ε := by
  intro n ε hε hratio
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul :
      Real.log (1 / ε) < (n : ℝ) * Real.log 2 :=
    (div_lt_iff₀ hlog2).mp hratio
  have hinv : 0 < (1 / ε : ℝ) := one_div_pos.mpr hε
  have hpowexp :
      Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hexp : (1 / ε : ℝ) < (2 : ℝ) ^ n := by
    have h := Real.exp_lt_exp.mpr hmul
    rw [Real.exp_log hinv, hpowexp] at h
    exact h
  have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  calc
    (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
      rw [div_pow]
      simp
    _ < ε := (div_lt_iff₀ hp).2 (by
      have hcross := (div_lt_iff₀ hε).mp hexp
      simpa [mul_comm] using hcross)

theorem gap9 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < ε →
      x ∈ Set.Icc (0 : ℝ) (1 / 2) →
      Real.log (1 / ε) / Real.log 2 < (n : ℝ) →
        |term n x - pointwiseLimit x| < ε := by
  intro n x ε hε hx hlog
  exact gap7 n x ε hx (gap8 n ε hε hlog)

theorem gap10 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < ε →
      cutoff ε ≤ n → x ∈ Set.Icc (0 : ℝ) (1 / 2) →
        |term n x - 0| < ε := by
  intro n x ε hε hn hx
  have hcut :
      Real.log (1 / ε) / Real.log 2 < (cutoff ε : ℝ) := by
    simpa [cutoff] using
      (Nat.lt_floor_add_one (Real.log (1 / ε) / Real.log 2))
  have hcast : (cutoff ε : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hlog : Real.log (1 / ε) / Real.log 2 < (n : ℝ) :=
    lt_of_lt_of_le hcut hcast
  simpa [gap2 x hx] using gap9 n x ε hε hx hlog

theorem gap11 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro ε hε
  refine ⟨cutoff ε, ?_⟩
  intro n hn x hx
  exact gap10 n x ε hε hn hx

theorem gap12 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (pointwiseLimit x)) := by
  intro x hx
  by_cases h : x = 1
  · subst x
    simp [term, pointwiseLimit]
  · have hlt : x < 1 := lt_of_le_of_ne hx.2 h
    simpa [term, pointwiseLimit, h] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 hlt)

theorem gap13 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 / 2 →
      let x := Real.rpow 2 (-(1 : ℝ) / n)
      |term n x - pointwiseLimit x| = 1 / 2 := by
  intro n ε₀ hn hε₀ hε₀lt
  dsimp only
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn0
  have ha : -(1 : ℝ) / (n : ℝ) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hnpos
  have hxlt : Real.rpow 2 (-(1 : ℝ) / (n : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ha
  have hxpos : 0 < Real.rpow 2 (-(1 : ℝ) / (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcancel :
      (-(1 : ℝ) / (n : ℝ)) * (n : ℝ) = -1 := by
    field_simp [ne_of_gt hnpos]
  have hlog :
      Real.log (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) =
        (-(1 : ℝ) / (n : ℝ)) * Real.log 2 := by
    simpa only using
      (Real.log_rpow (by norm_num : (0 : ℝ) < 2)
        (-(1 : ℝ) / (n : ℝ)))
  have hexponent :
      Real.log (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) * (n : ℝ) =
        -Real.log 2 := by
    rw [hlog]
    calc
      ((-(1 : ℝ) / (n : ℝ)) * Real.log 2) * (n : ℝ) =
          ((-(1 : ℝ) / (n : ℝ)) * (n : ℝ)) * Real.log 2 := by ring
      _ = (-1) * Real.log 2 := by rw [hcancel]
      _ = -Real.log 2 := by ring
  have hpow :
      term n (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) = 1 / 2 := by
    unfold term
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos hxpos]
    rw [hexponent, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hlimit :
      pointwiseLimit (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) = 0 := by
    unfold pointwiseLimit
    split
    · rename_i h
      exact ((ne_of_lt hxlt) h).elim
    · rfl
  calc
    |term n (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) -
        pointwiseLimit (Real.rpow 2 (-(1 : ℝ) / (n : ℝ)))| =
        |term n (Real.rpow 2 (-(1 : ℝ) / (n : ℝ)))| := by
          rw [hlimit, sub_zero]
    _ = |(1 / 2 : ℝ)| := by rw [hpow]
    _ = 1 / 2 := by norm_num

theorem gap14 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 → 1 / 2 > ε₀ := by
  intro ε₀ hpos hlt
  exact hlt

theorem gap15 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 / 2 →
      let x := Real.rpow 2 (-(1 : ℝ) / n)
      |term n x - pointwiseLimit x| > ε₀ := by
  intro n ε₀ hn hpos hlt
  dsimp only
  have h := gap13 n ε₀ hn hpos hlt
  dsimp only at h
  rw [h]
  exact hlt

theorem gap16 :
    ¬ UniformlyConvergesOn term pointwiseLimit (Set.Icc (0 : ℝ) 1) := by
  intro hU
  rcases hU (1 / 4 : ℝ) (by norm_num) with ⟨N, hN⟩
  let n : ℕ := max N 1
  have hnN : N ≤ n := le_max_left N 1
  have hn1 : 1 ≤ n := le_max_right N 1
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn0
  let x : ℝ := Real.rpow 2 (-(1 : ℝ) / (n : ℝ))
  have ha : -(1 : ℝ) / (n : ℝ) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hnpos
  have hxpos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hxlt : x < 1 := by
    dsimp [x]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ha
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hxpos, le_of_lt hxlt⟩
  have hsmall : |term n x - pointwiseLimit x| < (1 / 4 : ℝ) :=
    hN n hnN x hx
  have hlarge := gap15 n (1 / 4 : ℝ) hn1 (by norm_num) (by norm_num)
  dsimp only at hlarge
  change |term n x - pointwiseLimit x| > (1 / 4 : ℝ) at hlarge
  exact (not_lt_of_ge (le_of_lt hlarge)) hsmall

theorem gap17 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) (1 / 2)) ∧
      ¬ UniformlyConvergesOn term pointwiseLimit (Set.Icc (0 : ℝ) 1) := by
  exact ⟨gap11, gap16⟩

end

end ProofGap.Exercise2746
