import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2743

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n

def cutoff (ε x : ℝ) : ℤ :=
  Int.floor (Real.log ε / Real.log x)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x : ℝ, 0 < x → x < 1 →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx hx1
  simpa [term] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hx) hx1)

theorem gap2 :
    ∀ x : ℝ, 0 < x → x < 1 →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N < n → |term n x| < ε := by
  intro x hx hx1 ε hε
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 (gap1 x hx hx1)) ε hε
  refine ⟨N, ?_⟩
  intro n hn
  simpa [Real.dist_eq] using hN n (Nat.le_of_lt hn)

theorem gap3 :
    ∀ (x ε : ℝ) (n : ℕ), 0 < x → x < 1 → 0 < ε →
      (term n x < ε ↔ |term n x| < ε) := by
  intro x ε n hx _ _
  have hp : 0 < term n x := by
    simpa [term] using pow_pos hx n
  rw [abs_of_pos hp]

theorem gap4 :
    ∀ (x ε : ℝ) (n : ℕ),
      0 < x → x < 1 → 0 < ε → ε < 1 →
        (term n x < ε ↔ Real.log ε / Real.log x < (n : ℝ)) := by
  intro x ε n hx hx1 hε _
  have hp : 0 < term n x := by
    simpa [term] using pow_pos hx n
  have hlogx : Real.log x < 0 := Real.log_neg hx hx1
  have hlogpow :
      Real.log (term n x) = (n : ℝ) * Real.log x := by
    simp [term, Real.log_pow]
  constructor
  · intro h
    have hl := Real.strictMonoOn_log hp hε h
    rw [hlogpow] at hl
    exact (div_lt_iff_of_neg hlogx).2 hl
  · intro h
    have hl : (n : ℝ) * Real.log x < Real.log ε :=
      (div_lt_iff_of_neg hlogx).1 h
    have hl' : Real.log (term n x) < Real.log ε := by
      rw [hlogpow]
      exact hl
    have he := Real.exp_lt_exp.mpr hl'
    rw [Real.exp_log hp, Real.exp_log hε] at he
    exact he

theorem gap5 :
    ∀ (x ε : ℝ), 0 < x → x < 1 → 0 < ε → ε < 1 →
      cutoff ε x = Int.floor (Real.log ε / Real.log x) := by
  intro x ε _ _ _ _
  rfl

theorem gap6 :
    cutoff (1 / 1000 : ℝ) (1 / 10 : ℝ) = 3 := by
  have heq : (1 / 1000 : ℝ) = (1 / 10 : ℝ) ^ 3 := by
    norm_num
  have hneg : Real.log (1 / 10 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hne : Real.log (1 / 10 : ℝ) ≠ 0 := ne_of_lt hneg
  have hratio :
      Real.log (1 / 1000 : ℝ) / Real.log (1 / 10 : ℝ) = 3 := by
    rw [heq, Real.log_pow]
    field_simp [hne]
    norm_num
  rw [cutoff, hratio]
  norm_num

theorem gap7 :
    cutoff (1 / 1000 : ℝ) (1 / Real.sqrt 10) = 6 := by
  have hs2 : (Real.sqrt (10 : ℝ)) ^ 2 = 10 :=
    Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt (10 : ℝ) := Real.sqrt_nonneg _
  have hspos : 0 < Real.sqrt (10 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsgt : 1 < Real.sqrt (10 : ℝ) := by
    nlinarith [hs2]
  have hxpos : 0 < (1 / Real.sqrt 10 : ℝ) := one_div_pos.mpr hspos
  have hxlt : (1 / Real.sqrt 10 : ℝ) < 1 :=
    (div_lt_one hspos).2 hsgt
  have hs6 : (Real.sqrt (10 : ℝ)) ^ 6 = 1000 := by
    calc
      (Real.sqrt (10 : ℝ)) ^ 6 = ((Real.sqrt (10 : ℝ)) ^ 2) ^ 3 := by ring
      _ = (10 : ℝ) ^ 3 := by rw [hs2]
      _ = 1000 := by norm_num
  have heq :
      (1 / 1000 : ℝ) = (1 / Real.sqrt 10 : ℝ) ^ 6 := by
    symm
    rw [div_pow, hs6]
    norm_num
  have hneg : Real.log (1 / Real.sqrt 10 : ℝ) < 0 :=
    Real.log_neg hxpos hxlt
  have hne : Real.log (1 / Real.sqrt 10 : ℝ) ≠ 0 := ne_of_lt hneg
  have hratio :
      Real.log (1 / 1000 : ℝ) / Real.log (1 / Real.sqrt 10 : ℝ) = 6 := by
    rw [heq, Real.log_pow]
    field_simp [hne]
    norm_num
  rw [cutoff, hratio]
  norm_num

theorem gap8 :
    ∀ m : ℕ, 0 < m →
      cutoff (1 / 1000 : ℝ) (Real.rpow 10 (-(1 : ℝ) / m)) =
        (3 * m : ℕ) := by
  intro m hm
  have hm0 : (m : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hlog : Real.log (10 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hnum :
      Real.log (1 / 1000 : ℝ) = -(3 : ℝ) * Real.log 10 := by
    rw [show (1 / 1000 : ℝ) = 1 / (10 : ℝ) ^ 3 by norm_num]
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one,
      Real.log_pow]
    ring
  have hden :
      Real.log (Real.rpow 10 (-(1 : ℝ) / m)) =
        (-(1 : ℝ) / (m : ℝ)) * Real.log 10 := by
    change
      Real.log ((10 : ℝ) ^ (-(1 : ℝ) / (m : ℝ))) =
        (-(1 : ℝ) / (m : ℝ)) * Real.log 10
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 10)]
  have hratio :
      Real.log (1 / 1000 : ℝ) /
          Real.log (Real.rpow 10 (-(1 : ℝ) / m)) =
        (3 * m : ℝ) := by
    rw [hnum, hden]
    field_simp [hm0, hlog]
    <;> ring
  have hcast :
      (3 : ℝ) * (m : ℝ) = ((3 * m : ℕ) : ℝ) := by
    norm_num
  rw [cutoff, hratio]
  calc
    Int.floor ((3 : ℝ) * (m : ℝ)) =
        Int.floor (((3 * m : ℕ) : ℝ)) := congrArg Int.floor hcast
    _ = ((3 * m : ℕ) : ℤ) := Int.floor_natCast _

theorem gap9 :
    Tendsto
      (fun x : ℝ => Real.log (1 / 1000 : ℝ) / Real.log x)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) atTop := by
  have hc : Real.log (1 / 1000 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  refine tendsto_atTop.2 ?_
  intro b
  by_cases hb0 : b ≤ 0
  · have hposEv :
        ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1), 0 < x :=
      Filter.Eventually.filter_mono inf_le_left
        (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    refine (hposEv.and self_mem_nhdsWithin).mono ?_
    rintro x ⟨hxpos, hxlt⟩
    have hlogx : Real.log x < 0 := Real.log_neg hxpos hxlt
    have hqpos :
        0 < Real.log (1 / 1000 : ℝ) / Real.log x :=
      div_pos_of_neg_of_neg hc hlogx
    exact hb0.trans (le_of_lt hqpos)
  · have hb : 0 < b := lt_of_not_ge hb0
    have hargneg : Real.log (1 / 1000 : ℝ) / b < 0 :=
      div_neg_of_neg_of_pos hc hb
    have ha :
        Real.exp (Real.log (1 / 1000 : ℝ) / b) < 1 := by
      have he := Real.exp_lt_exp.mpr hargneg
      simpa using he
    have hboundEv :
        ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
          Real.exp (Real.log (1 / 1000 : ℝ) / b) < x :=
      Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds ha)
    refine (hboundEv.and self_mem_nhdsWithin).mono ?_
    rintro x ⟨hax, hxlt⟩
    have hxpos : 0 < x := (Real.exp_pos _).trans hax
    have hlogx : Real.log x < 0 := Real.log_neg hxpos hxlt
    have hloglower :
        Real.log (1 / 1000 : ℝ) / b < Real.log x := by
      apply Real.exp_lt_exp.mp
      simpa [Real.exp_log hxpos] using hax
    have hcprod :
        Real.log (1 / 1000 : ℝ) < b * Real.log x := by
      have h := (div_lt_iff₀ hb).1 hloglower
      simpa [mul_comm] using h
    exact (le_div_iff_of_neg hlogx).2 (le_of_lt hcprod)

theorem gap10 :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, term n x < (1 / 1000 : ℝ) := by
  rintro ⟨N, hN⟩
  let k : ℕ := N + 1
  have hkpos : 0 < k := by simp [k]
  have hkRpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkpos
  have hkR0 : (k : ℝ) ≠ 0 := ne_of_gt hkRpos
  have hε : (0 : ℝ) < 1 / 1000 := by norm_num
  have hc : Real.log (1 / 1000 : ℝ) < 0 :=
    Real.log_neg hε (by norm_num)
  let x : ℝ := Real.exp (Real.log (1 / 1000 : ℝ) / (k : ℝ))
  have hxpos : 0 < x := by
    simp [x, Real.exp_pos]
  have hxlt : x < 1 := by
    have harg : Real.log (1 / 1000 : ℝ) / (k : ℝ) < 0 :=
      div_neg_of_neg_of_pos hc hkRpos
    have he := Real.exp_lt_exp.mpr harg
    simpa [x] using he
  have hpow : term k x = (1 / 1000 : ℝ) := by
    change
      (Real.exp (Real.log (1 / 1000 : ℝ) / (k : ℝ))) ^ k =
        (1 / 1000 : ℝ)
    rw [← Real.exp_nat_mul]
    have harg :
        (k : ℝ) * (Real.log (1 / 1000 : ℝ) / (k : ℝ)) =
          Real.log (1 / 1000 : ℝ) := by
      field_simp [hkR0]
    rw [harg, Real.exp_log hε]
  have hbad := hN k (by simp [k]) x ⟨hxpos, hxlt⟩
  rw [hpow] at hbad
  exact (lt_irrefl _ hbad)

theorem gap11 :
    ¬ UniformlyConvergesOn
        (fun n x => term n x) (fun _ => 0) (Set.Ioo (0 : ℝ) 1) := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 1000 : ℝ) (by norm_num)
  apply gap10
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hp : 0 < term n x := by
    simpa [term] using pow_pos hx.1 n
  have hbound := hN n hn x hx
  simpa [abs_of_pos hp] using hbound

end

end ProofGap.Exercise2743
