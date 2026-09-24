import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2762

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow (1 + x ^ n) (1 / (n : ℝ))

def limitFunction (x : ℝ) : ℝ :=
  if x ≤ 1 then 1 else x

def rootDenom (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, term n x ^ (n - 1 - k)

def mixedDenom (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, term n x ^ (n - 1 - k) * x ^ k

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

private theorem term_pow_eq
    (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    term n x ^ n = 1 + x ^ n := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hbase : 0 < 1 + x ^ n := by
    nlinarith [pow_nonneg hx n]
  have ht_exp :
      term n x =
        Real.exp (Real.log (1 + x ^ n) * (1 / (n : ℝ))) := by
    unfold term
    exact Real.rpow_def_of_pos hbase (1 / (n : ℝ))
  rw [ht_exp, ← Real.exp_nat_mul]
  rw [show (n : ℝ) * (Real.log (1 + x ^ n) * (1 / (n : ℝ))) =
      Real.log (1 + x ^ n) by field_simp]
  exact Real.exp_log hbase

theorem gap1 :
    ∀ x ∈ Set.Icc (0 : ℝ) 2,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (limitFunction x)) := by
  intro x hx
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hsmall :
      Tendsto (fun n : ℕ => Real.log 2 * (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv)
  by_cases hle : x ≤ 1
  · have hexp :
        Tendsto
          (fun n : ℕ => Real.log (1 + x ^ n) * (1 / (n : ℝ)))
          atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hsmall
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hxpow0 : 0 ≤ x ^ n := pow_nonneg hx.1 n
        have hlog0 : 0 ≤ Real.log (1 + x ^ n) :=
          Real.log_nonneg (by nlinarith)
        have hinv0 : 0 ≤ 1 / (n : ℝ) := by
          exact le_of_lt (one_div_pos.mpr (by positivity))
        exact mul_nonneg hlog0 hinv0
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hxpow : x ^ n ≤ 1 := pow_le_one₀ hx.1 hle
        have hbasepos : 0 < 1 + x ^ n := by
          nlinarith [pow_nonneg hx.1 n]
        have htwopos : (0 : ℝ) < 2 := by norm_num
        have hbasele : 1 + x ^ n ≤ (2 : ℝ) := by linarith
        have hlog : Real.log (1 + x ^ n) ≤ Real.log 2 :=
          Real.strictMonoOn_log.monotoneOn hbasepos htwopos hbasele
        have hinv0 : 0 ≤ 1 / (n : ℝ) := by
          exact le_of_lt (one_div_pos.mpr (by positivity))
        exact mul_le_mul_of_nonneg_right hlog hinv0
    have hexp' := Real.continuous_exp.continuousAt.tendsto.comp hexp
    simpa [limitFunction, hle] using
      (hexp'.congr' (by
        filter_upwards with n
        have hb : 0 < 1 + x ^ n := by
          nlinarith [pow_nonneg hx.1 n]
        change
          Real.exp (Real.log (1 + x ^ n) * (1 / (n : ℝ))) =
            Real.rpow (1 + x ^ n) (1 / (n : ℝ))
        exact (Real.rpow_def_of_pos hb (1 / (n : ℝ))).symm))
  · have hx1 : 1 < x := lt_of_not_ge hle
    have hxpos : 0 < x := lt_trans zero_lt_one hx1
    have hexp :
        Tendsto
          (fun n : ℕ => Real.log (1 + x ^ n) * (1 / (n : ℝ)))
          atTop (𝓝 (Real.log x)) := by
      have hlower : Tendsto (fun _ : ℕ => Real.log x) atTop (𝓝 (Real.log x)) :=
        tendsto_const_nhds
      have hupper :
          Tendsto
            (fun n : ℕ => Real.log x + Real.log 2 * (1 / (n : ℝ)))
            atTop (𝓝 (Real.log x)) := by
        simpa using (tendsto_const_nhds.add hsmall)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        have hxpowpos : 0 < x ^ n := pow_pos hxpos n
        have hsumpos : 0 < 1 + x ^ n := by linarith
        have hxpowle : x ^ n ≤ 1 + x ^ n := by linarith
        have hlog : Real.log (x ^ n) ≤ Real.log (1 + x ^ n) :=
          Real.strictMonoOn_log.monotoneOn hxpowpos hsumpos hxpowle
        have hinv0 : 0 ≤ 1 / (n : ℝ) := by
          exact le_of_lt (one_div_pos.mpr (by positivity))
        calc
          Real.log x = Real.log (x ^ n) * (1 / (n : ℝ)) := by
            rw [Real.log_pow]
            field_simp
          _ ≤ Real.log (1 + x ^ n) * (1 / (n : ℝ)) :=
            mul_le_mul_of_nonneg_right hlog hinv0
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        have hxpowpos : 0 < x ^ n := pow_pos hxpos n
        have hxpow1 : 1 ≤ x ^ n := one_le_pow₀ hx1.le
        have hxpow_ne : x ^ n ≠ 0 := ne_of_gt hxpowpos
        have hsumpos : 0 < 1 + x ^ n := by linarith
        have htwopowpos : 0 < (2 : ℝ) * x ^ n :=
          mul_pos (by norm_num) hxpowpos
        have hsumle : 1 + x ^ n ≤ (2 : ℝ) * x ^ n := by
          nlinarith
        have hlog : Real.log (1 + x ^ n) ≤ Real.log (2 * x ^ n) :=
          Real.strictMonoOn_log.monotoneOn hsumpos htwopowpos hsumle
        have hinv0 : 0 ≤ 1 / (n : ℝ) := by
          exact le_of_lt (one_div_pos.mpr (by positivity))
        calc
          Real.log (1 + x ^ n) * (1 / (n : ℝ))
              ≤ Real.log (2 * x ^ n) * (1 / (n : ℝ)) :=
                mul_le_mul_of_nonneg_right hlog hinv0
          _ = Real.log x + Real.log 2 * (1 / (n : ℝ)) := by
            rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpow_ne, Real.log_pow]
            field_simp
            ring
    have hexp' := Real.continuous_exp.continuousAt.tendsto.comp hexp
    simpa [limitFunction, hle, Real.exp_log hxpos] using
      (hexp'.congr' (by
        filter_upwards with n
        have hb : 0 < 1 + x ^ n := by
          nlinarith [pow_nonneg hx.1 n]
        change
          Real.exp (Real.log (1 + x ^ n) * (1 / (n : ℝ))) =
            Real.rpow (1 + x ^ n) (1 / (n : ℝ))
        exact (Real.rpow_def_of_pos hb (1 / (n : ℝ))).symm))

theorem gap2 :
    ∀ x ∈ Set.Icc (0 : ℝ) 2,
      Tendsto (fun n : ℕ => term n x) atTop
        (𝓝 (if x ≤ 1 then 1 else x)) := by
  intro x hx
  simpa [limitFunction] using gap1 x hx

theorem gap3 :
    ∀ x ∈ Set.Icc (0 : ℝ) 2,
      limitFunction x = if x ≤ 1 then 1 else x := by
  intro x hx
  rfl

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      |term n x - limitFunction x| = |term n x - 1| := by
  intro n x hx
  simp [limitFunction, hx.2]

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → x ∈ Set.Icc (0 : ℝ) 1 →
      |term n x - 1| = x ^ n / rootDenom n x := by
  intro n x hn hx
  have hnpos : 0 < (n : ℝ) := by positivity
  have hbase : 0 < 1 + x ^ n := by
    nlinarith [pow_nonneg hx.1 n]
  have hexpnonneg : 0 ≤ 1 / (n : ℝ) :=
    le_of_lt (one_div_pos.mpr hnpos)
  have ht : 1 ≤ term n x := by
    unfold term
    exact Real.one_le_rpow (by nlinarith [pow_nonneg hx.1 n]) hexpnonneg
  have htpow : term n x ^ n = 1 + x ^ n :=
    term_pow_eq n x hn hx.1
  have hroot : rootDenom n x = ∑ k ∈ Finset.range n, term n x ^ k := by
    unfold rootDenom
    rw [Finset.sum_range_reflect]
  have hden : (n : ℝ) ≤ rootDenom n x := by
    rw [hroot]
    calc
      (n : ℝ) = ∑ k ∈ Finset.range n, (1 : ℝ) := by simp
      _ ≤ ∑ k ∈ Finset.range n, term n x ^ k := by
        exact Finset.sum_le_sum (fun k hk => one_le_pow₀ ht)
  have hdenpos : 0 < rootDenom n x := lt_of_lt_of_le hnpos hden
  have hgeom :
      rootDenom n x * (term n x - 1) = x ^ n := by
    rw [hroot]
    calc
      (∑ k ∈ Finset.range n, term n x ^ k) * (term n x - 1)
          = term n x ^ n - 1 := geom_sum_mul (term n x) n
      _ = x ^ n := by rw [htpow]; ring
  rw [abs_of_nonneg (sub_nonneg.mpr ht)]
  apply (eq_div_iff (ne_of_gt hdenpos)).2
  simpa [mul_comm] using hgeom

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), 2 ≤ n → x ∈ Set.Icc (0 : ℝ) 1 →
      x ^ n / rootDenom n x < 1 / (n : ℝ) := by
  intro n x hn hx
  have ht : 1 ≤ term n x := by
    unfold term
    exact Real.one_le_rpow (by nlinarith [pow_nonneg hx.1 n]) (by positivity)
  have hroot : rootDenom n x = ∑ k ∈ Finset.range n, term n x ^ k := by
    unfold rootDenom
    rw [Finset.sum_range_reflect]
  have hden : (n : ℝ) ≤ rootDenom n x := by
    rw [hroot]
    calc
      (n : ℝ) = ∑ k ∈ Finset.range n, (1 : ℝ) := by simp
      _ ≤ ∑ k ∈ Finset.range n, term n x ^ k := by
        exact Finset.sum_le_sum (fun k hk => one_le_pow₀ ht)
  have hnpos : 0 < (n : ℝ) := by positivity
  have hdenpos : 0 < rootDenom n x := lt_of_lt_of_le hnpos hden
  rw [div_lt_div_iff₀ hdenpos hnpos]
  rcases lt_or_eq_of_le hx.2 with hxl | rfl
  · have hxpow : x ^ n < 1 := pow_lt_one₀ hx.1 hxl (by omega)
    nlinarith
  · have htstrict : 1 < term n 1 := by
      unfold term
      apply Real.one_lt_rpow
      · norm_num
      · positivity
    have hstrict : (n : ℝ) < rootDenom n 1 := by
      rw [hroot]
      have hs :
          (∑ k ∈ Finset.range n, (1 : ℝ)) <
            ∑ k ∈ Finset.range n, term n 1 ^ k := by
        apply Finset.sum_lt_sum
        · intro k hk
          exact one_le_pow₀ ht
        · refine ⟨1, ?_, ?_⟩
          · simp
            omega
          · simpa using htstrict
      simpa using hs
    norm_num
    nlinarith

theorem gap7 :
    ∀ (n : ℕ) (x : ℝ), 2 ≤ n → x ∈ Set.Icc (0 : ℝ) 1 →
      |term n x - limitFunction x| < 1 / (n : ℝ) := by
  intro n x hn hx
  rw [gap4 n x hx, gap5 n x (by omega) hx]
  exact gap6 n x hn hx

theorem gap8 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Ioc (1 : ℝ) 2 →
      |term n x - limitFunction x| = |term n x - x| := by
  intro n x hx
  have hnot : ¬x ≤ 1 := not_le_of_gt hx.1
  simp [limitFunction, hnot]

theorem gap9 :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → x ∈ Set.Ioc (1 : ℝ) 2 →
      |term n x - x| = 1 / mixedDenom n x := by
  intro n x hn hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx.1
  have hxpowpos : 0 < x ^ n := pow_pos hxpos n
  have hbase : 0 < 1 + x ^ n := by linarith
  have htpos : 0 < term n x := by
    unfold term
    exact Real.rpow_pos_of_pos hbase _
  have htpow : term n x ^ n = 1 + x ^ n :=
    term_pow_eq n x hn hxpos.le
  have hxt : x < term n x := by
    by_contra h
    have hp : term n x ^ n ≤ x ^ n :=
      pow_le_pow_left₀ htpos.le (le_of_not_gt h) n
    nlinarith
  have hg : mixedDenom n x * (x - term n x) = -1 := by
    unfold mixedDenom
    calc
      (∑ k ∈ Finset.range n, term n x ^ (n - 1 - k) * x ^ k) *
          (x - term n x)
          = x ^ n - term n x ^ n := by
              simpa [mul_comm] using (geom_sum₂_mul x (term n x) n)
      _ = -1 := by rw [htpow]; ring
  have hgeom : mixedDenom n x * (term n x - x) = 1 := by
    calc
      mixedDenom n x * (term n x - x) =
          -(mixedDenom n x * (x - term n x)) := by ring
      _ = 1 := by rw [hg]; norm_num
  have hdenpos : 0 < mixedDenom n x := by
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hxt.le)]
  apply (eq_div_iff (ne_of_gt hdenpos)).2
  simpa [mul_comm] using hgeom

theorem gap10 :
    ∀ (n : ℕ) (x : ℝ), 2 ≤ n → x ∈ Set.Ioc (1 : ℝ) 2 →
      1 / mixedDenom n x < 1 / ((n : ℝ) * x ^ (n - 1)) := by
  intro n x hn hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx.1
  have hbase : 0 < 1 + x ^ n := by positivity
  have htpos : 0 < term n x := by
    unfold term
    exact Real.rpow_pos_of_pos hbase _
  have htpow : term n x ^ n = 1 + x ^ n :=
    term_pow_eq n x (by omega) hxpos.le
  have hxt : x < term n x := by
    by_contra h
    have hp : term n x ^ n ≤ x ^ n :=
      pow_le_pow_left₀ htpos.le (le_of_not_gt h) n
    nlinarith
  have hleterm :
      ∀ k ∈ Finset.range n,
        x ^ (n - 1) ≤ term n x ^ (n - 1 - k) * x ^ k := by
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hp : x ^ (n - 1 - k) ≤ term n x ^ (n - 1 - k) :=
      pow_le_pow_left₀ hxpos.le hxt.le (n - 1 - k)
    calc
      x ^ (n - 1) = x ^ (n - 1 - k) * x ^ k := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ term n x ^ (n - 1 - k) * x ^ k :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg hxpos.le k)
  have hstrict0 :
      x ^ (n - 1) < term n x ^ (n - 1 - 0) * x ^ 0 := by
    have hexp : n - 1 ≠ 0 := by omega
    have hp : x ^ (n - 1) < term n x ^ (n - 1) :=
      pow_lt_pow_left₀ hxt hxpos.le hexp
    simpa using hp
  have hsum :
      (∑ k ∈ Finset.range n, x ^ (n - 1)) < mixedDenom n x := by
    unfold mixedDenom
    apply Finset.sum_lt_sum
    · exact hleterm
    · refine ⟨0, by simp [show 0 < n by omega], ?_⟩
      exact hstrict0
  have hden : (n : ℝ) * x ^ (n - 1) < mixedDenom n x := by
    simpa using hsum
  have hpowpos : 0 < x ^ (n - 1) := pow_pos hxpos _
  have hcpos : 0 < (n : ℝ) * x ^ (n - 1) :=
    mul_pos (by positivity) hpowpos
  have hdpos : 0 < mixedDenom n x := lt_trans hcpos hden
  apply (div_lt_div_iff₀ hdpos hcpos).2
  simpa using hden

theorem gap11 :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → x ∈ Set.Ioc (1 : ℝ) 2 →
      1 / ((n : ℝ) * x ^ (n - 1)) ≤ 1 / (n : ℝ) := by
  intro n x hn hx
  have hnpos : 0 < (n : ℝ) := by positivity
  have hpow : 1 ≤ x ^ (n - 1) := one_le_pow₀ hx.1.le
  have hprod : (n : ℝ) ≤ (n : ℝ) * x ^ (n - 1) := by
    nlinarith
  have hprodpos : 0 < (n : ℝ) * x ^ (n - 1) := by
    exact mul_pos hnpos (pow_pos (lt_trans zero_lt_one hx.1) _)
  apply (div_le_div_iff₀ hprodpos hnpos).2
  simpa using hprod

theorem gap12 :
    ∀ (n : ℕ) (x : ℝ), 2 ≤ n → x ∈ Set.Ioc (1 : ℝ) 2 →
      |term n x - limitFunction x| < 1 / (n : ℝ) := by
  intro n x hn hx
  rw [gap8 n x hx, gap9 n x (by omega) hx]
  exact lt_of_lt_of_le (gap10 n x hn hx) (gap11 n x (by omega) hx)

theorem gap13 :
    ∀ (n : ℕ) (x : ℝ), 2 ≤ n → x ∈ Set.Icc (0 : ℝ) 2 →
      |term n x - limitFunction x| < 1 / (n : ℝ) := by
  intro n x hn hx
  by_cases h : x ≤ 1
  · exact gap7 n x hn ⟨hx.1, h⟩
  · exact gap12 n x hn ⟨lt_of_not_ge h, hx.2⟩

theorem gap14 :
    ∀ (n : ℕ) (x ε : ℝ), x ∈ Set.Icc (0 : ℝ) 2 → 0 < ε →
      1 / ε < (n : ℝ) → |term n x - limitFunction x| < ε := by
  intro n x ε hx hε hbound
  by_cases hn : 2 ≤ n
  · have hmain := gap13 n x hn hx
    have hnpos : 0 < (n : ℝ) := by positivity
    have hrecip : 1 / (n : ℝ) < ε := by
      rw [div_lt_iff₀ hnpos]
      have hb := (div_lt_iff₀ hε).mp hbound
      nlinarith
    exact lt_trans hmain hrecip
  · have hnle : n ≤ 1 := by omega
    cases n with
    | zero =>
        have hpos : 0 < 1 / ε := one_div_pos.mpr hε
        norm_num at hbound
        linarith
    | succ m =>
        have hm : m = 0 := by omega
        subst m
        have hε1 : 1 < ε := by
          have hb := (div_lt_iff₀ hε).mp hbound
          norm_num at hb ⊢
          exact hb
        by_cases hxl : x ≤ 1
        · have hxε : x < ε := lt_of_le_of_lt hxl hε1
          simpa [term, limitFunction, hxl, abs_of_nonneg hx.1] using hxε
        · have hxgt : 1 < x := lt_of_not_ge hxl
          simpa [term, limitFunction, hxl] using hε1

theorem gap15 :
    ∀ (n : ℕ) (x ε : ℝ), x ∈ Set.Icc (0 : ℝ) 2 → 0 < ε →
      1 / ε < (n : ℝ) → |term n x - limitFunction x| < ε := by
  exact gap14

theorem gap16 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Icc (0 : ℝ) 2, |term n x - limitFunction x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hNn x hx
  apply gap15 n x ε hx hε
  have hcast : (N : ℝ) < (n : ℝ) := by exact_mod_cast hNn
  exact lt_trans hN hcast

theorem gap17 :
    UniformlyConvergesOn term limitFunction (Set.Icc (0 : ℝ) 2) := by
  unfold UniformlyConvergesOn
  exact gap16

theorem gap18 :
    UniformlyConvergesOn term limitFunction (Set.Icc (0 : ℝ) 2) := by
  exact gap17

end

end ProofGap.Exercise2762
