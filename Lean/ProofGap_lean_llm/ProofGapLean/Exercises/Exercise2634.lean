import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2634

noncomputable section

open Filter

def exponent (a b c d : ℝ) (n : ℕ) : ℝ :=
  (a * Real.log n + b) / (c * Real.log n + d)

def u (a b c d : ℝ) (n : ℕ) : ℝ :=
  Real.exp (exponent a b c d n)

def raabe (a b c d : ℝ) (n : ℕ) : ℝ :=
  n * (u a b c d n / u a b c d (n + 1) - 1)

def converges (a b c d : ℝ) : Prop :=
  Summable (fun n : ℕ => u a b c d (n + 1))

private theorem tendsto_log_nat_add (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + (k : ℝ))) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

private theorem tendsto_exponent_of_c_ne_zero (a b c d : ℝ) (hc : c ≠ 0) :
    Tendsto (fun n : ℕ => exponent a b c d (n + 1)) atTop (nhds (a / c)) := by
  have hlog := tendsto_log_nat_add 1
  have hinv : Tendsto (fun n : ℕ => (Real.log ((n : ℝ) + 1))⁻¹) atTop (nhds 0) := by
    simpa using hlog.inv_tendsto_atTop
  have hnorm : Tendsto
      (fun n : ℕ =>
        (a + b * (Real.log (n + 1))⁻¹) /
          (c + d * (Real.log (n + 1))⁻¹))
      atTop (nhds ((a + b * 0) / (c + d * 0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)) (by simpa using hc)
  have hnorm' : Tendsto
      (fun n : ℕ =>
        (a + b * (Real.log (n + 1))⁻¹) /
          (c + d * (Real.log (n + 1))⁻¹))
      atTop (nhds (a / c)) := by simpa using hnorm
  apply hnorm'.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  simp only [exponent, Nat.cast_add, Nat.cast_one]
  let L := Real.log ((n : ℝ) + 1)
  change (a + b * L⁻¹) / (c + d * L⁻¹) = (a * L + b) / (c * L + d)
  have hL : L ≠ 0 := by simpa [L] using hn.ne'
  rw [show a + b * L⁻¹ = (a * L + b) / L by
      field_simp [hL],
    show c + d * L⁻¹ = (c * L + d) / L by
      field_simp [hL]]
  exact div_div_div_cancel_right₀ hL _ _

private theorem tendsto_u_of_c_ne_zero (a b c d : ℝ) (hc : c ≠ 0) :
    Tendsto (fun n : ℕ => u a b c d (n + 1)) atTop
      (nhds (Real.exp (a / c))) := by
  simpa only [u] using
    (Real.continuous_exp.tendsto (a / c)).comp
      (tendsto_exponent_of_c_ne_zero a b c d hc)

private theorem not_converges_of_c_ne_zero (a b c d : ℝ) (hc : c ≠ 0) :
    ¬ converges a b c d := by
  intro h
  have hz := h.tendsto_atTop_zero
  have heq := tendsto_nhds_unique (tendsto_u_of_c_ne_zero a b c d hc) hz
  exact (Real.exp_ne_zero (a / c)) heq

private theorem eventually_den_ne_zero (c d : ℝ) (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, c * Real.log n + d ≠ 0 := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop := by
    simpa using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (-d / c)] with n hn
  intro hzero
  have : Real.log n = -d / c := by
    field_simp [hc]
    linarith
  linarith

private theorem u_c_zero (a b d : ℝ) (n : ℕ) (hd : d ≠ 0) (hn : 1 ≤ n) :
    u a b 0 d n = Real.exp (b / d) * (n : ℝ) ^ (a / d) := by
  rw [u, exponent]
  simp only [zero_mul, zero_add]
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
  rw [← Real.exp_add]
  congr 1
  field_simp [hd]
  ring

private theorem converges_c_zero_iff (a b d : ℝ) :
    converges a b 0 d ↔ d ≠ 0 ∧ a / d < -1 := by
  by_cases hd : d = 0
  · subst d
    simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    intro h
    have hz := h.tendsto_atTop_zero
    have hz' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
      simpa [converges, u, exponent] using hz
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hz')
  · constructor
    · intro hconv
      have hscaled : Summable
          (fun n : ℕ => Real.exp (-b / d) * u a b 0 d (n + 1)) :=
        hconv.mul_left _
      have hpows : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (a / d)) :=
        hscaled.congr (fun n => by
          rw [u_c_zero a b d (n + 1) hd (by omega)]
          rw [← mul_assoc, ← Real.exp_add]
          have : -b / d + b / d = 0 := by ring
          rw [this, Real.exp_zero, one_mul])
      have hpows' : Summable (fun n : ℕ => (n : ℝ) ^ (a / d)) :=
        (summable_nat_add_iff 1).mp (by simpa [Nat.add_comm] using hpows)
      exact ⟨hd, Real.summable_nat_rpow.mp hpows'⟩
    · rintro ⟨_, hp⟩
      have hpows : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (a / d)) := by
        have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
        simpa [Nat.add_comm] using this
      exact (hpows.mul_left (Real.exp (b / d))).congr (fun n =>
        (u_c_zero a b d (n + 1) hd (by omega)).symm)

private theorem converges_iff (a b c d : ℝ) :
    converges a b c d ↔ c = 0 ∧ d ≠ 0 ∧ a / d < -1 := by
  by_cases hc : c = 0
  · subst c
    simpa [and_assoc] using converges_c_zero_iff a b d
  · constructor
    · intro h
      exact (not_converges_of_c_ne_zero a b c d hc h).elim
    · rintro ⟨h, _⟩
      exact (hc h).elim

private theorem exponent_sub_formula (a b c d : ℝ) (r s : ℕ)
    (hr : c * Real.log r + d ≠ 0) (hs : c * Real.log s + d ≠ 0) :
    exponent a b c d r - exponent a b c d s =
      (b * c - a * d) * (Real.log s - Real.log r) /
        ((c * Real.log r + d) * (c * Real.log s + d)) := by
  simp only [exponent]
  rw [div_sub_div _ _ hr hs]
  congr 1
  ring

private theorem tendsto_natSucc_mul_log_diff :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        (Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  have hg : Tendsto (fun n : ℕ => (n : ℝ) * (1 / (n : ℝ))) atTop (nhds 1) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp [Nat.cast_ne_zero.mpr hn]
  have hbase := Real.tendsto_nat_mul_log_one_add_of_tendsto hg
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  apply hshift.congr'
  filter_upwards with n
  simp only [Function.comp_apply]
  congr 1
  symm
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  push_cast
  field_simp
  ring

private theorem tendsto_den_inv (c d : ℝ) (hc : c ≠ 0) (k : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (c * Real.log ((n + k : ℕ) : ℝ) + d)⁻¹)
      atTop (nhds 0) := by
  have hlog : Tendsto
      (fun n : ℕ => Real.log ((n + k : ℕ) : ℝ)) atTop atTop := by
    simpa [Nat.cast_add] using tendsto_log_nat_add k
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact (tendsto_atBot_add_const_right atTop d
      ((tendsto_const_mul_atBot_of_neg hcneg).2 hlog)).inv_tendsto_atBot
  · exact (tendsto_atTop_add_const_right atTop d
      ((tendsto_const_mul_atTop_of_pos hcpos).2 hlog)).inv_tendsto_atTop

private theorem tendsto_exp_sub_one_div :
    Tendsto (fun x : ℝ => (Real.exp x - 1) / x)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  simpa [Real.exp_eq_exp_ℝ, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_exp_zero (𝕂 := ℝ)).tendsto_slope_zero

private theorem tendsto_natSucc_mul_exp_sub_one (δ : ℕ → ℝ) (l : ℝ)
    (hscaled : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * δ n) atTop (nhds l))
    (hzero : Tendsto δ atTop (nhds 0)) (hne : ∀ᶠ n : ℕ in atTop, δ n ≠ 0) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (Real.exp (δ n) - 1))
      atTop (nhds l) := by
  have hwithin : Tendsto δ atTop (nhdsWithin 0 {0}ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hne.mono (fun _ hn => by simpa using hn)⟩
  have hprod := hscaled.mul (tendsto_exp_sub_one_div.comp hwithin)
  have hprod' : Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) * δ n) * ((Real.exp (δ n) - 1) / δ n))
      atTop (nhds l) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [hne] with n hn
  field_simp [hn]

theorem gap1 (a b c d : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hden₀ : c * Real.log n + d ≠ 0)
    (hden₁ : c * Real.log (n + 1) + d ≠ 0) :
    raabe a b c d n =
      n * (Real.exp
        (exponent a b c d n - exponent a b c d (n + 1)) - 1) := by
  rw [raabe, u, u, Real.exp_sub]

theorem gap2 (a b c d : ℝ) (hc : c ≠ 0) (hdet : b * c - a * d ≠ 0) :
    Tendsto (fun n : ℕ => raabe a b c d (n + 1)) atTop (nhds 0) := by
  let δ : ℕ → ℝ := fun n =>
    exponent a b c d (n + 1) - exponent a b c d (n + 2)
  have hden := eventually_den_ne_zero c d hc
  have hden₁ := (tendsto_add_atTop_nat 1).eventually hden
  have hden₂ := (tendsto_add_atTop_nat 2).eventually hden
  have hraw : Tendsto
      (fun n : ℕ =>
        (b * c - a * d) *
          (((n + 1 : ℕ) : ℝ) *
            (Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) *
          (c * Real.log ((n + 1 : ℕ) : ℝ) + d)⁻¹ *
          (c * Real.log ((n + 2 : ℕ) : ℝ) + d)⁻¹)
      atTop (nhds 0) := by
    simpa using (((tendsto_const_nhds.mul tendsto_natSucc_mul_log_diff).mul
      (tendsto_den_inv c d hc 1)).mul (tendsto_den_inv c d hc 2))
  have hscaled : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * δ n) atTop (nhds 0) := by
    apply hraw.congr'
    filter_upwards [hden₁, hden₂] with n hn₁ hn₂
    simp only [δ]
    rw [exponent_sub_formula a b c d (n + 1) (n + 2) hn₁ hn₂]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  have hzero : Tendsto δ atTop (nhds 0) := by
    have hquot := hscaled.div_atTop htop
    apply hquot.congr'
    filter_upwards with n
    simp only [δ]
    field_simp
  have hne : ∀ᶠ n : ℕ in atTop, δ n ≠ 0 := by
    filter_upwards [hden₁, hden₂] with n hn₁ hn₂
    simp only [δ]
    rw [exponent_sub_formula a b c d (n + 1) (n + 2) hn₁ hn₂]
    apply div_ne_zero
    · apply mul_ne_zero hdet
      apply sub_ne_zero.mpr
      apply ne_of_gt
      rw [Real.log_lt_log_iff (by positivity) (by positivity)]
      norm_num
    · exact mul_ne_zero hn₁ hn₂
  have hexp := tendsto_natSucc_mul_exp_sub_one δ 0 hscaled hzero hne
  apply hexp.congr'
  filter_upwards [hden₁, hden₂] with n hn₁ hn₂
  symm
  exact gap1 a b c d (n + 1) (by omega) hn₁
    (by
      have hcast : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      simpa only [hcast] using hn₂)

theorem gap3 (a b c d : ℝ) (hc : c ≠ 0) (hdet : b * c - a * d ≠ 0) :
    ¬ converges a b c d := not_converges_of_c_ne_zero a b c d hc

theorem gap4 (a b c d : ℝ) (hc : c ≠ 0) (hdet : b * c - a * d = 0) :
    ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, u a b c d n = C := by
  have hden := eventually_den_ne_zero c d hc
  rw [eventually_atTop] at hden
  rcases hden with ⟨N, hN⟩
  refine ⟨Real.exp (a / c), Real.exp_pos _, N, ?_⟩
  intro n hn
  rw [u, exponent]
  congr 1
  apply (div_eq_div_iff (hN n hn) hc).2
  nlinarith [hdet]

theorem gap5 (a b c d : ℝ) (hc : c ≠ 0) (hdet : b * c - a * d = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, u a b c d n = C := by
  rcases gap4 a b c d hc hdet with ⟨C, hC, N, hN⟩
  exact ⟨C, hC, N, hN⟩

theorem gap6 (a b c d : ℝ) (hc : c ≠ 0) (hdet : b * c - a * d = 0) :
    ¬ converges a b c d := not_converges_of_c_ne_zero a b c d hc

theorem gap7 (a b d : ℝ) (hd : d ≠ 0) :
    Tendsto (fun n : ℕ => raabe a b 0 d (n + 1))
      atTop (nhds (-a / d)) := by
  by_cases ha : a = 0
  · subst a
    simpa [raabe, u, exponent, hd] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · let δ : ℕ → ℝ := fun n =>
      exponent a b 0 d (n + 1) - exponent a b 0 d (n + 2)
    have hbase : Tendsto
        (fun n : ℕ => -(a / d) *
          (((n + 1 : ℕ) : ℝ) *
            (Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))))
        atTop (nhds (-(a / d))) := by
      simpa using tendsto_const_nhds.mul tendsto_natSucc_mul_log_diff
    have hscaled : Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * δ n)
        atTop (nhds (-(a / d))) := by
      apply hbase.congr'
      filter_upwards with n
      simp only [δ]
      rw [exponent_sub_formula a b 0 d (n + 1) (n + 2)
        (by simpa using hd) (by simpa using hd)]
      field_simp [hd]
      ring
    have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        tendsto_natCast_atTop_atTop.atTop_add
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    have hzero : Tendsto δ atTop (nhds 0) := by
      have hquot := hscaled.div_atTop htop
      apply hquot.congr'
      filter_upwards with n
      simp only [δ]
      field_simp
    have hne : ∀ᶠ n : ℕ in atTop, δ n ≠ 0 := by
      filter_upwards with n
      simp only [δ]
      rw [exponent_sub_formula a b 0 d (n + 1) (n + 2)
        (by simpa using hd) (by simpa using hd)]
      apply div_ne_zero
      · apply mul_ne_zero
        · simpa [hd] using mul_ne_zero ha hd
        · apply sub_ne_zero.mpr
          apply ne_of_gt
          rw [Real.log_lt_log_iff (by positivity) (by positivity)]
          norm_num
      · simpa [hd]
    have hexp := tendsto_natSucc_mul_exp_sub_one δ (-(a / d)) hscaled hzero hne
    have hneg : -a / d = -(a / d) := by ring
    rw [hneg]
    apply hexp.congr'
    filter_upwards with n
    symm
    exact gap1 a b 0 d (n + 1) (by omega) (by simpa using hd)
      (by simpa [Nat.cast_add] using hd)

theorem gap8 (a b d : ℝ) (hd : d ≠ 0) (h : 1 < -a / d) :
    converges a b 0 d := by
  have hneg : -a / d = -(a / d) := by ring
  rw [hneg] at h
  apply (converges_c_zero_iff a b d).2
  constructor
  · exact hd
  · linarith

theorem gap9 (a b d : ℝ) (hd : d ≠ 0) (h : -a / d < 1) :
    ¬ converges a b 0 d := by
  have hneg : -a / d = -(a / d) := by ring
  rw [hneg] at h
  rw [converges_c_zero_iff a b d]
  push_neg
  exact fun _ => by linarith

theorem gap10 (a b d : ℝ) (hd : d ≠ 0) (h : -a / d = 1) :
    ∃ C > 0, ∀ n ≥ 1, u a b 0 d n = C / n := by
  have hneg : -a / d = -(a / d) := by ring
  rw [hneg] at h
  refine ⟨Real.exp (b / d), Real.exp_pos _, ?_⟩
  intro n hn
  rw [u_c_zero a b d n hd hn]
  have hp : a / d = -1 := by linarith
  rw [hp, Real.rpow_neg_one]
  norm_cast

theorem gap11 (a b d : ℝ) (hd : d ≠ 0) (h : -a / d = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ≥ 1, u a b 0 d n = C / n := by
  rcases gap10 a b d hd h with ⟨C, hC, hN⟩
  exact ⟨C, hC, hN⟩

theorem gap12 (a b d : ℝ) (hd : d ≠ 0) (h : -a / d = 1) :
    ¬ converges a b 0 d := by
  have hneg : -a / d = -(a / d) := by ring
  rw [hneg] at h
  rw [converges_c_zero_iff a b d]
  push_neg
  exact fun _ => by linarith

theorem gap13 (a b c d : ℝ) :
    (a, b, c, d) ∈
        {z : ℝ × ℝ × ℝ × ℝ |
          z.2.2.1 = 0 ∧ z.2.2.2 ≠ 0 ∧ z.1 / z.2.2.2 < -1} ↔
      converges a b c d := by
  change (c = 0 ∧ d ≠ 0 ∧ a / d < -1) ↔ converges a b c d
  exact (converges_iff a b c d).symm

end

end ProofGap.Exercise2634
