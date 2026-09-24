import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise998

open Filter

noncomputable section

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

noncomputable def f (x : ℝ) : ℝ := by
  classical
  exact if IsRational x then x ^ 2 else 0

noncomputable def zeroSlope (h : ℝ) : ℝ := by
  classical
  exact if IsRational h then h else 0

def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (g (a + h) - g a) / h

private theorem tendsto_recip_nat_add_one :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have hb := hnat.eventually (eventually_ge_atTop (b - 1))
    filter_upwards [hb] with n hn
    linarith
  simpa [one_div] using (tendsto_inv_atTop_zero.comp hden)

private theorem tendsto_pos_div_zero_right
    (c : ℝ) (hc : 0 < c) (w : ℕ → ℝ)
    (hwpos : ∀ n, 0 < w n) (hw : Tendsto w atTop (nhds 0)) :
    Tendsto (fun n => c / w n) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  let ε : ℝ := c / (|b| + 1)
  have habs : 0 < |b| + 1 := by positivity
  have hε : 0 < ε := div_pos hc habs
  have hevent : ∀ᶠ n in atTop, w n < ε :=
    hw.eventually (Iio_mem_nhds hε)
  filter_upwards [hevent] with n hn
  have hmul := mul_lt_mul_of_pos_left hn habs
  have hcancel : (|b| + 1) * ε = c := by
    dsimp [ε]
    field_simp
  rw [hcancel] at hmul
  have hquot : |b| + 1 < c / w n :=
    (lt_div_iff₀ (hwpos n)).2 hmul
  nlinarith [le_abs_self b]

theorem gap1 (h : ℝ) (hh : h ≠ 0) :
    dq f 0 h = zeroSlope h := by
  classical
  have hzero : IsRational (0 : ℝ) :=
    ⟨(0 : ℚ), by norm_num⟩
  by_cases hq : IsRational h
  · simp [dq, f, zeroSlope, hzero, hq, hh, pow_two]
  · simp [dq, f, zeroSlope, hzero, hq]

theorem gap2 :
    Tendsto (dq f 0) (nhds 0) (nhds 0) := by
  have hz : Tendsto zeroSlope (nhds 0) (nhds 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with h hh
    have hh' : |h| < ε := by
      simpa [Real.dist_eq] using hh
    by_cases hq : IsRational h
    · simpa [zeroSlope, hq, Real.dist_eq] using hh'
    · simpa [zeroSlope, hq, Real.dist_eq] using hε
  have heq : dq f 0 = zeroSlope := by
    funext h
    by_cases hh : h = 0
    · subst h
      simp [dq, f, zeroSlope, IsRational]
    · exact gap1 h hh
  rw [heq]
  exact hz

theorem gap3 :
    HasDerivAt f 0 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hdq :
      Tendsto (dq f 0) (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) :=
    gap2.mono_left
      (show nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds 0 from inf_le_left)
  have hslope : slope f 0 = dq f 0 := by
    funext h
    unfold slope dq
    simp [div_eq_mul_inv, mul_comm]
  rw [hslope]
  exact hdq

theorem gap4 :
    DifferentiableAt ℝ f 0 := by
  exact gap3.differentiableAt

theorem gap5 (x : ℝ) (hx0 : x ≠ 0) (hxq : IsRational x) :
    ∃ u : ℕ → ℝ,
      (∀ n, ¬ IsRational (u n) ∧ u n < x) ∧
      Tendsto u atTop (nhds x) := by
  let u : ℕ → ℝ := fun n => x - Real.sqrt 2 / ((n : ℝ) + 1)
  refine ⟨u, ?_, ?_⟩
  · intro n
    constructor
    · intro hun
      apply irrational_sqrt_two
      rcases hxq with ⟨qx, hqx⟩
      rcases hun with ⟨qu, hqu⟩
      refine ⟨(qx - qu) * ((n : ℚ) + 1), ?_⟩
      norm_num
      rw [hqx, hqu]
      dsimp [u]
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn] <;> ring_nf
    · dsimp [u]
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hden : 0 < (n : ℝ) + 1 := by positivity
      have hdiv : 0 < Real.sqrt 2 / ((n : ℝ) + 1) := div_pos hsqrt hden
      linarith
  · have hfrac : Tendsto (fun n : ℕ => Real.sqrt 2 / ((n : ℝ) + 1)) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul tendsto_recip_nat_add_one)
    simpa [u] using (tendsto_const_nhds.sub hfrac)

theorem gap6 (x : ℝ) (hx0 : x ≠ 0) (hxq : IsRational x)
    (u : ℕ → ℝ) (hu : ∀ n, ¬ IsRational (u n)) :
    (fun n => (f (u n) - f x) / (u n - x)) =
      fun n => (0 - x ^ 2) / (u n - x) := by
  funext n
  simp [f, hu n, hxq]

theorem gap7 (x : ℝ) (hx0 : x ≠ 0) (u : ℕ → ℝ)
    (hbelow : ∀ n, u n < x) (hu : Tendsto u atTop (nhds x)) :
    Tendsto (fun n => (0 - x ^ 2) / (u n - x)) atTop atTop := by
  have hxlim : Tendsto (fun _ : ℕ => x) atTop (nhds x) :=
    tendsto_const_nhds
  have hw : Tendsto (fun n => x - u n) atTop (nhds 0) := by
    simpa only [sub_self] using hxlim.sub hu
  have hpos : ∀ n, 0 < x - u n := fun n => sub_pos.2 (hbelow n)
  have ht : Tendsto (fun n => x ^ 2 / (x - u n)) atTop atTop :=
    tendsto_pos_div_zero_right (x ^ 2) (sq_pos_of_ne_zero hx0) _ hpos hw
  have heq :
      (fun n => (0 - x ^ 2) / (u n - x)) =
        fun n => x ^ 2 / (x - u n) := by
    funext n
    rw [show u n - x = -(x - u n) by ring]
    have hne : x - u n ≠ 0 := ne_of_gt (hpos n)
    field_simp [hne] <;> ring
  rw [heq]
  exact ht

theorem gap8 (x : ℝ) (hx0 : x ≠ 0) (hxq : IsRational x)
    (u : ℕ → ℝ) (hirr : ∀ n, ¬ IsRational (u n))
    (hbelow : ∀ n, u n < x) (hu : Tendsto u atTop (nhds x)) :
    Tendsto (fun n => (f (u n) - f x) / (u n - x)) atTop atTop := by
  rw [gap6 x hx0 hxq u hirr]
  exact gap7 x hx0 u hbelow hu

theorem gap9 (x : ℝ) (hx0 : x ≠ 0) (hxq : IsRational x) :
    ¬ DifferentiableAt ℝ f x := by
  intro hd
  obtain ⟨u, huall, hu⟩ := gap5 x hx0 hxq
  have hlim := hd.continuousAt.tendsto.comp hu
  have hfu : (f ∘ u) = (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    simp [Function.comp_apply, f, (huall n).1]
  have hfx : f x = x ^ 2 := by
    simp [f, hxq]
  rw [hfu, hfx] at hlim
  have hsquare : x ^ 2 = 0 :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  nlinarith [sq_pos_of_ne_zero hx0]

theorem gap10 (x : ℝ) (hx0 : x ≠ 0) (hxq : ¬ IsRational x) :
    ∃ v : ℕ → ℝ,
      (∀ n, IsRational (v n) ∧ x < v n) ∧
      Tendsto v atTop (nhds x) := by
  classical
  have hinterval : ∀ n : ℕ, x < x + 1 / ((n : ℝ) + 1) := by
    intro n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hfrac : 0 < (1 : ℝ) / ((n : ℝ) + 1) :=
      div_pos (by norm_num) hden
    linarith
  choose q hlo hhi using fun n => exists_rat_btwn (hinterval n)
  let v : ℕ → ℝ := fun n => (q n : ℝ)
  refine ⟨v, ?_, ?_⟩
  · intro n
    constructor
    · exact ⟨q n, rfl⟩
    · exact hlo n
  · have huplim :
        Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (nhds x) := by
      simpa using (tendsto_const_nhds.add tendsto_recip_nat_add_one)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds huplim
      (Filter.Eventually.of_forall fun n => le_of_lt (hlo n))
      (Filter.Eventually.of_forall fun n => le_of_lt (hhi n))

theorem gap11 (x : ℝ) (hx0 : x ≠ 0) (hxq : ¬ IsRational x)
    (v : ℕ → ℝ) (hv : ∀ n, IsRational (v n)) :
    (fun n => (f (v n) - f x) / (v n - x)) =
      fun n => v n ^ 2 / (v n - x) := by
  funext n
  simp [f, hv n, hxq]

theorem gap12 (x : ℝ) (hx0 : x ≠ 0) (v : ℕ → ℝ)
    (habove : ∀ n, x < v n) (hv : Tendsto v atTop (nhds x)) :
    Tendsto (fun n => v n ^ 2 / (v n - x)) atTop atTop := by
  have hxlim : Tendsto (fun _ : ℕ => x) atTop (nhds x) :=
    tendsto_const_nhds
  have hw : Tendsto (fun n => v n - x) atTop (nhds 0) := by
    simpa only [sub_self] using hv.sub hxlim
  have hpos : ∀ n, 0 < v n - x := fun n => sub_pos.2 (habove n)
  have hc : 0 < x ^ 2 / 2 := by
    nlinarith [sq_pos_of_ne_zero hx0]
  have hbase :
      Tendsto (fun n => (x ^ 2 / 2) / (v n - x)) atTop atTop :=
    tendsto_pos_div_zero_right (x ^ 2 / 2) hc _ hpos hw
  have hvpow : Tendsto (fun n => v n ^ 2) atTop (nhds (x ^ 2)) := hv.pow 2
  have hnum : ∀ᶠ n in atTop, x ^ 2 / 2 < v n ^ 2 :=
    hvpow.eventually (Ioi_mem_nhds (by nlinarith [sq_pos_of_ne_zero hx0]))
  refine tendsto_atTop.2 ?_
  intro b
  have hb := hbase.eventually (eventually_ge_atTop b)
  filter_upwards [hb, hnum] with n hbn hnum_n
  exact hbn.trans
    ((div_le_div_iff_of_pos_right (hpos n)).2 (le_of_lt hnum_n))

theorem gap13 (x : ℝ) (hx0 : x ≠ 0) (hxq : ¬ IsRational x)
    (v : ℕ → ℝ) (hrat : ∀ n, IsRational (v n))
    (habove : ∀ n, x < v n) (hv : Tendsto v atTop (nhds x)) :
    Tendsto (fun n => (f (v n) - f x) / (v n - x)) atTop atTop := by
  rw [gap11 x hx0 hxq v hrat]
  exact gap12 x hx0 v habove hv

theorem gap14 (x : ℝ) (hx0 : x ≠ 0) (hxq : ¬ IsRational x) :
    ¬ DifferentiableAt ℝ f x := by
  intro hd
  obtain ⟨v, hvall, hv⟩ := gap10 x hx0 hxq
  have hcont := hd.continuousAt.tendsto.comp hv
  have hfv : (f ∘ v) = (fun n => v n ^ 2) := by
    funext n
    simp [Function.comp_apply, f, (hvall n).1]
  have hfx : f x = 0 := by
    simp [f, hxq]
  rw [hfv, hfx] at hcont
  have hsquare : Tendsto (fun n => v n ^ 2) atTop (nhds (x ^ 2)) := hv.pow 2
  have hsq : (0 : ℝ) = x ^ 2 := tendsto_nhds_unique hcont hsquare
  nlinarith [sq_pos_of_ne_zero hx0]

theorem gap15 :
    DifferentiableAt ℝ f 0 := by
  exact gap4

theorem gap16 (x : ℝ) (hx0 : x ≠ 0) :
    ¬ DifferentiableAt ℝ f x := by
  classical
  by_cases hxq : IsRational x
  · exact gap9 x hx0 hxq
  · exact gap14 x hx0 hxq

theorem gap17 :
    DifferentiableAt ℝ f 0 ∧
      ∀ x, x ≠ 0 → ¬ DifferentiableAt ℝ f x := by
  exact ⟨gap15, fun x hx => gap16 x hx⟩

end

end ProofGap.Exercise998
