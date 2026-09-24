import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1391

noncomputable section

open Filter

def f (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2) - x
def normalizedRoot (x : ℝ) : ℝ := Real.sqrt (1 + (1 / x) ^ 2)
def normalizedPolynomial (x : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) / x ^ 2 - (1 / 8 : ℝ) / x ^ 4
def finalPolynomial (x : ℝ) : ℝ :=
  1 / (2 * x) - 1 / (8 * x ^ 3)

def AgreesAtTop (g p scale : ℝ → ℝ) : Prop :=
  Asymptotics.IsLittleO atTop (fun x => g x - p x) scale

private theorem sqrt_quadratic_error_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.sqrt (1 + t) - (1 + t / 2 - t ^ 2 / 8)| ≤ t ^ 3 := by
  let s : ℝ := Real.sqrt (1 + t)
  let q : ℝ := 1 + t / 2 - t ^ 2 / 8
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + t := by
    dsimp [s]
    exact Real.sq_sqrt (by linarith)
  have hq1 : 1 ≤ q := by
    have hp : 0 ≤ t * (4 - t) :=
      mul_nonneg ht0 (by linarith)
    dsimp [q]
    nlinarith
  have hdpos : 0 < s + q := by linarith
  have hn0 : 0 ≤ t ^ 3 / 8 - t ^ 4 / 64 := by
    have hp : 0 ≤ t ^ 3 * (8 - t) :=
      mul_nonneg (pow_nonneg ht0 3) (by linarith)
    nlinarith
  have hnle : t ^ 3 / 8 - t ^ 4 / 64 ≤ t ^ 3 := by
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht0 3
    have ht4 : 0 ≤ t ^ 4 := pow_nonneg ht0 4
    nlinarith
  have hid :
      (s - q) * (s + q) = t ^ 3 / 8 - t ^ 4 / 64 := by
    calc
      (s - q) * (s + q) = s ^ 2 - q ^ 2 := by ring
      _ = t ^ 3 / 8 - t ^ 4 / 64 := by
        rw [hs2]
        dsimp [q]
        ring
  have heq : s - q =
      (t ^ 3 / 8 - t ^ 4 / 64) / (s + q) := by
    apply (eq_div_iff (ne_of_gt hdpos)).2
    exact hid
  have hden : 1 ≤ s + q := by linarith
  change |s - q| ≤ t ^ 3
  rw [heq, abs_div, abs_of_nonneg hn0, abs_of_pos hdpos]
  exact (div_le_self hn0 hden).trans hnle

theorem gap1 :
    AgreesAtTop normalizedRoot normalizedPolynomial (fun x => 1 / x ^ 4) := by
  unfold AgreesAtTop
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [eventually_gt_atTop (max 1 (1 / c))] with x hx
  have hx1 : 1 < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hxpos : 0 < x := lt_trans (by norm_num) hx1
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hcx : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
  have hu0 : 0 ≤ 1 / x := le_of_lt (one_div_pos.mpr hxpos)
  have hu_lt_one : 1 / x < 1 := by
    apply (div_lt_iff₀ hxpos).2
    linarith
  have hu_lt_c : 1 / x < c := by
    apply (div_lt_iff₀ hxpos).2
    have hxc : 1 < x * c := (div_lt_iff₀ hc).1 hcx
    simpa [mul_comm] using hxc
  let t : ℝ := (1 / x) ^ 2
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have htu : t ≤ 1 / x := by
    dsimp [t]
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr (le_of_lt hu_lt_one))]
  have ht1 : t ≤ 1 := le_trans htu (le_of_lt hu_lt_one)
  have htc : t ≤ c := le_trans htu (le_of_lt hu_lt_c)
  have hpoly : normalizedPolynomial x = 1 + t / 2 - t ^ 2 / 8 := by
    dsimp [normalizedPolynomial, t]
    field_simp [hx0]
    <;> ring
  have hscale : ‖(1 / x ^ 4 : ℝ)‖ = t ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (pow_pos hxpos 4))]
    dsimp [t]
    field_simp [hx0]
    <;> ring
  have herr : ‖normalizedRoot x - normalizedPolynomial x‖ ≤ t ^ 3 := by
    rw [Real.norm_eq_abs, hpoly]
    simpa [normalizedRoot, t] using
      sqrt_quadratic_error_bound t ht0 ht1
  calc
    ‖normalizedRoot x - normalizedPolynomial x‖ ≤ t ^ 3 := herr
    _ ≤ c * t ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr htc)]
    _ = c * ‖(1 / x ^ 4 : ℝ)‖ := by rw [hscale]

theorem gap2 (x : ℝ) :
    f x = Real.sqrt (1 + x ^ 2) - x := by
  rfl

theorem gap3 (x : ℝ) (hx : 0 < x) :
    Real.sqrt (1 + x ^ 2) - x = x * normalizedRoot x - x := by
  unfold normalizedRoot
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hleft0 : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
  have harg : 0 ≤ 1 + (1 / x) ^ 2 := by positivity
  have hright0 : 0 ≤ x * Real.sqrt (1 + (1 / x) ^ 2) :=
    mul_nonneg (le_of_lt hx) (Real.sqrt_nonneg _)
  have hleftsq : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hrightsq : (Real.sqrt (1 + (1 / x) ^ 2)) ^ 2 =
      1 + (1 / x) ^ 2 := Real.sq_sqrt harg
  have hsq : (Real.sqrt (1 + x ^ 2)) ^ 2 =
      (x * Real.sqrt (1 + (1 / x) ^ 2)) ^ 2 := by
    rw [hleftsq, mul_pow, hrightsq]
    field_simp [hx0]
    <;> ring
  have heq : Real.sqrt (1 + x ^ 2) =
      x * Real.sqrt (1 + (1 / x) ^ 2) := by
    nlinarith
  rw [heq]

theorem gap4 :
    AgreesAtTop (fun x => x * normalizedRoot x - x)
      finalPolynomial (fun x => 1 / x ^ 3) := by
  unfold AgreesAtTop
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hbase :
      (fun x => normalizedRoot x - normalizedPolynomial x) =o[atTop]
        (fun x => 1 / x ^ 4) := by
    simpa [AgreesAtTop] using gap1
  have hsmall : ∀ᶠ x : ℝ in atTop,
      ‖normalizedRoot x - normalizedPolynomial x‖ ≤
        c * ‖(1 / x ^ 4 : ℝ)‖ :=
    (Asymptotics.isLittleO_iff.1 hbase) hc
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hbound hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hpoly : x * normalizedPolynomial x - x = finalPolynomial x := by
    change
      x * (1 + (1 / 2 : ℝ) / x ^ 2 - (1 / 8 : ℝ) / x ^ 4) - x =
        1 / (2 * x) - 1 / (8 * x ^ 3)
    field_simp [hx0]
    <;> ring
  have herr :
      (x * normalizedRoot x - x) - finalPolynomial x =
        x * (normalizedRoot x - normalizedPolynomial x) := by
    rw [← hpoly]
    ring
  have hx3 : 0 < (1 / x ^ 3 : ℝ) := one_div_pos.mpr (pow_pos hx 3)
  have hx4 : 0 < (1 / x ^ 4 : ℝ) := one_div_pos.mpr (pow_pos hx 4)
  have hnorm :
      ‖x‖ * (c * ‖(1 / x ^ 4 : ℝ)‖) =
        c * ‖(1 / x ^ 3 : ℝ)‖ := by
    simp only [Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hx3,
      abs_of_pos hx4]
    field_simp [hx0]
    <;> ring
  rw [herr, norm_mul]
  calc
    ‖x‖ * ‖normalizedRoot x - normalizedPolynomial x‖ ≤
        ‖x‖ * (c * ‖(1 / x ^ 4 : ℝ)‖) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg x)
    _ = c * ‖(1 / x ^ 3 : ℝ)‖ := hnorm

theorem gap5 :
    AgreesAtTop f finalPolynomial (fun x => 1 / x ^ 3) := by
  unfold AgreesAtTop
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hbase :
      (fun x => (x * normalizedRoot x - x) - finalPolynomial x) =o[atTop]
        (fun x => 1 / x ^ 3) := by
    simpa [AgreesAtTop] using gap4
  have hsmall : ∀ᶠ x : ℝ in atTop,
      ‖(x * normalizedRoot x - x) - finalPolynomial x‖ ≤
        c * ‖(1 / x ^ 3 : ℝ)‖ :=
    (Asymptotics.isLittleO_iff.1 hbase) hc
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hbound hx
  have hf : f x = x * normalizedRoot x - x := by
    calc
      f x = Real.sqrt (1 + x ^ 2) - x := gap2 x
      _ = x * normalizedRoot x - x := gap3 x hx
  rw [hf]
  exact hbound

end

end ProofGap.Exercise1391
