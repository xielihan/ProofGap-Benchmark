import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise460

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.sqrt (1 / x + Real.sqrt (1 / x + Real.sqrt (1 / x))) -
    Real.sqrt (1 / x - Real.sqrt (1 / x + Real.sqrt (1 / x)))

def rationalized (x : ℝ) : ℝ :=
  (2 * Real.sqrt (1 / x + Real.sqrt (1 / x))) /
    (Real.sqrt (1 / x + Real.sqrt (1 / x + Real.sqrt (1 / x))) +
      Real.sqrt (1 / x - Real.sqrt (1 / x + Real.sqrt (1 / x))))

def scaled (x : ℝ) : ℝ :=
  Real.sqrt (1 + Real.sqrt x) /
    (Real.sqrt (1 + Real.sqrt (x + x * Real.sqrt x)) +
      Real.sqrt (1 - Real.sqrt (x + x * Real.sqrt x)))

def HasRightLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds L)

/-- Exercise 460, gap 1; rationalize the difference of square roots. -/
private theorem nonneg_eq_of_sq_eq
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hsq : p ^ 2 = q ^ 2) : p = q := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hd : 0 < q - p := sub_pos.mpr hpq
    have hs : 0 < q + p := by nlinarith
    have hm := mul_pos hd hs
    nlinarith
  · have hd : 0 < p - q := sub_pos.mpr hqp
    have hs : 0 < p + q := by nlinarith
    have hm := mul_pos hd hs
    nlinarith

set_option maxHeartbeats 16000000 in
private theorem original_eq_rationalized_near_zero
    (x : ℝ) (hx : 0 < x) (hsmall : x < 1 / 16) :
    original x = rationalized x := by
  let a : ℝ := 1 / x
  let u : ℝ := Real.sqrt a
  let b : ℝ := Real.sqrt (a + u)
  let A : ℝ := Real.sqrt (a + b)
  let B : ℝ := Real.sqrt (a - b)
  have ha : 16 < a := by
    dsimp [a]
    rw [lt_div_iff₀ hx]
    nlinarith
  have ha0 : 0 ≤ a := by nlinarith
  have hu0 : 0 ≤ u := Real.sqrt_nonneg a
  have hu_sq : u ^ 2 = a := by
    dsimp [u]
    exact Real.sq_sqrt ha0
  have hu_gt : 4 < u := by
    nlinarith
  have hu_lt_a : u < a := by
    have hm : 0 < u * (u - 1) := mul_pos (by nlinarith) (by nlinarith)
    nlinarith
  have hb0 : 0 ≤ b := Real.sqrt_nonneg (a + u)
  have hb_sq : b ^ 2 = a + u := by
    dsimp [b]
    exact Real.sq_sqrt (by nlinarith)
  have haa : a + u < a ^ 2 := by
    have hm : 0 < a * (a - 2) := mul_pos (by nlinarith) (by nlinarith)
    nlinarith
  have hb_lt_a : b < a := by
    by_contra h
    have hab : a ≤ b := le_of_not_gt h
    have hm : 0 ≤ (b - a) * (b + a) :=
      mul_nonneg (sub_nonneg.mpr hab) (by nlinarith)
    nlinarith
  have hminus : 0 ≤ a - b := by nlinarith
  have hA0 : 0 ≤ A := Real.sqrt_nonneg (a + b)
  have hApos : 0 < A := Real.sqrt_pos.2 (by nlinarith)
  have hA_sq : A ^ 2 = a + b := by
    dsimp [A]
    exact Real.sq_sqrt (by nlinarith)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg (a - b)
  have hB_sq : B ^ 2 = a - b := by
    dsimp [B]
    exact Real.sq_sqrt hminus
  have hden : A + B ≠ 0 := by
    apply ne_of_gt
    nlinarith
  change A - B = 2 * b / (A + B)
  apply (eq_div_iff hden).2
  nlinarith

set_option maxHeartbeats 16000000 in
private theorem rationalized_eq_two_scaled_near_zero
    (x : ℝ) (hx : 0 < x) (hsmall : x < 1 / 16) :
    rationalized x = 2 * scaled x := by
  let r : ℝ := Real.sqrt x
  let a : ℝ := 1 / x
  let u : ℝ := Real.sqrt a
  let b : ℝ := Real.sqrt (a + u)
  let d : ℝ := Real.sqrt (a + b)
  let f : ℝ := Real.sqrt (a - b)
  let c : ℝ := Real.sqrt (1 + r)
  let q : ℝ := Real.sqrt (x + x * r)
  let e : ℝ := Real.sqrt (1 + q)
  let g : ℝ := Real.sqrt (1 - q)
  have ha : 16 < a := by
    dsimp [a]
    rw [lt_div_iff₀ hx]
    nlinarith
  have ha0 : 0 ≤ a := by nlinarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg x
  have hrpos : 0 < r := Real.sqrt_pos.2 hx
  have hr_sq : r ^ 2 = x := by
    dsimp [r]
    exact Real.sq_sqrt (le_of_lt hx)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg a
  have hu_sq : u ^ 2 = a := by
    dsimp [u]
    exact Real.sq_sqrt ha0
  have hu_gt : 4 < u := by nlinarith
  have hu_lt_a : u < a := by
    have hm : 0 < u * (u - 1) := mul_pos (by nlinarith) (by nlinarith)
    nlinarith
  have hxa : x * a = 1 := by
    dsimp [a]
    field_simp [ne_of_gt hx]
  have hru_sq : (r * u) ^ 2 = (1 : ℝ) ^ 2 := by
    calc
      (r * u) ^ 2 = r ^ 2 * u ^ 2 := by ring
      _ = x * a := by rw [hr_sq, hu_sq]
      _ = 1 := hxa
      _ = (1 : ℝ) ^ 2 := by norm_num
  have hru : r * u = 1 :=
    nonneg_eq_of_sq_eq (r * u) 1 (mul_nonneg hr0 hu0) (by norm_num) hru_sq
  have hxu : x * u = r := by
    calc
      x * u = r * (r * u) := by rw [← hr_sq]; ring
      _ = r := by rw [hru]; ring
  have hb0 : 0 ≤ b := Real.sqrt_nonneg (a + u)
  have hb_sq : b ^ 2 = a + u := by
    dsimp [b]
    exact Real.sq_sqrt (by nlinarith)
  have haa : a + u < a ^ 2 := by
    have hm : 0 < a * (a - 2) := mul_pos (by nlinarith) (by nlinarith)
    nlinarith
  have hb_lt_a : b < a := by
    by_contra h
    have hab : a ≤ b := le_of_not_gt h
    have hm : 0 ≤ (b - a) * (b + a) :=
      mul_nonneg (sub_nonneg.mpr hab) (by nlinarith)
    nlinarith
  have hminus : 0 ≤ a - b := by nlinarith
  have hd0 : 0 ≤ d := Real.sqrt_nonneg (a + b)
  have hdpos : 0 < d := Real.sqrt_pos.2 (by nlinarith)
  have hd_sq : d ^ 2 = a + b := by
    dsimp [d]
    exact Real.sq_sqrt (by nlinarith)
  have hf0 : 0 ≤ f := Real.sqrt_nonneg (a - b)
  have hf_sq : f ^ 2 = a - b := by
    dsimp [f]
    exact Real.sq_sqrt hminus
  have hc0 : 0 ≤ c := Real.sqrt_nonneg (1 + r)
  have hc_sq : c ^ 2 = 1 + r := by
    dsimp [c]
    exact Real.sq_sqrt (by nlinarith)
  have hrb_sq : (r * b) ^ 2 = c ^ 2 := by
    calc
      (r * b) ^ 2 = r ^ 2 * b ^ 2 := by ring
      _ = x * (a + u) := by rw [hr_sq, hb_sq]
      _ = 1 + r := by rw [mul_add, hxa, hxu]
      _ = c ^ 2 := by rw [hc_sq]
  have hrb : r * b = c :=
    nonneg_eq_of_sq_eq (r * b) c (mul_nonneg hr0 hb0) hc0 hrb_sq
  have hxb_lt_one : x * b < 1 := by
    calc
      x * b < x * a := mul_lt_mul_of_pos_left hb_lt_a hx
      _ = 1 := hxa
  have hq0 : 0 ≤ q := Real.sqrt_nonneg (x + x * r)
  have hq_sq : q ^ 2 = x + x * r := by
    dsimp [q]
    exact Real.sq_sqrt (by nlinarith)
  have hxb_sq : (x * b) ^ 2 = q ^ 2 := by
    calc
      (x * b) ^ 2 = x ^ 2 * b ^ 2 := by ring
      _ = x ^ 2 * (a + u) := by rw [hb_sq]
      _ = x * (x * a) + x * (x * u) := by ring
      _ = x + x * r := by rw [hxa, hxu]; ring
      _ = q ^ 2 := by rw [hq_sq]
  have hxb : x * b = q :=
    nonneg_eq_of_sq_eq (x * b) q (mul_nonneg (le_of_lt hx) hb0) hq0 hxb_sq
  have hq_lt_one : q < 1 := by nlinarith
  have he0 : 0 ≤ e := Real.sqrt_nonneg (1 + q)
  have he_sq : e ^ 2 = 1 + q := by
    dsimp [e]
    exact Real.sq_sqrt (by nlinarith)
  have hg0 : 0 ≤ g := Real.sqrt_nonneg (1 - q)
  have hg_sq : g ^ 2 = 1 - q := by
    dsimp [g]
    exact Real.sq_sqrt (by nlinarith)
  have hrd_sq : (r * d) ^ 2 = e ^ 2 := by
    calc
      (r * d) ^ 2 = r ^ 2 * d ^ 2 := by ring
      _ = x * (a + b) := by rw [hr_sq, hd_sq]
      _ = x * a + x * b := by ring
      _ = 1 + q := by rw [hxa, hxb]
      _ = e ^ 2 := by rw [he_sq]
  have hrd : r * d = e :=
    nonneg_eq_of_sq_eq (r * d) e (mul_nonneg hr0 hd0) he0 hrd_sq
  have hrf_sq : (r * f) ^ 2 = g ^ 2 := by
    calc
      (r * f) ^ 2 = r ^ 2 * f ^ 2 := by ring
      _ = x * (a - b) := by rw [hr_sq, hf_sq]
      _ = x * a - x * b := by ring
      _ = 1 - q := by rw [hxa, hxb]
      _ = g ^ 2 := by rw [hg_sq]
  have hrf : r * f = g :=
    nonneg_eq_of_sq_eq (r * f) g (mul_nonneg hr0 hf0) hg0 hrf_sq
  have hden : d + f ≠ 0 := by
    apply ne_of_gt
    nlinarith
  change 2 * b / (d + f) = 2 * (c / (e + g))
  rw [← hrb, ← hrd, ← hrf, ← mul_add]
  field_simp [ne_of_gt hrpos, hden] <;> ring

theorem gap1 (L : ℝ) :
    HasRightLimitAt original 0 L ↔ HasRightLimitAt rationalized 0 L := by
  unfold HasRightLimitAt
  have hlt : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < 1 / 16 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)).filter_mono inf_le_left
  have heq : original =ᶠ[nhdsWithin 0 (Set.Ioi 0)] rationalized := by
    filter_upwards [self_mem_nhdsWithin, hlt] with x hx hsmall
    exact original_eq_rationalized_near_zero x hx hsmall
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Exercise 460, gap 2; scale numerator and denominator by `√x`. -/
theorem gap2 (L : ℝ) :
    HasRightLimitAt rationalized 0 L ↔
      HasRightLimitAt (fun x => 2 * scaled x) 0 L := by
  unfold HasRightLimitAt
  have hlt : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < 1 / 16 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)).filter_mono inf_le_left
  have heq : rationalized =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun x => 2 * scaled x) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with x hx hsmall
    exact rationalized_eq_two_scaled_near_zero x hx hsmall
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Exercise 460, gap 3. -/
theorem gap3 : HasRightLimitAt (fun x => 2 * scaled x) 0 1 := by
  have hinner : Continuous (fun x : ℝ => x + x * Real.sqrt x) :=
    continuous_id.add (continuous_id.mul Real.continuous_sqrt)
  have hrootInner : Continuous (fun x : ℝ => Real.sqrt (x + x * Real.sqrt x)) :=
    Real.continuous_sqrt.comp hinner
  have hnum : Continuous (fun x : ℝ => Real.sqrt (1 + Real.sqrt x)) :=
    Real.continuous_sqrt.comp (continuous_const.add Real.continuous_sqrt)
  have hden₁ :
      Continuous (fun x : ℝ => Real.sqrt (1 + Real.sqrt (x + x * Real.sqrt x))) :=
    Real.continuous_sqrt.comp (continuous_const.add hrootInner)
  have hden₂ :
      Continuous (fun x : ℝ => Real.sqrt (1 - Real.sqrt (x + x * Real.sqrt x))) :=
    Real.continuous_sqrt.comp (continuous_const.sub hrootInner)
  have hscaled : ContinuousAt scaled 0 := by
    unfold scaled
    exact hnum.continuousAt.div (hden₁.add hden₂).continuousAt (by norm_num)
  have hcont : ContinuousAt (fun x : ℝ => 2 * scaled x) 0 :=
    continuousAt_const.mul hscaled
  have hvalue : 2 * scaled 0 = 1 := by
    norm_num [scaled]
  unfold HasRightLimitAt
  rw [← hvalue]
  exact hcont.mono_left inf_le_left

end

end ProofGap.Exercise460
