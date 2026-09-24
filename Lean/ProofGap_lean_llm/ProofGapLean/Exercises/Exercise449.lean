import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

namespace ProofGap.Exercise449

noncomputable section

def root (k : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (k : ℝ))
def original (x : ℝ) : ℝ :=
  (Real.sqrt (x + 2) - root 3 (x + 20)) / (root 4 (x + 9) - 2)
def bridge (x : ℝ) : ℝ :=
  (Finset.range 6).sum (fun k =>
    root 6 ((x + 2) ^ (15 - 3 * k) * (x + 20) ^ (2 * k)))
def cancelled (x : ℝ) : ℝ :=
  ((x ^ 2 + 12 * x + 56) * (root 4 (x + 9) + 2) *
      (Real.sqrt (x + 9) + 4)) / bridge x
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_449/1.txt`; replace the radical ellipsis by a six-term finite sum. -/
private theorem root_pow_self
    (k : ℕ) (hk : 0 < k) (t : ℝ) (ht : 0 ≤ t) :
    root k (t ^ k) = t := by
  rcases eq_or_lt_of_le ht with hzero | htpos
  · subst t
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    simp [root, hk0]
  · unfold root
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hlog :
        (k : ℝ) * Real.log t * (1 / (k : ℝ)) = Real.log t := by
      field_simp [hk0]
    calc
      Real.rpow (t ^ k) (1 / (k : ℝ)) =
          Real.exp (Real.log (t ^ k) * (1 / (k : ℝ))) := by
        exact Real.rpow_def_of_pos (pow_pos htpos k) (1 / (k : ℝ))
      _ = Real.exp ((k : ℝ) * Real.log t * (1 / (k : ℝ))) := by
        rw [Real.log_pow]
      _ = Real.exp (Real.log t) := by rw [hlog]
      _ = t := Real.exp_log htpos

private theorem root_continuousAt
    (k : ℕ) {x : ℝ} (hx : 0 < x) : ContinuousAt (root k) x := by
  let g : ℝ → ℝ := fun y => Real.exp (Real.log y * (1 / (k : ℝ)))
  have heq : root k =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [root, g, Real.rpow_def_of_pos hy]
  have hg : ContinuousAt g x := by
    dsimp [g]
    fun_prop (disch := positivity)
  have hg' : Filter.Tendsto g (nhds x) (nhds (root k x)) := by
    simpa [g, root, Real.rpow_def_of_pos hx] using hg
  exact (Filter.tendsto_congr' heq).2 hg'

private theorem bridge_eq_radicals
    (x : ℝ) (hy : 0 < x + 2) (hz : 0 < x + 20) :
    bridge x =
      (Real.sqrt (x + 2)) ^ 5 +
      (Real.sqrt (x + 2)) ^ 4 * root 3 (x + 20) +
      (Real.sqrt (x + 2)) ^ 3 * (root 3 (x + 20)) ^ 2 +
      (Real.sqrt (x + 2)) ^ 2 * (root 3 (x + 20)) ^ 3 +
      Real.sqrt (x + 2) * (root 3 (x + 20)) ^ 4 +
      (root 3 (x + 20)) ^ 5 := by
  let y : ℝ := x + 2
  let z : ℝ := x + 20
  let a : ℝ := Real.sqrt y
  let b : ℝ := root 3 z
  have ha : 0 ≤ a := by
    dsimp [a]
    exact Real.sqrt_nonneg y
  have hb : 0 < b := by
    dsimp [b, root]
    positivity
  have hb0 : 0 ≤ b := le_of_lt hb
  have ha2 : a ^ 2 = y := by
    dsimp [a]
    exact Real.sq_sqrt (le_of_lt hy)
  have hb3 : b ^ 3 = z := by
    dsimp [b, root, z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hz)]
    norm_num
  have ht0 : root 6 (y ^ 15 * z ^ 0) = a ^ 5 := by
    rw [show y ^ 15 * z ^ 0 = (a ^ 5) ^ 6 by
      rw [← ha2]
      ring]
    exact root_pow_self 6 (by norm_num) (a ^ 5) (pow_nonneg ha 5)
  have ht1 : root 6 (y ^ 12 * z ^ 2) = a ^ 4 * b := by
    rw [show y ^ 12 * z ^ 2 = (a ^ 4 * b) ^ 6 by
      rw [← ha2, ← hb3]
      ring]
    exact root_pow_self 6 (by norm_num) (a ^ 4 * b)
      (mul_nonneg (pow_nonneg ha 4) hb0)
  have ht2 : root 6 (y ^ 9 * z ^ 4) = a ^ 3 * b ^ 2 := by
    rw [show y ^ 9 * z ^ 4 = (a ^ 3 * b ^ 2) ^ 6 by
      rw [← ha2, ← hb3]
      ring]
    exact root_pow_self 6 (by norm_num) (a ^ 3 * b ^ 2)
      (mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb0 2))
  have ht3 : root 6 (y ^ 6 * z ^ 6) = a ^ 2 * b ^ 3 := by
    rw [show y ^ 6 * z ^ 6 = (a ^ 2 * b ^ 3) ^ 6 by
      rw [← ha2, ← hb3]
      ring]
    exact root_pow_self 6 (by norm_num) (a ^ 2 * b ^ 3)
      (mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb0 3))
  have ht4 : root 6 (y ^ 3 * z ^ 8) = a * b ^ 4 := by
    rw [show y ^ 3 * z ^ 8 = (a * b ^ 4) ^ 6 by
      rw [← ha2, ← hb3]
      ring]
    exact root_pow_self 6 (by norm_num) (a * b ^ 4)
      (mul_nonneg ha (pow_nonneg hb0 4))
  have ht5 : root 6 (y ^ 0 * z ^ 10) = b ^ 5 := by
    rw [show y ^ 0 * z ^ 10 = (b ^ 5) ^ 6 by
      rw [← hb3]
      ring]
    exact root_pow_self 6 (by norm_num) (b ^ 5) (pow_nonneg hb0 5)
  have ht0' : root 6 (y ^ 15) = a ^ 5 := by simpa using ht0
  have ht5' : root 6 (z ^ 10) = b ^ 5 := by simpa using ht5
  dsimp [y, z, a, b] at ht0' ht1 ht2 ht3 ht4 ht5' ⊢
  norm_num [bridge, Finset.sum_range_succ, ht0', ht1, ht2, ht3, ht4, ht5']

private theorem original_eq_cancelled_near_seven
    (x : ℝ) (hxI : x ∈ Set.Ioo (6 : ℝ) 8) (hx7 : x ≠ 7) :
    original x = cancelled x := by
  let y : ℝ := x + 2
  let z : ℝ := x + 20
  let w : ℝ := x + 9
  let a : ℝ := Real.sqrt y
  let b : ℝ := root 3 z
  let c : ℝ := root 4 w
  have hy : 0 < y := by dsimp [y]; linarith [hxI.1]
  have hz : 0 < z := by dsimp [z]; linarith [hxI.1]
  have hw : 0 < w := by dsimp [w]; linarith [hxI.1]
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b, root]; positivity
  have hc : 0 < c := by dsimp [c, root]; positivity
  have ha2 : a ^ 2 = y := by
    dsimp [a]
    exact Real.sq_sqrt (le_of_lt hy)
  have hb3 : b ^ 3 = z := by
    dsimp [b, root]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hz)]
    norm_num
  have hc4 : c ^ 4 = w := by
    dsimp [c, root]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hw)]
    norm_num
  have hbridge : bridge x =
      a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 +
        a * b ^ 4 + b ^ 5 := by
    simpa [y, z, a, b] using bridge_eq_radicals x hy hz
  have ha6 : a ^ 6 = y ^ 3 := by
    calc
      a ^ 6 = (a ^ 2) ^ 3 := by ring
      _ = y ^ 3 := by rw [ha2]
  have hb6 : b ^ 6 = z ^ 2 := by
    calc
      b ^ 6 = (b ^ 3) ^ 2 := by ring
      _ = z ^ 2 := by rw [hb3]
  have hnum :
      (a - b) * bridge x = (x - 7) * (x ^ 2 + 12 * x + 56) := by
    rw [hbridge]
    calc
      (a - b) *
          (a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 +
            a * b ^ 4 + b ^ 5) = a ^ 6 - b ^ 6 := by ring
      _ = y ^ 3 - z ^ 2 := by rw [ha6, hb6]
      _ = (x - 7) * (x ^ 2 + 12 * x + 56) := by
        dsimp [y, z]
        ring
  have hs2 : (Real.sqrt w) ^ 2 = w := Real.sq_sqrt (le_of_lt hw)
  have hc2 : c ^ 2 = Real.sqrt w := by
    nlinarith [hc4, hs2, Real.sqrt_nonneg w, sq_nonneg c,
      sq_nonneg (c ^ 2 - Real.sqrt w), sq_nonneg (c ^ 2 + Real.sqrt w)]
  have hden :
      (c - 2) * (c + 2) * (Real.sqrt w + 4) = x - 7 := by
    rw [← hc2]
    calc
      (c - 2) * (c + 2) * (c ^ 2 + 4) = c ^ 4 - 16 := by ring
      _ = w - 16 := by rw [hc4]
      _ = x - 7 := by dsimp [w]; ring
  have hcminus : c - 2 ≠ 0 := by
    intro h
    have : x - 7 = 0 := by rw [← hden, h]; ring
    exact hx7 (by linarith)
  have hbridge_ne : bridge x ≠ 0 := by
    rw [hbridge]
    positivity
  unfold original cancelled
  change (a - b) / (c - 2) =
    ((x ^ 2 + 12 * x + 56) * (c + 2) * (Real.sqrt w + 4)) / bridge x
  apply (div_eq_div_iff hcminus hbridge_ne).2
  calc
    (a - b) * bridge x = (x - 7) * (x ^ 2 + 12 * x + 56) := hnum
    _ = ((x ^ 2 + 12 * x + 56) * (c + 2) * (Real.sqrt w + 4)) *
          (c - 2) := by rw [← hden]; ring

private theorem bridge_continuousAt_seven : ContinuousAt bridge 7 := by
  let e : ℝ → ℝ := fun x =>
    (Real.sqrt (x + 2)) ^ 5 +
    (Real.sqrt (x + 2)) ^ 4 * root 3 (x + 20) +
    (Real.sqrt (x + 2)) ^ 3 * (root 3 (x + 20)) ^ 2 +
    (Real.sqrt (x + 2)) ^ 2 * (root 3 (x + 20)) ^ 3 +
    Real.sqrt (x + 2) * (root 3 (x + 20)) ^ 4 +
    (root 3 (x + 20)) ^ 5
  have heq : bridge =ᶠ[nhds (7 : ℝ)] e := by
    filter_upwards [Ioo_mem_nhds (show (6 : ℝ) < 7 by norm_num)
      (show (7 : ℝ) < 8 by norm_num)] with x hx
    dsimp [e]
    apply bridge_eq_radicals
    · linarith [hx.1]
    · linarith [hx.1]
  have hpoint : bridge 7 = e 7 := by
    dsimp [e]
    exact bridge_eq_radicals 7 (by norm_num) (by norm_num)
  have ha : ContinuousAt (fun x : ℝ => Real.sqrt (x + 2)) 7 := by
    fun_prop (disch := positivity)
  have hb : ContinuousAt (fun x : ℝ => root 3 (x + 20)) 7 := by
    have hinner : ContinuousAt (fun x : ℝ => x + 20) 7 := by fun_prop
    have houter :
        ContinuousAt (root 3) ((fun x : ℝ => x + 20) 7) :=
      root_continuousAt 3 (by norm_num)
    exact ContinuousAt.comp (f := fun x : ℝ => x + 20) (x := (7 : ℝ))
      houter hinner
  have he : ContinuousAt e 7 := by
    dsimp [e]
    have h0 := (ha.pow 5).add ((ha.pow 4).mul hb)
    have h1 := h0.add ((ha.pow 3).mul (hb.pow 2))
    have h2 := h1.add ((ha.pow 2).mul (hb.pow 3))
    have h3 := h2.add (ha.mul (hb.pow 4))
    have h4 := h3.add (hb.pow 5)
    exact h4
  change Filter.Tendsto bridge (nhds 7) (nhds (bridge 7))
  apply (Filter.tendsto_congr' heq).2
  rw [hpoint]
  exact he

private theorem cancelled_limit_at_seven :
    HasLimitAt cancelled 7 ((189 * 4 * 8 : ℝ) / 1458) := by
  have hr4 : root 4 (16 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
    exact root_pow_self 4 (by norm_num) 2 (by norm_num)
  have hr3 : root 3 (27 : ℝ) = 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
    exact root_pow_self 3 (by norm_num) 3 (by norm_num)
  have hs9 : Real.sqrt (9 : ℝ) = 3 := by
    have hs9sq : (Real.sqrt (9 : ℝ)) ^ 2 = 9 :=
      Real.sq_sqrt (by norm_num)
    have hs9nonneg : 0 ≤ Real.sqrt (9 : ℝ) := Real.sqrt_nonneg 9
    nlinarith
  have hs16 : Real.sqrt (16 : ℝ) = 4 := by
    have hs16sq : (Real.sqrt (16 : ℝ)) ^ 2 = 16 :=
      Real.sq_sqrt (by norm_num)
    have hs16nonneg : 0 ≤ Real.sqrt (16 : ℝ) := Real.sqrt_nonneg 16
    nlinarith
  have hb : bridge 7 = 1458 := by
    rw [bridge_eq_radicals 7 (by norm_num) (by norm_num)]
    norm_num [hr3, hs9]
  have hrcont : ContinuousAt (fun x : ℝ => root 4 (x + 9)) 7 := by
    have hinner : ContinuousAt (fun x : ℝ => x + 9) 7 := by fun_prop
    have houter :
        ContinuousAt (root 4) ((fun x : ℝ => x + 9) 7) :=
      root_continuousAt 4 (by norm_num)
    exact ContinuousAt.comp (f := fun x : ℝ => x + 9) (x := (7 : ℝ))
      houter hinner
  have hscont : ContinuousAt (fun x : ℝ => Real.sqrt (x + 9)) 7 := by
    fun_prop (disch := positivity)
  have hpcont : ContinuousAt (fun x : ℝ => x ^ 2 + 12 * x + 56) 7 := by
    fun_prop
  have hnumcont : ContinuousAt
      (fun x : ℝ => (x ^ 2 + 12 * x + 56) * (root 4 (x + 9) + 2) *
        (Real.sqrt (x + 9) + 4)) 7 := by
    exact (hpcont.mul (hrcont.add continuousAt_const)).mul
      (hscont.add continuousAt_const)
  have hcont : ContinuousAt cancelled 7 := by
    unfold cancelled
    apply ContinuousAt.div hnumcont bridge_continuousAt_seven
    simpa [hb]
  have hval : cancelled 7 = (189 * 4 * 8 : ℝ) / 1458 := by
    norm_num [cancelled, hb, hr4, hs16]
  unfold HasLimitAt
  rw [← hval]
  exact hcont.tendsto.mono_left inf_le_left

theorem gap1 : HasLimitAt original 7 (4 + 4 / 27) ↔
    HasLimitAt cancelled 7 (4 + 4 / 27) := by
  unfold HasLimitAt
  have hI :
      ∀ᶠ x in nhdsWithin (7 : ℝ) ({7} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (6 : ℝ) 8 :=
    Filter.Eventually.filter_mono inf_le_left
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  have heq :
      original =ᶠ[nhdsWithin (7 : ℝ) ({7} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [hI, self_mem_nhdsWithin] with x hxI hx7
    apply original_eq_cancelled_near_seven x hxI
    simpa using hx7
  exact Filter.tendsto_congr' heq

/-- Source: `proof_gap/exercise_449/2.txt`. -/
theorem gap2 : HasLimitAt original 7 (4 + 4 / 27) ↔
    HasLimitAt cancelled 7 (4 + 4 / 27) := by
  exact gap1

/-- Source: `proof_gap/exercise_449/3.txt`. -/
theorem gap3 : HasLimitAt cancelled 7 ((189 * 4 * 8 : ℝ) / 1458) := by
  exact cancelled_limit_at_seven

/-- Source: `proof_gap/exercise_449/4.txt`. -/
theorem gap4 : (189 * 4 * 8 : ℝ) / 1458 = 6048 / 1458 := by
  norm_num

/-- Source: `proof_gap/exercise_449/5.txt`. -/
theorem gap5 : (6048 : ℝ) / 1458 = 4 + 4 / 27 := by
  norm_num

/-- Source: `proof_gap/exercise_449/6.txt`. -/
theorem gap6 : HasLimitAt cancelled 7 (4 + 4 / 27) := by
  rw [← gap5, ← gap4]
  exact gap3

end

end ProofGap.Exercise449
