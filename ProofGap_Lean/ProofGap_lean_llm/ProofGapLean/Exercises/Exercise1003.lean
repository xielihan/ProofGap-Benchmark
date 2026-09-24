import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1003

open Filter

noncomputable section

def f (x : ℝ) : ℝ := Real.sqrt (Real.sin (x ^ 2))
def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

def evenRoot (k : ℕ) : ℝ := Real.sqrt (2 * (k : ℝ) * Real.pi)
def oddRoot (k : ℕ) : ℝ := Real.sqrt ((2 * (k : ℝ) + 1) * Real.pi)

private theorem sin_period_nat (y : ℝ) : ∀ k : ℕ,
    Real.sin (y + 2 * (k : ℝ) * Real.pi) = Real.sin y := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        Real.sin (y + 2 * ((k + 1 : ℕ) : ℝ) * Real.pi) =
            Real.sin ((y + 2 * (k : ℝ) * Real.pi) + 2 * Real.pi) := by
              congr 1
              push_cast
              ring
        _ = Real.sin (y + 2 * (k : ℝ) * Real.pi) := Real.sin_add_two_pi _
        _ = Real.sin y := ih

private theorem cos_period_nat (y : ℝ) : ∀ k : ℕ,
    Real.cos (y + 2 * (k : ℝ) * Real.pi) = Real.cos y := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        Real.cos (y + 2 * ((k + 1 : ℕ) : ℝ) * Real.pi) =
            Real.cos ((y + 2 * (k : ℝ) * Real.pi) + 2 * Real.pi) := by
              congr 1
              push_cast
              ring
        _ = Real.cos (y + 2 * (k : ℝ) * Real.pi) := Real.cos_add_two_pi _
        _ = Real.cos y := ih

private theorem even_root_sq (k : ℕ) :
    evenRoot k ^ 2 = 2 * (k : ℝ) * Real.pi := by
  unfold evenRoot
  rw [Real.sq_sqrt]
  positivity

private theorem odd_root_sq (k : ℕ) :
    oddRoot k ^ 2 = (2 * (k : ℝ) + 1) * Real.pi := by
  unfold oddRoot
  rw [Real.sq_sqrt]
  positivity

private theorem sin_even_root (k : ℕ) :
    Real.sin (evenRoot k ^ 2) = 0 := by
  rw [even_root_sq]
  have h := sin_period_nat 0 k
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

private theorem cos_even_root (k : ℕ) :
    Real.cos (evenRoot k ^ 2) = 1 := by
  rw [even_root_sq]
  have h := cos_period_nat 0 k
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

private theorem sin_odd_root (k : ℕ) :
    Real.sin (oddRoot k ^ 2) = 0 := by
  rw [odd_root_sq]
  have h := sin_period_nat Real.pi k
  convert h using 1 <;> ring_nf <;> simp

private theorem cos_odd_root (k : ℕ) :
    Real.cos (oddRoot k ^ 2) = -1 := by
  rw [odd_root_sq]
  have h := cos_period_nat Real.pi k
  convert h using 1 <;> ring_nf <;> simp

private theorem sin_sq_pos_between (k : ℕ) (x : ℝ)
    (hl : evenRoot k < |x|) (hr : |x| < oddRoot k) :
    0 < Real.sin (x ^ 2) := by
  have he : 0 ≤ evenRoot k := Real.sqrt_nonneg _
  have ho : 0 ≤ oddRoot k := Real.sqrt_nonneg _
  have hxpos : 0 < |x| := lt_of_le_of_lt he hl
  have hsuml : 0 < evenRoot k + |x| :=
    add_pos_of_nonneg_of_pos he hxpos
  have hsumr : 0 < oddRoot k + |x| :=
    add_pos_of_nonneg_of_pos ho hxpos
  have hlowprod := mul_pos (sub_pos.mpr hl) hsuml
  have hupprod := mul_pos (sub_pos.mpr hr) hsumr
  have hlow : evenRoot k ^ 2 < x ^ 2 := by
    rw [← sq_abs x]
    nlinarith
  have hupp : x ^ 2 < oddRoot k ^ 2 := by
    rw [← sq_abs x]
    nlinarith
  have hy0 : 0 < x ^ 2 - 2 * (k : ℝ) * Real.pi := by
    rw [← even_root_sq]
    linarith
  have hypi : x ^ 2 - 2 * (k : ℝ) * Real.pi < Real.pi := by
    rw [odd_root_sq] at hupp
    linarith
  have hp := Real.sin_pos_of_pos_of_lt_pi hy0 hypi
  have hper := sin_period_nat (x ^ 2 - 2 * (k : ℝ) * Real.pi) k
  calc
    0 < Real.sin (x ^ 2 - 2 * (k : ℝ) * Real.pi) := hp
    _ = Real.sin (x ^ 2) := by
      rw [← hper]
      congr 1
      ring

private theorem hasDerivAt_hasSides {g : ℝ → ℝ} {g' a : ℝ}
    (hg : HasDerivAt g g' a) :
    HasLeftDerivAt g g' a ∧ HasRightDerivAt g g' a := by
  have ht : Tendsto (dq g a) (nhdsWithin 0 ({0}ᶜ)) (nhds g') := by
    simpa [dq, div_eq_mul_inv, mul_comm] using hg.tendsto_slope_zero
  constructor
  · exact ht.mono_left (nhdsWithin_mono 0 (by
      intro h hh
      simp only [Set.mem_Iio] at hh
      simp [ne_of_lt hh]))
  · exact ht.mono_left (nhdsWithin_mono 0 (by
      intro h hh
      simp only [Set.mem_Ioi] at hh
      simp [ne_of_gt hh]))

private theorem slope_right {q : ℝ → ℝ} {c : ℝ}
    (hq0 : q 0 = 0) (hq : HasDerivAt q c 0) :
    Tendsto (fun h => q h / h) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  have ht : Tendsto (fun h => q h / h) (nhdsWithin 0 ({0}ᶜ)) (nhds c) := by
    simpa [hq0, div_eq_mul_inv, mul_comm] using hq.tendsto_slope_zero
  exact ht.mono_left (nhdsWithin_mono 0 (by
    intro h hh
    simp only [Set.mem_Ioi] at hh
    simp [ne_of_gt hh]))

private theorem slope_left {q : ℝ → ℝ} {c : ℝ}
    (hq0 : q 0 = 0) (hq : HasDerivAt q c 0) :
    Tendsto (fun h => q h / h) (nhdsWithin 0 (Set.Iio 0)) (nhds c) := by
  have ht : Tendsto (fun h => q h / h) (nhdsWithin 0 ({0}ᶜ)) (nhds c) := by
    simpa [hq0, div_eq_mul_inv, mul_comm] using hq.tendsto_slope_zero
  exact ht.mono_left (nhdsWithin_mono 0 (by
    intro h hh
    simp only [Set.mem_Iio] at hh
    simp [ne_of_lt hh]))

private theorem sqrt_div_right_atTop {q : ℝ → ℝ} {c : ℝ}
    (hq0 : q 0 = 0) (hq : HasDerivAt q c 0) (hc : 0 < c) :
    Tendsto (fun h => Real.sqrt (q h) / h)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hslope := slope_right hq0 hq
  rw [tendsto_atTop]
  intro b
  let B : ℝ := |b| + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg b]
  let C : ℝ := c / (2 * B ^ 2)
  have hden : 0 < 2 * B ^ 2 := by positivity
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos hc hden
  have heSlope : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), c / 2 < q h / h :=
    hslope.eventually (Ioi_mem_nhds (by linarith))
  have hId : Tendsto (fun h : ℝ => h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have heSmall : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), h < C :=
    hId.eventually (Iio_mem_nhds hC)
  filter_upwards [heSlope, heSmall, self_mem_nhdsWithin] with h hsl hsmall hh
  have hh0 : 0 < h := hh
  have hccomp : 2 * B ^ 2 * h < c := by
    have ht : h * (2 * B ^ 2) < c :=
      (lt_div_iff₀ hden).mp (by simpa [C] using hsmall)
    nlinarith
  have hqbound : c / 2 * h < q h := (lt_div_iff₀ hh0).mp hsl
  have hsqbound : (B * h) ^ 2 < q h := by
    have hm := mul_pos (sub_pos.mpr hccomp) hh0
    nlinarith
  have hqpos : 0 < q h := by
    have : 0 < c / 2 * h := by positivity
    linarith
  have hsqsqrt := Real.sq_sqrt (le_of_lt hqpos)
  have hsqrt : B * h < Real.sqrt (q h) := by
    have hsnonneg := Real.sqrt_nonneg (q h)
    nlinarith
  have hbB : b < B := by
    dsimp [B]
    linarith [le_abs_self b]
  have hBquot : B < Real.sqrt (q h) / h := (lt_div_iff₀ hh0).2 (by
    simpa [mul_comm] using hsqrt)
  exact le_of_lt (hbB.trans hBquot)

private theorem sqrt_div_left_atBot {q : ℝ → ℝ} {c : ℝ}
    (hq0 : q 0 = 0) (hq : HasDerivAt q c 0) (hc : c < 0) :
    Tendsto (fun h => Real.sqrt (q h) / h)
      (nhdsWithin 0 (Set.Iio 0)) atBot := by
  have hslope := slope_left hq0 hq
  rw [tendsto_atBot]
  intro b
  let B : ℝ := |b| + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg b]
  let C : ℝ := (-c) / (2 * B ^ 2)
  have hden : 0 < 2 * B ^ 2 := by positivity
  have hnegc : 0 < -c := neg_pos.mpr hc
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos hnegc hden
  have heSlope : ∀ᶠ h in nhdsWithin 0 (Set.Iio 0), q h / h < c / 2 :=
    hslope.eventually (Iio_mem_nhds (by linarith))
  have hId : Tendsto (fun h : ℝ => h)
      (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have heSmall : ∀ᶠ h in nhdsWithin 0 (Set.Iio 0), -C < h :=
    hId.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [heSlope, heSmall, self_mem_nhdsWithin] with h hsl hsmall hh
  have hhneg : h < 0 := hh
  have hccomp : 2 * B ^ 2 * (-h) < -c := by
    have hsmall' : -h < C := by linarith
    have ht : (-h) * (2 * B ^ 2) < -c :=
      (lt_div_iff₀ hden).mp (by simpa [C] using hsmall')
    nlinarith
  have hqbound : c / 2 * h < q h := (div_lt_iff_of_neg hhneg).mp hsl
  have hsqbound : (B * (-h)) ^ 2 < q h := by
    have hm := mul_pos (sub_pos.mpr hccomp) (neg_pos.mpr hhneg)
    nlinarith
  have hqpos : 0 < q h := by
    have hprod : 0 < c / 2 * h :=
      mul_pos_of_neg_of_neg (by linarith) hhneg
    exact hprod.trans hqbound
  have hsqsqrt := Real.sq_sqrt (le_of_lt hqpos)
  have hsqrt : B * (-h) < Real.sqrt (q h) := by
    have hsnonneg := Real.sqrt_nonneg (q h)
    nlinarith
  have hquot : Real.sqrt (q h) / h < -B := by
    apply (div_lt_iff_of_neg hhneg).2
    nlinarith
  have hBb : -B < b := by
    dsimp [B]
    linarith [neg_abs_le b]
  exact le_of_lt (hquot.trans hBb)

private theorem sqrt_div_zero_left {q : ℝ → ℝ} {c : ℝ}
    (hq0 : q 0 = 0) (hq : HasDerivAt q c 0) (hc : 0 < c) :
    Tendsto (fun h => Real.sqrt (q h) / h)
      (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
  have hslope := slope_left hq0 hq
  have heSlope : ∀ᶠ h in nhdsWithin 0 (Set.Iio 0), c / 2 < q h / h :=
    hslope.eventually (Ioi_mem_nhds (by linarith))
  have heq : (fun h => Real.sqrt (q h) / h) =ᶠ[nhdsWithin 0 (Set.Iio 0)]
      fun _ => 0 := by
    filter_upwards [heSlope, self_mem_nhdsWithin] with h hs hh
    have hhneg : h < 0 := hh
    have hspos : 0 < q h / h := lt_trans (by linarith) hs
    have hqneg : q h < 0 := by
      by_contra hn
      have hqnonneg : 0 ≤ q h := le_of_not_gt hn
      have hdiv : q h / h ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos hqnonneg (le_of_lt hhneg)
      exact (not_lt_of_ge hdiv) hspos
    rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hqneg)]
    simp
  exact tendsto_const_nhds.congr' heq.symm

private theorem sqrt_div_zero_right {q : ℝ → ℝ} {c : ℝ}
    (hq0 : q 0 = 0) (hq : HasDerivAt q c 0) (hc : c < 0) :
    Tendsto (fun h => Real.sqrt (q h) / h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hslope := slope_right hq0 hq
  have heSlope : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), q h / h < c / 2 :=
    hslope.eventually (Iio_mem_nhds (by linarith))
  have heq : (fun h => Real.sqrt (q h) / h) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun _ => 0 := by
    filter_upwards [heSlope, self_mem_nhdsWithin] with h hs hh
    have hhpos : 0 < h := hh
    have hsneg : q h / h < 0 := lt_trans hs (by linarith)
    have hqneg : q h < 0 := by
      by_contra hn
      have hqnonneg : 0 ≤ q h := le_of_not_gt hn
      have hdiv : 0 ≤ q h / h :=
        div_nonneg hqnonneg (le_of_lt hhpos)
      exact (not_lt_of_ge hdiv) hsneg
    rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hqneg)]
    simp
  exact tendsto_const_nhds.congr' heq.symm

private theorem hasDerivAt_even_root (k : ℕ) :
    HasDerivAt (fun h : ℝ => Real.sin ((evenRoot k + h) ^ 2))
      (2 * evenRoot k) 0 := by
  have hp : HasDerivAt (fun h : ℝ => (evenRoot k + h) ^ 2)
      (2 * evenRoot k) 0 := by
    simpa [id, mul_comm] using
      (((hasDerivAt_id 0).const_add (evenRoot k)).pow 2)
  simpa [cos_even_root, mul_assoc, mul_left_comm, mul_comm] using
    (Real.hasDerivAt_sin ((evenRoot k + 0) ^ 2)).comp 0 hp

private theorem hasDerivAt_odd_root (k : ℕ) :
    HasDerivAt (fun h : ℝ => Real.sin ((oddRoot k + h) ^ 2))
      (-(2 * oddRoot k)) 0 := by
  have hp : HasDerivAt (fun h : ℝ => (oddRoot k + h) ^ 2)
      (2 * oddRoot k) 0 := by
    simpa [id, mul_comm] using
      (((hasDerivAt_id 0).const_add (oddRoot k)).pow 2)
  simpa [cos_odd_root, mul_assoc, mul_left_comm, mul_comm] using
    (Real.hasDerivAt_sin ((oddRoot k + 0) ^ 2)).comp 0 hp

private theorem sinc_sq_tendsto :
    Tendsto (fun h : ℝ => Real.sinc (h ^ 2)) (nhds 0) (nhds 1) := by
  have hp : Tendsto (fun h : ℝ => h ^ 2) (nhds 0) (nhds 0) := by
    simpa using
      (tendsto_id.pow 2 : Tendsto (fun h : ℝ => h ^ 2) (nhds 0) (nhds (0 ^ 2)))
  simpa using Real.continuous_sinc.continuousAt.tendsto.comp hp

private theorem sinc_sq_tendsto_right :
    Tendsto (fun h : ℝ => Real.sinc (h ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  sinc_sq_tendsto.mono_left inf_le_left

private theorem sinc_sq_tendsto_left :
    Tendsto (fun h : ℝ => Real.sinc (h ^ 2))
      (nhdsWithin 0 (Set.Iio 0)) (nhds 1) :=
  sinc_sq_tendsto.mono_left inf_le_left

private theorem dq_at_sin_zero (a : ℝ) (ha : Real.sin (a ^ 2) = 0) :
    dq f a = fun h => Real.sqrt (Real.sin ((a + h) ^ 2)) / h := by
  funext h
  simp [dq, f, ha]

theorem gap1 (k : ℕ) (x : ℝ)
    (hl : evenRoot k < |x|) (hr : |x| < oddRoot k) :
    HasLeftDerivAt f (x * Real.cos (x ^ 2) / Real.sqrt (Real.sin (x ^ 2))) x ∧
      HasRightDerivAt f
        (x * Real.cos (x ^ 2) / Real.sqrt (Real.sin (x ^ 2))) x := by
  have hs : 0 < Real.sin (x ^ 2) := sin_sq_pos_between k x hl hr
  have hsqrt : Real.sqrt (Real.sin (x ^ 2)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hs)
  have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using (hasDerivAt_id x).pow 2
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (y ^ 2))
      (2 * x * Real.cos (x ^ 2)) x := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_sin (x ^ 2)).comp x hp
  have hd : HasDerivAt f
      (x * Real.cos (x ^ 2) / Real.sqrt (Real.sin (x ^ 2))) x := by
    unfold f
    convert (Real.hasDerivAt_sqrt hs.ne').comp x hsin using 1
    field_simp
  exact hasDerivAt_hasSides hd

theorem gap2 (k : ℕ) (x : ℝ)
    (hl : evenRoot k < |x|) (hr : |x| < oddRoot k) :
    HasLeftDerivAt f
      (x * Real.cos (x ^ 2) / Real.sqrt (Real.sin (x ^ 2))) x := by
  exact (gap1 k x hl hr).1

theorem gap3 (k : ℕ) (x : ℝ)
    (hl : evenRoot k < |x|) (hr : |x| < oddRoot k) :
    HasRightDerivAt f
      (x * Real.cos (x ^ 2) / Real.sqrt (Real.sin (x ^ 2))) x := by
  exact (gap1 k x hl hr).2

theorem gap4 (h : ℝ) (hh : 0 < h) :
    dq f 0 h = Real.sqrt (Real.sin (h ^ 2)) / h := by
  simp [dq, f]

theorem gap5 :
    Tendsto (fun h : ℝ => Real.sqrt (Real.sin (h ^ 2)) / h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsinc : Tendsto (fun h : ℝ => Real.sinc (h ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := sinc_sq_tendsto_right
  have hsqrt : Tendsto (fun h : ℝ => Real.sqrt (Real.sinc (h ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hsinc)
  apply hsqrt.congr'
  have hevent : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < Real.sinc (h ^ 2) :=
    hsinc.eventually (Ioi_mem_nhds zero_lt_one)
  filter_upwards [hevent, self_mem_nhdsWithin] with h hsincpos hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hsinc_eq : Real.sinc (h ^ 2) = Real.sin (h ^ 2) / h ^ 2 := by
    simp [Real.sinc, hh0]
  have hsin : 0 ≤ Real.sin (h ^ 2) := by
    rw [hsinc_eq] at hsincpos
    have hsq : 0 < h ^ 2 := sq_pos_of_ne_zero hh0
    rcases div_pos_iff.mp hsincpos with hcase | hcase
    · exact hcase.1.le
    · exfalso
      exact (not_lt_of_ge hsq.le) hcase.2
  rw [hsinc_eq, Real.sqrt_div hsin, Real.sqrt_sq_eq_abs, abs_of_pos hh]

theorem gap6 :
    HasRightDerivAt f 1 0 := by
  unfold HasRightDerivAt
  apply gap5.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (gap4 h hh).symm

theorem gap7 (h : ℝ) (hh : h < 0) :
    dq f 0 h = -Real.sqrt (Real.sin (h ^ 2) / h ^ 2) := by
  have hf0 : f 0 = 0 := by
    simp [f]
  unfold dq
  rw [hf0, sub_zero, zero_add]
  unfold f
  have hh0 : h ≠ 0 := ne_of_lt hh
  by_cases hs : 0 ≤ Real.sin (h ^ 2)
  · rw [Real.sqrt_div hs, Real.sqrt_sq_eq_abs, abs_of_neg hh]
    field_simp [hh0]
  · have hsin : Real.sin (h ^ 2) ≤ 0 := le_of_not_ge hs
    have hquot : Real.sin (h ^ 2) / h ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hsin (sq_nonneg h)
    rw [Real.sqrt_eq_zero_of_nonpos hsin,
      Real.sqrt_eq_zero_of_nonpos hquot]
    simp

theorem gap8 :
    Tendsto (fun h : ℝ => -Real.sqrt (Real.sin (h ^ 2) / h ^ 2))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (-1)) := by
  have hsinc : Tendsto (fun h : ℝ => Real.sinc (h ^ 2))
      (nhdsWithin 0 (Set.Iio 0)) (nhds 1) := sinc_sq_tendsto_left
  have hsqrt : Tendsto (fun h : ℝ => -Real.sqrt (Real.sinc (h ^ 2)))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (-1)) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hsinc).neg
  apply hsqrt.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_lt hh
  simp [Real.sinc, hh0]

theorem gap9 :
    HasLeftDerivAt f (-1) 0 := by
  unfold HasLeftDerivAt
  apply gap8.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (gap7 h hh).symm

theorem gap10 (k : ℕ) (hk : 0 < k) :
    Tendsto (dq f (evenRoot k)) (nhdsWithin 0 (Set.Ioi 0)) atTop ↔
      Tendsto
        (fun h => Real.sqrt (Real.sin ((evenRoot k + h) ^ 2)) / h)
        (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  rw [dq_at_sin_zero (evenRoot k) (sin_even_root k)]

theorem gap11 (k : ℕ) (hk : 0 < k) :
    Tendsto (fun h => Real.sqrt (Real.sin ((evenRoot k + h) ^ 2)) / h)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  let q : ℝ → ℝ := fun h => Real.sin ((evenRoot k + h) ^ 2)
  have ha : 0 < evenRoot k := by
    rw [evenRoot]
    apply Real.sqrt_pos.2
    positivity
  have hq0 : q 0 = 0 := by
    simp [q, sin_even_root]
  have hqd : HasDerivAt q (2 * evenRoot k) 0 :=
    hasDerivAt_even_root k
  simpa [q] using sqrt_div_right_atTop hq0 hqd (by positivity)

theorem gap12 (k : ℕ) (hk : 0 < k) :
    Tendsto (dq f (evenRoot k)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  exact (gap10 k hk).2 (gap11 k hk)

theorem gap13 (k : ℕ) (hk : 0 < k) :
    Tendsto (dq f (evenRoot k))
      (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
  let q : ℝ → ℝ := fun h => Real.sin ((evenRoot k + h) ^ 2)
  have ha : 0 < evenRoot k := by
    rw [evenRoot]
    apply Real.sqrt_pos.2
    positivity
  have hq0 : q 0 = 0 := by
    simp [q, sin_even_root]
  have hqd : HasDerivAt q (2 * evenRoot k) 0 :=
    hasDerivAt_even_root k
  have ht := sqrt_div_zero_left hq0 hqd (by positivity)
  rw [dq_at_sin_zero (evenRoot k) (sin_even_root k)]
  simpa [q] using ht

theorem gap14 (k : ℕ) :
    Tendsto (dq f (oddRoot k)) (nhdsWithin 0 (Set.Iio 0)) atBot := by
  let q : ℝ → ℝ := fun h => Real.sin ((oddRoot k + h) ^ 2)
  have ha : 0 < oddRoot k := by
    rw [oddRoot]
    apply Real.sqrt_pos.2
    positivity
  have hq0 : q 0 = 0 := by
    simp [q, sin_odd_root]
  have hqd : HasDerivAt q (-(2 * oddRoot k)) 0 :=
    hasDerivAt_odd_root k
  have hc : -(2 * oddRoot k) < 0 := by
    nlinarith
  have ht := sqrt_div_left_atBot hq0 hqd hc
  rw [dq_at_sin_zero (oddRoot k) (sin_odd_root k)]
  simpa [q] using ht

theorem gap15 (k : ℕ) :
    Tendsto (dq f (oddRoot k))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let q : ℝ → ℝ := fun h => Real.sin ((oddRoot k + h) ^ 2)
  have ha : 0 < oddRoot k := by
    rw [oddRoot]
    apply Real.sqrt_pos.2
    positivity
  have hq0 : q 0 = 0 := by
    simp [q, sin_odd_root]
  have hqd : HasDerivAt q (-(2 * oddRoot k)) 0 :=
    hasDerivAt_odd_root k
  have hc : -(2 * oddRoot k) < 0 := by
    nlinarith
  have ht := sqrt_div_zero_right hq0 hqd hc
  rw [dq_at_sin_zero (oddRoot k) (sin_odd_root k)]
  simpa [q] using ht

end

end ProofGap.Exercise1003
