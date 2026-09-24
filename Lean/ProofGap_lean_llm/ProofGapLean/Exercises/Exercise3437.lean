import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise3437

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

def dydx (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 y t / d1 x t

def d2ydx2 (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  (d2 y t * d1 x t - d1 y t * d2 x t) / (d1 x t) ^ 3

def regular (t : ℝ) : Prop :=
  0 < Real.tan (t / 2)

private lemma half_cos_ne_zero (t : ℝ) (ht : regular t) :
    Real.cos (t / 2) ≠ 0 := by
  have htan : Real.tan (t / 2) ≠ 0 := ne_of_gt ht
  intro hc
  apply htan
  simp [Real.tan_eq_sin_div_cos, hc]

private lemma half_sin_ne_zero (t : ℝ) (ht : regular t) :
    Real.sin (t / 2) ≠ 0 := by
  have htan : Real.tan (t / 2) ≠ 0 := ne_of_gt ht
  intro hs
  apply htan
  simp [Real.tan_eq_sin_div_cos, hs]

private lemma sin_ne_zero_of_regular (t : ℝ) (ht : regular t) :
    Real.sin t ≠ 0 := by
  rw [show t = 2 * (t / 2) by ring, Real.sin_two_mul]
  exact mul_ne_zero
    (mul_ne_zero two_ne_zero (half_sin_ne_zero t ht))
    (half_cos_ne_zero t ht)

private lemma regular_eventually (t : ℝ) (ht : regular t) :
    ∀ᶠ s in nhds t, regular s := by
  have hhalf : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have htan :=
    (Real.hasDerivAt_tan (half_cos_ne_zero t ht)).comp t hhalf
  have ht' : 0 < Real.tan (t / 2) := ht
  have hpos :
      Set.Ioi (0 : ℝ) ∈ nhds (Real.tan (t / 2)) :=
    isOpen_Ioi.mem_nhds ht'
  simpa [regular, Function.comp_def] using
    htan.continuousAt hpos

theorem gap1 (x : ℝ → ℝ)
    (hParam : ∀ t, x t = Real.log (Real.tan (t / 2))) :
    ∀ t, regular t → d1 x t = 1 / Real.sin t := by
  intro t ht
  have hhalf : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have htan :=
    (Real.hasDerivAt_tan (half_cos_ne_zero t ht)).comp t hhalf
  have hlog :=
    (Real.hasDerivAt_log (ne_of_gt ht)).comp t htan
  unfold d1
  rw [funext hParam]
  calc
    deriv (fun s : ℝ => Real.log (Real.tan (s / 2))) t = _ := hlog.deriv
    _ = 1 / Real.sin t := by
      rw [show t = 2 * (t / 2) by ring, Real.sin_two_mul,
        Real.tan_eq_sin_div_cos]
      field_simp [half_sin_ne_zero t ht, half_cos_ne_zero t ht]
      <;> ring

theorem gap2 (x : ℝ → ℝ)
    (hParam : ∀ t, x t = Real.log (Real.tan (t / 2)))
    (hFirst : ∀ t, regular t → d1 x t = 1 / Real.sin t) :
    ∀ t, regular t →
      d2 x t = -Real.cos t / (Real.sin t) ^ 2 := by
  intro t ht
  have heq :
      deriv x =ᶠ[nhds t] (fun s : ℝ => 1 / Real.sin s) :=
    (regular_eventually t ht).mono (fun s hs => by
      simpa [d1] using hFirst s hs)
  have hd :
      HasDerivAt (fun s : ℝ => 1 / Real.sin s)
        (-Real.cos t / (Real.sin t) ^ 2) t := by
    simpa [one_div] using
      (Real.hasDerivAt_sin t).inv (sin_ne_zero_of_regular t ht)
  unfold d2
  calc
    deriv (deriv x) t = deriv (fun s : ℝ => 1 / Real.sin s) t := heq.deriv_eq
    _ = -Real.cos t / (Real.sin t) ^ 2 := hd.deriv

theorem gap3 (x : ℝ → ℝ)
    (hParam : ∀ t, x t = Real.log (Real.tan (t / 2))) :
    ∀ t, regular t →
      Real.cosh (x t) = 1 / Real.sin t := by
  intro t ht
  have hz : 0 < Real.tan (t / 2) := ht
  have hcoshlog :
      Real.cosh (Real.log (Real.tan (t / 2))) =
        (Real.tan (t / 2) + (Real.tan (t / 2))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_log hz, Real.exp_neg, Real.exp_log hz]
  rw [hParam t, hcoshlog]
  rw [show t = 2 * (t / 2) by ring, Real.sin_two_mul,
    Real.tan_eq_sin_div_cos]
  field_simp [half_sin_ne_zero t ht, half_cos_ne_zero t ht]
  <;> nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

theorem gap4 (x : ℝ → ℝ)
    (hParam : ∀ t, x t = Real.log (Real.tan (t / 2))) :
    ∀ t, regular t →
      Real.tanh (x t) = -Real.cos t := by
  intro t ht
  have hz : 0 < Real.tan (t / 2) := ht
  have hsum :
      0 < Real.tan (t / 2) + (Real.tan (t / 2))⁻¹ :=
    add_pos hz (inv_pos.mpr hz)
  have htanhlog :
      Real.tanh (Real.log (Real.tan (t / 2))) =
        (Real.tan (t / 2) - (Real.tan (t / 2))⁻¹) /
          (Real.tan (t / 2) + (Real.tan (t / 2))⁻¹) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    simp only [Real.exp_neg, Real.exp_log hz]
    field_simp [ne_of_gt hz, ne_of_gt hsum]
    <;> ring
  rw [hParam t, htanhlog]
  rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul,
    Real.tan_eq_sin_div_cos]
  field_simp [half_sin_ne_zero t ht, half_cos_ne_zero t ht]
  <;> nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

theorem gap5 (x y : ℝ → ℝ)
    (hFirst : ∀ t, regular t → d1 x t = 1 / Real.sin t) :
    ∀ t, regular t →
      dydx x y t = Real.sin t * d1 y t := by
  intro t ht
  have hs := sin_ne_zero_of_regular t ht
  rw [dydx, hFirst t ht]
  field_simp [hs]
  <;> ring

theorem gap6 (x y : ℝ → ℝ)
    (hFirst :
      ∀ t, regular t → d1 x t = 1 / Real.sin t)
    (hSecond :
      ∀ t, regular t →
        d2 x t = -Real.cos t / (Real.sin t) ^ 2) :
    ∀ t, regular t →
      d2ydx2 x y t =
        (Real.sin t) ^ 2 * d2 y t +
          Real.sin t * Real.cos t * d1 y t := by
  intro t ht
  have hs := sin_ne_zero_of_regular t ht
  rw [d2ydx2, hFirst t ht, hSecond t ht]
  field_simp [hs]
  <;> ring

theorem gap7 (m : ℝ) (x y : ℝ → ℝ)
    (hODE :
      ∀ t, regular t →
        d2ydx2 x y t +
            dydx x y t * Real.tanh (x t) +
            m ^ 2 / (Real.cosh (x t)) ^ 2 * y t =
          0)
    (hCosh :
      ∀ t, regular t →
        Real.cosh (x t) = 1 / Real.sin t)
    (hTanh :
      ∀ t, regular t →
        Real.tanh (x t) = -Real.cos t)
    (hFirst :
      ∀ t, regular t →
        dydx x y t = Real.sin t * d1 y t)
    (hSecond :
      ∀ t, regular t →
        d2ydx2 x y t =
          (Real.sin t) ^ 2 * d2 y t +
            Real.sin t * Real.cos t * d1 y t) :
    ∀ t, regular t →
      d2 y t + m ^ 2 * y t = 0 := by
  intro t ht
  have hs := sin_ne_zero_of_regular t ht
  have hscaled :
      (Real.sin t) ^ 2 * (d2 y t + m ^ 2 * y t) = 0 := by
    calc
      (Real.sin t) ^ 2 * (d2 y t + m ^ 2 * y t) =
          d2ydx2 x y t +
            dydx x y t * Real.tanh (x t) +
            m ^ 2 / (Real.cosh (x t)) ^ 2 * y t := by
              rw [hSecond t ht, hFirst t ht, hTanh t ht, hCosh t ht]
              field_simp [hs]
              <;> ring
      _ = 0 := hODE t ht
  rcases mul_eq_zero.mp hscaled with hzero | hresult
  · exact (pow_ne_zero 2 hs hzero).elim
  · exact hresult

end

end ProofGap.Exercise3437
