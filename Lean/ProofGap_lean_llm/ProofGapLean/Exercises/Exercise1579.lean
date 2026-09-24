import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1579

noncomputable section

def csc (φ : ℝ) : ℝ := 1 / Real.sin φ
def cot (φ : ℝ) : ℝ := Real.cos φ / Real.sin φ
def base (S h φ : ℝ) : ℝ := S / h - h * cot φ
def length (S h φ : ℝ) : ℝ := 2 * h * csc φ + S / h - h * cot φ

def IsMinimizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x₀ ≤ u x

theorem gap1 (S h φ : ℝ) :
    length S h φ = base S h φ + 2 * h * csc φ := by
  unfold length base
  ring

theorem gap2 (S h φ : ℝ) (hh : h ≠ 0) :
    S = (base S h φ + h * cot φ) * h := by
  unfold base
  field_simp [hh]
  <;> ring

theorem gap3 (S h φ : ℝ) :
    (base S h φ + h * cot φ) * h =
      base S h φ * h + h ^ 2 * cot φ := by
  ring

theorem gap4 (S h φ : ℝ) (hh : h ≠ 0) :
    S = base S h φ * h + h ^ 2 * cot φ := by
  calc
    S = (base S h φ + h * cot φ) * h := gap2 S h φ hh
    _ = base S h φ * h + h ^ 2 * cot φ := gap3 S h φ

theorem gap5 (S h φ : ℝ) :
    length S h φ = 2 * h * csc φ + S / h - h * cot φ := by
  rfl

theorem gap6 (S h φ : ℝ) (hsin : Real.sin φ ≠ 0) :
    deriv (length S h) φ =
      (-2 * h * Real.cos φ + h) / Real.sin φ ^ 2 := by
  unfold length csc cot
  have hrecip :
      HasDerivAt (fun x : ℝ => 1 / Real.sin x)
        (-Real.cos φ / Real.sin φ ^ 2) φ := by
    convert (hasDerivAt_const φ (1 : ℝ)).div (Real.hasDerivAt_sin φ) hsin using 1
    <;> ring
  have hquot :
      HasDerivAt (fun x : ℝ => Real.cos x / Real.sin x)
        (-1 / Real.sin φ ^ 2) φ := by
    convert (Real.hasDerivAt_cos φ).div (Real.hasDerivAt_sin φ) hsin using 1
    rw [← Real.sin_sq_add_cos_sq φ]
    ring
  convert (((hrecip.const_mul (2 * h)).add_const (S / h)).sub
    (hquot.const_mul h)).deriv using 1
  <;> ring

theorem gap7 (S h φ : ℝ) (hh : 0 < h) (hφ : φ ∈ Set.Ioo 0 Real.pi)
    (hmin : IsMinimizerOn (length S h) (Set.Ioo 0 Real.pi) φ) :
    (-2 * h * Real.cos φ + h) / Real.sin φ ^ 2 = 0 := by
  have hs : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hlocal : IsLocalMin (length S h) φ := by
    filter_upwards [isOpen_Ioo.mem_nhds hφ] with x hx
    exact hmin.2 x hx
  have hzero : deriv (length S h) φ = 0 := hlocal.deriv_eq_zero
  rw [gap6 S h φ hs.ne'] at hzero
  exact hzero

theorem gap8 (S h φ : ℝ) (hh : 0 < h) (hφ : φ ∈ Set.Ioo 0 Real.pi)
    (hmin : IsMinimizerOn (length S h) (Set.Ioo 0 Real.pi) φ) :
    deriv (length S h) φ = 0 := by
  have hs : Real.sin φ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2).ne'
  rw [gap6 S h φ hs]
  exact gap7 S h φ hh hφ hmin

theorem gap9 (S h φ : ℝ) (hh : 0 < h) (hφ : φ ∈ Set.Ioo 0 Real.pi)
    (hcrit : deriv (length S h) φ = 0) :
    Real.cos φ = 1 / 2 := by
  have hs : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  rw [gap6 S h φ hs.ne'] at hcrit
  field_simp [hs.ne'] at hcrit
  nlinarith

theorem gap10 (S h φ : ℝ) (hh : 0 < h) (hφ : φ ∈ Set.Ioo 0 Real.pi)
    (hcrit : Real.cos φ = 1 / 2) :
    φ = Real.pi / 3 := by
  apply Real.strictAntiOn_cos.injOn
  · exact ⟨hφ.1.le, hφ.2.le⟩
  · constructor
    · nlinarith [Real.pi_gt_three]
    · nlinarith [Real.pi_gt_three]
  · simpa [Real.cos_pi_div_three] using hcrit

theorem gap11 (S h : ℝ) (hh : 0 < h) :
    deriv (deriv (length S h)) (Real.pi / 3) =
      4 * h / Real.sqrt 3 := by
  have hx0 : 0 < Real.pi / 3 := by
    nlinarith [Real.pi_gt_three]
  have hxpi : Real.pi / 3 < Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsin0 : Real.sin (Real.pi / 3) ≠ 0 := by
    rw [Real.sin_pi_div_three]
    exact div_ne_zero hsqrt.ne' (by norm_num)
  have heq :
      Filter.EventuallyEq (nhds (Real.pi / 3))
        (deriv (length S h))
        (fun x : ℝ => (-2 * h * Real.cos x + h) / Real.sin x ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hx0, hxpi⟩] with x hx
    rcases hx with ⟨hx0', hxpi'⟩
    exact gap6 S h x
      (Real.sin_pos_of_pos_of_lt_pi hx0' hxpi').ne'
  have hn :
      HasDerivAt (fun x : ℝ => -2 * h * Real.cos x + h)
        (2 * h * Real.sin (Real.pi / 3)) (Real.pi / 3) := by
    convert ((Real.hasDerivAt_cos (Real.pi / 3)).const_mul
      (-2 * h)).add_const h using 1
    <;> ring
  have hd :
      HasDerivAt (fun x : ℝ => Real.sin x ^ 2)
        (2 * Real.sin (Real.pi / 3) * Real.cos (Real.pi / 3))
        (Real.pi / 3) := by
    convert (Real.hasDerivAt_sin (Real.pi / 3)).pow 2 using 1
    <;> ring
  have hden : Real.sin (Real.pi / 3) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hsin0
  have hg :
      deriv (fun x : ℝ =>
        (-2 * h * Real.cos x + h) / Real.sin x ^ 2)
        (Real.pi / 3) = 4 * h / Real.sqrt 3 := by
    convert (hn.div hd hden).deriv using 1
    rw [Real.sin_pi_div_three, Real.cos_pi_div_three]
    field_simp [hsqrt.ne']
    nlinarith [hsqrt_sq]
  calc
    deriv (deriv (length S h)) (Real.pi / 3) =
        deriv (fun x : ℝ =>
          (-2 * h * Real.cos x + h) / Real.sin x ^ 2)
          (Real.pi / 3) := heq.deriv_eq
    _ = 4 * h / Real.sqrt 3 := hg

theorem gap12 (h : ℝ) (hh : 0 < h) :
    0 < 4 * h / Real.sqrt 3 := by
  exact div_pos (mul_pos (by norm_num) hh)
    (Real.sqrt_pos.2 (by norm_num))

theorem gap13 (S h : ℝ) (hh : 0 < h) :
    0 < deriv (deriv (length S h)) (Real.pi / 3) := by
  rw [gap11 S h hh]
  exact gap12 h hh

theorem gap14 (S h : ℝ) (hh : 0 < h) :
    IsMinimizerOn (length S h) (Set.Ioo 0 Real.pi) (Real.pi / 3) := by
  have hx0 : 0 < Real.pi / 3 := by
    nlinarith [Real.pi_gt_three]
  have hxpi : Real.pi / 3 < Real.pi := by
    nlinarith [Real.pi_gt_three]
  refine ⟨⟨hx0, hxpi⟩, ?_⟩
  intro x hx
  have hs : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsq :
      (Real.sqrt 3 * Real.sin x) ^ 2 ≤
        (2 - Real.cos x) ^ 2 := by
    calc
      (Real.sqrt 3 * Real.sin x) ^ 2 =
          3 * Real.sin x ^ 2 := by
            rw [mul_pow, hsqrt_sq]
      _ ≤ (2 - Real.cos x) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x,
          sq_nonneg (2 * Real.cos x - 1)]
  have hApos : 0 < 2 - Real.cos x := by
    nlinarith [Real.cos_le_one x]
  have hBnonneg : 0 ≤ Real.sqrt 3 * Real.sin x :=
    mul_nonneg hsqrt.le hs.le
  have hroot :
      Real.sqrt 3 * Real.sin x ≤ 2 - Real.cos x := by
    by_contra hn
    have hlt : 2 - Real.cos x < Real.sqrt 3 * Real.sin x :=
      lt_of_not_ge hn
    have hprod :
        0 < (Real.sqrt 3 * Real.sin x - (2 - Real.cos x)) *
          (Real.sqrt 3 * Real.sin x + (2 - Real.cos x)) :=
      mul_pos (sub_pos.mpr hlt)
        (add_pos_of_nonneg_of_pos hBnonneg hApos)
    nlinarith
  have hratio :
      Real.sqrt 3 ≤ (2 - Real.cos x) / Real.sin x :=
    (le_div_iff₀ hs).2 hroot
  have hspecial :
      length S h (Real.pi / 3) = S / h + h * Real.sqrt 3 := by
    unfold length csc cot
    rw [Real.sin_pi_div_three, Real.cos_pi_div_three]
    field_simp [hh.ne', hsqrt.ne']
    nlinarith [hsqrt_sq]
  have hxform :
      length S h x =
        S / h + h * ((2 - Real.cos x) / Real.sin x) := by
    unfold length csc cot
    field_simp [hh.ne', hs.ne']
    <;> ring
  rw [hspecial, hxform]
  simpa [add_comm] using
    (add_le_add_left
      (mul_le_mul_of_nonneg_left hratio hh.le) (S / h))

end

end ProofGap.Exercise1579
