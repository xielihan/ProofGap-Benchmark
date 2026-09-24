import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1779_1

noncomputable section

def sec (t : ℝ) : ℝ := 1 / Real.cos t
def xOf (t : ℝ) : ℝ := Real.sqrt 2 * sec t
def angleDomain : Set ℝ := Set.Ioo 0 (Real.pi / 2)
def integrand (x : ℝ) : ℝ := x ^ 2 / Real.sqrt (x ^ 2 - 2)
def anglePrimitive (t : ℝ) : ℝ :=
  Real.tan t * sec t + Real.log (sec t + Real.tan t)
def primitive (x : ℝ) : ℝ :=
  x / 2 * Real.sqrt (x ^ 2 - 2) +
    Real.log (x + Real.sqrt (x ^ 2 - 2))
def domain : Set ℝ := Set.Ioi (Real.sqrt 2)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (t : ℝ) (ht : t ∈ angleDomain) :
    integrand (xOf t) =
      2 * sec t ^ 2 / (Real.sqrt 2 * Real.tan t) := by
  rcases ht with ⟨ht0, ht1⟩
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi ht0
    nlinarith [Real.pi_pos]
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have htrig := Real.sin_sq_add_cos_sq t
  have hrad : (xOf t) ^ 2 - 2 = 2 * Real.tan t ^ 2 := by
    unfold xOf sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    nlinarith
  have hsqrt : Real.sqrt ((xOf t) ^ 2 - 2) = Real.sqrt 2 * Real.tan t := by
    rw [hrad]
    rw [show 2 * Real.tan t ^ 2 = (Real.sqrt 2 * Real.tan t) ^ 2 by
      rw [mul_pow, hsqrt2sq]]
    exact Real.sqrt_sq (le_of_lt (mul_pos hsqrt2 htan))
  unfold integrand
  rw [hsqrt]
  unfold xOf sec
  field_simp [ne_of_gt hcos, ne_of_gt htan, ne_of_gt hsqrt2]
  exact hsqrt2sq

theorem gap2 (t : ℝ) (ht : t ∈ angleDomain) :
    deriv xOf t = Real.sqrt 2 * sec t * Real.tan t := by
  rcases ht with ⟨ht0, ht1⟩
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hcosne : Real.cos t ≠ 0 := ne_of_gt hcos
  have hsec : HasDerivAt sec (Real.sin t / Real.cos t ^ 2) t := by
    unfold sec
    convert
      (hasDerivAt_const (x := t) (c := (1 : ℝ))).div
        (Real.hasDerivAt_cos t) hcosne using 1 <;> ring
  have hx : HasDerivAt xOf
      (Real.sqrt 2 * (Real.sin t / Real.cos t ^ 2)) t := by
    unfold xOf
    exact hsec.const_mul (Real.sqrt 2)
  rw [hx.deriv]
  unfold sec
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcosne]

theorem gap3 (t : ℝ) (ht : t ∈ angleDomain) :
    integrand (xOf t) * deriv xOf t = 2 * sec t ^ 3 := by
  rcases ht with ⟨ht0, ht1⟩
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi ht0
    nlinarith [Real.pi_pos]
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [gap1 t ⟨ht0, ht1⟩, gap2 t ⟨ht0, ht1⟩]
  unfold sec
  field_simp [ne_of_gt hcos, ne_of_gt htan, ne_of_gt hsqrt2]

theorem gap4 (t : ℝ) (ht : t ∈ angleDomain) :
    sec t ^ 3 =
      deriv Real.sin t / (1 - Real.sin t ^ 2) ^ 2 := by
  rcases ht with ⟨ht0, ht1⟩
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hcosne : Real.cos t ≠ 0 := ne_of_gt hcos
  have htrig := Real.sin_sq_add_cos_sq t
  have hid : 1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by
    nlinarith
  rw [(Real.hasDerivAt_sin t).deriv, hid]
  unfold sec
  field_simp [hcosne]

theorem gap5 (t : ℝ) (ht : t ∈ angleDomain) :
    integrand (xOf t) * deriv xOf t =
      2 * deriv Real.sin t / (1 - Real.sin t ^ 2) ^ 2 := by
  rw [gap3 t ht, gap4 t ht]
  ring

theorem gap6 (t : ℝ) (ht : t ∈ angleDomain) :
    2 / (1 - Real.sin t ^ 2) ^ 2 =
      (1 / 2 : ℝ) *
        (1 / (1 + Real.sin t) + 1 / (1 - Real.sin t)) ^ 2 := by
  rcases ht with ⟨ht0, ht1⟩
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi ht0
    nlinarith [Real.pi_pos]
  have htrig := Real.sin_sq_add_cos_sq t
  have hsinlt : Real.sin t < 1 := by
    nlinarith [sq_pos_of_pos hcos]
  have hp : 0 < 1 + Real.sin t := by linarith
  have hm : 0 < 1 - Real.sin t := by linarith
  have hpne : 1 + Real.sin t ≠ 0 := ne_of_gt hp
  have hmne : 1 - Real.sin t ≠ 0 := ne_of_gt hm
  have hfac : 1 - Real.sin t ^ 2 =
      (1 + Real.sin t) * (1 - Real.sin t) := by ring
  rw [hfac]
  field_simp [hpne, hmne] <;> ring

theorem gap7 (t : ℝ) (ht : t ∈ angleDomain) :
    HasDerivAt
      (fun u =>
        (1 / 2 : ℝ) * (1 / (1 - Real.sin u) - 1 / (1 + Real.sin u)) +
        (1 / 2 : ℝ) * Real.log ((1 + Real.sin u) / (1 - Real.sin u)))
      (integrand (xOf t) * deriv xOf t) t := by
  rcases ht with ⟨ht0, ht1⟩
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi ht0
    nlinarith [Real.pi_pos]
  have htrig := Real.sin_sq_add_cos_sq t
  have hsinlt : Real.sin t < 1 := by
    nlinarith [sq_pos_of_pos hcos]
  have hpne : 1 + Real.sin t ≠ 0 := ne_of_gt (by linarith)
  have hmne : 1 - Real.sin t ≠ 0 := ne_of_gt (by linarith)
  have hsquare_ne : 1 - Real.sin t ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hcos]
  have hsquare2_ne : (1 - Real.sin t ^ 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hsquare_ne
  have hp : HasDerivAt (fun u => 1 + Real.sin u) (Real.cos t) t := by
    convert
      (hasDerivAt_const (x := t) (c := (1 : ℝ))).add
        (Real.hasDerivAt_sin t) using 1 <;> ring
  have hm : HasDerivAt (fun u => 1 - Real.sin u) (-Real.cos t) t := by
    convert
      (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
        (Real.hasDerivAt_sin t) using 1 <;> ring
  have hrm : HasDerivAt (fun u => 1 / (1 - Real.sin u))
      (Real.cos t / (1 - Real.sin t) ^ 2) t := by
    convert
      (hasDerivAt_const (x := t) (c := (1 : ℝ))).div hm hmne using 1 <;> ring
  have hrp : HasDerivAt (fun u => 1 / (1 + Real.sin u))
      (-Real.cos t / (1 + Real.sin t) ^ 2) t := by
    convert
      (hasDerivAt_const (x := t) (c := (1 : ℝ))).div hp hpne using 1 <;> ring
  have hq := hp.div hm hmne
  have hlog := hq.log (div_ne_zero hpne hmne)
  convert
    ((hrm.sub hrp).const_mul (1 / 2 : ℝ)).add
      (hlog.const_mul (1 / 2 : ℝ)) using 1
  rw [gap5 t ⟨ht0, ht1⟩, (Real.hasDerivAt_sin t).deriv]
  dsimp
  field_simp [hpne, hmne, hsquare_ne, hsquare2_ne] <;> ring

theorem gap8 (t : ℝ) (ht : t ∈ angleDomain) :
    (1 / 2 : ℝ) * (1 / (1 - Real.sin t) - 1 / (1 + Real.sin t)) +
        (1 / 2 : ℝ) * Real.log ((1 + Real.sin t) / (1 - Real.sin t)) =
      anglePrimitive t := by
  rcases ht with ⟨ht0, ht1⟩
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi ht0
    nlinarith [Real.pi_pos]
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have htrig := Real.sin_sq_add_cos_sq t
  have hsinlt : Real.sin t < 1 := by
    nlinarith [sq_pos_of_pos hcos]
  have hpne : 1 + Real.sin t ≠ 0 := ne_of_gt (by linarith)
  have hmne : 1 - Real.sin t ≠ 0 := ne_of_gt (by linarith)
  have hcosne : Real.cos t ≠ 0 := ne_of_gt hcos
  have hy : 0 < sec t + Real.tan t := by
    unfold sec
    exact add_pos (one_div_pos.mpr hcos) htan
  have hrat :
      (1 / 2 : ℝ) *
          (1 / (1 - Real.sin t) - 1 / (1 + Real.sin t)) =
        Real.tan t * sec t := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hpne, hmne, hcosne]
    nlinarith
  have hquot :
      (1 + Real.sin t) / (1 - Real.sin t) =
        (sec t + Real.tan t) ^ 2 := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hpne, hmne, hcosne]
    nlinarith
  unfold anglePrimitive
  rw [hrat, hquot, pow_two,
    Real.log_mul (ne_of_gt hy) (ne_of_gt hy)]
  ring

theorem gap9 (t : ℝ) (ht : t ∈ angleDomain) :
    HasDerivAt anglePrimitive
      (integrand (xOf t) * deriv xOf t) t := by
  have h := gap7 t ht
  have heq :
      (fun u =>
        (1 / 2 : ℝ) *
            (1 / (1 - Real.sin u) - 1 / (1 + Real.sin u)) +
          (1 / 2 : ℝ) *
            Real.log ((1 + Real.sin u) / (1 - Real.sin u))) =ᶠ[nhds t]
        anglePrimitive := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact gap8 u hu
  exact h.congr_of_eventuallyEq heq.symm

theorem gap10 (t : ℝ) (ht : t ∈ angleDomain) :
    primitive (xOf t) = anglePrimitive t + Real.log (Real.sqrt 2) := by
  rcases ht with ⟨ht0, ht1⟩
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi ht0
    nlinarith [Real.pi_pos]
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have htrig := Real.sin_sq_add_cos_sq t
  have hrad : (xOf t) ^ 2 - 2 = 2 * Real.tan t ^ 2 := by
    unfold xOf sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    nlinarith
  have hsqrt : Real.sqrt ((xOf t) ^ 2 - 2) = Real.sqrt 2 * Real.tan t := by
    rw [hrad]
    rw [show 2 * Real.tan t ^ 2 = (Real.sqrt 2 * Real.tan t) ^ 2 by
      rw [mul_pow, hsqrt2sq]]
    exact Real.sqrt_sq (le_of_lt (mul_pos hsqrt2 htan))
  have hy : 0 < sec t + Real.tan t := by
    unfold sec
    exact add_pos (one_div_pos.mpr hcos) htan
  have hfirst :
      Real.sqrt 2 * sec t / 2 * (Real.sqrt 2 * Real.tan t) =
        Real.tan t * sec t := by
    calc
      Real.sqrt 2 * sec t / 2 * (Real.sqrt 2 * Real.tan t) =
          ((Real.sqrt 2) ^ 2 / 2) * (Real.tan t * sec t) := by ring
      _ = Real.tan t * sec t := by rw [hsqrt2sq]; ring
  unfold primitive
  rw [hsqrt]
  unfold xOf
  rw [hfirst]
  rw [show Real.sqrt 2 * sec t + Real.sqrt 2 * Real.tan t =
      Real.sqrt 2 * (sec t + Real.tan t) by ring]
  rw [Real.log_mul (ne_of_gt hsqrt2) (ne_of_gt hy)]
  unfold anglePrimitive
  ring

theorem gap11 :
    Family integrand domain = Translates primitive domain := by
  have hprimitive : IsAntiderivativeOn primitive integrand domain := by
    intro x hx
    change Real.sqrt 2 < x at hx
    have hsqrt2nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    have hxpos : 0 < x := lt_trans hsqrt2pos hx
    have hsumpos : 0 < x + Real.sqrt 2 := add_pos hxpos hsqrt2pos
    have hprod :
        0 < (x - Real.sqrt 2) * (x + Real.sqrt 2) :=
      mul_pos (sub_pos.mpr hx) hsumpos
    have hrad : 0 < x ^ 2 - 2 := by
      nlinarith [hprod, hsqrt2sq]
    have hsqrt : 0 < Real.sqrt (x ^ 2 - 2) := Real.sqrt_pos.2 hrad
    have hsqrtne : Real.sqrt (x ^ 2 - 2) ≠ 0 := ne_of_gt hsqrt
    have hadd : 0 < x + Real.sqrt (x ^ 2 - 2) := add_pos hxpos hsqrt
    have hq : HasDerivAt (fun y : ℝ => y ^ 2 - 2) (2 * x) x := by
      convert ((hasDerivAt_id x).pow 2).sub_const 2 using 1 <;>
        simp [id_eq] <;> ring
    have hroot : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 2))
        (x / Real.sqrt (x ^ 2 - 2)) x := by
      convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hq using 1
      field_simp [hsqrtne] <;> ring
    have hhalf : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) x := by
      convert (hasDerivAt_id x).div_const 2 using 1 <;> norm_num
    have hterm : HasDerivAt
        (fun y : ℝ => y / 2 * Real.sqrt (y ^ 2 - 2))
        ((1 / 2 : ℝ) * Real.sqrt (x ^ 2 - 2) +
          x / 2 * (x / Real.sqrt (x ^ 2 - 2))) x :=
      hhalf.mul hroot
    have hsum : HasDerivAt
        (fun y : ℝ => y + Real.sqrt (y ^ 2 - 2))
        (1 + x / Real.sqrt (x ^ 2 - 2)) x :=
      (hasDerivAt_id x).add hroot
    have hlog : HasDerivAt
        (fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 - 2)))
        (1 / Real.sqrt (x ^ 2 - 2)) x := by
      convert hsum.log (ne_of_gt hadd) using 1
      field_simp [hsqrtne, ne_of_gt hadd] <;> ring
    have hsquare : (Real.sqrt (x ^ 2 - 2)) ^ 2 = x ^ 2 - 2 :=
      Real.sq_sqrt (le_of_lt hrad)
    unfold primitive integrand
    convert hterm.add hlog using 1
    field_simp [hsqrtne] <;> nlinarith [hsquare]
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    let D : ℝ → ℝ := fun x => F x - primitive x
    have hD : ∀ x ∈ domain, HasDerivAt D 0 x := by
      intro x hx
      dsimp [D]
      convert (hF x hx).sub (hprimitive x hx) using 1 <;> ring
    let x₀ : ℝ := Real.sqrt 2 + 1
    have hx₀ : x₀ ∈ domain := by
      simp [x₀, domain]
    refine ⟨D x₀, ?_⟩
    intro x hx
    let b : ℝ := max x x₀ + 1
    have hxb : x < b := by
      dsimp [b]
      linarith [le_max_left x x₀]
    have hx₀b : x₀ < b := by
      dsimp [b]
      linarith [le_max_right x x₀]
    have hxI : x ∈ Set.Ioo (Real.sqrt 2) b := ⟨hx, hxb⟩
    have hx₀I : x₀ ∈ Set.Ioo (Real.sqrt 2) b := ⟨hx₀, hx₀b⟩
    have hDdiff : DifferentiableOn ℝ D (Set.Ioo (Real.sqrt 2) b) := by
      intro y hy
      exact (hD y hy.1).differentiableAt.differentiableWithinAt
    have hDzero : ∀ y ∈ Set.Ioo (Real.sqrt 2) b, deriv D y = 0 := by
      intro y hy
      exact (hD y hy.1).deriv
    have heq : D x = D x₀ :=
      (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hDdiff hDzero)
        hxI hx₀I
    dsimp [D] at heq ⊢
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hlocal : ∀ᶠ y in nhds x, y ∈ domain :=
      isOpen_Ioi.mem_nhds hx
    have heq : (fun y => primitive y + C) =ᶠ[nhds x] F := by
      filter_upwards [hlocal] with y hy
      exact (hC y hy).symm
    exact ((hprimitive x hx).add_const C).congr_of_eventuallyEq heq.symm

end

end ProofGap.Exercise1779_1
