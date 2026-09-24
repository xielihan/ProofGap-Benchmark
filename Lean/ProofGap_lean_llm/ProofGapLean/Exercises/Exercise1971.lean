import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1971

noncomputable section

def branch : Set ℝ := {x | 1 < |x|}
def negativeBranch : Set ℝ := {x | x < -1}
def positiveBranch : Set ℝ := {x | 1 < x}
def originalIntegrand (x : ℝ) :=
  1 / (Real.sqrt (x ^ 2 + 1) - Real.sqrt (x ^ 2 - 1))
def rationalizedIntegrand (x : ℝ) :=
  (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1)) /
    ((x ^ 2 + 1) - (x ^ 2 - 1))
def firstPart (x : ℝ) := Real.sqrt (x ^ 2 + 1)
def secondPart (x : ℝ) := Real.sqrt (x ^ 2 - 1)
def primitive (x : ℝ) :=
  x / 4 * (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1)) +
    1 / 4 *
      Real.log
        |(x + Real.sqrt (x ^ 2 + 1)) /
          (x + Real.sqrt (x ^ 2 - 1))|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn firstPart,
    ∃ H ∈ AntiderivativesOn secondPart,
      ∀ x ∈ branch, F x = 1 / 2 * G x + 1 / 2 * H x}
def BranchwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ Cneg Cpos : ℝ,
    (∀ x ∈ negativeBranch, F x = primitive x + Cneg) ∧
    (∀ x ∈ positiveBranch, F x = primitive x + Cpos)}

private theorem branch_open : IsOpen branch := by
  change IsOpen {x : ℝ | 1 < |x|}
  exact isOpen_Ioi.preimage continuous_abs

private theorem negativeBranch_open : IsOpen negativeBranch := by
  change IsOpen {x : ℝ | x < -1}
  exact isOpen_Iio

private theorem positiveBranch_open : IsOpen positiveBranch := by
  change IsOpen {x : ℝ | 1 < x}
  exact isOpen_Ioi

private theorem positive_mem_branch {x : ℝ} (hx : 1 < x) : x ∈ branch := by
  change 1 < |x|
  rw [abs_of_pos (lt_trans (by norm_num) hx)]
  exact hx

private theorem negative_mem_branch {x : ℝ} (hx : x < -1) : x ∈ branch := by
  change 1 < |x|
  rw [abs_of_neg (lt_trans hx (by norm_num))]
  linarith

private theorem branch_cases {x : ℝ} (hx : x ∈ branch) : x ∈ negativeBranch ∨ x ∈ positiveBranch := by
  change 1 < |x| at hx
  by_cases h : 0 ≤ x
  · right
    change 1 < x
    simpa [abs_of_nonneg h] using hx
  · left
    change x < -1
    rw [abs_of_neg (lt_of_not_ge h)] at hx
    linarith

private theorem hasDerivAt_congr_on_open {s : Set ℝ} (hs : IsOpen s)
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ s)
    (hfg : ∀ y ∈ s, f y = g y) (hg : HasDerivAt g f' x) :
    HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with y hy
  exact hfg y hy

private theorem branch_square_gt_one {x : ℝ} (hx : x ∈ branch) : 1 < x ^ 2 := by
  change 1 < |x| at hx
  rw [← sq_abs]
  nlinarith [sq_nonneg (|x| - 1)]

private theorem integrands_agree {x : ℝ} (hx : x ∈ branch) :
    originalIntegrand x = rationalizedIntegrand x := by
  have hx2 : 1 < x ^ 2 := branch_square_gt_one hx
  have hp : 0 ≤ x ^ 2 + 1 := by positivity
  have hm : 0 ≤ x ^ 2 - 1 := by linarith
  have hsp := Real.sq_sqrt hp
  have hsm := Real.sq_sqrt hm
  have hne : Real.sqrt (x ^ 2 + 1) - Real.sqrt (x ^ 2 - 1) ≠ 0 := by
    intro h
    have heq : Real.sqrt (x ^ 2 + 1) = Real.sqrt (x ^ 2 - 1) := sub_eq_zero.mp h
    rw [heq] at hsp
    nlinarith [hsp, hsm]
  unfold originalIntegrand rationalizedIntegrand
  field_simp [hne]
  nlinarith [hsp, hsm]

private theorem rationalized_split (x : ℝ) :
    rationalizedIntegrand x = 1 / 2 * firstPart x + 1 / 2 * secondPart x := by
  unfold rationalizedIntegrand firstPart secondPart
  ring

private def firstPrimitiveAux (x : ℝ) :=
  x / 2 * Real.sqrt (x ^ 2 + 1) +
    1 / 2 * Real.log |x + Real.sqrt (x ^ 2 + 1)|

private def secondPrimitiveAux (x : ℝ) :=
  x / 2 * Real.sqrt (x ^ 2 - 1) -
    1 / 2 * Real.log |x + Real.sqrt (x ^ 2 - 1)|

private theorem hasDerivAt_sqrt_quadratic (x c : ℝ) (h : 0 < x ^ 2 + c) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + c))
      (x / Real.sqrt (x ^ 2 + c)) x := by
  have hpoly : HasDerivAt (fun y : ℝ => y ^ 2 + c) (2 * x) x := by
    convert (((hasDerivAt_id x).pow 2).add_const c) using 1 <;>
      simp [id, mul_comm]
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt h)).comp x hpoly
  have hs0 : Real.sqrt (x ^ 2 + c) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h)
  convert hs using 1
  dsimp only [id]
  field_simp [hs0]

private theorem hasDerivAt_log_abs {u : ℝ → ℝ} {u' x : ℝ}
    (hu : HasDerivAt u u' x) (hne : u x ≠ 0) :
    HasDerivAt (fun y => Real.log |u y|) (u' / u x) x := by
  have h := (Real.hasDerivAt_log hne).comp x hu
  simpa [Real.log_abs, div_eq_mul_inv, mul_comm] using h

private theorem firstPrimitiveAux_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt firstPrimitiveAux (firstPart x) x := by
  have ha : 0 < x ^ 2 + 1 := by positivity
  have hsa : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.2 ha
  have hs := hasDerivAt_sqrt_quadratic x 1 ha
  have hu := (hasDerivAt_id x).add hs
  have hu0 : x + Real.sqrt (x ^ 2 + 1) ≠ 0 := by
    intro hzero
    have hsquare := Real.sq_sqrt (le_of_lt ha)
    have heq : Real.sqrt (x ^ 2 + 1) = -x := by linarith
    rw [heq] at hsquare
    nlinarith
  have hl := hasDerivAt_log_abs hu hu0
  have hratio :
      (1 + x / Real.sqrt (x ^ 2 + 1)) /
          (x + Real.sqrt (x ^ 2 + 1)) =
        1 / Real.sqrt (x ^ 2 + 1) := by
    field_simp [ne_of_gt hsa, hu0]
    <;> ring
  have hsquare := Real.sq_sqrt (le_of_lt ha)
  have hd :=
    (((hasDerivAt_id x).div_const 2).mul hs).add
      ((hasDerivAt_const x (1 / 2 : ℝ)).mul hl)
  unfold firstPrimitiveAux firstPart
  convert hd using 1
  simp only [Pi.add_apply, id, zero_mul, zero_add]
  rw [hratio]
  field_simp [ne_of_gt hsa]
  nlinarith [hsquare]

private theorem secondPrimitiveAux_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt secondPrimitiveAux (secondPart x) x := by
  have hx2 : 1 < x ^ 2 := branch_square_gt_one hx
  have hb : 0 < x ^ 2 - 1 := by linarith
  have hsb : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 hb
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
      (x / Real.sqrt (x ^ 2 - 1)) x := by
    simpa [sub_eq_add_neg] using hasDerivAt_sqrt_quadratic x (-1) hb
  have hu := (hasDerivAt_id x).add hs
  have hu0 : x + Real.sqrt (x ^ 2 - 1) ≠ 0 := by
    intro hzero
    have hsquare := Real.sq_sqrt (le_of_lt hb)
    have heq : Real.sqrt (x ^ 2 - 1) = -x := by linarith
    rw [heq] at hsquare
    nlinarith
  have hl := hasDerivAt_log_abs hu hu0
  have hratio :
      (1 + x / Real.sqrt (x ^ 2 - 1)) /
          (x + Real.sqrt (x ^ 2 - 1)) =
        1 / Real.sqrt (x ^ 2 - 1) := by
    field_simp [ne_of_gt hsb, hu0]
    <;> ring
  have hsquare := Real.sq_sqrt (le_of_lt hb)
  have hd :=
    (((hasDerivAt_id x).div_const 2).mul hs).sub
      ((hasDerivAt_const x (1 / 2 : ℝ)).mul hl)
  unfold secondPrimitiveAux secondPart
  convert hd using 1
  simp only [Pi.add_apply, id, zero_mul, zero_add]
  rw [hratio]
  field_simp [ne_of_gt hsb]
  nlinarith [hsquare]

private theorem firstPrimitiveAux_mem :
    firstPrimitiveAux ∈ AntiderivativesOn firstPart := by
  intro x hx
  exact firstPrimitiveAux_deriv x hx

private theorem primitive_split_aux {x : ℝ} (hx : x ∈ branch) :
    primitive x = 1 / 2 * firstPrimitiveAux x + 1 / 2 * secondPrimitiveAux x := by
  have hx2 : 1 < x ^ 2 := branch_square_gt_one hx
  have ha : 0 < x ^ 2 + 1 := by positivity
  have hb : 0 < x ^ 2 - 1 := by linarith
  have hua : x + Real.sqrt (x ^ 2 + 1) ≠ 0 := by
    intro hzero
    have hsquare := Real.sq_sqrt (le_of_lt ha)
    have heq : Real.sqrt (x ^ 2 + 1) = -x := by linarith
    rw [heq] at hsquare
    nlinarith
  have hub : x + Real.sqrt (x ^ 2 - 1) ≠ 0 := by
    intro hzero
    have hsquare := Real.sq_sqrt (le_of_lt hb)
    have heq : Real.sqrt (x ^ 2 - 1) = -x := by linarith
    rw [heq] at hsquare
    nlinarith
  unfold primitive firstPrimitiveAux secondPrimitiveAux
  rw [Real.log_abs, Real.log_div hua hub, Real.log_abs, Real.log_abs]
  ring

private theorem primitive_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (originalIntegrand x) x := by
  have hd :=
    ((hasDerivAt_const x (1 / 2 : ℝ)).mul (firstPrimitiveAux_deriv x hx)).add
      ((hasDerivAt_const x (1 / 2 : ℝ)).mul (secondPrimitiveAux_deriv x hx))
  have hd' : HasDerivAt
      (fun y => 1 / 2 * firstPrimitiveAux y + 1 / 2 * secondPrimitiveAux y)
      (originalIntegrand x) x := by
    convert hd using 1
    simp only [zero_mul, zero_add]
    rw [integrands_agree hx, rationalized_split]
  exact hasDerivAt_congr_on_open branch_open hx
    (fun y hy => primitive_split_aux hy) hd'

private theorem eq_of_lt_of_hasDerivAt_zero {f : ℝ → ℝ} {x y : ℝ}
    (hxy : x < y) (hseg : ∀ z ∈ Set.Icc x y, HasDerivAt f 0 z) :
    f x = f y := by
  have hcont : ContinuousOn f (Set.Icc x y) := by
    intro z hz
    exact (hseg z hz).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo x y) := by
    intro z hz
    exact (hseg z ⟨le_of_lt hz.1, le_of_lt hz.2⟩).differentiableAt.differentiableWithinAt
  obtain ⟨z, hz, hslope⟩ := exists_deriv_eq_slope f hxy hcont hdiff
  have hdz : deriv f z = 0 :=
    (hseg z ⟨le_of_lt hz.1, le_of_lt hz.2⟩).deriv
  have hq : (f y - f x) / (y - x) = 0 := by
    rw [← hslope, hdz]
  have hnum : f y - f x = 0 := by
    calc
      f y - f x = ((f y - f x) / (y - x)) * (y - x) := by
        field_simp [ne_of_gt (sub_pos.mpr hxy)]
      _ = 0 := by rw [hq, zero_mul]
  linarith

private theorem const_on_Ioi_of_hasDerivAt_zero {f : ℝ → ℝ} {a : ℝ}
    (h : ∀ z, a < z → HasDerivAt f 0 z) :
    ∀ {x y}, a < x → a < y → f x = f y := by
  intro x y hx hy
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact eq_of_lt_of_hasDerivAt_zero hxy
      (fun z hz => h z (lt_of_lt_of_le hx hz.1))
  · simpa [hxy]
  · exact (eq_of_lt_of_hasDerivAt_zero hxy
      (fun z hz => h z (lt_of_lt_of_le hy hz.1))).symm

private theorem const_on_Iio_of_hasDerivAt_zero {f : ℝ → ℝ} {a : ℝ}
    (h : ∀ z, z < a → HasDerivAt f 0 z) :
    ∀ {x y}, x < a → y < a → f x = f y := by
  intro x y hx hy
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact eq_of_lt_of_hasDerivAt_zero hxy
      (fun z hz => h z (lt_of_le_of_lt hz.2 hy))
  · simpa [hxy]
  · exact (eq_of_lt_of_hasDerivAt_zero hxy
      (fun z hz => h z (lt_of_le_of_lt hz.2 hx))).symm

theorem gap1 :
    AntiderivativesOn originalIntegrand =
      AntiderivativesOn rationalizedIntegrand := by
  apply Set.ext
  intro F
  constructor
  · intro hF x hx
    simpa [integrands_agree hx] using hF x hx
  · intro hF x hx
    simpa [integrands_agree hx] using hF x hx
theorem gap2 :
    AntiderivativesOn rationalizedIntegrand = SplitFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨firstPrimitiveAux, firstPrimitiveAux_mem, fun y => 2 * F y - firstPrimitiveAux y, ?_, ?_⟩
    · intro x hx
      have hd := ((hasDerivAt_const x (2 : ℝ)).mul (hF x hx)).sub
        (firstPrimitiveAux_deriv x hx)
      convert hd using 1
      simp only [zero_mul, zero_add]
      rw [rationalized_split]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, H, hH, hF⟩
    intro x hx
    have hd :=
      ((hasDerivAt_const x (1 / 2 : ℝ)).mul (hG x hx)).add
        ((hasDerivAt_const x (1 / 2 : ℝ)).mul (hH x hx))
    have hd' : HasDerivAt (fun y => 1 / 2 * G y + 1 / 2 * H y)
        (rationalizedIntegrand x) x := by
      convert hd using 1
      simp only [zero_mul, zero_add]
      rw [rationalized_split]
    exact hasDerivAt_congr_on_open branch_open hx
      (fun y hy => hF y hy) hd'
theorem gap3 :
    AntiderivativesOn originalIntegrand = SplitFamily := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn originalIntegrand = BranchwisePrimitiveFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hDneg : ∀ y, y < -1 → HasDerivAt D 0 y := by
      intro y hy
      have hyb : y ∈ branch := negative_mem_branch hy
      simpa [D] using (hF y hyb).sub (primitive_deriv y hyb)
    have hDpos : ∀ y, 1 < y → HasDerivAt D 0 y := by
      intro y hy
      have hyb : y ∈ branch := positive_mem_branch hy
      simpa [D] using (hF y hyb).sub (primitive_deriv y hyb)
    refine ⟨D (-2), D 2, ?_, ?_⟩
    · intro x hx
      have hc : D x = D (-2) :=
        const_on_Iio_of_hasDerivAt_zero hDneg hx (by norm_num)
      change F x = primitive x + D (-2)
      dsimp [D] at hc ⊢
      linarith
    · intro x hx
      have hc : D x = D 2 :=
        const_on_Ioi_of_hasDerivAt_zero hDpos hx (by norm_num)
      change F x = primitive x + D 2
      dsimp [D] at hc ⊢
      linarith
  · rintro ⟨Cneg, Cpos, hneg, hpos⟩
    intro x hx
    rcases branch_cases hx with hxneg | hxpos
    · have hd : HasDerivAt (fun y => primitive y + Cneg)
          (originalIntegrand x) x :=
        (primitive_deriv x hx).add_const Cneg
      exact hasDerivAt_congr_on_open negativeBranch_open hxneg
        (fun y hy => hneg y hy) hd
    · have hd : HasDerivAt (fun y => primitive y + Cpos)
          (originalIntegrand x) x :=
        (primitive_deriv x hx).add_const Cpos
      exact hasDerivAt_congr_on_open positiveBranch_open hxpos
        (fun y hy => hpos y hy) hd

end
end ProofGap.Exercise1971
