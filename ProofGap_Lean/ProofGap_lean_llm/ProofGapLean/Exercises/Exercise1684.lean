import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1684

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (Real.sqrt (x ^ 2 + 1)) ^ 3
def auxiliary (x : ℝ) : ℝ := 1 + 1 / x ^ 2
def intermediate (x : ℝ) : ℝ := Real.sign x / Real.sqrt (auxiliary x)
def primitive (x : ℝ) : ℝ := x / Real.sqrt (x ^ 2 + 1)
def punctured : Set ℝ := {x | x ≠ 0}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hu : 0 < x ^ 2 + 1 := by positivity
  have hroot : Real.sqrt (x ^ 2 + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu)
  have hsquare : (Real.sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 :=
    Real.sq_sqrt (le_of_lt hu)
  have hi :
      HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const 1 using 1 <;> norm_num <;> ring
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x hi
  unfold primitive
  convert (hasDerivAt_id x).div hs hroot using 1
  unfold integrand
  dsimp
  field_simp [hroot]
  rw [hsquare]
  ring

private theorem intermediate_eq_primitive_of_ne (x : ℝ) (hx : x ∈ punctured) :
    intermediate x = primitive x := by
  have hx0 : x ≠ 0 := by simpa [punctured] using hx
  have hu : 0 ≤ x ^ 2 + 1 := by positivity
  have hroot : Real.sqrt (x ^ 2 + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hquot : 1 + 1 / x ^ 2 = (x ^ 2 + 1) / x ^ 2 := by
    field_simp [hx0]
  have hsqrt :
      Real.sqrt (auxiliary x) = Real.sqrt (x ^ 2 + 1) / |x| := by
    unfold auxiliary
    rw [hquot, Real.sqrt_div hu, Real.sqrt_sq_eq_abs]
  rw [intermediate, primitive, hsqrt]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
    field_simp [hx0, hroot]
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
    field_simp [hx0, hroot]

private theorem values_eq_of_hasDerivAt_zero
    (f : ℝ → ℝ) (h : ∀ x, HasDerivAt f 0 x) (x y : ℝ) : f x = f y := by
  have hdiff : Differentiable ℝ f := fun z => (h z).differentiableAt
  have hderiv : ∀ z, deriv f z = 0 := fun z => (h z).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv x y

theorem gap1 (x : ℝ) (hx : x ∈ punctured) :
    integrand x =
      Real.sign x / (x ^ 3 * (Real.sqrt (auxiliary x)) ^ 3) := by
  have hx0 : x ≠ 0 := by simpa [punctured] using hx
  have hu : 0 ≤ x ^ 2 + 1 := by positivity
  have hroot : Real.sqrt (x ^ 2 + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hquot : 1 + 1 / x ^ 2 = (x ^ 2 + 1) / x ^ 2 := by
    field_simp [hx0]
  have hsqrt :
      Real.sqrt (auxiliary x) = Real.sqrt (x ^ 2 + 1) / |x| := by
    unfold auxiliary
    rw [hquot, Real.sqrt_div hu, Real.sqrt_sq_eq_abs]
  unfold integrand
  rw [hsqrt]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
    field_simp [hx0, hroot]
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
    field_simp [hx0, hroot]

theorem gap2 (x : ℝ) (hx : x ∈ punctured) :
    integrand x =
      -(1 / 2 : ℝ) * (auxiliary x) ^ (-3 / 2 : ℝ) *
        Real.sign x * deriv auxiliary x := by
  have hx0 : x ≠ 0 := by simpa [punctured] using hx
  have hauxpos : 0 < auxiliary x := by
    unfold auxiliary
    have hrecip : 0 < 1 / x ^ 2 :=
      one_div_pos.mpr (sq_pos_of_ne_zero hx0)
    linarith
  have hd : HasDerivAt auxiliary (-2 / x ^ 3) x := by
    have h :=
      (hasDerivAt_const (x := x) (1 : ℝ)).add
        ((hasDerivAt_const (x := x) (1 : ℝ)).div
          ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0))
    convert h using 1
    field_simp [hx0]
    simp
    ring
  have hderiv : deriv auxiliary x = -2 / x ^ 3 := hd.deriv
  have hhalfnonneg :
      0 ≤ auxiliary x ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hauxpos) _
  have hrpowpos :
      auxiliary x ^ (3 / 2 : ℝ) = (Real.sqrt (auxiliary x)) ^ 3 := by
    calc
      auxiliary x ^ (3 / 2 : ℝ) =
          auxiliary x ^ ((1 / 2 : ℝ) * 3) := by congr 1 <;> ring
      _ = (auxiliary x ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
        rw [Real.rpow_mul (le_of_lt hauxpos)]
      _ = (auxiliary x ^ (1 / 2 : ℝ)) ^ (3 : ℕ) := by
        simpa using (Real.rpow_natCast hhalfnonneg 3)
      _ = (Real.sqrt (auxiliary x)) ^ 3 := by
        rw [Real.sqrt_eq_rpow]
  have hrpow :
      auxiliary x ^ (-3 / 2 : ℝ) =
        1 / (Real.sqrt (auxiliary x)) ^ 3 := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring,
      Real.rpow_neg (le_of_lt hauxpos), hrpowpos]
    simp only [one_div]
  rw [gap1 x hx, hderiv, hrpow]
  field_simp [hx0, ne_of_gt (Real.sqrt_pos.2 hauxpos)]
  <;> ring

theorem gap3 (x : ℝ) (hx : x ∈ punctured) :
    HasDerivAt intermediate (integrand x) x := by
  have hfun : intermediate = primitive := by
    funext y
    by_cases hy : y = 0
    · subst y
      norm_num [intermediate, primitive, auxiliary]
    · exact intermediate_eq_primitive_of_ne y (by simpa [punctured] using hy)
  rw [hfun]
  exact primitive_hasDerivAt x

theorem gap4 (x : ℝ) (hx : x ∈ punctured) :
    intermediate x = primitive x := by
  exact intermediate_eq_primitive_of_ne x hx

theorem gap5 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand Set.univ at hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C
    have hzero : ∀ y : ℝ,
        HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y
      convert (hF y (Set.mem_univ y)).sub (primitive_hasDerivAt y) using 1
      ring
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hxy : F x - primitive x = F 0 - primitive 0 :=
      values_eq_of_hasDerivAt_zero (fun z => F z - primitive z) hzero x 0
    linarith
  · intro hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand Set.univ
    rcases hF with ⟨C, hC⟩
    have hfun : F = fun y => primitive y + C := by
      funext y
      exact hC y (Set.mem_univ y)
    intro x hx
    rw [hfun]
    exact (primitive_hasDerivAt x).add_const C

end

end ProofGap.Exercise1684
