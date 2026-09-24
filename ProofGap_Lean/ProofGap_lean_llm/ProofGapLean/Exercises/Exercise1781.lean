import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1781

noncomputable section

def sec (t : ℝ) : ℝ := 1 / Real.cos t
def xOf (a t : ℝ) : ℝ := a * Real.tan t
def angleDomain : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def integrand (a x : ℝ) : ℝ := 1 / (Real.sqrt (x ^ 2 + a ^ 2)) ^ 3
def primitive (a x : ℝ) : ℝ :=
  x / (a ^ 2 * Real.sqrt (a ^ 2 + x ^ 2))
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private theorem sqrt_xOf_eq (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ angleDomain) :
    Real.sqrt (xOf a t ^ 2 + a ^ 2) = a * sec t := by
  have hcos : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    simpa only [angleDomain, Set.mem_Ioo, neg_div] using ht
  have hinside :
      xOf a t ^ 2 + a ^ 2 = (a / Real.cos t) ^ 2 := by
    rw [xOf, Real.tan_eq_sin_div_cos]
    calc
      (a * (Real.sin t / Real.cos t)) ^ 2 + a ^ 2 =
          a ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) /
            Real.cos t ^ 2 := by
        field_simp [hcos.ne']
      _ = a ^ 2 / Real.cos t ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
      _ = (a / Real.cos t) ^ 2 := by ring
  rw [hinside, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos ha hcos)]
  simp [sec, div_eq_mul_inv]

theorem gap1 (a t : ℝ) (ha : 0 < a) (ht : t ∈ angleDomain) :
    (Real.sqrt (xOf a t ^ 2 + a ^ 2)) ^ 3 = a ^ 3 * sec t ^ 3 := by
  rw [sqrt_xOf_eq a t ha ht]
  ring

theorem gap2 (a t : ℝ) (ha : 0 < a) (ht : t ∈ angleDomain) :
    deriv (xOf a) t = a * sec t ^ 2 := by
  have hcos : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    simpa only [angleDomain, Set.mem_Ioo, neg_div] using ht
  have hderiv := (Real.hasDerivAt_tan hcos.ne').const_mul a
  change deriv (fun u => a * Real.tan u) t = a * sec t ^ 2
  rw [hderiv.deriv]
  simp [sec]

theorem gap3 (a t : ℝ) (ha : 0 < a) (ht : t ∈ angleDomain) :
    integrand a (xOf a t) * deriv (xOf a) t =
      1 / a ^ 2 * Real.cos t := by
  have hcos : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    simpa only [angleDomain, Set.mem_Ioo, neg_div] using ht
  unfold integrand
  rw [gap1 a t ha ht, gap2 a t ha ht]
  unfold sec
  field_simp [ha.ne', hcos.ne']

theorem gap4 (a t : ℝ) (ha : 0 < a) (ht : t ∈ angleDomain) :
    HasDerivAt (fun u => 1 / a ^ 2 * Real.sin u)
      (integrand a (xOf a t) * deriv (xOf a) t) t := by
  simpa only [gap3 a t ha ht] using
    (Real.hasDerivAt_sin t).const_mul (1 / a ^ 2)

theorem gap5 (a t : ℝ) (ha : 0 < a) (ht : t ∈ angleDomain) :
    HasDerivAt (fun u => 1 / a ^ 2 * Real.sin u)
      (1 / a ^ 2 * Real.cos t) t := by
  simpa only [one_div] using
    (Real.hasDerivAt_sin t).const_mul ((a ^ 2)⁻¹)

theorem gap6 (t : ℝ) (ht : t ∈ angleDomain) :
    Real.sin t = Real.tan t / Real.sqrt (1 + Real.tan t ^ 2) := by
  have hcos : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    simpa only [angleDomain, Set.mem_Ioo, neg_div] using ht
  have hroot : Real.sqrt (1 + Real.tan t ^ 2) = sec t := by
    simpa [xOf, add_comm] using
      (sqrt_xOf_eq (1 : ℝ) t zero_lt_one ht)
  rw [hroot]
  unfold sec
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos.ne']

theorem gap7 (a t : ℝ) (ha : 0 < a) (ht : t ∈ angleDomain) :
    1 / a ^ 2 * Real.sin t = primitive a (xOf a t) := by
  have hcos : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    simpa only [angleDomain, Set.mem_Ioo, neg_div] using ht
  have hroot :
      Real.sqrt (a ^ 2 + xOf a t ^ 2) = a * sec t := by
    simpa [add_comm] using sqrt_xOf_eq a t ha ht
  have hroot_one : Real.sqrt (1 + Real.tan t ^ 2) = sec t := by
    simpa [xOf, add_comm] using
      (sqrt_xOf_eq (1 : ℝ) t zero_lt_one ht)
  rw [gap6 t ht, hroot_one]
  unfold primitive
  rw [hroot]
  unfold xOf sec
  field_simp [ha.ne', hcos.ne']

theorem gap8 (a : ℝ) (ha : 0 < a) :
    Family (integrand a) = Translates (primitive a) := by
  have hprimitive : IsAntiderivative (primitive a) (integrand a) := by
    intro x
    have hpos : 0 < a ^ 2 + x ^ 2 := by
      positivity
    have hspos : 0 < Real.sqrt (a ^ 2 + x ^ 2) :=
      Real.sqrt_pos.2 hpos
    have hinner :
        HasDerivAt (fun y : ℝ => a ^ 2 + y ^ 2) (2 * x) x := by
      convert (hasDerivAt_const x (a ^ 2)).add
        ((hasDerivAt_id x).pow 2) using 1 <;> simp [id] <;> ring
    have hsqrt :
        HasDerivAt (fun y : ℝ => Real.sqrt (a ^ 2 + y ^ 2))
          (x / Real.sqrt (a ^ 2 + x ^ 2)) x := by
      convert (Real.hasDerivAt_sqrt hpos.ne').comp x hinner using 1 <;>
        field_simp [hspos.ne'] <;> ring
    have hden := hsqrt.const_mul (a ^ 2)
    have hraw := (hasDerivAt_id x).div hden
      (mul_ne_zero (pow_ne_zero 2 ha.ne') hspos.ne')
    have hsquare :
        Real.sqrt (a ^ 2 + x ^ 2) ^ 2 = a ^ 2 + x ^ 2 :=
      Real.sq_sqrt hpos.le
    have hcoef :
        (1 * (a ^ 2 * Real.sqrt (a ^ 2 + x ^ 2)) -
            x * (a ^ 2 * (x / Real.sqrt (a ^ 2 + x ^ 2)))) /
            (a ^ 2 * Real.sqrt (a ^ 2 + x ^ 2)) ^ 2 =
          integrand a x := by
      calc
        _ = (Real.sqrt (a ^ 2 + x ^ 2) ^ 2 - x ^ 2) /
              (a ^ 2 * Real.sqrt (a ^ 2 + x ^ 2) ^ 3) := by
            field_simp [ha.ne', hspos.ne'] <;> ring
        _ = a ^ 2 /
              (a ^ 2 * Real.sqrt (a ^ 2 + x ^ 2) ^ 3) := by
            rw [hsquare]
            ring
        _ = 1 / Real.sqrt (a ^ 2 + x ^ 2) ^ 3 := by
            field_simp [ha.ne']
        _ = integrand a x := by
            simp [integrand, add_comm]
    convert hraw using 1
    simpa [id] using hcoef.symm
  ext F
  constructor
  · intro hF
    change IsAntiderivative F (integrand a) at hF
    let G : ℝ → ℝ := fun x => F x - primitive a x
    have hG : ∀ x, HasDerivAt G 0 x := by
      intro x
      simpa [G] using (hF x).sub (hprimitive x)
    have hdiff : Differentiable ℝ G :=
      fun x => (hG x).differentiableAt
    have hderiv : ∀ x, deriv G x = 0 :=
      fun x => (hG x).deriv
    have hconst : ∀ x y, G x = G y :=
      is_const_of_deriv_eq_zero hdiff hderiv
    refine ⟨G 0, ?_⟩
    intro x
    have hx : G x = G 0 := hconst x 0
    dsimp [G] at hx ⊢
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivative F (integrand a)
    have hfun : F = fun x => primitive a x + C := funext hC
    rw [hfun]
    intro x
    simpa using (hprimitive x).const_add C

end

end ProofGap.Exercise1781
