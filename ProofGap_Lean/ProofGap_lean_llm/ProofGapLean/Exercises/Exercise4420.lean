import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4420

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def vectorField (y z : ℝ → ℝ) (x : ℝ) : Vec3 :=
  (x, y x, 2 * z x)

def velocity (y z : ℝ → ℝ) (x : ℝ) : Vec3 :=
  (1, deriv y x, deriv z x)

def scaleVec (s : ℝ) (v : Vec3) : Vec3 :=
  (s * v.1, s * v.2.1, s * v.2.2)

def IsIntegralCurveAt (y z : ℝ → ℝ) (x : ℝ) : Prop :=
  0 < x ∧
    HasDerivAt y (y x / x) x ∧
      HasDerivAt z (2 * z x / x) x

def IsIntegralCurveOnPositive (y z : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → IsIntegralCurveAt y z x

private theorem positive_eq_at_one_of_zero_deriv (f : ℝ → ℝ)
    (hf : ∀ x, 0 < x → HasDerivAt f 0 x) :
    ∀ x, 0 < x → f x = f 1 := by
  intro x hx
  let b : ℝ := x + 2
  have hxb : x < b := by
    dsimp [b]
    linarith
  have hb1 : 1 < b := by
    dsimp [b]
    linarith
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 b) := by
    intro t ht
    exact (hf t ht.1).differentiableAt.differentiableWithinAt
  have hzero : ∀ t ∈ Set.Ioo (0 : ℝ) b, deriv f t = 0 := by
    intro t ht
    exact (hf t ht.1).deriv
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero
    ⟨hx, hxb⟩ ⟨zero_lt_one, hb1⟩

theorem gap1 (y z : ℝ → ℝ) (x : ℝ)
    (h : IsIntegralCurveAt y z x) :
    HasDerivAt y (y x / x) x := by
  exact h.2.1

theorem gap2 (y z : ℝ → ℝ) (x : ℝ)
    (h : IsIntegralCurveAt y z x) :
    HasDerivAt z (2 * z x / x) x := by
  exact h.2.2

theorem gap3 (y z : ℝ → ℝ) (x : ℝ)
    (h : IsIntegralCurveAt y z x) :
    velocity y z x = scaleVec (1 / x) (vectorField y z x) := by
  rcases h with ⟨hx, hy, hz⟩
  apply Prod.ext
  · change (1 : ℝ) = (1 / x) * x
    field_simp [hx.ne']
  · apply Prod.ext
    · change deriv y x = (1 / x) * y x
      rw [hy.deriv]
      ring
    · change deriv z x = (1 / x) * (2 * z x)
      rw [hz.deriv]
      ring

theorem gap4 (y z : ℝ → ℝ) (x : ℝ) :
    (vectorField y z x).1 = x := by
  rfl

theorem gap5 (y z : ℝ → ℝ) (x : ℝ) :
    (vectorField y z x).2.1 = y x := by
  rfl

theorem gap6 (y z : ℝ → ℝ) (x : ℝ) :
    (vectorField y z x).2.2 = 2 * z x := by
  rfl

theorem gap7 (y z : ℝ → ℝ) (x : ℝ)
    (h : IsIntegralCurveAt y z x) :
    deriv y x = y x / x := by
  exact (gap1 y z x h).deriv

theorem gap8 (y z : ℝ → ℝ) (x : ℝ)
    (h : IsIntegralCurveAt y z x) :
    deriv y x = y x / x ∧ deriv z x = 2 * z x / x := by
  exact ⟨(gap1 y z x h).deriv, (gap2 y z x h).deriv⟩

theorem gap9 (y z : ℝ → ℝ) (x : ℝ)
    (h : IsIntegralCurveAt y z x) :
    deriv z x = 2 * z x / x := by
  exact (gap2 y z x h).deriv

theorem gap10 (y z : ℝ → ℝ)
    (hCurve : IsIntegralCurveOnPositive y z) :
    ∃ c₁ : ℝ, ∀ x, 0 < x → y x = c₁ * x := by
  refine ⟨y 1, ?_⟩
  intro x hx
  have hzero : ∀ t, 0 < t → HasDerivAt (fun u => y u / u) 0 t := by
    intro t ht
    have hy := gap1 y z t (hCurve t ht)
    have hid : HasDerivAt (fun u : ℝ => u) 1 t := by
      simpa using (hasDerivAt_id t)
    convert hy.div hid ht.ne' using 1 <;>
      field_simp [ht.ne'] <;> ring
  have hconst := positive_eq_at_one_of_zero_deriv (fun t => y t / t) hzero x hx
  have hratio : y x / x = y 1 := by
    simpa using hconst
  calc
    y x = (y x / x) * x := by field_simp [hx.ne']
    _ = y 1 * x := by rw [hratio]

theorem gap11 (y z : ℝ → ℝ)
    (hCurve : IsIntegralCurveOnPositive y z) :
    ∃ c₂ : ℝ, ∀ x, 0 < x → z x = c₂ * x ^ 2 := by
  refine ⟨z 1, ?_⟩
  intro x hx
  have hzero : ∀ t, 0 < t → HasDerivAt (fun u => z u / u ^ 2) 0 t := by
    intro t ht
    have hz := gap2 y z t (hCurve t ht)
    have hid : HasDerivAt (fun u : ℝ => u) 1 t := by
      simpa using (hasDerivAt_id t)
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa [pow_two, two_mul] using hid.mul hid
    convert hz.div hsq (pow_ne_zero 2 ht.ne') using 1 <;>
      field_simp [ht.ne'] <;> ring
  have hconst := positive_eq_at_one_of_zero_deriv (fun t => z t / t ^ 2) hzero x hx
  have hratio : z x / x ^ 2 = z 1 := by
    simpa using hconst
  calc
    z x = (z x / x ^ 2) * x ^ 2 := by field_simp [hx.ne']
    _ = z 1 * x ^ 2 := by rw [hratio]

theorem gap12 (c₁ c₂ : ℝ) :
    IsIntegralCurveOnPositive (fun x => c₁ * x) (fun x => c₂ * x ^ 2) := by
  intro x hx
  refine ⟨hx, ?_, ?_⟩
  · convert (hasDerivAt_id x).const_mul c₁ using 1 <;>
      field_simp [hx.ne'] <;> ring
  · have hid : HasDerivAt (fun u : ℝ => u) 1 x := by
      simpa using (hasDerivAt_id x)
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
      simpa [pow_two, two_mul] using hid.mul hid
    convert hsq.const_mul c₂ using 1 <;>
      field_simp [hx.ne'] <;> ring

end

end ProofGap.Exercise4420
