import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1854

noncomputable section

def domain : Set ℝ := Set.Ioi (Real.sqrt (1 + Real.sqrt 2))

def integrand (x : ℝ) : ℝ :=
  x ^ 3 / Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1) +
    (1 / 2 : ℝ) *
      Real.log |x ^ 2 - 1 + Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)|

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hs2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbase_nonneg : 0 ≤ 1 + Real.sqrt 2 := by
    linarith
  have hbase_sq : (Real.sqrt (1 + Real.sqrt 2)) ^ 2 = 1 + Real.sqrt 2 :=
    Real.sq_sqrt hbase_nonneg
  have hxlt : Real.sqrt (1 + Real.sqrt 2) < x := hx
  have hxsum : 0 < x + Real.sqrt (1 + Real.sqrt 2) := by
    nlinarith [Real.sqrt_nonneg (1 + Real.sqrt 2)]
  have hxprod :
      0 < (x - Real.sqrt (1 + Real.sqrt 2)) *
        (x + Real.sqrt (1 + Real.sqrt 2)) :=
    mul_pos (sub_pos.mpr hxlt) hxsum
  have hx2 : 1 + Real.sqrt 2 < x ^ 2 := by
    nlinarith [hbase_sq]
  have hu : Real.sqrt 2 < x ^ 2 - 1 := by
    linarith
  have hua : 0 < x ^ 2 - 1 := lt_of_le_of_lt hs2_nonneg hu
  have husum : 0 < x ^ 2 - 1 + Real.sqrt 2 :=
    add_pos_of_pos_of_nonneg hua hs2_nonneg
  have huprod :
      0 < (x ^ 2 - 1 - Real.sqrt 2) *
        (x ^ 2 - 1 + Real.sqrt 2) :=
    mul_pos (sub_pos.mpr hu) husum
  have hqpos : 0 < x ^ 4 - 2 * x ^ 2 - 1 := by
    nlinarith [hs2_sq]
  have hqne : x ^ 4 - 2 * x ^ 2 - 1 ≠ 0 := ne_of_gt hqpos
  have hspos : 0 < Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1) :=
    Real.sqrt_pos.2 hqpos
  have hsne : Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1) ≠ 0 := ne_of_gt hspos
  have hsne_norm : Real.sqrt (-1 - x ^ 2 * 2 + x ^ 4) ≠ 0 := by
    rw [show -1 - x ^ 2 * 2 + x ^ 4 = x ^ 4 - 2 * x ^ 2 - 1 by ring]
    exact hsne
  have hq : HasDerivAt
      (fun y : ℝ => y ^ 4 - 2 * y ^ 2 - 1)
      (4 * x * (x ^ 2 - 1)) x := by
    convert (((hasDerivAt_id x).pow 4).sub
      ((hasDerivAt_const x 2).mul ((hasDerivAt_id x).pow 2))).sub_const 1 using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt0 := (Real.hasDerivAt_sqrt hqne).comp x hq
  have hsqrt : HasDerivAt
      (fun y : ℝ => Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1))
      (2 * x * (x ^ 2 - 1) /
        Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)) x := by
    convert hsqrt0 using 1
    field_simp [hsne]
    ring
  have huDeriv : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;>
      simp only [id_eq] <;> ring
  have ha := huDeriv.add hsqrt
  have hapos :
      0 < x ^ 2 - 1 + Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1) :=
    add_pos_of_pos_of_nonneg hua
      (Real.sqrt_nonneg (x ^ 4 - 2 * x ^ 2 - 1))
  have hane :
      x ^ 2 - 1 + Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1) ≠ 0 :=
    ne_of_gt hapos
  have hevpos : ∀ᶠ y in nhds x,
      0 < y ^ 2 - 1 + Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1) :=
    ha.continuousAt (isOpen_Ioi.mem_nhds hapos)
  have hevabs :
      (fun y : ℝ => |y ^ 2 - 1 + Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1)|) =ᶠ[nhds x]
        ((fun y : ℝ => y ^ 2 - 1) +
          fun y : ℝ => Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1)) := by
    filter_upwards [hevpos] with y hy
    simpa using (abs_of_pos hy)
  have habs : HasDerivAt
      (fun y : ℝ => |y ^ 2 - 1 + Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1)|)
      (2 * x + 2 * x * (x ^ 2 - 1) /
        Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)) x :=
    ha.congr_of_eventuallyEq hevabs
  have hlog0 :=
    (Real.hasDerivAt_log (abs_ne_zero.mpr hane)).comp x habs
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log
        |y ^ 2 - 1 + Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1)|)
      (2 * x / Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)) x := by
    convert hlog0 using 1
    rw [abs_of_pos hapos]
    field_simp [hsne, hane] <;> ring_nf <;> simp [hsne, hsne_norm]
  have hp :=
    ((hasDerivAt_const x (1 / 2 : ℝ)).mul hsqrt).add
      ((hasDerivAt_const x (1 / 2 : ℝ)).mul hlog)
  have hp' : HasDerivAt
      (fun y : ℝ =>
        (1 / 2 : ℝ) * Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1) +
          (1 / 2 : ℝ) * Real.log
            |y ^ 2 - 1 + Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1)|)
      ((1 / 2 : ℝ) *
          (2 * x * (x ^ 2 - 1) /
            Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)) +
        (1 / 2 : ℝ) *
          (2 * x / Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1))) x := by
    simpa only [zero_mul, zero_add] using hp
  have halg :
      (1 / 2 : ℝ) *
          (2 * x * (x ^ 2 - 1) /
            Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)) +
        (1 / 2 : ℝ) *
          (2 * x / Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)) =
      x ^ 3 / Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1) := by
    field_simp [hsne] <;> ring
  change HasDerivAt
    (fun y : ℝ =>
      (1 / 2 : ℝ) * Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1) +
        (1 / 2 : ℝ) * Real.log
          |y ^ 2 - 1 + Real.sqrt (y ^ 4 - 2 * y ^ 2 - 1)|)
    (x ^ 3 / Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1)) x
  rw [← halg]
  exact hp'

theorem gap1 :
    antiderivatives integrand =
      antiderivatives
        (fun x => x * (x ^ 2 - 1 + 1) /
          Real.sqrt ((x ^ 2 - 1) ^ 2 - 2)) := by
  apply congrArg antiderivatives
  funext x
  unfold integrand
  have hn : x * (x ^ 2 - 1 + 1) = x ^ 3 := by
    ring
  have hr : (x ^ 2 - 1) ^ 2 - 2 = x ^ 4 - 2 * x ^ 2 - 1 := by
    ring
  rw [hn, hr]

theorem gap2 : antiderivatives integrand = primitiveFamily primitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hF'⟩
    have hconst : ∀ ⦃x⦄, x ∈ domain → ∀ ⦃y⦄, y ∈ domain →
        F x - primitive x = F y - primitive y := by
      intro x hx y hy
      let u : ℝ := max x y + 1
      have hxI : x ∈ Ioo (Real.sqrt (1 + Real.sqrt 2)) u := by
        constructor
        · exact hx
        · dsimp [u]
          linarith [le_max_left x y]
      have hyI : y ∈ Ioo (Real.sqrt (1 + Real.sqrt 2)) u := by
        constructor
        · exact hy
        · dsimp [u]
          linarith [le_max_right x y]
      have hdiff : DifferentiableOn ℝ (fun z => F z - primitive z)
          (Ioo (Real.sqrt (1 + Real.sqrt 2)) u) := by
        intro z hz
        have hzdom : z ∈ domain := hz.1
        have hFat : DifferentiableAt ℝ F z :=
          (hF z hzdom).differentiableAt (isOpen_Ioi.mem_nhds hzdom)
        exact hFat.differentiableWithinAt.sub
          (primitive_hasDerivAt hzdom).differentiableAt.differentiableWithinAt
      have hzero : ∀ z ∈ Ioo (Real.sqrt (1 + Real.sqrt 2)) u,
          deriv (fun w => F w - primitive w) z = 0 := by
        intro z hz
        have hzdom : z ∈ domain := hz.1
        have hFat : DifferentiableAt ℝ F z :=
          (hF z hzdom).differentiableAt (isOpen_Ioi.mem_nhds hzdom)
        have hd := (hFat.hasDerivAt.sub (primitive_hasDerivAt hzdom)).deriv
        rw [hF' z hzdom] at hd
        simpa using hd
      exact
        (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero)
          hxI hyI
    let b : ℝ := Real.sqrt (1 + Real.sqrt 2) + 1
    have hb : b ∈ domain := by
      simp [b, domain]
    refine ⟨F b - primitive b, ?_⟩
    intro x hx
    have heq := hconst hx hb
    linarith
  · rintro ⟨C, hFC⟩
    have hder : ∀ x ∈ domain, HasDerivAt F (integrand x) x := by
      intro x hx
      have hev : F =ᶠ[nhds x] (fun y => primitive y + C) :=
        Filter.mem_of_superset (isOpen_Ioi.mem_nhds hx)
          (fun y hy => hFC y hy)
      exact ((primitive_hasDerivAt hx).add_const C).congr_of_eventuallyEq hev
    constructor
    · intro x hx
      exact (hder x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hder x hx).deriv

end

end ProofGap.Exercise1854
