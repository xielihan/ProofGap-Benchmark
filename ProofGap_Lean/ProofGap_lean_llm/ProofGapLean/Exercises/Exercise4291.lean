import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4291

noncomputable section

abbrev Point3 := ℝ × ℝ × ℝ

def field (p : Point3) : Point3 :=
  (1 - 1 / p.2.1 + p.2.1 / p.2.2,
    p.1 / p.2.2 + p.1 / p.2.1 ^ 2,
    -(p.1 * p.2.1 / p.2.2 ^ 2))

def potential (p : Point3) : ℝ :=
  p.1 - p.1 / p.2.1 + p.1 * p.2.1 / p.2.2

def InRegularDomain (p : Point3) : Prop :=
  p.2.1 ≠ 0 ∧ p.2.2 ≠ 0

def InPositiveComponent (p : Point3) : Prop :=
  0 < p.2.1 ∧ 0 < p.2.2

def coordinateDifferential (V v : Point3) : ℝ :=
  V.1 * v.1 + V.2.1 * v.2.1 + V.2.2 * v.2.2

def differential (F : Point3 → ℝ) (p v : Point3) : ℝ :=
  deriv (fun x => F (x, p.2.1, p.2.2)) p.1 * v.1 +
    deriv (fun y => F (p.1, y, p.2.2)) p.2.1 * v.2.1 +
      deriv (fun z => F (p.1, p.2.1, z)) p.2.2 * v.2.2

def firstExpansion (p v : Point3) : ℝ :=
  v.1 - (1 / p.2.1) * v.1 + (p.1 / p.2.1 ^ 2) * v.2.1 +
    (1 / p.2.2) * (p.2.1 * v.1 + p.1 * v.2.1) -
      p.1 * p.2.1 / p.2.2 ^ 2 * v.2.2

def productRuleExpansion (p v : Point3) : ℝ :=
  v.1 + (-1 / p.2.1) * v.1 +
    p.1 * (1 / p.2.1 ^ 2 * v.2.1) +
    (1 / p.2.2) * (p.2.1 * v.1 + p.1 * v.2.1) +
    p.1 * p.2.1 * (-1 / p.2.2 ^ 2 * v.2.2)

def HasCoordinateGradientAt
    (F : Point3 → ℝ) (V : Point3) (p : Point3) : Prop :=
  HasDerivAt (fun x => F (x, p.2.1, p.2.2)) V.1 p.1 ∧
    HasDerivAt (fun y => F (p.1, y, p.2.2)) V.2.1 p.2.1 ∧
      HasDerivAt (fun z => F (p.1, p.2.1, z)) V.2.2 p.2.2

def IsPositiveSolution (u : Point3 → ℝ) : Prop :=
  ∀ p, InPositiveComponent p → HasCoordinateGradientAt u (field p) p

private theorem potential_hasCoordinateGradientAt
    (p : Point3) (hp : InRegularDomain p) :
    HasCoordinateGradientAt potential (field p) p := by
  rcases hp with ⟨hy, hz⟩
  dsimp [HasCoordinateGradientAt]
  constructor
  · simpa [potential, field] using
      (((hasDerivAt_id p.1).sub
        ((hasDerivAt_id p.1).div_const p.2.1)).add
        (((hasDerivAt_id p.1).mul_const p.2.1).div_const p.2.2))
  · constructor
    · dsimp [potential, field]
      convert
        (((hasDerivAt_const p.2.1 p.1).sub
          ((hasDerivAt_const p.2.1 p.1).div
            (hasDerivAt_id p.2.1) hy)).add
          (((hasDerivAt_const p.2.1 p.1).mul
            (hasDerivAt_id p.2.1)).div_const p.2.2)) using 1 <;>
        simp <;> ring
    · dsimp [potential, field]
      convert
        (((hasDerivAt_const p.2.2 p.1).sub
          ((hasDerivAt_const p.2.2 p.1).div_const p.2.1)).add
          (((hasDerivAt_const p.2.2 p.1).mul_const p.2.1).div
            (hasDerivAt_id p.2.2) hz)) using 1 <;>
        simp <;> ring

theorem gap1 (p v : Point3) (hp : InRegularDomain p) :
    coordinateDifferential (field p) v = firstExpansion p v := by
  dsimp [coordinateDifferential, field, firstExpansion]
  ring

theorem gap2 (p v : Point3) (hp : InRegularDomain p) :
    firstExpansion p v = productRuleExpansion p v := by
  dsimp [firstExpansion, productRuleExpansion]
  ring

theorem gap3 (p v : Point3) (hp : InRegularDomain p) :
    productRuleExpansion p v =
      differential (fun q => q.1) p v +
        differential (fun q => -q.1 / q.2.1) p v +
          differential (fun q => q.1 * q.2.1 / q.2.2) p v := by
  rcases hp with ⟨hy, hz⟩
  have hBx :
      deriv (fun x : ℝ => -x / p.2.1) p.1 = -1 / p.2.1 := by
    simpa using ((hasDerivAt_id p.1).neg.div_const p.2.1).deriv
  have hBy :
      deriv (fun y : ℝ => -p.1 / y) p.2.1 = p.1 / p.2.1 ^ 2 := by
    simpa using
      (((hasDerivAt_const p.2.1 (-p.1)).div
        (hasDerivAt_id p.2.1) hy).deriv)
  have hCx :
      deriv (fun x : ℝ => x * p.2.1 / p.2.2) p.1 = p.2.1 / p.2.2 := by
    simpa using
      (((hasDerivAt_id p.1).mul_const p.2.1).div_const p.2.2).deriv
  have hCy :
      deriv (fun y : ℝ => p.1 * y / p.2.2) p.2.1 = p.1 / p.2.2 := by
    simpa using
      (((hasDerivAt_const p.2.1 p.1).mul
        (hasDerivAt_id p.2.1)).div_const p.2.2).deriv
  have hCz :
      deriv (fun z : ℝ => p.1 * p.2.1 / z) p.2.2 =
        -(p.1 * p.2.1 / p.2.2 ^ 2) := by
    calc
      deriv (fun z : ℝ => p.1 * p.2.1 / z) p.2.2 =
          -(p.1 * p.2.1) / p.2.2 ^ 2 := by
        simpa using
          (((hasDerivAt_const p.2.2 (p.1 * p.2.1)).div
            (hasDerivAt_id p.2.2) hz).deriv)
      _ = -(p.1 * p.2.1 / p.2.2 ^ 2) := by ring
  dsimp [productRuleExpansion, differential]
  simp [hBx, hBy, hCx, hCy, hCz] <;> ring

theorem gap4 (p v : Point3) (hp : InRegularDomain p) :
    differential (fun q => q.1) p v +
        differential (fun q => -q.1 / q.2.1) p v +
          differential (fun q => q.1 * q.2.1 / q.2.2) p v =
      differential potential p v := by
  calc
    differential (fun q => q.1) p v +
          differential (fun q => -q.1 / q.2.1) p v +
            differential (fun q => q.1 * q.2.1 / q.2.2) p v =
        productRuleExpansion p v := (gap3 p v hp).symm
    _ = firstExpansion p v := (gap2 p v hp).symm
    _ = coordinateDifferential (field p) v := (gap1 p v hp).symm
    _ = differential potential p v := by
      have h := potential_hasCoordinateGradientAt p hp
      dsimp [coordinateDifferential, differential]
      rw [h.1.deriv, h.2.1.deriv, h.2.2.deriv]

theorem gap5 (p v : Point3) (hp : InRegularDomain p) :
    coordinateDifferential (field p) v = differential potential p v := by
  have h := potential_hasCoordinateGradientAt p hp
  dsimp [coordinateDifferential, differential]
  rw [h.1.deriv, h.2.1.deriv, h.2.2.deriv]

theorem gap6 (u : Point3 → ℝ) :
    IsPositiveSolution u ↔
      ∃ C : ℝ, ∀ p, InPositiveComponent p → u p = potential p + C := by
  constructor
  · intro hu
    let b : Point3 := (0, 1, 1)
    refine ⟨u b - potential b, ?_⟩
    intro p hp
    have hxderiv : ∀ x : ℝ,
        HasDerivAt
          (fun t => u ((t, p.2.1, p.2.2) : Point3) -
            potential ((t, p.2.1, p.2.2) : Point3)) 0 x := by
      intro x
      simpa using
        ((hu ((x, p.2.1, p.2.2) : Point3) ⟨hp.1, hp.2⟩).1.sub
          (potential_hasCoordinateGradientAt
            ((x, p.2.1, p.2.2) : Point3)
            ⟨ne_of_gt hp.1, ne_of_gt hp.2⟩).1)
    have hx :
        u p - potential p =
          u ((0, p.2.1, p.2.2) : Point3) -
            potential ((0, p.2.1, p.2.2) : Point3) := by
      exact is_const_of_deriv_eq_zero
        (fun x => (hxderiv x).differentiableAt)
        (fun x => (hxderiv x).deriv) p.1 0
    have hyderiv : ∀ t : ℝ,
        HasDerivAt
          (fun s => u ((0, Real.exp s, p.2.2) : Point3) -
            potential ((0, Real.exp s, p.2.2) : Point3)) 0 t := by
      intro t
      have houter :
          HasDerivAt
            (fun y => u ((0, y, p.2.2) : Point3) -
              potential ((0, y, p.2.2) : Point3)) 0 (Real.exp t) := by
        simpa using
          ((hu ((0, Real.exp t, p.2.2) : Point3)
              ⟨Real.exp_pos t, hp.2⟩).2.1.sub
            (potential_hasCoordinateGradientAt
              ((0, Real.exp t, p.2.2) : Point3)
              ⟨ne_of_gt (Real.exp_pos t), ne_of_gt hp.2⟩).2.1)
      simpa using houter.comp t (Real.hasDerivAt_exp t)
    have hylog := is_const_of_deriv_eq_zero
      (fun t => (hyderiv t).differentiableAt)
      (fun t => (hyderiv t).deriv) (Real.log p.2.1) 0
    have hy :
        u ((0, p.2.1, p.2.2) : Point3) -
            potential ((0, p.2.1, p.2.2) : Point3) =
          u ((0, 1, p.2.2) : Point3) -
            potential ((0, 1, p.2.2) : Point3) := by
      simpa [Real.exp_log hp.1] using hylog
    have hzderiv : ∀ t : ℝ,
        HasDerivAt
          (fun s => u ((0, 1, Real.exp s) : Point3) -
            potential ((0, 1, Real.exp s) : Point3)) 0 t := by
      intro t
      have houter :
          HasDerivAt
            (fun z => u ((0, 1, z) : Point3) -
              potential ((0, 1, z) : Point3)) 0 (Real.exp t) := by
        simpa using
          ((hu ((0, 1, Real.exp t) : Point3)
              ⟨by norm_num, Real.exp_pos t⟩).2.2.sub
            (potential_hasCoordinateGradientAt
              ((0, 1, Real.exp t) : Point3)
              ⟨by norm_num, ne_of_gt (Real.exp_pos t)⟩).2.2)
      simpa using houter.comp t (Real.hasDerivAt_exp t)
    have hzlog := is_const_of_deriv_eq_zero
      (fun t => (hzderiv t).differentiableAt)
      (fun t => (hzderiv t).deriv) (Real.log p.2.2) 0
    have hz :
        u ((0, 1, p.2.2) : Point3) -
            potential ((0, 1, p.2.2) : Point3) =
          u ((0, 1, 1) : Point3) -
            potential ((0, 1, 1) : Point3) := by
      simpa [Real.exp_log hp.2] using hzlog
    have hEq := hx.trans (hy.trans hz)
    change u p = potential p +
      (u ((0, 1, 1) : Point3) - potential ((0, 1, 1) : Point3))
    linarith
  · rintro ⟨C, hC⟩
    intro p hp
    have hpot := potential_hasCoordinateGradientAt p
      ⟨ne_of_gt hp.1, ne_of_gt hp.2⟩
    constructor
    · have hg :
          HasDerivAt
            (fun x => potential ((x, p.2.1, p.2.2) : Point3) + C)
            (field p).1 p.1 := by
        simpa using hpot.1.add_const C
      have heq :
          (fun x => u ((x, p.2.1, p.2.2) : Point3)) =ᶠ[nhds p.1]
            (fun x => potential ((x, p.2.1, p.2.2) : Point3) + C) :=
        Filter.Eventually.of_forall
          (fun x => hC ((x, p.2.1, p.2.2) : Point3) ⟨hp.1, hp.2⟩)
      exact hg.congr_of_eventuallyEq heq
    · constructor
      · have hg :
            HasDerivAt
              (fun y => potential ((p.1, y, p.2.2) : Point3) + C)
              (field p).2.1 p.2.1 := by
          simpa using hpot.2.1.add_const C
        have hypos : ∀ᶠ y in nhds p.2.1, 0 < y := Ioi_mem_nhds hp.1
        have heq :
            (fun y => u ((p.1, y, p.2.2) : Point3)) =ᶠ[nhds p.2.1]
              (fun y => potential ((p.1, y, p.2.2) : Point3) + C) :=
          hypos.mono
            (fun y hy => hC ((p.1, y, p.2.2) : Point3) ⟨hy, hp.2⟩)
        exact hg.congr_of_eventuallyEq heq
      · have hg :
            HasDerivAt
              (fun z => potential ((p.1, p.2.1, z) : Point3) + C)
              (field p).2.2 p.2.2 := by
          simpa using hpot.2.2.add_const C
        have hzpos : ∀ᶠ z in nhds p.2.2, 0 < z := Ioi_mem_nhds hp.2
        have heq :
            (fun z => u ((p.1, p.2.1, z) : Point3)) =ᶠ[nhds p.2.2]
              (fun z => potential ((p.1, p.2.1, z) : Point3) + C) :=
          hzpos.mono
            (fun z hz => hC ((p.1, p.2.1, z) : Point3) ⟨hp.1, hz⟩)
        exact hg.congr_of_eventuallyEq heq

theorem gap7 (C : ℝ) :
    IsPositiveSolution (fun p => potential p + C) := by
  intro p hp
  have h := potential_hasCoordinateGradientAt p
    ⟨ne_of_gt hp.1, ne_of_gt hp.2⟩
  constructor
  · simpa using h.1.add_const C
  · constructor
    · simpa using h.2.1.add_const C
    · simpa using h.2.2.add_const C

end

end ProofGap.Exercise4291
