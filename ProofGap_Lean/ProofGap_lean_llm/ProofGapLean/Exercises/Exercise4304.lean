import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4304

noncomputable section

open MeasureTheory
open scoped Interval

def P (φ : ℝ → ℝ) (m x y : ℝ) : ℝ :=
  φ y * Real.exp x - m * y

def Q (dφ : ℝ → ℝ) (m x y : ℝ) : ℝ :=
  dφ y * Real.exp x - m

def pathIntegral
    (P Q : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
      Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t

def segment (B A : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) * B.1 + t * A.1, (1 - t) * B.2 + t * A.2)

def closedIntegral
    (P Q : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (A B : ℝ × ℝ) : ℝ :=
  pathIntegral P Q γ + pathIntegral P Q (segment B A)

def regionIntegral (D : Set (ℝ × ℝ)) (m : ℝ) : ℝ :=
  ∫ _z in D, m

def regionArea (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ _z in D, (1 : ℝ)

def IsPositiveGreenBoundary
    (γ : ℝ → ℝ × ℝ) (A B : ℝ × ℝ)
    (D : Set (ℝ × ℝ)) : Prop :=
  γ 0 = A ∧ γ 1 = B ∧
    ∀ U V : ℝ → ℝ → ℝ,
      Continuous
          (fun z : ℝ × ℝ =>
            deriv (fun x => V x z.2) z.1) →
      Continuous
          (fun z : ℝ × ℝ =>
            deriv (fun y => U z.1 y) z.2) →
      closedIntegral U V γ A B =
        ∫ z in D,
          deriv (fun x => V x z.2) z.1 -
            deriv (fun y => U z.1 y) z.2

def potential (φ : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp z.1 * φ z.2

def segmentAuxIntegral (A B : ℝ × ℝ) : ℝ :=
  pathIntegral (fun _ y => y) (fun _ _ => 1) (segment B A)

private theorem hasDerivAt_Q_x
    (dφ : ℝ → ℝ) (m x y : ℝ) :
    HasDerivAt (fun u => Q dφ m u y)
      (dφ y * Real.exp x) x := by
  simpa [Q] using
    ((Real.hasDerivAt_exp x).const_mul (dφ y)).sub_const m

private theorem hasDerivAt_P_y
    (φ dφ : ℝ → ℝ) (m x y : ℝ)
    (hφ : ∀ y, HasDerivAt φ (dφ y) y) :
    HasDerivAt (fun v => P φ m x v)
      (dφ y * Real.exp x - m) y := by
  have hm :
      HasDerivAt (fun v : ℝ => m * v) m y := by
    simpa using (hasDerivAt_id y).const_mul m
  simpa [P, mul_comm] using
    ((hφ y).mul_const (Real.exp x)).sub hm

private theorem segment_hasDerivAt_fst
    (A B : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s => (segment B A s).1)
      (A.1 - B.1) t := by
  convert
    (((hasDerivAt_const t (1 : ℝ)).sub
        (hasDerivAt_id t)).mul_const B.1).add
      ((hasDerivAt_id t).mul_const A.1)
    using 1 <;>
    simp [segment] <;> ring

private theorem segment_hasDerivAt_snd
    (A B : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s => (segment B A s).2)
      (A.2 - B.2) t := by
  convert
    (((hasDerivAt_const t (1 : ℝ)).sub
        (hasDerivAt_id t)).mul_const B.2).add
      ((hasDerivAt_id t).mul_const A.2)
    using 1 <;>
    simp [segment] <;> ring

private theorem potential_segment_hasDerivAt
    (φ dφ : ℝ → ℝ) (A B : ℝ × ℝ)
    (hφ : ∀ y, HasDerivAt φ (dφ y) y)
    (t : ℝ) :
    HasDerivAt
      (fun s => potential φ (segment B A s))
      (P φ 0 (segment B A t).1 (segment B A t).2 *
          deriv (fun s => (segment B A s).1) t +
        Q dφ 0 (segment B A t).1 (segment B A t).2 *
          deriv (fun s => (segment B A s).2) t) t := by
  have hx := segment_hasDerivAt_fst A B t
  have hy := segment_hasDerivAt_snd A B t
  have he :=
    (Real.hasDerivAt_exp (segment B A t).1).comp t hx
  have hp :=
    (hφ (segment B A t).2).comp t hy
  convert he.mul hp using 1
  rw [hx.deriv, hy.deriv]
  simp [P, Q]
  ring

private theorem segmentAux_value (A B : ℝ × ℝ) :
    segmentAuxIntegral A B =
      A.2 - B.2 +
        (A.1 - B.1) * (A.2 + B.2) / 2 := by
  let K : ℝ → ℝ := fun t =>
    (A.1 - B.1) *
        (B.2 * t + (A.2 - B.2) * t ^ 2 / 2) +
      (A.2 - B.2) * t
  have hK (t : ℝ) :
      HasDerivAt K
        ((segment B A t).2 *
            deriv (fun s => (segment B A s).1) t +
          (1 : ℝ) *
            deriv (fun s => (segment B A s).2) t) t := by
    have ht2 :
        HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      convert (hasDerivAt_id t).pow 2 using 1 <;> simp <;> ring
    have hinside :=
      ((hasDerivAt_id t).const_mul B.2).add
        ((ht2.const_mul (A.2 - B.2)).div_const 2)
    have hraw :=
      (hinside.const_mul (A.1 - B.1)).add
        ((hasDerivAt_id t).const_mul (A.2 - B.2))
    convert hraw using 1
    dsimp [K]
    rw [(segment_hasDerivAt_fst A B t).deriv,
      (segment_hasDerivAt_snd A B t).deriv]
    simp [segment]
    ring
  have hcont :
      Continuous
        (fun t =>
          (segment B A t).2 *
              deriv (fun s => (segment B A s).1) t +
            (1 : ℝ) *
              deriv (fun s => (segment B A s).2) t) := by
    simp_rw [(segment_hasDerivAt_fst A B _).deriv,
      (segment_hasDerivAt_snd A B _).deriv]
    simp [segment]
    fun_prop
  unfold segmentAuxIntegral pathIntegral
  calc
    _ = K 1 - K 0 := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hK t)
        (hcont.intervalIntegrable 0 1)
    _ = A.2 - B.2 +
        (A.1 - B.1) * (A.2 + B.2) / 2 := by
      dsimp [K]
      ring

private theorem pathIntegral_segment_formula
    (φ dφ : ℝ → ℝ) (m : ℝ) (A B : ℝ × ℝ)
    (hφ : ∀ y, HasDerivAt φ (dφ y) y)
    (hdφ : Continuous dφ) :
    pathIntegral (P φ m) (Q dφ m) (segment B A) =
      potential φ A - potential φ B -
        m * segmentAuxIntegral A B := by
  have hφcont : Continuous φ :=
    continuous_iff_continuousAt.2 fun y =>
      (hφ y).continuousAt
  let exactPart : ℝ → ℝ := fun t =>
    P φ 0 (segment B A t).1 (segment B A t).2 *
        deriv (fun s => (segment B A s).1) t +
      Q dφ 0 (segment B A t).1 (segment B A t).2 *
        deriv (fun s => (segment B A s).2) t
  let auxPart : ℝ → ℝ := fun t =>
    (segment B A t).2 *
        deriv (fun s => (segment B A s).1) t +
      (1 : ℝ) * deriv (fun s => (segment B A s).2) t
  have hexact :
      Continuous exactPart := by
    dsimp [exactPart]
    simp_rw [(segment_hasDerivAt_fst A B _).deriv,
      (segment_hasDerivAt_snd A B _).deriv]
    simp only [P, Q, zero_mul, sub_zero]
    fun_prop
  have haux :
      Continuous auxPart := by
    dsimp [auxPart]
    simp_rw [(segment_hasDerivAt_fst A B _).deriv,
      (segment_hasDerivAt_snd A B _).deriv]
    fun_prop
  have hexactInt :
      (∫ t in (0 : ℝ)..1, exactPart t) =
        potential φ A - potential φ B := by
    calc
      _ = potential φ (segment B A 1) -
          potential φ (segment B A 0) := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => by
            simpa [exactPart] using
              potential_segment_hasDerivAt
                φ dφ A B hφ t)
          (hexact.intervalIntegrable 0 1)
      _ = potential φ A - potential φ B := by
        simp [segment]
  have hauxInt :
      (∫ t in (0 : ℝ)..1, auxPart t) =
        segmentAuxIntegral A B := by
    rfl
  have hmaux :
      (∫ t in (0 : ℝ)..1, m * auxPart t) =
        m * ∫ t in (0 : ℝ)..1, auxPart t := by
    exact intervalIntegral.integral_const_mul
      (a := (0 : ℝ)) (b := (1 : ℝ))
      m auxPart
  unfold pathIntegral
  calc
    (∫ t in (0 : ℝ)..1,
      P φ m (segment B A t).1 (segment B A t).2 *
          deriv (fun s => (segment B A s).1) t +
        Q dφ m (segment B A t).1 (segment B A t).2 *
          deriv (fun s => (segment B A s).2) t) =
        ∫ t in (0 : ℝ)..1,
          exactPart t - m * auxPart t := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [exactPart, auxPart]
      simp only [P, Q]
      ring
    _ = (∫ t in (0 : ℝ)..1, exactPart t) -
        m * ∫ t in (0 : ℝ)..1, auxPart t := by
      calc
        _ = (∫ t in (0 : ℝ)..1, exactPart t) -
            ∫ t in (0 : ℝ)..1, m * auxPart t := by
          exact intervalIntegral.integral_sub
            (hexact.intervalIntegrable 0 1)
            ((continuous_const.mul haux).intervalIntegrable 0 1)
        _ = _ := by rw [hmaux]
    _ = potential φ A - potential φ B -
        m * segmentAuxIntegral A B := by
      rw [hexactInt, hauxInt]

theorem gap1
    (φ dφ : ℝ → ℝ) (m : ℝ) (γ : ℝ → ℝ × ℝ)
    (A B : ℝ × ℝ) :
    closedIntegral (P φ m) (Q dφ m) γ A B =
      pathIntegral (P φ m) (Q dφ m) γ +
        pathIntegral (P φ m) (Q dφ m) (segment B A) := by
  rfl

theorem gap2
    (φ dφ : ℝ → ℝ) (m : ℝ) (γ : ℝ → ℝ × ℝ)
    (A B : ℝ × ℝ) (D : Set (ℝ × ℝ))
    (hφ : ∀ y, HasDerivAt φ (dφ y) y)
    (hdφ : Continuous dφ)
    (hBoundary : IsPositiveGreenBoundary γ A B D) :
    closedIntegral (P φ m) (Q dφ m) γ A B =
      regionIntegral D m := by
  have hqx :
      (fun z : ℝ × ℝ =>
        deriv (fun x => Q dφ m x z.2) z.1) =
        fun z => dφ z.2 * Real.exp z.1 := by
    funext z
    exact (hasDerivAt_Q_x dφ m z.1 z.2).deriv
  have hpy :
      (fun z : ℝ × ℝ =>
        deriv (fun y => P φ m z.1 y) z.2) =
        fun z => dφ z.2 * Real.exp z.1 - m := by
    funext z
    exact (hasDerivAt_P_y φ dφ m z.1 z.2 hφ).deriv
  have hcx :
      Continuous
        (fun z : ℝ × ℝ =>
          deriv (fun x => Q dφ m x z.2) z.1) := by
    rw [hqx]
    exact (hdφ.comp continuous_snd).mul
      (Real.continuous_exp.comp continuous_fst)
  have hcy :
      Continuous
        (fun z : ℝ × ℝ =>
          deriv (fun y => P φ m z.1 y) z.2) := by
    rw [hpy]
    exact ((hdφ.comp continuous_snd).mul
      (Real.continuous_exp.comp continuous_fst)).sub
        continuous_const
  have hgreen :=
    hBoundary.2.2 (P φ m) (Q dφ m) hcx hcy
  rw [hgreen]
  unfold regionIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change
      deriv (fun x => Q dφ m x z.2) z.1 -
          deriv (fun y => P φ m z.1 y) z.2 =
        m
    rw [congrFun hqx z, congrFun hpy z]
    ring

theorem gap3
    (D : Set (ℝ × ℝ)) (m S : ℝ)
    (hInt : IntegrableOn (fun _z : ℝ × ℝ => (1 : ℝ)) D)
    (hArea : regionArea D = S) :
    regionIntegral D m = m * S := by
  unfold regionIntegral regionArea at *
  calc
    (∫ _z in D, m) =
        ∫ _z in D, m * (1 : ℝ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _z => by ring
    _ = m * ∫ _z in D, (1 : ℝ) := by
      rw [integral_const_mul]
    _ = m * S := by rw [hArea]

theorem gap4
    (φ dφ : ℝ → ℝ) (m S : ℝ) (γ : ℝ → ℝ × ℝ)
    (A B : ℝ × ℝ) (D : Set (ℝ × ℝ))
    (hφ : ∀ y, HasDerivAt φ (dφ y) y)
    (hdφ : Continuous dφ)
    (hBoundary : IsPositiveGreenBoundary γ A B D)
    (hInt : IntegrableOn (fun _z : ℝ × ℝ => (1 : ℝ)) D)
    (hArea : regionArea D = S) :
    closedIntegral (P φ m) (Q dφ m) γ A B = m * S := by
  rw [gap2 φ dφ m γ A B D hφ hdφ hBoundary,
    gap3 D m S hInt hArea]

theorem gap5
    (φ dφ : ℝ → ℝ) (m : ℝ) (A B : ℝ × ℝ)
    (hφ : ∀ y, HasDerivAt φ (dφ y) y)
    (hdφ : Continuous dφ) :
    pathIntegral (P φ m) (Q dφ m) (segment B A) =
      potential φ A - potential φ B -
        m * segmentAuxIntegral A B := by
  exact pathIntegral_segment_formula φ dφ m A B hφ hdφ

theorem gap6
    (φ dφ : ℝ → ℝ) (m : ℝ)
    (x₁ y₁ x₂ y₂ : ℝ)
    (hφ : ∀ y, HasDerivAt φ (dφ y) y)
    (hdφ : Continuous dφ) :
    pathIntegral (P φ m) (Q dφ m)
        (segment (x₂, y₂) (x₁, y₁)) =
      Real.exp x₁ * φ y₁ - Real.exp x₂ * φ y₂ +
        m * (y₂ - y₁) +
        m / 2 * (x₂ - x₁) * (y₂ + y₁) := by
  rw [gap5 φ dφ m (x₁, y₁) (x₂, y₂) hφ hdφ,
    segmentAux_value]
  simp only [potential, Prod.fst, Prod.snd]
  ring

theorem gap7
    (φ dφ : ℝ → ℝ) (m S : ℝ) (γ : ℝ → ℝ × ℝ)
    (x₁ y₁ x₂ y₂ : ℝ) (D : Set (ℝ × ℝ))
    (hφ : ∀ y, HasDerivAt φ (dφ y) y)
    (hdφ : Continuous dφ)
    (hBoundary :
      IsPositiveGreenBoundary γ (x₁, y₁) (x₂, y₂) D)
    (hInt : IntegrableOn (fun _z : ℝ × ℝ => (1 : ℝ)) D)
    (hArea : regionArea D = S) :
    pathIntegral (P φ m) (Q dφ m) γ =
      m * S + Real.exp x₂ * φ y₂ - Real.exp x₁ * φ y₁ -
        m * (y₂ - y₁) -
        m / 2 * (x₂ - x₁) * (y₂ + y₁) := by
  have hc :=
    gap4 φ dφ m S γ (x₁, y₁) (x₂, y₂) D
      hφ hdφ hBoundary hInt hArea
  have hs :=
    gap6 φ dφ m x₁ y₁ x₂ y₂ hφ hdφ
  unfold closedIntegral at hc
  rw [hs] at hc
  linarith

end

end ProofGap.Exercise4304
