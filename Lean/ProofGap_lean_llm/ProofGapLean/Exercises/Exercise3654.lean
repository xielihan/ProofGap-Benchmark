import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise3654

open Filter

noncomputable section

structure Point2 where
  x : ℝ
  y : ℝ
  deriving DecidableEq

def z (p : Point2) : ℝ :=
  p.x * p.y

def constraintLine : Set Point2 :=
  {p | p.x + p.y = 1}

def lagrangian (x y lam : ℝ) : ℝ :=
  x * y + lam * (x + y - 1)

def LagrangeStationary (x y lam : ℝ) : Prop :=
  y + lam = 0 ∧ x + lam = 0 ∧ x + y = 1

def candidate : Point2 :=
  ⟨1 / 2, 1 / 2⟩

def IsUniqueGlobalMaximizerOn (p : Point2) : Prop :=
  p ∈ constraintLine ∧
    (∀ q ∈ constraintLine, z q ≤ z p) ∧
    (∀ q ∈ constraintLine, z q = z p → q = p)

def minimumPointsOn : Set Point2 :=
  {p | p ∈ constraintLine ∧
    ∀ q ∈ constraintLine, z p ≤ z q}

theorem gap1 (x y lam : ℝ) :
    LagrangeStationary x y lam → x = 1 / 2 := by
  rintro ⟨hy, hx, hsum⟩
  linarith

theorem gap2 (x y lam : ℝ) :
    LagrangeStationary x y lam → y = 1 / 2 := by
  rintro ⟨hy, hx, hsum⟩
  linarith

theorem gap3 :
    z candidate = 1 / 4 := by
  norm_num [z, candidate]

theorem gap4 :
    LagrangeStationary (1 / 2) (1 / 2) (-1 / 2) := by
  norm_num [LagrangeStationary]

theorem gap5 :
    Tendsto (fun x : ℝ => 1 - x) atTop atBot := by
  refine tendsto_atBot.2 (fun b => ?_)
  exact (eventually_ge_atTop (1 - b)).mono (fun x hx => by
    linarith)

theorem gap6 :
    Tendsto (fun x : ℝ => 1 - x) atBot atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  exact (eventually_le_atBot (1 - b)).mono (fun x hx => by
    linarith)

theorem gap7 :
    Tendsto (fun x : ℝ => z ⟨x, 1 - x⟩) atTop atBot ∧
      Tendsto (fun x : ℝ => z ⟨x, 1 - x⟩) atBot atBot := by
  constructor
  · refine tendsto_atBot.2 (fun b => ?_)
    exact (eventually_ge_atTop (max 1 (1 - b))).mono (fun x hx => by
      have hx1 : 1 ≤ x := le_trans (le_max_left 1 (1 - b)) hx
      have hxb : 1 - b ≤ x := le_trans (le_max_right 1 (1 - b)) hx
      dsimp [z]
      nlinarith [sq_nonneg (x - 1)])
  · refine tendsto_atBot.2 (fun b => ?_)
    exact (eventually_le_atBot (min 0 b)).mono (fun x hx => by
      have hx0 : x ≤ 0 := le_trans hx (min_le_left 0 b)
      have hxb : x ≤ b := le_trans hx (min_le_right 0 b)
      dsimp [z]
      nlinarith [sq_nonneg x])

theorem gap8 :
    IsUniqueGlobalMaximizerOn candidate := by
  unfold IsUniqueGlobalMaximizerOn
  refine ⟨?_, ?_, ?_⟩
  · norm_num [constraintLine, candidate]
  · intro q hq
    change q.x + q.y = 1 at hq
    change q.x * q.y ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ)
    have hy : q.y = 1 - q.x := by
      linarith
    rw [hy]
    nlinarith [sq_nonneg (q.x - (1 / 2 : ℝ))]
  · intro q hq hz
    change q.x + q.y = 1 at hq
    change q.x * q.y = (1 / 2 : ℝ) * (1 / 2 : ℝ) at hz
    have hyExpr : q.y = 1 - q.x := by
      linarith
    rw [hyExpr] at hz
    have hx : q.x = (1 / 2 : ℝ) := by
      nlinarith [sq_nonneg (q.x - (1 / 2 : ℝ))]
    have hy : q.y = (1 / 2 : ℝ) := by
      linarith
    change (⟨q.x, q.y⟩ : Point2) = ⟨(1 / 2 : ℝ), (1 / 2 : ℝ)⟩
    rw [hx, hy]

theorem gap9 :
    z candidate = 1 / 4 := by
  exact gap3

theorem gap10 :
    minimumPointsOn = ∅ := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases hp with ⟨_, hmin⟩
    let t : ℝ := |z p| + 2
    let q : Point2 := ⟨t, 1 - t⟩
    have hq : q ∈ constraintLine := by
      simp [q, constraintLine]
    have hle : z p ≤ z q := hmin q hq
    have hs : -|z p| ≤ z p := neg_abs_le _
    have hqneg : z q < -|z p| := by
      change (|p.x * p.y| + 2) * (1 - (|p.x * p.y| + 2)) < -|p.x * p.y|
      nlinarith [abs_nonneg (p.x * p.y), sq_nonneg (|p.x * p.y|)]
    have hzlt : z q < z p := lt_of_lt_of_le hqneg hs
    exact (not_lt_of_ge hle hzlt).elim
  · intro p hp
    exact hp.elim

end

end ProofGap.Exercise3654
