import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1285

noncomputable section

def rightEndpoint (f : ℝ → ℝ) (a k : ℝ) : ℝ :=
  a - f a / k

def RootData (f : ℝ → ℝ) (a k : ℝ) : Prop :=
  0 < k ∧ f a < 0 ∧
    ContinuousOn f (Set.Ici a) ∧
    DifferentiableOn ℝ f (Set.Ioi a) ∧
    ∀ x ∈ Set.Ioi a, k < deriv f x

private theorem rightEndpoint_gt_of_rootData
    (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    a < rightEndpoint f a k := by
  have hquot : f a / k < 0 :=
    div_neg_of_neg_of_pos h.2.1 h.1
  unfold rightEndpoint
  linarith

theorem gap1 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    ∃ ξ ∈ Set.Ioo a (rightEndpoint f a k),
      f (rightEndpoint f a k) - f a =
        (rightEndpoint f a k - a) * deriv f ξ := by
  have hab : a < rightEndpoint f a k :=
    rightEndpoint_gt_of_rootData f a k h
  rcases h with ⟨hk, hfa, hcont, hdiff, hderiv⟩
  have hcont' : ContinuousOn f (Set.Icc a (rightEndpoint f a k)) := by
    exact hcont.mono (fun _ hx => hx.1)
  have hdiff' : DifferentiableOn ℝ f (Set.Ioo a (rightEndpoint f a k)) := by
    exact hdiff.mono (fun _ hx => hx.1)
  rcases exists_deriv_eq_slope f hab hcont' hdiff' with ⟨ξ, hξ, hξder⟩
  refine ⟨ξ, hξ, ?_⟩
  rw [hξder]
  have hne : rightEndpoint f a k - a ≠ 0 :=
    ne_of_gt (sub_pos.mpr hab)
  field_simp [hne]

theorem gap2 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    ∃ ξ ∈ Set.Ioo a (rightEndpoint f a k),
      -(f a / k) * deriv f ξ > -(f a / k) * k := by
  rcases gap1 f a k h with ⟨ξ, hξ, _⟩
  refine ⟨ξ, hξ, ?_⟩
  have hcoef : 0 < -(f a / k) := by
    exact neg_pos.mpr (div_neg_of_neg_of_pos h.2.1 h.1)
  exact mul_lt_mul_of_pos_left (h.2.2.2.2 ξ hξ.1) hcoef

theorem gap3 (f : ℝ → ℝ) (a k : ℝ) (hk : k ≠ 0) :
    -(f a / k) * k = -f a := by
  field_simp [hk]

theorem gap4 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    f (rightEndpoint f a k) - f a > -f a := by
  rcases gap1 f a k h with ⟨ξ, hξ, heq⟩
  have hcoef : 0 < -(f a / k) := by
    exact neg_pos.mpr (div_neg_of_neg_of_pos h.2.1 h.1)
  have hmul :
      -(f a / k) * deriv f ξ > -(f a / k) * k := by
    exact mul_lt_mul_of_pos_left (h.2.2.2.2 ξ hξ.1) hcoef
  calc
    f (rightEndpoint f a k) - f a =
        (rightEndpoint f a k - a) * deriv f ξ := heq
    _ = -(f a / k) * deriv f ξ := by
      unfold rightEndpoint
      ring
    _ > -(f a / k) * k := hmul
    _ = -f a := gap3 f a k (ne_of_gt h.1)

theorem gap5 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    0 < f (rightEndpoint f a k) := by
  have hdiff := gap4 f a k h
  linarith

theorem gap6 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    f a < 0 := by
  exact h.2.1

theorem gap7 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    ∃ x ∈ Set.Ioo a (rightEndpoint f a k), f x = 0 := by
  have hab : a < rightEndpoint f a k :=
    rightEndpoint_gt_of_rootData f a k h
  have hcont : ContinuousOn f (Set.Icc a (rightEndpoint f a k)) := by
    exact h.2.2.1.mono (fun _ hx => hx.1)
  have hz :
      (0 : ℝ) ∈ Set.Icc (f a) (f (rightEndpoint f a k)) := by
    exact ⟨(gap6 f a k h).le, (gap5 f a k h).le⟩
  rcases intermediate_value_Icc hab.le hcont hz with ⟨x, hx, hfx⟩
  have hax_ne : a ≠ x := by
    intro hax
    subst x
    linarith [gap6 f a k h]
  have hxb_ne : x ≠ rightEndpoint f a k := by
    intro hxb
    subst x
    linarith [gap5 f a k h]
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 hax_ne, lt_of_le_of_ne hx.2 hxb_ne⟩, hfx⟩

theorem gap8 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    ∀ x ∈ Set.Ioi a, 0 < deriv f x := by
  intro x hx
  have hk := h.1
  have hd := h.2.2.2.2 x hx
  linarith

theorem gap9 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    StrictMonoOn f (Set.Ioi a) := by
  intro x hx y hy hxy
  have hcont : ContinuousOn f (Set.Icc x y) := by
    exact h.2.2.1.mono (fun _ hz => le_trans (le_of_lt hx) hz.1)
  have hdiff : DifferentiableOn ℝ f (Set.Ioo x y) := by
    exact h.2.2.2.1.mono (fun _ hz => lt_trans hx hz.1)
  rcases exists_deriv_eq_slope f hxy hcont hdiff with ⟨ξ, hξ, hslope⟩
  have hslope_pos : 0 < (f y - f x) / (y - x) := by
    rw [← hslope]
    exact gap8 f a k h ξ (lt_trans hx hξ.1)
  rcases (div_pos_iff.mp hslope_pos) with hpos | hneg
  · exact sub_pos.mp hpos.1
  · exact False.elim ((not_lt_of_ge (le_of_lt (sub_pos.mpr hxy))) hneg.2)

theorem gap10 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    ∃! x, x ∈ Set.Ioo a (rightEndpoint f a k) ∧ f x = 0 := by
  rcases gap7 f a k h with ⟨x, hx, hfx⟩
  refine ⟨x, ⟨hx, hfx⟩, ?_⟩
  intro y hy
  exact ((gap9 f a k h).injOn hx.1 hy.1.1 (hfx.trans hy.2.symm)).symm

theorem gap11 (f : ℝ → ℝ) (a k : ℝ) (h : RootData f a k) :
    ∃! x, x ∈ Set.Ioi a ∧ f x = 0 := by
  rcases gap7 f a k h with ⟨x, hx, hfx⟩
  refine ⟨x, ⟨hx.1, hfx⟩, ?_⟩
  intro y hy
  exact ((gap9 f a k h).injOn hx.1 hy.1 (hfx.trans hy.2.symm)).symm

end

end ProofGap.Exercise1285
