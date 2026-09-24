import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1316

noncomputable section

def adjusted (f : ℝ → ℝ) (ξ x : ℝ) : ℝ :=
  f x - deriv f ξ * x

def PositiveCurvatureNear (f : ℝ → ℝ) (a b ξ : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    Set.Icc (ξ - δ) (ξ + δ) ⊆ Set.Ioo a b ∧
    ContDiffOn ℝ 2 f (Set.Icc (ξ - δ) (ξ + δ)) ∧
    ∀ x ∈ Set.Ioo (ξ - δ) (ξ + δ),
      0 < deriv (deriv f) x

private theorem adjusted_deriv_aux (f : ℝ → ℝ) (ξ x : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    deriv (adjusted f ξ) x = deriv f x - deriv f ξ := by
  have hlin : HasDerivAt (fun y : ℝ => deriv f ξ * y) (deriv f ξ) x := by
    simpa using (hasDerivAt_const x (deriv f ξ)).mul (hasDerivAt_id x)
  simpa only [adjusted] using (hf.hasDerivAt.sub hlin).deriv

private theorem adjusted_second_deriv_aux (f : ℝ → ℝ) (ξ x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (adjusted f ξ)) x = deriv (deriv f) x := by
  have hevent :
      (fun y => deriv (adjusted f ξ) y) =ᶠ[nhds x]
        (fun y => deriv f y - deriv f ξ) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact adjusted_deriv_aux f ξ y (hy.differentiableAt (by decide))
  calc
    deriv (deriv (adjusted f ξ)) x =
        deriv (fun y => deriv f y - deriv f ξ) x := hevent.deriv_eq
    _ = deriv (deriv f) x := by
      by_cases hd : DifferentiableAt ℝ (deriv f) x
      · simpa using (hd.hasDerivAt.sub_const (deriv f ξ)).deriv
      · have hconst : DifferentiableAt ℝ (fun _ : ℝ => deriv f ξ) x :=
          differentiableAt_const (c := deriv f ξ)
        have hnot :
            ¬DifferentiableAt ℝ (fun y => deriv f y - deriv f ξ) x := by
          intro hs
          apply hd
          have hadd :
              DifferentiableAt ℝ
                ((fun y : ℝ => deriv f y - deriv f ξ) +
                  (fun _ : ℝ => deriv f ξ)) x :=
            hs.add hconst
          have heq :
              (fun y : ℝ => deriv f y - deriv f ξ) +
                  (fun _ : ℝ => deriv f ξ) = deriv f := by
            funext y
            exact sub_add_cancel (deriv f y) (deriv f ξ)
          rw [heq] at hadd
          exact hadd
        rw [deriv_zero_of_not_differentiableAt hnot,
          deriv_zero_of_not_differentiableAt hd]

private theorem exists_value_in_open_of_lt
    (f : ℝ → ℝ) (l u y : ℝ) (hlu : l < u)
    (hcont : ContinuousOn f (Set.Icc l u))
    (hy : y ∈ Set.Ioo (f l) (f u)) :
    ∃ x ∈ Set.Ioo l u, f x = y := by
  have hyc : y ∈ Set.Icc (f l) (f u) := ⟨hy.1.le, hy.2.le⟩
  rcases intermediate_value_Icc (f := f) hlu.le hcont hyc with ⟨x, hx, hxy⟩
  have hxl : l < x := by
    apply lt_of_le_of_ne hx.1
    intro heq
    have heq' : x = l := heq.symm
    subst x
    have hbad := hy.1
    rw [hxy] at hbad
    exact (lt_irrefl y) hbad
  have hxu : x < u := by
    apply lt_of_le_of_ne hx.2
    intro heq
    subst x
    have hbad := hy.2
    rw [hxy] at hbad
    exact (lt_irrefl y) hbad
  exact ⟨x, ⟨hxl, hxu⟩, hxy⟩

private theorem exists_value_in_open_of_gt
    (f : ℝ → ℝ) (l u y : ℝ) (hlu : l < u)
    (hcont : ContinuousOn f (Set.Icc l u))
    (hy : y ∈ Set.Ioo (f u) (f l)) :
    ∃ x ∈ Set.Ioo l u, f x = y := by
  have hneg : ContinuousOn (fun x => -f x) (Set.Icc l u) := hcont.neg
  have hny : -y ∈ Set.Ioo (-f l) (-f u) :=
    ⟨neg_lt_neg hy.2, neg_lt_neg hy.1⟩
  rcases exists_value_in_open_of_lt (fun x => -f x) l u (-y) hlu hneg hny with
    ⟨x, hx, hxy⟩
  have heq : f x = y := by linarith [hxy]
  exact ⟨x, hx, heq⟩

private theorem curvature_shape_aux (f : ℝ → ℝ) (a b ξ : ℝ)
    (hcurv : PositiveCurvatureNear f a b ξ)
    (hcrit : deriv f ξ = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      Set.Icc (ξ - δ) (ξ + δ) ⊆ Set.Ioo a b ∧
      ContinuousOn f (Set.Icc (ξ - δ) (ξ + δ)) ∧
      StrictAntiOn f (Set.Icc (ξ - δ) ξ) ∧
      StrictMonoOn f (Set.Icc ξ (ξ + δ)) := by
  rcases hcurv with ⟨r, hr, hsub, hcd, hpos⟩
  have hcont : ContinuousOn f (Set.Icc (ξ - r) (ξ + r)) := hcd.continuousOn
  have hderivCont : ContinuousOn (deriv f) (Set.Ioo (ξ - r) (ξ + r)) := by
    intro x hx
    have hdiff : DifferentiableAt ℝ (deriv f) x := by
      by_contra hnd
      have hz : deriv (deriv f) x = 0 :=
        deriv_zero_of_not_differentiableAt hnd
      have hp := hpos x hx
      rw [hz] at hp
      exact (lt_irrefl 0) hp
    exact hdiff.continuousAt.continuousWithinAt
  have hdmono : StrictMonoOn (deriv f) (Set.Ioo (ξ - r) (ξ + r)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (ξ - r) (ξ + r)) hderivCont
    intro x hx
    apply hpos x
    simpa only [interior_Ioo] using hx
  have hξopen : ξ ∈ Set.Ioo (ξ - r) (ξ + r) := ⟨by linarith, by linarith⟩
  have hleftCont : ContinuousOn f (Set.Icc (ξ - r) ξ) :=
    hcont.mono fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hrightCont : ContinuousOn f (Set.Icc ξ (ξ + r)) :=
    hcont.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hnegmono : StrictMonoOn (fun x : ℝ => -f x) (Set.Icc (ξ - r) ξ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (ξ - r) ξ) hleftCont.neg
    intro x hx
    have hxio : x ∈ Set.Ioo (ξ - r) ξ := by
      simpa only [interior_Icc] using hx
    have hxopen : x ∈ Set.Ioo (ξ - r) (ξ + r) :=
      ⟨hxio.1, by linarith [hxio.2]⟩
    have hlt := hdmono hxopen hξopen hxio.2
    have hfneg : deriv f x < 0 := by simpa only [hcrit] using hlt
    have hfat : ContDiffAt ℝ 2 f x :=
      hcd.contDiffAt (Icc_mem_nhds hxopen.1 hxopen.2)
    have hfdiff : DifferentiableAt ℝ f x :=
      hfat.differentiableAt (by decide)
    have hnegderiv : deriv (fun y : ℝ => -f y) x = -deriv f x := by
      simpa only [Pi.neg_apply] using hfdiff.hasDerivAt.neg.deriv
    rw [hnegderiv]
    exact neg_pos.mpr hfneg
  have hanti : StrictAntiOn f (Set.Icc (ξ - r) ξ) := by
    intro x hx y hy hxy
    have hn := hnegmono hx hy hxy
    linarith [hn]
  have hmono : StrictMonoOn f (Set.Icc ξ (ξ + r)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ξ (ξ + r)) hrightCont
    intro x hx
    have hxio : x ∈ Set.Ioo ξ (ξ + r) := by
      simpa only [interior_Icc] using hx
    have hxopen : x ∈ Set.Ioo (ξ - r) (ξ + r) :=
      ⟨by linarith [hxio.1], hxio.2⟩
    have hlt := hdmono hξopen hxopen hxio.1
    simpa only [hcrit] using hlt
  exact ⟨r, hr, hsub, hcont, hanti, hmono⟩

private theorem adjusted_pair_aux (f : ℝ → ℝ) (a b ξ : ℝ)
    (hcurv : PositiveCurvatureNear f a b ξ) :
    ∃ x₁ ∈ Set.Ioo a b, ∃ x₂ ∈ Set.Ioo a b,
      x₁ < ξ ∧ ξ < x₂ ∧ adjusted f ξ x₁ = adjusted f ξ x₂ := by
  rcases hcurv with ⟨r, hr, hsub, hcd, hpos⟩
  have hlin : ContDiffOn ℝ 2 (fun x : ℝ => deriv f ξ * x)
      (Set.Icc (ξ - r) (ξ + r)) :=
    contDiffOn_const.mul contDiffOn_id
  have hgcd : ContDiffOn ℝ 2 (adjusted f ξ)
      (Set.Icc (ξ - r) (ξ + r)) := by
    simpa only [adjusted] using hcd.sub hlin
  have hgpos : ∀ x ∈ Set.Ioo (ξ - r) (ξ + r),
      0 < deriv (deriv (adjusted f ξ)) x := by
    intro x hx
    have hfat : ContDiffAt ℝ 2 f x :=
      hcd.contDiffAt (Icc_mem_nhds hx.1 hx.2)
    rw [adjusted_second_deriv_aux f ξ x hfat]
    exact hpos x hx
  have hgcurv : PositiveCurvatureNear (adjusted f ξ) a b ξ :=
    ⟨r, hr, hsub, hgcd, hgpos⟩
  have hξopen : ξ ∈ Set.Ioo (ξ - r) (ξ + r) := ⟨by linarith, by linarith⟩
  have hfatξ : ContDiffAt ℝ 2 f ξ :=
    hcd.contDiffAt (Icc_mem_nhds hξopen.1 hξopen.2)
  have hfdiff : DifferentiableAt ℝ f ξ :=
    hfatξ.differentiableAt (by decide)
  have hgcrit : deriv (adjusted f ξ) ξ = 0 := by
    rw [adjusted_deriv_aux f ξ ξ hfdiff]
    exact sub_self (deriv f ξ)
  rcases curvature_shape_aux (adjusted f ξ) a b ξ hgcurv hgcrit with
    ⟨δ, hδ, hsub', hcont, hanti, hmono⟩
  have hl : ξ - δ ∈ Set.Icc (ξ - δ) (ξ + δ) := ⟨le_rfl, by linarith⟩
  have hr' : ξ + δ ∈ Set.Icc (ξ - δ) (ξ + δ) := ⟨by linarith, le_rfl⟩
  have hlc : ξ - δ ∈ Set.Icc (ξ - δ) ξ := ⟨le_rfl, by linarith⟩
  have hcl : ξ ∈ Set.Icc (ξ - δ) ξ := ⟨by linarith, le_rfl⟩
  have hcr : ξ ∈ Set.Icc ξ (ξ + δ) := ⟨le_rfl, by linarith⟩
  have hrr : ξ + δ ∈ Set.Icc ξ (ξ + δ) := ⟨by linarith, le_rfl⟩
  have hleftlow : adjusted f ξ ξ < adjusted f ξ (ξ - δ) :=
    hanti hlc hcl (by linarith)
  have hrightlow : adjusted f ξ ξ < adjusted f ξ (ξ + δ) :=
    hmono hcr hrr (by linarith)
  have hleftCont : ContinuousOn (adjusted f ξ) (Set.Icc (ξ - δ) ξ) :=
    hcont.mono fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hrightCont : ContinuousOn (adjusted f ξ) (Set.Icc ξ (ξ + δ)) :=
    hcont.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩
  rcases lt_trichotomy (adjusted f ξ (ξ + δ)) (adjusted f ξ (ξ - δ)) with
      hcmp | heq | hcmp
  · rcases exists_value_in_open_of_gt (adjusted f ξ) (ξ - δ) ξ
        (adjusted f ξ (ξ + δ)) (by linarith) hleftCont
        ⟨hrightlow, hcmp⟩ with ⟨x₁, hx₁, heq₁⟩
    have hx₁full : x₁ ∈ Set.Icc (ξ - δ) (ξ + δ) :=
      ⟨hx₁.1.le, by linarith [hx₁.2]⟩
    exact ⟨x₁, hsub' hx₁full, ξ + δ, hsub' hr', hx₁.2,
      by linarith, heq₁⟩
  · exact ⟨ξ - δ, hsub' hl, ξ + δ, hsub' hr', by linarith,
      by linarith, heq.symm⟩
  · rcases exists_value_in_open_of_lt (adjusted f ξ) ξ (ξ + δ)
        (adjusted f ξ (ξ - δ)) (by linarith) hrightCont
        ⟨hleftlow, hcmp⟩ with ⟨x₂, hx₂, heq₂⟩
    have hx₂full : x₂ ∈ Set.Icc (ξ - δ) (ξ + δ) :=
      ⟨by linarith [hx₂.1], hx₂.2.le⟩
    exact ⟨ξ - δ, hsub' hl, x₂, hsub' hx₂full, by linarith,
      hx₂.1, heq₂.symm⟩

theorem gap1 (f : ℝ → ℝ) (a b ξ : ℝ)
    (hcurv : PositiveCurvatureNear f a b ξ)
    (hcrit : deriv f ξ = 0) :
    IsLocalMin f ξ := by
  rcases curvature_shape_aux f a b ξ hcurv hcrit with
    ⟨δ, hδ, hsub, hcont, hanti, hmono⟩
  have hnhds : Set.Icc (ξ - δ) (ξ + δ) ∈ nhds ξ :=
    Icc_mem_nhds (sub_lt_self ξ hδ) (lt_add_of_pos_right ξ hδ)
  filter_upwards [hnhds] with x hx
  rcases lt_trichotomy x ξ with hlt | rfl | hgt
  · exact (hanti ⟨hx.1, hlt.le⟩ ⟨by linarith, le_rfl⟩ hlt).le
  · exact le_rfl
  · exact (hmono ⟨le_rfl, by linarith⟩ ⟨hgt.le, hx.2⟩ hgt).le

theorem gap2 (f : ℝ → ℝ) (a b ξ : ℝ)
    (hcurv : PositiveCurvatureNear f a b ξ)
    (hcrit : deriv f ξ = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      Set.Icc (ξ - δ) (ξ + δ) ⊆ Set.Ioo a b ∧
      StrictAntiOn f (Set.Icc (ξ - δ) ξ) ∧
      StrictMonoOn f (Set.Icc ξ (ξ + δ)) := by
  rcases curvature_shape_aux f a b ξ hcurv hcrit with
    ⟨δ, hδ, hsub, hcont, hanti, hmono⟩
  exact ⟨δ, hδ, hsub, hanti, hmono⟩

theorem gap3 (f : ℝ → ℝ) (ξ x₁ x₂ : ℝ)
    (hcrit : deriv f ξ = 0) (hne : x₁ ≠ x₂)
    (heq : f x₁ = f x₂) :
    (f x₂ - f x₁) / (x₂ - x₁) = deriv f ξ := by
  simp [heq, hcrit]

theorem gap4 (f : ℝ → ℝ) (ξ δ x₁ : ℝ)
    (hleft : StrictAntiOn f (Set.Icc (ξ - δ) ξ))
    (hx₁ : x₁ ∈ Set.Ioo (ξ - δ) ξ) :
    f x₁ ∈ Set.Ioo (f ξ) (f (ξ - δ)) := by
  have hends : ξ - δ < ξ := lt_trans hx₁.1 hx₁.2
  constructor
  · exact hleft ⟨hx₁.1.le, hx₁.2.le⟩ ⟨hends.le, le_rfl⟩ hx₁.2
  · exact hleft ⟨le_rfl, hends.le⟩ ⟨hx₁.1.le, hx₁.2.le⟩ hx₁.1

theorem gap5 (f : ℝ → ℝ) (ξ δ x₁ : ℝ)
    (hcont : ContinuousOn f (Set.Icc ξ (ξ + δ)))
    (hmono : StrictMonoOn f (Set.Icc ξ (ξ + δ)))
    (hδ : 0 < δ)
    (hy : f x₁ ∈ Set.Ioo (f ξ) (f (ξ + δ))) :
    ∃ x₂ ∈ Set.Ioo ξ (ξ + δ), f x₂ = f x₁ := by
  exact exists_value_in_open_of_lt f ξ (ξ + δ) (f x₁)
    (by linarith) hcont hy

theorem gap6 (f : ℝ → ℝ) (ξ x₁ x₂ : ℝ)
    (hcrit : deriv f ξ = 0) (h12 : x₁ < x₂)
    (heq : f x₁ = f x₂) :
    (f x₂ - f x₁) / (x₂ - x₁) = deriv f ξ := by
  exact gap3 f ξ x₁ x₂ hcrit (ne_of_lt h12) heq

theorem gap7 (f : ℝ → ℝ) (ξ δ : ℝ)
    (hcont : ContinuousOn f (Set.Icc (ξ - δ) ξ))
    (hanti : StrictAntiOn f (Set.Icc (ξ - δ) ξ))
    (hmono : StrictMonoOn f (Set.Icc ξ (ξ + δ)))
    (hδ : 0 < δ) (hcmp : f (ξ + δ) < f (ξ - δ)) :
    ∃ x₁ ∈ Set.Ioo (ξ - δ) ξ, f x₁ = f (ξ + δ) := by
  have hξright : ξ ∈ Set.Icc ξ (ξ + δ) := ⟨le_rfl, by linarith⟩
  have hright : ξ + δ ∈ Set.Icc ξ (ξ + δ) := ⟨by linarith, le_rfl⟩
  have hlow : f ξ < f (ξ + δ) := hmono hξright hright (by linarith)
  exact exists_value_in_open_of_gt f (ξ - δ) ξ (f (ξ + δ))
    (by linarith) hcont ⟨hlow, hcmp⟩

theorem gap8 (f : ℝ → ℝ) (ξ x₁ x₂ : ℝ)
    (hcrit : deriv f ξ = 0) (h12 : x₁ < x₂)
    (heq : f x₁ = f x₂) :
    (f x₂ - f x₁) / (x₂ - x₁) = deriv f ξ := by
  exact gap3 f ξ x₁ x₂ hcrit (ne_of_lt h12) heq

theorem gap9 (f : ℝ → ℝ) (ξ : ℝ)
    (hf : DifferentiableAt ℝ f ξ) :
    deriv (adjusted f ξ) ξ = deriv f ξ - deriv f ξ := by
  exact adjusted_deriv_aux f ξ ξ hf

theorem gap10 (f : ℝ → ℝ) (ξ : ℝ) :
    deriv f ξ - deriv f ξ = 0 := by
  exact sub_self (deriv f ξ)

theorem gap11 (f : ℝ → ℝ) (ξ : ℝ)
    (hf : DifferentiableAt ℝ f ξ) :
    deriv (adjusted f ξ) ξ = 0 := by
  rw [gap9 f ξ hf, gap10 f ξ]

theorem gap12 (f : ℝ → ℝ) (ξ : ℝ)
    (hf : ContDiffAt ℝ 2 f ξ) :
    deriv (deriv (adjusted f ξ)) ξ =
      deriv (deriv f) ξ := by
  exact adjusted_second_deriv_aux f ξ ξ hf

theorem gap13 (f : ℝ → ℝ) (ξ : ℝ)
    (hpos : 0 < deriv (deriv f) ξ) :
    0 < deriv (deriv f) ξ := by
  exact hpos

theorem gap14 (f : ℝ → ℝ) (ξ : ℝ)
    (hf : ContDiffAt ℝ 2 f ξ)
    (hpos : 0 < deriv (deriv f) ξ) :
    0 < deriv (deriv (adjusted f ξ)) ξ := by
  rw [gap12 f ξ hf]
  exact hpos

theorem gap15 (f : ℝ → ℝ) (a b ξ : ℝ)
    (hcurv : PositiveCurvatureNear f a b ξ) :
    ∃ x₁ x₂ : ℝ, x₁ < ξ ∧ ξ < x₂ ∧
      adjusted f ξ x₁ = adjusted f ξ x₂ := by
  rcases adjusted_pair_aux f a b ξ hcurv with
    ⟨x₁, hx₁, x₂, hx₂, h₁, h₂, heq⟩
  exact ⟨x₁, x₂, h₁, h₂, heq⟩

theorem gap16 (f : ℝ → ℝ) (ξ x₁ x₂ : ℝ)
    (heq : adjusted f ξ x₁ = adjusted f ξ x₂) :
    f x₁ - deriv f ξ * x₁ =
      f x₂ - deriv f ξ * x₂ := by
  simpa only [adjusted] using heq

theorem gap17 (f : ℝ → ℝ) (ξ x₁ x₂ : ℝ)
    (h12 : x₁ < x₂)
    (heq : adjusted f ξ x₁ = adjusted f ξ x₂) :
    deriv f ξ = (f x₂ - f x₁) / (x₂ - x₁) := by
  have hne : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt h12)
  apply (eq_div_iff hne).2
  have h := gap16 f ξ x₁ x₂ heq
  nlinarith [h]

theorem gap18 (f : ℝ → ℝ) (a b ξ : ℝ)
    (hξ : ξ ∈ Set.Ioo a b)
    (hcurv : PositiveCurvatureNear f a b ξ) :
    ∃ x₁ ∈ Set.Ioo a b, ∃ x₂ ∈ Set.Ioo a b,
      x₁ < x₂ ∧
      (f x₂ - f x₁) / (x₂ - x₁) = deriv f ξ := by
  rcases adjusted_pair_aux f a b ξ hcurv with
    ⟨x₁, hx₁, x₂, hx₂, h₁, h₂, heq⟩
  have h12 : x₁ < x₂ := lt_trans h₁ h₂
  have hs := gap17 f ξ x₁ x₂ h12 heq
  exact ⟨x₁, hx₁, x₂, hx₂, h12, hs.symm⟩

end

end ProofGap.Exercise1316
