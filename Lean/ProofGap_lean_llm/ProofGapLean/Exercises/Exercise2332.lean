import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2332

noncomputable section

def energy (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, deriv f x ^ 2

def amplitude (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x ∈ Set.Icc a b, y = |f x|}

def squareValues (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {y : ℝ | ∃ x ∈ Set.Icc a b, y = f x ^ 2}

private noncomputable abbrev volume : MeasureTheory.Measure ℝ := MeasureTheory.volume

private theorem intervalIntegral.integral_add_adjacent {f : ℝ → ℝ} {a b c : ℝ} (hab : IntervalIntegrable f MeasureTheory.volume a b) (hbc : IntervalIntegrable f MeasureTheory.volume b c) : (∫ x in a..b, f x) + (∫ x in b..c, f x) = ∫ x in a..c, f x := intervalIntegral.integral_add_adjacent_intervals hab hbc

private theorem intervalIntegral.integral_mul_le_L2_mul_L2
    {g : ℝ → ℝ} {a b : ℝ}
    (_hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b)
    (_hg : IntervalIntegrable g volume a b)
    (hab : a ≤ b)
    (hcont : ContinuousOn g (Set.uIcc a b)) :
    (∫ t in a..b, g t) ^ 2 ≤
      (∫ _t in a..b, (1 : ℝ)) * ∫ t in a..b, g t ^ 2 := by
  by_cases heq : a = b
  · subst b
    simp
  · have hlt : a < b := lt_of_le_of_ne hab heq
    have hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b :=
      (hcont.pow 2).intervalIntegrable
    let I : ℝ := ∫ t in a..b, g t
    let c : ℝ := I / (b - a)
    have hlin :
        IntervalIntegrable (fun t : ℝ => (-2 * c) * g t) volume a b :=
      (continuousOn_const.mul hcont).intervalIntegrable
    have hconst :
        IntervalIntegrable (fun _ : ℝ => c ^ 2) volume a b :=
      continuousOn_const.intervalIntegrable
    have hpoly :
        (∫ t in a..b, (g t - c) ^ 2) =
          (∫ t in a..b, g t ^ 2) +
            ((-2 * c) * I + (b - a) * c ^ 2) := by
      calc
        (∫ t in a..b, (g t - c) ^ 2) =
            ∫ t in a..b, g t ^ 2 + ((-2 * c) * g t + c ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
        _ = (∫ t in a..b, g t ^ 2) +
              ∫ t in a..b, ((-2 * c) * g t + c ^ 2) :=
          intervalIntegral.integral_add hg2 (hlin.add hconst)
        _ = (∫ t in a..b, g t ^ 2) +
              ((-2 * c) * I + (b - a) * c ^ 2) := by
          rw [intervalIntegral.integral_add hlin hconst]
          simp [I]
    have hsquare : 0 ≤ ∫ t in a..b, (g t - c) ^ 2 :=
      intervalIntegral.integral_nonneg hab
        (fun t _ => sq_nonneg (g t - c))
    rw [hpoly] at hsquare
    have hc : c * (b - a) = I := by
      dsimp [c]
      exact div_mul_cancel₀ I (ne_of_gt (sub_pos.mpr hlt))
    have hsimplify :
        (∫ t in a..b, g t ^ 2) +
              ((-2 * c) * I + (b - a) * c ^ 2) =
          (∫ t in a..b, g t ^ 2) - c ^ 2 * (b - a) := by
      rw [← hc]
      ring
    rw [hsimplify] at hsquare
    have henergy : c ^ 2 * (b - a) ≤ ∫ t in a..b, g t ^ 2 := by
      linarith
    have hmul :
        (b - a) * (c ^ 2 * (b - a)) ≤
          (b - a) * ∫ t in a..b, g t ^ 2 :=
      mul_le_mul_of_nonneg_left henergy (sub_nonneg.mpr hab)
    have hfinal :
        I ^ 2 ≤ (b - a) * ∫ t in a..b, g t ^ 2 := by
      calc
        I ^ 2 = (c * (b - a)) ^ 2 := by rw [hc]
        _ = (b - a) * (c ^ 2 * (b - a)) := by ring
        _ ≤ (b - a) * ∫ t in a..b, g t ^ 2 := hmul
    simpa [I] using hfinal

theorem gap1 (f : ℝ → ℝ) (a b x : ℝ) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫ t in a..x, deriv f t) ^ 2 ≤
      (∫ _t in a..x, (1 : ℝ)) * ∫ t in a..x, deriv f t ^ 2 := by
  have hsub : Set.uIcc a x ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hx.1]
    intro y hy
    exact ⟨hy.1, le_trans hy.2 hx.2⟩
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a x :=
    continuousOn_const.intervalIntegrable
  have hderiv : IntervalIntegrable (deriv f) volume a x :=
    (hf'.mono hsub).intervalIntegrable
  simpa using
    (intervalIntegral.integral_mul_le_L2_mul_L2
      (g := deriv f) (a := a) (b := x) hone hderiv
      (hab := hx.1) (hcont := hf'.mono hsub))

theorem gap2 (f : ℝ → ℝ) (a b x : ℝ)
    (hfa : f a = 0) (hx : x ∈ Set.Icc a b) :
    f x ^ 2 = (f x - f a) ^ 2 := by
  simp [hfa]

theorem gap3 (f : ℝ → ℝ) (a b x : ℝ) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) (hfa : f a = 0)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (deriv f y) y)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    (f x - f a) ^ 2 ≤
      (x - a) * ∫ t in a..x, deriv f t ^ 2 := by
  have hsub : Set.uIcc a x ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hx.1]
    intro y hy
    exact ⟨hy.1, le_trans hy.2 hx.2⟩
  have hdiff : ∀ y ∈ Set.uIcc a x, DifferentiableAt ℝ f y := by
    intro y hy
    exact (hf y (hsub hy)).differentiableAt
  have hcont : ContinuousOn (deriv f) (Set.uIcc a x) :=
    hf'.mono hsub
  have hint : IntervalIntegrable (deriv f) volume a x :=
    hcont.intervalIntegrable
  have hftc : ∫ t in a..x, deriv f t = f x - f a :=
    intervalIntegral.integral_deriv_eq_sub hdiff hint
  have hcs := gap1 f a b x hab hx hf'
  rw [hftc] at hcs
  simpa using hcs

theorem gap4 (f : ℝ → ℝ) (a b x : ℝ) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    (x - a) * (∫ t in a..x, deriv f t ^ 2) ≤
      (b - a) * energy f a b := by
  change (x - a) * (∫ t in a..x, deriv f t ^ 2) ≤
    (b - a) * ∫ t in a..b, deriv f t ^ 2
  have hsub_ax : Set.uIcc a x ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hx.1]
    intro y hy
    exact ⟨hy.1, le_trans hy.2 hx.2⟩
  have hsub_xb : Set.uIcc x b ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hx.2]
    intro y hy
    exact ⟨le_trans hx.1 hy.1, hy.2⟩
  have hg : ContinuousOn (fun t => deriv f t ^ 2) (Set.Icc a b) :=
    hf'.pow 2
  have hint_ax : IntervalIntegrable (fun t => deriv f t ^ 2) volume a x :=
    (hg.mono hsub_ax).intervalIntegrable
  have hint_xb : IntervalIntegrable (fun t => deriv f t ^ 2) volume x b :=
    (hg.mono hsub_xb).intervalIntegrable
  have hnonneg_ax : 0 ≤ ∫ t in a..x, deriv f t ^ 2 :=
    intervalIntegral.integral_nonneg hx.1 (fun t _ => sq_nonneg (deriv f t))
  have hnonneg_xb : 0 ≤ ∫ t in x..b, deriv f t ^ 2 :=
    intervalIntegral.integral_nonneg hx.2 (fun t _ => sq_nonneg (deriv f t))
  have hadd :
      (∫ t in a..x, deriv f t ^ 2) + (∫ t in x..b, deriv f t ^ 2) =
        ∫ t in a..b, deriv f t ^ 2 :=
    intervalIntegral.integral_add_adjacent hint_ax hint_xb
  have hint_le :
      (∫ t in a..x, deriv f t ^ 2) ≤ ∫ t in a..b, deriv f t ^ 2 := by
    linarith
  exact mul_le_mul (sub_le_sub_right hx.2 a) hint_le hnonneg_ax
    (sub_nonneg.mpr hab)

theorem gap5 (f : ℝ → ℝ) (a b x : ℝ) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) (hfa : f a = 0)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (deriv f y) y)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    f x ^ 2 ≤ (b - a) * energy f a b := by
  calc
    f x ^ 2 = (f x - f a) ^ 2 := gap2 f a b x hfa hx
    _ ≤ (x - a) * ∫ t in a..x, deriv f t ^ 2 :=
      gap3 f a b x hab hx hfa hf hf'
    _ ≤ (b - a) * energy f a b := gap4 f a b x hab hx hf'

theorem gap6 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    amplitude f a b ^ 2 = sSup (squareValues f a b) := by
  obtain ⟨x, hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hf.abs
  have hA_nonempty :
      ({y : ℝ | ∃ z ∈ Set.Icc a b, y = |f z|} : Set ℝ).Nonempty :=
    ⟨|f x|, x, hx, rfl⟩
  have hA_bdd : BddAbove {y : ℝ | ∃ z ∈ Set.Icc a b, y = |f z|} := by
    refine ⟨|f x|, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hmax hz
  have hamp : amplitude f a b = |f x| := by
    unfold amplitude
    apply le_antisymm
    · refine csSup_le hA_nonempty ?_
      rintro y ⟨z, hz, rfl⟩
      exact hmax hz
    · exact le_csSup hA_bdd ⟨x, hx, rfl⟩
  have hsqmax : ∀ z ∈ Set.Icc a b, f z ^ 2 ≤ f x ^ 2 := by
    intro z hz
    have hzle : |f z| ≤ |f x| := hmax hz
    have hp : 0 ≤ (|f x| - |f z|) * (|f x| + |f z|) :=
      mul_nonneg (sub_nonneg.mpr hzle)
        (add_nonneg (abs_nonneg (f x)) (abs_nonneg (f z)))
    nlinarith [sq_abs (f z), sq_abs (f x)]
  have hB_nonempty : (squareValues f a b).Nonempty :=
    ⟨f x ^ 2, x, hx, rfl⟩
  have hB_bdd : BddAbove (squareValues f a b) := by
    refine ⟨f x ^ 2, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hsqmax z hz
  have hsup_sq : sSup (squareValues f a b) = f x ^ 2 := by
    apply le_antisymm
    · refine csSup_le hB_nonempty ?_
      rintro y ⟨z, hz, rfl⟩
      exact hsqmax z hz
    · exact le_csSup hB_bdd ⟨x, hx, rfl⟩
  rw [hamp, hsup_sq]
  exact sq_abs (f x)

theorem gap7 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hfa : f a = 0)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (deriv f y) y)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    sSup (squareValues f a b) ≤ (b - a) * energy f a b := by
  have hne : (squareValues f a b).Nonempty := by
    refine ⟨f a ^ 2, a, ?_, rfl⟩
    exact ⟨le_rfl, hab⟩
  refine csSup_le hne ?_
  rintro y ⟨x, hx, rfl⟩
  exact gap5 f a b x hab hx hfa hf hf'

theorem gap8 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hfa : f a = 0)
    (hf : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Icc a b, HasDerivAt f (deriv f y) y)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    amplitude f a b ^ 2 ≤ (b - a) * energy f a b := by
  rw [gap6 f a b hab hf]
  exact gap7 f a b hab hfa hderiv hf'

theorem gap9 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hfa : f a = 0)
    (hf : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Icc a b, HasDerivAt f (deriv f y) y)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    amplitude f a b ^ 2 ≤
      (b - a) * ∫ x in a..b, deriv f x ^ 2 := by
  simpa [energy] using gap8 f a b hab hfa hf hderiv hf'

end

end ProofGap.Exercise2332
