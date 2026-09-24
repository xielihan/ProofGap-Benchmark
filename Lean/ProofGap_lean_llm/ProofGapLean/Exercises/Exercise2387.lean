import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas

namespace ProofGap.Exercise2387
noncomputable section

open Filter Set MeasureTheory
open scoped Interval

def TailConverges (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (fun A => ∫ x in a..A, f x) atTop (nhds L)

theorem gap1 (f : ℝ → ℝ) (c : ℝ) (hf : Antitone f) (hc : f c < 0) :
    ∀ x ≥ c, f x ≤ f c := by
  intro x hx
  exact hf hx

theorem gap2 (f : ℝ → ℝ) (c A : ℝ) (hf : Antitone f)
    (hcA : c ≤ A) :
    (∫ x in c..A, f x) ≤ ∫ x in c..A, f c := by
  apply intervalIntegral.integral_mono_on hcA hf.intervalIntegrable
    intervalIntegrable_const
  intro x hx
  exact hf hx.1

theorem gap3 (c k : ℝ) (hk : k < 0) :
    Tendsto (fun A => ∫ _x in c..A, k) atTop atBot := by
  have hlin : Tendsto (fun A : ℝ => (A - c) * k) atTop atBot :=
    (tendsto_atTop_add_const_right atTop (-c) tendsto_id).atTop_mul_const_of_neg hk
  simpa [sub_eq_add_neg] using hlin

theorem gap4 (f : ℝ → ℝ) (a c : ℝ) (hf : Antitone f)
    (hac : a ≤ c) (hc : f c < 0) :
    ¬ TailConverges f a := by
  rintro ⟨L, hL⟩
  obtain ⟨B, hB⟩ := (Metric.tendsto_atTop.1 hL) 1 zero_lt_one
  have hconst : ∀ᶠ A : ℝ in atTop,
      (∫ _x in c..A, f c) ≤ L - 1 - ∫ x in a..c, f x :=
    (tendsto_atBot.1 (gap3 c (f c) hc)) _
  obtain ⟨D, hD⟩ := eventually_atTop.1 hconst
  let A := max B (max D c)
  have hAB : B ≤ A := le_max_left _ _
  have hAD : D ≤ A := (le_max_left D c).trans (le_max_right B (max D c))
  have hcA : c ≤ A := (le_max_right D c).trans (le_max_right B (max D c))
  have hnear := hB A hAB
  rw [Real.dist_eq] at hnear
  have hlower : L - 1 < ∫ x in a..A, f x := by
    linarith [(abs_lt.mp hnear).1]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (a := a) (b := c))
    (hf.intervalIntegrable (μ := volume) (a := c) (b := A))
  have hupper : (∫ x in a..A, f x) ≤ L - 1 := by
    calc
      (∫ x in a..A, f x) = (∫ x in a..c, f x) + ∫ x in c..A, f x := hadd.symm
      _ ≤ (∫ x in a..c, f x) + ∫ _x in c..A, f c :=
        add_le_add le_rfl (gap2 f c A hf hcA)
      _ ≤ L - 1 := by linarith [hD A hAD]
  linarith

theorem gap5 (f : ℝ → ℝ) (a : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) :
    ¬ ∃ c ≥ a, f c < 0 := by
  rintro ⟨c, hca, hc⟩
  exact gap4 f a c hf hca hc hconv

theorem gap6 (f : ℝ → ℝ) (a : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) :
    ∀ x ≥ a, 0 ≤ f x := by
  intro x hx
  by_contra hn
  exact gap5 f a hf hconv ⟨x, hx, lt_of_not_ge hn⟩

theorem gap7 (f : ℝ → ℝ) (a : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) :
    ∀ ε > 0, ∃ A > max (2 * a) 0,
      ∀ x > A, |∫ t in x / 2..x, f t| < ε / 2 := by
  rintro ε hε
  obtain ⟨L, hL⟩ := hconv
  have hhalf : Tendsto (fun x : ℝ => x / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hdiff : Tendsto (fun x => ∫ t in x / 2..x, f t) atTop (nhds 0) := by
    have hsub : Tendsto
        (fun x => (∫ t in a..x, f t) - ∫ t in a..x / 2, f t)
        atTop (nhds 0) := by
      simpa using hL.sub (hL.comp hhalf)
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop (max (2 * a) 0)] with x hx
    have hxa : a ≤ x / 2 := by
      have := (le_max_left (2 * a) 0).trans hx
      linarith
    have hxx : x / 2 ≤ x := by
      have := (le_max_right (2 * a) 0).trans hx
      linarith
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (a := a) (b := x / 2))
      (hf.intervalIntegrable (μ := volume) (a := x / 2) (b := x))
    change (∫ t in a..x, f t) - ∫ t in a..x / 2, f t =
      ∫ t in x / 2..x, f t
    linarith [hadd]
  obtain ⟨B, hB⟩ := (Metric.tendsto_atTop.1 hdiff) (ε / 2) (by linarith)
  let A := max (B + 1) (max (2 * a) 0 + 1)
  refine ⟨A, ?_, ?_⟩
  · dsimp only [A]
    linarith [le_max_right (B + 1) (max (2 * a) 0 + 1)]
  · intro x hx
    have hxB : B ≤ x := by
      dsimp only [A] at hx
      linarith [le_max_left (B + 1) (max (2 * a) 0 + 1)]
    simpa [Real.dist_eq] using hB x hxB

theorem gap8 (f : ℝ → ℝ) (a x : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) (hx : max (2 * a) 0 < x) :
    |∫ t in x / 2..x, f t| = ∫ t in x / 2..x, f t := by
  rw [abs_of_nonneg]
  apply intervalIntegral.integral_nonneg
  · linarith [lt_of_le_of_lt (le_max_right (2 * a) 0) hx]
  · intro t ht
    apply gap6 f a hf hconv t
    have := lt_of_le_of_lt (le_max_left (2 * a) 0) hx
    linarith [ht.1]

theorem gap9 (f : ℝ → ℝ) (a x : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) (hx : max (2 * a) 0 < x) :
    f x * (x - x / 2) ≤ ∫ t in x / 2..x, f t := by
  have hhalf : x / 2 ≤ x := by
    linarith [lt_of_le_of_lt (le_max_right (2 * a) 0) hx]
  have hconst : IntervalIntegrable (fun _ : ℝ => f x) volume (x / 2) x :=
    intervalIntegrable_const
  have hfint : IntervalIntegrable f volume (x / 2) x :=
    hf.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hhalf hconst hfint
    (fun t ht => hf ht.2)
  simpa [intervalIntegral.integral_const, mul_comm] using hmono

theorem gap10 (f : ℝ → ℝ) (x : ℝ) :
    f x * (x - x / 2) = x / 2 * f x := by ring

theorem gap11 (f : ℝ → ℝ) (a x : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) (hx : max (2 * a) 0 < x) :
    x / 2 * f x ≤ |∫ t in x / 2..x, f t| := by
  rw [← gap10 f x, gap8 f a x hf hconv hx]
  exact gap9 f a x hf hconv hx

theorem gap12 (f : ℝ → ℝ) (a x : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) (hx : max (2 * a) 0 < x) :
    0 ≤ x * f x := by
  exact mul_nonneg (le_of_lt ((le_max_right (2 * a) 0).trans_lt hx))
    (gap6 f a hf hconv x (by
      have h2a := (le_max_left (2 * a) 0).trans_lt hx
      have hxpos := (le_max_right (2 * a) 0).trans_lt hx
      linarith))

theorem gap13 (f : ℝ → ℝ) (a : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) :
    ∀ ε > 0, ∃ A, ∀ x > A, x * f x < ε := by
  intro ε hε
  obtain ⟨A, hA, hsmall⟩ := gap7 f a hf hconv ε hε
  refine ⟨A, fun x hx => ?_⟩
  have hblock := hsmall x hx
  have hlower := gap11 f a x hf hconv (hA.trans hx)
  linarith

theorem gap14 (f : ℝ → ℝ) (a : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) :
    ∀ ε > 0, ∃ A, ∀ x > A, 0 ≤ x * f x ∧ x * f x < ε := by
  intro ε hε
  obtain ⟨B, hB⟩ := gap13 f a hf hconv ε hε
  let A := max B (max (2 * a) 0)
  refine ⟨A, fun x hx => ?_⟩
  refine ⟨gap12 f a x hf hconv ?_, hB x ?_⟩
  · exact (le_max_right B (max (2 * a) 0)).trans_lt hx
  · exact (le_max_left B (max (2 * a) 0)).trans_lt hx

theorem gap15 (f : ℝ → ℝ) (a : ℝ) (hf : Antitone f)
    (hconv : TailConverges f a) :
    Tendsto (fun x => x * f x) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨A, hA⟩ := gap14 f a hf hconv ε hε
  refine ⟨A + 1, fun x hx => ?_⟩
  have hx' := hA x (lt_of_lt_of_le (lt_add_one A) hx)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hx'.1]
  exact hx'.2

theorem gap16 (f g : ℝ → ℝ) (hf : Monotone f) (hg : ∀ x, g x = -f x) :
    Antitone g := by
  intro x y hxy
  rw [hg x, hg y]
  exact neg_le_neg (hf hxy)

theorem gap17 (f g : ℝ → ℝ) (a : ℝ) (hf : Monotone f)
    (hg : ∀ x, g x = -f x) (hconv : TailConverges f a) :
    Tendsto (fun x => x * g x) atTop (nhds 0) := by
  obtain ⟨L, hL⟩ := hconv
  have hfun : g = fun x => -f x := funext hg
  have hgconv : TailConverges g a := by
    refine ⟨-L, ?_⟩
    rw [hfun]
    simpa only [intervalIntegral.integral_neg] using hL.neg
  exact gap15 g a (gap16 f g hf hg) hgconv

theorem gap18 (f : ℝ → ℝ) (a : ℝ) (hf : Monotone f)
    (hconv : TailConverges f a) :
    Tendsto (fun x => x * f x) atTop (nhds 0) := by
  have hneg := gap17 f (fun x => -f x) a hf (fun _ => rfl) hconv
  have h := hneg.neg
  simpa only [mul_neg, neg_neg, neg_zero] using h

theorem gap19 (f : ℝ → ℝ) (a : ℝ)
    (hmono : Antitone f ∨ Monotone f) (hconv : TailConverges f a) :
    Asymptotics.IsLittleO atTop f (fun x : ℝ => 1 / x) := by
  have hxf : Tendsto (fun x => x * f x) atTop (nhds 0) := by
    rcases hmono with hf | hf
    · exact gap15 f a hf hconv
    · exact gap18 f a hf hconv
  refine (Asymptotics.isLittleO_iff_tendsto'
    (l := atTop) (f := f) (g := fun x : ℝ => 1 / x) ?_).2 ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro hzero
    exact False.elim (one_div_ne_zero hx.ne' hzero)
  · apply hxf.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
    <;> ring

theorem gap20 (f : ℝ → ℝ) (a : ℝ)
    (hmono : Antitone f ∨ Monotone f) (hconv : TailConverges f a) :
    Asymptotics.IsLittleO atTop f (fun x : ℝ => 1 / x) := by
  exact gap19 f a hmono hconv

end
end ProofGap.Exercise2387
