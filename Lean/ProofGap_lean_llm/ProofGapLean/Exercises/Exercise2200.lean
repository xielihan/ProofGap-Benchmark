import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2200
noncomputable section

open Filter MeasureTheory
open scoped BigOperators Interval

def grid (a b : ℝ) (n i : ℕ) : ℝ :=
  a + ((i : ℝ) / n) * (b - a)

def cell (a b : ℝ) (n i : ℕ) : Set ℝ :=
  Set.Icc (grid a b n i) (grid a b n (i + 1))

def oscillationOn (g : ℝ → ℝ) (I : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |g u - g v|}

def omega (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) : ℝ :=
  oscillationOn f (cell a b n i)

def omegaAbs (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) : ℝ :=
  oscillationOn (fun x => |f x|) (cell a b n i)

def width (a b : ℝ) (n i : ℕ) : ℝ :=
  grid a b n (i + 1) - grid a b n i

def oscillationSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, omega f a b n i * width a b n i

def absOscillationSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, omegaAbs f a b n i * width a b n i

def RiemannIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  IntervalIntegrable f volume a b ∧
    Bornology.IsBounded (f '' Set.Icc a b) ∧
    Tendsto (oscillationSum f a b) atTop (nhds (0 : ℝ))

private theorem width_eq_aux (a b : ℝ) (n i : ℕ) (hn : 0 < n) :
    width a b n i = (b - a) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold width grid
  rw [Nat.cast_add, Nat.cast_one]
  field_simp [hn0] <;> ring

private theorem width_nonneg_aux (a b : ℝ) (n i : ℕ)
    (hab : a ≤ b) (hn : 0 < n) :
    0 ≤ width a b n i := by
  rw [width_eq_aux a b n i hn]
  exact div_nonneg (sub_nonneg.mpr hab) (by positivity)

private theorem cell_nonempty_aux (a b : ℝ) (n i : ℕ)
    (hab : a ≤ b) (hn : 0 < n) :
    (cell a b n i).Nonempty := by
  refine ⟨grid a b n i, ?_⟩
  constructor
  · exact le_rfl
  · have h := width_nonneg_aux a b n i hab hn
    unfold width at h
    linarith

private theorem oscillationOn_nonneg_aux (g : ℝ → ℝ) (I : Set ℝ)
    (hI : I.Nonempty) :
    0 ≤ oscillationOn g I := by
  rcases hI with ⟨w, hw⟩
  let S : Set ℝ := {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |g u - g v|}
  change 0 ≤ sSup S
  by_cases hS : BddAbove S
  · apply le_csSup hS
    exact ⟨w, hw, w, hw, by simp⟩
  · rw [csSup_of_not_bddAbove hS]
    simpa using (le_refl (0 : ℝ))

private theorem oscillationOn_abs_le_aux (f : ℝ → ℝ) (I : Set ℝ) :
    oscillationOn (fun x => |f x|) I ≤ oscillationOn f I := by
  classical
  let A : Set ℝ :=
    {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |(fun x => |f x|) u - (fun x => |f x|) v|}
  let B : Set ℝ := {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |f u - f v|}
  change sSup A ≤ sSup B
  by_cases hI : I.Nonempty
  · by_cases hB : BddAbove B
    · have hAne : A.Nonempty := by
        rcases hI with ⟨w, hw⟩
        exact ⟨0, ⟨w, hw, w, hw, by simp⟩⟩
      apply csSup_le hAne
      intro r hr
      rcases hr with ⟨u, hu, v, hv, rfl⟩
      calc
        |(fun x => |f x|) u - (fun x => |f x|) v| ≤ |f u - f v| :=
          abs_abs_sub_abs_le_abs_sub (f u) (f v)
        _ ≤ sSup B := le_csSup hB ⟨u, hu, v, hv, rfl⟩
    · have hA : ¬ BddAbove A := by
        intro hAbdd
        apply hB
        rcases hAbdd with ⟨C, hC⟩
        rcases hI with ⟨w, hw⟩
        refine ⟨2 * (C + |f w|), ?_⟩
        intro r hr
        rcases hr with ⟨u, hu, v, hv, rfl⟩
        have hCu : |(fun x => |f x|) u - (fun x => |f x|) w| ≤ C :=
          hC ⟨u, hu, w, hw, rfl⟩
        have hCv : |(fun x => |f x|) v - (fun x => |f x|) w| ≤ C :=
          hC ⟨v, hv, w, hw, rfl⟩
        have hu_bound : |f u| ≤ C + |f w| := by
          have hu_abs := le_abs_self (|f u| - |f w|)
          linarith
        have hv_bound : |f v| ≤ C + |f w| := by
          have hv_abs := le_abs_self (|f v| - |f w|)
          linarith
        have huv : |f u - f v| ≤ |f u| + |f v| := by
          simpa [sub_eq_add_neg] using (abs_add_le (f u) (-f v))
        linarith
      simp [csSup_of_not_bddAbove hA, csSup_of_not_bddAbove hB]
  · have hIempty : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hI
    subst I
    simp [A, B]

theorem gap1 (f : ℝ → ℝ) (u v : ℝ) :
    abs (abs (f u) - abs (f v)) ≤ abs (f u - f v) := by
  exact abs_abs_sub_abs_le_abs_sub (f u) (f v)

theorem gap2 (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) :
    omegaAbs f a b n i ≤ omega f a b n i := by
  exact oscillationOn_abs_le_aux f (cell a b n i)

theorem gap3 (f : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hab : a ≤ b) (hn : 0 < n) :
    absOscillationSum f a b n ≤ oscillationSum f a b n := by
  unfold absOscillationSum oscillationSum
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right (gap2 f a b n i)
    (width_nonneg_aux a b n i hab hn)

theorem gap4 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    Tendsto (oscillationSum f a b) atTop (nhds (0 : ℝ)) := by
  exact hf.2.2

theorem gap5 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    Tendsto (absOscillationSum f a b) atTop (nhds (0 : ℝ)) := by
  have hlo : ∀ᶠ n in atTop, (0 : ℝ) ≤ absOscillationSum f a b n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    unfold absOscillationSum
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (oscillationOn_nonneg_aux (fun x => |f x|) (cell a b n i)
        (cell_nonempty_aux a b n i hab hn))
      (width_nonneg_aux a b n i hab hn)
  have hup : ∀ᶠ n in atTop,
      absOscillationSum f a b n ≤ oscillationSum f a b n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact gap3 f a b n hab hn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (gap4 f a b hab hf) hlo hup

theorem gap6 (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannIntegrableOn f a b) :
    IntervalIntegrable (fun x => |f x|) volume a b := by
  exact hf.1.abs

theorem gap7 (f : ℝ → ℝ) (x : ℝ) :
    -|f x| ≤ f x := by
  exact neg_abs_le (f x)

theorem gap8 (f : ℝ → ℝ) (x : ℝ) :
    f x ≤ |f x| := by
  exact le_abs_self (f x)

theorem gap9 (f : ℝ → ℝ) (x : ℝ) :
    -|f x| ≤ |f x| := by
  exact neg_le_self (abs_nonneg (f x))

theorem gap10 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    -(∫ x in a..b, |f x|) ≤ ∫ x in a..b, f x := by
  have hmono :
      (∫ x in a..b, -|f x|) ≤ ∫ x in a..b, f x :=
    intervalIntegral.integral_mono_on hab hf.abs.neg hf
      (fun x _ => gap7 f x)
  simpa only [intervalIntegral.integral_neg] using hmono

theorem gap11 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, |f x| := by
  exact intervalIntegral.integral_mono_on hab hf hf.abs
    (fun x _ => gap8 f x)

theorem gap12 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    -(∫ x in a..b, |f x|) ≤ ∫ x in a..b, |f x| := by
  simpa only [abs_abs] using
    (gap10 (fun x => |f x|) a b hab hf.abs)

theorem gap13 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := by
  exact (abs_le).2 ⟨gap10 f a b hab hf, gap11 f a b hab hf⟩

theorem gap14 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    IntervalIntegrable (fun x => |f x|) volume a b ∧
      |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := by
  exact ⟨gap6 f a b hf, gap13 f a b hab hf.1⟩

end
end ProofGap.Exercise2200
