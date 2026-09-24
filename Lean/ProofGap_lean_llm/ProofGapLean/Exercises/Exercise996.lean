import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise996

noncomputable section

def absSum {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |x - a k|

theorem gap1 (a : ℝ) :
    ContinuousAt (fun x : ℝ => |x - a|) a := by
  exact (continuousAt_id.sub continuousAt_const).abs

theorem gap2 (a : ℝ) :
    ¬ DifferentiableAt ℝ (fun x : ℝ => |x - a|) a := by
  intro h
  have houter :
      DifferentiableAt ℝ (fun x : ℝ => |x - a|) ((fun x : ℝ => x + a) 0) := by
    simpa using h
  have hinner : DifferentiableAt ℝ (fun x : ℝ => x + a) 0 :=
    differentiableAt_id.add (differentiableAt_const a)
  have hc :
      DifferentiableAt ℝ
        ((fun x : ℝ => |x - a|) ∘ (fun x : ℝ => x + a)) 0 :=
    houter.comp 0 hinner
  have habs : DifferentiableAt ℝ (fun x : ℝ => |x|) 0 := by
    simpa [Function.comp_def] using hc
  have hminSub : IsLocalMin (fun x : ℝ => |x| - x) 0 := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa using (sub_nonneg.mpr (le_abs_self x))
  have hminAdd : IsLocalMin (fun x : ℝ => |x| + x) 0 := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa using (sub_nonneg.mpr (neg_le_abs x))
  have hextrSub : IsLocalExtr (fun x : ℝ => |x| - x) 0 :=
    Or.inl hminSub
  have hextrAdd : IsLocalExtr (fun x : ℝ => |x| + x) 0 :=
    Or.inl hminAdd
  have hfSub :
      fderiv ℝ (fun x : ℝ => |x| - x) 0 = 0 :=
    hextrSub.fderiv_eq_zero
  have hfAdd :
      fderiv ℝ (fun x : ℝ => |x| + x) 0 = 0 :=
    hextrAdd.fderiv_eq_zero
  have hdSub : deriv (fun x : ℝ => |x| - x) 0 = 0 := by
    simp [deriv, hfSub]
  have hdAdd : deriv (fun x : ℝ => |x| + x) 0 = 0 := by
    simp [deriv, hfAdd]
  have hslopeSub :
      deriv (fun x : ℝ => |x| - x) 0 =
        deriv (fun x : ℝ => |x|) 0 - 1 :=
    (habs.hasDerivAt.sub (hasDerivAt_id (𝕜 := ℝ) 0)).deriv
  have hslopeAdd :
      deriv (fun x : ℝ => |x| + x) 0 =
        deriv (fun x : ℝ => |x|) 0 + 1 :=
    (habs.hasDerivAt.add (hasDerivAt_id (𝕜 := ℝ) 0)).deriv
  linarith

theorem gap3 {n : ℕ} (a : Fin n → ℝ) :
    Continuous (absSum a) := by
  unfold absSum
  have hsum : ∀ s : Finset (Fin n),
      Continuous (fun x : ℝ => Finset.sum s (fun j => |x - a j|)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    | @insert j s hjs ih =>
        have hj : Continuous (fun x : ℝ => |x - a j|) :=
          (continuous_id.sub continuous_const).abs
        simpa [Finset.sum_insert, hjs] using hj.add ih
  simpa using hsum Finset.univ

theorem gap4 {n : ℕ} (a : Fin n → ℝ) (k : Fin n) :
    ¬ DifferentiableAt ℝ (absSum a) (a k) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun j => a j = a k)
  let t : Finset (Fin n) := Finset.univ.filter (fun j => a j ≠ a k)
  have hpart_aux (u : Finset (Fin n)) (x : ℝ) :
      Finset.sum u (fun j => |x - a j|) =
        Finset.sum (u.filter (fun j => a j = a k)) (fun j => |x - a j|) +
        Finset.sum (u.filter (fun j => a j ≠ a k)) (fun j => |x - a j|) := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert j u hju ih =>
        rw [Finset.sum_insert hju, ih]
        by_cases hj : a j = a k
        · simp [Finset.filter_insert, hj, hju, add_left_comm, add_comm]
        · simp [Finset.filter_insert, hj, hju, add_left_comm]
  have hpartition (x : ℝ) :
      absSum a x =
        Finset.sum s (fun j => |x - a j|) +
        Finset.sum t (fun j => |x - a j|) := by
    simpa [absSum, s, t] using hpart_aux Finset.univ x
  have hequal (x : ℝ) :
      Finset.sum s (fun j => |x - a j|) =
        (s.card : ℝ) * |x - a k| := by
    calc
      Finset.sum s (fun j => |x - a j|) =
          Finset.sum s (fun _ => |x - a k|) := by
        apply Finset.sum_congr rfl
        intro j hj
        have haj : a j = a k := by simpa [s] using hj
        rw [haj]
      _ = (s.card : ℝ) * |x - a k| := by simp
  have hterm (j : Fin n) (hj : j ∈ t) :
      DifferentiableAt ℝ (fun x : ℝ => |x - a j|) (a k) := by
    have haj : a j ≠ a k := by simpa [t] using hj
    have hne : a k - a j ≠ 0 := sub_ne_zero.mpr (Ne.symm haj)
    have hsub :
        DifferentiableAt ℝ (fun x : ℝ => x - a j) (a k) :=
      differentiableAt_id.sub (differentiableAt_const (a j))
    have hcont :
        ContinuousAt (fun x : ℝ => x - a j) (a k) :=
      continuousAt_id.sub continuousAt_const
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hev : ∀ᶠ x in nhds (a k), x - a j < 0 :=
        hcont (isOpen_Iio.mem_nhds hneg)
      have heq :
          (fun x : ℝ => |x - a j|) =ᶠ[nhds (a k)]
            (fun x : ℝ => -(x - a j)) :=
        hev.mono (fun x hx => abs_of_neg hx)
      exact (heq.differentiableAt_iff).2 hsub.neg
    · have hev : ∀ᶠ x in nhds (a k), 0 < x - a j :=
        hcont (isOpen_Ioi.mem_nhds hpos)
      have heq :
          (fun x : ℝ => |x - a j|) =ᶠ[nhds (a k)]
            (fun x : ℝ => x - a j) :=
        hev.mono (fun x hx => abs_of_pos hx)
      exact (heq.differentiableAt_iff).2 hsub
  have hsum : ∀ u : Finset (Fin n), u ⊆ t →
      DifferentiableAt ℝ
        (fun x : ℝ => Finset.sum u (fun j => |x - a j|)) (a k) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro _
        simpa using
          (differentiableAt_id.sub differentiableAt_id :
            DifferentiableAt ℝ (fun x : ℝ => x - x) (a k))
    | @insert j u hju ih =>
        intro hu
        have hjdiff := hterm j (hu (Finset.mem_insert_self j u))
        have hudiff := ih (fun i hi => hu (Finset.mem_insert_of_mem hi))
        simpa [Finset.sum_insert, hju] using hjdiff.add hudiff
  have hrem :
      DifferentiableAt ℝ
        (fun x : ℝ => Finset.sum t (fun j => |x - a j|)) (a k) :=
    hsum t (fun _ hj => hj)
  intro h
  have hfun :
      absSum a = fun x : ℝ =>
        (s.card : ℝ) * |x - a k| +
          Finset.sum t (fun j => |x - a j|) := by
    funext x
    rw [hpartition x, hequal x]
  have htotal := h
  rw [hfun] at htotal
  have hscaled' := htotal.sub hrem
  change DifferentiableAt ℝ
    (fun x : ℝ =>
      ((s.card : ℝ) * |x - a k| +
        Finset.sum t (fun j => |x - a j|)) -
        Finset.sum t (fun j => |x - a j|)) (a k) at hscaled'
  have hscaled :
      DifferentiableAt ℝ (fun x : ℝ => (s.card : ℝ) * |x - a k|) (a k) := by
    simpa only [add_sub_cancel_right] using hscaled'
  have hk : k ∈ s := by simp [s]
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.mpr ⟨k, hk⟩
  have hcoeff : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
  have habs : DifferentiableAt ℝ (fun x : ℝ => |x - a k|) (a k) := by
    have hscaled' := hscaled.const_mul ((s.card : ℝ)⁻¹)
    simpa [← mul_assoc, hcoeff] using hscaled'
  exact gap2 (a k) habs

theorem gap5 {n : ℕ} (a : Fin n → ℝ) (g : ℝ → ℝ)
    (hg : g = absSum a) :
    Continuous g ∧ ∀ k, ¬ DifferentiableAt ℝ g (a k) := by
  subst g
  exact ⟨gap3 a, fun k => gap4 a k⟩

end

end ProofGap.Exercise996
