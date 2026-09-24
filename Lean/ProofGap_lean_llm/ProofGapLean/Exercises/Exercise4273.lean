import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4273

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def P (x y : ℝ) : ℝ :=
  (x ^ 2 + 2 * x * y + 5 * y ^ 2) / (x + y) ^ 3

def Q (x y : ℝ) : ℝ :=
  (x ^ 2 - 2 * x * y + y ^ 2) / (x + y) ^ 3

def field (p : Point) : Point :=
  (P p.1 p.2, Q p.1 p.2)

def InConstructionDomain (p : Point) : Prop :=
  0 < p.2 ∧ 0 < p.1 + p.2

def potential (p : Point) : ℝ :=
  Real.log |p.1 + p.2| - 2 * p.2 ^ 2 / (p.1 + p.2) ^ 2

def constructedPotential (p : Point) : ℝ :=
  (∫ s in (0 : ℝ)..p.1, P s p.2) +
    ∫ t in (1 : ℝ)..p.2, Q 0 t

def simplifiedConstruction (p : Point) : ℝ :=
  (∫ s in (0 : ℝ)..p.1,
      ((s + p.2) ^ 2 + 4 * p.2 ^ 2) / (s + p.2) ^ 3) +
    ∫ t in (1 : ℝ)..p.2, 1 / t

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (p : Point) : Prop :=
  HasDerivAt (fun x => U (x, p.2)) V.1 p.1 ∧
    HasDerivAt (fun y => U (p.1, y)) V.2 p.2

def IsSolution (z : Point → ℝ) : Prop :=
  ∀ p, InConstructionDomain p →
    HasCoordinateGradientAt z (field p) p

private theorem potential_hasCoordinateGradientAt
    (p : Point) (hp : InConstructionDomain p) :
    HasCoordinateGradientAt potential (field p) p := by
  rcases hp with ⟨hy, hs⟩
  have hs0 : p.1 + p.2 ≠ 0 := ne_of_gt hs
  constructor
  · dsimp [potential, field, P]
    have hadd := (hasDerivAt_id p.1).add_const p.2
    have hlog := (Real.hasDerivAt_log hs0).comp p.1 hadd
    have hden := hadd.pow 2
    have hquot :=
      (hasDerivAt_const p.1 (2 * p.2 ^ 2)).div hden
        (pow_ne_zero 2 hs0)
    simpa only [Real.log_abs] using (show
      HasDerivAt
        (fun x => Real.log (x + p.2) - 2 * p.2 ^ 2 / (x + p.2) ^ 2)
        ((p.1 ^ 2 + 2 * p.1 * p.2 + 5 * p.2 ^ 2) /
          (p.1 + p.2) ^ 3) p.1 by
      convert hlog.sub hquot using 1 <;>
        simp [Function.comp_apply] <;>
        field_simp [hs0] <;>
        ring)
  · dsimp [potential, field, Q]
    have hadd := (hasDerivAt_const p.2 p.1).add (hasDerivAt_id p.2)
    have hlog := (Real.hasDerivAt_log hs0).comp p.2 hadd
    have hnum :=
      (hasDerivAt_const p.2 2).mul ((hasDerivAt_id p.2).pow 2)
    have hden := hadd.pow 2
    have hquot := hnum.div hden (pow_ne_zero 2 hs0)
    simpa only [Real.log_abs] using (show
      HasDerivAt
        (fun y => Real.log (p.1 + y) - 2 * y ^ 2 / (p.1 + y) ^ 2)
        ((p.1 ^ 2 - 2 * p.1 * p.2 + p.2 ^ 2) /
          (p.1 + p.2) ^ 3) p.2 by
      convert hlog.sub hquot using 1 <;>
        simp [Function.comp_apply] <;>
        field_simp [hs0] <;>
        ring)

private theorem solution_iff_potential (z : Point → ℝ) :
    IsSolution z ↔
      ∃ C : ℝ, ∀ p, InConstructionDomain p → z p = potential p + C := by
  constructor
  · intro hz
    let w : Point → ℝ := fun p => z p - potential p
    have horizontal : ∀ (y a b : ℝ), 0 < y → 0 < a + y → 0 < b + y →
        w (a, y) = w (b, y) := by
      intro y a b hy ha hb
      let f : ℝ → ℝ := fun x => w (x, y)
      have hdiff : DifferentiableOn ℝ f (Set.Ioi (-y)) := by
        intro x hx
        change -y < x at hx
        have hdom : InConstructionDomain (x, y) := by
          refine ⟨hy, ?_⟩
          change 0 < x + y
          linarith
        have hzero :=
          (hz (x, y) hdom).1.sub
            (potential_hasCoordinateGradientAt (x, y) hdom).1
        have hfzero : HasDerivAt f 0 x := by
          simpa [f, w, field] using hzero
        exact hfzero.differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ Set.Ioi (-y), deriv f x = 0 := by
        intro x hx
        change -y < x at hx
        have hdom : InConstructionDomain (x, y) := by
          refine ⟨hy, ?_⟩
          change 0 < x + y
          linarith
        have hzero :=
          (hz (x, y) hdom).1.sub
            (potential_hasCoordinateGradientAt (x, y) hdom).1
        have hfzero : HasDerivAt f 0 x := by
          simpa [f, w, field] using hzero
        exact hfzero.deriv
      apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff hderiv
      · change -y < a
        linarith
      · change -y < b
        linarith
    have vertical : ∀ (a b : ℝ), 0 < a → 0 < b →
        w (0, a) = w (0, b) := by
      intro a b ha hb
      let f : ℝ → ℝ := fun y => w (0, y)
      have hdiff : DifferentiableOn ℝ f (Set.Ioi 0) := by
        intro y hy
        change 0 < y at hy
        have hdom : InConstructionDomain (0, y) := by
          refine ⟨hy, ?_⟩
          simpa using hy
        have hzero :=
          (hz (0, y) hdom).2.sub
            (potential_hasCoordinateGradientAt (0, y) hdom).2
        have hfzero : HasDerivAt f 0 y := by
          simpa [f, w, field] using hzero
        exact hfzero.differentiableAt.differentiableWithinAt
      have hderiv : ∀ y ∈ Set.Ioi 0, deriv f y = 0 := by
        intro y hy
        change 0 < y at hy
        have hdom : InConstructionDomain (0, y) := by
          refine ⟨hy, ?_⟩
          simpa using hy
        have hzero :=
          (hz (0, y) hdom).2.sub
            (potential_hasCoordinateGradientAt (0, y) hdom).2
        have hfzero : HasDerivAt f 0 y := by
          simpa [f, w, field] using hzero
        exact hfzero.deriv
      exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff hderiv ha hb
    refine ⟨w (0, 1), ?_⟩
    intro p hp
    rcases hp with ⟨hy, hs⟩
    have h₁ := horizontal p.2 p.1 0 hy hs (by simpa using hy)
    have h₂ := vertical p.2 1 hy (by norm_num)
    dsimp [w] at h₁ h₂ ⊢
    linarith
  · rintro ⟨C, hC⟩
    intro p hp
    have hpot := potential_hasCoordinateGradientAt p hp
    constructor
    · have heq :
          (fun x => z (x, p.2)) =ᶠ[nhds p.1]
            (fun x => potential (x, p.2) + C) := by
          filter_upwards [Ioi_mem_nhds (show -p.2 < p.1 by
            linarith [hp.2])] with x hx
          change -p.2 < x at hx
          apply hC (x, p.2)
          refine ⟨hp.1, ?_⟩
          change 0 < x + p.2
          linarith
      have hder := hpot.1.add_const C
      exact hder.congr_of_eventuallyEq heq
    · have heq :
          (fun y => z (p.1, y)) =ᶠ[nhds p.2]
            (fun y => potential (p.1, y) + C) := by
          filter_upwards [Ioi_mem_nhds hp.1,
            Ioi_mem_nhds (show -p.1 < p.2 by linarith [hp.2])]
              with y hy hsum
          change 0 < y at hy
          change -p.1 < y at hsum
          apply hC (p.1, y)
          refine ⟨hy, ?_⟩
          change 0 < p.1 + y
          linarith
      have hder := hpot.2.add_const C
      exact hder.congr_of_eventuallyEq heq

private theorem constructed_eq_potential_add_two
    (p : Point) (hp : InConstructionDomain p) :
    constructedPotential p = potential p + 2 := by
  rcases hp with ⟨hy, hs⟩
  have hs0 : p.1 + p.2 ≠ 0 := ne_of_gt hs
  have first_pos : ∀ s ∈ Set.uIcc (0 : ℝ) p.1, 0 < s + p.2 := by
    intro s hs'
    rw [Set.mem_uIcc] at hs'
    rcases hs' with hs' | hs' <;> linarith
  let F : ℝ → ℝ := fun s =>
    Real.log (s + p.2) - 2 * p.2 ^ 2 / (s + p.2) ^ 2
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) p.1,
      HasDerivAt F (P s p.2) s := by
    intro s hs'
    have hspos := first_pos s hs'
    have hsne : s + p.2 ≠ 0 := ne_of_gt hspos
    have hadd := (hasDerivAt_id s).add_const p.2
    have hlog := (Real.hasDerivAt_log hsne).comp s hadd
    have hquot :=
      (hasDerivAt_const s (2 * p.2 ^ 2)).div (hadd.pow 2)
        (pow_ne_zero 2 hsne)
    dsimp [F, P]
    convert hlog.sub hquot using 1 <;>
      simp [Function.comp_apply] <;>
      field_simp [hsne] <;>
      ring
  have hPcont : ContinuousOn (fun s => P s p.2)
      (Set.uIcc (0 : ℝ) p.1) := by
    intro s hs'
    have hsne : s + p.2 ≠ 0 := ne_of_gt (first_pos s hs')
    have hnum : ContinuousAt
        (fun u : ℝ => u ^ 2 + 2 * u * p.2 + 5 * p.2 ^ 2) s := by
      fun_prop
    have hden : ContinuousAt (fun u : ℝ => (u + p.2) ^ 3) s := by
      fun_prop
    exact (hnum.div hden (pow_ne_zero 3 hsne)).continuousWithinAt
  have hFderivCont : ContinuousOn (deriv F)
      (Set.uIcc (0 : ℝ) p.1) := by
    apply hPcont.congr
    intro s hs'
    exact (hF s hs').deriv
  have hfirstDeriv : (∫ s in (0 : ℝ)..p.1, deriv F s) = F p.1 - F 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun s hs' => (hF s hs').differentiableAt)
      hFderivCont.intervalIntegrable
  have hfirst : (∫ s in (0 : ℝ)..p.1, P s p.2) = F p.1 - F 0 := by
    calc
      (∫ s in (0 : ℝ)..p.1, P s p.2) =
          ∫ s in (0 : ℝ)..p.1, deriv F s := by
        apply intervalIntegral.integral_congr
        intro s hs'
        exact (hF s hs').deriv.symm
      _ = F p.1 - F 0 := hfirstDeriv
  have second_pos : ∀ t ∈ Set.uIcc (1 : ℝ) p.2, 0 < t := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht <;> linarith
  have hQ : ∀ t ∈ Set.uIcc (1 : ℝ) p.2,
      HasDerivAt Real.log (Q 0 t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (second_pos t ht)
    unfold Q
    convert Real.hasDerivAt_log ht0 using 1 <;>
      simp [Function.comp_apply] <;>
      field_simp [ht0] <;>
      ring
  have hQcont : ContinuousOn (fun t => Q 0 t)
      (Set.uIcc (1 : ℝ) p.2) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (second_pos t ht)
    have hnum : ContinuousAt
        (fun u : ℝ => 0 ^ 2 - 2 * 0 * u + u ^ 2) t := by
      fun_prop
    have hden : ContinuousAt (fun u : ℝ => (0 + u) ^ 3) t := by
      fun_prop
    exact (hnum.div hden (pow_ne_zero 3 (by simpa using ht0))).continuousWithinAt
  have hLogDerivCont : ContinuousOn (deriv Real.log)
      (Set.uIcc (1 : ℝ) p.2) := by
    apply hQcont.congr
    intro t ht
    exact (hQ t ht).deriv
  have hsecondDeriv : (∫ t in (1 : ℝ)..p.2, deriv Real.log t) =
      Real.log p.2 - Real.log 1 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun t ht => (hQ t ht).differentiableAt)
      hLogDerivCont.intervalIntegrable
  have hsecond : (∫ t in (1 : ℝ)..p.2, Q 0 t) =
      Real.log p.2 - Real.log 1 := by
    calc
      (∫ t in (1 : ℝ)..p.2, Q 0 t) =
          ∫ t in (1 : ℝ)..p.2, deriv Real.log t := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (hQ t ht).deriv.symm
      _ = Real.log p.2 - Real.log 1 := hsecondDeriv
  rw [constructedPotential, hfirst, hsecond]
  dsimp [F, potential]
  rw [abs_of_pos hs, Real.log_one]
  field_simp [ne_of_gt hy, hs0] <;>
    ring_nf

theorem gap1 (z : Point → ℝ) :
    IsSolution z ↔
      ∃ C : ℝ, ∀ p, InConstructionDomain p →
        z p = constructedPotential p + C := by
  constructor
  · intro hz
    obtain ⟨C, hC⟩ := (solution_iff_potential z).1 hz
    refine ⟨C - 2, ?_⟩
    intro p hp
    rw [constructed_eq_potential_add_two p hp, hC p hp]
    ring
  · rintro ⟨C, hC⟩
    apply (solution_iff_potential z).2
    refine ⟨C + 2, ?_⟩
    intro p hp
    calc
      z p = constructedPotential p + C := hC p hp
      _ = potential p + (C + 2) := by
        rw [constructed_eq_potential_add_two p hp]
        ring

theorem gap2 (p : Point) (hp : InConstructionDomain p) :
    constructedPotential p = simplifiedConstruction p := by
  unfold constructedPotential simplifiedConstruction
  congr 1
  · apply intervalIntegral.integral_congr
    intro s hs
    unfold P
    ring
  · apply intervalIntegral.integral_congr
    intro t htmem
    unfold Q
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [ht]
      ring

theorem gap3 (z : Point → ℝ) :
    IsSolution z ↔
      ∃ C₁ : ℝ, ∀ p, InConstructionDomain p →
        z p = potential p + C₁ := by
  exact solution_iff_potential z

theorem gap4 (z : Point → ℝ) :
    IsSolution z ↔
      ∃ C₁ : ℝ, ∀ p, InConstructionDomain p →
        z p = potential p + C₁ := by
  exact gap3 z

theorem gap5 (C₁ : ℝ) :
    IsSolution (fun p => potential p + C₁) := by
  apply (gap3 (fun p => potential p + C₁)).2
  exact ⟨C₁, fun p hp => rfl⟩

end

end ProofGap.Exercise4273
