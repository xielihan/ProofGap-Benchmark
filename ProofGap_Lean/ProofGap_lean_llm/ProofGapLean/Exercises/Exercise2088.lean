import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2088
noncomputable section

def U : Set ℝ := Set.Ioi 0
def f (x : ℝ) := Real.sqrt ((Real.exp x - 1) / (Real.exp x + 1))
def rewritten (x : ℝ) :=
  (Real.exp x - 1) / Real.sqrt (Real.exp (2 * x) - 1)
def primitive (x : ℝ) :=
  Real.log (Real.exp x + Real.sqrt (Real.exp (2 * x) - 1)) +
    Real.arcsin (Real.exp (-x))
def Family (g : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Split := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => Real.exp x / Real.sqrt (Real.exp (2 * x) - 1)),
  ∃ B ∈ Family (fun x => 1 / Real.sqrt (Real.exp (2 * x) - 1)),
  ∃ C, ∀ x ∈ U, F x = A x - B x + C}
def Substitutions := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => deriv Real.exp x /
    Real.sqrt (Real.exp x ^ 2 - 1)),
  ∃ B ∈ Family (fun x => deriv (fun y => Real.exp (-y)) x /
    Real.sqrt (1 - Real.exp (-x) ^ 2)),
  ∃ C, ∀ x ∈ U, F x = A x + B x + C}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}

private lemma exp_two_eq_sq (x : ℝ) :
    Real.exp (2 * x) = Real.exp x ^ 2 := by
  rw [show 2 * x = x + x by ring, Real.exp_add]
  ring

private lemma positive_exp_facts {x : ℝ} (hx : x ∈ U) :
    1 < Real.exp x ∧ 0 < Real.exp (2 * x) - 1 := by
  change 0 < x at hx
  have he : 1 < Real.exp x := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hx
  constructor
  · exact he
  · rw [exp_two_eq_sq]
    nlinarith

private lemma value_identity (x : ℝ) (hx : x ∈ U) :
    f x = rewritten x := by
  obtain ⟨he, hq⟩ := positive_exp_facts hx
  have hq' : 0 < Real.exp x ^ 2 - 1 := by
    simpa only [exp_two_eq_sq] using hq
  have hep : 0 < Real.exp x + 1 := by linarith
  have hs : 0 < Real.sqrt (Real.exp x ^ 2 - 1) := Real.sqrt_pos.2 hq'
  have hratio : 0 ≤ (Real.exp x - 1) / (Real.exp x + 1) :=
    div_nonneg (by linarith) (le_of_lt hep)
  have hr2 := Real.sq_sqrt hratio
  have hs2 := Real.sq_sqrt (le_of_lt hq')
  have hsq :
      Real.sqrt ((Real.exp x - 1) / (Real.exp x + 1)) ^ 2 =
        ((Real.exp x - 1) / Real.sqrt (Real.exp x ^ 2 - 1)) ^ 2 := by
    rw [hr2]
    field_simp [ne_of_gt hep, ne_of_gt hs]
    rw [hs2]
    ring
  have hleft := Real.sqrt_nonneg ((Real.exp x - 1) / (Real.exp x + 1))
  have hright : 0 ≤ (Real.exp x - 1) / Real.sqrt (Real.exp x ^ 2 - 1) :=
    div_nonneg (by linarith) (le_of_lt hs)
  have heq :
      Real.sqrt ((Real.exp x - 1) / (Real.exp x + 1)) =
        (Real.exp x - 1) / Real.sqrt (Real.exp x ^ 2 - 1) := by
    nlinarith [sq_nonneg
      (Real.sqrt ((Real.exp x - 1) / (Real.exp x + 1)) +
        (Real.exp x - 1) / Real.sqrt (Real.exp x ^ 2 - 1))]
  simpa [f, rewritten, exp_two_eq_sq] using heq

private lemma hasDerivAt_log_component (x : ℝ) (hx : x ∈ U) :
    HasDerivAt
      (fun y => Real.log (Real.exp y + Real.sqrt (Real.exp (2 * y) - 1)))
      (Real.exp x / Real.sqrt (Real.exp (2 * x) - 1)) x := by
  obtain ⟨he, hq⟩ := positive_exp_facts hx
  have hspos : 0 < Real.sqrt (Real.exp (2 * x) - 1) := Real.sqrt_pos.2 hq
  have hinner : HasDerivAt (fun y : ℝ => Real.exp (2 * y) - 1)
      (2 * Real.exp (2 * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (((Real.hasDerivAt_exp (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)).sub_const 1)
  have hs0 := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hinner
  have hscoef :
      1 / (2 * Real.sqrt (Real.exp (2 * x) - 1)) *
          (2 * Real.exp (2 * x)) =
        Real.exp (2 * x) / Real.sqrt (Real.exp (2 * x) - 1) := by
    field_simp [ne_of_gt hspos]
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (Real.exp (2 * y) - 1))
      (Real.exp (2 * x) / Real.sqrt (Real.exp (2 * x) - 1)) x := by
    simpa only [Function.comp_def, hscoef] using hs0
  have hsumpos :
      0 < Real.exp x + Real.sqrt (Real.exp (2 * x) - 1) :=
    add_pos (Real.exp_pos x) hspos
  have hsum := (Real.hasDerivAt_exp x).add hs
  have hlog := (Real.hasDerivAt_log (ne_of_gt hsumpos)).comp x hsum
  have hcoef :
      (Real.exp x + Real.sqrt (Real.exp (2 * x) - 1))⁻¹ *
          (Real.exp x +
            Real.exp (2 * x) / Real.sqrt (Real.exp (2 * x) - 1)) =
        Real.exp x / Real.sqrt (Real.exp (2 * x) - 1) := by
    field_simp [ne_of_gt hspos, ne_of_gt hsumpos]
    rw [exp_two_eq_sq]
    ring
  simpa only [Function.comp_def, hcoef] using hlog

private lemma hasDerivAt_neg_exp (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg

private lemma hasDerivAt_asin_component_raw (x : ℝ) (hx : x ∈ U) :
    HasDerivAt (fun y => Real.arcsin (Real.exp (-y)))
      (deriv (fun y => Real.exp (-y)) x /
        Real.sqrt (1 - Real.exp (-x) ^ 2)) x := by
  change 0 < x at hx
  have htpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
  have htlt : Real.exp (-x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hne_neg : Real.exp (-x) ≠ -1 := by linarith
  have hne_one : Real.exp (-x) ≠ 1 := ne_of_lt htlt
  have hd : deriv (fun y : ℝ => Real.exp (-y)) x = -Real.exp (-x) :=
    (hasDerivAt_neg_exp x).deriv
  have hcomp :=
    (Real.hasDerivAt_arcsin hne_neg hne_one).comp x (hasDerivAt_neg_exp x)
  simpa [Function.comp_def, hd, div_eq_mul_inv, mul_comm] using hcomp

private lemma exp_neg_sqrt_ratio (x : ℝ) (hx : x ∈ U) :
    Real.exp (-x) / Real.sqrt (1 - Real.exp (-x) ^ 2) =
      1 / Real.sqrt (Real.exp (2 * x) - 1) := by
  change 0 < x at hx
  have htpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
  have htlt : Real.exp (-x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hrpos : 0 < 1 - Real.exp (-x) ^ 2 := by
    have hp : 0 < (1 - Real.exp (-x)) * (1 + Real.exp (-x)) :=
      mul_pos (sub_pos.mpr htlt) (by linarith)
    nlinarith
  have hq : 0 < Real.exp (2 * x) - 1 := by
    rw [exp_two_eq_sq]
    have he : 1 < Real.exp x := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hx
    nlinarith
  have hs1pos : 0 < Real.sqrt (1 - Real.exp (-x) ^ 2) := Real.sqrt_pos.2 hrpos
  have hs2pos : 0 < Real.sqrt (Real.exp (2 * x) - 1) := Real.sqrt_pos.2 hq
  have hs1sq := Real.sq_sqrt (le_of_lt hrpos)
  have hs2sq := Real.sq_sqrt (le_of_lt hq)
  have het : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have het2 := congrArg (fun z : ℝ => z ^ 2) het
  ring_nf at het2
  have hsq :
      (Real.exp (-x) * Real.sqrt (Real.exp (2 * x) - 1)) ^ 2 =
        Real.sqrt (1 - Real.exp (-x) ^ 2) ^ 2 := by
    rw [hs1sq]
    calc
      (Real.exp (-x) * Real.sqrt (Real.exp (2 * x) - 1)) ^ 2 =
          Real.exp (-x) ^ 2 * Real.sqrt (Real.exp (2 * x) - 1) ^ 2 := by ring
      _ = Real.exp (-x) ^ 2 * (Real.exp (2 * x) - 1) := by rw [hs2sq]
      _ = 1 - Real.exp (-x) ^ 2 := by
        rw [exp_two_eq_sq]
        nlinarith
  have hprod :
      Real.exp (-x) * Real.sqrt (Real.exp (2 * x) - 1) =
        Real.sqrt (1 - Real.exp (-x) ^ 2) := by
    have hpnon :
        0 ≤ Real.exp (-x) * Real.sqrt (Real.exp (2 * x) - 1) :=
      mul_nonneg (le_of_lt htpos) (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg
      (Real.exp (-x) * Real.sqrt (Real.exp (2 * x) - 1) +
        Real.sqrt (1 - Real.exp (-x) ^ 2))]
  apply (div_eq_div_iff (ne_of_gt hs1pos) (ne_of_gt hs2pos)).2
  simpa using hprod

private lemma hasDerivAt_asin_component (x : ℝ) (hx : x ∈ U) :
    HasDerivAt (fun y => Real.arcsin (Real.exp (-y)))
      (-1 / Real.sqrt (Real.exp (2 * x) - 1)) x := by
  have hraw := hasDerivAt_asin_component_raw x hx
  have hd : deriv (fun y : ℝ => Real.exp (-y)) x = -Real.exp (-x) :=
    (hasDerivAt_neg_exp x).deriv
  have hcoef :
      deriv (fun y : ℝ => Real.exp (-y)) x /
          Real.sqrt (1 - Real.exp (-x) ^ 2) =
        -1 / Real.sqrt (Real.exp (2 * x) - 1) := by
    rw [hd]
    calc
      -Real.exp (-x) / Real.sqrt (1 - Real.exp (-x) ^ 2) =
          -(Real.exp (-x) / Real.sqrt (1 - Real.exp (-x) ^ 2)) := by
            rw [neg_div]
      _ = -(1 / Real.sqrt (Real.exp (2 * x) - 1)) := by
            rw [exp_neg_sqrt_ratio x hx]
      _ = -1 / Real.sqrt (Real.exp (2 * x) - 1) := by ring
  simpa only [hcoef] using hraw

private lemma hasDerivAt_neg_asin_component (x : ℝ) (hx : x ∈ U) :
    HasDerivAt (fun y => -Real.arcsin (Real.exp (-y)))
      (1 / Real.sqrt (Real.exp (2 * x) - 1)) x := by
  have hcoef :
      -(-1 / Real.sqrt (Real.exp (2 * x) - 1)) =
        1 / Real.sqrt (Real.exp (2 * x) - 1) := by
    ring
  simpa only [hcoef] using (hasDerivAt_asin_component x hx).neg

private lemma hasDerivAt_primitive (x : ℝ) (hx : x ∈ U) :
    HasDerivAt primitive (rewritten x) x := by
  have hlog := hasDerivAt_log_component x hx
  have hasin := hasDerivAt_asin_component x hx
  have hcoef :
      Real.exp x / Real.sqrt (Real.exp (2 * x) - 1) +
          -1 / Real.sqrt (Real.exp (2 * x) - 1) = rewritten x := by
    unfold rewritten
    ring
  simpa [primitive, hcoef] using hlog.add hasin

private lemma translates_of_same_deriv {F p g : ℝ → ℝ}
    (hF : ∀ x ∈ U, HasDerivAt F (g x) x)
    (hp : ∀ x ∈ U, HasDerivAt p (g x) x) :
    F ∈ Translates p := by
  have hdiff : DifferentiableOn ℝ (fun z => F z - p z) U := by
    intro z hz
    exact ((hF z hz).sub (hp z hz)).differentiableAt.differentiableWithinAt
  have hzero : ∀ z ∈ U, deriv (fun y => F y - p y) z = 0 := by
    intro z hz
    simpa using ((hF z hz).sub (hp z hz)).deriv
  refine ⟨F 1 - p 1, ?_⟩
  intro x hx
  have hx' : x ∈ Set.Ioi (0 : ℝ) := by simpa [U] using hx
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hc : F x - p x = F 1 - p 1 := by
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (by simpa [U] using hdiff) (by simpa [U] using hzero)
      (x := x) (y := (1 : ℝ)) hx' h1
  linarith

private theorem family_eq_translates : Family f = Translates primitive := by
  ext F
  constructor
  · intro hF
    apply translates_of_same_deriv
    · intro x hx
      simpa only [value_identity x hx] using hF x hx
    · exact hasDerivAt_primitive
  · rintro ⟨C, hC⟩
    change ∀ x ∈ U, HasDerivAt F (f x) x
    intro x hx
    have hmem : Set.Ioi (0 : ℝ) ∈ nhds x :=
      isOpen_Ioi.mem_nhds (by simpa [U] using hx)
    have hev : (fun y => primitive y + C) =ᶠ[nhds x] F := by
      filter_upwards [hmem] with y hy
      exact (hC y (by simpa [U] using hy)).symm
    have hp := (hasDerivAt_primitive x hx).add_const C
    have hFderiv : HasDerivAt F (rewritten x) x :=
      hp.congr_of_eventuallyEq hev.symm
    simpa only [value_identity x hx] using hFderiv

private theorem split_eq_translates : Split = Translates primitive := by
  ext F
  constructor
  · rintro ⟨A, hA, B, hB, C, hF⟩
    have hAt : A ∈ Translates
        (fun y => Real.log (Real.exp y + Real.sqrt (Real.exp (2 * y) - 1))) :=
      translates_of_same_deriv hA hasDerivAt_log_component
    have hBt : B ∈ Translates
        (fun y => -Real.arcsin (Real.exp (-y))) :=
      translates_of_same_deriv hB hasDerivAt_neg_asin_component
    rcases hAt with ⟨CA, hCA⟩
    rcases hBt with ⟨CB, hCB⟩
    refine ⟨CA - CB + C, ?_⟩
    intro x hx
    rw [hF x hx, hCA x hx, hCB x hx]
    unfold primitive
    ring
  · rintro ⟨C, hF⟩
    refine ⟨
      (fun y => Real.log (Real.exp y + Real.sqrt (Real.exp (2 * y) - 1))),
      ?_, (fun y => -Real.arcsin (Real.exp (-y))), ?_, C, ?_⟩
    · exact hasDerivAt_log_component
    · exact hasDerivAt_neg_asin_component
    · intro x hx
      rw [hF x hx]
      unfold primitive
      ring

private theorem substitutions_eq_translates :
    Substitutions = Translates primitive := by
  ext F
  constructor
  · rintro ⟨A, hA, B, hB, C, hF⟩
    have hAt : A ∈ Translates
        (fun y => Real.log (Real.exp y + Real.sqrt (Real.exp (2 * y) - 1))) := by
      apply translates_of_same_deriv hA
      intro x hx
      have hd : deriv Real.exp x = Real.exp x := (Real.hasDerivAt_exp x).deriv
      simpa [hd, exp_two_eq_sq] using hasDerivAt_log_component x hx
    have hBt : B ∈ Translates (fun y => Real.arcsin (Real.exp (-y))) :=
      translates_of_same_deriv hB hasDerivAt_asin_component_raw
    rcases hAt with ⟨CA, hCA⟩
    rcases hBt with ⟨CB, hCB⟩
    refine ⟨CA + CB + C, ?_⟩
    intro x hx
    rw [hF x hx, hCA x hx, hCB x hx]
    unfold primitive
    ring
  · rintro ⟨C, hF⟩
    refine ⟨
      (fun y => Real.log (Real.exp y + Real.sqrt (Real.exp (2 * y) - 1))),
      ?_, (fun y => Real.arcsin (Real.exp (-y))), ?_, C, ?_⟩
    · intro x hx
      have hd : deriv Real.exp x = Real.exp x := (Real.hasDerivAt_exp x).deriv
      simpa [hd, exp_two_eq_sq] using hasDerivAt_log_component x hx
    · exact hasDerivAt_asin_component_raw
    · intro x hx
      simpa [primitive] using hF x hx

theorem gap1 : Family f = Family rewritten := by
  ext F
  constructor
  · intro h
    change ∀ x ∈ U, HasDerivAt F (rewritten x) x
    intro x hx
    simpa only [value_identity x hx] using h x hx
  · intro h
    change ∀ x ∈ U, HasDerivAt F (f x) x
    intro x hx
    simpa only [value_identity x hx] using h x hx
theorem gap2 : Family f = Split := by
  exact family_eq_translates.trans split_eq_translates.symm
theorem gap3 : Family f = Substitutions := by
  exact family_eq_translates.trans substitutions_eq_translates.symm
theorem gap4 : Substitutions = Translates primitive := by
  exact substitutions_eq_translates
theorem gap5 : Family f = Translates primitive := by
  exact family_eq_translates

end
end ProofGap.Exercise2088
