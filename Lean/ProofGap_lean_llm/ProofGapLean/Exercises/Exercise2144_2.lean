import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2144_2

noncomputable section

def branch : Set ℝ := Set.Ioo 0 1
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def logTerm (x : ℝ) := Real.log (x / Real.sqrt (1 - x))
def integrand (x : ℝ) :=
  x / Real.sqrt (1 - x ^ 2) * logTerm x
def FirstByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x ∈ branch,
      HasDerivAt G
        (logTerm x * deriv (fun y : ℝ => Real.sqrt (1 - y ^ 2)) x) x) ∧
    ∀ x ∈ branch, F x = -G x}
def residual (x : ℝ) :=
  Real.sqrt (1 - x ^ 2) * (2 - x) / (x * (1 - x))
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residual,
    ∀ x ∈ branch,
      F x = -Real.sqrt (1 - x ^ 2) * logTerm x + 1 / 2 * G x}
def rationalizedResidual (x : ℝ) :=
  (1 - x ^ 2) * (2 - x) /
    (x * (1 - x) * Real.sqrt (1 - x ^ 2))
def simplifiedResidual (x : ℝ) :=
  (2 + x - x ^ 2) / (x * Real.sqrt (1 - x ^ 2))
def ThreePartFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn
      (fun x => 1 / (x * Real.sqrt (1 - x ^ 2))),
    ∃ B ∈ AntiderivativesOn (fun x => 1 / Real.sqrt (1 - x ^ 2)),
    ∃ D ∈ AntiderivativesOn (fun x => x / Real.sqrt (1 - x ^ 2)),
    ∀ x ∈ branch, F x = 2 * A x + B x - D x}
def ReciprocalPullbackFamily : Set (ℝ → ℝ) :=
  {F | ∃ A : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt A
          (deriv (fun y : ℝ => 1 / y) x /
            Real.sqrt ((1 / x) ^ 2 - 1)) x) ∧
    ∀ x ∈ branch,
      F x = -2 * A x + Real.arcsin x + Real.sqrt (1 - x ^ 2)}
def residualPrimitiveRaw (x : ℝ) :=
  -2 * Real.log |1 / x + Real.sqrt (1 / x ^ 2 - 1)| +
    Real.arcsin x + Real.sqrt (1 - x ^ 2)
def residualPrimitive (x : ℝ) :=
  -2 * Real.log ((1 + Real.sqrt (1 - x ^ 2)) / x) +
    Real.arcsin x + Real.sqrt (1 - x ^ 2)
def primitive (x : ℝ) :=
  (1 / 2 - logTerm x) * Real.sqrt (1 - x ^ 2) -
    Real.log ((1 + Real.sqrt (1 - x ^ 2)) / x) +
    1 / 2 * Real.arcsin x

private lemma pg_branch_facts {x : ℝ} (hx : x ∈ branch) :
    0 < x ∧ 0 < 1 - x ∧ 0 < 1 - x ^ 2 := by
  change x ∈ Set.Ioo (0 : ℝ) 1 at hx
  refine ⟨hx.1, sub_pos.mpr hx.2, ?_⟩
  have hplus : 0 < 1 + x := add_pos (by norm_num) hx.1
  have hprod := mul_pos (sub_pos.mpr hx.2) hplus
  nlinarith

private lemma pg_hasDerivAt_congr_branch {f g : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ branch) (hfg : ∀ y ∈ branch, f y = g y)
    (hg : HasDerivAt g d x) : HasDerivAt f d x := by
  apply hg.congr_of_eventuallyEq
  have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [branch] using hx
  filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
  exact hfg y (by simpa [branch] using hy)

private lemma pg_deriv_s (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hu : 0 < 1 - x ^ 2 := (pg_branch_facts hx).2.2
  have hi : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1
    norm_num [id] <;> ring
  have hc := (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x hi
  convert hc using 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 hu)] <;> ring

private lemma pg_logTerm_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt logTerm ((2 - x) / (2 * x * (1 - x))) x := by
  have hf := pg_branch_facts hx
  have hx0 : x ≠ 0 := ne_of_gt hf.1
  have h1 : 0 < 1 - x := hf.2.1
  have hs0 : Real.sqrt (1 - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1)
  have hs2 : Real.sqrt (1 - x) ^ 2 = 1 - x :=
    Real.sq_sqrt (le_of_lt h1)
  have hi : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1
    norm_num [id] <;> ring
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y))
      (-1 / (2 * Real.sqrt (1 - x))) x := by
    have hc := (Real.hasDerivAt_sqrt (ne_of_gt h1)).comp x hi
    convert hc using 1
    field_simp [hs0] <;> ring
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hq : HasDerivAt (fun y : ℝ => y / Real.sqrt (1 - y))
      ((1 * Real.sqrt (1 - x) -
        x * (-1 / (2 * Real.sqrt (1 - x)))) /
        Real.sqrt (1 - x) ^ 2) x := by
    exact hid.div hs hs0
  have hq0 : x / Real.sqrt (1 - x) ≠ 0 := div_ne_zero hx0 hs0
  have hl0 : HasDerivAt Real.log
      ((x / Real.sqrt (1 - x))⁻¹) (x / Real.sqrt (1 - x)) :=
    Real.hasDerivAt_log hq0
  have hl : HasDerivAt (fun y : ℝ => Real.log (y / Real.sqrt (1 - y)))
      ((x / Real.sqrt (1 - x))⁻¹ *
        ((1 * Real.sqrt (1 - x) -
          x * (-1 / (2 * Real.sqrt (1 - x)))) /
          Real.sqrt (1 - x) ^ 2)) x := by
    simpa only [Function.comp_apply] using hl0.comp x hq
  change HasDerivAt (fun y : ℝ => Real.log (y / Real.sqrt (1 - y)))
    ((2 - x) / (2 * x * (1 - x))) x
  convert hl using 1
  field_simp [hx0, hs0]
  rw [hs2]
  ring_nf

private lemma pg_arcsin_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
  have hf := pg_branch_facts hx
  exact Real.hasDerivAt_arcsin (by linarith [hf.1]) (by linarith [hf.2.1])

private lemma pg_neglog_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ => -Real.log ((1 + Real.sqrt (1 - y ^ 2)) / y))
      (1 / (x * Real.sqrt (1 - x ^ 2))) x := by
  have hf := pg_branch_facts hx
  have hx0 : x ≠ 0 := ne_of_gt hf.1
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hf.2.2)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hf.2.2)
  have hs := pg_deriv_s x hx
  have hn := (hasDerivAt_const x (1 : ℝ)).add hs
  have hnpos : 0 < 1 + Real.sqrt (1 - x ^ 2) := by positivity
  let q : ℝ → ℝ :=
    fun y => (1 + Real.sqrt (1 - y ^ 2)) / y
  have hq0 : q x ≠ 0 := by
    dsimp only [q]
    exact div_ne_zero (ne_of_gt hnpos) hx0
  have hq : HasDerivAt q
      (((-x / Real.sqrt (1 - x ^ 2)) * x -
        (1 + Real.sqrt (1 - x ^ 2))) / x ^ 2) x := by
    dsimp only [q]
    convert hn.div (hasDerivAt_id x) hx0 using 1
    norm_num [id] <;> ring
  have hl0 : HasDerivAt Real.log (q x)⁻¹ (q x) :=
    Real.hasDerivAt_log hq0
  have hlq : HasDerivAt (Real.log ∘ q)
      ((q x)⁻¹ *
        (((-x / Real.sqrt (1 - x ^ 2)) * x -
          (1 + Real.sqrt (1 - x ^ 2))) / x ^ 2)) x :=
    hl0.comp x hq
  have hl : HasDerivAt
      (fun y : ℝ => Real.log ((1 + Real.sqrt (1 - y ^ 2)) / y))
      (((1 + Real.sqrt (1 - x ^ 2)) / x)⁻¹ *
        (((-x / Real.sqrt (1 - x ^ 2)) * x -
          (1 + Real.sqrt (1 - x ^ 2))) / x ^ 2)) x := by
    simpa only [q, Function.comp_apply] using hlq
  have hneg : HasDerivAt
      (fun y : ℝ => -Real.log ((1 + Real.sqrt (1 - y ^ 2)) / y))
      (-(((1 + Real.sqrt (1 - x ^ 2)) / x)⁻¹ *
        (((-x / Real.sqrt (1 - x ^ 2)) * x -
          (1 + Real.sqrt (1 - x ^ 2))) / x ^ 2))) x := by
    exact hl.neg
  convert hneg using 1
  field_simp [hx0, hs0, ne_of_gt hnpos] <;> nlinarith [hs2]

private lemma pg_poslog_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ => Real.log ((1 + Real.sqrt (1 - y ^ 2)) / y))
      (-1 / (x * Real.sqrt (1 - x ^ 2))) x := by
  convert (pg_neglog_deriv x hx).neg using 1
  · funext y
    simp
  · ring

private lemma pg_neg_s_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => -Real.sqrt (1 - y ^ 2))
      (x / Real.sqrt (1 - x ^ 2)) x := by
  convert (pg_deriv_s x hx).neg using 1
  ring

private lemma pg_residual_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt residualPrimitive (residual x) x := by
  have hlog := pg_neglog_deriv x hx
  have hasin := pg_arcsin_deriv x hx
  have hs := pg_deriv_s x hx
  have h := (hlog.const_mul 2).add hasin |>.add hs
  convert h using 1
  · funext y
    change
      -2 * Real.log ((1 + Real.sqrt (1 - y ^ 2)) / y) +
          Real.arcsin y + Real.sqrt (1 - y ^ 2) =
        2 * (-Real.log ((1 + Real.sqrt (1 - y ^ 2)) / y)) +
          Real.arcsin y + Real.sqrt (1 - y ^ 2)
    ring
  · unfold residual
    have hf := pg_branch_facts hx
    have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
      Real.sq_sqrt (le_of_lt hf.2.2)
    field_simp [ne_of_gt hf.1, ne_of_gt hf.2.1,
      ne_of_gt (Real.sqrt_pos.2 hf.2.2)]
    rw [hs2] <;> ring

private lemma pg_primitive_identity (x : ℝ) :
    primitive x =
      -Real.sqrt (1 - x ^ 2) * logTerm x + 1 / 2 * residualPrimitive x := by
  unfold primitive residualPrimitive
  ring

private lemma pg_primitive_deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have hs := pg_deriv_s x hx
  have hl := pg_logTerm_deriv x hx
  have hr := pg_residual_deriv x hx
  have h := (hs.mul hl).neg.add (hr.const_mul (1 / 2))
  convert h using 1
  · funext y
    change primitive y =
      -(Real.sqrt (1 - y ^ 2) * logTerm y) +
        1 / 2 * residualPrimitive y
    rw [pg_primitive_identity y]
    ring
  · unfold integrand residual
    have hf := pg_branch_facts hx
    have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
      Real.sq_sqrt (le_of_lt hf.2.2)
    field_simp [ne_of_gt hf.1, ne_of_gt hf.2.1,
      ne_of_gt (Real.sqrt_pos.2 hf.2.2)]
    rw [hs2] <;> ring

private theorem pg_antiderivatives_eq_primitive {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (f x) x at hF
    refine ⟨F (1 / 2) - p (1 / 2), ?_⟩
    intro x hx
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) (Set.Ioo 0 1) := by
      intro y hy
      have hy' : y ∈ branch := by simpa [branch] using hy
      exact ((hF y hy').sub (hp y hy')).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        deriv (fun z => F z - p z) y = 0 := by
      intro y hy
      have hy' : y ∈ branch := by simpa [branch] using hy
      simpa using ((hF y hy').sub (hp y hy')).deriv
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [branch] using hx
    have hc : F x - p x = F (1 / 2) - p (1 / 2) :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hzero hx' (by norm_num)
    linarith
  · rintro ⟨C, hF⟩
    intro x hx
    exact pg_hasDerivAt_congr_branch hx (fun y hy => hF y hy)
      ((hp x hx).add_const C)

private lemma pg_residual_rationalized (x : ℝ) (hx : x ∈ branch) :
    residual x = rationalizedResidual x := by
  have hf := pg_branch_facts hx
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hf.2.2)
  unfold residual rationalizedResidual
  field_simp [ne_of_gt hf.1, ne_of_gt hf.2.1,
    ne_of_gt (Real.sqrt_pos.2 hf.2.2)]
  rw [hs2] <;> ring

private lemma pg_rationalized_simplified (x : ℝ) (hx : x ∈ branch) :
    rationalizedResidual x = simplifiedResidual x := by
  have hf := pg_branch_facts hx
  unfold rationalizedResidual simplifiedResidual
  field_simp [ne_of_gt hf.1, ne_of_gt hf.2.1,
    ne_of_gt (Real.sqrt_pos.2 hf.2.2)] <;> ring

private lemma pg_sqrt_recip (x : ℝ) (hx : x ∈ branch) :
    Real.sqrt ((1 / x) ^ 2 - 1) = Real.sqrt (1 - x ^ 2) / x := by
  have hf := pg_branch_facts hx
  have hx0 : x ≠ 0 := ne_of_gt hf.1
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hf.2.2
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hf.2.2)
  have heq : (1 / x) ^ 2 - 1 =
      (Real.sqrt (1 - x ^ 2) / x) ^ 2 := by
    field_simp [hx0] <;> nlinarith [hs2]
  rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hspos hf.1)]

private lemma pg_reciprocal_coefficient (x : ℝ) (hx : x ∈ branch) :
    deriv (fun y : ℝ => 1 / y) x /
        Real.sqrt ((1 / x) ^ 2 - 1) =
      -1 / (x * Real.sqrt (1 - x ^ 2)) := by
  have hf := pg_branch_facts hx
  have hx0 : x ≠ 0 := ne_of_gt hf.1
  have hd : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx0 using 1
    norm_num [id] <;> ring
  rw [hd.deriv, pg_sqrt_recip x hx]
  field_simp [hx0, ne_of_gt (Real.sqrt_pos.2 hf.2.2)] <;> ring

private lemma pg_raw_eq (x : ℝ) (hx : x ∈ branch) :
    residualPrimitiveRaw x = residualPrimitive x := by
  have hf := pg_branch_facts hx
  have hx0 : x ≠ 0 := ne_of_gt hf.1
  have hsqrt : Real.sqrt (1 / x ^ 2 - 1) =
      Real.sqrt (1 - x ^ 2) / x := by
    rw [show 1 / x ^ 2 - 1 = (1 / x) ^ 2 - 1 by
      field_simp [hx0] <;> simp <;> ring]
    exact pg_sqrt_recip x hx
  have harg : 1 / x + Real.sqrt (1 / x ^ 2 - 1) =
      (1 + Real.sqrt (1 - x ^ 2)) / x := by
    rw [hsqrt]
    field_simp [hx0]
  have hnum : 0 < 1 + Real.sqrt (1 - x ^ 2) := by
    positivity
  have hpos : 0 < (1 + Real.sqrt (1 - x ^ 2)) / x :=
    div_pos hnum hf.1
  unfold residualPrimitiveRaw residualPrimitive
  rw [harg, abs_of_pos hpos]

theorem gap1 :
    AntiderivativesOn integrand = FirstByPartsFamily := by
  rw [pg_antiderivatives_eq_primitive pg_primitive_deriv]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun x => -primitive x - C, ?_, ?_⟩
    · intro x hx
      have hs := (pg_deriv_s x hx).deriv
      rw [hs]
      convert (pg_primitive_deriv x hx).neg.sub_const C using 1
      unfold integrand
      ring
    · intro x hx
      rw [hF x hx]
      ring
  · rintro ⟨G, hG, hFG⟩
    have hGa : G ∈ AntiderivativesOn (fun x => -integrand x) := by
      intro x hx
      have hs := (pg_deriv_s x hx).deriv
      have h := hG x hx
      rw [hs] at h
      convert h using 1
      unfold integrand
      ring
    have hEq := pg_antiderivatives_eq_primitive
      (f := fun x => -integrand x) (p := fun x => -primitive x)
      (fun x hx => (pg_primitive_deriv x hx).neg)
    have hGp : G ∈ PrimitiveFamily (fun x => -primitive x) := by
      rw [← hEq]
      exact hGa
    rcases hGp with ⟨C, hGC⟩
    refine ⟨-C, ?_⟩
    intro x hx
    rw [hFG x hx, hGC x hx]
    ring
theorem gap2 :
    AntiderivativesOn integrand = ByPartsFamily := by
  rw [pg_antiderivatives_eq_primitive pg_primitive_deriv]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun x => residualPrimitive x + 2 * C, ?_, ?_⟩
    · intro x hx
      exact (pg_residual_deriv x hx).add_const (2 * C)
    · intro x hx
      rw [hF x hx, pg_primitive_identity x]
      ring
  · rintro ⟨G, hGa, hFG⟩
    have hEq := pg_antiderivatives_eq_primitive pg_residual_deriv
    have hGp : G ∈ PrimitiveFamily residualPrimitive := by
      rw [← hEq]
      exact hGa
    rcases hGp with ⟨C, hGC⟩
    refine ⟨C / 2, ?_⟩
    intro x hx
    rw [hFG x hx, hGC x hx, pg_primitive_identity x]
    ring
theorem gap3 :
    AntiderivativesOn residual =
      AntiderivativesOn rationalizedResidual := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    intro x hx
    have h := hF x hx
    rw [pg_residual_rationalized x hx] at h
    exact h
  · intro hF
    intro x hx
    have h := hF x hx
    rw [← pg_residual_rationalized x hx] at h
    exact h
theorem gap4 :
    AntiderivativesOn rationalizedResidual =
      AntiderivativesOn simplifiedResidual := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    intro x hx
    have h := hF x hx
    rw [pg_rationalized_simplified x hx] at h
    exact h
  · intro hF
    intro x hx
    have h := hF x hx
    rw [← pg_rationalized_simplified x hx] at h
    exact h
theorem gap5 :
    AntiderivativesOn residual =
      AntiderivativesOn simplifiedResidual := by
  exact gap3.trans gap4
theorem gap6 :
    AntiderivativesOn residual = ThreePartFamily := by
  rw [pg_antiderivatives_eq_primitive pg_residual_deriv]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun x => -Real.log ((1 + Real.sqrt (1 - x ^ 2)) / x) + C / 2, ?_, ?_⟩
    · intro x hx
      exact (pg_neglog_deriv x hx).add_const (C / 2)
    · refine ⟨fun x => Real.arcsin x, ?_, ?_⟩
      · intro x hx
        exact pg_arcsin_deriv x hx
      · refine ⟨fun x => -Real.sqrt (1 - x ^ 2), ?_, ?_⟩
        · intro x hx
          exact pg_neg_s_deriv x hx
        · intro x hx
          rw [hF x hx]
          unfold residualPrimitive
          ring
  · rintro ⟨A, hAa, B, hBa, D, hDa, hF⟩
    have hEA := pg_antiderivatives_eq_primitive pg_neglog_deriv
    have hAp : A ∈ PrimitiveFamily
        (fun x => -Real.log ((1 + Real.sqrt (1 - x ^ 2)) / x)) := by
      rw [← hEA]
      exact hAa
    have hEB := pg_antiderivatives_eq_primitive pg_arcsin_deriv
    have hBp : B ∈ PrimitiveFamily Real.arcsin := by
      rw [← hEB]
      exact hBa
    have hED := pg_antiderivatives_eq_primitive
      (f := fun x => x / Real.sqrt (1 - x ^ 2))
      (p := fun x => -Real.sqrt (1 - x ^ 2))
      pg_neg_s_deriv
    have hDp : D ∈ PrimitiveFamily (fun x => -Real.sqrt (1 - x ^ 2)) := by
      rw [← hED]
      exact hDa
    rcases hAp with ⟨CA, hA⟩
    rcases hBp with ⟨CB, hB⟩
    rcases hDp with ⟨CD, hD⟩
    refine ⟨2 * CA + CB - CD, ?_⟩
    intro x hx
    rw [hF x hx, hA x hx, hB x hx, hD x hx]
    unfold residualPrimitive
    ring
theorem gap7 :
    ThreePartFamily = ReciprocalPullbackFamily := by
  rw [← gap6]
  rw [pg_antiderivatives_eq_primitive pg_residual_deriv]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun x => Real.log ((1 + Real.sqrt (1 - x ^ 2)) / x) - C / 2, ?_, ?_⟩
    · intro x hx
      rw [pg_reciprocal_coefficient x hx]
      exact (pg_poslog_deriv x hx).sub_const (C / 2)
    · intro x hx
      rw [hF x hx]
      unfold residualPrimitive
      ring
  · rintro ⟨A, hA, hF⟩
    have hLA : ∀ x ∈ branch,
        HasDerivAt A
          (-1 / (x * Real.sqrt (1 - x ^ 2))) x := by
      intro x hx
      have h := hA x hx
      rw [pg_reciprocal_coefficient x hx] at h
      exact h
    have hEL := pg_antiderivatives_eq_primitive
      (f := fun x => -1 / (x * Real.sqrt (1 - x ^ 2)))
      (p := fun x => Real.log ((1 + Real.sqrt (1 - x ^ 2)) / x))
      pg_poslog_deriv
    have hLp : A ∈ PrimitiveFamily
        (fun x => Real.log ((1 + Real.sqrt (1 - x ^ 2)) / x)) := by
      rw [← hEL]
      exact hLA
    rcases hLp with ⟨C, hAC⟩
    refine ⟨-2 * C, ?_⟩
    intro x hx
    rw [hF x hx, hAC x hx]
    unfold residualPrimitive
    ring
theorem gap8 :
    AntiderivativesOn residual = ReciprocalPullbackFamily := by
  exact gap6.trans gap7
theorem gap9 :
    AntiderivativesOn residual = PrimitiveFamily residualPrimitiveRaw := by
  apply pg_antiderivatives_eq_primitive
  intro x hx
  apply pg_hasDerivAt_congr_branch hx (fun y hy => pg_raw_eq y hy)
  exact pg_residual_deriv x hx
theorem gap10 :
    PrimitiveFamily residualPrimitiveRaw =
      PrimitiveFamily residualPrimitive := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← pg_raw_eq x hx]
    exact hF x hx
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [pg_raw_eq x hx]
    exact hF x hx
theorem gap11 :
    AntiderivativesOn residual = PrimitiveFamily residualPrimitive := by
  exact gap9.trans gap10
theorem gap12 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact pg_antiderivatives_eq_primitive pg_primitive_deriv

end
end ProofGap.Exercise2144_2
