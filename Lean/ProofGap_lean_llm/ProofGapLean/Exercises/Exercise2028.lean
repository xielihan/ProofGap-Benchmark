import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2028
noncomputable section

def branch : Set ℝ := Set.Ioo (-Real.pi) Real.pi
def t (x : ℝ) := Real.tan (x / 2)
def integrand (ε x : ℝ) := 1 / (1 + ε * Real.cos x)
def rational (ε u : ℝ) := 1 / (1 + ε + (1 - ε) * u ^ 2)
def normalizedSub (ε u : ℝ) := 1 / (1 + (1 - ε) / (1 + ε) * u ^ 2)
def normalizedSuper (ε u : ℝ) := 1 / ((ε + 1) / (ε - 1) - u ^ 2)
def primitiveSub (ε u : ℝ) :=
  2 / Real.sqrt (1 - ε ^ 2) *
    Real.arctan (u * Real.sqrt ((1 - ε) / (1 + ε)))
def primitiveSuperT (ε u : ℝ) :=
  1 / Real.sqrt (ε ^ 2 - 1) *
    Real.log |(Real.sqrt (ε + 1) + Real.sqrt (ε - 1) * u) /
      (Real.sqrt (ε + 1) - Real.sqrt (ε - 1) * u)|
def primitiveSuper (ε x : ℝ) :=
  1 / Real.sqrt (ε ^ 2 - 1) *
    Real.log |(ε + Real.cos x + Real.sqrt (ε ^ 2 - 1) * Real.sin x) /
      (1 + ε * Real.cos x)|
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def RegularSuper (U : Set ℝ) (ε : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ U ⊆ branch ∧
    (∀ x ∈ U, 1 + ε * Real.cos x ≠ 0 ∧
      ε + Real.cos x + Real.sqrt (ε ^ 2 - 1) * Real.sin x ≠ 0)

private theorem hasDerivAt_t_on_branch {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt t (deriv t x) x := by
  change -Real.pi < x ∧ x < Real.pi at hx
  have hxhalf : x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcpos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hxhalf
  have h :=
    (Real.hasDerivAt_tan (ne_of_gt hcpos)).comp x
      ((hasDerivAt_id x).div_const 2)
  have ht : HasDerivAt t ((1 / Real.cos (x / 2) ^ 2) * (1 / 2)) x := by
    simpa [t] using h
  exact ht.differentiableAt.hasDerivAt

theorem gap1 (ε x : ℝ) (hx : x ∈ branch)
    (hden : 1 + ε * Real.cos x ≠ 0) :
    integrand ε x = 2 * rational ε (t x) * deriv t x := by
  change -Real.pi < x ∧ x < Real.pi at hx
  have hxhalf : x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcpos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hxhalf
  have hc : Real.cos (x / 2) ≠ 0 := ne_of_gt hcpos
  have ht0 :=
    (Real.hasDerivAt_tan hc).comp x ((hasDerivAt_id x).div_const 2)
  have ht :
      HasDerivAt t ((1 / Real.cos (x / 2) ^ 2) * (1 / 2)) x := by
    simpa [t] using ht0
  have hunit := Real.sin_sq_add_cos_sq (x / 2)
  have hcosx :
      Real.cos x = Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 := by
    rw [show x = x / 2 + x / 2 by ring, Real.cos_add]
    ring
  have hr :
      (1 + ε + (1 - ε) * Real.tan (x / 2) ^ 2) *
          Real.cos (x / 2) ^ 2 =
        1 + ε * Real.cos x := by
    rw [hcosx, Real.tan_eq_sin_div_cos]
    field_simp [hc]
    nlinarith
  have hrden :
      1 + ε + (1 - ε) * Real.tan (x / 2) ^ 2 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hr
    exact hden hr.symm
  rw [ht.deriv]
  unfold integrand rational t
  field_simp [hc, hden, hrden]
  nlinarith [hr]
theorem gap2 (ε u : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    2 * rational ε u = 2 / (1 + ε) * normalizedSub ε u := by
  have hep : 0 < 1 + ε := by linarith
  have hq : 0 < (1 - ε) / (1 + ε) :=
    div_pos (sub_pos.mpr hε1) hep
  have hn :
      0 < 1 + (1 - ε) / (1 + ε) * u ^ 2 := by
    nlinarith [sq_nonneg u]
  unfold rational normalizedSub
  field_simp [ne_of_gt hep, ne_of_gt hn] <;> ring
theorem gap3 (ε u : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasDerivAt (primitiveSub ε) (2 * rational ε u) u := by
  have hep : 0 < 1 + ε := by linarith
  have hquad : 0 < 1 - ε ^ 2 := by nlinarith
  have hratio : 0 < (1 - ε) / (1 + ε) :=
    div_pos (sub_pos.mpr hε1) hep
  let q := Real.sqrt ((1 - ε) / (1 + ε))
  let d := Real.sqrt (1 - ε ^ 2)
  have hqpos : 0 < q := Real.sqrt_pos.2 hratio
  have hdpos : 0 < d := Real.sqrt_pos.2 hquad
  have hq2 : q ^ 2 = (1 - ε) / (1 + ε) :=
    Real.sq_sqrt (le_of_lt hratio)
  have hd2 : d ^ 2 = 1 - ε ^ 2 :=
    Real.sq_sqrt (le_of_lt hquad)
  have hqrel : (1 + ε) * q ^ 2 = 1 - ε := by
    rw [hq2]
    field_simp [ne_of_gt hep]
  have hsquare : ((1 + ε) * q) ^ 2 = d ^ 2 := by
    calc
      ((1 + ε) * q) ^ 2 = (1 + ε) * ((1 + ε) * q ^ 2) := by ring
      _ = (1 + ε) * (1 - ε) := by rw [hqrel]
      _ = d ^ 2 := by rw [hd2]; ring
  have hscale : d = (1 + ε) * q := by
    have hpq : 0 < (1 + ε) * q := mul_pos hep hqpos
    have hsum : 0 < (1 + ε) * q + d := add_pos hpq hdpos
    have hfactor :
        ((1 + ε) * q - d) * ((1 + ε) * q + d) = 0 := by
      calc
        ((1 + ε) * q - d) * ((1 + ε) * q + d) =
            ((1 + ε) * q) ^ 2 - d ^ 2 := by ring
        _ = 0 := by rw [hsquare]; ring
    have hleft :=
      (mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hsum)
    linarith
  have hz : 1 + (u * q) ^ 2 ≠ 0 := by positivity
  have hdeneq :
      1 + ε + (1 - ε) * u ^ 2 =
        (1 + ε) * (1 + (u * q) ^ 2) := by
    calc
      1 + ε + (1 - ε) * u ^ 2 =
          (1 + ε) + (1 - ε) * u ^ 2 := by ring
      _ = (1 + ε) + ((1 + ε) * q ^ 2) * u ^ 2 := by rw [hqrel]
      _ = (1 + ε) * (1 + (u * q) ^ 2) := by ring
  have hu : HasDerivAt (fun v : ℝ => v * q) q u := by
    simpa using (hasDerivAt_id u).mul_const q
  have ha := (Real.hasDerivAt_arctan (u * q)).comp u hu
  have hp := ha.const_mul (2 / d)
  change HasDerivAt
    (fun v => 2 / d * Real.arctan (v * q))
    (2 * (1 / (1 + ε + (1 - ε) * u ^ 2))) u
  convert hp using 1
  rw [hdeneq, hscale]
  field_simp [ne_of_gt hep, ne_of_gt hqpos, hz] <;> ring
theorem gap4 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Family branch (integrand ε) =
      Translates branch (fun x => primitiveSub ε (t x)) := by
  have hp : ∀ x ∈ branch,
      HasDerivAt (fun y => primitiveSub ε (t y)) (integrand ε x) x := by
    intro x hx
    have hcos := Real.neg_one_le_cos x
    have hdenpos : 0 < 1 + ε * Real.cos x := by
      nlinarith
    have hc := hasDerivAt_t_on_branch hx
    have hcomp := (gap3 ε (t x) hε0 hε1).comp x hc
    convert hcomp using 1
    exact gap1 ε x hx (ne_of_gt hdenpos)
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand ε x) x) ↔
      ∃ C, ∀ x ∈ branch, F x = primitiveSub ε (t x) + C
  constructor
  · intro hF
    let p : ℝ → ℝ := fun y => primitiveSub ε (t y)
    have hg : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      simpa [p] using (hF x hx).sub (hp x hx)
    have hgdiff : DifferentiableOn ℝ (fun y => F y - p y) branch := by
      intro x hx
      exact (hg x hx).differentiableAt.differentiableWithinAt
    have hgzero : ∀ x ∈ branch, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      exact (hg x hx).deriv
    have hzero : (0 : ℝ) ∈ branch := by
      change -Real.pi < (0 : ℝ) ∧ (0 : ℝ) < Real.pi
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F 0 - p 0, ?_⟩
    intro x hx
    have heq :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hgdiff hgzero hx hzero
    dsimp [p] at heq ⊢
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hbase := (hp x hx).add_const C
    have hev :
        F =ᶠ[nhds x] (fun y => primitiveSub ε (t y) + C) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hC y hy
    exact hbase.congr_of_eventuallyEq hev
theorem gap5 (ε u : ℝ) (hε : 1 < ε) :
    2 * rational ε u = 2 / (ε - 1) * normalizedSuper ε u := by
  have he : ε - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hε)
  have hfac :
      1 + ε + (1 - ε) * u ^ 2 =
        (ε - 1) * ((ε + 1) / (ε - 1) - u ^ 2) := by
    field_simp [he]
    ring
  unfold rational normalizedSuper
  rw [hfac]
  by_cases hz : (ε + 1) / (ε - 1) - u ^ 2 = 0
  · simp [hz]
  · field_simp [he, hz] <;> ring
theorem gap6 (ε u : ℝ) (hε : 1 < ε)
    (hden : (ε + 1) - (ε - 1) * u ^ 2 ≠ 0) :
    HasDerivAt (primitiveSuperT ε) (2 * rational ε u) u := by
  let a := Real.sqrt (ε + 1)
  let b := Real.sqrt (ε - 1)
  let d := Real.sqrt (ε ^ 2 - 1)
  let n : ℝ → ℝ := fun v => a + b * v
  let m : ℝ → ℝ := fun v => a - b * v
  have haarg : 0 < ε + 1 := by linarith
  have hbarg : 0 < ε - 1 := by linarith
  have hdarg : 0 < ε ^ 2 - 1 := by nlinarith
  have hapos : 0 < a := Real.sqrt_pos.2 haarg
  have hbpos : 0 < b := Real.sqrt_pos.2 hbarg
  have hdpos : 0 < d := Real.sqrt_pos.2 hdarg
  have ha2 : a ^ 2 = ε + 1 := Real.sq_sqrt (le_of_lt haarg)
  have hb2 : b ^ 2 = ε - 1 := Real.sq_sqrt (le_of_lt hbarg)
  have hd2 : d ^ 2 = ε ^ 2 - 1 := Real.sq_sqrt (le_of_lt hdarg)
  have hsquare : (a * b) ^ 2 = d ^ 2 := by
    calc
      (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
      _ = (ε + 1) * (ε - 1) := by rw [ha2, hb2]
      _ = d ^ 2 := by rw [hd2]; ring
  have hscale : d = a * b := by
    have habpos : 0 < a * b := mul_pos hapos hbpos
    have hsum : 0 < a * b + d := add_pos habpos hdpos
    have hfactor : (a * b - d) * (a * b + d) = 0 := by
      calc
        (a * b - d) * (a * b + d) = (a * b) ^ 2 - d ^ 2 := by ring
        _ = 0 := by rw [hsquare]; ring
    have hleft :=
      (mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hsum)
    linarith
  have hprod : n u * m u = (ε + 1) - (ε - 1) * u ^ 2 := by
    dsimp [n, m]
    calc
      (a + b * u) * (a - b * u) = a ^ 2 - b ^ 2 * u ^ 2 := by ring
      _ = (ε + 1) - (ε - 1) * u ^ 2 := by rw [ha2, hb2]
  have hn : n u ≠ 0 := by
    intro hn0
    apply hden
    rw [← hprod, hn0, zero_mul]
  have hm : m u ≠ 0 := by
    intro hm0
    apply hden
    rw [← hprod, hm0, mul_zero]
  have hnDer : HasDerivAt n b u := by
    change HasDerivAt (fun v => a + b * v) b u
    convert
      (hasDerivAt_const u a).add ((hasDerivAt_id u).const_mul b)
      using 1 <;> ring
  have hmDer : HasDerivAt m (-b) u := by
    change HasDerivAt (fun v => a - b * v) (-b) u
    convert
      (hasDerivAt_const u a).sub ((hasDerivAt_id u).const_mul b)
      using 1 <;> ring
  have hratio := hnDer.div hmDer hm
  have hlog := (Real.hasDerivAt_log (div_ne_zero hn hm)).comp u hratio
  have hfinal := hlog.const_mul (1 / d)
  have hrat :
      1 + ε + (1 - ε) * u ^ 2 =
        (ε + 1) - (ε - 1) * u ^ 2 := by ring
  change HasDerivAt
    (fun v => 1 / d * Real.log |n v / m v|)
    (2 * (1 / (1 + ε + (1 - ε) * u ^ 2))) u
  convert hfinal using 1
  · funext v
    simp only [Real.log_abs, Function.comp_apply]
    change 1 / d * Real.log (n v / m v) =
      1 / d * Real.log (n v / m v)
    rfl
  · rw [hrat, hscale, ← hprod]
    dsimp [n, m]
    field_simp [hn, hm, ne_of_gt hapos, ne_of_gt hbpos] <;> ring
theorem gap7 (U : Set ℝ) (ε : ℝ) (hε : 1 < ε)
    (hU : RegularSuper U ε) :
    Family U (integrand ε) = Translates U (primitiveSuper ε) := by
  rcases hU with ⟨hUopen, hUconn, hUbranch, hreg⟩
  let d := Real.sqrt (ε ^ 2 - 1)
  let A : ℝ → ℝ := fun y => ε + Real.cos y + d * Real.sin y
  let B : ℝ → ℝ := fun y => 1 + ε * Real.cos y
  have hdarg : 0 < ε ^ 2 - 1 := by nlinarith
  have hdpos : 0 < d := Real.sqrt_pos.2 hdarg
  have hd2 : d ^ 2 = ε ^ 2 - 1 := Real.sq_sqrt (le_of_lt hdarg)
  have hp : ∀ x ∈ U, HasDerivAt (primitiveSuper ε) (integrand ε x) x := by
    intro x hx
    have hA : A x ≠ 0 := by
      simpa [A, d] using (hreg x hx).2
    have hB : B x ≠ 0 := by
      simpa [B] using (hreg x hx).1
    have hADer :
        HasDerivAt A (-Real.sin x + d * Real.cos x) x := by
      dsimp [A]
      simpa using
        ((hasDerivAt_const x ε).add (Real.hasDerivAt_cos x)).add
          ((Real.hasDerivAt_sin x).const_mul d)
    have hBDer : HasDerivAt B (-ε * Real.sin x) x := by
      change HasDerivAt
        (fun y => 1 + ε * Real.cos y) (-ε * Real.sin x) x
      convert
        (hasDerivAt_const x 1).add
          ((Real.hasDerivAt_cos x).const_mul ε)
        using 1 <;> ring
    have hratio := hADer.div hBDer hB
    have hlog := (Real.hasDerivAt_log (div_ne_zero hA hB)).comp x hratio
    have hfinal := hlog.const_mul (1 / d)
    have hunit := Real.sin_sq_add_cos_sq x
    have hunit' : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by
      simpa [add_comm] using hunit
    have hnumid :
        (-Real.sin x + d * Real.cos x) * B x -
            A x * (-ε * Real.sin x) =
          d * A x := by
      have hcalc :
          (-Real.sin x + d * Real.cos x) * B x -
              A x * (-ε * Real.sin x) =
            (ε ^ 2 - 1) * Real.sin x + d * Real.cos x +
              ε * d * (Real.cos x ^ 2 + Real.sin x ^ 2) := by
        dsimp [A, B]
        ring
      rw [hcalc, hunit', ← hd2]
      dsimp [A]
      ring
    change HasDerivAt
      (fun y => 1 / d * Real.log |A y / B y|)
      (1 / B x) x
    convert hfinal using 1
    · funext y
      simp only [Real.log_abs, Function.comp_apply]
      change 1 / d * Real.log (A y / B y) =
        1 / d * Real.log (A y / B y)
      rfl
    · rw [hnumid]
      field_simp [hA, hB, ne_of_gt hdpos] <;> ring
  apply Set.ext
  intro F
  change
    (∀ x ∈ U, HasDerivAt F (integrand ε x) x) ↔
      ∃ C, ∀ x ∈ U, F x = primitiveSuper ε x + C
  constructor
  · intro hF
    by_cases hUne : U.Nonempty
    · rcases hUne with ⟨x₀, hx₀⟩
      have hg : ∀ x ∈ U,
          HasDerivAt (fun y => F y - primitiveSuper ε y) 0 x := by
        intro x hx
        simpa using (hF x hx).sub (hp x hx)
      have hgdiff :
          DifferentiableOn ℝ (fun y => F y - primitiveSuper ε y) U := by
        intro x hx
        exact (hg x hx).differentiableAt.differentiableWithinAt
      have hgzero :
          ∀ x ∈ U, deriv (fun y => F y - primitiveSuper ε y) x = 0 := by
        intro x hx
        exact (hg x hx).deriv
      refine ⟨F x₀ - primitiveSuper ε x₀, ?_⟩
      intro x hx
      have heq :=
        hUopen.is_const_of_deriv_eq_zero hUconn
          hgdiff hgzero hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hUne ⟨x, hx⟩)
  · rintro ⟨C, hC⟩
    intro x hx
    have hbase := (hp x hx).add_const C
    have hev : F =ᶠ[nhds x] (fun y => primitiveSuper ε y + C) := by
      filter_upwards [hUopen.mem_nhds hx] with y hy
      exact hC y hy
    exact hbase.congr_of_eventuallyEq hev

end
end ProofGap.Exercise2028
