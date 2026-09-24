import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1580

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def outline (a α b : ℝ) : ℝ := 4 * a + 2 * b * (1 - Real.cos α)
def sectionArea (a α b : ℝ) : ℝ :=
  (2 * a - b * Real.cos α) * b * Real.sin α
def equivalentRadius (a α b : ℝ) : ℝ :=
  Real.sqrt (sectionArea a α b / Real.pi)
def circleLength (a α b : ℝ) : ℝ :=
  2 * Real.sqrt (Real.pi * sectionArea a α b)
def K (a α b : ℝ) : ℝ :=
  (2 * a + b * (1 - Real.cos α)) /
    Real.sqrt (Real.pi * sectionArea a α b)
def optimizer (a α : ℝ) : ℝ := a * sec (α / 2) ^ 2

def Admissible (a α b : ℝ) : Prop :=
  0 < b ∧ 0 < sectionArea a α b

def IsMinimizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x₀ ≤ u x

private theorem hasDerivAt_K_of_admissible
    (a α b : ℝ) (hadm : Admissible a α b) :
    HasDerivAt (K a α)
      (((1 - Real.cos α) * Real.sqrt (Real.pi * sectionArea a α b) -
          (2 * a + b * (1 - Real.cos α)) *
            ((1 / (2 * Real.sqrt (Real.pi * sectionArea a α b))) *
              (Real.pi *
                (((-Real.cos α) * b + (2 * a - b * Real.cos α)) *
                  Real.sin α)))) /
        Real.sqrt (Real.pi * sectionArea a α b) ^ 2) b := by
  have hR : 0 < Real.pi * sectionArea a α b :=
    mul_pos Real.pi_pos hadm.2
  have hlinear :
      HasDerivAt (fun x : ℝ => 2 * a - x * Real.cos α)
        (-Real.cos α) b := by
    convert (hasDerivAt_const b (2 * a)).sub
      ((hasDerivAt_id b).mul_const (Real.cos α)) using 1 <;> ring
  have hsec :
      HasDerivAt (sectionArea a α)
        (((-Real.cos α) * b + (2 * a - b * Real.cos α)) * Real.sin α) b := by
    unfold sectionArea
    convert ((hlinear.mul (hasDerivAt_id b)).mul_const
      (Real.sin α)) using 1 <;> simp <;> ring
  have hrad :
      HasDerivAt (fun x : ℝ => Real.pi * sectionArea a α x)
        (Real.pi *
          (((-Real.cos α) * b + (2 * a - b * Real.cos α)) *
            Real.sin α)) b := by
    convert hsec.const_mul Real.pi using 1 <;> ring
  have hsqrt :
      HasDerivAt
        (fun x : ℝ => Real.sqrt (Real.pi * sectionArea a α x))
        ((1 / (2 * Real.sqrt (Real.pi * sectionArea a α b))) *
          (Real.pi *
            (((-Real.cos α) * b + (2 * a - b * Real.cos α)) *
              Real.sin α))) b := by
    exact (Real.hasDerivAt_sqrt (ne_of_gt hR)).comp b hrad
  have hnum :
      HasDerivAt (fun x : ℝ => 2 * a + x * (1 - Real.cos α))
        (1 - Real.cos α) b := by
    convert (hasDerivAt_const b (2 * a)).add
      ((hasDerivAt_id b).mul_const (1 - Real.cos α)) using 1 <;> ring
  unfold K
  exact hnum.div hsqrt (ne_of_gt (Real.sqrt_pos.2 hR))

private theorem optimizer_facts
    (a α : ℝ) (ha : 0 < a) (hα : α ∈ Set.Ioo 0 Real.pi) :
    0 < 1 + Real.cos α ∧
      0 < optimizer a α ∧
      (1 + Real.cos α) * optimizer a α = 2 * a := by
  have hhalf : α / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.pi_pos, hα.1]
    · nlinarith [hα.2]
  have hc : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo hhalf
  have htrig :
      1 + Real.cos α = 2 * Real.cos (α / 2) ^ 2 := by
    rw [show α = 2 * (α / 2) by ring, Real.cos_two_mul]
    ring
  have hd : 0 < 1 + Real.cos α := by
    nlinarith [sq_pos_of_pos hc]
  refine ⟨hd, ?_, ?_⟩
  · unfold optimizer sec
    positivity
  · unfold optimizer sec
    field_simp [ne_of_gt hc]
    nlinarith [htrig]

private theorem optimizer_isMinimizer
    (a α : ℝ) (ha : 0 < a) (hα : α ∈ Set.Ioo 0 Real.pi) :
    IsMinimizerOn (K a α) {t | Admissible a α t} (optimizer a α) := by
  obtain ⟨hd, ho, hrel⟩ := optimizer_facts a α ha hα
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hfacO :
      2 * a - optimizer a α * Real.cos α = optimizer a α := by
    nlinarith [hrel]
  have hAo :
      sectionArea a α (optimizer a α) =
        optimizer a α ^ 2 * Real.sin α := by
    unfold sectionArea
    rw [hfacO]
    ring
  have hNo :
      2 * a + optimizer a α * (1 - Real.cos α) =
        2 * optimizer a α := by
    nlinarith [hfacO]
  have hAdmO : Admissible a α (optimizer a α) := by
    constructor
    · exact ho
    · rw [hAo]
      positivity
  refine ⟨hAdmO, ?_⟩
  intro b hb
  have harea :
      0 < ((2 * a - b * Real.cos α) * b) * Real.sin α := by
    simpa [sectionArea] using hb.2
  have hqb : 0 < (2 * a - b * Real.cos α) * b := by
    rcases (mul_pos_iff.mp harea) with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge hsin.le) hneg.2)
  have hfacB : 0 < 2 * a - b * Real.cos α := by
    rcases (mul_pos_iff.mp hqb) with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge hb.1.le) hneg.2)
  have hNb : 0 < 2 * a + b * (1 - Real.cos α) := by
    nlinarith [hfacB, hb.1]
  have hRb : 0 < Real.pi * sectionArea a α b :=
    mul_pos Real.pi_pos hb.2
  have hRo : 0 < Real.pi * sectionArea a α (optimizer a α) :=
    mul_pos Real.pi_pos hAdmO.2
  have hsRb : 0 < Real.sqrt (Real.pi * sectionArea a α b) :=
    Real.sqrt_pos.2 hRb
  have hsRo :
      0 < Real.sqrt (Real.pi * sectionArea a α (optimizer a α)) :=
    Real.sqrt_pos.2 hRo
  have hid :
      (2 * a + b * (1 - Real.cos α)) ^ 2 -
          4 * ((2 * a - b * Real.cos α) * b) =
        (2 * a - (1 + Real.cos α) * b) ^ 2 := by
    ring
  have halg :
      (2 * a + b * (1 - Real.cos α)) ^ 2 *
          (Real.pi * sectionArea a α (optimizer a α)) -
        (2 * a + optimizer a α * (1 - Real.cos α)) ^ 2 *
          (Real.pi * sectionArea a α b) =
        Real.pi * Real.sin α * optimizer a α ^ 2 *
          (2 * a - (1 + Real.cos α) * b) ^ 2 := by
    rw [hAo, hNo]
    unfold sectionArea
    calc
      _ = Real.pi * Real.sin α * optimizer a α ^ 2 *
          ((2 * a + b * (1 - Real.cos α)) ^ 2 -
            4 * ((2 * a - b * Real.cos α) * b)) := by ring
      _ = _ := by rw [hid]
  have hnonneg :
      0 ≤ Real.pi * Real.sin α * optimizer a α ^ 2 *
        (2 * a - (1 + Real.cos α) * b) ^ 2 := by
    positivity
  have hsquare :
      ((2 * a + optimizer a α * (1 - Real.cos α)) *
          Real.sqrt (Real.pi * sectionArea a α b)) ^ 2 ≤
        ((2 * a + b * (1 - Real.cos α)) *
          Real.sqrt (Real.pi * sectionArea a α (optimizer a α))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hRb.le, Real.sq_sqrt hRo.le]
    nlinarith [halg]
  have hNoPos :
      0 < 2 * a + optimizer a α * (1 - Real.cos α) := by
    rw [hNo]
    positivity
  have hleft_nonneg :
      0 ≤ (2 * a + optimizer a α * (1 - Real.cos α)) *
        Real.sqrt (Real.pi * sectionArea a α b) :=
    mul_nonneg hNoPos.le hsRb.le
  have hright_nonneg :
      0 ≤ (2 * a + b * (1 - Real.cos α)) *
        Real.sqrt (Real.pi * sectionArea a α (optimizer a α)) :=
    mul_nonneg hNb.le hsRo.le
  have hcross :
      (2 * a + optimizer a α * (1 - Real.cos α)) *
          Real.sqrt (Real.pi * sectionArea a α b) ≤
        (2 * a + b * (1 - Real.cos α)) *
          Real.sqrt (Real.pi * sectionArea a α (optimizer a α)) := by
    nlinarith [hsquare]
  unfold K
  exact (div_le_div_iff₀ hsRo hsRb).2 hcross

theorem gap1 (a α b : ℝ) :
    outline a α b = 4 * a + 2 * b * (1 - Real.cos α) := by
  rfl

theorem gap2 (a α b : ℝ) :
    sectionArea a α b = (2 * a - b * Real.cos α) * b * Real.sin α := by
  rfl

theorem gap3 (a α b : ℝ) (hA : 0 ≤ sectionArea a α b) :
    equivalentRadius a α b =
      1 / Real.sqrt Real.pi * Real.sqrt (sectionArea a α b) := by
  unfold equivalentRadius
  rw [Real.sqrt_div hA]
  ring

theorem gap4 (a α b : ℝ) :
    2 * Real.pi * equivalentRadius a α b =
      2 * Real.pi * Real.sqrt (sectionArea a α b / Real.pi) := by
  rfl

theorem gap5 (a α b : ℝ) (hA : 0 ≤ sectionArea a α b) :
    2 * Real.pi * equivalentRadius a α b = circleLength a α b := by
  rw [gap3 a α b hA]
  unfold circleLength
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hp2 : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hdiv : Real.pi / Real.sqrt Real.pi = Real.sqrt Real.pi := by
    apply (div_eq_iff (ne_of_gt hp)).2
    simpa [pow_two] using hp2.symm
  have hmul :
      Real.sqrt (Real.pi * sectionArea a α b) =
        Real.sqrt Real.pi * Real.sqrt (sectionArea a α b) := by
    rw [Real.sqrt_mul Real.pi_pos.le]
  rw [hmul]
  calc
    2 * Real.pi *
        (1 / Real.sqrt Real.pi * Real.sqrt (sectionArea a α b)) =
        2 * (Real.pi / Real.sqrt Real.pi) *
          Real.sqrt (sectionArea a α b) := by ring
    _ = 2 * Real.sqrt Real.pi * Real.sqrt (sectionArea a α b) := by
      rw [hdiv]
    _ = 2 * (Real.sqrt Real.pi * Real.sqrt (sectionArea a α b)) := by
      ring

theorem gap6 (a α b : ℝ) :
    circleLength a α b =
      2 * Real.sqrt (Real.pi * sectionArea a α b) := by
  rfl

theorem gap7 (a α b : ℝ) :
    K a α b =
      (2 * a + b * (1 - Real.cos α)) /
        Real.sqrt (Real.pi * (2 * a - b * Real.cos α) * b * Real.sin α) := by
  unfold K sectionArea
  congr 2
  ring

theorem gap8 (a α b : ℝ) (ha : 0 < a) (hα : α ∈ Set.Ioo 0 Real.pi)
    (hmin : IsMinimizerOn (K a α) {t | Admissible a α t} b) :
    deriv (K a α) b = 0 := by
  have hcont : Continuous (sectionArea a α) := by
    unfold sectionArea
    fun_prop
  have hopen : IsOpen {t : ℝ | Admissible a α t} := by
    rw [show {t : ℝ | Admissible a α t} =
        Set.Ioi 0 ∩ (sectionArea a α) ⁻¹' Set.Ioi 0 by
      ext x
      simp [Admissible]]
    exact isOpen_Ioi.inter (isOpen_Ioi.preimage hcont)
  have hlocal : IsLocalMin (K a α) b := by
    filter_upwards [hopen.mem_nhds hmin.1] with x hx
    exact hmin.2 x hx
  have hextr : IsLocalExtr (K a α) b := Or.inl hlocal
  exact hextr.deriv_eq_zero

theorem gap9 (a α b : ℝ) (ha : 0 < a) (hα : α ∈ Set.Ioo 0 Real.pi)
    (hadm : Admissible a α b) (hcrit : deriv (K a α) b = 0) :
    b = optimizer a α := by
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hR : 0 < Real.pi * sectionArea a α b :=
    mul_pos Real.pi_pos hadm.2
  have hsqrt : 0 < Real.sqrt (Real.pi * sectionArea a α b) :=
    Real.sqrt_pos.2 hR
  have hd := (hasDerivAt_K_of_admissible a α b hadm).deriv
  have hquot :
      ((1 - Real.cos α) * Real.sqrt (Real.pi * sectionArea a α b) -
          (2 * a + b * (1 - Real.cos α)) *
            ((1 / (2 * Real.sqrt (Real.pi * sectionArea a α b))) *
              (Real.pi *
                (((-Real.cos α) * b + (2 * a - b * Real.cos α)) *
                  Real.sin α)))) /
        Real.sqrt (Real.pi * sectionArea a α b) ^ 2 = 0 :=
    hd.symm.trans hcrit
  have hden : Real.sqrt (Real.pi * sectionArea a α b) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt hsqrt)
  have hnum :
      (1 - Real.cos α) * Real.sqrt (Real.pi * sectionArea a α b) -
          (2 * a + b * (1 - Real.cos α)) *
            ((1 / (2 * Real.sqrt (Real.pi * sectionArea a α b))) *
              (Real.pi *
                (((-Real.cos α) * b + (2 * a - b * Real.cos α)) *
                  Real.sin α))) = 0 := by
    rcases (div_eq_zero_iff.mp hquot) with hn | hz
    · exact hn
    · exact False.elim (hden hz)
  have hsq :
      Real.sqrt (Real.pi * sectionArea a α b) ^ 2 =
        Real.pi * sectionArea a α b :=
    Real.sq_sqrt hR.le
  have hcleared :
      2 * (1 - Real.cos α) * (Real.pi * sectionArea a α b) -
          (2 * a + b * (1 - Real.cos α)) * Real.pi *
            (((-Real.cos α) * b + (2 * a - b * Real.cos α)) *
              Real.sin α) = 0 := by
    calc
      _ = 2 * Real.sqrt (Real.pi * sectionArea a α b) *
          ((1 - Real.cos α) * Real.sqrt (Real.pi * sectionArea a α b) -
            (2 * a + b * (1 - Real.cos α)) *
              ((1 / (2 * Real.sqrt (Real.pi * sectionArea a α b))) *
                (Real.pi *
                  (((-Real.cos α) * b + (2 * a - b * Real.cos α)) *
                    Real.sin α)))) := by
              field_simp [ne_of_gt hsqrt]
              rw [hsq]
              ring
      _ = 0 := by rw [hnum]; ring
  have hfactor :
      2 * a * Real.pi * Real.sin α *
          ((1 + Real.cos α) * b - 2 * a) = 0 := by
    calc
      _ = 2 * (1 - Real.cos α) * (Real.pi * sectionArea a α b) -
          (2 * a + b * (1 - Real.cos α)) * Real.pi *
            (((-Real.cos α) * b + (2 * a - b * Real.cos α)) *
              Real.sin α) := by
            unfold sectionArea
            ring
      _ = 0 := hcleared
  have hcoef : 2 * a * Real.pi * Real.sin α ≠ 0 := by
    positivity
  have hfaczero : (1 + Real.cos α) * b - 2 * a = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hcoef
  have hbrel : (1 + Real.cos α) * b = 2 * a := by
    linarith
  obtain ⟨hdpos, _, horel⟩ := optimizer_facts a α ha hα
  nlinarith [hbrel, horel]

theorem gap10 (a α : ℝ) :
    (optimizer a α, optimizer a α).1 =
      (optimizer a α, optimizer a α).2 := by
  rfl

theorem gap11 (a α : ℝ) :
    (optimizer a α, optimizer a α).2 = a * sec (α / 2) ^ 2 := by
  rfl

theorem gap12 (a α : ℝ) :
    (optimizer a α, optimizer a α).1 = a * sec (α / 2) ^ 2 := by
  rfl

theorem gap13 (a α : ℝ) (ha : 0 < a) (hα : α ∈ Set.Ioo 0 Real.pi) :
    IsMinimizerOn (K a α) {t | Admissible a α t} (optimizer a α) := by
  exact optimizer_isMinimizer a α ha hα

theorem gap14 (a α : ℝ) (ha : 0 < a) (hα : α ∈ Set.Ioo 0 Real.pi) :
    Admissible a α (optimizer a α) ∧
      ∀ b, Admissible a α b →
        K a α (optimizer a α) ≤ K a α b := by
  exact gap13 a α ha hα

end

end ProofGap.Exercise1580
