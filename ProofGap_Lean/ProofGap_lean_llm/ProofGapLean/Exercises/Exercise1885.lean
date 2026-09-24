import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1885

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (x ^ 4 + x ^ 2 + 1)
def qPlus (x : ℝ) : ℝ := x ^ 2 + x + 1
def qMinus (x : ℝ) : ℝ := x ^ 2 - x + 1
def primitiveSum (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.log (qPlus x / qMinus x) +
    1 / (2 * Real.sqrt 3) *
      (Real.arctan ((2 * x + 1) / Real.sqrt 3) +
        Real.arctan ((2 * x - 1) / Real.sqrt 3))
def primitiveMiddle (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.log (qPlus x / qMinus x) +
    1 / (2 * Real.sqrt 3) *
      Real.arctan (Real.sqrt 3 * x / (1 - x ^ 2))
def primitiveAlt (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt 3) *
      Real.arctan ((x ^ 2 - 1) / (x * Real.sqrt 3)) +
    (1 / 4 : ℝ) * Real.log (qPlus x / qMinus x)
def middleDomain : Set ℝ := {x | x ≠ -1 ∧ x ≠ 1}
def altDomain : Set ℝ := {x | x ≠ 0}
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}
def CoeffIdentity (A B C D : ℝ) : Prop :=
  ∀ x, 1 =
    (A * x + B) * (x ^ 2 - x + 1) +
      (C * x + D) * (x ^ 2 + x + 1)

private theorem qPlus_pos (x : ℝ) : 0 < qPlus x := by
  unfold qPlus
  nlinarith [sq_nonneg (2 * x + 1)]

private theorem qMinus_pos (x : ℝ) : 0 < qMinus x := by
  unfold qMinus
  nlinarith [sq_nonneg (2 * x - 1)]

private theorem hasDerivAt_qPlus (x : ℝ) :
    HasDerivAt qPlus (2 * x + 1) x := by
  unfold qPlus
  convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1 using 1 <;>
    simp <;> ring

private theorem hasDerivAt_qMinus (x : ℝ) :
    HasDerivAt qMinus (2 * x - 1) x := by
  unfold qMinus
  convert (((hasDerivAt_id x).pow 2).sub (hasDerivAt_id x)).add_const 1 using 1 <;>
    simp <;> ring

private theorem hasDerivAt_primitiveSum (x : ℝ) :
    HasDerivAt primitiveSum
      (((1 / 2 : ℝ) * (x + 1)) / qPlus x -
        ((1 / 2 : ℝ) * (x - 1)) / qMinus x) x := by
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hs2 : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have hpa : 1 + ((2 * x + 1) / Real.sqrt 3) ^ 2 ≠ 0 := by positivity
  have hma : 1 + ((2 * x - 1) / Real.sqrt 3) ^ 2 ≠ 0 := by positivity
  have hratio := (hasDerivAt_qPlus x).div (hasDerivAt_qMinus x) hqm
  have hlog := (Real.hasDerivAt_log (div_ne_zero hqp hqm)).comp x hratio
  have hpArg := (((hasDerivAt_id x).const_mul 2).add_const 1).div_const (Real.sqrt 3)
  have hmArg := (((hasDerivAt_id x).const_mul 2).sub_const 1).div_const (Real.sqrt 3)
  have hpAtan := (Real.hasDerivAt_arctan _).comp x hpArg
  have hmAtan := (Real.hasDerivAt_arctan _).comp x hmArg
  have h := (hlog.const_mul (1 / 4 : ℝ)).add
    ((hpAtan.add hmAtan).const_mul (1 / (2 * Real.sqrt 3)))
  convert h using 1
  simp
  field_simp [hs3, hqp, hqm, hpa, hma]
  rw [hs2]
  simp only [qPlus, qMinus]
  ring

private theorem hasDerivAt_primitiveMiddle (x : ℝ)
    (hneg : x ≠ -1) (hpos : x ≠ 1) :
    HasDerivAt primitiveMiddle
      (((1 / 2 : ℝ) * (x + 1)) / qPlus x -
        ((1 / 2 : ℝ) * (x - 1)) / qMinus x) x := by
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hs2 : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have hden : 1 - x ^ 2 ≠ 0 := by
    intro hz
    have hfac : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · apply hpos
      linarith
    · apply hneg
      linarith
  have ha : 1 + (Real.sqrt 3 * x / (1 - x ^ 2)) ^ 2 ≠ 0 := by positivity
  have hratio := (hasDerivAt_qPlus x).div (hasDerivAt_qMinus x) hqm
  have hlog := (Real.hasDerivAt_log (div_ne_zero hqp hqm)).comp x hratio
  have hnum := (hasDerivAt_id x).const_mul (Real.sqrt 3)
  have hdenDeriv := ((hasDerivAt_id x).pow 2).const_sub 1
  have harg := hnum.div hdenDeriv hden
  have hatan := (Real.hasDerivAt_arctan _).comp x harg
  have h := (hlog.const_mul (1 / 4 : ℝ)).add
    (hatan.const_mul (1 / (2 * Real.sqrt 3)))
  convert h using 1
  simp
  field_simp [hs3, hqp, hqm, hden, ha]
  rw [hs2]
  simp only [qPlus, qMinus]
  ring

private theorem hasDerivAt_primitiveAlt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt primitiveAlt
      (((1 / 2 : ℝ) * (x + 1)) / qPlus x -
        ((1 / 2 : ℝ) * (x - 1)) / qMinus x) x := by
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hs2 : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have hxden : x * Real.sqrt 3 ≠ 0 := mul_ne_zero hx hs3
  have ha : 1 + ((x ^ 2 - 1) / (x * Real.sqrt 3)) ^ 2 ≠ 0 := by positivity
  have hratio := (hasDerivAt_qPlus x).div (hasDerivAt_qMinus x) hqm
  have hlog := (Real.hasDerivAt_log (div_ne_zero hqp hqm)).comp x hratio
  have hnum := ((hasDerivAt_id x).pow 2).sub_const 1
  have hden := (hasDerivAt_id x).mul_const (Real.sqrt 3)
  have harg := hnum.div hden hxden
  have hatan := (Real.hasDerivAt_arctan _).comp x harg
  have h := (hatan.const_mul (1 / (2 * Real.sqrt 3))).add
    (hlog.const_mul (1 / 4 : ℝ))
  convert h using 1
  simp
  field_simp [hs3, hqp, hqm, hx, hxden, ha]
  rw [hs2]
  simp only [qPlus, qMinus]
  ring

private theorem family_eq_translates_of_hasDeriv
    (P f : ℝ → ℝ) (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hP : ∀ x ∈ s, HasDerivAt P (f x) x) :
    Family f s = Translates P s := by
  ext F
  change IsAntiderivativeOn F f s ↔ ∃ C, ∀ x ∈ s, F x = P x + C
  constructor
  · intro hF
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x0, hx0⟩
      have hz : ∀ x ∈ s, HasDerivAt (fun y => F y - P y) 0 x := by
        intro x hx
        convert (hF x hx).sub (hP x hx) using 1 <;> ring
      have hdiff : DifferentiableOn ℝ (fun y => F y - P y) s := by
        intro x hx
        exact (hz x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ s, deriv (fun y => F y - P y) x = 0 := by
        intro x hx
        exact (hz x hx).deriv
      refine ⟨F x0 - P x0, ?_⟩
      intro x hx
      have heq : F x - P x = F x0 - P x0 :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv
          (x := x) (y := x0) hx hx0
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => P y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hP x hx).add_const C).congr_of_eventuallyEq heq

theorem gap1 :
    ∃ A B C D : ℝ, CoeffIdentity A B C D := by
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), -(1 / 2 : ℝ), (1 / 2 : ℝ), ?_⟩
  intro x
  ring

theorem gap2 (A B C D x : ℝ) (h : CoeffIdentity A B C D) :
    1 =
      (A * x + B) * (x ^ 2 - x + 1) +
        (C * x + D) * (x ^ 2 + x + 1) := by
  exact h x

theorem gap3 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A + C = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num at h0 h1 hm1 h2
  linarith

theorem gap4 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    -A + B + C + D = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num at h0 h1 hm1 h2
  linarith

theorem gap5 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A - B + C + D = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num at h0 h1 hm1 h2
  linarith

theorem gap6 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    B + D = 1 := by
  have h0 := h 0
  norm_num at h0
  linarith

theorem gap7 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A = 1 / 2 := by
  have h3 := gap3 A B C D h
  have h4 := gap4 A B C D h
  have h6 := gap6 A B C D h
  linarith

theorem gap8 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    B = 1 / 2 := by
  have h3 := gap3 A B C D h
  have h5 := gap5 A B C D h
  have h6 := gap6 A B C D h
  linarith

theorem gap9 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    C = -(1 / 2 : ℝ) := by
  have h3 := gap3 A B C D h
  have h7 := gap7 A B C D h
  linarith

theorem gap10 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    D = 1 / 2 := by
  have h3 := gap3 A B C D h
  have h5 := gap5 A B C D h
  have h6 := gap6 A B C D h
  linarith

theorem gap11 (x : ℝ) :
    integrand x =
      ((1 / 2 : ℝ) * (x + 1)) / qPlus x -
        ((1 / 2 : ℝ) * (x - 1)) / qMinus x := by
  have hp : 1 + x + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x + 1)]
  have hm : 1 - x + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  have hi : 1 + x ^ 2 + x ^ 4 ≠ 0 := by
    nlinarith [sq_nonneg (x ^ 2)]
  unfold integrand qPlus qMinus
  rw [show x ^ 4 + x ^ 2 + 1 = 1 + x ^ 2 + x ^ 4 by ring]
  rw [show x ^ 2 + x + 1 = 1 + x + x ^ 2 by ring]
  rw [show x ^ 2 - x + 1 = 1 - x + x ^ 2 by ring]
  field_simp [hp, hm, hi]
  ring

theorem gap12 :
    Family integrand Set.univ = Translates primitiveSum Set.univ := by
  apply family_eq_translates_of_hasDeriv primitiveSum integrand Set.univ
      isOpen_univ isPreconnected_univ
  intro x hx
  rw [gap11]
  exact hasDerivAt_primitiveSum x

theorem gap13 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ middleDomain) :
    Family integrand s = Translates primitiveMiddle s := by
  apply family_eq_translates_of_hasDeriv primitiveMiddle integrand s hopen hs
  intro x hx
  have hxm := hdom hx
  rw [gap11]
  exact hasDerivAt_primitiveMiddle x hxm.1 hxm.2

theorem gap14 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ altDomain) :
    Family integrand s = Translates primitiveAlt s := by
  apply family_eq_translates_of_hasDeriv primitiveAlt integrand s hopen hs
  intro x hx
  rw [gap11]
  exact hasDerivAt_primitiveAlt x (hdom hx)

theorem gap15 (x : ℝ) (hx : x ∈ altDomain) :
    integrand x =
      (1 / 2 : ℝ) *
          ((1 + 1 / x ^ 2) / (x ^ 2 + 1 + 1 / x ^ 2)) -
        (1 / 2 : ℝ) *
          ((1 - 1 / x ^ 2) / (x ^ 2 + 1 + 1 / x ^ 2)) := by
  have hx0 : x ≠ 0 := hx
  have hi : x ^ 4 + x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg (x ^ 2)]
  unfold integrand
  field_simp [hx0, hi] <;> ring

theorem gap16 (x : ℝ) (hx : x ∈ altDomain) :
    HasDerivAt primitiveAlt (integrand x) x := by
  rw [gap11]
  exact hasDerivAt_primitiveAlt x hx

theorem gap17 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ altDomain) :
    Family integrand s = Translates primitiveAlt s := by
  exact gap14 s hopen hs hdom

end

end ProofGap.Exercise1885
