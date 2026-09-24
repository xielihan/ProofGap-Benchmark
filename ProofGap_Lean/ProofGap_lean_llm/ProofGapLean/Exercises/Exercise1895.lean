import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1895

noncomputable section

def q (x : ℝ) : ℝ := x ^ 4 + 1
def integrand (x : ℝ) : ℝ := 1 / q x ^ 2
def primitive (x : ℝ) : ℝ :=
  x / (4 * q x) +
    3 / (16 * Real.sqrt 2) *
      Real.log ((x ^ 2 + x * Real.sqrt 2 + 1) /
        (x ^ 2 - x * Real.sqrt 2 + 1)) -
    3 / (8 * Real.sqrt 2) *
      Real.arctan (x * Real.sqrt 2 / (x ^ 2 - 1))
def formulaDomain : Set ℝ := {x | x ≠ -1 ∧ x ≠ 1}
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}
def CoeffIdentity (A B C D E F G H : ℝ) : Prop :=
  ∀ x, 1 =
    (3 * A * x ^ 2 + 2 * B * x + C) * q x -
      4 * x ^ 3 * (A * x ^ 3 + B * x ^ 2 + C * x + D) +
      (E * x ^ 3 + F * x ^ 2 + G * x + H) * q x

private theorem coeffIdentity_determined
    (A B C D E F G H : ℝ) (h : CoeffIdentity A B C D E F G H) :
    A = 0 ∧ B = 0 ∧ C = 1 / 4 ∧ D = 0 ∧
      E = 0 ∧ F = 0 ∧ G = 0 ∧ H = 3 / 4 := by
  set_option maxHeartbeats 2000000 in
    have h0 := h (0 : ℝ)
    have h1 := h (1 : ℝ)
    have hm1 := h (-1 : ℝ)
    have h2 := h (2 : ℝ)
    have hm2 := h (-2 : ℝ)
    have h3 := h (3 : ℝ)
    have hm3 := h (-3 : ℝ)
    have h4 := h (4 : ℝ)
    norm_num [q] at h0 h1 hm1 h2 hm2 h3 hm3 h4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem rationalTerm_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => y / (4 * q y))
      ((4 * q x - 16 * x ^ 4) / (4 * q x) ^ 2) x := by
  have hq : HasDerivAt q (4 * x ^ 3) x := by
    simpa [q, id_eq] using
      (((hasDerivAt_id x).pow 4).add
        (hasDerivAt_const (x := x) (c := (1 : ℝ))))
  have hqpos : 0 < q x := by
    unfold q
    positivity
  have hden : HasDerivAt (fun y => 4 * q y) (16 * x ^ 3) x := by
    convert hq.const_mul (4 : ℝ) using 1 <;> ring
  have hdiv := (hasDerivAt_id x).div hden
    (mul_ne_zero (by norm_num) (ne_of_gt hqpos))
  simp only [id_eq] at hdiv
  convert hdiv using 1 <;> ring

private theorem primitive_hasDerivAt (x : ℝ) (hxneg : x ≠ -1) (hxpos : x ≠ 1) :
    HasDerivAt primitive (integrand x) x := by
  set_option maxHeartbeats 2000000 in
    let r : ℝ := Real.sqrt 2
    have hrpos : 0 < r := by
      dsimp [r]
      positivity
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hrsq : r ^ 2 = 2 := by
      dsimp [r]
      exact Real.sq_sqrt (by norm_num)
    have hqpos : 0 < q x := by
      unfold q
      positivity
    have hqne : q x ≠ 0 := ne_of_gt hqpos
    have hapos : 0 < x ^ 2 + x * r + 1 := by
      nlinarith [sq_nonneg (x + r / 2), hrsq]
    have hbpos : 0 < x ^ 2 - x * r + 1 := by
      nlinarith [sq_nonneg (x - r / 2), hrsq]
    have hane : x ^ 2 + x * r + 1 ≠ 0 := ne_of_gt hapos
    have hbne : x ^ 2 - x * r + 1 ≠ 0 := ne_of_gt hbpos
    have hdne : x ^ 2 - 1 ≠ 0 := by
      rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
      apply mul_ne_zero
      · exact sub_ne_zero.mpr hxpos
      · intro hx
        apply hxneg
        linarith
    have hab :
        (x ^ 2 + x * r + 1) * (x ^ 2 - x * r + 1) = q x := by
      unfold q
      calc
        (x ^ 2 + x * r + 1) * (x ^ 2 - x * r + 1) =
            x ^ 4 + (2 - r ^ 2) * x ^ 2 + 1 := by ring
        _ = x ^ 4 + 1 := by rw [hrsq]; ring
    have hc : (x ^ 2 - 1) ^ 2 + (x * r) ^ 2 = q x := by
      unfold q
      calc
        (x ^ 2 - 1) ^ 2 + (x * r) ^ 2 =
            x ^ 4 + (r ^ 2 - 2) * x ^ 2 + 1 := by ring
        _ = x ^ 4 + 1 := by rw [hrsq]; ring
    have ha : HasDerivAt (fun y => y ^ 2 + y * r + 1)
        (2 * x + r) x := by
      convert ((((hasDerivAt_id x).pow 2).add
        ((hasDerivAt_id x).mul_const r)).add_const (1 : ℝ)) using 1 <;>
          simp only [id_eq] <;> ring
    have hb : HasDerivAt (fun y => y ^ 2 - y * r + 1)
        (2 * x - r) x := by
      convert ((((hasDerivAt_id x).pow 2).sub
        ((hasDerivAt_id x).mul_const r)).add_const (1 : ℝ)) using 1 <;>
          simp only [id_eq] <;> ring
    have hratio : HasDerivAt
        (fun y => (y ^ 2 + y * r + 1) / (y ^ 2 - y * r + 1))
        (2 * r * (1 - x ^ 2) / (x ^ 2 - x * r + 1) ^ 2) x := by
      convert ha.div hb hbne using 1 <;> ring
    have hratio_ne :
        (x ^ 2 + x * r + 1) / (x ^ 2 - x * r + 1) ≠ 0 :=
      div_ne_zero hane hbne
    have hlog : HasDerivAt
        (fun y => Real.log ((y ^ 2 + y * r + 1) /
          (y ^ 2 - y * r + 1)))
        (2 * r * (1 - x ^ 2) / q x) x := by
      convert hratio.log hratio_ne using 1
      rw [← hab]
      field_simp [hane, hbne]
    have hnum : HasDerivAt (fun y => y * r) r x := by
      simpa only [id_eq, one_mul] using (hasDerivAt_id x).mul_const r
    have hden : HasDerivAt (fun y => y ^ 2 - 1) (2 * x) x := by
      simpa only [id_eq, Nat.reduceSub, pow_one, mul_one] using
        ((hasDerivAt_id x).pow 2).sub_const (1 : ℝ)
    have hu : HasDerivAt (fun y => y * r / (y ^ 2 - 1))
        (-r * (x ^ 2 + 1) / (x ^ 2 - 1) ^ 2) x := by
      convert hnum.div hden hdne using 1 <;>
        field_simp [hdne] <;> ring
    have hatan : HasDerivAt
        (fun y => Real.arctan (y * r / (y ^ 2 - 1)))
        (-r * (x ^ 2 + 1) / q x) x := by
      convert hu.arctan using 1
      rw [← hc]
      field_simp [hdne]
    have hfirst := rationalTerm_hasDerivAt x
    have htotal :=
      (hfirst.add (hlog.const_mul (3 / (16 * r)))).sub
        (hatan.const_mul (3 / (8 * r)))
    convert htotal using 1 <;> simp only [primitive, r, id_eq]
    unfold integrand q
    field_simp [hqne, hrne]
    ring

theorem gap1 :
    ∃ A B C D E F G H : ℝ, CoeffIdentity A B C D E F G H := by
  refine ⟨0, 0, (1 / 4 : ℝ), 0, 0, 0, 0, (3 / 4 : ℝ), ?_⟩
  intro x
  unfold q
  ring

theorem gap2 (A B C D E F G H x : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    1 =
      (3 * A * x ^ 2 + 2 * B * x + C) * q x -
        4 * x ^ 3 * (A * x ^ 3 + B * x ^ 2 + C * x + D) +
        (E * x ^ 3 + F * x ^ 2 + G * x + H) * q x := by
  exact h x

theorem gap3 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    3 * A + F = 0 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  linarith

theorem gap4 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    2 * B + G = 0 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  linarith

theorem gap5 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    C + H = 1 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  linarith

theorem gap6 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    A = 0 := by
  exact (coeffIdentity_determined A B C D E F G H h).1

theorem gap7 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    B = 0 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  exact hB

theorem gap8 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    C = 1 / 4 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  exact hC

theorem gap9 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    D = 0 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  exact hD

theorem gap10 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    E = 0 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  exact hE

theorem gap11 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    F = 0 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  exact hF

theorem gap12 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    G = 0 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  exact hG

theorem gap13 (A B C D E F G H : ℝ)
    (h : CoeffIdentity A B C D E F G H) :
    H = 3 / 4 := by
  rcases coeffIdentity_determined A B C D E F G H h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩
  exact hH

theorem gap14 (x : ℝ) :
    integrand x =
      deriv (fun y => y / (4 * q y)) x + (3 / 4 : ℝ) / q x := by
  have hd := rationalTerm_hasDerivAt x
  rw [hd.deriv]
  change 1 / (x ^ 4 + 1) ^ 2 =
    (4 * (x ^ 4 + 1) - 16 * x ^ 4) / (4 * (x ^ 4 + 1)) ^ 2 +
      (3 / 4 : ℝ) / (x ^ 4 + 1)
  have hne : x ^ 4 + 1 ≠ 0 := by
    positivity
  field_simp [hne]
  ring

theorem gap15 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ formulaDomain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact ⟨0, by simp⟩
    · let g : ℝ → ℝ := fun x => F x - primitive x
      have hg : ∀ x ∈ s, HasDerivAt g 0 x := by
        intro x hx
        have hdx := hdom hx
        change x ≠ -1 ∧ x ≠ 1 at hdx
        simpa [g] using (hF x hx).sub
          (primitive_hasDerivAt x hdx.1 hdx.2)
      have hdiff : DifferentiableOn ℝ g s := by
        intro x hx
        exact (hg x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ s, deriv g x = 0 := by
        intro x hx
        exact (hg x hx).deriv
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : g x = g x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      dsimp [g] at heq
      linarith
  · intro hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand s
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hdx := hdom hx
    change x ≠ -1 ∧ x ≠ 1 at hdx
    have hp := (primitive_hasDerivAt x hdx.1 hdx.2).add_const C
    apply hp.congr_of_eventuallyEq
    exact Filter.mem_of_superset (hopen.mem_nhds hx)
      (fun y hy => hC y hy)

end

end ProofGap.Exercise1895
