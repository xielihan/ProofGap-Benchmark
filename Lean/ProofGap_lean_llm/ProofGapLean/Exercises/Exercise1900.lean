import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1900

noncomputable section

def p (x : ℝ) : ℝ := x ^ 5 + x + 1
def integrand (x : ℝ) : ℝ := (4 * x ^ 5 - 1) / p x ^ 2
def primitive (x : ℝ) : ℝ := -x / p x
def domain : Set ℝ := {x | p x ≠ 0}
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}
def CoeffIdentity (A B C D E F G H L M : ℝ) : Prop :=
  ∀ x, 4 * x ^ 5 - 1 =
    (4 * A * x ^ 3 + 3 * B * x ^ 2 + 2 * C * x + D) * p x -
      (5 * x ^ 4 + 1) * (A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E) +
      (F * x ^ 4 + G * x ^ 3 + H * x ^ 2 + L * x + M) * p x

private theorem coeffIdentity_unique
    (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = -1 ∧ E = 0 ∧
      F = 0 ∧ G = 0 ∧ H = 0 ∧ L = 0 ∧ M = 0 := by
  set_option maxHeartbeats 2000000 in
    unfold CoeffIdentity at h
    have hm4 := h (-4 : ℝ)
    have hm3 := h (-3 : ℝ)
    have hm2 := h (-2 : ℝ)
    have hm1 := h (-1 : ℝ)
    have h0 := h (0 : ℝ)
    have h1 := h (1 : ℝ)
    have h2 := h (2 : ℝ)
    have h3 := h (3 : ℝ)
    have h4 := h (4 : ℝ)
    have h5 := h (5 : ℝ)
    norm_num [p] at hm4 hm3 hm2 hm1 h0 h1 h2 h3 h4 h5
    have hA : A = 0 := by
      linarith
    have hB : B = 0 := by
      linarith
    have hC : C = 0 := by
      linarith
    have hD : D = -1 := by
      linarith
    have hE : E = 0 := by
      linarith
    have hF : F = 0 := by
      linarith
    have hG : G = 0 := by
      linarith
    have hH : H = 0 := by
      linarith
    have hL : L = 0 := by
      linarith
    have hM : M = 0 := by
      linarith
    exact ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩

private theorem primitive_hasDerivAt (x : ℝ) (hx : p x ≠ 0) :
    HasDerivAt primitive (integrand x) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert hid.mul hid using 1
    · funext y
      simp [pow_two]
    · ring
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert h2.mul hid using 1 <;> ring
  have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    convert h3.mul hid using 1 <;> ring
  have hpow : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by
    convert h4.mul hid using 1 <;> ring
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x 1
  have hp : HasDerivAt p (5 * x ^ 4 + 1) x := by
    convert (hpow.add hid).add hone using 1 <;> simp [p] <;> ring
  have hquot : HasDerivAt primitive
      (((-1 : ℝ) * p x - (-x) * (5 * x ^ 4 + 1)) / p x ^ 2) x := by
    simpa [primitive] using (hasDerivAt_id x).neg.div hp hx
  convert hquot using 1 <;> simp [integrand, p] <;> ring

theorem gap1 :
    ∃ A B C D E F G H L M : ℝ,
      CoeffIdentity A B C D E F G H L M := by
  refine ⟨0, 0, 0, -1, 0, 0, 0, 0, 0, 0, ?_⟩
  intro x
  simp [p]
  ring

theorem gap2 (A B C D E F G H L M x : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) :
    4 * x ^ 5 - 1 =
      (4 * A * x ^ 3 + 3 * B * x ^ 2 + 2 * C * x + D) * p x -
        (5 * x ^ 4 + 1) * (A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E) +
        (F * x ^ 4 + G * x ^ 3 + H * x ^ 2 + L * x + M) * p x := by
  exact h x

theorem gap3 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : A = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hA

theorem gap4 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : B = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hB

theorem gap5 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : C = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hC

theorem gap6 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : D = -1 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hD

theorem gap7 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : E = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hE

theorem gap8 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : F = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hF

theorem gap9 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : G = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hG

theorem gap10 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : H = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hH

theorem gap11 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : L = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hL

theorem gap12 (A B C D E F G H L M : ℝ)
    (h : CoeffIdentity A B C D E F G H L M) : M = 0 := by
  rcases coeffIdentity_unique A B C D E F G H L M h with
    ⟨hA, hB, hC, hD, hE, hF, hG, hH, hL, hM⟩
  exact hM

theorem gap13 (x : ℝ) :
    (0 * x ^ 4 + 0 * x ^ 3 + 0 * x ^ 2 - x + 0) / p x =
      primitive x := by
  simp [primitive]

theorem gap14 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub
        (primitive_hasDerivAt x (hdom hx))
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · intro hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand s
    rcases hF with ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) :=
      Filter.mem_of_superset (hopen.mem_nhds hx) (by
        intro y hy
        exact hC y hy)
    exact ((primitive_hasDerivAt x (hdom hx)).add_const C).congr_of_eventuallyEq heq

end

end ProofGap.Exercise1900
