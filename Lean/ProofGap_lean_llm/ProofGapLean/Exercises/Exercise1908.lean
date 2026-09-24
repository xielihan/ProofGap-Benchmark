import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1908

noncomputable section

def a : ℝ := Real.sqrt 10
def u (x : ℝ) : ℝ := x ^ 5
def domain : Set ℝ := {x | x ^ 10 ≠ 10}
def integrand (x : ℝ) : ℝ := x ^ 4 / (x ^ 10 - 10) ^ 2
def substitutedIntegrand (x : ℝ) : ℝ :=
  (1 / 5 : ℝ) *
    (1 / (((u x - a) * (u x + a)) ^ 2)) * deriv u x
def scaledSquareIntegrand (x : ℝ) : ℝ :=
  (1 / 200 : ℝ) *
    ((u x - a - (u x + a)) ^ 2 /
      (((u x - a) * (u x + a)) ^ 2)) *
    deriv u x
def reciprocalSquareIntegrand (x : ℝ) : ℝ :=
  (1 / 200 : ℝ) *
    (1 / (u x - a) - 1 / (u x + a)) ^ 2 * deriv u x
def decomposedIntegrand (x : ℝ) : ℝ :=
  ((1 / 200 : ℝ) / (u x - a) ^ 2 -
      (1 / 100 : ℝ) / (u x ^ 2 - 10) +
      (1 / 200 : ℝ) / (u x + a) ^ 2) *
    deriv u x
def primitiveRaw (x : ℝ) : ℝ :=
  -1 / (200 * (u x - a)) -
    1 / (200 * a) * Real.log |(u x - a) / (u x + a)| -
    1 / (200 * (u x + a))
def primitive (x : ℝ) : ℝ :=
  -(1 / 100 : ℝ) *
    (u x / (x ^ 10 - 10) +
      1 / (2 * a) * Real.log |(u x - a) / (u x + a)|)
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}

private lemma ex1908_a_pos : 0 < a := by
  unfold a
  positivity

private lemma ex1908_a_sq : a ^ 2 = 10 := by
  unfold a
  rw [Real.sq_sqrt]
  norm_num

private lemma ex1908_u_sq (x : ℝ) : u x ^ 2 = x ^ 10 := by
  unfold u
  ring

private lemma ex1908_factor (x : ℝ) :
    (u x - a) * (u x + a) = x ^ 10 - 10 := by
  calc
    (u x - a) * (u x + a) = u x ^ 2 - a ^ 2 := by ring
    _ = x ^ 10 - 10 := by rw [ex1908_u_sq, ex1908_a_sq]

private lemma ex1908_hasDerivAt_u (x : ℝ) :
    HasDerivAt u (5 * x ^ 4) x := by
  simpa [u] using (hasDerivAt_id x).pow 5

private lemma ex1908_deriv_u (x : ℝ) : deriv u x = 5 * x ^ 4 :=
  (ex1908_hasDerivAt_u x).deriv

private lemma ex1908_factor_ne {x : ℝ} (hx : x ∈ domain) :
    (u x - a) * (u x + a) ≠ 0 := by
  change x ^ 10 ≠ 10 at hx
  rw [ex1908_factor]
  exact sub_ne_zero.mpr hx

private lemma ex1908_minus_ne {x : ℝ} (hx : x ∈ domain) : u x - a ≠ 0 :=
  (mul_ne_zero_iff.mp (ex1908_factor_ne hx)).1

private lemma ex1908_plus_ne {x : ℝ} (hx : x ∈ domain) : u x + a ≠ 0 :=
  (mul_ne_zero_iff.mp (ex1908_factor_ne hx)).2

private lemma ex1908_integrand_eq_substituted (x : ℝ) (hx : x ∈ domain) :
    integrand x = substitutedIntegrand x := by
  change x ^ 10 ≠ 10 at hx
  unfold integrand substitutedIntegrand
  rw [ex1908_deriv_u, ex1908_factor]
  field_simp [sub_ne_zero.mpr hx]

private lemma ex1908_substituted_eq_scaled (x : ℝ) :
    substitutedIntegrand x = scaledSquareIntegrand x := by
  have hn : (u x - a - (u x + a)) ^ 2 = 40 := by
    calc
      (u x - a - (u x + a)) ^ 2 = 4 * a ^ 2 := by ring
      _ = 40 := by rw [ex1908_a_sq]; norm_num
  unfold substitutedIntegrand scaledSquareIntegrand
  rw [ex1908_factor, hn]
  ring

private lemma ex1908_integrand_eq_scaled (x : ℝ) (hx : x ∈ domain) :
    integrand x = scaledSquareIntegrand x := by
  rw [ex1908_integrand_eq_substituted x hx, ex1908_substituted_eq_scaled x]

private lemma ex1908_integrand_eq_reciprocal (x : ℝ) (hx : x ∈ domain) :
    integrand x = reciprocalSquareIntegrand x := by
  rw [ex1908_integrand_eq_scaled x hx]
  have hm : u x - a ≠ 0 := ex1908_minus_ne hx
  have hp : u x + a ≠ 0 := ex1908_plus_ne hx
  unfold scaledSquareIntegrand reciprocalSquareIntegrand
  field_simp [hm, hp]
  ring

private lemma ex1908_integrand_eq_decomposed (x : ℝ) (hx : x ∈ domain) :
    integrand x = decomposedIntegrand x := by
  rw [ex1908_integrand_eq_reciprocal x hx]
  have hm : u x - a ≠ 0 := ex1908_minus_ne hx
  have hp : u x + a ≠ 0 := ex1908_plus_ne hx
  have hmid : u x ^ 2 - 10 = (u x - a) * (u x + a) := by
    calc
      u x ^ 2 - 10 = u x ^ 2 - a ^ 2 := by rw [ex1908_a_sq]
      _ = (u x - a) * (u x + a) := by ring
  unfold reciprocalSquareIntegrand decomposedIntegrand
  rw [hmid]
  field_simp [hm, hp]
  ring

private lemma ex1908_hasDerivAt_primitiveRaw (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitiveRaw (integrand x) x := by
  let d : ℝ := 5 * x ^ 4
  have hu : HasDerivAt u d x := by
    simpa [d] using ex1908_hasDerivAt_u x
  have hm : u x - a ≠ 0 := ex1908_minus_ne hx
  have hp : u x + a ≠ 0 := ex1908_plus_ne hx
  have ha : a ≠ 0 := ne_of_gt ex1908_a_pos
  have hminus : HasDerivAt (fun y => u y - a) d x := hu.sub_const a
  have hplus : HasDerivAt (fun y => u y + a) d x := hu.add_const a
  have hleft :=
    ((hasDerivAt_const x (200 : ℝ)).mul hminus).inv
      (mul_ne_zero (by norm_num) hm)
  have hright :=
    ((hasDerivAt_const x (200 : ℝ)).mul hplus).inv
      (mul_ne_zero (by norm_num) hp)
  have hratio := hminus.div hplus hp
  have hratio_ne : (u x - a) / (u x + a) ≠ 0 := div_ne_zero hm hp
  have hlog := (Real.hasDerivAt_log hratio_ne).comp x hratio
  change HasDerivAt
    (fun y => Real.log ((u y - a) / (u y + a))) _ x at hlog
  have hlogfun :
      (fun y => Real.log ((u y - a) / (u y + a))) =
        (fun y => Real.log |(u y - a) / (u y + a)|) := by
    funext y
    rw [Real.log_abs]
  rw [hlogfun] at hlog
  have hlogterm :=
    (hasDerivAt_const x (1 / (200 * a) : ℝ)).mul hlog
  have htotal := (hleft.neg.sub hlogterm).sub hright
  have hdec : HasDerivAt primitiveRaw (decomposedIntegrand x) x := by
    convert htotal using 1
    · funext y
      simp [primitiveRaw, div_eq_mul_inv]
    · have hmid : u x ^ 2 - 10 = (u x - a) * (u x + a) := by
        calc
          u x ^ 2 - 10 = u x ^ 2 - a ^ 2 := by rw [ex1908_a_sq]
          _ = (u x - a) * (u x + a) := by ring
      unfold decomposedIntegrand
      rw [ex1908_deriv_u, hmid]
      dsimp [d]
      field_simp [hm, hp, ha]
      ring
  simpa [ex1908_integrand_eq_decomposed x hx] using hdec

private lemma ex1908_eq_of_hasDerivAt_zero
    {f : ℝ → ℝ} {s : Set ℝ} (hopen : IsOpen s) (hs : IsPreconnected s)
    (h : ∀ x ∈ s, HasDerivAt f 0 x) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  have hdiff : DifferentiableOn ℝ f s := by
    intro z hz
    exact (h z hz).differentiableAt.differentiableWithinAt
  have hderiv : ∀ z ∈ s, deriv f z = 0 := by
    intro z hz
    exact (h z hz).deriv
  exact hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hy

private lemma ex1908_primitive_eq (x : ℝ) (hx : x ∈ domain) :
    primitiveRaw x = primitive x := by
  have hm : u x - a ≠ 0 := ex1908_minus_ne hx
  have hp : u x + a ≠ 0 := ex1908_plus_ne hx
  have ha : a ≠ 0 := ne_of_gt ex1908_a_pos
  unfold primitiveRaw primitive
  rw [← ex1908_factor]
  field_simp [hm, hp, ha]
  ring

theorem gap1 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family substitutedIntegrand s := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa [ex1908_integrand_eq_substituted x (hdom hx)] using hF x hx
  · intro hF x hx
    simpa [ex1908_integrand_eq_substituted x (hdom hx)] using hF x hx

theorem gap2 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family substitutedIntegrand s = Family scaledSquareIntegrand s := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa [ex1908_substituted_eq_scaled x] using hF x hx
  · intro hF x hx
    simpa [ex1908_substituted_eq_scaled x] using hF x hx

theorem gap3 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family scaledSquareIntegrand s := by
  calc
    Family integrand s = Family substitutedIntegrand s := gap1 s hdom
    _ = Family scaledSquareIntegrand s := gap2 s hdom

theorem gap4 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family reciprocalSquareIntegrand s := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa [ex1908_integrand_eq_reciprocal x (hdom hx)] using hF x hx
  · intro hF x hx
    simpa [ex1908_integrand_eq_reciprocal x (hdom hx)] using hF x hx

theorem gap5 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family decomposedIntegrand s := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa [ex1908_integrand_eq_decomposed x (hdom hx)] using hF x hx
  · intro hF x hx
    simpa [ex1908_integrand_eq_decomposed x (hdom hx)] using hF x hx

theorem gap6 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitiveRaw s := by
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitiveRaw x₀, ?_⟩
      intro x hx
      have hz : ∀ y ∈ s,
          HasDerivAt (fun z => F z - primitiveRaw z) 0 y := by
        intro y hy
        convert (hF y hy).sub
            (ex1908_hasDerivAt_primitiveRaw y (hdom hy)) using 1 <;> ring
      have hc := ex1908_eq_of_hasDerivAt_zero hopen hs hz hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩ x hx
    have hp : HasDerivAt (fun y => primitiveRaw y + C) (integrand x) x :=
      (ex1908_hasDerivAt_primitiveRaw x (hdom hx)).add_const C
    have hwithin : HasDerivWithinAt F (integrand x) s x :=
      hp.hasDerivWithinAt.congr
        (fun y hy => hC y hy) (hC x hx)
    exact hwithin.hasDerivAt (hopen.mem_nhds hx)

theorem gap7 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  calc
    Family integrand s = Translates primitiveRaw s := gap6 s hopen hs hdom
    _ = Translates primitive s := by
      apply Set.ext
      intro F
      simp only [Translates, Set.mem_setOf_eq]
      constructor
      · rintro ⟨C, hC⟩
        refine ⟨C, ?_⟩
        intro x hx
        rw [← ex1908_primitive_eq x (hdom hx)]
        exact hC x hx
      · rintro ⟨C, hC⟩
        refine ⟨C, ?_⟩
        intro x hx
        rw [ex1908_primitive_eq x (hdom hx)]
        exact hC x hx

end

end ProofGap.Exercise1908
