import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2146

noncomputable section

def xBranch : Set ℝ := Set.Ioo (-Real.pi) Real.pi
def t (x : ℝ) := Real.tan (x / 2)
def tIntegrand (u : ℝ) := (1 + u ^ 2) / (1 + u + u ^ 2) ^ 2
def rewrittenTIntegrand (u : ℝ) :=
  (1 + u + u ^ 2 - 1 / 2 * (2 * u + 1) + 1 / 2) /
    (1 + u + u ^ 2) ^ 2
def AntiderivativesX (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ xBranch, HasDerivAt F (f x) x}
def AntiderivativesT (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u, HasDerivAt F (f u) u}
def PrimitiveFamilyX (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ xBranch, F x = p x + C}
def PullbackFamily (A : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ A, ∀ x ∈ xBranch, F x = G (t x)}
def HalfParameterFamily (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {G | ∃ H ∈ AntiderivativesT f, ∀ u, G u = 1 / 2 * H u}
def DecompositionParameterFamily : Set (ℝ → ℝ) :=
  {G | ∃ A ∈ AntiderivativesT (fun u => 1 / (1 + u + u ^ 2)),
    ∃ B ∈ AntiderivativesT
      (fun u => (2 * u + 1) / (1 + u + u ^ 2) ^ 2),
    ∃ D ∈ AntiderivativesT (fun u => 1 / (1 + u + u ^ 2) ^ 2),
    ∀ u, G u = 1 / 2 * A u - 1 / 4 * B u + 1 / 4 * D u}
def integrand (x : ℝ) := 1 / (2 + Real.sin x) ^ 2
def primitiveT (u : ℝ) :=
  4 / (3 * Real.sqrt 3) *
      Real.arctan ((2 * u + 1) / Real.sqrt 3) +
    (u + 2) / (6 * (1 + u + u ^ 2))
def primitive (x : ℝ) :=
  4 / (3 * Real.sqrt 3) *
      Real.arctan ((1 + 2 * Real.tan (x / 2)) / Real.sqrt 3) +
    Real.cos x / (3 * (2 + Real.sin x))

private theorem sqrt_three_ne : Real.sqrt 3 ≠ 0 := by
  positivity

private theorem sqrt_three_sq_aux : Real.sqrt 3 ^ 2 = (3 : ℝ) := by
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private theorem quadratic_pos (u : ℝ) : 0 < 1 + u + u ^ 2 := by
  nlinarith [sq_nonneg (u + 1 / 2)]

private theorem hasDerivAt_quadratic (u : ℝ) :
    HasDerivAt (fun v : ℝ => 1 + v + v ^ 2) (1 + 2 * u) u := by
  convert ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).add
      ((hasDerivAt_id u).pow 2) using 1 <;> simp <;> ring

private theorem half_cos_ne (x : ℝ) (hx : x ∈ xBranch) :
    Real.cos (x / 2) ≠ 0 := by
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have := hx.1
    linarith
  · have := hx.2
    linarith

private theorem one_add_sin_mul_cos_ne (y : ℝ) :
    1 + Real.sin y * Real.cos y ≠ 0 := by
  have htrig := Real.sin_sq_add_cos_sq y
  have hsquare := sq_nonneg (Real.sin y + Real.cos y)
  nlinarith

private theorem sin_eq_two_t_div (x : ℝ) (hx : x ∈ xBranch) :
    Real.sin x = 2 * t x / (1 + t x ^ 2) := by
  have hc := half_cos_ne x hx
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  have hmul := congrArg
    (fun z : ℝ => Real.sin (x / 2) * z) hs
  unfold t
  rw [Real.tan_eq_sin_div_cos]
  conv_lhs =>
    rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]
  field_simp [hc]
  ring_nf at hmul ⊢
  exact hmul

private theorem hasDerivAt_t (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt t ((1 + t x ^ 2) / 2) x := by
  have hc := half_cos_ne x hx
  have hi : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    convert (hasDerivAt_id x).div_const 2 using 1 <;> ring
  have ht := (Real.hasDerivAt_tan hc).comp x hi
  convert ht using 1
  · unfold t
    rw [Real.tan_eq_sin_div_cos]
    have hs := Real.sin_sq_add_cos_sq (x / 2)
    field_simp [hc] <;> nlinarith [hs]

private theorem hasDerivAt_primitiveT (u : ℝ) :
    HasDerivAt primitiveT (tIntegrand u / 2) u := by
  have hs := sqrt_three_ne
  have hqpos := quadratic_pos u
  have hqne : 1 + u + u ^ 2 ≠ 0 := ne_of_gt hqpos
  have hz : HasDerivAt
      (fun v : ℝ => (2 * v + 1) / Real.sqrt 3)
      (2 / Real.sqrt 3) u := by
    convert (((hasDerivAt_id u).const_mul 2).add_const 1).div_const
      (Real.sqrt 3) using 1 <;> ring
  have hat := (Real.hasDerivAt_arctan
      ((2 * u + 1) / Real.sqrt 3)).comp u hz
  have hfirst := hat.const_mul (4 / (3 * Real.sqrt 3))
  have hq := hasDerivAt_quadratic u
  have hnum : HasDerivAt (fun v : ℝ => v + 2) 1 u := by
    convert (hasDerivAt_id u).add_const 2 using 1 <;> ring
  have hden := hq.const_mul 6
  have hrat := hnum.div hden (mul_ne_zero (by norm_num) hqne)
  have hsum := hfirst.add hrat
  convert hsum using 1
  · unfold tIntegrand
    field_simp [hs, hqne] <;>
      simp only [sqrt_three_sq_aux] <;> ring

private theorem hasDerivAt_composed_primitive (x : ℝ)
    (hx : x ∈ xBranch) :
    HasDerivAt (fun y => primitiveT (t y)) (integrand x) x := by
  have hcomp := (hasDerivAt_primitiveT (t x)).comp x (hasDerivAt_t x hx)
  have hs := sin_eq_two_t_div x hx
  have hsq : 1 + t x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (t x)]
  have hq : 1 + t x + t x ^ 2 ≠ 0 :=
    ne_of_gt (quadratic_pos (t x))
  have htwo : 2 + Real.sin x =
      2 * (1 + t x + t x ^ 2) / (1 + t x ^ 2) := by
    rw [hs]
    field_simp [hsq]
    ring
  convert hcomp using 1
  · unfold integrand tIntegrand
    rw [htwo]
    field_simp [hsq, hq] <;> ring

private theorem same_deriv_global {f p F : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hp : ∀ x, HasDerivAt p (f x) x) :
    ∃ C : ℝ, ∀ x, F x = p x + C := by
  let d : ℝ → ℝ := fun x => F x - p x
  have hd : ∀ x, HasDerivAt d 0 x := by
    intro x
    simpa [d] using (hF x).sub (hp x)
  have hdiff : Differentiable ℝ d := fun x => (hd x).differentiableAt
  have hzero : ∀ x, deriv d x = 0 := fun x => (hd x).deriv
  refine ⟨d 0, ?_⟩
  intro x
  have he : d x = d 0 :=
    is_const_of_deriv_eq_zero hdiff hzero x 0
  dsimp [d] at he ⊢
  linarith

private theorem same_deriv_on_branch {f p F : ℝ → ℝ}
    (hF : ∀ x ∈ xBranch, HasDerivAt F (f x) x)
    (hp : ∀ x ∈ xBranch, HasDerivAt p (f x) x) :
    ∃ C : ℝ, ∀ x ∈ xBranch, F x = p x + C := by
  let d : ℝ → ℝ := fun x => F x - p x
  have hd : ∀ x ∈ xBranch, HasDerivAt d 0 x := by
    intro x hx
    simpa [d] using (hF x hx).sub (hp x hx)
  have hdiff : DifferentiableOn ℝ d (Set.Ioo (-Real.pi) Real.pi) := by
    intro x hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ Set.Ioo (-Real.pi) Real.pi, deriv d x = 0 := by
    intro x hx
    exact (hd x hx).deriv
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  refine ⟨d 0, ?_⟩
  intro x hx
  have he : d x = d 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hzero hx hzero_mem
  dsimp [d] at he ⊢
  linarith

private theorem hasDerivAt_of_eqOn_branch {F G : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ xBranch) (hG : HasDerivAt G d x)
    (hEq : ∀ y ∈ xBranch, F y = G y) :
    HasDerivAt F d x := by
  have heq : F =ᶠ[nhds x] G := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hEq y hy
  exact hG.congr_of_eventuallyEq heq

private theorem antiderivativesX_eq_primitiveFamily
    {f p : ℝ → ℝ}
    (hp : ∀ x ∈ xBranch, HasDerivAt p (f x) x) :
    AntiderivativesX f = PrimitiveFamilyX p := by
  ext F
  constructor
  · intro hF
    exact same_deriv_on_branch hF hp
  · rintro ⟨C, hF⟩
    intro x hx
    apply hasDerivAt_of_eqOn_branch hx ((hp x hx).add_const C)
    intro y hy
    exact hF y hy

private theorem antiderivativesX_eq_primitiveT :
    AntiderivativesX integrand =
      PrimitiveFamilyX (fun x => primitiveT (t x)) := by
  apply antiderivativesX_eq_primitiveFamily
  exact hasDerivAt_composed_primitive

private theorem pullback_half_eq_primitiveFamily :
    PullbackFamily (HalfParameterFamily tIntegrand) =
      PrimitiveFamilyX (fun x => primitiveT (t x)) := by
  ext F
  constructor
  · rintro ⟨G, ⟨H, hH, hGH⟩, hFG⟩
    have hp2 : ∀ u, HasDerivAt (fun v => 2 * primitiveT v)
        (tIntegrand u) u := by
      intro u
      convert (hasDerivAt_primitiveT u).const_mul 2 using 1 <;> ring
    obtain ⟨C, hHC⟩ := same_deriv_global hH hp2
    refine ⟨C / 2, ?_⟩
    intro x hx
    rw [hFG x hx, hGH (t x), hHC (t x)]
    ring
  · rintro ⟨C, hF⟩
    let G : ℝ → ℝ := fun u => primitiveT u + C
    let H : ℝ → ℝ := fun u => 2 * (primitiveT u + C)
    have hHA : H ∈ AntiderivativesT tIntegrand := by
      intro u
      have h := ((hasDerivAt_primitiveT u).add_const C).const_mul 2
      convert h using 1 <;> ring
    have hGH : ∀ u, G u = 1 / 2 * H u := by
      intro u
      dsimp [G, H]
      ring
    refine ⟨G, ⟨H, hHA, hGH⟩, ?_⟩
    intro x hx
    simpa [G] using hF x hx

private theorem tIntegrand_eq_rewritten :
    tIntegrand = rewrittenTIntegrand := by
  funext u
  unfold tIntegrand rewrittenTIntegrand
  ring

private def baseA (u : ℝ) :=
  2 / Real.sqrt 3 *
    Real.arctan ((2 * u + 1) / Real.sqrt 3)

private def baseB (u : ℝ) :=
  -1 / (1 + u + u ^ 2)

private def baseD (u : ℝ) :=
  (2 * u + 1) / (3 * (1 + u + u ^ 2)) +
    4 / (3 * Real.sqrt 3) *
      Real.arctan ((2 * u + 1) / Real.sqrt 3)

private theorem hasDerivAt_baseA (u : ℝ) :
    HasDerivAt baseA (1 / (1 + u + u ^ 2)) u := by
  have hs := sqrt_three_ne
  have hqne : 1 + u + u ^ 2 ≠ 0 := ne_of_gt (quadratic_pos u)
  have hz : HasDerivAt
      (fun v : ℝ => (2 * v + 1) / Real.sqrt 3)
      (2 / Real.sqrt 3) u := by
    convert (((hasDerivAt_id u).const_mul 2).add_const 1).div_const
      (Real.sqrt 3) using 1 <;> ring
  have hat := (Real.hasDerivAt_arctan
      ((2 * u + 1) / Real.sqrt 3)).comp u hz
  convert hat.const_mul (2 / Real.sqrt 3) using 1
  · field_simp [hs, hqne] <;>
      simp only [sqrt_three_sq_aux] <;> ring

private theorem hasDerivAt_baseB (u : ℝ) :
    HasDerivAt baseB ((2 * u + 1) / (1 + u + u ^ 2) ^ 2) u := by
  have hqne : 1 + u + u ^ 2 ≠ 0 := ne_of_gt (quadratic_pos u)
  have hq := hasDerivAt_quadratic u
  have hb := (hasDerivAt_const u (-1 : ℝ)).div hq hqne
  convert hb using 1
  · field_simp [hqne] <;> ring

private theorem hasDerivAt_baseD (u : ℝ) :
    HasDerivAt baseD (1 / (1 + u + u ^ 2) ^ 2) u := by
  have hs := sqrt_three_ne
  have hqne : 1 + u + u ^ 2 ≠ 0 := ne_of_gt (quadratic_pos u)
  have hq := hasDerivAt_quadratic u
  have hn : HasDerivAt (fun v : ℝ => 2 * v + 1) 2 u := by
    convert ((hasDerivAt_id u).const_mul 2).add_const 1 using 1 <;> ring
  have hd := hq.const_mul 3
  have hrat := hn.div hd (mul_ne_zero (by norm_num) hqne)
  have hz : HasDerivAt
      (fun v : ℝ => (2 * v + 1) / Real.sqrt 3)
      (2 / Real.sqrt 3) u := by
    convert (((hasDerivAt_id u).const_mul 2).add_const 1).div_const
      (Real.sqrt 3) using 1 <;> ring
  have hat := (Real.hasDerivAt_arctan
      ((2 * u + 1) / Real.sqrt 3)).comp u hz
  have hsum := hrat.add (hat.const_mul (4 / (3 * Real.sqrt 3)))
  convert hsum using 1
  · field_simp [hs, hqne] <;>
      simp only [sqrt_three_sq_aux] <;> ring

private theorem canonical_decomposition (u : ℝ) :
    1 / 2 * baseA u - 1 / 4 * baseB u + 1 / 4 * baseD u =
      primitiveT u := by
  have hs := sqrt_three_ne
  have hqne : 1 + u + u ^ 2 ≠ 0 := ne_of_gt (quadratic_pos u)
  unfold baseA baseB baseD primitiveT
  field_simp [hs, hqne] <;> ring

private theorem decomposition_eq_half :
    DecompositionParameterFamily =
      HalfParameterFamily rewrittenTIntegrand := by
  ext G
  constructor
  · rintro ⟨A, hA, B, hB, D, hD, hG⟩
    let H : ℝ → ℝ := fun u =>
      2 * (1 / 2 * A u - 1 / 4 * B u + 1 / 4 * D u)
    have hHA : H ∈ AntiderivativesT rewrittenTIntegrand := by
      intro u
      have hqne : 1 + u + u ^ 2 ≠ 0 := ne_of_gt (quadratic_pos u)
      have hcomb := (((hA u).const_mul (1 / 2)).sub
        ((hB u).const_mul (1 / 4))).add
        ((hD u).const_mul (1 / 4))
      have hscaled := hcomb.const_mul 2
      convert hscaled using 1
      · unfold rewrittenTIntegrand
        field_simp [hqne] <;> ring
    refine ⟨H, hHA, ?_⟩
    intro u
    rw [hG u]
    dsimp [H]
    ring
  · rintro ⟨H, hH, hGH⟩
    have hp2 : ∀ u, HasDerivAt (fun v => 2 * primitiveT v)
        (rewrittenTIntegrand u) u := by
      intro u
      have hp := (hasDerivAt_primitiveT u).const_mul 2
      rw [← congrFun tIntegrand_eq_rewritten u]
      convert hp using 1 <;> ring
    obtain ⟨C, hHC⟩ := same_deriv_global hH hp2
    refine ⟨fun u => baseA u + C, ?_, baseB, ?_, baseD, ?_, ?_⟩
    · intro u
      exact (hasDerivAt_baseA u).add_const C
    · exact hasDerivAt_baseB
    · exact hasDerivAt_baseD
    · intro u
      rw [hGH u, hHC u]
      change 1 / 2 * (2 * primitiveT u + C) =
        1 / 2 * (baseA u + C) - 1 / 4 * baseB u + 1 / 4 * baseD u
      rw [← canonical_decomposition u]
      ring

theorem gap1 (x : ℝ) (hx : x ∈ xBranch) :
    -Real.pi < x := by
  exact hx.1
theorem gap2 (x : ℝ) (hx : x ∈ xBranch) :
    x < Real.pi := by
  exact hx.2
theorem gap3 (x : ℝ) (hx : x ∈ xBranch) :
    Real.sin x = 2 * t x / (1 + t x ^ 2) := by
  exact sin_eq_two_t_div x hx
theorem gap4 (x : ℝ) (hx : x ∈ xBranch) :
    1 = 2 / (1 + t x ^ 2) * deriv t x := by
  rw [(hasDerivAt_t x hx).deriv]
  have hne : 1 + t x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (t x)]
  field_simp [hne]
theorem gap5 :
    AntiderivativesX integrand =
      PullbackFamily (HalfParameterFamily tIntegrand) := by
  calc
    AntiderivativesX integrand =
        PrimitiveFamilyX (fun x => primitiveT (t x)) :=
      antiderivativesX_eq_primitiveT
    _ = PullbackFamily (HalfParameterFamily tIntegrand) :=
      pullback_half_eq_primitiveFamily.symm
theorem gap6 :
    PullbackFamily (HalfParameterFamily tIntegrand) =
      PullbackFamily (HalfParameterFamily rewrittenTIntegrand) := by
  rw [tIntegrand_eq_rewritten]
theorem gap7 :
    AntiderivativesX integrand =
      PullbackFamily (HalfParameterFamily rewrittenTIntegrand) := by
  exact gap5.trans gap6
theorem gap8 :
    AntiderivativesX integrand =
      PullbackFamily DecompositionParameterFamily := by
  calc
    AntiderivativesX integrand =
        PullbackFamily (HalfParameterFamily rewrittenTIntegrand) := gap7
    _ = PullbackFamily DecompositionParameterFamily :=
      congrArg PullbackFamily decomposition_eq_half.symm
theorem gap9 :
    AntiderivativesX integrand =
      PrimitiveFamilyX (fun x => primitiveT (t x)) := by
  exact antiderivativesX_eq_primitiveT
theorem gap10 (x : ℝ) (hx : x ∈ xBranch) :
    (t x + 2) / (6 * (1 + t x + t x ^ 2)) =
      1 / 6 *
        ((Real.sin (x / 2) + 2 * Real.cos (x / 2)) /
          Real.cos (x / 2)) /
        ((1 + Real.sin (x / 2) * Real.cos (x / 2)) /
          Real.cos (x / 2) ^ 2) := by
  have hc := half_cos_ne x hx
  have hd := one_add_sin_mul_cos_ne (x / 2)
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  have hq : 1 + t x + t x ^ 2 =
      (1 + Real.sin (x / 2) * Real.cos (x / 2)) /
        Real.cos (x / 2) ^ 2 := by
    unfold t
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc]
    nlinarith [hs]
  rw [hq]
  unfold t
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc, hd]
theorem gap11 (x : ℝ) (hx : x ∈ xBranch) :
    1 / 6 *
        ((Real.sin (x / 2) + 2 * Real.cos (x / 2)) /
          Real.cos (x / 2)) /
        ((1 + Real.sin (x / 2) * Real.cos (x / 2)) /
          Real.cos (x / 2) ^ 2) =
      1 / 6 * ((1 / 2 * Real.sin x + 1 + Real.cos x) /
        (1 / 2 * Real.sin x + 1)) := by
  have hc := half_cos_ne x hx
  have hd := one_add_sin_mul_cos_ne (x / 2)
  have hs : Real.sin x =
      2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    conv_lhs =>
      rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]
  have hcos : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    conv_lhs =>
      rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
  have hnum :
      1 / 2 * Real.sin x + 1 + Real.cos x =
        Real.cos (x / 2) *
          (Real.sin (x / 2) + 2 * Real.cos (x / 2)) := by
    rw [hs, hcos]
    ring
  have hden :
      1 / 2 * Real.sin x + 1 =
        1 + Real.sin (x / 2) * Real.cos (x / 2) := by
    rw [hs]
    ring
  rw [hnum, hden]
  field_simp [hc, hd] <;> ring
theorem gap12 (x : ℝ) (hx : x ∈ xBranch) :
    1 / 6 * ((1 / 2 * Real.sin x + 1 + Real.cos x) /
        (1 / 2 * Real.sin x + 1)) =
      1 / 6 + Real.cos x / (3 * (2 + Real.sin x)) := by
  have hs := Real.neg_one_le_sin x
  have hne : 2 + Real.sin x ≠ 0 := by
    nlinarith
  have hnum :
      1 / 2 * Real.sin x + 1 + Real.cos x =
        (2 + Real.sin x + 2 * Real.cos x) / 2 := by
    ring
  have hden :
      1 / 2 * Real.sin x + 1 =
        (2 + Real.sin x) / 2 := by
    ring
  rw [hnum, hden]
  field_simp [hne] <;> ring
theorem gap13 (x : ℝ) (hx : x ∈ xBranch) :
    (t x + 2) / (6 * (1 + t x + t x ^ 2)) =
      1 / 6 + Real.cos x / (3 * (2 + Real.sin x)) := by
  calc
    (t x + 2) / (6 * (1 + t x + t x ^ 2)) =
        1 / 6 *
          ((Real.sin (x / 2) + 2 * Real.cos (x / 2)) /
            Real.cos (x / 2)) /
          ((1 + Real.sin (x / 2) * Real.cos (x / 2)) /
            Real.cos (x / 2) ^ 2) := gap10 x hx
    _ = 1 / 6 * ((1 / 2 * Real.sin x + 1 + Real.cos x) /
          (1 / 2 * Real.sin x + 1)) := gap11 x hx
    _ = 1 / 6 + Real.cos x / (3 * (2 + Real.sin x)) := gap12 x hx
theorem gap14 :
    AntiderivativesX integrand = PrimitiveFamilyX primitive := by
  rw [gap9]
  have hp : ∀ x ∈ xBranch,
      primitiveT (t x) = primitive x + 1 / 6 := by
    intro x hx
    have hr := gap13 x hx
    have hz : 2 * t x + 1 =
        1 + 2 * Real.tan (x / 2) := by
      unfold t
      ring
    unfold primitiveT primitive
    rw [hr, hz]
    ring
  ext F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C + 1 / 6, ?_⟩
    intro x hx
    rw [hF x hx]
    change primitiveT (t x) + C = primitive x + (C + 1 / 6)
    rw [hp x hx]
    ring
  · rintro ⟨C, hF⟩
    refine ⟨C - 1 / 6, ?_⟩
    intro x hx
    rw [hF x hx]
    change primitive x + C = primitiveT (t x) + (C - 1 / 6)
    rw [hp x hx]
    ring

end
end ProofGap.Exercise2146
