import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1921

noncomputable section

def quadratic (a b c x : ℝ) := a * x ^ 2 + b * x + c
def t (a b x : ℝ) := 2 * a * x + b
def discr (a b c : ℝ) := 4 * a * c - b ^ 2
def regularBranch (a b c : ℝ) : Set ℝ := {x | quadratic a b c x ≠ 0}
def zeroBranch (a b : ℝ) : Set ℝ := {x | x + b / (2 * a) > 0}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def generalIntegrand (a b c : ℝ) (n : ℕ) (x : ℝ) :=
  1 / (quadratic a b c x) ^ n
def I (a b c : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  AntiderivativesOn (regularBranch a b c) (generalIntegrand a b c n)
def transformedIntegrand (a b c : ℝ) (n : ℕ) (x : ℝ) :=
  (4 * a) ^ n / ((t a b x) ^ 2 + discr a b c) ^ n
def jIntegrand (a b c : ℝ) (n : ℕ) (x : ℝ) :=
  1 / ((t a b x) ^ 2 + discr a b c) ^ n * deriv (t a b) x
def J (a b c : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  AntiderivativesOn (regularBranch a b c) (jIntegrand a b c n)
def scaleCoeff (a : ℝ) (n : ℕ) : ℝ :=
  2 ^ (2 * n - 1) * a ^ (n - 1)
def ScaledJFamily (a b c : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ J a b c n,
    ∀ x ∈ regularBranch a b c, F x = scaleCoeff a n * G x}
def jResidual (a b c : ℝ) (n : ℕ) (x : ℝ) :=
  (t a b x) ^ 2 / ((t a b x) ^ 2 + discr a b c) ^ (n + 1) *
    deriv (t a b) x
def jRewrittenResidual (a b c : ℝ) (n : ℕ) (x : ℝ) :=
  ((t a b x) ^ 2 + discr a b c - discr a b c) /
      ((t a b x) ^ 2 + discr a b c) ^ (n + 1) *
    deriv (t a b) x
def jBoundary (a b c : ℝ) (n : ℕ) (x : ℝ) :=
  t a b x / ((t a b x) ^ 2 + discr a b c) ^ n
def JByPartsFamily (a b c : ℝ) (n : ℕ) (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (regularBranch a b c) r,
    ∀ x ∈ regularBranch a b c,
      F x = jBoundary a b c n x + 2 * (n : ℝ) * G x}
def JRawRecurrenceFamily (a b c : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ J a b c n, ∃ H ∈ J a b c (n + 1),
    ∀ x ∈ regularBranch a b c,
      F x = jBoundary a b c n x + 2 * (n : ℝ) * G x -
        2 * (n : ℝ) * discr a b c * H x}
def JStepFamily (a b c : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ J a b c n,
    ∀ x ∈ regularBranch a b c,
      F x =
        1 / (2 * (n : ℝ) * discr a b c) * jBoundary a b c n x +
        (2 * (n : ℝ) - 1) / (2 * (n : ℝ)) *
          (1 / discr a b c) * G x}
def iBoundary (a b c : ℝ) (n : ℕ) (x : ℝ) :=
  1 / (((n : ℝ) - 1) * discr a b c) *
    (2 * a * x + b) / (quadratic a b c x) ^ (n - 1)
def IStepFamily (a b c : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ I a b c (n - 1),
    ∀ x ∈ regularBranch a b c,
      F x = iBoundary a b c n x +
        (2 * (n : ℝ) - 3) / ((n : ℝ) - 1) *
          (2 * a / discr a b c) * G x}
def zeroTransformedIntegrand (a b : ℝ) (n : ℕ) (x : ℝ) :=
  (4 * a) ^ n / (2 * a * x + b) ^ (2 * n)
def zeroJIntegrand (a b : ℝ) (n : ℕ) (x : ℝ) :=
  1 / (2 * a * x + b) ^ (2 * n) * deriv (t a b) x
def ZeroScaledFamily (a b : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (zeroBranch a b) (zeroJIntegrand a b n),
    ∀ x ∈ zeroBranch a b, F x = scaleCoeff a n * G x}
def zeroPrimitive (a b : ℝ) (n : ℕ) (x : ℝ) :=
  1 / (a ^ n * (1 - 2 * (n : ℝ))) *
    Real.rpow (x + b / (2 * a)) (1 - 2 * (n : ℝ))
def q₃ (x : ℝ) := x ^ 2 + x + 1
def i3Integrand (x : ℝ) := 1 / (q₃ x) ^ 3
def i2Integrand (x : ℝ) := 1 / (q₃ x) ^ 2
def i1Integrand (x : ℝ) := 1 / q₃ x
def I3 : Set (ℝ → ℝ) := AntiderivativesOn Set.univ i3Integrand
def I3Step1 : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn Set.univ i2Integrand,
    ∀ x, F x = (2 * x + 1) / (6 * (q₃ x) ^ 2) + G x}
def I3Step2 : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn Set.univ i1Integrand,
    ∀ x, F x = (2 * x + 1) / (6 * (q₃ x) ^ 2) +
      (2 * x + 1) / (3 * q₃ x) + (2 / 3 : ℝ) * G x}
def i3Primitive (x : ℝ) :=
  (2 * x + 1) / (6 * (q₃ x) ^ 2) +
    (2 * x + 1) / (3 * q₃ x) +
    4 / (3 * Real.sqrt 3) *
      Real.arctan ((2 * x + 1) / Real.sqrt 3)
def I3PrimitiveFamily : Set (ℝ → ℝ) :=
  PrimitiveFamilyOn Set.univ i3Primitive

private theorem regularBranch_isOpen (a b c : ℝ) :
    IsOpen (regularBranch a b c) := by
  unfold regularBranch
  have hc : Continuous (quadratic a b c) := by
    unfold quadratic
    fun_prop
  have hz : IsOpen {y : ℝ | y ≠ 0} := isOpen_ne
  exact hz.preimage hc

private theorem zeroBranch_isOpen (a b : ℝ) :
    IsOpen (zeroBranch a b) := by
  unfold zeroBranch
  exact isOpen_lt continuous_const
    (continuous_id.add continuous_const)

private theorem zeroBranch_preconnected (a b : ℝ) :
    IsPreconnected (zeroBranch a b) := by
  have heq : zeroBranch a b = Set.Ioi (-b / (2 * a)) := by
    ext x
    change x + b / (2 * a) > 0 ↔ x > -b / (2 * a)
    have hneg : -b / (2 * a) = -(b / (2 * a)) := by ring
    rw [hneg]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact isPreconnected_Ioi

private theorem deriv_t (a b x : ℝ) :
    deriv (t a b) x = 2 * a := by
  have h : HasDerivAt (t a b) (2 * a) x := by
    unfold t
    convert (hasDerivAt_id x).const_mul (2 * a) |>.add_const b using 1 <;> ring
  exact h.deriv

private theorem antiderivatives_congr
    {s : Set ℝ} {f g : ℝ → ℝ} (hfg : ∀ x ∈ s, f x = g x) :
    AntiderivativesOn s f = AntiderivativesOn s g := by
  ext F
  constructor <;> intro h <;> intro x hx
  · simpa [hfg x hx] using h x hx
  · simpa [hfg x hx] using h x hx

private theorem antiderivatives_scale
    {s : Set ℝ} (hopen : IsOpen s) (f g : ℝ → ℝ) (k : ℝ) (hk : k ≠ 0)
    (hfg : ∀ x ∈ s, f x = k * g x) :
    AntiderivativesOn s f =
      {F | ∃ G ∈ AntiderivativesOn s g, ∀ x ∈ s, F x = k * G x} := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => F x / k, ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).div_const k
      convert h using 1
      rw [hfg x hx]
      field_simp [hk]
    · intro x hx
      field_simp [hk]
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => k * G y := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    have h := (hG x hx).const_mul k
    rw [← hfg x hx] at h
    exact h.congr_of_eventuallyEq heq

private theorem antiderivatives_boundary_scale
    {s : Set ℝ} (hopen : IsOpen s) (f g p : ℝ → ℝ) (k : ℝ) (hk : k ≠ 0)
    (hp : ∀ x ∈ s, HasDerivAt p (f x - k * g x) x) :
    AntiderivativesOn s f =
      {F | ∃ G ∈ AntiderivativesOn s g,
        ∀ x ∈ s, F x = p x + k * G x} := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => (F x - p x) / k, ?_, ?_⟩
    · intro x hx
      have h := ((hF x hx).sub (hp x hx)).div_const k
      convert h using 1
      field_simp [hk]
      ring
    · intro x hx
      field_simp [hk]
      ring
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + k * G y := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    have h := (hp x hx).add ((hG x hx).const_mul k)
    convert h.congr_of_eventuallyEq heq using 1 <;> ring

private theorem antiderivatives_eq_translates
    {s : Set ℝ} (hopen : IsOpen s) (hs : IsPreconnected s)
    (f p : ℝ → ℝ) (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x0, hx0⟩
      have hz : ∀ x ∈ s, HasDerivAt (fun y => F y - p y) 0 x := by
        intro x hx
        simpa using (hF x hx).sub (hp x hx)
      have hdiff : DifferentiableOn ℝ (fun y => F y - p y) s := by
        intro x hx
        exact (hz x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ s, deriv (fun y => F y - p y) x = 0 := by
        intro x hx
        exact (hz x hx).deriv
      refine ⟨F x0 - p x0, ?_⟩
      intro x hx
      have heq : F x - p x = F x0 - p x0 :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv
          (x := x) (y := x0) hx hx0
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

theorem gap1 (a b c x : ℝ) :
    4 * a * quadratic a b c x =
      (2 * a * x + b) ^ 2 + 4 * a * c - b ^ 2 := by
  unfold quadratic
  ring
theorem gap2 (a b c x : ℝ) :
    (2 * a * x + b) ^ 2 + 4 * a * c - b ^ 2 =
      (t a b x) ^ 2 + discr a b c := by
  unfold t discr
  ring
theorem gap3 (a b c x : ℝ) :
    4 * a * quadratic a b c x =
      (t a b x) ^ 2 + discr a b c := by
  rw [gap1, gap2]
theorem gap4 (a b c : ℝ) (n : ℕ) :
    I a b c n =
      AntiderivativesOn (regularBranch a b c) (generalIntegrand a b c n) := by
  rfl
theorem gap5 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ) :
    I a b c n =
      AntiderivativesOn (regularBranch a b c) (transformedIntegrand a b c n) := by
  rw [gap4]
  apply antiderivatives_congr
  intro x hx
  have hq : quadratic a b c x ≠ 0 := hx
  have h4a : 4 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  unfold generalIntegrand transformedIntegrand
  rw [← gap3 a b c x, mul_pow]
  field_simp [h4a, hq]
  simp only [mul_pow]
  ring
theorem gap6 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    AntiderivativesOn (regularBranch a b c) (transformedIntegrand a b c n) =
      ScaledJFamily a b c n := by
  unfold ScaledJFamily J
  apply antiderivatives_scale (regularBranch_isOpen a b c)
  · unfold scaleCoeff
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ ha)
  · intro x hx
    have hcoeff : (4 * a) ^ n = scaleCoeff a n * (2 * a) := by
      calc
        (4 * a) ^ n = 2 ^ (2 * n) * a ^ n := by
          rw [mul_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        _ = 2 ^ ((2 * n - 1) + 1) * a ^ ((n - 1) + 1) := by
          congr 2 <;> omega
        _ = scaleCoeff a n * (2 * a) := by
          rw [pow_succ, pow_succ]
          unfold scaleCoeff
          ring
    unfold transformedIntegrand jIntegrand
    rw [deriv_t]
    rw [hcoeff]
    ring
theorem gap7 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    I a b c n = ScaledJFamily a b c n := by
  rw [gap5 a b c ha n, gap6 a b c ha n hn]

private theorem jBoundary_hasDerivAt (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : x ∈ regularBranch a b c) :
    HasDerivAt (jBoundary a b c n)
      (jIntegrand a b c n x -
        2 * (n : ℝ) * jResidual a b c n x) x := by
  by_cases ha : a = 0
  · subst a
    have heq : jBoundary 0 b c n = fun _ => 0 := by
      funext y
      simp [jBoundary, t, discr, hn.ne']
    rw [heq]
    convert (hasDerivAt_const (x := x) (c := (0 : ℝ))) using 1
    simp [jIntegrand, jResidual, t, discr, deriv_t, hn.ne']
  · have hq : quadratic a b c x ≠ 0 := hx
    have hden : (t a b x) ^ 2 + discr a b c ≠ 0 := by
      rw [← gap3]
      exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hq
    have ht : HasDerivAt (t a b) (2 * a) x := by
      unfold t
      convert ((hasDerivAt_id x).const_mul (2 * a)).add_const b using 1 <;> ring
    have hd :
        HasDerivAt (fun y => (t a b y) ^ 2 + discr a b c)
          (2 * t a b x * (2 * a)) x := by
      convert (ht.pow 2).add_const (discr a b c) using 1 <;> ring
    have hb := ht.div (hd.pow n) (pow_ne_zero n hden)
    convert hb using 1
    unfold jIntegrand jResidual
    simp only [deriv_t]
    rw [show n = (n - 1) + 1 by omega]
    simp only [Pi.pow_apply, pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp [hden]
    rw [show n - 1 + 1 - 1 = n - 1 by omega]
    ring

theorem gap8 (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (hΔ : discr a b c ≠ 0) :
    J a b c n = JByPartsFamily a b c n (jResidual a b c n) := by
  unfold J JByPartsFamily
  apply antiderivatives_boundary_scale (regularBranch_isOpen a b c)
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast hn.ne')
  · intro x hx
    exact jBoundary_hasDerivAt a b c n hn x hx

theorem gap9 (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (hΔ : discr a b c ≠ 0) :
    J a b c n = JByPartsFamily a b c n (jRewrittenResidual a b c n) := by
  have hr : jResidual a b c n = jRewrittenResidual a b c n := by
    funext x
    unfold jResidual jRewrittenResidual
    ring
  rw [gap8 a b c n hn hΔ, hr]

private theorem jResidual_eq_sub (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (x : ℝ) :
    jResidual a b c n x =
      jIntegrand a b c n x -
        discr a b c * jIntegrand a b c (n + 1) x := by
  unfold jResidual jIntegrand
  simp only [deriv_t]
  by_cases hden : (t a b x) ^ 2 + discr a b c = 0
  · simp [hden, hn.ne']
  · rw [pow_succ]
    field_simp [hden]
    ring

theorem gap10 (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (hΔ : discr a b c ≠ 0) :
    J a b c n = JRawRecurrenceFamily a b c n := by
  unfold J JRawRecurrenceFamily
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcoef : 2 * (n : ℝ) * discr a b c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hnR) hΔ
  ext F
  constructor
  · intro hF
    let H : ℝ → ℝ := fun y =>
      1 / (2 * (n : ℝ) * discr a b c) *
        (jBoundary a b c n y + (2 * (n : ℝ) - 1) * F y)
    refine ⟨F, hF, H, ?_, ?_⟩
    · intro x hx
      have hb := jBoundary_hasDerivAt a b c n hn x hx
      have hraw :=
        (hb.add ((hF x hx).const_mul (2 * (n : ℝ) - 1))).const_mul
          (1 / (2 * (n : ℝ) * discr a b c))
      convert hraw using 1
      rw [jResidual_eq_sub a b c n hn x]
      field_simp [hcoef]
      ring
    · intro x hx
      dsimp [H]
      field_simp [hcoef]
      ring
  · rintro ⟨G, hG, H, hH, hEq⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y =>
        jBoundary a b c n y + 2 * (n : ℝ) * G y -
          2 * (n : ℝ) * discr a b c * H y := by
      filter_upwards [(regularBranch_isOpen a b c).mem_nhds hx] with y hy
      exact hEq y hy
    have hb := jBoundary_hasDerivAt a b c n hn x hx
    have hraw :=
      (hb.add ((hG x hx).const_mul (2 * (n : ℝ)))).sub
        ((hH x hx).const_mul (2 * (n : ℝ) * discr a b c))
    have hfinal := hraw.congr_of_eventuallyEq heq
    convert hfinal using 1
    rw [jResidual_eq_sub a b c n hn x]
    ring
theorem gap11 (a b c : ℝ) (n : ℕ) (hn : 0 < n) (hΔ : discr a b c ≠ 0) :
    J a b c (n + 1) = JStepFamily a b c n := by
  unfold J JStepFamily
  let α : ℝ := 1 / (2 * (n : ℝ) * discr a b c)
  let k : ℝ := (2 * (n : ℝ) - 1) / (2 * (n : ℝ)) *
    (1 / discr a b c)
  change AntiderivativesOn (regularBranch a b c) (jIntegrand a b c (n + 1)) =
    {F | ∃ G ∈ AntiderivativesOn (regularBranch a b c) (jIntegrand a b c n),
      ∀ x ∈ regularBranch a b c,
        F x = α * jBoundary a b c n x + k * G x}
  apply antiderivatives_boundary_scale (regularBranch_isOpen a b c)
      (jIntegrand a b c (n + 1)) (jIntegrand a b c n)
      (fun x => α * jBoundary a b c n x) k
  · unfold k
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnRone : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    exact mul_ne_zero
      (div_ne_zero (by nlinarith) (mul_ne_zero (by norm_num) hnR))
      (one_div_ne_zero hΔ)
  · intro x hx
    by_cases ha : a = 0
    · subst a
      have hn0 : n ≠ 0 := hn.ne'
      have hnp : n + 1 ≠ 0 := by omega
      simp [α, k, jIntegrand, jBoundary, t, discr, deriv_t, hn0, hnp]
      exact hasDerivAt_const x 0
    · have hq : quadratic a b c x ≠ 0 := hx
      have hden :
          (t a b x) ^ 2 + discr a b c ≠ 0 := by
        rw [← gap3]
        exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hq
      have ht : HasDerivAt (t a b) (2 * a) x := by
        unfold t
        convert ((hasDerivAt_id x).const_mul (2 * a)).add_const b using 1 <;> ring
      have hd :
          HasDerivAt (fun y => (t a b y) ^ 2 + discr a b c)
            (2 * t a b x * (2 * a)) x := by
        convert (ht.pow 2).add_const (discr a b c) using 1 <;> ring
      have hb :=
        ht.div (hd.pow n) (pow_ne_zero n hden)
      have hp := hb.const_mul α
      convert hp using 1
      unfold α k jIntegrand
      simp only [deriv_t]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [show n = (n - 1) + 1 by omega]
      simp only [Pi.pow_apply, pow_succ, Nat.cast_add, Nat.cast_one]
      field_simp [hden, hΔ, hnR]
      rw [show n - 1 + 1 - 1 = n - 1 by omega]
      ring
theorem gap12 (a b c : ℝ) (n : ℕ) (hn : 1 < n) (hΔ : discr a b c ≠ 0) :
    J a b c n = JStepFamily a b c (n - 1) := by
  have hpos : 0 < n - 1 := Nat.sub_pos_of_lt hn
  have hstep := gap11 a b c (n - 1) hpos hΔ
  have hn1 : 1 ≤ n := le_trans (by norm_num) (Nat.le_of_lt hn)
  rw [Nat.sub_add_cancel hn1] at hstep
  exact hstep
theorem gap13 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ)
    (hn : 1 < n) (hΔ : discr a b c ≠ 0) :
    I a b c n = IStepFamily a b c n := by
  unfold I IStepFamily
  let k : ℝ := (2 * (n : ℝ) - 3) / ((n : ℝ) - 1) *
    (2 * a / discr a b c)
  change AntiderivativesOn (regularBranch a b c) (generalIntegrand a b c n) =
    {F | ∃ G ∈ AntiderivativesOn (regularBranch a b c)
        (generalIntegrand a b c (n - 1)),
      ∀ x ∈ regularBranch a b c, F x = iBoundary a b c n x + k * G x}
  apply antiderivatives_boundary_scale (regularBranch_isOpen a b c)
      (generalIntegrand a b c n) (generalIntegrand a b c (n - 1))
      (iBoundary a b c n) k
  · unfold k
    have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    exact mul_ne_zero
      (div_ne_zero (by nlinarith) (by nlinarith))
      (div_ne_zero (mul_ne_zero (by norm_num) ha) hΔ)
  · intro x hx
    have hq : quadratic a b c x ≠ 0 := hx
    have ht : HasDerivAt (t a b) (2 * a) x := by
      unfold t
      convert ((hasDerivAt_id x).const_mul (2 * a)).add_const b using 1 <;> ring
    have hquad :
        HasDerivAt (quadratic a b c) (t a b x) x := by
      unfold quadratic t
      convert
        ((((hasDerivAt_id x).pow 2).const_mul a).add
          ((hasDerivAt_id x).const_mul b)).add_const c using 1 <;>
        simp only [id_eq] <;> ring
    have hb :=
      ht.div (hquad.pow (n - 1)) (pow_ne_zero (n - 1) hq)
    have hp :=
      hb.const_mul (1 / (((n : ℝ) - 1) * discr a b c))
    convert hp using 1
    · funext y
      simp [iBoundary, t, Pi.pow_apply]
      ring
    · unfold generalIntegrand k
      have hnR : (n : ℝ) - 1 ≠ 0 := by
        have : 1 < (n : ℝ) := by exact_mod_cast hn
        linarith
      rw [show n = (n - 1) + 1 by omega]
      simp only [Pi.pow_apply, pow_succ, Nat.cast_add, Nat.cast_one]
      simp only [Nat.add_sub_cancel]
      rw [show n - 1 = (n - 1 - 1) + 1 by omega]
      simp only [pow_succ, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      have htSq :
          t a b x ^ 2 = 4 * a * quadratic a b c x - discr a b c := by
        nlinarith [gap3 a b c x]
      field_simp [hq, hΔ, hnR, ha]
      ring_nf
      rw [htSq]
      ring
theorem gap14 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ)
    (hn : 1 < n) (hΔ : discr a b c ≠ 0) :
    I a b c n = IStepFamily a b c n := by
  exact gap13 a b c ha n hn hΔ
theorem gap15 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ) (hΔ : discr a b c = 0) :
    I a b c n =
      AntiderivativesOn (regularBranch a b c) (zeroTransformedIntegrand a b n) := by
  rw [gap5 a b c ha n]
  apply antiderivatives_congr
  intro x hx
  unfold transformedIntegrand zeroTransformedIntegrand
  rw [hΔ]
  simp only [add_zero, t, pow_mul]
theorem gap16 (a b : ℝ) (ha : a ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    AntiderivativesOn (zeroBranch a b) (zeroTransformedIntegrand a b n) =
      ZeroScaledFamily a b n := by
  unfold ZeroScaledFamily
  apply antiderivatives_scale (zeroBranch_isOpen a b)
  · unfold scaleCoeff
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ha)
  · intro x hx
    have hcoeff : (4 * a) ^ n = scaleCoeff a n * (2 * a) := by
      calc
        (4 * a) ^ n = 2 ^ (2 * n) * a ^ n := by
          rw [mul_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        _ = 2 ^ ((2 * n - 1) + 1) * a ^ ((n - 1) + 1) := by
          congr 2 <;> omega
        _ = scaleCoeff a n * (2 * a) := by
          rw [pow_succ, pow_succ]
          unfold scaleCoeff
          ring
    unfold zeroTransformedIntegrand zeroJIntegrand
    rw [deriv_t, hcoeff]
    ring
theorem gap17 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ)
    (hn : 1 ≤ n) (hΔ : discr a b c = 0) :
    AntiderivativesOn (zeroBranch a b) (generalIntegrand a b c n) =
      ZeroScaledFamily a b n := by
  rw [← gap16 a b ha n hn]
  apply antiderivatives_congr
  intro x hx
  have hzpos : 0 < x + b / (2 * a) := hx
  have htform : t a b x = 2 * a * (x + b / (2 * a)) := by
    unfold t
    field_simp [ha]
  have htne : t a b x ≠ 0 := by
    rw [htform]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) (ne_of_gt hzpos)
  have hq : quadratic a b c x ≠ 0 := by
    intro hzero
    have hid := gap3 a b c x
    rw [hΔ, hzero] at hid
    simp at hid
    exact htne (sq_eq_zero_iff.mp hid.symm)
  calc
    generalIntegrand a b c n x = transformedIntegrand a b c n x := by
      have h4a : 4 * a ≠ 0 := mul_ne_zero (by norm_num) ha
      unfold generalIntegrand transformedIntegrand
      rw [← gap3 a b c x, mul_pow]
      field_simp [h4a, hq]
      simp only [mul_pow]
      ring
    _ = zeroTransformedIntegrand a b n x := by
      unfold transformedIntegrand zeroTransformedIntegrand
      rw [hΔ]
      simp only [add_zero, t, pow_mul]
theorem gap18 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ)
    (hn : 1 ≤ n) (hΔ : discr a b c = 0) :
    AntiderivativesOn (zeroBranch a b) (generalIntegrand a b c n) =
      PrimitiveFamilyOn (zeroBranch a b) (zeroPrimitive a b n) := by
  apply antiderivatives_eq_translates
    (zeroBranch_isOpen a b) (zeroBranch_preconnected a b)
  intro x hx
  let z : ℝ := x + b / (2 * a)
  let p : ℝ := 1 - 2 * (n : ℝ)
  have hzpos : 0 < z := hx
  have hz : z ≠ 0 := ne_of_gt hzpos
  have hpne : p ≠ 0 := by
    unfold p
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hzDeriv : HasDerivAt (fun y : ℝ => y + b / (2 * a)) 1 x :=
    (hasDerivAt_id x).add_const _
  have hrpow :=
    (Real.hasDerivAt_rpow_const (p := p) (Or.inl hz)).comp x hzDeriv
  have hraw :=
    hrpow.const_mul (1 / (a ^ n * p))
  have htform : t a b x = 2 * a * z := by
    unfold t z
    field_simp [ha]
  have hqform : quadratic a b c x = a * z ^ 2 := by
    have h4a : 4 * a ≠ 0 := mul_ne_zero (by norm_num) ha
    apply mul_left_cancel₀ h4a
    rw [gap3 a b c x, hΔ, htform]
    ring
  unfold zeroPrimitive
  change HasDerivAt
    (fun y => 1 / (a ^ n * p) *
      Real.rpow (y + b / (2 * a)) p)
    (generalIntegrand a b c n x) x
  convert hraw using 1
  unfold generalIntegrand
  rw [hqform, mul_pow]
  change 1 / (a ^ n * (z ^ 2) ^ n) =
    1 / (a ^ n * p) * (p * z ^ (p - 1) * 1)
  rw [show p - 1 = -((2 * n : ℕ) : ℝ) by
    unfold p
    push_cast
    ring]
  rw [Real.rpow_neg hzpos.le, Real.rpow_natCast]
  rw [← pow_mul]
  field_simp [ha, hpne, hz]
theorem gap19 (a b c : ℝ) (ha : a ≠ 0) (n : ℕ)
    (hn : 1 < n) (hΔ : discr a b c ≠ 0) :
    I a b c n = IStepFamily a b c n := by
  exact gap13 a b c ha n hn hΔ

private theorem q3_pos (x : ℝ) : 0 < q₃ x := by
  unfold q₃
  nlinarith [sq_nonneg (x + 1 / 2)]

private theorem q3_hasDerivAt (x : ℝ) :
    HasDerivAt q₃ (2 * x + 1) x := by
  unfold q₃
  convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1
    using 1 <;> simp only [id_eq] <;> ring

private theorem i3_boundary1_deriv (x : ℝ) :
    HasDerivAt (fun y => (2 * y + 1) / (6 * (q₃ y) ^ 2))
      (i3Integrand x - i2Integrand x) x := by
  have hq : q₃ x ≠ 0 := ne_of_gt (q3_pos x)
  have hn : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    convert ((hasDerivAt_id x).const_mul 2).add_const 1 using 1 <;> ring
  have hd := ((q3_hasDerivAt x).pow 2).const_mul 6
  have h := hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hq))
  convert h using 1
  unfold i3Integrand i2Integrand
  simp only [Pi.pow_apply]
  field_simp [hq]
  simp only [q₃]
  ring

private theorem i3_boundary2_deriv (x : ℝ) :
    HasDerivAt (fun y => (2 * y + 1) / (3 * q₃ y))
      (i2Integrand x - (2 / 3 : ℝ) * i1Integrand x) x := by
  have hq : q₃ x ≠ 0 := ne_of_gt (q3_pos x)
  have hn : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    convert ((hasDerivAt_id x).const_mul 2).add_const 1 using 1 <;> ring
  have hd := (q3_hasDerivAt x).const_mul 3
  have h := hn.div hd (mul_ne_zero (by norm_num) hq)
  convert h using 1
  unfold i2Integrand i1Integrand q₃
  field_simp [hq]
  ring

private def i1Primitive (x : ℝ) : ℝ :=
  2 / Real.sqrt 3 * Real.arctan ((2 * x + 1) / Real.sqrt 3)

private theorem i1Primitive_hasDerivAt (x : ℝ) :
    HasDerivAt i1Primitive (i1Integrand x) x := by
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  have hq : q₃ x ≠ 0 := ne_of_gt (q3_pos x)
  have hs2 : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have harg :
      HasDerivAt (fun y : ℝ => (2 * y + 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    convert (((hasDerivAt_id x).const_mul 2).add_const 1).div_const
      (Real.sqrt 3) using 1 <;> ring
  have h :=
    ((Real.hasDerivAt_arctan ((2 * x + 1) / Real.sqrt 3)).comp x harg)
      |>.const_mul (2 / Real.sqrt 3)
  unfold i1Primitive i1Integrand
  convert h using 1
  field_simp [hs, hq]
  rw [hs2]
  simp only [q₃]
  ring
theorem gap20 :
    I3 = AntiderivativesOn Set.univ i3Integrand := by
  rfl
theorem gap21 :
    I3 = I3Step1 := by
  unfold I3 I3Step1
  simpa using
    (antiderivatives_boundary_scale isOpen_univ i3Integrand i2Integrand
      (fun y => (2 * y + 1) / (6 * (q₃ y) ^ 2)) 1 one_ne_zero
      (fun x hx => by simpa using i3_boundary1_deriv x))
theorem gap22 :
    I3 = I3Step1 := by
  exact gap21
theorem gap23 :
    I3 = I3Step2 := by
  have hi2 :
      AntiderivativesOn Set.univ i2Integrand =
        {F | ∃ G ∈ AntiderivativesOn Set.univ i1Integrand,
          ∀ x ∈ Set.univ,
            F x = (2 * x + 1) / (3 * q₃ x) + (2 / 3 : ℝ) * G x} := by
    simpa using
      (antiderivatives_boundary_scale isOpen_univ i2Integrand i1Integrand
        (fun y => (2 * y + 1) / (3 * q₃ y)) (2 / 3 : ℝ)
        (by norm_num) (fun x hx => by simpa using i3_boundary2_deriv x))
  rw [gap21]
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    rw [hi2] at hG
    rcases hG with ⟨H, hH, hGH⟩
    refine ⟨H, hH, ?_⟩
    intro x
    rw [hFG x, hGH x (Set.mem_univ x)]
    ring
  · rintro ⟨H, hH, hFH⟩
    let G := fun x => (2 * x + 1) / (3 * q₃ x) + (2 / 3 : ℝ) * H x
    refine ⟨G, ?_, ?_⟩
    · rw [hi2]
      exact ⟨H, hH, fun x hx => rfl⟩
    · intro x
      simpa [G, add_assoc] using hFH x
theorem gap24 :
    I3 = I3PrimitiveFamily := by
  unfold I3 I3PrimitiveFamily
  apply antiderivatives_eq_translates isOpen_univ isPreconnected_univ
  intro x hx
  have h :=
    (i3_boundary1_deriv x).add
      ((i3_boundary2_deriv x).add
        ((i1Primitive_hasDerivAt x).const_mul (2 / 3 : ℝ)))
  unfold i3Primitive
  convert h using 1
  · funext y
    simp [i1Primitive, Function.comp_def]
    ring
  · ring

end
end ProofGap.Exercise1921
