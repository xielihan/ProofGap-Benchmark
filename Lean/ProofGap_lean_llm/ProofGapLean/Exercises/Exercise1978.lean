import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1978

noncomputable section

def branch : Set ℝ :=
  {x | 0 < x ∧ 0 < x ^ 4 + 2 * x ^ 2 - 1}
def t (x : ℝ) := 1 / x ^ 2
def w (x : ℝ) := 1 - t x
def originalIntegrand (x : ℝ) :=
  1 / (x * Real.sqrt (x ^ 4 + 2 * x ^ 2 - 1))
def tIntegrand (x : ℝ) :=
  deriv t x / Real.sqrt (1 + 2 * t x - t x ^ 2)
def wIntegrand (x : ℝ) :=
  deriv w x / Real.sqrt (2 - w x ^ 2)
def tPrimitive (x : ℝ) :=
  1 / 2 * Real.arcsin ((1 - t x) / Real.sqrt 2)
def xPrimitive (x : ℝ) :=
  1 / 2 *
    Real.arcsin ((x ^ 2 - 1) / (x ^ 2 * Real.sqrt 2))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ScaledFamily (f : ℝ → ℝ) (c : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f, ∀ x ∈ branch, F x = c * G x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem private_isOpen_branch : IsOpen branch := by
  unfold branch
  apply IsOpen.inter
  · exact isOpen_lt continuous_const continuous_id
  · exact isOpen_lt continuous_const
      (((continuous_id.pow 4).add
        (continuous_const.mul (continuous_id.pow 2))).sub continuous_const)

private theorem private_t_pos (x : ℝ) (hx : x ∈ branch) : 0 < t x := by
  unfold t
  exact one_div_pos.mpr (sq_pos_of_pos hx.1)

private theorem private_transformed_identity (x : ℝ) (hx0 : x ≠ 0) :
    1 + 2 * t x - t x ^ 2 =
      (t x) ^ 2 * (x ^ 4 + 2 * x ^ 2 - 1) := by
  unfold t
  field_simp [hx0]

private theorem private_transformed_pos (x : ℝ) (hx : x ∈ branch) :
    0 < 1 + 2 * t x - t x ^ 2 := by
  rw [private_transformed_identity x (ne_of_gt hx.1)]
  exact mul_pos (sq_pos_of_pos (private_t_pos x hx)) hx.2

private theorem private_hasDerivAt_t (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt t (-2 / x ^ 3) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have h := (hasDerivAt_const x (1 : ℝ)).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)
  change HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / x ^ 3) x
  convert h using 1
  · norm_num
    field_simp [hx0] <;> ring

private theorem private_hasDerivAt_w (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt w (2 / x ^ 3) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).sub (private_hasDerivAt_t x hx)
  convert h using 1 <;> simp
  ring

private theorem private_integrand_relation (x : ℝ) (hx : x ∈ branch) :
    tIntegrand x = -2 * originalIntegrand x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have ht0 : t x ≠ 0 := ne_of_gt (private_t_pos x hx)
  have hs0 : Real.sqrt (x ^ 4 + 2 * x ^ 2 - 1) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hx.2
  have hdt := (private_hasDerivAt_t x hx).deriv
  have hsqrt :
      Real.sqrt (1 + 2 * t x - t x ^ 2) =
        t x * Real.sqrt (x ^ 4 + 2 * x ^ 2 - 1) := by
    rw [private_transformed_identity x hx0, Real.sqrt_mul (sq_nonneg (t x))]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (private_t_pos x hx)]
  unfold tIntegrand originalIntegrand
  rw [hdt, hsqrt]
  unfold t
  field_simp [hx0, hs0]

private theorem private_w_integrand_relation (x : ℝ) (hx : x ∈ branch) :
    wIntegrand x = -tIntegrand x := by
  have hdt := (private_hasDerivAt_t x hx).deriv
  have hdw := (private_hasDerivAt_w x hx).deriv
  have hrad : 2 - w x ^ 2 = 1 + 2 * t x - t x ^ 2 := by
    unfold w
    ring
  unfold wIntegrand tIntegrand
  rw [hrad, hdw, hdt]
  ring

private theorem private_hasDerivAt_congr_branch
    {F G : ℝ → ℝ} {d : ℝ} (x : ℝ) (hx : x ∈ branch)
    (hFG : ∀ y ∈ branch, F y = G y) (hG : HasDerivAt G d x) :
    HasDerivAt F d x := by
  apply hG.congr_of_eventuallyEq
  exact (private_isOpen_branch.eventually_mem hx).mono fun y hy => hFG y hy

private theorem private_branch_eq_Ioi :
    branch = Set.Ioi (Real.sqrt (Real.sqrt 2 - 1)) := by
  let a : ℝ := Real.sqrt (Real.sqrt 2 - 1)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by nlinarith
  have hbase : 0 ≤ Real.sqrt 2 - 1 := le_of_lt (sub_pos.mpr hs1)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha_sq : a ^ 2 = Real.sqrt 2 - 1 := by
    dsimp [a]
    exact Real.sq_sqrt hbase
  ext x
  simp only [branch, Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · rintro ⟨hx0, hp⟩
    have hx2 : Real.sqrt 2 - 1 < x ^ 2 := by
      by_contra hn
      have hle : x ^ 2 ≤ Real.sqrt 2 - 1 := le_of_not_gt hn
      have hq0 : 0 ≤ x ^ 2 + 1 := by positivity
      have hqle : x ^ 2 + 1 ≤ Real.sqrt 2 := by linarith
      have hmul : 0 ≤ (Real.sqrt 2 - (x ^ 2 + 1)) *
          (Real.sqrt 2 + (x ^ 2 + 1)) :=
        mul_nonneg (sub_nonneg.mpr hqle) (add_nonneg hs0 hq0)
      nlinarith
    nlinarith
  · intro hax
    have hx0 : 0 < x := lt_of_le_of_lt ha0 hax
    have hmul : 0 < (x - a) * (x + a) :=
      mul_pos (sub_pos.mpr hax) (add_pos_of_pos_of_nonneg hx0 ha0)
    have hx2 : Real.sqrt 2 - 1 < x ^ 2 := by nlinarith
    have hq : Real.sqrt 2 < x ^ 2 + 1 := by linarith
    have hq0 : 0 ≤ x ^ 2 + 1 := by positivity
    have hmul2 : 0 < ((x ^ 2 + 1) - Real.sqrt 2) *
        ((x ^ 2 + 1) + Real.sqrt 2) :=
      mul_pos (sub_pos.mpr hq) (add_pos_of_pos_of_nonneg (by positivity) hs0)
    constructor
    · exact hx0
    · nlinarith

private theorem private_antiderivativesOn_eq_primitive
    (f p : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let a : ℝ := Real.sqrt (Real.sqrt 2 - 1)
    let b : ℝ := a + 1
    have hb : b ∈ branch := by
      rw [private_branch_eq_Ioi]
      simp [a, b]
    let H : ℝ → ℝ := fun y => F y - p y
    have hHd : ∀ x ∈ branch, HasDerivAt H 0 x := by
      intro x hx
      simpa [H] using (hF x hx).sub (hp x hx)
    have hHdiff : DifferentiableOn ℝ H branch := by
      intro x hx
      exact (hHd x hx).differentiableAt.differentiableWithinAt
    have hHderiv : ∀ x ∈ branch, deriv H x = 0 := by
      intro x hx
      exact (hHd x hx).deriv
    have hpre : IsPreconnected branch := by
      rw [private_branch_eq_Ioi]
      exact isPreconnected_Ioi
    have hHconst : ∀ x ∈ branch, ∀ y ∈ branch, H x = H y := by
      intro x hx y hy
      exact private_isOpen_branch.is_const_of_deriv_eq_zero
        hpre hHdiff hHderiv hx hy
    refine ⟨F b - p b, ?_⟩
    intro x hx
    have hconst : H x = H b := hHconst x hx b hb
    dsimp [H] at hconst
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hd : HasDerivAt (fun y => p y + C) (f x) x := (hp x hx).add_const C
    exact private_hasDerivAt_congr_branch x hx hFC hd

private theorem private_hasDerivAt_tPrimitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt tPrimitive ((1 / 2 : ℝ) * wIntegrand x) x := by
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2pos
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hwpos : 0 < 2 - w x ^ 2 := by
    have h := private_transformed_pos x hx
    convert h using 1 <;> unfold w <;> ring
  let u : ℝ := w x / Real.sqrt 2
  have hu_sq : u ^ 2 = w x ^ 2 / 2 := by
    dsimp [u]
    field_simp [hs2ne]
    nlinarith
  have hu2 : u ^ 2 < 1 := by
    rw [hu_sq]
    linarith
  have hu : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg (u - 1), sq_nonneg (u + 1)]
  have hwder := private_hasDerivAt_w x hx
  have huder : HasDerivAt (fun y => w y / Real.sqrt 2)
      ((2 / x ^ 3) / Real.sqrt 2) x := hwder.div_const _
  have harc :=
    (Real.hasDerivAt_arcsin (ne_of_gt hu.1) (ne_of_lt hu.2)).comp x huder
  have hsqrt : Real.sqrt (1 - u ^ 2) =
      Real.sqrt (2 - w x ^ 2) / Real.sqrt 2 := by
    rw [hu_sq]
    have hrewrite : 1 - w x ^ 2 / 2 = (2 - w x ^ 2) / 2 := by ring
    rw [hrewrite, Real.sqrt_div (le_of_lt hwpos)]
  have hfinal := harc.const_mul (1 / 2 : ℝ)
  unfold tPrimitive wIntegrand
  rw [(private_hasDerivAt_w x hx).deriv]
  dsimp [u] at hfinal
  rw [hsqrt] at hfinal
  convert hfinal using 1
  field_simp [hs2ne, Real.sqrt_ne_zero'.mpr hwpos]

private theorem private_scaled_half_w :
    ScaledFamily wIntegrand (1 / 2) =
      AntiderivativesOn (fun x => (1 / 2 : ℝ) * wIntegrand x) := by
  apply Set.ext
  intro F
  simp only [ScaledFamily, AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hd := (hG x hx).const_mul (1 / 2 : ℝ)
    exact private_hasDerivAt_congr_branch x hx hFG hd
  · intro hF
    refine ⟨fun y => (2 : ℝ) * F y, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul (2 : ℝ)
      convert hd using 1 <;> ring
    · intro x hx
      ring

private theorem private_primitives_agree (x : ℝ) (hx : x ∈ branch) :
    tPrimitive x = xPrimitive x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  unfold tPrimitive xPrimitive t
  congr 2
  field_simp [hx0]

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    1 = -1 / (2 * t x * Real.sqrt (t x)) * deriv t x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hdt := (private_hasDerivAt_t x hx).deriv
  have hsqrt : Real.sqrt (t x) = 1 / x := by
    have hpos : 0 < 1 / x := one_div_pos.mpr hx.1
    calc
      Real.sqrt (t x) = Real.sqrt ((1 / x) ^ 2) := by
        congr 1
        simp [t, one_div, pow_two]
      _ = |1 / x| := Real.sqrt_sq_eq_abs _
      _ = 1 / x := abs_of_pos hpos
  rw [hdt, hsqrt]
  simp only [t]
  field_simp [hx0]
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    Real.sqrt (x ^ 4 + 2 * x ^ 2 - 1) =
      Real.sqrt (1 + 2 * t x - t x ^ 2) / t x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have ht : 0 < t x := private_t_pos x hx
  have hrad : 0 ≤ x ^ 4 + 2 * x ^ 2 - 1 := le_of_lt hx.2
  have hid : 1 + 2 * t x - t x ^ 2 = (t x) ^ 2 * (x ^ 4 + 2 * x ^ 2 - 1) :=
    private_transformed_identity x hx0
  have hsqrt :
      Real.sqrt (1 + 2 * t x - t x ^ 2) =
        t x * Real.sqrt (x ^ 4 + 2 * x ^ 2 - 1) := by
    rw [hid, Real.sqrt_mul (sq_nonneg (t x))]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  rw [hsqrt]
  field_simp [ne_of_gt ht]
theorem gap3 :
    AntiderivativesOn originalIntegrand =
      ScaledFamily tIntegrand (-1 / 2) := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, ScaledFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => (-2 : ℝ) * F y, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul (-2 : ℝ)
      simpa [private_integrand_relation x hx] using hd
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hd := (hG x hx).const_mul (-1 / 2 : ℝ)
    have hcoef : (-1 / 2 : ℝ) * tIntegrand x = originalIntegrand x := by
      rw [private_integrand_relation x hx]
      ring
    rw [hcoef] at hd
    exact private_hasDerivAt_congr_branch x hx hFG hd
theorem gap4 :
    ScaledFamily tIntegrand (-1 / 2) =
      ScaledFamily wIntegrand (1 / 2) := by
  apply Set.ext
  intro F
  simp only [ScaledFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => -G y, ?_, ?_⟩
    · intro x hx
      have hd := (hG x hx).neg
      simpa [private_w_integrand_relation x hx] using hd
    · intro x hx
      specialize hFG x hx
      rw [hFG]
      ring
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => -G y, ?_, ?_⟩
    · intro x hx
      have hd := (hG x hx).neg
      simpa [private_w_integrand_relation x hx] using hd
    · intro x hx
      specialize hFG x hx
      rw [hFG]
      ring
theorem gap5 :
    ScaledFamily wIntegrand (1 / 2) =
      PrimitiveFamily tPrimitive := by
  rw [private_scaled_half_w]
  apply private_antiderivativesOn_eq_primitive
  intro x hx
  exact private_hasDerivAt_tPrimitive x hx
theorem gap6 :
    AntiderivativesOn originalIntegrand =
      PrimitiveFamily tPrimitive := by
  rw [gap3, gap4, gap5]
theorem gap7 :
    AntiderivativesOn originalIntegrand =
      PrimitiveFamily xPrimitive := by
  rw [gap6]
  apply Set.ext
  intro F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, private_primitives_agree x hx]
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, private_primitives_agree x hx]

end
end ProofGap.Exercise1978
