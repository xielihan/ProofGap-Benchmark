import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2157

noncomputable section

def xBranch : Set ℝ := Set.Ioo (-1) 1
def tBranch : Set ℝ := Set.Ioo (-Real.pi / 4) (Real.pi / 4)
def tOf (x : ℝ) := Real.arctan x
def sec (t : ℝ) := 1 / Real.cos t
def AntiderivativesX (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ xBranch, HasDerivAt F (f x) x}
def AntiderivativesT (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ t ∈ tBranch, HasDerivAt F (f t) t}
def PrimitiveFamilyX (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ xBranch, F x = p x + C}
def PrimitiveFamilyT (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ t ∈ tBranch, F t = p t + C}
def PullbackFamily (A : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ A, ∀ x ∈ xBranch, F x = G (tOf x)}
def l (x : ℝ) := Real.log (x + Real.sqrt (1 + x ^ 2))
def integrand (x : ℝ) := x * l x / (1 - x ^ 2) ^ 2
def InitialFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x ∈ xBranch,
      HasDerivAt G
        (l x * deriv (fun y : ℝ => 1 / (1 - y ^ 2)) x) x) ∧
    ∀ x ∈ xBranch, F x = 1 / 2 * G x}
def residual (x : ℝ) := 1 / ((1 - x ^ 2) * Real.sqrt (1 + x ^ 2))
def ReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesX residual,
    ∀ x ∈ xBranch,
      F x = l x / (2 * (1 - x ^ 2)) - 1 / 2 * G x}
def parameterIntegrand₁ (t : ℝ) :=
  sec t / (1 - Real.tan t ^ 2)
def parameterIntegrand₂ (t : ℝ) :=
  Real.cos t / (Real.cos t ^ 2 - Real.sin t ^ 2)
def parameterIntegrand₃ (t : ℝ) :=
  deriv Real.sin t / (1 - 2 * Real.sin t ^ 2)
def primitiveT (t : ℝ) :=
  1 / (2 * Real.sqrt 2) *
    Real.log |(1 + Real.sqrt 2 * Real.sin t) /
      (1 - Real.sqrt 2 * Real.sin t)|
def residualPrimitive (x : ℝ) :=
  1 / (2 * Real.sqrt 2) *
    Real.log |(Real.sqrt (1 + x ^ 2) + x * Real.sqrt 2) /
      (Real.sqrt (1 + x ^ 2) - x * Real.sqrt 2)|
def primitive (x : ℝ) :=
  l x / (2 * (1 - x ^ 2)) +
    1 / (4 * Real.sqrt 2) *
      Real.log |(Real.sqrt (1 + x ^ 2) - x * Real.sqrt 2) /
        (Real.sqrt (1 + x ^ 2) + x * Real.sqrt 2)|

private theorem one_sub_sq_pos {x : ℝ} (hx : x ∈ xBranch) :
    0 < 1 - x ^ 2 := by
  change -1 < x ∧ x < 1 at hx
  calc
    0 < (1 - x) * (1 + x) := mul_pos (by linarith) (by linarith)
    _ = 1 - x ^ 2 := by ring

private theorem t_mem_tanBranch (t : ℝ) (ht : t ∈ tBranch) :
    t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  unfold tBranch at ht
  have hq : Real.pi / 4 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hnegq : -(Real.pi / 2) < -Real.pi / 4 := by
    convert (neg_lt_neg hq) using 1 <;> ring
  exact ⟨lt_trans hnegq ht.1, lt_trans ht.2 hq⟩

private theorem tan_mem_xBranch_of_mem_tBranch (t : ℝ) (ht : t ∈ tBranch) :
    Real.tan t ∈ xBranch := by
  have ht' := t_mem_tanBranch t ht
  have hn : -Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hp : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hnegarg : -Real.pi / 4 = -(Real.pi / 4) := by ring
  have htan_neg : Real.tan (-Real.pi / 4) = -1 := by
    calc
      Real.tan (-Real.pi / 4) = Real.tan (-(Real.pi / 4)) :=
        congrArg Real.tan hnegarg
      _ = -Real.tan (Real.pi / 4) := Real.tan_neg _
      _ = -1 := by rw [Real.tan_pi_div_four]
  have htan_pos : Real.tan (Real.pi / 4) = 1 := Real.tan_pi_div_four
  unfold xBranch
  constructor
  · rw [← htan_neg]
    exact Real.strictMonoOn_tan hn ht' ht.1
  · rw [← htan_pos]
    exact Real.strictMonoOn_tan ht' hp ht.2

private theorem arctan_mem_tBranch (x : ℝ) (hx : x ∈ xBranch) :
    tOf x ∈ tBranch := by
  have hn : -Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hp : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have ha : Real.arctan x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_lt_arctan x, Real.arctan_lt_pi_div_two x⟩
  have hnegarg : -Real.pi / 4 = -(Real.pi / 4) := by ring
  have htan_neg : Real.tan (-Real.pi / 4) = -1 := by
    calc
      Real.tan (-Real.pi / 4) = Real.tan (-(Real.pi / 4)) :=
        congrArg Real.tan hnegarg
      _ = -Real.tan (Real.pi / 4) := Real.tan_neg _
      _ = -1 := by rw [Real.tan_pi_div_four]
  have htan_pos : Real.tan (Real.pi / 4) = 1 := Real.tan_pi_div_four
  unfold tOf tBranch
  constructor
  · by_contra h
    have hle : Real.arctan x ≤ -Real.pi / 4 := le_of_not_gt h
    have hm := Real.strictMonoOn_tan.monotoneOn ha hn hle
    rw [Real.tan_arctan, htan_neg] at hm
    exact (not_le_of_gt hx.1) hm
  · by_contra h
    have hle : Real.pi / 4 ≤ Real.arctan x := le_of_not_gt h
    have hm := Real.strictMonoOn_tan.monotoneOn hp ha hle
    rw [htan_pos, Real.tan_arctan] at hm
    exact (not_le_of_gt hx.2) hm

private theorem sqrt_two_mul_sin_bounds (t : ℝ) (ht : t ∈ tBranch) :
    -(1 : ℝ) < Real.sqrt 2 * Real.sin t ∧
      Real.sqrt 2 * Real.sin t < 1 := by
  have ht' := t_mem_tanBranch t ht
  have htm : t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨le_of_lt ht'.1, le_of_lt ht'.2⟩
  have hn : -Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hp : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hleft := Real.strictMonoOn_sin hn htm ht.1
  have hright := Real.strictMonoOn_sin htm hp ht.2
  have hnegarg : -Real.pi / 4 = -(Real.pi / 4) := by ring
  have hsin_neg :
      Real.sin (-Real.pi / 4) = -Real.sin (Real.pi / 4) := by
    calc
      Real.sin (-Real.pi / 4) = Real.sin (-(Real.pi / 4)) :=
        congrArg Real.sin hnegarg
      _ = -Real.sin (Real.pi / 4) := Real.sin_neg _
  rw [hsin_neg, Real.sin_pi_div_four] at hleft
  rw [Real.sin_pi_div_four] at hright
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hleft' := mul_lt_mul_of_pos_left hleft hs2
  have hright' := mul_lt_mul_of_pos_left hright hs2
  constructor
  · nlinarith [hleft']
  · nlinarith [hright']

private theorem hasDerivAt_l (x : ℝ) :
    HasDerivAt l (1 / Real.sqrt (1 + x ^ 2)) x := by
  have hu : 0 < 1 + x ^ 2 := by positivity
  have hs0 : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x hinner using 1 <;>
      simp [id_eq] <;> field_simp [hs0] <;> ring
  have hsum : HasDerivAt
      (fun y : ℝ => y + Real.sqrt (1 + y ^ 2))
      (1 + x / Real.sqrt (1 + x ^ 2)) x := by
    convert (hasDerivAt_id x).add hs using 1 <;> simp [id_eq] <;> ring
  have ha : 0 < x + Real.sqrt (1 + x ^ 2) := by
    have hsquare := Real.sq_sqrt (le_of_lt hu)
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
  unfold l
  convert (Real.hasDerivAt_log (ne_of_gt ha)).comp x hsum using 1
  have hsquare := Real.sq_sqrt (le_of_lt hu)
  field_simp [ne_of_gt ha, hs0]
  nlinarith

private theorem eq_add_const_on_Ioo
    {f g q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (q x) x)
    (hg : ∀ x ∈ Set.Ioo a b, HasDerivAt g (q x) x) :
    ∃ C : ℝ, ∀ x ∈ Set.Ioo a b, f x = g x + C := by
  let z := (a + b) / 2
  have hz : z ∈ Set.Ioo a b := by
    dsimp [z]
    constructor <;> linarith
  have hd : DifferentiableOn ℝ (f - g) (Set.Ioo a b) := by
    intro x hx
    exact ((hf x hx).sub (hg x hx)).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ Set.Ioo a b, deriv (f - g) x = 0 := by
    intro x hx
    simpa using ((hf x hx).sub (hg x hx)).deriv
  refine ⟨f z - g z, fun x hx => ?_⟩
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero
    isPreconnected_Ioo hd hzero hx hz
  change f x - g x = f z - g z at hc
  linarith

private theorem hasDerivAt_primitiveT (t : ℝ) (ht : t ∈ tBranch) :
    HasDerivAt primitiveT (parameterIntegrand₃ t) t := by
  unfold primitiveT parameterIntegrand₃
  rw [(Real.hasDerivAt_sin t).deriv]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hbounds := sqrt_two_mul_sin_bounds t ht
  have hp : 0 < 1 + Real.sqrt 2 * Real.sin t := by linarith
  have hm : 0 < 1 - Real.sqrt 2 * Real.sin t := by linarith
  have hratio : 0 < (1 + Real.sqrt 2 * Real.sin t) /
      (1 - Real.sqrt 2 * Real.sin t) := div_pos hp hm
  have hnum := (hasDerivAt_const t (1 : ℝ)).add
    ((hasDerivAt_const t (Real.sqrt 2)).mul (Real.hasDerivAt_sin t))
  have hden := (hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_const t (Real.sqrt 2)).mul (Real.hasDerivAt_sin t))
  have hquot := hnum.div hden (ne_of_gt hm)
  have habsRaw := (hasDerivAt_abs (ne_of_gt hratio)).comp t hquot
  have habs : HasDerivAt
      (fun y => |(1 + Real.sqrt 2 * Real.sin y) /
        (1 - Real.sqrt 2 * Real.sin y)|)
      (((Real.sqrt 2 * Real.cos t) * (1 - Real.sqrt 2 * Real.sin t) -
          (1 + Real.sqrt 2 * Real.sin t) * (-Real.sqrt 2 * Real.cos t)) /
        (1 - Real.sqrt 2 * Real.sin t) ^ 2) t := by
    convert habsRaw using 1 <;> simp [hratio] <;> ring
  have hlog := (Real.hasDerivAt_log
    (abs_ne_zero.mpr (div_ne_zero (ne_of_gt hp) (ne_of_gt hm)))).comp t habs
  rw [abs_of_pos hratio] at hlog
  have hdenprod :
      (1 + Real.sqrt 2 * Real.sin t) *
        (1 - Real.sqrt 2 * Real.sin t) =
      1 - 2 * Real.sin t ^ 2 := by
    calc
      (1 + Real.sqrt 2 * Real.sin t) *
          (1 - Real.sqrt 2 * Real.sin t) =
        1 - (Real.sqrt 2) ^ 2 * Real.sin t ^ 2 := by ring
      _ = 1 - 2 * Real.sin t ^ 2 := by rw [hs2sq]
  have halg :
      1 / (2 * Real.sqrt 2) *
          (((1 + Real.sqrt 2 * Real.sin t) /
              (1 - Real.sqrt 2 * Real.sin t))⁻¹ *
            ((Real.sqrt 2 * Real.cos t *
                (1 - Real.sqrt 2 * Real.sin t) -
              (1 + Real.sqrt 2 * Real.sin t) *
                (-Real.sqrt 2 * Real.cos t)) /
              (1 - Real.sqrt 2 * Real.sin t) ^ 2)) =
        Real.cos t / (1 - 2 * Real.sin t ^ 2) := by
    rw [← hdenprod]
    field_simp [ne_of_gt hp, ne_of_gt hm, ne_of_gt hs2]
    ring
  convert hlog.const_mul (1 / (2 * Real.sqrt 2)) using 1
  exact halg.symm

private theorem parameterIntegrand_one_eq_two (t : ℝ) (ht : t ∈ tBranch) :
    parameterIntegrand₁ t = parameterIntegrand₂ t := by
  have ht' := t_mem_tanBranch t ht
  have hc : Real.cos t ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ht')
  have htan := tan_mem_xBranch_of_mem_tBranch t ht
  have hne : 1 - Real.tan t ^ 2 ≠ 0 :=
    ne_of_gt (one_sub_sq_pos htan)
  have htanEq := Real.tan_eq_sin_div_cos t
  have hsin : Real.sin t = Real.tan t * Real.cos t := by
    rw [htanEq]
    field_simp [hc]
  have hcs : 0 < Real.cos t ^ 2 - Real.sin t ^ 2 := by
    rw [hsin]
    have hc2 : 0 < Real.cos t ^ 2 := sq_pos_of_ne_zero hc
    nlinarith [one_sub_sq_pos htan]
  unfold parameterIntegrand₁ parameterIntegrand₂ sec
  rw [htanEq]
  field_simp [hc, hne, ne_of_gt hcs]

private theorem primitiveT_arctan (x : ℝ) (hx : x ∈ xBranch) :
    primitiveT (tOf x) = residualPrimitive x := by
  unfold primitiveT residualPrimitive tOf
  rw [Real.sin_arctan]
  have hs : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity
  congr 2
  field_simp [hs]

private theorem primitive_eq_reduction (x : ℝ) (hx : x ∈ xBranch) :
    primitive x = l x / (2 * (1 - x ^ 2)) - 1 / 2 * residualPrimitive x := by
  unfold primitive residualPrimitive
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsnonneg := Real.sqrt_nonneg (1 + x ^ 2)
  have hxpos := one_sub_sq_pos hx
  have habsq : (x * Real.sqrt 2) ^ 2 <
      (Real.sqrt (1 + x ^ 2)) ^ 2 := by
    nlinarith
  have hp : 0 < Real.sqrt (1 + x ^ 2) + x * Real.sqrt 2 := by
    nlinarith [sq_nonneg (Real.sqrt (1 + x ^ 2) - x * Real.sqrt 2)]
  have hm : 0 < Real.sqrt (1 + x ^ 2) - x * Real.sqrt 2 := by
    nlinarith [sq_nonneg (Real.sqrt (1 + x ^ 2) + x * Real.sqrt 2)]
  rw [abs_of_pos (div_pos hm hp), abs_of_pos (div_pos hp hm)]
  rw [Real.log_div (ne_of_gt hm) (ne_of_gt hp),
    Real.log_div (ne_of_gt hp) (ne_of_gt hm)]
  ring

theorem gap1 :
    AntiderivativesX integrand = InitialFamily := by
  apply Set.Subset.antisymm
  · intro F hF
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · intro x hx
      have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos hx)
      have hd : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
        convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
          simp [id_eq] <;> ring
      have hinv := hd.inv hne
      change HasDerivAt (fun y : ℝ => (1 - y ^ 2)⁻¹)
        (-(-2 * x) / (1 - x ^ 2) ^ 2) x at hinv
      have hcoeff :
          -(-2 * x) / (1 - x ^ 2) ^ 2 =
            2 * x / (1 - x ^ 2) ^ 2 := by
        ring
      rw [hcoeff] at hinv
      have hr : HasDerivAt (fun y : ℝ => 1 / (1 - y ^ 2))
          (2 * x / (1 - x ^ 2) ^ 2) x := by
        simpa only [one_div] using hinv
      convert (hF x hx).const_mul 2 using 1
      rw [hr.deriv]
      unfold integrand
      ring
    · intro x hx
      ring
  · intro F hF
    rcases hF with ⟨G, hG, hFG⟩
    intro x hx
    have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos hx)
    have hd : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
        simp [id_eq] <;> ring
    have hinv := hd.inv hne
    change HasDerivAt (fun y : ℝ => (1 - y ^ 2)⁻¹)
      (-(-2 * x) / (1 - x ^ 2) ^ 2) x at hinv
    have hcoeff :
        -(-2 * x) / (1 - x ^ 2) ^ 2 =
          2 * x / (1 - x ^ 2) ^ 2 := by
      ring
    rw [hcoeff] at hinv
    have hr : HasDerivAt (fun y : ℝ => 1 / (1 - y ^ 2))
        (2 * x / (1 - x ^ 2) ^ 2) x := by
      simpa only [one_div] using hinv
    have hG' := (hG x hx).const_mul (1 / 2)
    have hG'' : HasDerivAt (fun y => 1 / 2 * G y) (integrand x) x := by
      convert hG' using 1
      rw [hr.deriv]
      unfold integrand
      ring
    have hlocal : F =ᶠ[nhds x] (fun y => 1 / 2 * G y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hFG y hy
    exact hG''.congr_of_eventuallyEq hlocal
theorem gap2 :
    AntiderivativesX integrand = ReductionFamily := by
  apply Set.Subset.antisymm
  · intro F hF
    refine ⟨fun x => 2 * (l x / (2 * (1 - x ^ 2)) - F x), ?_, ?_⟩
    · intro x hx
      have hl := hasDerivAt_l x
      have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos hx)
      have hi : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
        convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
          simp [id_eq] <;> ring
      have hq : HasDerivAt (fun y : ℝ => 2 * (1 - y ^ 2)) (-4 * x) x := by
        convert hi.const_mul 2 using 1 <;> simp [id_eq] <;> ring
      have hmain : HasDerivAt (fun y => l y / (2 * (1 - y ^ 2)))
          (integrand x + 1 / 2 * residual x) x := by
        convert hl.div hq (mul_ne_zero (by norm_num) hne) using 1 <;>
          unfold integrand residual <;>
          field_simp [hne, Real.sqrt_ne_zero'.mpr (by positivity : 0 < 1 + x ^ 2)] <;>
          ring
      convert (hmain.sub (hF x hx)).const_mul 2 using 1 <;>
        unfold residual <;> ring
    · intro x hx
      ring
  · intro F hF
    rcases hF with ⟨G, hG, hFG⟩
    intro x hx
    have hl := hasDerivAt_l x
    have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos hx)
    have hi : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
        simp [id_eq] <;> ring
    have hq : HasDerivAt (fun y : ℝ => 2 * (1 - y ^ 2)) (-4 * x) x := by
      convert hi.const_mul 2 using 1 <;> simp [id_eq] <;> ring
    have hmain : HasDerivAt (fun y => l y / (2 * (1 - y ^ 2)))
        (integrand x + 1 / 2 * residual x) x := by
      convert hl.div hq (mul_ne_zero (by norm_num) hne) using 1 <;>
        unfold integrand residual <;>
        field_simp [hne, Real.sqrt_ne_zero'.mpr (by positivity : 0 < 1 + x ^ 2)] <;>
        ring
    have hcandidate := hmain.sub ((hG x hx).const_mul (1 / 2))
    have hcandidate' : HasDerivAt
        (fun y => l y / (2 * (1 - y ^ 2)) - 1 / 2 * G y)
        (integrand x) x := by
      convert hcandidate using 1 <;> ring
    have hlocal : F =ᶠ[nhds x]
        (fun y => l y / (2 * (1 - y ^ 2)) - 1 / 2 * G y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hFG y hy
    exact hcandidate'.congr_of_eventuallyEq hlocal
theorem gap3 (x : ℝ) (hx : x ∈ xBranch) :
    Real.sqrt (1 + x ^ 2) = sec (tOf x) := by
  unfold sec tOf
  rw [Real.cos_arctan]
  have hs : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity
  field_simp
theorem gap4 (x : ℝ) (hx : x ∈ xBranch) :
    deriv Real.tan (tOf x) = sec (tOf x) ^ 2 := by
  have hc : Real.cos (tOf x) ≠ 0 := by
    unfold tOf
    rw [Real.cos_arctan]
    positivity
  simpa [sec] using (Real.hasDerivAt_tan hc).deriv
theorem gap5 :
    AntiderivativesX residual =
      PullbackFamily (AntiderivativesT parameterIntegrand₁) := by
  apply Set.Subset.antisymm
  · intro F hF
    refine ⟨fun t => F (Real.tan t), ?_, ?_⟩
    · intro t ht
      have ht' := t_mem_tanBranch t ht
      have hc : Real.cos t ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ht')
      have htan : Real.tan t ∈ xBranch := tan_mem_xBranch_of_mem_tBranch t ht
      have hne : 1 - Real.tan t ^ 2 ≠ 0 :=
        ne_of_gt (one_sub_sq_pos htan)
      have hder := (hF (Real.tan t) htan).comp t (Real.hasDerivAt_tan hc)
      change HasDerivAt (fun s => F (Real.tan s)) _ t at hder
      convert hder using 1
      unfold residual parameterIntegrand₁
      rw [gap3 (Real.tan t) htan]
      have hat : tOf (Real.tan t) = t := by
        unfold tOf
        exact Real.arctan_tan ht'.1 ht'.2
      rw [hat]
      unfold sec
      field_simp [hc, hne]
    · intro x hx
      change F x = F (Real.tan (Real.arctan x))
      rw [Real.tan_arctan]
  · intro F hF
    rcases hF with ⟨G, hG, hFG⟩
    intro x hx
    have ha := Real.hasDerivAt_arctan x
    have hcomp := (hG (tOf x) (arctan_mem_tBranch x hx)).comp x ha
    change HasDerivAt (fun y => G (tOf y)) _ x at hcomp
    have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos hx)
    have hs : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity
    have hu : 1 + x ^ 2 ≠ 0 := by positivity
    have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)
    have htan_tOf : Real.tan (tOf x) = x := by
      unfold tOf
      exact Real.tan_arctan x
    have hcomp' : HasDerivAt (fun y => G (tOf y)) (residual x) x := by
      convert hcomp using 1
      unfold parameterIntegrand₁ residual
      rw [← gap3 x hx, htan_tOf]
      field_simp [hne, hs, hu] <;> nlinarith [hsquare]
    have hlocal : F =ᶠ[nhds x] (fun y => G (tOf y)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hFG y hy
    exact hcomp'.congr_of_eventuallyEq hlocal
theorem gap6 :
    AntiderivativesT parameterIntegrand₁ =
      AntiderivativesT parameterIntegrand₂ := by
  apply Set.ext
  intro F
  simp only [AntiderivativesT, Set.mem_setOf_eq]
  constructor <;> intro h t ht
  · simpa [parameterIntegrand_one_eq_two t ht] using h t ht
  · simpa [parameterIntegrand_one_eq_two t ht] using h t ht
theorem gap7 :
    AntiderivativesT parameterIntegrand₂ =
      AntiderivativesT parameterIntegrand₃ := by
  apply Set.ext
  intro F
  simp only [AntiderivativesT, Set.mem_setOf_eq]
  constructor <;> intro h t ht
  · have hden : Real.cos t ^ 2 - Real.sin t ^ 2 =
        1 - 2 * Real.sin t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    simpa [parameterIntegrand₂, parameterIntegrand₃,
      (Real.hasDerivAt_sin t).deriv, hden] using h t ht
  · have hden : Real.cos t ^ 2 - Real.sin t ^ 2 =
        1 - 2 * Real.sin t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    simpa [parameterIntegrand₂, parameterIntegrand₃,
      (Real.hasDerivAt_sin t).deriv, hden] using h t ht
theorem gap8 :
    AntiderivativesT parameterIntegrand₃ =
      PrimitiveFamilyT primitiveT := by
  apply Set.Subset.antisymm
  · intro F hF
    rcases eq_add_const_on_Ioo (a := -Real.pi / 4) (b := Real.pi / 4)
      (f := F) (g := primitiveT) (q := parameterIntegrand₃)
      (by nlinarith [Real.pi_pos]) hF hasDerivAt_primitiveT with ⟨C, hC⟩
    exact ⟨C, hC⟩
  · intro F hF
    rcases hF with ⟨C, hFC⟩
    intro t ht
    have hc := (hasDerivAt_primitiveT t ht).const_add C
    have hlocal : F =ᶠ[nhds t] (fun y => C + primitiveT y) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
      simpa [add_comm] using hFC y hy
    exact hc.congr_of_eventuallyEq hlocal
theorem gap9 :
    AntiderivativesX residual =
      PullbackFamily (PrimitiveFamilyT primitiveT) := by
  calc
    AntiderivativesX residual = PullbackFamily (AntiderivativesT parameterIntegrand₁) := gap5
    _ = PullbackFamily (AntiderivativesT parameterIntegrand₂) := congrArg PullbackFamily gap6
    _ = PullbackFamily (AntiderivativesT parameterIntegrand₃) := congrArg PullbackFamily gap7
    _ = PullbackFamily (PrimitiveFamilyT primitiveT) := congrArg PullbackFamily gap8
theorem gap10 :
    AntiderivativesX residual = PrimitiveFamilyX residualPrimitive := by
  rw [gap9]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨G, ⟨C, hG⟩, hF⟩
    refine ⟨C, fun x hx => ?_⟩
    rw [hF x hx, hG (tOf x) (arctan_mem_tBranch x hx)]
    rw [primitiveT_arctan x hx]
  · rintro ⟨C, hF⟩
    refine ⟨fun t => primitiveT t + C, ⟨C, fun t ht => rfl⟩, fun x hx => ?_⟩
    rw [hF x hx]
    change residualPrimitive x + C = primitiveT (tOf x) + C
    rw [primitiveT_arctan x hx]
theorem gap11 :
    AntiderivativesX integrand = PrimitiveFamilyX primitive := by
  rw [gap2]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨G, hG, hF⟩
    have hGP : G ∈ PrimitiveFamilyX residualPrimitive := by
      rw [← gap10]
      exact hG
    rcases hGP with ⟨C, hGC⟩
    refine ⟨-(1 / 2) * C, fun x hx => ?_⟩
    rw [hF x hx, hGC x hx, primitive_eq_reduction x hx]
    ring
  · rintro ⟨C, hF⟩
    let G : ℝ → ℝ := fun x => residualPrimitive x - 2 * C
    have hGP : G ∈ PrimitiveFamilyX residualPrimitive := by
      refine ⟨-2 * C, fun x hx => ?_⟩
      dsimp [G]
      ring
    have hGA : G ∈ AntiderivativesX residual := by
      rw [gap10]
      exact hGP
    refine ⟨G, hGA, fun x hx => ?_⟩
    rw [hF x hx, primitive_eq_reduction x hx]
    dsimp [G]
    ring

end
end ProofGap.Exercise2157
