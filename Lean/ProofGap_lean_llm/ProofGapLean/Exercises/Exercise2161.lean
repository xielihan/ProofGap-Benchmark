import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2161

noncomputable section

def branch : Set ℝ := Set.Iio 0
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def integrand (x : ℝ) := Real.arcsin (Real.exp x) / Real.exp x
def FirstReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ H ∈ AntiderivativesOn
      (fun x => 1 / Real.sqrt (1 - Real.exp (2 * x))),
    ∀ x ∈ branch,
      F x = -Real.exp (-x) * Real.arcsin (Real.exp x) + H x}
def SecondReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt G
          (deriv (fun y : ℝ => Real.exp (-y)) x /
            Real.sqrt ((Real.exp (-x)) ^ 2 - 1)) x) ∧
    ∀ x ∈ branch,
      F x = -Real.exp (-x) * Real.arcsin (Real.exp x) - G x}
def primitiveRaw (x : ℝ) :=
  -Real.exp (-x) * Real.arcsin (Real.exp x) -
    Real.log (Real.exp (-x) + Real.sqrt (Real.exp (-2 * x) - 1))
def primitive (x : ℝ) :=
  x - Real.exp (-x) * Real.arcsin (Real.exp x) -
    Real.log (1 + Real.sqrt (1 - Real.exp (2 * x)))

private def mainTerm (x : ℝ) :=
  -Real.exp (-x) * Real.arcsin (Real.exp x)

private def reducedTerm (x : ℝ) :=
  1 / Real.sqrt (1 - Real.exp (2 * x))

private def auxiliaryRate (x : ℝ) :=
  deriv (fun y : ℝ => Real.exp (-y)) x /
    Real.sqrt ((Real.exp (-x)) ^ 2 - 1)

private def logarithmicTerm (x : ℝ) :=
  Real.log (Real.exp (-x) +
    Real.sqrt ((Real.exp (-x)) ^ 2 - 1))

private lemma branch_exp_facts (x : ℝ) (hx : x ∈ branch) :
    Real.exp x ∈ Set.Ioo (-1 : ℝ) 1 ∧
      0 < 1 - Real.exp (2 * x) := by
  have hx0 : x < 0 := by simpa [branch] using hx
  have hepos : 0 < Real.exp x := Real.exp_pos x
  have helt : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx0
  have h2x : 2 * x < 0 := by linarith
  refine ⟨⟨by linarith, helt⟩, ?_⟩
  have h := Real.exp_lt_one_iff.mpr h2x
  linarith

private lemma hasDerivAt_mainTerm (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt mainTerm (integrand x - reducedTerm x) x := by
  obtain ⟨hexp_mem, hrad⟩ := branch_exp_facts x hx
  have hnegexp :
      HasDerivAt (fun y : ℝ => -Real.exp (-y)) (Real.exp (-x)) x := by
    convert ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).neg using 1 <;>
      ring
  have hasin :=
    (Real.hasDerivAt_arcsin (ne_of_gt hexp_mem.1) (ne_of_lt hexp_mem.2)).comp
      x (Real.hasDerivAt_exp x)
  have hd := hnegexp.mul hasin
  have hexp2 : Real.exp (2 * x) = (Real.exp x) ^ 2 := by
    rw [show 2 * x = x + x by ring, Real.exp_add, pow_two]
  have hsqrt : 0 < Real.sqrt (1 - Real.exp (2 * x)) :=
    Real.sqrt_pos.2 hrad
  convert hd using 1
  dsimp [mainTerm, integrand, reducedTerm]
  rw [hexp2, Real.exp_neg]
  field_simp [Real.exp_ne_zero, hsqrt.ne'] <;> ring

private lemma sqrt_scaled (x : ℝ) :
    Real.sqrt ((Real.exp (-x)) ^ 2 - 1) =
      Real.exp (-x) * Real.sqrt (1 - Real.exp (2 * x)) := by
  have hpair : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp2 : Real.exp (2 * x) = (Real.exp x) ^ 2 := by
    rw [show 2 * x = x + x by ring, Real.exp_add, pow_two]
  have hprod : (Real.exp (-x)) ^ 2 * Real.exp (2 * x) = 1 := by
    rw [hexp2]
    calc
      (Real.exp (-x)) ^ 2 * (Real.exp x) ^ 2 =
          (Real.exp (-x) * Real.exp x) ^ 2 := by ring
      _ = 1 := by rw [hpair]; norm_num
  have hid :
      (Real.exp (-x)) ^ 2 - 1 =
        (Real.exp (-x)) ^ 2 * (1 - Real.exp (2 * x)) := by
    nlinarith
  calc
    Real.sqrt ((Real.exp (-x)) ^ 2 - 1) =
        Real.sqrt ((Real.exp (-x)) ^ 2 * (1 - Real.exp (2 * x))) := by
      rw [hid]
    _ = Real.sqrt ((Real.exp (-x)) ^ 2) *
        Real.sqrt (1 - Real.exp (2 * x)) := by
      exact Real.sqrt_mul (sq_nonneg (Real.exp (-x)))
        (1 - Real.exp (2 * x))
    _ = Real.exp (-x) * Real.sqrt (1 - Real.exp (2 * x)) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos (-x))]

private lemma auxiliaryRate_eq (x : ℝ) (hx : x ∈ branch) :
    auxiliaryRate x = -reducedTerm x := by
  obtain ⟨_, hrad⟩ := branch_exp_facts x hx
  have hu : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x) using 1 <;>
      ring
  have hdu : deriv (fun y : ℝ => Real.exp (-y)) x = -Real.exp (-x) := hu.deriv
  have hsqrt : 0 < Real.sqrt (1 - Real.exp (2 * x)) :=
    Real.sqrt_pos.2 hrad
  rw [auxiliaryRate, reducedTerm, hdu, sqrt_scaled x]
  field_simp [Real.exp_ne_zero, hsqrt.ne']

private lemma hasDerivAt_logarithmicTerm (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt logarithmicTerm (auxiliaryRate x) x := by
  have hx0 : x < 0 := by simpa [branch] using hx
  have hu_gt : 1 < Real.exp (-x) :=
    Real.one_lt_exp_iff.mpr (by linarith)
  have hzpos : 0 < (Real.exp (-x)) ^ 2 - 1 := by nlinarith
  have hvpos : 0 < Real.sqrt ((Real.exp (-x)) ^ 2 - 1) :=
    Real.sqrt_pos.2 hzpos
  have hsumpos :
      0 < Real.exp (-x) + Real.sqrt ((Real.exp (-x)) ^ 2 - 1) := by
    positivity
  have hu : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x) using 1 <;>
      ring
  have hz := (hu.pow 2).sub_const 1
  have hv := (Real.hasDerivAt_sqrt hzpos.ne').comp x hz
  have hs := hu.add hv
  have hl := (Real.hasDerivAt_log hsumpos.ne').comp x hs
  have hv_sq :
      (Real.sqrt ((Real.exp (-x)) ^ 2 - 1)) ^ 2 =
        (Real.exp (-x)) ^ 2 - 1 :=
    Real.sq_sqrt (le_of_lt hzpos)
  have hdu : deriv (fun y : ℝ => Real.exp (-y)) x = -Real.exp (-x) := hu.deriv
  rw [auxiliaryRate, hdu]
  have hl' : HasDerivAt logarithmicTerm
      ((-Real.exp (-x) +
          (1 / (2 * Real.sqrt ((Real.exp (-x)) ^ 2 - 1))) *
            (2 * Real.exp (-x) * (-Real.exp (-x)))) /
        (Real.exp (-x) + Real.sqrt ((Real.exp (-x)) ^ 2 - 1))) x := by
    convert hl using 1 <;> dsimp [logarithmicTerm] <;> ring
  convert hl' using 1
  field_simp [hvpos.ne', hsumpos.ne']
  nlinarith

private lemma hasDerivAt_primitiveRaw (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveRaw (integrand x) x := by
  have hd := (hasDerivAt_mainTerm x hx).sub
    (hasDerivAt_logarithmicTerm x hx)
  rw [auxiliaryRate_eq x hx] at hd
  have hfun : primitiveRaw = mainTerm - logarithmicTerm := by
    funext y
    have he : Real.exp (-2 * y) = (Real.exp (-y)) ^ 2 := by
      rw [show -2 * y = (-y) + (-y) by ring, Real.exp_add, pow_two]
    dsimp [primitiveRaw, mainTerm, logarithmicTerm]
    rw [he]
  rw [hfun]
  convert hd using 1 <;> ring

private lemma hasDerivAt_of_eq_on_branch
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ branch)
    (hfg : ∀ y ∈ branch, f y = g y) (hg : HasDerivAt g f' x) :
    HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds
      (show x ∈ Set.Iio (0 : ℝ) by simpa [branch] using hx)] with y hy
  exact hfg y (by simpa [branch] using hy)

private theorem antiderivatives_eq_primitive
    {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (f x) x at hF
    change F ∈ PrimitiveFamily p
    refine ⟨F (-1) - p (-1), ?_⟩
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) (Set.Iio 0) := by
      intro y hy
      exact ((hF y (by simpa [branch] using hy)).sub
        (hp y (by simpa [branch] using hy))).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ Set.Iio (0 : ℝ),
        deriv (fun z => F z - p z) y = 0 := by
      intro y hy
      have hd := (hF y (by simpa [branch] using hy)).sub
        (hp y (by simpa [branch] using hy))
      simpa using hd.deriv
    intro x hx
    have heq : F x - p x = F (-1) - p (-1) :=
      isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio hdiff hzero
        (x := x) (y := (-1 : ℝ))
        (by simpa [branch] using hx)
        (by norm_num)
    linarith
  · rintro ⟨C, hC⟩
    change ∀ x ∈ branch, HasDerivAt F (f x) x
    intro x hx
    apply hasDerivAt_of_eq_on_branch
      (f := F) (g := fun y => p y + C) hx hC
    exact (hp x hx).add_const C

private lemma primitiveRaw_eq_primitive (x : ℝ) (hx : x ∈ branch) :
    primitiveRaw x = primitive x := by
  have he : Real.exp (-2 * x) = (Real.exp (-x)) ^ 2 := by
    rw [show -2 * x = (-x) + (-x) by ring, Real.exp_add, pow_two]
  have hs :
      Real.sqrt (Real.exp (-2 * x) - 1) =
        Real.exp (-x) * Real.sqrt (1 - Real.exp (2 * x)) := by
    rw [he]
    exact sqrt_scaled x
  have hpositive :
      0 < 1 + Real.sqrt (1 - Real.exp (2 * x)) := by positivity
  have hfactor :
      Real.exp (-x) + Real.exp (-x) * Real.sqrt (1 - Real.exp (2 * x)) =
        Real.exp (-x) * (1 + Real.sqrt (1 - Real.exp (2 * x))) := by
    ring
  have hlog :
      Real.log (Real.exp (-x) + Real.sqrt (Real.exp (-2 * x) - 1)) =
        -x + Real.log (1 + Real.sqrt (1 - Real.exp (2 * x))) := by
    rw [hs, hfactor]
    rw [Real.log_mul (Real.exp_ne_zero _) hpositive.ne']
    rw [Real.log_exp]
  rw [primitiveRaw, primitive, hlog]
  ring

theorem gap1 :
    AntiderivativesOn integrand = FirstReductionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change F ∈ FirstReductionFamily
    refine ⟨F - mainTerm, ?_, ?_⟩
    · change ∀ x ∈ branch, HasDerivAt (F - mainTerm) (reducedTerm x) x
      intro x hx
      convert (hF x hx).sub (hasDerivAt_mainTerm x hx) using 1 <;> ring
    · intro x hx
      dsimp [mainTerm]
      ring
  · intro hF
    change F ∈ FirstReductionFamily at hF
    rcases hF with ⟨H, hH, hFH⟩
    change ∀ x ∈ branch, HasDerivAt H (reducedTerm x) x at hH
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    apply hasDerivAt_of_eq_on_branch (f := F) (g := mainTerm + H) hx
    · intro y hy
      simpa [mainTerm] using hFH y hy
    · convert (hasDerivAt_mainTerm x hx).add (hH x hx) using 1 <;> ring
theorem gap2 :
    AntiderivativesOn integrand = SecondReductionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change F ∈ SecondReductionFamily
    refine ⟨mainTerm - F, ?_, ?_⟩
    · intro x hx
      change HasDerivAt (mainTerm - F) (auxiliaryRate x) x
      have hd := (hasDerivAt_mainTerm x hx).sub (hF x hx)
      rw [auxiliaryRate_eq x hx]
      convert hd using 1 <;> ring
    · intro x hx
      dsimp [mainTerm]
      ring
  · intro hF
    change F ∈ SecondReductionFamily at hF
    rcases hF with ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt G (auxiliaryRate x) x at hG
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    apply hasDerivAt_of_eq_on_branch (f := F) (g := mainTerm - G) hx
    · intro y hy
      simpa [mainTerm] using hFG y hy
    · have hd := (hasDerivAt_mainTerm x hx).sub (hG x hx)
      rw [auxiliaryRate_eq x hx] at hd
      convert hd using 1 <;> ring
theorem gap3 :
    SecondReductionFamily = PrimitiveFamily primitiveRaw := by
  calc
    SecondReductionFamily = AntiderivativesOn integrand := gap2.symm
    _ = PrimitiveFamily primitiveRaw :=
      antiderivatives_eq_primitive hasDerivAt_primitiveRaw
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveRaw := by
  exact gap2.trans gap3
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap4]
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← primitiveRaw_eq_primitive x hx]
    exact hC x hx
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [primitiveRaw_eq_primitive x hx]
    exact hC x hx

end
end ProofGap.Exercise2161
