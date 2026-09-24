import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1814

noncomputable section

def branch : Set ℝ := Set.Ioo (-1 : ℝ) 1
def logRatio (x : ℝ) := Real.log ((1 - x) / (1 + x))
def integrand (x : ℝ) := x ^ 2 * logRatio x
def scaledIntegrand (x : ℝ) := logRatio x * deriv (fun t : ℝ => t ^ 3) x
def residual (x : ℝ) := x ^ 3 / (1 - x ^ 2)
def rewrittenResidual (x : ℝ) := -x + x / (1 - x ^ 2)
def boundary (x : ℝ) := x ^ 3 / 3 * logRatio x
def primitive (x : ℝ) :=
  boundary x - (1 / 3 : ℝ) * x ^ 2 -
    (1 / 3 : ℝ) * Real.log (1 - x ^ 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ThirdFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn scaledIntegrand,
    ∀ x ∈ branch, F x = (1 / 3 : ℝ) * G x}
def ByPartsFamily (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn r,
    ∀ x ∈ branch, F x = boundary x + (2 / 3 : ℝ) * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem localCalculus (x : ℝ) (hx : x ∈ branch) :
    deriv (fun t : ℝ => t ^ 3) x = 3 * x ^ 2 ∧
    residual x = rewrittenResidual x ∧
    HasDerivAt boundary (integrand x - (2 / 3 : ℝ) * residual x) x ∧
    HasDerivAt primitive (integrand x) x := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hminus : 1 - x ≠ 0 := by linarith
  have hplus : 1 + x ≠ 0 := by linarith
  have hdenpos : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (show 0 < x + 1 by linarith) (show 0 < 1 - x by linarith)]
  have hden : 1 - x ^ 2 ≠ 0 := ne_of_gt hdenpos
  have hcubicDer : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using ((hasDerivAt_id x).pow 3)
  have hcubic : deriv (fun t : ℝ => t ^ 3) x = 3 * x ^ 2 := hcubicDer.deriv
  have hnum : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> ring
  have hdenom : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x) using 1 <;> ring
  have hquot : HasDerivAt (fun y : ℝ => (1 - y) / (1 + y))
      (-2 / (1 + x) ^ 2) x := by
    have hraw := hnum.div hdenom hplus
    convert hraw using 1
    field_simp [hplus]
    <;> ring
  have hlog : HasDerivAt logRatio (-2 / (1 - x ^ 2)) x := by
    change HasDerivAt (fun y : ℝ => Real.log ((1 - y) / (1 + y)))
      (-2 / (1 - x ^ 2)) x
    convert hquot.log (div_ne_zero hminus hplus) using 1
    field_simp [hminus, hplus, hden]
    <;> ring
  have hthird : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
    convert hcubicDer.div_const 3 using 1 <;> ring
  have hboundary :
      HasDerivAt boundary (integrand x - (2 / 3 : ℝ) * residual x) x := by
    change HasDerivAt (fun y : ℝ => y ^ 3 / 3 * logRatio y)
      (integrand x - (2 / 3 : ℝ) * residual x) x
    convert hthird.mul hlog using 1
    dsimp [integrand, residual]
    ring
  have hresidual : residual x = rewrittenResidual x := by
    dsimp [residual, rewrittenResidual]
    field_simp [hden]
    <;> ring
  have hsquare : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2)
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub hsquare using 1 <;> ring
  have hinnerLog : HasDerivAt (fun y : ℝ => Real.log (1 - y ^ 2))
      ((-2 * x) / (1 - x ^ 2)) x := hinner.log hden
  have hprimitive : HasDerivAt primitive (integrand x) x := by
    have hp := (hboundary.sub (hsquare.const_mul (1 / 3 : ℝ))).sub
      (hinnerLog.const_mul (1 / 3 : ℝ))
    convert hp using 1
    rw [hresidual]
    dsimp [rewrittenResidual]
    ring
  exact ⟨hcubic, hresidual, hboundary, hprimitive⟩

theorem gap1 :
    AntiderivativesOn integrand = ThirdFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => 3 * F y, ?_, ?_⟩
    · intro x hx
      have hcubic := (localCalculus x hx).1
      convert (hF x hx).const_mul 3 using 1 <;>
        simp [scaledIntegrand, integrand, hcubic] <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hcubic := (localCalculus x hx).1
    have hbase := (hG x hx).const_mul (1 / 3 : ℝ)
    have hxn : branch ∈ nhds x :=
      (show IsOpen branch by simpa [branch] using isOpen_Ioo).mem_nhds hx
    have heq : (fun y => (1 / 3 : ℝ) * G y) =ᶠ[nhds x] F := by
      filter_upwards [hxn] with y hy
      exact (hFG y hy).symm
    have hd := hbase.congr_of_eventuallyEq heq.symm
    convert hd using 1 <;>
      simp [scaledIntegrand, integrand, hcubic] <;> ring
theorem gap2 :
    ThirdFamily = ByPartsFamily residual := by
  rw [← gap1]
  ext F
  constructor
  · intro hF
    refine ⟨fun y => (3 / 2 : ℝ) * (F y - boundary y), ?_, ?_⟩
    · intro x hx
      have hboundary := (localCalculus x hx).2.2.1
      convert ((hF x hx).sub hboundary).const_mul (3 / 2 : ℝ) using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hboundary := (localCalculus x hx).2.2.1
    have hbase := hboundary.add ((hG x hx).const_mul (2 / 3 : ℝ))
    have hxn : branch ∈ nhds x :=
      (show IsOpen branch by simpa [branch] using isOpen_Ioo).mem_nhds hx
    have heq : (fun y => boundary y + (2 / 3 : ℝ) * G y) =ᶠ[nhds x] F := by
      filter_upwards [hxn] with y hy
      exact (hFG y hy).symm
    have hd := hbase.congr_of_eventuallyEq heq.symm
    convert hd using 1 <;> ring
theorem gap3 :
    AntiderivativesOn integrand = ByPartsFamily residual := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand = ByPartsFamily rewrittenResidual := by
  rw [gap3]
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    have hresidual := (localCalculus x hx).2.1
    simpa [hresidual] using hG x hx
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    have hresidual := (localCalculus x hx).2.1
    simpa [hresidual] using hG x hx
theorem gap5 :
    ByPartsFamily rewrittenResidual = PrimitiveFamily := by
  rw [← gap4]
  ext F
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hDderiv : ∀ y ∈ branch, HasDerivAt D 0 y := by
      intro y hy
      dsimp [D]
      convert (hF y hy).sub (localCalculus y hy).2.2.2 using 1 <;> ring
    have hDdiff : DifferentiableOn ℝ D (Set.Ioo (-1 : ℝ) 1) := by
      intro y hy
      exact (hDderiv y (by simpa [branch] using hy)).differentiableAt.differentiableWithinAt
    have hDzero : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, deriv D y = 0 := by
      intro y hy
      exact (hDderiv y (by simpa [branch] using hy)).deriv
    have hzero : (0 : ℝ) ∈ branch := by
      simp [branch]
    refine ⟨D 0, ?_⟩
    intro x hx
    have hconst : D x = D 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hDdiff hDzero
        (x := x) (y := 0)
        (by simpa [branch] using hx)
        (by simpa [branch] using hzero)
    dsimp [D] at hconst ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hbase := (localCalculus x hx).2.2.2.const_add C
    have hxn : branch ∈ nhds x :=
      (show IsOpen branch by simpa [branch] using isOpen_Ioo).mem_nhds hx
    have heq : F =ᶠ[nhds x] (fun y => C + primitive y) := by
      filter_upwards [hxn] with y hy
      rw [hFC y hy]
      ring
    exact hbase.congr_of_eventuallyEq heq
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1814
