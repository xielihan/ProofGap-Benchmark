import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2151

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def integrand (x : ℝ) := x * Real.log x / (1 + x ^ 2) ^ 2
def InitialFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x ∈ branch,
      HasDerivAt G
        (Real.log x * deriv (fun y : ℝ => 1 / (1 + y ^ 2)) x) x) ∧
    ∀ x ∈ branch, F x = -1 / 2 * G x}
def residual (x : ℝ) := 1 / (x * (1 + x ^ 2))
def ReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residual,
    ∀ x ∈ branch,
      F x = -Real.log x / (2 * (1 + x ^ 2)) + 1 / 2 * G x}
def splitResidual (x : ℝ) := 1 / x - x / (1 + x ^ 2)
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn splitResidual,
    ∀ x ∈ branch,
      F x = -Real.log x / (2 * (1 + x ^ 2)) + 1 / 2 * G x}
def primitiveLong (x : ℝ) :=
  -Real.log x / (2 * (1 + x ^ 2)) +
    1 / 2 * Real.log x - 1 / 4 * Real.log (1 + x ^ 2)
def primitive (x : ℝ) :=
  -Real.log x / (2 * (1 + x ^ 2)) +
    1 / 4 * Real.log (x ^ 2 / (1 + x ^ 2))

private theorem private_hasDerivAt_quad (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
    simp only [id] <;> ring

private theorem private_hasDerivAt_invquad (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 / (1 + y ^ 2))
      (-2 * x / (1 + x ^ 2) ^ 2) x := by
  have hq : 1 + x ^ 2 ≠ 0 := by positivity
  convert (hasDerivAt_const x (1 : ℝ)).div (private_hasDerivAt_quad x) hq using 1 <;>
    field_simp [hq] <;> ring

private theorem private_residual_eq_splitResidual
    (x : ℝ) (hx : x ∈ branch) : residual x = splitResidual x := by
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hq : 1 + x ^ 2 ≠ 0 := by positivity
  unfold residual splitResidual
  field_simp [hx0, hq]
  ring

private theorem private_reduction_eq_split : ReductionFamily = SplitFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    change (∀ x ∈ branch, HasDerivAt G (residual x) x) at hG
    change ∀ x ∈ branch, HasDerivAt G (splitResidual x) x
    intro x hx
    convert hG x hx using 1
    exact (private_residual_eq_splitResidual x hx).symm
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    change (∀ x ∈ branch, HasDerivAt G (splitResidual x) x) at hG
    change ∀ x ∈ branch, HasDerivAt G (residual x) x
    intro x hx
    convert hG x hx using 1
    exact private_residual_eq_splitResidual x hx

private theorem private_antiderivatives_eq_primitiveFamily
    {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  constructor
  · intro hF
    change (∀ x ∈ branch, HasDerivAt F (f x) x) at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C
    refine ⟨F 1 - p 1, ?_⟩
    intro x hx
    let b : ℝ := max x 1 + 1
    have hxI : x ∈ Set.Ioo 0 b := by
      constructor
      · simpa [branch] using hx
      · dsimp [b]
        have hle : x ≤ max x 1 := le_max_left _ _
        linarith
    have h1I : (1 : ℝ) ∈ Set.Ioo 0 b := by
      constructor
      · norm_num
      · dsimp [b]
        have hle : (1 : ℝ) ≤ max x 1 := le_max_right _ _
        linarith
    have hdiff :
        DifferentiableOn ℝ (fun z => F z - p z) (Set.Ioo 0 b) := by
      intro z hz
      have hzbranch : z ∈ branch := by simpa [branch] using hz.1
      exact ((hF z hzbranch).sub (hp z hzbranch)).differentiableAt.differentiableWithinAt
    have hzero : ∀ z ∈ Set.Ioo 0 b, deriv (fun w => F w - p w) z = 0 := by
      intro z hz
      have hzbranch : z ∈ branch := by simpa [branch] using hz.1
      simpa using ((hF z hzbranch).sub (hp z hzbranch)).deriv
    have heq : F x - p x = F 1 - p 1 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hzero hxI h1I
    linarith
  · rintro ⟨C, hFC⟩
    change ∀ x ∈ branch, HasDerivAt F (f x) x
    intro x hx
    have hbase : HasDerivAt (fun y => p y + C) (f x) x :=
      (hp x hx).add_const C
    have hopen : branch ∈ nhds x := by
      simpa [branch] using isOpen_Ioi.mem_nhds hx
    have hev : (fun y => p y + C) =ᶠ[nhds x] F := by
      filter_upwards [hopen] with y hy
      exact (hFC y hy).symm
    exact hbase.congr_of_eventuallyEq hev.symm

private theorem private_hasDerivAt_primitiveLong
    (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveLong (integrand x) x := by
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hq0 : 1 + x ^ 2 ≠ 0 := by positivity
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx0
  have hq := private_hasDerivAt_quad x
  have hden : HasDerivAt (fun y : ℝ => 2 * (1 + y ^ 2)) (4 * x) x := by
    convert (hasDerivAt_const x (2 : ℝ)).mul hq using 1 <;> ring
  have hlogq :
      HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2))
        (2 * x / (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_log hq0).comp x hq using 1 <;>
      field_simp [hq0] <;> ring
  have ht1 := hlog.neg.div hden (mul_ne_zero (by norm_num) hq0)
  have ht2 := (hasDerivAt_const x (1 / 2 : ℝ)).mul hlog
  have ht3 := (hasDerivAt_const x (-1 / 4 : ℝ)).mul hlogq
  convert (ht1.add ht2).add ht3 using 1
  · ext y
    dsimp [primitiveLong]
    ring
  · simp only [Pi.neg_apply, integrand]
    field_simp [hx0, hq0]
    ring

private theorem private_primitive_eq_primitiveLong
    (x : ℝ) (hx : x ∈ branch) : primitiveLong x = primitive x := by
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hq0 : 1 + x ^ 2 ≠ 0 := by positivity
  unfold primitive primitiveLong
  rw [Real.log_div (pow_ne_zero 2 hx0) hq0, Real.log_pow]
  ring

theorem gap1 :
    AntiderivativesOn integrand = InitialFamily := by
  ext F
  constructor
  · intro hF
    change (∀ x ∈ branch, HasDerivAt F (integrand x) x) at hF
    change ∃ G : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt G
          (Real.log x * deriv (fun y : ℝ => 1 / (1 + y ^ 2)) x) x) ∧
      ∀ x ∈ branch, F x = -1 / 2 * G x
    refine ⟨fun y => (-2 : ℝ) * F y, ?_, ?_⟩
    · intro x hx
      have hd := private_hasDerivAt_invquad x
      have hd' := hd.deriv
      convert (hasDerivAt_const x (-2 : ℝ)).mul (hF x hx) using 1
      rw [hd']
      simp only [integrand]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hd := private_hasDerivAt_invquad x
    have hd' := hd.deriv
    have hbase :
        HasDerivAt (fun y => (-1 / 2 : ℝ) * G y) (integrand x) x := by
      convert (hasDerivAt_const x (-1 / 2 : ℝ)).mul (hG x hx) using 1
      rw [hd']
      simp only [integrand]
      ring
    have hopen : branch ∈ nhds x := by
      simpa [branch] using isOpen_Ioi.mem_nhds hx
    have hev : (fun y => (-1 / 2 : ℝ) * G y) =ᶠ[nhds x] F := by
      filter_upwards [hopen] with y hy
      exact (hFG y hy).symm
    exact hbase.congr_of_eventuallyEq hev.symm
theorem gap2 :
    InitialFamily = ReductionFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    change ∃ K ∈ AntiderivativesOn residual,
      ∀ x ∈ branch,
        F x = -Real.log x / (2 * (1 + x ^ 2)) + 1 / 2 * K x
    refine ⟨fun y => Real.log y * (1 / (1 + y ^ 2)) - G y, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => Real.log y * (1 / (1 + y ^ 2)) - G y)
          (residual x) x
      intro x hx
      have hxpos : 0 < x := by simpa [branch] using hx
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      have hlog : HasDerivAt Real.log (1 / x) x := by
        simpa [one_div] using Real.hasDerivAt_log hx0
      have hd := private_hasDerivAt_invquad x
      have hd' := hd.deriv
      convert (hlog.mul hd).sub (hG x hx) using 1
      rw [hd']
      simp only [residual]
      field_simp [hx0]
      ring
    · intro x hx
      have hq0 : 1 + x ^ 2 ≠ 0 := by positivity
      rw [hFG x hx]
      field_simp [hq0]
      ring
  · rintro ⟨K, hK, hFK⟩
    change ∃ G : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt G
          (Real.log x * deriv (fun y : ℝ => 1 / (1 + y ^ 2)) x) x) ∧
      ∀ x ∈ branch, F x = -1 / 2 * G x
    refine ⟨fun y => Real.log y * (1 / (1 + y ^ 2)) - K y, ?_, ?_⟩
    · intro x hx
      have hxpos : 0 < x := by simpa [branch] using hx
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      have hlog : HasDerivAt Real.log (1 / x) x := by
        simpa [one_div] using Real.hasDerivAt_log hx0
      have hd := private_hasDerivAt_invquad x
      have hd' := hd.deriv
      convert (hlog.mul hd).sub (hK x hx) using 1
      rw [hd']
      simp only [residual]
      field_simp [hx0]
      ring
    · intro x hx
      have hq0 : 1 + x ^ 2 ≠ 0 := by positivity
      rw [hFK x hx]
      field_simp [hq0]
      ring
theorem gap3 :
    AntiderivativesOn integrand = ReductionFamily := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand = SplitFamily := by
  calc
    AntiderivativesOn integrand = ReductionFamily := gap3
    _ = SplitFamily := private_reduction_eq_split
theorem gap5 :
    SplitFamily = PrimitiveFamily primitiveLong := by
  calc
    SplitFamily = AntiderivativesOn integrand := gap4.symm
    _ = PrimitiveFamily primitiveLong :=
      private_antiderivatives_eq_primitiveFamily private_hasDerivAt_primitiveLong
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveLong := by
  exact private_antiderivatives_eq_primitiveFamily private_hasDerivAt_primitiveLong
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  apply private_antiderivatives_eq_primitiveFamily
  intro x hx
  have hlong := private_hasDerivAt_primitiveLong x hx
  have hopen : branch ∈ nhds x := by
    simpa [branch] using isOpen_Ioi.mem_nhds hx
  have hev : primitiveLong =ᶠ[nhds x] primitive := by
    filter_upwards [hopen] with y hy
    exact private_primitive_eq_primitiveLong y hy
  exact hlong.congr_of_eventuallyEq hev.symm

end
end ProofGap.Exercise2151
