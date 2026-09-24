import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1935

noncomputable section

def xOf (t : ℝ) := ((t ^ 2 - 1) / (2 * t)) ^ 2
def parameterBranch : Set ℝ := {t | 1 < t}
def xBranch : Set ℝ := {x | 0 < x}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def sourceParamIntegrand (t : ℝ) :=
  1 / (1 + Real.sqrt (xOf t) + Real.sqrt (xOf t + 1)) * deriv xOf t
def rationalParamIntegrand (t : ℝ) :=
  (t ^ 4 - 1) / (t ^ 3 * (t + 1))
def expandedParamIntegrand (t : ℝ) :=
  1 - 1 / t + 1 / t ^ 2 - 1 / t ^ 3
def HalfScaledFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn parameterBranch p,
    ∀ t ∈ parameterBranch, F t = 1 / 2 * G t}
def parameterPrimitive (t : ℝ) :=
  1 / 2 * (t - Real.log t - 1 / t + 1 / (2 * t ^ 2))
def sourceXIntegrand (x : ℝ) :=
  1 / (1 + Real.sqrt x + Real.sqrt (1 + x))
def xPrimitive (x : ℝ) :=
  Real.sqrt x -
    1 / 2 * Real.log (Real.sqrt x + Real.sqrt (x + 1)) +
    x / 2 - 1 / 2 * Real.sqrt (x * (x + 1))

private theorem hasDerivAt_of_eqOn_Ioi
    {a x f' : ℝ} {f g : ℝ → ℝ}
    (hx : x ∈ Set.Ioi a) (hfg : Set.EqOn f g (Set.Ioi a))
    (hg : HasDerivAt g f' x) : HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact hfg hy

private theorem antiderivativesOn_Ioi_eq_primitiveFamilyOn
    (a : ℝ) (f P : ℝ → ℝ)
    (hP : ∀ x ∈ Set.Ioi a, HasDerivAt P (f x) x) :
    AntiderivativesOn (Set.Ioi a) f =
      PrimitiveFamilyOn (Set.Ioi a) P := by
  ext F
  constructor
  · intro hF
    have hD : ∀ x ∈ Set.Ioi a,
        HasDerivAt (fun y => F y - P y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hP x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - P y) (Set.Ioi a) := by
      intro x hx
      exact (hD x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ Set.Ioi a,
        deriv (fun y => F y - P y) x = 0 := by
      intro x hx
      exact (hD x hx).deriv
    refine ⟨F (a + 1) - P (a + 1), ?_⟩
    intro x hx
    have ha : a + 1 ∈ Set.Ioi a := by simp
    have heq : F x - P x = F (a + 1) - P (a + 1) :=
      isOpen_Ioi.is_const_of_deriv_eq_zero
        ((convex_Ioi a : Convex ℝ (Set.Ioi a)).isPreconnected)
        hdiff hzero hx ha
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    apply hasDerivAt_of_eqOn_Ioi hx
    · intro y hy
      exact hC y hy
    · exact (hP x hx).add_const C

theorem gap1 (t : ℝ) (ht : t ∈ parameterBranch) :
    1 < t := by
  exact ht
theorem gap2 (t : ℝ) (ht : t ∈ parameterBranch) :
    xOf t = ((t ^ 2 - 1) / (2 * t)) ^ 2 := by
  rfl
theorem gap3 (t : ℝ) (ht : t ∈ parameterBranch) :
    HasDerivAt xOf ((t ^ 4 - 1) / (2 * t ^ 3)) t := by
  have ht' : 1 < t := gap1 t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht')
  have hnum : HasDerivAt (fun u : ℝ => u ^ 2 - 1) (2 * t) t := by
    simpa [id_eq] using ((hasDerivAt_id t).pow 2).sub_const 1
  have hden : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
    simpa [id_eq] using (hasDerivAt_id t).const_mul 2
  have hquot := hnum.div hden (mul_ne_zero (by norm_num) ht0)
  have hinner : HasDerivAt
      (fun u : ℝ => (u ^ 2 - 1) / (2 * u))
      ((t ^ 2 + 1) / (2 * t ^ 2)) t := by
    convert hquot using 1
    field_simp [ht0] <;> ring
  have hsq := hinner.pow 2
  have hderiv :
      (2 : ℝ) * ((t ^ 2 - 1) / (2 * t)) ^ (2 - 1) *
          ((t ^ 2 + 1) / (2 * t ^ 2)) =
        (t ^ 4 - 1) / (2 * t ^ 3) := by
    norm_num
    field_simp [ht0] <;> ring
  unfold xOf
  rw [← hderiv]
  exact hsq
theorem gap4 (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (xOf t + 1) = (t ^ 2 + 1) / (2 * t) := by
  have ht' : 1 < t := gap1 t ht
  have htpos : 0 < t := lt_trans zero_lt_one ht'
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have hsq :
      ((t ^ 2 - 1) / (2 * t)) ^ 2 + 1 =
        ((t ^ 2 + 1) / (2 * t)) ^ 2 := by
    field_simp [ht0]
    ring
  have hpos : 0 < (t ^ 2 + 1) / (2 * t) := by
    apply div_pos
    · nlinarith [sq_nonneg t]
    · nlinarith
  rw [gap2 t ht, hsq, Real.sqrt_sq_eq_abs, abs_of_pos hpos]
theorem gap5 (t : ℝ) (ht : t ∈ parameterBranch) :
    t = Real.sqrt (xOf t) + Real.sqrt (xOf t + 1) := by
  have ht' : 1 < t := gap1 t ht
  have htpos : 0 < t := lt_trans zero_lt_one ht'
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have hu : 0 < (t ^ 2 - 1) / (2 * t) := by
    apply div_pos
    · nlinarith
    · nlinarith
  rw [gap4 t ht, gap2 t ht, Real.sqrt_sq_eq_abs, abs_of_pos hu]
  field_simp [ht0]
  ring
theorem gap6 :
    AntiderivativesOn parameterBranch sourceParamIntegrand =
      HalfScaledFamily rationalParamIntegrand := by
  have hsource : ∀ t ∈ parameterBranch,
      sourceParamIntegrand t = 1 / 2 * rationalParamIntegrand t := by
    intro t ht
    have ht' : 1 < t := gap1 t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht')
    have ht1 : t + 1 ≠ 0 := ne_of_gt (by linarith)
    have hsum :
        1 + Real.sqrt (xOf t) + Real.sqrt (xOf t + 1) = 1 + t := by
      linarith [gap5 t ht]
    unfold sourceParamIntegrand rationalParamIntegrand
    rw [(gap3 t ht).deriv, hsum]
    field_simp [ht0, ht1]
    ring
  ext F
  constructor
  · intro hF
    change ∀ t ∈ parameterBranch,
      HasDerivAt F (sourceParamIntegrand t) t at hF
    change ∃ G ∈ AntiderivativesOn parameterBranch rationalParamIntegrand,
      ∀ t ∈ parameterBranch, F t = 1 / 2 * G t
    refine ⟨fun t => 2 * F t, ?_, ?_⟩
    · intro t ht
      convert (hF t ht).const_mul 2 using 1 <;>
        rw [hsource t ht] <;> ring
    · intro t ht
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ t ∈ parameterBranch,
      HasDerivAt F (sourceParamIntegrand t) t
    change ∀ t ∈ parameterBranch,
      HasDerivAt G (rationalParamIntegrand t) t at hG
    intro t ht
    apply hasDerivAt_of_eqOn_Ioi (a := 1) ht
    · intro y hy
      exact hFG y hy
    · convert (hG t ht).const_mul (1 / 2) using 1 <;>
        rw [hsource t ht] <;> ring
theorem gap7 :
    HalfScaledFamily rationalParamIntegrand =
      HalfScaledFamily expandedParamIntegrand := by
  have hparam : ∀ t ∈ parameterBranch,
      rationalParamIntegrand t = expandedParamIntegrand t := by
    intro t ht
    have ht' : 1 < t := gap1 t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht')
    unfold rationalParamIntegrand expandedParamIntegrand
    field_simp [ht0]
    ring
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro t ht
    rw [← hparam t ht]
    exact hG t ht
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro t ht
    rw [hparam t ht]
    exact hG t ht
theorem gap8 :
    HalfScaledFamily expandedParamIntegrand =
      PrimitiveFamilyOn parameterBranch parameterPrimitive := by
  have hprimitive : ∀ t ∈ parameterBranch,
      HasDerivAt parameterPrimitive
        (1 / 2 * expandedParamIntegrand t) t := by
    intro t ht
    have ht' : 1 < t := gap1 t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht')
    have ht20 : 2 * t ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 ht0)
    have hid : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id t
    have hrecip : HasDerivAt (fun y : ℝ => 1 / y) (-1 / t ^ 2) t := by
      simpa only [one_div, id_eq] using hid.inv ht0
    have hden : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (4 * t) t := by
      convert (hid.pow 2).const_mul 2 using 1 <;>
        norm_num [id_eq] <;> ring
    have hlast : HasDerivAt
        (fun y : ℝ => 1 / (2 * y ^ 2)) (-1 / t ^ 3) t := by
      convert hden.inv ht20 using 1
      · funext y
        simp [one_div]
      · field_simp [ht0] <;> ring
    have hinner :=
      (((hid.sub (Real.hasDerivAt_log ht0)).sub hrecip).add hlast)
    have htotal := hinner.const_mul (1 / 2)
    unfold parameterPrimitive expandedParamIntegrand
    convert htotal using 1 <;> ring
  have hhalf :
      HalfScaledFamily expandedParamIntegrand =
        AntiderivativesOn parameterBranch
          (fun t => 1 / 2 * expandedParamIntegrand t) := by
    ext F
    constructor
    · rintro ⟨G, hG, hFG⟩
      intro t ht
      apply hasDerivAt_of_eqOn_Ioi (a := 1) ht
      · intro y hy
        exact hFG y hy
      · convert (hG t ht).const_mul (1 / 2) using 1 <;> ring
    · intro hF
      refine ⟨fun t => 2 * F t, ?_, ?_⟩
      · intro t ht
        convert (hF t ht).const_mul 2 using 1 <;> ring
      · intro t ht
        ring
  rw [hhalf]
  change AntiderivativesOn (Set.Ioi 1)
      (fun t => 1 / 2 * expandedParamIntegrand t) =
    PrimitiveFamilyOn (Set.Ioi 1) parameterPrimitive
  apply antiderivativesOn_Ioi_eq_primitiveFamilyOn
  intro t ht
  exact hprimitive t ht
theorem gap9 :
    AntiderivativesOn parameterBranch sourceParamIntegrand =
      PrimitiveFamilyOn parameterBranch parameterPrimitive := by
  exact gap6.trans (gap7.trans gap8)
theorem gap10 :
    AntiderivativesOn xBranch sourceXIntegrand =
      PrimitiveFamilyOn xBranch xPrimitive := by
  have hprimitive : ∀ x ∈ xBranch,
      HasDerivAt xPrimitive (sourceXIntegrand x) x := by
    intro x hx
    have hxpos : 0 < x := hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hxp1pos : 0 < x + 1 := by linarith
    have hxp10 : x + 1 ≠ 0 := ne_of_gt hxp1pos
    have hprodpos : 0 < x * (x + 1) := mul_pos hxpos hxp1pos
    have hprod0 : x * (x + 1) ≠ 0 := ne_of_gt hprodpos
    have hapos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hbpos : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 hxp1pos
    have hcpos : 0 < Real.sqrt (x * (x + 1)) := Real.sqrt_pos.2 hprodpos
    have ha0 : Real.sqrt x ≠ 0 := ne_of_gt hapos
    have hb0 : Real.sqrt (x + 1) ≠ 0 := ne_of_gt hbpos
    have hc0 : Real.sqrt (x * (x + 1)) ≠ 0 := ne_of_gt hcpos
    have hsum0 : Real.sqrt x + Real.sqrt (x + 1) ≠ 0 :=
      ne_of_gt (add_pos hapos hbpos)
    have hsx : HasDerivAt Real.sqrt
        (1 / (2 * Real.sqrt x)) x := by
      convert Real.hasDerivAt_sqrt hx0 using 1 <;>
        field_simp [ha0] <;> ring
    have hsarg : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
      convert (hasDerivAt_id x).add_const 1 using 1 <;>
        simp only [id_eq] <;> ring
    have hsb : HasDerivAt (fun y : ℝ => Real.sqrt (y + 1))
        (1 / (2 * Real.sqrt (x + 1))) x := by
      convert (Real.hasDerivAt_sqrt hxp10).comp x hsarg using 1 <;>
        field_simp [hb0] <;> ring
    have hlog : HasDerivAt
        (fun y : ℝ => Real.log (Real.sqrt y + Real.sqrt (y + 1)))
        ((1 / (2 * Real.sqrt x) + 1 / (2 * Real.sqrt (x + 1))) /
          (Real.sqrt x + Real.sqrt (x + 1))) x := by
      convert (Real.hasDerivAt_log hsum0).comp x (hsx.add hsb) using 1 <;>
        field_simp [ha0, hb0, hsum0] <;> ring
    have hprodarg : HasDerivAt (fun y : ℝ => y * (y + 1))
        (2 * x + 1) x := by
      convert (hasDerivAt_id x).mul hsarg using 1 <;>
        simp only [id_eq] <;> ring
    have hsc : HasDerivAt
        (fun y : ℝ => Real.sqrt (y * (y + 1)))
        ((2 * x + 1) / (2 * Real.sqrt (x * (x + 1)))) x := by
      convert (Real.hasDerivAt_sqrt hprod0).comp x hprodarg using 1 <;>
        field_simp [hc0] <;> ring
    have hd : HasDerivAt xPrimitive
        (1 / (2 * Real.sqrt x) -
          1 / 2 *
            ((1 / (2 * Real.sqrt x) + 1 / (2 * Real.sqrt (x + 1))) /
              (Real.sqrt x + Real.sqrt (x + 1))) +
          1 / 2 -
          1 / 2 * ((2 * x + 1) /
            (2 * Real.sqrt (x * (x + 1))))) x := by
      unfold xPrimitive
      convert (((hsx.sub (hlog.const_mul (1 / 2))).add
        ((hasDerivAt_id x).div_const 2)).sub
          (hsc.const_mul (1 / 2))) using 1 <;>
        simp only [id_eq] <;> ring
    have hc : Real.sqrt (x * (x + 1)) =
        Real.sqrt x * Real.sqrt (x + 1) := by
      rw [Real.sqrt_mul (le_of_lt hxpos)]
    have hsqa : (Real.sqrt x) ^ 2 = x :=
      Real.sq_sqrt (le_of_lt hxpos)
    have hsqb : (Real.sqrt (x + 1)) ^ 2 = x + 1 :=
      Real.sq_sqrt (le_of_lt hxp1pos)
    have htarget0 :
        1 + Real.sqrt x + Real.sqrt (x + 1) ≠ 0 :=
      ne_of_gt (by linarith)
    have halg :
        1 / (2 * Real.sqrt x) -
            1 / 2 *
              ((1 / (2 * Real.sqrt x) + 1 / (2 * Real.sqrt (x + 1))) /
                (Real.sqrt x + Real.sqrt (x + 1))) +
            1 / 2 -
            1 / 2 * ((2 * x + 1) /
              (2 * Real.sqrt (x * (x + 1)))) =
          sourceXIntegrand x := by
      unfold sourceXIntegrand
      rw [show Real.sqrt (1 + x) = Real.sqrt (x + 1) by ring, hc]
      field_simp [ha0, hb0, hsum0, htarget0]
      nlinarith [hsqa, hsqb]
    rw [halg] at hd
    exact hd
  change AntiderivativesOn (Set.Ioi 0) sourceXIntegrand =
    PrimitiveFamilyOn (Set.Ioi 0) xPrimitive
  apply antiderivativesOn_Ioi_eq_primitiveFamilyOn
  intro x hx
  exact hprimitive x hx

end
end ProofGap.Exercise1935
