import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2139

noncomputable section

def branch : Set ℝ := Set.Ioi (-1)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def q (x : ℝ) := 1 + x + x ^ 2
def integrand (x : ℝ) := Real.log (q x) / (1 + x) ^ 2
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x ∈ branch,
      HasDerivAt G
        (Real.log (q x) * deriv (fun y : ℝ => 1 / (1 + y)) x) x) ∧
    ∀ x ∈ branch, F x = -G x}
def reductionIntegrand (x : ℝ) :=
  (2 * x + 1) / ((x + 1) * q x)
def ReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn reductionIntegrand,
    ∀ x ∈ branch, F x = -Real.log (q x) / (1 + x) + G x}
def partialFractionIntegrand (x : ℝ) :=
  (x + 2) / q x - 1 / (1 + x)
def PartialFractionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn partialFractionIntegrand,
    ∀ x ∈ branch, F x = -Real.log (q x) / (1 + x) + G x}
def FinalReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn
      (fun x => (2 * x + 1) / q x + 3 / q x),
    ∀ x ∈ branch,
      F x = -Real.log (q x) / (1 + x) + 1 / 2 * G x -
        Real.log |1 + x|}
def primitiveLong (x : ℝ) :=
  -Real.log (q x) / (1 + x) +
    1 / 2 * Real.log (q x) +
    Real.sqrt 3 * Real.arctan ((2 * x + 1) / Real.sqrt 3) -
    Real.log |1 + x|
def primitiveFinal (x : ℝ) :=
  -Real.log (q x) / (1 + x) -
    1 / 2 * Real.log ((1 + x) ^ 2 / q x) +
    Real.sqrt 3 * Real.arctan ((2 * x + 1) / Real.sqrt 3)

private theorem branch_add_one_pos {x : ℝ} (hx : x ∈ branch) : 0 < 1 + x := by
  change -1 < x at hx
  linarith

private theorem q_pos (x : ℝ) : 0 < q x := by
  unfold q
  nlinarith [sq_nonneg (2 * x + 1)]

private theorem q_hasDerivAt (x : ℝ) : HasDerivAt q (2 * x + 1) x := by
  have hlin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa [add_comm] using (hasDerivAt_id x).add_const 1
  have hsq0 := (hasDerivAt_id x).pow 2
  have hpow :
      (id ^ 2 : ℝ → ℝ) = (fun y : ℝ => y ^ 2) := by
    funext y
    rfl
  rw [hpow] at hsq0
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hsq0
  have hd := hlin.add hsq
  have hsum :
      ((fun y : ℝ => 1 + y) + (fun y : ℝ => y ^ 2)) = q := by
    funext y
    rfl
  rw [hsum] at hd
  have hcoef : (1 : ℝ) + 2 * x = 2 * x + 1 := by
    ring
  rw [hcoef] at hd
  exact hd

private theorem reciprocal_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => 1 / (1 + y)) (-1 / (1 + x) ^ 2) x := by
  have hne : 1 + x ≠ 0 := ne_of_gt (branch_add_one_pos hx)
  have hne' : x + 1 ≠ 0 := by
    simpa [add_comm] using hne
  have hbase : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const 1
  simpa [one_div, add_comm] using hbase.inv hne'

private theorem log_q_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (q y)) ((2 * x + 1) / q x) x := by
  have hq : q x ≠ 0 := ne_of_gt (q_pos x)
  have hd := (Real.hasDerivAt_log hq).comp x (q_hasDerivAt x)
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using hd

private theorem quotient_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.log (q y) / (1 + y))
      (reductionIntegrand x - integrand x) x := by
  have h1 : 1 + x ≠ 0 := ne_of_gt (branch_add_one_pos hx)
  have hx1 : x + 1 ≠ 0 := by
    simpa [add_comm] using h1
  have hq : q x ≠ 0 := ne_of_gt (q_pos x)
  have hpoly : 1 + x + x ^ 2 ≠ 0 := by
    simpa [q] using hq
  have hd :
      HasDerivAt (fun y : ℝ => Real.log (q y) / (1 + y))
        (((2 * x + 1) / q x) * (1 / (1 + x)) +
          Real.log (q x) * (-1 / (1 + x) ^ 2)) x := by
    simpa [div_eq_mul_inv] using
      (log_q_hasDerivAt x).mul (reciprocal_hasDerivAt x hx)
  have hval :
      ((2 * x + 1) / q x) * (1 / (1 + x)) +
          Real.log (q x) * (-1 / (1 + x) ^ 2) =
        reductionIntegrand x - integrand x := by
    unfold reductionIntegrand integrand q
    field_simp [h1, hx1, hpoly]
    ring
  rw [hval] at hd
  exact hd

private theorem hasDerivAt_of_eqOn_branch
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ branch)
    (hfg : ∀ y ∈ branch, f y = g y) (hg : HasDerivAt g f' x) :
    HasDerivAt f f' x := by
  have hopen : IsOpen branch := by
    simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ)))
  exact hg.congr_of_eventuallyEq
    (Filter.Eventually.mono (hopen.mem_nhds hx)
      (fun y hy => hfg y hy))

private theorem reduction_eq_partialFraction (x : ℝ) (hx : x ∈ branch) :
    reductionIntegrand x = partialFractionIntegrand x := by
  have h1 : 1 + x ≠ 0 := ne_of_gt (branch_add_one_pos hx)
  have hx1 : x + 1 ≠ 0 := by
    simpa [add_comm] using h1
  have hq : q x ≠ 0 := ne_of_gt (q_pos x)
  have hpoly : 1 + x + x ^ 2 ≠ 0 := by
    simpa [q] using hq
  unfold reductionIntegrand partialFractionIntegrand q
  field_simp [h1, hx1, hpoly]
  ring

private theorem final_kernel_relation (x : ℝ) (hx : x ∈ branch) :
    2 * (reductionIntegrand x + 1 / (1 + x)) =
      (2 * x + 1) / q x + 3 / q x := by
  have h1 : 1 + x ≠ 0 := ne_of_gt (branch_add_one_pos hx)
  have hx1 : x + 1 ≠ 0 := by
    simpa [add_comm] using h1
  have hq : q x ≠ 0 := ne_of_gt (q_pos x)
  have hpoly : 1 + x + x ^ 2 ≠ 0 := by
    simpa [q] using hq
  unfold reductionIntegrand q
  field_simp [h1, hx1, hpoly]
  ring

private theorem half_final_kernel_relation (x : ℝ) (hx : x ∈ branch) :
    (1 / 2 : ℝ) * ((2 * x + 1) / q x + 3 / q x) - 1 / (1 + x) =
      reductionIntegrand x := by
  have h := final_kernel_relation x hx
  linarith

private theorem log_abs_add_one_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.log |1 + y|) (1 / (1 + x)) x := by
  have h1 : 1 + x ≠ 0 := ne_of_gt (branch_add_one_pos hx)
  have hbase : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa [add_comm] using (hasDerivAt_id x).add_const 1
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    simpa [Function.comp_def, one_div] using
      (Real.hasDerivAt_log h1).comp x hbase
  apply hasDerivAt_of_eqOn_branch hx _ hlog
  intro y hy
  rw [abs_of_pos (branch_add_one_pos hy)]

private theorem reductionFamily_eq_finalReductionFamily :
    ReductionFamily = FinalReductionFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => 2 * (G y + Real.log |1 + y|), ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => 2 * (G y + Real.log |1 + y|))
          ((2 * x + 1) / q x + 3 / q x) x
      change ∀ x ∈ branch, HasDerivAt G (reductionIntegrand x) x at hG
      intro x hx
      have hd :
          HasDerivAt (fun y => 2 * (G y + Real.log |1 + y|))
            (2 * (reductionIntegrand x + 1 / (1 + x))) x := by
        simpa using
          ((hG x hx).add (log_abs_add_one_hasDerivAt x hx)).const_mul 2
      rw [final_kernel_relation x hx] at hd
      exact hd
    · intro x hx
      rw [hFG x hx]
      ring
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => (1 / 2 : ℝ) * G y - Real.log |1 + y|, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => (1 / 2 : ℝ) * G y - Real.log |1 + y|)
          (reductionIntegrand x) x
      change ∀ x ∈ branch,
        HasDerivAt G ((2 * x + 1) / q x + 3 / q x) x at hG
      intro x hx
      have hd :
          HasDerivAt (fun y => (1 / 2 : ℝ) * G y - Real.log |1 + y|)
            ((1 / 2 : ℝ) * ((2 * x + 1) / q x + 3 / q x) -
              1 / (1 + x)) x := by
        simpa using
          ((hG x hx).const_mul (1 / 2 : ℝ)).sub
            (log_abs_add_one_hasDerivAt x hx)
      rw [half_final_kernel_relation x hx] at hd
      exact hd
    · intro x hx
      rw [hFG x hx]
      ring

private theorem sqrt_three_pos : 0 < Real.sqrt 3 := by
  exact Real.sqrt_pos.2 (by norm_num)

private theorem arctan_term_hasDerivAt (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.sqrt 3 * Real.arctan ((2 * y + 1) / Real.sqrt 3))
      (3 / (2 * q x)) x := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt_three_pos
  have hs_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : q x ≠ 0 := ne_of_gt (q_pos x)
  have haff : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 1
  have hinner :
      HasDerivAt (fun y : ℝ => (2 * y + 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    simpa using haff.div_const (Real.sqrt 3)
  have hd :=
    ((Real.hasDerivAt_arctan ((2 * x + 1) / Real.sqrt 3)).comp x hinner).const_mul
      (Real.sqrt 3)
  have hden : 1 + ((2 * x + 1) / Real.sqrt 3) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ((2 * x + 1) / Real.sqrt 3)]
  have hval :
      Real.sqrt 3 *
          (1 / (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2) *
            (2 / Real.sqrt 3)) =
        3 / (2 * q x) := by
    field_simp [hs, hq, hden] <;>
      unfold q <;>
      nlinarith [hs_sq]
  rw [hval] at hd
  simpa [Function.comp_def] using hd

private theorem primitiveLong_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveLong (integrand x) x := by
  have h1 : 1 + x ≠ 0 := ne_of_gt (branch_add_one_pos hx)
  have hx1 : x + 1 ≠ 0 := by
    simpa [add_comm] using h1
  have hq : q x ≠ 0 := ne_of_gt (q_pos x)
  have hpoly : 1 + x + x ^ 2 ≠ 0 := by
    simpa [q] using hq
  have hd0 :=
    (((quotient_hasDerivAt x hx).neg.add
      ((log_q_hasDerivAt x).const_mul (1 / 2 : ℝ))).add
      (arctan_term_hasDerivAt x)).sub
      (log_abs_add_one_hasDerivAt x hx)
  have hd :
      HasDerivAt
        (fun y =>
          -(Real.log (q y) / (1 + y)) +
            (1 / 2 : ℝ) * Real.log (q y) +
            Real.sqrt 3 * Real.arctan ((2 * y + 1) / Real.sqrt 3) -
            Real.log |1 + y|)
        (-(reductionIntegrand x - integrand x) +
          (1 / 2 : ℝ) * ((2 * x + 1) / q x) +
          3 / (2 * q x) - 1 / (1 + x)) x := by
    simpa using hd0
  have hfun :
      (fun y =>
        -(Real.log (q y) / (1 + y)) +
          (1 / 2 : ℝ) * Real.log (q y) +
          Real.sqrt 3 * Real.arctan ((2 * y + 1) / Real.sqrt 3) -
          Real.log |1 + y|) = primitiveLong := by
    funext y
    unfold primitiveLong
    ring
  rw [hfun] at hd
  have hval :
      -(reductionIntegrand x - integrand x) +
          (1 / 2 : ℝ) * ((2 * x + 1) / q x) +
          3 / (2 * q x) - 1 / (1 + x) =
        integrand x := by
    unfold reductionIntegrand integrand q
    field_simp [h1, hx1, hpoly]
    ring
  rw [hval] at hd
  exact hd

private theorem antiderivatives_eq_primitive
    {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (f x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) branch := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      simpa using ((hF x hx).sub (hp x hx)).deriv
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ)))
    have hconn : IsPreconnected branch := by
      simpa [branch] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (-1 : ℝ)))
    refine ⟨F 0 - p 0, ?_⟩
    intro x hx
    have hzero_mem : (0 : ℝ) ∈ branch := by
      simp [branch]
    have heq : F x - p x = F 0 - p 0 := by
      exact hopen.is_const_of_deriv_eq_zero hconn hdiff hzero hx hzero_mem
    linarith
  · rintro ⟨C, hFC⟩
    change ∀ x ∈ branch, HasDerivAt F (f x) x
    intro x hx
    exact hasDerivAt_of_eqOn_branch hx (fun y hy => hFC y hy)
      ((hp x hx).add_const C)

private theorem primitiveFamily_congr {p r : ℝ → ℝ}
    (hpr : ∀ x ∈ branch, p x = r x) :
    PrimitiveFamily p = PrimitiveFamily r := by
  ext F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← hpr x hx]
    exact hF x hx
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hpr x hx]
    exact hF x hx

private theorem primitiveLong_eq_primitiveFinal (x : ℝ) (hx : x ∈ branch) :
    primitiveLong x = primitiveFinal x := by
  have h1p : 0 < 1 + x := branch_add_one_pos hx
  have h1 : 1 + x ≠ 0 := ne_of_gt h1p
  have hq : q x ≠ 0 := ne_of_gt (q_pos x)
  have hpow : (1 + x) ^ 2 ≠ 0 := pow_ne_zero 2 h1
  unfold primitiveLong primitiveFinal
  rw [abs_of_pos h1p, Real.log_div hpow hq, Real.log_pow]
  ring

theorem gap1 :
    AntiderivativesOn integrand = ByPartsFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt G
          (Real.log (q x) * deriv (fun y : ℝ => 1 / (1 + y)) x) x) ∧
      ∀ x ∈ branch, F x = -G x
    refine ⟨fun y => -F y, ?_, ?_⟩
    · intro x hx
      have hr := (reciprocal_hasDerivAt x hx).deriv
      have hval :
          Real.log (q x) * deriv (fun y : ℝ => 1 / (1 + y)) x =
            -integrand x := by
        rw [hr]
        unfold integrand
        ring
      rw [hval]
      simpa using (hF x hx).neg
    · intro x hx
      simp
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hr := (reciprocal_hasDerivAt x hx).deriv
    have hval :
        Real.log (q x) * deriv (fun y : ℝ => 1 / (1 + y)) x =
          -integrand x := by
      rw [hr]
      unfold integrand
      ring
    have hd := (hG x hx).neg
    rw [hval] at hd
    have hd' : HasDerivAt (fun y => -G y) (integrand x) x := by
      simpa using hd
    exact hasDerivAt_of_eqOn_branch hx (fun y hy => hFG y hy) hd'
theorem gap2 :
    AntiderivativesOn integrand = ReductionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn reductionIntegrand,
      ∀ x ∈ branch, F x = -Real.log (q x) / (1 + x) + G x
    refine ⟨fun y => F y + Real.log (q y) / (1 + y), ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => F y + Real.log (q y) / (1 + y))
          (reductionIntegrand x) x
      intro x hx
      have hd := (hF x hx).add (quotient_hasDerivAt x hx)
      have hval :
          integrand x + (reductionIntegrand x - integrand x) =
            reductionIntegrand x := by
        ring
      rw [hval] at hd
      exact hd
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    change ∀ x ∈ branch, HasDerivAt G (reductionIntegrand x) x at hG
    intro x hx
    have hd0 := (quotient_hasDerivAt x hx).neg.add (hG x hx)
    have hd :
        HasDerivAt
          (fun y => -(Real.log (q y) / (1 + y)) + G y)
          (-(reductionIntegrand x - integrand x) + reductionIntegrand x) x := by
      simpa using hd0
    have hval :
        -(reductionIntegrand x - integrand x) + reductionIntegrand x =
          integrand x := by
      ring
    rw [hval] at hd
    have hd' :
        HasDerivAt
          (fun y => -Real.log (q y) / (1 + y) + G y)
          (integrand x) x := by
      simpa only [neg_div] using hd
    exact hasDerivAt_of_eqOn_branch hx (fun y hy => hFG y hy) hd'
theorem gap3 :
    ReductionFamily = PartialFractionFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    change ∀ x ∈ branch, HasDerivAt G (reductionIntegrand x) x at hG
    change ∀ x ∈ branch, HasDerivAt G (partialFractionIntegrand x) x
    intro x hx
    rw [← reduction_eq_partialFraction x hx]
    exact hG x hx
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    change ∀ x ∈ branch, HasDerivAt G (partialFractionIntegrand x) x at hG
    change ∀ x ∈ branch, HasDerivAt G (reductionIntegrand x) x
    intro x hx
    rw [reduction_eq_partialFraction x hx]
    exact hG x hx
theorem gap4 :
    AntiderivativesOn integrand = PartialFractionFamily := by
  exact gap2.trans gap3
theorem gap5 :
    AntiderivativesOn integrand = FinalReductionFamily := by
  exact gap2.trans reductionFamily_eq_finalReductionFamily
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveLong := by
  exact antiderivatives_eq_primitive primitiveLong_hasDerivAt
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveFinal := by
  calc
    AntiderivativesOn integrand = PrimitiveFamily primitiveLong := gap6
    _ = PrimitiveFamily primitiveFinal :=
      primitiveFamily_congr primitiveLong_eq_primitiveFinal

end
end ProofGap.Exercise2139
