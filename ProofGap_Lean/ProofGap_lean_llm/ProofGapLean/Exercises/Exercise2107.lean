import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2107
noncomputable section

def domain : Set ℝ := Set.Ioo 0 2
def t (x : ℝ) := 1 - x
def integrand (x : ℝ) := x * Real.arcsin (1 - x)
def squareDifferential (x : ℝ) :=
  Real.arcsin (1 - x) * deriv (fun y : ℝ => y ^ 2) x
def residual (x : ℝ) := x ^ 2 / Real.sqrt (1 - (1 - x) ^ 2)
def transformedResidual (x : ℝ) :=
  (-(1 - 2 * t x + t x ^ 2) / Real.sqrt (1 - t x ^ 2)) * deriv t x
def decomposedResidual (x : ℝ) :=
  ((1 - t x ^ 2) / Real.sqrt (1 - t x ^ 2) -
    2 / Real.sqrt (1 - t x ^ 2) +
    2 * t x / Real.sqrt (1 - t x ^ 2)) * deriv t x
def reducedResidual (x : ℝ) :=
  Real.sqrt (1 - t x ^ 2) * deriv t x
def residualPrimitiveInT (x : ℝ) :=
  t x / 2 * Real.sqrt (1 - t x ^ 2) -
    (3 / 2 : ℝ) * Real.arcsin (t x) - 2 * Real.sqrt (1 - t x ^ 2)
def residualPrimitiveInX (x : ℝ) :=
  (-3 - x) / 2 * Real.sqrt (2 * x - x ^ 2) -
    (3 / 2 : ℝ) * Real.arcsin (1 - x)
def primitive (x : ℝ) :=
  (2 * x ^ 2 - 3) / 4 * Real.arcsin (1 - x) -
    (3 + x) / 4 * Real.sqrt (2 * x - x ^ 2)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def HalfFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x ∈ domain, F x = (1 / 2 : ℝ) * A x}
def ByPartsFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family residual, ∀ x ∈ domain,
    F x = (1 / 2 : ℝ) * x ^ 2 * Real.arcsin (1 - x) + (1 / 2 : ℝ) * A x}
def DecompositionFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family decomposedResidual, ∀ x ∈ domain, F x = A x}
def ReducedFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family reducedResidual, ∀ x ∈ domain,
    F x = A x - 2 * Real.arcsin (t x) - 2 * Real.sqrt (1 - t x ^ 2)}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private lemma hasDerivAt_of_eqOn_domain {F A : ℝ → ℝ} {a x : ℝ}
    (hx : x ∈ domain) (hEq : ∀ y ∈ domain, F y = A y)
    (hA : HasDerivAt A a x) : HasDerivAt F a x := by
  have hn : Set.Ioo (0 : ℝ) 2 ∈ nhds x := by
    exact Ioo_mem_nhds hx.1 hx.2
  have heq : F =ᶠ[nhds x] A := by
    filter_upwards [hn] with y hy
    exact hEq y hy
  exact heq.hasDerivAt_iff.mpr hA

private lemma family_congr {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ domain, f x = g x) : Family f = Family g := by
  apply Set.ext
  intro F
  constructor
  · intro hF x hx
    rw [← hfg x hx]
    exact hF x hx
  · intro hF x hx
    rw [hfg x hx]
    exact hF x hx

private lemma deriv_t (x : ℝ) : deriv t x = -1 := by
  exact ((hasDerivAt_id x).const_sub 1).deriv

private lemma deriv_sq (x : ℝ) : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
  simpa using ((hasDerivAt_id x).pow 2).deriv

private lemma squareDifferential_eq (x : ℝ) :
    squareDifferential x = 2 * integrand x := by
  unfold squareDifferential integrand
  rw [deriv_sq]
  ring

private lemma t_mem_Ioo (x : ℝ) (hx : x ∈ domain) :
    t x ∈ Set.Ioo (-1 : ℝ) 1 := by
  unfold domain at hx
  unfold t
  constructor <;> linarith [hx.1, hx.2]

private lemma one_sub_t_sq_pos (x : ℝ) (hx : x ∈ domain) :
    0 < 1 - t x ^ 2 := by
  have ht := t_mem_Ioo x hx
  have hp : 0 < (1 - t x) * (1 + t x) :=
    mul_pos (sub_pos.mpr ht.2) (by linarith [ht.1])
  nlinarith

private lemma hasDerivAt_t (x : ℝ) : HasDerivAt t (-1) x := by
  simpa [t] using (hasDerivAt_id x).const_sub 1

private lemma hasDerivAt_arcsin_t (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => Real.arcsin (t y))
      (-1 / Real.sqrt (1 - t x ^ 2)) x := by
  have ht := t_mem_Ioo x hx
  have hn : t x ≠ -1 := ne_of_gt ht.1
  have hp : t x ≠ 1 := ne_of_lt ht.2
  have h := (Real.hasDerivAt_arcsin hn hp).comp x (hasDerivAt_t x)
  convert h using 1 <;> ring

private lemma hasDerivAt_sqrt_t (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => Real.sqrt (1 - t y ^ 2))
      (t x / Real.sqrt (1 - t x ^ 2)) x := by
  have hu : 1 - t x ^ 2 ≠ 0 := ne_of_gt (one_sub_t_sq_pos x hx)
  have hi : HasDerivAt (fun y => 1 - t y ^ 2) (2 * t x) x := by
    convert ((hasDerivAt_t x).pow 2).const_sub 1 using 1 <;> ring
  have h := (Real.hasDerivAt_sqrt hu).comp x hi
  have hs : Real.sqrt (1 - t x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (one_sub_t_sq_pos x hx))
  convert h using 1 <;> field_simp [hs] <;> ring

private lemma hasDerivAt_xsq_arcsin (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => y ^ 2 * Real.arcsin (1 - y))
      (2 * integrand x - residual x) x := by
  have h := ((hasDerivAt_id x).pow 2).mul (hasDerivAt_arcsin_t x hx)
  convert h using 1 <;>
    simp [integrand, residual, t] <;> ring

private lemma decomposedResidual_eq (x : ℝ) (hx : x ∈ domain) :
    decomposedResidual x = reducedResidual x +
      2 / Real.sqrt (1 - t x ^ 2) -
      2 * t x / Real.sqrt (1 - t x ^ 2) := by
  have hu : 0 ≤ 1 - t x ^ 2 := (one_sub_t_sq_pos x hx).le
  have hs : Real.sqrt (1 - t x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (one_sub_t_sq_pos x hx))
  have hsq := Real.sq_sqrt hu
  unfold decomposedResidual reducedResidual
  rw [deriv_t]
  field_simp [hs]
  nlinarith

private lemma hasDerivAt_sub_correction {A : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (reducedResidual x) x) (hx : x ∈ domain) :
    HasDerivAt
      (fun y => A y - 2 * Real.arcsin (t y) -
        2 * Real.sqrt (1 - t y ^ 2))
      (decomposedResidual x) x := by
  have ha := (hasDerivAt_arcsin_t x hx).const_mul 2
  have hs := (hasDerivAt_sqrt_t x hx).const_mul 2
  have h := (hA.sub ha).sub hs
  rw [decomposedResidual_eq x hx]
  convert h using 1 <;> ring

private lemma hasDerivAt_add_correction {F : ℝ → ℝ} {x : ℝ}
    (hF : HasDerivAt F (decomposedResidual x) x) (hx : x ∈ domain) :
    HasDerivAt
      (fun y => F y + 2 * Real.arcsin (t y) +
        2 * Real.sqrt (1 - t y ^ 2))
      (reducedResidual x) x := by
  have ha := (hasDerivAt_arcsin_t x hx).const_mul 2
  have hs := (hasDerivAt_sqrt_t x hx).const_mul 2
  have h := (hF.add ha).add hs
  rw [decomposedResidual_eq x hx] at h
  convert h using 1 <;> ring

private lemma family_eq_translates_of_hasDerivAt {f p : ℝ → ℝ}
    (hp : ∀ x ∈ domain, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C
    refine ⟨F 1 - p 1, ?_⟩
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) (Set.Ioo 0 2) := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ Set.Ioo (0 : ℝ) 2,
        deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      simpa using ((hF x hx).sub (hp x hx)).deriv
    intro x hx
    have h1 : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := by norm_num
    have heq : F x - p x = F 1 - p 1 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hdiff hzero hx h1
    linarith
  · rintro ⟨C, hEq⟩
    change ∀ x ∈ domain, HasDerivAt F (f x) x
    intro x hx
    apply hasDerivAt_of_eqOn_domain hx hEq
    exact (hp x hx).add_const C

private lemma hasDerivAt_residualPrimitiveInT (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt residualPrimitiveInT (residual x) x := by
  have ht := (hasDerivAt_t x).const_mul (1 / 2 : ℝ)
  have hs := hasDerivAt_sqrt_t x hx
  have ha := hasDerivAt_arcsin_t x hx
  have h := ((ht.mul hs).sub (ha.const_mul (3 / 2 : ℝ))).sub
    (hs.const_mul 2)
  have hs0 : Real.sqrt (1 - t x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (one_sub_t_sq_pos x hx))
  have hsq := Real.sq_sqrt (one_sub_t_sq_pos x hx).le
  have h' : HasDerivAt residualPrimitiveInT
      ((1 / 2 : ℝ) * -1 * Real.sqrt (1 - t x ^ 2) +
        (1 / 2 : ℝ) * t x *
          (t x / Real.sqrt (1 - t x ^ 2)) -
        (3 / 2 : ℝ) *
          (-1 / Real.sqrt (1 - t x ^ 2)) -
        2 * (t x / Real.sqrt (1 - t x ^ 2))) x := by
    convert h using 1
    · funext y
      simp [residualPrimitiveInT] <;> ring <;> simp
  have hxt : x = 1 - t x := by
    unfold t
    ring
  have hd : residual x =
      (1 / 2 : ℝ) * -1 * Real.sqrt (1 - t x ^ 2) +
        (1 / 2 : ℝ) * t x *
          (t x / Real.sqrt (1 - t x ^ 2)) -
        (3 / 2 : ℝ) *
          (-1 / Real.sqrt (1 - t x ^ 2)) -
        2 * (t x / Real.sqrt (1 - t x ^ 2)) := by
    unfold residual
    change x ^ 2 / Real.sqrt (1 - t x ^ 2) = _
    field_simp [hs0]
    nlinarith [hsq, hxt]
  rw [hd]
  exact h'

private lemma translates_congr {p q : ℝ → ℝ}
    (hpq : ∀ x ∈ domain, p x = q x) : Translates p = Translates q := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← hpq x hx]
    exact hF x hx
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hpq x hx]
    exact hF x hx

private lemma primitive_decomposition (x : ℝ) :
    (1 / 2 : ℝ) * x ^ 2 * Real.arcsin (1 - x) +
      (1 / 2 : ℝ) * residualPrimitiveInX x = primitive x := by
  unfold residualPrimitiveInX primitive
  ring

theorem gap1 : Family integrand = HalfFamily squareDifferential := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∃ A ∈ Family squareDifferential, ∀ x ∈ domain,
      F x = (1 / 2 : ℝ) * A x
    refine ⟨fun y => 2 * F y, ?_, ?_⟩
    · intro x hx
      rw [squareDifferential_eq]
      exact (hF x hx).const_mul 2
    · intro x hx
      ring
  · rintro ⟨A, hA, hEq⟩
    change ∀ x ∈ domain, HasDerivAt F (integrand x) x
    intro x hx
    apply hasDerivAt_of_eqOn_domain hx hEq
    have h := (hA x hx).const_mul (1 / 2 : ℝ)
    rw [squareDifferential_eq] at h
    convert h using 1 <;> ring
theorem gap2 : Family integrand = ByPartsFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∃ A ∈ Family residual, ∀ x ∈ domain,
      F x = (1 / 2 : ℝ) * x ^ 2 * Real.arcsin (1 - x) +
        (1 / 2 : ℝ) * A x
    refine ⟨fun y => 2 * F y - y ^ 2 * Real.arcsin (1 - y), ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).const_mul 2
      have hp := hasDerivAt_xsq_arcsin x hx
      convert h.sub hp using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨A, hA, hEq⟩
    change ∀ x ∈ domain, HasDerivAt F (integrand x) x
    intro x hx
    apply hasDerivAt_of_eqOn_domain hx hEq
    have hp := (hasDerivAt_xsq_arcsin x hx).const_mul (1 / 2 : ℝ)
    have hA' := (hA x hx).const_mul (1 / 2 : ℝ)
    convert hp.add hA' using 1
    · funext y
      simp <;> ring
    · ring
theorem gap3 : Family residual = Family transformedResidual := by
  apply family_congr
  intro x hx
  unfold residual transformedResidual
  rw [deriv_t]
  unfold t
  ring_nf
theorem gap4 : Family transformedResidual = DecompositionFamily := by
  calc
    Family transformedResidual = Family decomposedResidual := by
      apply family_congr
      intro x hx
      unfold transformedResidual decomposedResidual
      ring
    _ = DecompositionFamily := by
      apply Set.ext
      intro F
      constructor
      · intro hF
        exact ⟨F, hF, fun x hx => rfl⟩
      · rintro ⟨A, hA, hEq⟩
        intro x hx
        exact hasDerivAt_of_eqOn_domain hx hEq (hA x hx)
theorem gap5 : Family residual = DecompositionFamily := by
  exact gap3.trans gap4
theorem gap6 : Family residual = ReducedFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    have hDec : F ∈ DecompositionFamily := by
      rw [← gap5]
      exact hF
    rcases hDec with ⟨D, hD, hEqD⟩
    have hFD : F ∈ Family decomposedResidual := by
      intro x hx
      exact hasDerivAt_of_eqOn_domain hx hEqD (hD x hx)
    refine ⟨fun y => F y + 2 * Real.arcsin (t y) +
      2 * Real.sqrt (1 - t y ^ 2), ?_, ?_⟩
    · intro x hx
      exact hasDerivAt_add_correction (hFD x hx) hx
    · intro x hx
      ring
  · rintro ⟨A, hA, hEq⟩
    have hFD : F ∈ Family decomposedResidual := by
      intro x hx
      apply hasDerivAt_of_eqOn_domain hx hEq
      exact hasDerivAt_sub_correction (hA x hx) hx
    have hDec : F ∈ DecompositionFamily :=
      ⟨F, hFD, fun x hx => rfl⟩
    rw [← gap5] at hDec
    exact hDec
theorem gap7 : ReducedFamily = Translates residualPrimitiveInT := by
  rw [← gap6]
  exact family_eq_translates_of_hasDerivAt hasDerivAt_residualPrimitiveInT
theorem gap8 : Family residual = Translates residualPrimitiveInT := by
  exact gap6.trans gap7
theorem gap9 : Family residual = Translates residualPrimitiveInX := by
  calc
    Family residual = Translates residualPrimitiveInT := gap8
    _ = Translates residualPrimitiveInX := by
      apply translates_congr
      intro x hx
      unfold residualPrimitiveInT residualPrimitiveInX t
      ring_nf
theorem gap10 : Family integrand = Translates primitive := by
  rw [gap2]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨A, hA, hEq⟩
    have hAT : A ∈ Translates residualPrimitiveInX := by
      rw [← gap9]
      exact hA
    rcases hAT with ⟨C, hC⟩
    refine ⟨(1 / 2 : ℝ) * C, ?_⟩
    intro x hx
    rw [hEq x hx, hC x hx]
    calc
      (1 / 2 : ℝ) * x ^ 2 * Real.arcsin (1 - x) +
          (1 / 2 : ℝ) * (residualPrimitiveInX x + C) =
        ((1 / 2 : ℝ) * x ^ 2 * Real.arcsin (1 - x) +
          (1 / 2 : ℝ) * residualPrimitiveInX x) + (1 / 2 : ℝ) * C := by ring
      _ = primitive x + (1 / 2 : ℝ) * C := by
        rw [primitive_decomposition]
  · rintro ⟨C, hC⟩
    let A : ℝ → ℝ := fun y => residualPrimitiveInX y + 2 * C
    have hAT : A ∈ Translates residualPrimitiveInX := by
      exact ⟨2 * C, fun x hx => rfl⟩
    have hA : A ∈ Family residual := by
      rw [gap9]
      exact hAT
    refine ⟨A, hA, ?_⟩
    intro x hx
    rw [hC x hx]
    change primitive x + C =
      (1 / 2 : ℝ) * x ^ 2 * Real.arcsin (1 - x) +
        (1 / 2 : ℝ) * (residualPrimitiveInX x + 2 * C)
    calc
      primitive x + C =
          ((1 / 2 : ℝ) * x ^ 2 * Real.arcsin (1 - x) +
            (1 / 2 : ℝ) * residualPrimitiveInX x) + C := by
        rw [primitive_decomposition]
      _ = (1 / 2 : ℝ) * x ^ 2 * Real.arcsin (1 - x) +
          (1 / 2 : ℝ) * (residualPrimitiveInX x + 2 * C) := by ring

end
end ProofGap.Exercise2107
