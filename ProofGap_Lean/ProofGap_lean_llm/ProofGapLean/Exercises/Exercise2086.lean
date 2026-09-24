import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2086
noncomputable section

def xOfT (t : ℝ) := 4 * Real.log t
def f (x : ℝ) :=
  (1 + Real.exp (x / 2)) / (1 + Real.exp (x / 4)) ^ 2
def tKernel (t : ℝ) := (1 + t ^ 2) / (t * (1 + t) ^ 2)
def partialKernel (t : ℝ) := 1 / t - 2 / (1 + t) ^ 2
def tPrimitive (t : ℝ) := 4 * Real.log t + 8 / (1 + t)
def xPrimitive (x : ℝ) := x + 8 / (1 + Real.exp (x / 4))
def Family (U : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def PullbackFamily (A : Set (ℝ → ℝ)) :=
  {G : ℝ → ℝ | ∃ F ∈ A, ∀ t ∈ Set.Ioi (0 : ℝ), G t = F (xOfT t)}
def ScaledFamily (g : ℝ → ℝ) :=
  {G : ℝ → ℝ | ∃ H ∈ Family (Set.Ioi 0) g, ∃ C,
    ∀ t ∈ Set.Ioi (0 : ℝ), G t = 4 * H t + C}
def TTranslates := {G : ℝ → ℝ | ∃ C,
  ∀ t ∈ Set.Ioi (0 : ℝ), G t = tPrimitive t + C}
def XTranslates := {F : ℝ → ℝ | ∃ C, ∀ x, F x = xPrimitive x + C}

private theorem hasDerivAt_xOfT (t : ℝ) (ht : 0 < t) :
    HasDerivAt xOfT (4 / t) t := by
  simpa [xOfT, div_eq_mul_inv] using
    (Real.hasDerivAt_log (ne_of_gt ht)).const_mul 4

private theorem kernel_eq (t : ℝ) (ht : 0 < t) :
    tKernel t = partialKernel t := by
  unfold tKernel partialKernel
  field_simp [ne_of_gt ht, ne_of_gt (add_pos zero_lt_one ht)] <;>
    ring_nf

private theorem f_xOfT_eq (t : ℝ) (ht : 0 < t) :
    f (xOfT t) = (1 + t ^ 2) / (1 + t) ^ 2 := by
  have hquarter : xOfT t / 4 = Real.log t := by
    unfold xOfT
    ring
  have hhalf : xOfT t / 2 = Real.log t + Real.log t := by
    unfold xOfT
    ring
  unfold f
  rw [hhalf, Real.exp_add, Real.exp_log ht, hquarter, Real.exp_log ht]
  ring_nf

private theorem hasDerivAt_xPrimitive (x : ℝ) :
    HasDerivAt xPrimitive (f x) x := by
  have hi := (hasDerivAt_id x).div_const 4
  have he := (Real.hasDerivAt_exp (x / 4)).comp x hi
  have hu := (hasDerivAt_const x (1 : ℝ)).add he
  have hne : 1 + Real.exp (x / 4) ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (Real.exp_pos _))
  have hsum :=
    (hasDerivAt_id x).add ((hu.inv hne).const_mul 8)
  have hexp : Real.exp (x / 2) = Real.exp (x / 4) ^ 2 := by
    rw [show x / 2 = x / 4 + x / 4 by ring, Real.exp_add]
    ring
  convert hsum using 1
  unfold f
  rw [hexp]
  simp only [Function.comp_apply, Pi.add_apply, Pi.inv_apply, id_eq]
  field_simp [hne] <;> ring_nf

private theorem hasDerivAt_tPrimitive (t : ℝ) (ht : 0 < t) :
    HasDerivAt tPrimitive (4 * partialKernel t) t := by
  have hne : 1 + t ≠ 0 := ne_of_gt (add_pos zero_lt_one ht)
  have hden := (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
  have h :=
    ((Real.hasDerivAt_log (ne_of_gt ht)).const_mul 4).add
      ((hden.inv hne).const_mul 8)
  convert h using 1
  unfold partialKernel
  simp only [Pi.add_apply, Pi.inv_apply, id_eq]
  field_simp [ne_of_gt ht, hne] <;> ring_nf

private theorem exists_const_eq_on_pos {p r q : ℝ → ℝ}
    (hp : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt p (q t) t)
    (hr : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt r (q t) t) :
    ∃ C, ∀ t ∈ Set.Ioi (0 : ℝ), p t = r t + C := by
  let d : ℝ → ℝ := fun t => p t - r t
  have hd : DifferentiableOn ℝ d (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact ((hp x hx).sub (hr x hx)).differentiableAt.differentiableWithinAt
  have hz : ∀ x ∈ Set.Ioi (0 : ℝ), deriv d x = 0 := by
    intro x hx
    have h := ((hp x hx).sub (hr x hx)).deriv
    simpa [d] using h
  refine ⟨d 1, ?_⟩
  intro x hx
  have hone : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    change (0 : ℝ) < 1
    exact zero_lt_one
  have hc : d x = d 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hd hz hx hone
  have hpr : p x - r x = d 1 := by
    change p x - r x = d 1 at hc
    exact hc
  change p x = r x + d 1
  calc
    p x = d 1 + r x := (sub_eq_iff_eq_add).mp hpr
    _ = r x + d 1 := add_comm _ _

private theorem exists_const_eq {p r q : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p (q x) x)
    (hr : ∀ x, HasDerivAt r (q x) x) :
    ∃ C, ∀ x, p x = r x + C := by
  let d : ℝ → ℝ := fun x => p x - r x
  have hd : Differentiable ℝ d := by
    intro x
    exact ((hp x).sub (hr x)).differentiableAt
  have hz : ∀ x, deriv d x = 0 := by
    intro x
    have h := ((hp x).sub (hr x)).deriv
    simpa [d] using h
  refine ⟨d 0, ?_⟩
  intro x
  have hc : d x = d 0 := is_const_of_deriv_eq_zero hd hz x 0
  have hpr : p x - r x = d 0 := by
    change p x - r x = d 0 at hc
    exact hc
  change p x = r x + d 0
  calc
    p x = d 0 + r x := (sub_eq_iff_eq_add).mp hpr
    _ = r x + d 0 := add_comm _ _

private theorem scaledFamily_congr {g h : ℝ → ℝ}
    (heq : ∀ t, 0 < t → g t = h t) :
    ScaledFamily g = ScaledFamily h := by
  ext G
  constructor
  · rintro ⟨H, hH, C, hG⟩
    refine ⟨H, ?_, C, hG⟩
    intro t ht
    rw [← heq t ht]
    exact hH t ht
  · rintro ⟨H, hH, C, hG⟩
    refine ⟨H, ?_, C, hG⟩
    intro t ht
    rw [heq t ht]
    exact hH t ht

private theorem xPrimitive_xOfT (t : ℝ) (ht : 0 < t) :
    xPrimitive (xOfT t) = tPrimitive t := by
  unfold xPrimitive tPrimitive
  rw [show xOfT t / 4 = Real.log t by unfold xOfT; ring,
    Real.exp_log ht]
  unfold xOfT
  rfl

theorem gap1 (t : ℝ) : xOfT t = 4 * Real.log t := by
  rfl
theorem gap2 (t : ℝ) (ht : 0 < t) :
    HasDerivAt xOfT (4 / t) t := by
  exact hasDerivAt_xOfT t ht
theorem gap3 :
    PullbackFamily (Family Set.univ f) = ScaledFamily tKernel := by
  ext G
  constructor
  · rintro ⟨F, hF, hG⟩
    let H : ℝ → ℝ := fun t => F (xOfT t) / 4
    refine ⟨H, ?_, 0, ?_⟩
    · intro t ht
      change 0 < t at ht
      have hc :=
        (hF (xOfT t) (Set.mem_univ _)).comp t (hasDerivAt_xOfT t ht)
      have hd := hc.div_const 4
      convert hd using 1
      rw [f_xOfT_eq t ht]
      unfold tKernel
      field_simp [ne_of_gt ht, ne_of_gt (add_pos zero_lt_one ht)] <;>
        ring_nf
    · intro t ht
      change 0 < t at ht
      dsimp [H]
      rw [hG t ht]
      ring
  · rintro ⟨H, hH, C, hG⟩
    let F : ℝ → ℝ := fun x => 4 * H (Real.exp (x / 4)) + C
    refine ⟨F, ?_, ?_⟩
    · intro x hx
      have hi :=
        (Real.hasDerivAt_exp (x / 4)).comp x
          ((hasDerivAt_id x).div_const 4)
      have hepos : 0 < Real.exp (x / 4) := Real.exp_pos _
      have hh := hH (Real.exp (x / 4)) hepos
      have hd := ((hh.comp x hi).const_mul 4).add_const C
      have hexp : Real.exp (x / 2) = Real.exp (x / 4) ^ 2 := by
        rw [show x / 2 = x / 4 + x / 4 by ring, Real.exp_add]
        ring
      convert hd using 1
      unfold f tKernel
      rw [hexp]
      field_simp [ne_of_gt hepos,
        ne_of_gt (add_pos zero_lt_one hepos)] <;>
        ring_nf
    · intro t ht
      change 0 < t at ht
      dsimp [F]
      rw [show xOfT t / 4 = Real.log t by unfold xOfT; ring,
        Real.exp_log ht]
      exact hG t ht
theorem gap4 :
    PullbackFamily (Family Set.univ f) = ScaledFamily partialKernel := by
  calc
    PullbackFamily (Family Set.univ f) = ScaledFamily tKernel := gap3
    _ = ScaledFamily partialKernel := by
      apply scaledFamily_congr
      intro t ht
      exact kernel_eq t ht
theorem gap5 : ScaledFamily partialKernel = TTranslates := by
  ext G
  constructor
  · rintro ⟨H, hH, C, hG⟩
    have hp : ∀ t ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun s => 4 * H s) (4 * partialKernel t) t := by
      intro t ht
      exact (hH t ht).const_mul 4
    have hr : ∀ t ∈ Set.Ioi (0 : ℝ),
        HasDerivAt tPrimitive (4 * partialKernel t) t := by
      intro t ht
      change 0 < t at ht
      exact hasDerivAt_tPrimitive t ht
    rcases exists_const_eq_on_pos hp hr with ⟨D, hD⟩
    refine ⟨D + C, ?_⟩
    intro t ht
    rw [hG t ht, hD t ht]
    ring
  · rintro ⟨C, hG⟩
    refine ⟨fun t => tPrimitive t / 4, ?_, C, ?_⟩
    · intro t ht
      change 0 < t at ht
      convert (hasDerivAt_tPrimitive t ht).div_const 4 using 1 <;> ring
    · intro t ht
      rw [hG t ht]
      ring
theorem gap6 : TTranslates = PullbackFamily XTranslates := by
  ext G
  constructor
  · rintro ⟨C, hG⟩
    let F : ℝ → ℝ := fun x => xPrimitive x + C
    refine ⟨F, ⟨C, ?_⟩, ?_⟩
    · intro x
      rfl
    · intro t ht
      change 0 < t at ht
      dsimp [F]
      rw [xPrimitive_xOfT t ht]
      exact hG t ht
  · rintro ⟨F, ⟨C, hF⟩, hG⟩
    refine ⟨C, ?_⟩
    intro t ht
    change 0 < t at ht
    calc
      G t = F (xOfT t) := hG t ht
      _ = xPrimitive (xOfT t) + C := hF (xOfT t)
      _ = tPrimitive t + C := by rw [xPrimitive_xOfT t ht]
theorem gap7 : Family Set.univ f = XTranslates := by
  ext F
  constructor
  · intro hF
    have hp : ∀ x, HasDerivAt F (f x) x := by
      intro x
      exact hF x (Set.mem_univ _)
    have hr : ∀ x, HasDerivAt xPrimitive (f x) x := by
      intro x
      exact hasDerivAt_xPrimitive x
    rcases exists_const_eq hp hr with ⟨C, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hF⟩
    have hfun : F = fun x => xPrimitive x + C := by
      funext x
      exact hF x
    rw [hfun]
    intro x hx
    exact (hasDerivAt_xPrimitive x).add_const C

end
end ProofGap.Exercise2086
