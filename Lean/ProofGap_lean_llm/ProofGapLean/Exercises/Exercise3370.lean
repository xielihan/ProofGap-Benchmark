import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Real.Sign
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise3370

open Filter
open scoped Topology

noncomputable section

def forwardMap (k : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  k * t + φ t

def Assumptions (k ω : ℝ) (φ : ℝ → ℝ) : Prop :=
  k ≠ 0 ∧ 0 < ω ∧ Function.Periodic φ ω ∧
    Differentiable ℝ φ ∧ ∀ t, |deriv φ t| < |k|

def BoundedFunction (φ : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |φ t| ≤ M

def IsDifferentiableInverse (k : ℝ) (φ y : ℝ → ℝ) : Prop :=
  Differentiable ℝ y ∧
    Function.LeftInverse y (forwardMap k φ) ∧
      Function.RightInverse y (forwardMap k φ)

def periodicRemainder (k : ℝ) (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  y x - x / k

theorem gap1 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) :
    ∀ t, deriv (forwardMap k φ) t = k + deriv φ t := by
  intro t
  have hk : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hφ : HasDerivAt φ (deriv φ t) t :=
    h.2.2.2.1.differentiableAt.hasDerivAt
  simpa only [forwardMap] using (hk.add hφ).deriv

theorem gap2 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) :
    ∀ t, Real.sign (deriv (forwardMap k φ) t) = Real.sign k := by
  intro t
  rw [gap1 k ω φ h t]
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hb := h.2.2.2.2 t
    rw [abs_of_neg hk] at hb
    have hsum : k + deriv φ t < 0 := by
      linarith [(abs_lt.mp hb).2]
    rw [Real.sign_of_neg hsum, Real.sign_of_neg hk]
  · exact (h.1 hk).elim
  · have hb := h.2.2.2.2 t
    rw [abs_of_pos hk] at hb
    have hsum : 0 < k + deriv φ t := by
      linarith [(abs_lt.mp hb).1]
    rw [Real.sign_of_pos hsum, Real.sign_of_pos hk]

theorem gap3 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) :
    StrictMono (forwardMap k φ) ∨ StrictAnti (forwardMap k φ) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · right
    apply strictAnti_of_deriv_neg
    intro t
    rw [gap1 k ω φ h t]
    have hb := h.2.2.2.2 t
    rw [abs_of_neg hk] at hb
    linarith [(abs_lt.mp hb).2]
  · exact (h.1 hk).elim
  · left
    apply strictMono_of_deriv_pos
    intro t
    rw [gap1 k ω φ h t]
    have hb := h.2.2.2.2 t
    rw [abs_of_pos hk] at hb
    linarith [(abs_lt.mp hb).1]

theorem gap4 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) :
    Continuous (forwardMap k φ) := by
  unfold forwardMap
  have hk : Differentiable ℝ (fun t : ℝ => k * t) := by fun_prop
  exact (hk.add h.2.2.2.1).continuous

theorem gap5 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) :
    BoundedFunction φ := by
  have hb : Bornology.IsBounded (Set.range φ) :=
    h.2.2.1.isBounded_of_continuous (ne_of_gt h.2.1)
      h.2.2.2.1.continuous
  rcases hb.exists_norm_le with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  have ht := hC (φ t) ⟨t, rfl⟩
  rw [Real.norm_eq_abs] at ht
  exact ht.trans (le_max_left _ _)

theorem gap6 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) (hk : 0 < k) :
    Tendsto (forwardMap k φ) atBot atBot := by
  rcases gap5 k ω φ h with ⟨M, -, hM⟩
  have hlin : Tendsto (fun t : ℝ => k * t) atBot atBot :=
    (tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot).const_mul_atBot hk
  rw [tendsto_atBot]
  intro b
  filter_upwards [tendsto_atBot.1 hlin (b - M)] with t ht
  unfold forwardMap
  have hφ := (abs_le.mp (hM t)).2
  linarith

theorem gap7 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) (hk : 0 < k) :
    Tendsto (forwardMap k φ) atTop atTop := by
  rcases gap5 k ω φ h with ⟨M, -, hM⟩
  have hlin : Tendsto (fun t : ℝ => k * t) atTop atTop :=
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop hk
  rw [tendsto_atTop]
  intro b
  filter_upwards [tendsto_atTop.1 hlin (b + M)] with t ht
  unfold forwardMap
  have hφ := (abs_le.mp (hM t)).1
  linarith

theorem gap8 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) (hk : k < 0) :
    Tendsto (forwardMap k φ) atBot atTop := by
  rcases gap5 k ω φ h with ⟨M, -, hM⟩
  have hlin : Tendsto (fun t : ℝ => k * t) atBot atTop :=
    (tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot).const_mul_atBot_of_neg hk
  rw [tendsto_atTop]
  intro b
  filter_upwards [tendsto_atTop.1 hlin (b + M)] with t ht
  unfold forwardMap
  have hφ := (abs_le.mp (hM t)).1
  linarith

theorem gap9 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) (hk : k < 0) :
    Tendsto (forwardMap k φ) atTop atBot := by
  rcases gap5 k ω φ h with ⟨M, -, hM⟩
  have hlin : Tendsto (fun t : ℝ => k * t) atTop atBot :=
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop_of_neg hk
  rw [tendsto_atBot]
  intro b
  filter_upwards [tendsto_atBot.1 hlin (b - M)] with t ht
  unfold forwardMap
  have hφ := (abs_le.mp (hM t)).2
  linarith

theorem gap10 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) :
    ∃! y : ℝ → ℝ, IsDifferentiableInverse k φ y := by
  let F := forwardMap k φ
  have hFdiff : Differentiable ℝ F := by
    dsimp [F, forwardMap]
    have hk : Differentiable ℝ (fun t : ℝ => k * t) := by fun_prop
    exact hk.add h.2.2.2.1
  have hderiv_ne : ∀ t, deriv F t ≠ 0 := by
    intro t hzero
    apply h.1
    apply Real.sign_eq_zero_iff.mp
    rw [← gap2 k ω φ h t]
    simp only [F, hzero, Real.sign_zero]
  have buildInverse (y : ℝ → ℝ) (hycont : Continuous y)
      (hleft : Function.LeftInverse y F)
      (hright : Function.RightInverse y F) :
      IsDifferentiableInverse k φ y := by
    refine ⟨?_, hleft, hright⟩
    intro x
    have hF : HasDerivAt F (deriv F (y x)) (y x) :=
      hFdiff.differentiableAt.hasDerivAt
    exact (hF.of_local_left_inverse hycont.continuousAt
      (hderiv_ne (y x)) (Eventually.of_forall hright)).differentiableAt
  obtain ⟨y, hy⟩ :
      ∃ y : ℝ → ℝ, IsDifferentiableInverse k φ y := by
    rcases lt_trichotomy k 0 with hk | hk | hk
    · have ha : StrictAnti F := by
        apply strictAnti_of_deriv_neg
        intro t
        dsimp only [F]
        rw [gap1 k ω φ h t]
        have hb := h.2.2.2.2 t
        rw [abs_of_neg hk] at hb
        linarith [(abs_lt.mp hb).2]
      have hsurj : Function.Surjective F :=
        (gap4 k ω φ h).surjective' (gap8 k ω φ h hk)
          (gap9 k ω φ h hk)
      let G : ℝ → ℝ := fun x => -F x
      have hmG : StrictMono G := ha.neg
      have hsurjG : Function.Surjective G := by
        intro v
        rcases hsurj (-v) with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        dsimp only [G]
        rw [hx]
        ring
      let e : ℝ ≃o ℝ := hmG.orderIsoOfSurjective G hsurjG
      let y : ℝ → ℝ := fun x => e.symm (-x)
      have hycont : Continuous y := by
        have hecont : Continuous (fun x : ℝ => e.symm x) :=
          e.toHomeomorph.continuous_invFun
        exact hecont.comp continuous_neg
      have hleft : Function.LeftInverse y F := by
        intro x
        simpa [y, e, G] using
          StrictMono.orderIsoOfSurjective_symm_apply_self
            G hmG hsurjG x
      have hright : Function.RightInverse y F := by
        intro x
        dsimp only [y]
        have heq :=
          StrictMono.orderIsoOfSurjective_self_symm_apply
            G hmG hsurjG (-x)
        dsimp only [G] at heq
        linarith
      exact ⟨y, buildInverse y hycont hleft hright⟩
    · exact (h.1 hk).elim
    · have hm : StrictMono F := by
        apply strictMono_of_deriv_pos
        intro t
        dsimp only [F]
        rw [gap1 k ω φ h t]
        have hb := h.2.2.2.2 t
        rw [abs_of_pos hk] at hb
        linarith [(abs_lt.mp hb).1]
      have hsurj : Function.Surjective F :=
        (gap4 k ω φ h).surjective (gap7 k ω φ h hk)
          (gap6 k ω φ h hk)
      let e : ℝ ≃o ℝ := hm.orderIsoOfSurjective F hsurj
      let y : ℝ → ℝ := e.symm
      have hycont : Continuous y :=
        e.toHomeomorph.continuous_invFun
      have hleft : Function.LeftInverse y F := by
        intro x
        simpa [y, e] using
          StrictMono.orderIsoOfSurjective_symm_apply_self
            F hm hsurj x
      have hright : Function.RightInverse y F := by
        intro x
        simpa [y, e] using
          StrictMono.orderIsoOfSurjective_self_symm_apply
            F hm hsurj x
      exact ⟨y, buildInverse y hycont hleft hright⟩
  refine ⟨y, hy, ?_⟩
  intro z hz
  funext x
  calc
    z x = y (F (z x)) := (hy.2.1 (z x)).symm
    _ = y x := congrArg y (hz.2.2 x)

theorem gap11 (k ω : ℝ) (φ y : ℝ → ℝ)
    (h : Assumptions k ω φ) (hy : IsDifferentiableInverse k φ y) :
    ∀ x, x = k * y x + φ (y x) := by
  intro x
  simpa only [forwardMap] using (hy.2.2 x).symm

theorem gap12 (k ω : ℝ) (φ y : ℝ → ℝ)
    (h : Assumptions k ω φ) :
    ∀ x, φ (y x + ω) = φ (y x) := by
  intro x
  exact h.2.2.1 (y x)

theorem gap13 (k ω : ℝ) (φ y : ℝ → ℝ)
    (hy : ∀ x, x = k * y x + φ (y x)) :
    ∀ x, x + k * ω = k * y x + φ (y x) + k * ω := by
  intro x
  exact congrArg (fun a => a + k * ω) (hy x)

theorem gap14 (k ω : ℝ) (φ y : ℝ → ℝ)
    (hperiodic : Function.Periodic φ ω) :
    ∀ x,
      k * y x + φ (y x) + k * ω =
        k * (y x + ω) + φ (y x + ω) := by
  intro x
  rw [hperiodic (y x)]
  ring

theorem gap15 (k ω : ℝ) (φ y : ℝ → ℝ)
    (hy : ∀ x, x = k * y x + φ (y x))
    (hperiodic : Function.Periodic φ ω) :
    ∀ x, x + k * ω =
      k * (y x + ω) + φ (y x + ω) := by
  intro x
  exact (gap13 k ω φ y hy x).trans (gap14 k ω φ y hperiodic x)

theorem gap16 (k ω : ℝ) (φ y : ℝ → ℝ)
    (h : Assumptions k ω φ) (hy : IsDifferentiableInverse k φ y) :
    ∀ x, y (x + k * ω) = y x + ω := by
  intro x
  have hrel := gap15 k ω φ y (gap11 k ω φ y h hy) h.2.2.1 x
  calc
    y (x + k * ω) =
        y (forwardMap k φ (y x + ω)) := congrArg y hrel
    _ = y x + ω := hy.2.1 (y x + ω)

theorem gap17 (k : ℝ) (y : ℝ → ℝ) :
    ∀ x, periodicRemainder k y (x) =
      y x - x / k := by
  intro x
  rfl

theorem gap18 (k ω : ℝ) (y : ℝ → ℝ)
    (hk : k ≠ 0) (hyshift : ∀ x, y (x + k * ω) = y x + ω) :
    ∀ x,
      y (x + k * ω) - (x + k * ω) / k =
        y x - x / k := by
  intro x
  rw [hyshift x]
  field_simp [hk]
  ring

theorem gap19 (k : ℝ) (y : ℝ → ℝ) :
    ∀ x, y x - x / k = periodicRemainder k y x := by
  intro x
  rfl

theorem gap20 (k ω : ℝ) (y : ℝ → ℝ)
    (hk : k ≠ 0) (hyshift : ∀ x, y (x + k * ω) = y x + ω) :
    ∀ x,
      periodicRemainder k y (x + k * ω) =
        periodicRemainder k y x := by
  intro x
  exact gap18 k ω y hk hyshift x

theorem gap21 (k ω : ℝ) (y : ℝ → ℝ)
    (hk : k ≠ 0) (hyshift : ∀ x, y (x + k * ω) = y x + ω) :
    ∀ x,
      periodicRemainder k y (x - k * ω) =
        periodicRemainder k y x := by
  intro x
  have hx := (gap20 k ω y hk hyshift (x - k * ω)).symm
  convert hx using 1 <;> ring

theorem gap22 (k ω : ℝ) (φ y : ℝ → ℝ)
    (h : Assumptions k ω φ) (hy : IsDifferentiableInverse k φ y) :
    Function.Periodic (periodicRemainder k y) (|k| * ω) := by
  intro x
  have hyshift := gap16 k ω φ y h hy
  rcases lt_trichotomy k 0 with hk | hk | hk
  · convert gap21 k ω y h.1 hyshift x using 1 <;>
      simp [abs_of_neg hk] <;> ring
  · exact (h.1 hk).elim
  · simpa [abs_of_pos hk] using gap20 k ω y h.1 hyshift x

theorem gap23 (k : ℝ) (y : ℝ → ℝ) :
    ∀ x, y x = x / k + periodicRemainder k y x := by
  intro x
  unfold periodicRemainder
  ring

theorem gap24 (k ω : ℝ) (φ : ℝ → ℝ)
    (h : Assumptions k ω φ) :
    ∃ y ψ : ℝ → ℝ,
      IsDifferentiableInverse k φ y ∧
        Function.Periodic ψ (|k| * ω) ∧
          ∀ x, y x = x / k + ψ x := by
  rcases gap10 k ω φ h with ⟨y, hy, -⟩
  exact ⟨y, periodicRemainder k y, hy, gap22 k ω φ y h hy,
    gap23 k y⟩

end

end ProofGap.Exercise3370
