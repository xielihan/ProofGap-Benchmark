import ProofGapLean.Prelude.Core
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise3365_5

noncomputable section

abbrev LocalInterval (δ : ℝ) :=
  {x : ℝ // x ∈ Set.Ioo (1 - δ) (1 + δ)}

def localIdentity (δ : ℝ) (x : LocalInterval δ) : ℝ :=
  x

def hasValueAtOne (δ : ℝ) (y : LocalInterval δ → ℝ) : Prop :=
  ∀ p : LocalInterval δ, (p : ℝ) = 1 → y p = 1

def IsLocalSolution (δ : ℝ) (y : LocalInterval δ → ℝ) : Prop :=
  Continuous y ∧
    (∀ x : LocalInterval δ, (x : ℝ) ^ 2 = y x ^ 2) ∧
      hasValueAtOne δ y

def localSolutions (δ : ℝ) : Set (LocalInterval δ → ℝ) :=
  {y | IsLocalSolution δ y}

theorem gap1 (δ : ℝ) (hδpos : 0 < δ) (hδsmall : δ ≤ 1) :
    localSolutions δ = {localIdentity δ} := by
  apply Set.ext
  intro y
  constructor
  · intro hy
    change IsLocalSolution δ y at hy
    rcases hy with ⟨hcont, hsq, hvalue⟩
    let one : LocalInterval δ := ⟨1, by constructor <;> linarith⟩
    have hyone : y one = 1 := hvalue one (by rfl)
    have hfun : y = localIdentity δ := by
      funext x
      change y x = (x : ℝ)
      have hxpos : 0 < (x : ℝ) := by
        have hxlower := x.property.1
        linarith
      have hypos : 0 < y x := by
        by_contra hnot
        have hyle : y x ≤ 0 := le_of_not_gt hnot
        have hyne : y x ≠ 0 := by
          intro hyzero
          have heq := hsq x
          rw [hyzero] at heq
          nlinarith
        have hyneg : y x < 0 := lt_of_le_of_ne hyle hyne
        let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
        have hclamp_nonneg (t : ℝ) : 0 ≤ clamp t := by
          simp [clamp]
        have hclamp_le_one (t : ℝ) : clamp t ≤ 1 := by
          simp [clamp]
        let path : ℝ → LocalInterval δ := fun t =>
          ⟨(1 - clamp t) * (x : ℝ) + clamp t, by
            have hs0 : 0 ≤ clamp t := hclamp_nonneg t
            have hs1 : clamp t ≤ 1 := hclamp_le_one t
            by_cases hs : clamp t = 0
            · simpa [hs] using x.property
            · have hspos : 0 < clamp t :=
                lt_of_le_of_ne hs0 (Ne.symm hs)
              have hlow0 :
                  0 ≤ (1 - clamp t) * ((x : ℝ) - (1 - δ)) :=
                mul_nonneg (sub_nonneg.mpr hs1) (by linarith [x.property.1])
              have hlow1 :
                  0 < clamp t * (1 - (1 - δ)) :=
                mul_pos hspos (by linarith)
              have hupp0 :
                  0 ≤ (1 - clamp t) * ((1 + δ) - (x : ℝ)) :=
                mul_nonneg (sub_nonneg.mpr hs1) (by linarith [x.property.2])
              have hupp1 :
                  0 < clamp t * ((1 + δ) - 1) :=
                mul_pos hspos (by linarith)
              constructor <;> nlinarith⟩
        have hmincont : Continuous (fun t : ℝ => min 1 t) :=
          continuous_const.min continuous_id
        have hclampcont : Continuous clamp := by
          change Continuous (fun t : ℝ => max 0 (min 1 t))
          exact continuous_const.max hmincont
        have hvalcont : Continuous (fun t : ℝ =>
            (1 - clamp t) * (x : ℝ) + clamp t) :=
          ((continuous_const.sub hclampcont).mul continuous_const).add hclampcont
        have hpathcont : Continuous path := by
          exact hvalcont.subtype_mk (fun t => (path t).property)
        have hpath_zero : path 0 = x := by
          apply Subtype.ext
          simp [path, clamp]
        have hpath_one : path 1 = one := by
          apply Subtype.ext
          simp [path, clamp, one]
        let f : ℝ → ℝ := fun t => y (path t)
        have hfcont : Continuous f := by
          change Continuous (fun t : ℝ => y (path t))
          exact hcont.comp hpathcont
        have hfzero : f 0 = y x := by
          simpa [f] using congrArg y hpath_zero
        have hfone : f 1 = 1 := by
          calc
            f 1 = y one := by
              simpa [f] using congrArg y hpath_one
            _ = 1 := hyone
        have hzmem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
          rw [hfzero, hfone]
          constructor <;> linarith
        rcases (intermediate_value_Icc (f := f)
            (show (0 : ℝ) ≤ 1 by linarith) hfcont.continuousOn hzmem) with
          ⟨z, hzIcc, hzval⟩
        have hz : y (path z) = 0 := by
          simpa [f] using hzval
        have hzpos : 0 < ((path z : LocalInterval δ) : ℝ) := by
          have hzlower := (path z).property.1
          linarith
        have hzsq := hsq (path z)
        rw [hz] at hzsq
        nlinarith
      have heq := hsq x
      nlinarith
    simpa only [Set.mem_singleton_iff] using hfun
  · intro hy
    have hyid : y = localIdentity δ := by
      simpa only [Set.mem_singleton_iff] using hy
    subst y
    change IsLocalSolution δ (localIdentity δ)
    refine ⟨continuous_subtype_val, ?_, ?_⟩
    · intro x
      rfl
    · intro p hp
      exact hp

theorem gap2 (δ : ℝ) (hδpos : 0 < δ) (hδsmall : δ ≤ 1) :
    (localSolutions δ).ncard = 1 := by
  rw [gap1 δ hδpos hδsmall]
  simp

end

end ProofGap.Exercise3365_5
