import ProofGapLean.Prelude.Elementary
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3364_1

noncomputable section

def circleFunction (n : ℕ) (x : ℝ) : ℝ :=
  if x = 1 / (n : ℝ) then
    -Real.sqrt (1 - x ^ 2)
  else
    Real.sqrt (1 - x ^ 2)

def IsCircleSolution (y : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 + y x ^ 2 = 1

def positiveNaturals : Type :=
  {n : ℕ // 0 < n}

private theorem circleFunction_ne_of_one_lt
    {n m : ℕ} (hn : 1 < n) (hm : 0 < m) (hne : n ≠ m) :
    circleFunction n ≠ circleFunction m := by
  intro hfun
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hnposR : (0 : ℝ) < (n : ℝ) := by
    linarith
  have hmposR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnposR
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmposR
  have hrecip : (1 / (n : ℝ)) ≠ 1 / (m : ℝ) := by
    intro h
    have hcross : (1 : ℝ) * (m : ℝ) = 1 * (n : ℝ) :=
      (div_eq_div_iff hn0 hm0).mp h
    have hnmR : (n : ℝ) = (m : ℝ) := by
      linarith
    apply hne
    exact_mod_cast hnmR
  have hxpos : (0 : ℝ) < 1 / (n : ℝ) :=
    div_pos zero_lt_one hnposR
  have hxlt : (1 : ℝ) / (n : ℝ) < 1 :=
    (div_lt_one hnposR).2 hnR
  have hprod :
      0 < (1 - 1 / (n : ℝ)) * (1 + 1 / (n : ℝ)) :=
    mul_pos (sub_pos.mpr hxlt) (by linarith)
  have hrad : 0 < 1 - (1 / (n : ℝ)) ^ 2 := by
    nlinarith [hprod]
  have hval := congrFun hfun (1 / (n : ℝ))
  have hleft :
      circleFunction n (1 / (n : ℝ)) =
        -Real.sqrt (1 - (1 / (n : ℝ)) ^ 2) := by
    unfold circleFunction
    rw [if_pos rfl]
  have hright :
      circleFunction m (1 / (n : ℝ)) =
        Real.sqrt (1 - (1 / (n : ℝ)) ^ 2) := by
    unfold circleFunction
    rw [if_neg hrecip]
  rw [hleft, hright] at hval
  have hsqrt : 0 < Real.sqrt (1 - (1 / (n : ℝ)) ^ 2) :=
    Real.sqrt_pos.2 hrad
  linarith

theorem gap1 :
    ∀ n : ℕ, 0 < n → IsCircleSolution (circleFunction n) := by
  intro n hn x hx
  have hprod : 0 ≤ (1 - x) * (1 + x) :=
    mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1])
  have hrad : 0 ≤ 1 - x ^ 2 := by
    nlinarith [hprod]
  unfold circleFunction
  split_ifs <;> nlinarith [Real.sq_sqrt hrad]

theorem gap2 :
    Function.Injective
        (fun n : positiveNaturals => circleFunction n.1) ∧
      Set.Infinite {y : ℝ → ℝ | IsCircleSolution y} := by
  have hinj :
      Function.Injective (fun n : positiveNaturals => circleFunction n.1) := by
    intro a b hfun
    apply Subtype.ext
    by_contra hne
    by_cases ha : a.1 = 1
    · have hbne : b.1 ≠ 1 := by
        intro hb
        apply hne
        exact ha.trans hb.symm
      have hbgt : 1 < b.1 :=
        lt_of_le_of_ne b.property (Ne.symm hbne)
      exact
        (circleFunction_ne_of_one_lt hbgt a.property (Ne.symm hne)) hfun.symm
    · have hagt : 1 < a.1 :=
        lt_of_le_of_ne a.property (Ne.symm ha)
      exact
        (circleFunction_ne_of_one_lt hagt b.property hne) hfun
  refine ⟨hinj, ?_⟩
  have hsucc_inj :
      Function.Injective (fun n : ℕ => circleFunction n.succ) := by
    intro n m hnm
    have hsub :
        (⟨n.succ, Nat.succ_pos n⟩ : positiveNaturals) =
          (⟨m.succ, Nat.succ_pos m⟩ : positiveNaturals) :=
      @hinj
        (⟨n.succ, Nat.succ_pos n⟩ : positiveNaturals)
        (⟨m.succ, Nat.succ_pos m⟩ : positiveNaturals)
        hnm
    exact Nat.succ.inj (congrArg Subtype.val hsub)
  have hrange :
      Set.Infinite (Set.range (fun n : ℕ => circleFunction n.succ)) :=
    Set.infinite_range_of_injective hsucc_inj
  exact hrange.mono (by
    rintro y ⟨n, rfl⟩
    exact gap1 n.succ (Nat.succ_pos n))

end

end ProofGap.Exercise3364_1
