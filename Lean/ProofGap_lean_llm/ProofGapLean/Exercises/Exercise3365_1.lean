import ProofGapLean.Prelude.Core
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise3365_1

noncomputable section

def signFlip (n : ℕ) (x : ℝ) : ℝ :=
  if x = 1 / (n : ℝ) then -|x| else |x|

def IsSquareRootChoice (y : ℝ → ℝ) : Prop :=
  ∀ x, x ^ 2 = y x ^ 2

def positiveNaturals : Type :=
  {n : ℕ // 0 < n}

def squareRootChoices : Set (ℝ → ℝ) :=
  {y | IsSquareRootChoice y}

theorem gap1 :
    ∀ n : ℕ, 0 < n → IsSquareRootChoice (signFlip n) := by
  intro n hn x
  simp [signFlip, sq_abs]

theorem gap2 :
    Function.Injective (fun n : positiveNaturals => signFlip n.1) ∧
      Set.Infinite squareRootChoices := by
  have hinj : Function.Injective (fun n : positiveNaturals => signFlip n.1) := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have haR : (0 : ℝ) < (a.1 : ℝ) := Nat.cast_pos.mpr a.2
    have hv := congrFun hab (1 / (a.1 : ℝ))
    simp [signFlip] at hv
    have hv' := hv hne
    have hx : 0 < ((a.1 : ℝ)⁻¹) := inv_pos.mpr haR
    linarith [hv']
  constructor
  · exact hinj
  · have hinjNat : Function.Injective (fun n : ℕ => signFlip n.succ) := by
      intro a b hab
      have hs :
          (⟨a.succ, Nat.zero_lt_succ a⟩ : positiveNaturals) =
            ⟨b.succ, Nat.zero_lt_succ b⟩ := hinj hab
      exact Nat.succ.inj (congrArg Subtype.val hs)
    have hrange : Set.Infinite (Set.range (fun n : ℕ => signFlip n.succ)) :=
      Set.infinite_range_of_injective hinjNat
    refine hrange.mono ?_
    rintro y ⟨n, rfl⟩
    exact gap1 n.succ (Nat.zero_lt_succ n)

end

end ProofGap.Exercise3365_1
