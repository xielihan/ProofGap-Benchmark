import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3105_3

noncomputable section

open Filter
open scoped BigOperators Topology

def admissible (x : ℝ) : Prop :=
  ∀ m : ℕ, x ≠ -(m : ℝ)

def eulerApproximant (x : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * Real.rpow n x /
    (x * ∏ k ∈ Finset.Icc 1 n, (x + k))

def shiftedApproximant (x : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * Real.rpow n (x + 1) /
    (∏ k ∈ Finset.Icc 1 (n + 1), (x + k))

def quotientApproximant (x : ℝ) (n : ℕ) : ℝ :=
  shiftedApproximant x n / eulerApproximant x n

def simplifiedQuotient (x : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * x / (x + n + 1)

/--
Exercise 3105_3, gap 1; both Euler limits are named
explicitly and restricted to the non-pole domain.
-/
private lemma product_relations (x : ℝ) (n : ℕ) :
    ((∏ k ∈ Finset.Icc 1 (n + 1), (x + (k : ℝ))) =
        (x + 1) * ∏ k ∈ Finset.Icc 1 n, (x + 1 + (k : ℝ))) ∧
      ((∏ k ∈ Finset.Icc 1 (n + 1), (x + (k : ℝ))) =
        (∏ k ∈ Finset.Icc 1 n, (x + (k : ℝ))) *
          (x + (n : ℝ) + 1)) := by
  have hsucc : ∀ (y : ℝ) (m : ℕ),
      (∏ k ∈ Finset.Icc 1 (m + 1), (y + (k : ℝ))) =
        (∏ k ∈ Finset.Icc 1 m, (y + (k : ℝ))) *
          (y + (m : ℝ) + 1) := by
    intro y m
    have hIcc :
        Finset.Icc 1 (m + 1) =
          insert (m + 1) (Finset.Icc 1 m) := by
      apply Finset.ext
      intro k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by
      intro hmem
      have hle : m + 1 ≤ m := (Finset.mem_Icc.mp hmem).2
      omega
    rw [hIcc, Finset.prod_insert hnot]
    norm_num [Nat.cast_add, Nat.cast_one] <;> ring
  constructor
  · induction n with
    | zero =>
        rw [hsucc x 0]
        norm_num
    | succ n ih =>
        rw [hsucc x (n + 1), hsucc (x + 1) n, ih]
        norm_num [Nat.cast_add, Nat.cast_one] <;> ring
  · exact hsucc x n

theorem gap1 (Gamma : ℝ → ℝ)
    (hGamma :
      ∀ x : ℝ, admissible x →
        Tendsto (eulerApproximant x) atTop (𝓝 (Gamma x))) :
    ∀ x : ℝ, admissible x →
      Tendsto (shiftedApproximant x) atTop (𝓝 (Gamma (x + 1))) ∧
      Tendsto (eulerApproximant x) atTop (𝓝 (Gamma x)) := by
  intro x hx
  have hxshift : admissible (x + 1) := by
    intro m h
    apply hx (m + 1)
    norm_num [Nat.cast_add, Nat.cast_one] at h ⊢
    linarith
  have hshift :
      shiftedApproximant x = eulerApproximant (x + 1) := by
    funext n
    unfold shiftedApproximant eulerApproximant
    rw [(product_relations x n).1]
  constructor
  · rw [hshift]
    exact hGamma (x + 1) hxshift
  · exact hGamma x hx

/--
Exercise 3105_3, gap 2; division of limits requires the
denominator limit to be nonzero.
-/
theorem gap2 (Gamma : ℝ → ℝ) (x : ℝ)
    (hx : admissible x)
    (hnum : Tendsto (shiftedApproximant x) atTop (𝓝 (Gamma (x + 1))))
    (hden : Tendsto (eulerApproximant x) atTop (𝓝 (Gamma x)))
    (hGamma0 : Gamma x ≠ 0) :
    Tendsto (quotientApproximant x) atTop
      (𝓝 (Gamma (x + 1) / Gamma x)) := by
  simpa only [quotientApproximant] using hnum.div hden hGamma0

/-- Exercise 3105_3, gap 3; cancel only on the non-pole domain. -/
theorem gap3 (Gamma : ℝ → ℝ) (x : ℝ)
    (hx : admissible x)
    (hquot :
      Tendsto (quotientApproximant x) atTop
        (𝓝 (Gamma (x + 1) / Gamma x))) :
    Tendsto (simplifiedQuotient x) atTop
      (𝓝 (Gamma (x + 1) / Gamma x)) := by
  have heq :
      quotientApproximant x =ᶠ[atTop] simplifiedQuotient x := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnposNat : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnposNat
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hxk : ∀ k : ℕ, x + (k : ℝ) ≠ 0 := by
      intro k hk
      apply hx k
      linarith
    have hx0 : x ≠ 0 := by
      simpa using hxk 0
    have hlast0 : x + (n : ℝ) + 1 ≠ 0 := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hxk (n + 1)
    have hprod0 :
        (∏ k ∈ Finset.Icc 1 n, (x + (k : ℝ))) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact hxk k
    have hfact0 : (Nat.factorial n : ℝ) ≠ 0 := by
      positivity
    have hpow0 : Real.rpow (n : ℝ) x ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hnpos x)
    have hrpow :
        Real.rpow (n : ℝ) (x + 1) =
          Real.rpow (n : ℝ) x * (n : ℝ) := by
      simpa only [Real.rpow_one] using
        (Real.rpow_add hnpos x (1 : ℝ))
    unfold quotientApproximant shiftedApproximant eulerApproximant
      simplifiedQuotient
    rw [(product_relations x n).2, hrpow]
    field_simp [hfact0, hpow0, hx0, hprod0, hlast0] <;> ring
  exact (tendsto_congr' heq).mp hquot

/-- Exercise 3105_3, gap 4; the simplified quotient tends to `x`. -/
theorem gap4 (Gamma : ℝ → ℝ) (x : ℝ)
    (hx : admissible x)
    (hGamma :
      ∀ z : ℝ, admissible z →
        Tendsto (eulerApproximant z) atTop (𝓝 (Gamma z)))
    (hGamma0 : Gamma x ≠ 0) :
    Gamma (x + 1) / Gamma x = x := by
  obtain ⟨hnum, hden⟩ := gap1 Gamma hGamma x hx
  have hquotient := gap2 Gamma x hx hnum hden hGamma0
  have hfromQuotient := gap3 Gamma x hx hquotient
  have hnat :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_inv_atTop_zero.comp hnat
  have hsmall :
      Tendsto (fun n : ℕ => (x + 1) * (n : ℝ)⁻¹)
        atTop (nhds (0 : ℝ)) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => x + 1) atTop (nhds (x + 1))).mul hinv)
  have hunit :
      Tendsto (fun n : ℕ => 1 + (x + 1) * (n : ℝ)⁻¹)
        atTop (nhds (1 : ℝ)) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (1 : ℝ))).add hsmall)
  have hratio :
      Tendsto (fun n : ℕ => x / (1 + (x + 1) * (n : ℝ)⁻¹))
        atTop (nhds x) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => x) atTop (nhds x)).div hunit
            (by norm_num : (1 : ℝ) ≠ 0))
  have heq :
      (fun n : ℕ => x / (1 + (x + 1) * (n : ℝ)⁻¹)) =ᶠ[atTop]
        simplifiedQuotient x := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnposNat : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnposNat
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hsum0 : x + (n : ℝ) + 1 ≠ 0 := by
      intro hzero
      apply hx (n + 1)
      norm_num [Nat.cast_add, Nat.cast_one] at hzero ⊢
      linarith
    have hdenEq :
        1 + (x + 1) * (n : ℝ)⁻¹ =
          (x + (n : ℝ) + 1) / (n : ℝ) := by
      field_simp [hn0] <;> ring
    unfold simplifiedQuotient
    rw [hdenEq]
    field_simp [hn0, hsum0] <;> ring
  have hsimplified :
      Tendsto (simplifiedQuotient x) atTop (nhds x) :=
    (tendsto_congr' heq).mp hratio
  exact tendsto_nhds_unique hfromQuotient hsimplified

/-- Exercise 3105_3, gap 5; multiply by the nonzero denominator. -/
theorem gap5 (Gamma : ℝ → ℝ) (x : ℝ)
    (hx : admissible x)
    (hGamma0 : Gamma x ≠ 0)
    (hquot : Gamma (x + 1) / Gamma x = x) :
    Gamma (x + 1) = x * Gamma x := by
  exact (div_eq_iff hGamma0).mp hquot

/-- Exercise 3105_3, gap 6. -/
theorem gap6 (Gamma : ℝ → ℝ)
    (hGamma :
      ∀ z : ℝ, admissible z →
        Tendsto (eulerApproximant z) atTop (𝓝 (Gamma z)))
    (hGamma0 : ∀ z : ℝ, admissible z → Gamma z ≠ 0) :
    ∀ x : ℝ, admissible x →
      Gamma (x + 1) = x * Gamma x := by
  intro x hx
  exact gap5 Gamma x hx (hGamma0 x hx)
    (gap4 Gamma x hx hGamma (hGamma0 x hx))

end

end ProofGap.Exercise3105_3
