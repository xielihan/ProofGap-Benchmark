import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise2747

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n - x ^ (n + 1)

def g (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n * (1 - x)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → (x = 0 ∨ x = 1) → term n x = 0 := by
  intro n x hn hx
  have hn0 : n ≠ 0 := by omega
  rcases hx with rfl | rfl <;> simp [term, hn0]

theorem gap2 :
    ∀ x : ℝ, 0 < x → x < 1 →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx hx1
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hx]
    exact hx1
  have hpow : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hmul := hpow.mul_const (1 - x)
  have heq : (fun n : ℕ => term n x) = (fun n : ℕ => x ^ n * (1 - x)) := by
    funext n
    unfold term
    rw [pow_succ]
    ring
  rw [heq]
  simpa using hmul

theorem gap3 :
    ∀ x : ℝ, 0 < x → x < 1 → (0 : ℝ) = 0 := by
  intro x hx hx1
  rfl

theorem gap4 :
    ∀ x : ℝ, 0 < x → x < 1 →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx hx1
  exact gap2 x hx hx1

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), 0 < x → x < 1 →
      |term n x - 0| = x ^ n - x ^ (n + 1) := by
  intro n x hx hx1
  have hp : 0 ≤ x ^ n := pow_nonneg (le_of_lt hx) n
  have hterm : 0 ≤ term n x := by
    unfold term
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hx1) hp
    simpa using hmul
  rw [sub_zero, abs_of_nonneg hterm]
  rfl

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), 0 < x → x < 1 →
      x ^ n - x ^ (n + 1) = g n x := by
  intro n x hx hx1
  unfold g
  rw [pow_succ]
  ring

theorem gap7 :
    ∀ (n : ℕ) (x : ℝ), 0 < x → x < 1 →
      |term n x - 0| = g n x := by
  intro n x hx hx1
  calc
    |term n x - 0| = x ^ n - x ^ (n + 1) := gap5 n x hx hx1
    _ = g n x := gap6 n x hx hx1

theorem gap8 :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → 0 < x → x < 1 →
      HasDerivAt (g n)
        (x ^ (n - 1) * ((n : ℝ) - ((n : ℝ) + 1) * x)) x := by
  intro n x hn hx hx1
  have hpow_succ : ∀ k : ℕ,
      HasDerivAt (fun y : ℝ => y ^ (k + 1))
        (((k : ℝ) + 1) * x ^ k) x := by
    intro k
    induction k with
    | zero =>
        simpa using (hasDerivAt_id x)
    | succ k ih =>
        convert ih.mul (hasDerivAt_id x) using 1 <;>
          simp [pow_succ, Nat.cast_succ] <;> ring
  cases n with
  | zero => omega
  | succ k =>
      convert
        ((hpow_succ k).mul
          ((hasDerivAt_const x 1).sub (hasDerivAt_id x))) using 1 <;>
        simp [g, pow_succ, Nat.cast_succ] <;> ring

theorem gap9 :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → 0 < x → x < 1 →
      x ^ (n - 1) * ((n : ℝ) - ((n : ℝ) + 1) * x) = 0 →
        x = (n : ℝ) / ((n : ℝ) + 1) := by
  intro n x hn hx hx1 hzero
  have hp : 0 < x ^ (n - 1) := pow_pos hx _
  have hfactor : (n : ℝ) - ((n : ℝ) + 1) * x = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hp)
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hden).2
  nlinarith

theorem gap10 :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → 0 < x → x < 1 →
      g n x ≤
        ((n : ℝ) / ((n : ℝ) + 1)) ^ n *
          (1 - (n : ℝ) / ((n : ℝ) + 1)) := by
  intro n x hn hx hx1
  set c : ℝ := (n : ℝ) / ((n : ℝ) + 1)
  let d : ℝ → ℝ := fun y =>
    y ^ (n - 1) * ((n : ℝ) - ((n : ℝ) + 1) * y)
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hc0 : 0 < c := by
    simp only [c]
    exact div_pos hnreal hden
  have hc1 : c < 1 := by
    simp only [c]
    exact (div_lt_one hden).2 (by linarith)
  have hcont : Continuous (g n) := by
    simpa [g] using
      ((continuous_id.pow n).mul (continuous_const.sub continuous_id))
  have hmax : g n x ≤ g n c := by
    by_cases hxc : x = c
    · rw [hxc]
    · by_cases hleft : x < c
      · obtain ⟨z, hz, hzslope⟩ :=
          exists_hasDerivAt_eq_slope (f := g n) d hleft
            hcont.continuousOn
            (fun y hy => gap8 n y hn (lt_trans hx hy.1) (lt_trans hy.2 hc1))
        have hz0 : 0 < z := lt_trans hx hz.1
        have hzcrit : ((n : ℝ) + 1) * z < (n : ℝ) := by
          have hzlt : z < (n : ℝ) / ((n : ℝ) + 1) := by
            simpa [c] using hz.2
          have hm := (lt_div_iff₀ hden).mp hzlt
          nlinarith
        have hderpos :
            0 < z ^ (n - 1) * ((n : ℝ) - ((n : ℝ) + 1) * z) :=
          mul_pos (pow_pos hz0 _) (by nlinarith)
        have hquot : 0 < (g n c - g n x) / (c - x) := by
          rw [← hzslope]
          simpa [d] using hderpos
        rcases (div_pos_iff.mp hquot) with ⟨hnum, hcd⟩ | ⟨hnum, hcd⟩
        · linarith
        · linarith
      · have hright : c < x := by
          rcases lt_trichotomy x c with h | h | h
          · exact False.elim (hleft h)
          · exact False.elim (hxc h)
          · exact h
        obtain ⟨z, hz, hzslope⟩ :=
          exists_hasDerivAt_eq_slope (f := g n) d hright
            hcont.continuousOn
            (fun y hy => gap8 n y hn (lt_trans hc0 hy.1) (lt_trans hy.2 hx1))
        have hz0 : 0 < z := lt_trans hc0 hz.1
        have hzcrit : (n : ℝ) < ((n : ℝ) + 1) * z := by
          have hzgt : (n : ℝ) / ((n : ℝ) + 1) < z := by
            simpa [c] using hz.1
          have hm := (div_lt_iff₀ hden).mp hzgt
          nlinarith
        have hderneg :
            z ^ (n - 1) * ((n : ℝ) - ((n : ℝ) + 1) * z) < 0 :=
          mul_neg_of_pos_of_neg (pow_pos hz0 _) (by nlinarith)
        have hquot : (g n x - g n c) / (x - c) < 0 := by
          rw [← hzslope]
          simpa [d] using hderneg
        rcases (div_neg_iff.mp hquot) with ⟨hnum, hxcpos⟩ | ⟨hnum, hxcneg⟩
        · linarith
        · linarith
  simpa [g, c] using hmax

theorem gap11 :
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) / ((n : ℝ) + 1)) ^ n *
          (1 - (n : ℝ) / ((n : ℝ) + 1)) =
        ((n : ℝ) / ((n : ℝ) + 1)) ^ n *
          (1 / ((n : ℝ) + 1)) := by
  intro n hn
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem gap12 :
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) / ((n : ℝ) + 1)) ^ n *
          (1 / ((n : ℝ) + 1)) <
        1 / ((n : ℝ) + 1) := by
  intro n hn
  set c : ℝ := (n : ℝ) / ((n : ℝ) + 1)
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hc0 : 0 < c := by
    simp only [c]
    exact div_pos hnreal hden
  have hc1 : c < 1 := by
    simp only [c]
    exact (div_lt_one hden).2 (by linarith)
  have hpow : c ^ n < 1 :=
    pow_lt_one₀ (le_of_lt hc0) hc1 (by omega)
  have hrecip : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hden
  have hprod :
      0 < (1 - c ^ n) * (1 / ((n : ℝ) + 1)) :=
    mul_pos (sub_pos.mpr hpow) hrecip
  simpa [c] using (show c ^ n * (1 / ((n : ℝ) + 1)) <
      1 / ((n : ℝ) + 1) by nlinarith)

theorem gap13 :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → 0 < x → x < 1 →
      g n x < 1 / ((n : ℝ) + 1) := by
  intro n x hn hx hx1
  calc
    g n x ≤
        ((n : ℝ) / ((n : ℝ) + 1)) ^ n *
          (1 - (n : ℝ) / ((n : ℝ) + 1)) := gap10 n x hn hx hx1
    _ = ((n : ℝ) / ((n : ℝ) + 1)) ^ n *
          (1 / ((n : ℝ) + 1)) := gap11 n hn
    _ < 1 / ((n : ℝ) + 1) := gap12 n hn

theorem gap14 :
    ∀ (n : ℕ) (x ε : ℝ), 1 ≤ n → x ∈ Set.Icc (0 : ℝ) 1 →
      0 < ε → 1 / ((n : ℝ) + 1) < ε → |term n x| < ε := by
  intro n x ε hn hx hε hbound
  rcases hx with ⟨hx0, hx1⟩
  have hn0 : n ≠ 0 := by omega
  by_cases h0 : x = 0
  · subst x
    simpa [term, hn0] using hε
  by_cases h1 : x = 1
  · subst x
    simpa [term] using hε
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h0)
  have hxlt : x < 1 := lt_of_le_of_ne hx1 h1
  calc
    |term n x| = g n x := by simpa using gap7 n x hxpos hxlt
    _ < 1 / ((n : ℝ) + 1) := gap13 n x hn hxpos hxlt
    _ < ε := hbound

theorem gap15 :
    ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      1 / ε < (n : ℝ) → 1 / ((n : ℝ) + 1) < ε := by
  intro n ε hε hn
  have hden : 0 < (n : ℝ) + 1 := by positivity
  apply (div_lt_iff₀ hden).2
  have hmul := (div_lt_iff₀ hε).mp hn
  nlinarith

theorem gap16 :
    ∀ (n : ℕ) (x ε : ℝ), 1 ≤ n → x ∈ Set.Icc (0 : ℝ) 1 →
      0 < ε → 1 / ε < (n : ℝ) → |term n x| < ε := by
  intro n x ε hn hx hε hnε
  exact gap14 n x ε hn hx hε (gap15 n ε hε hnε)

theorem gap17 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Icc (0 : ℝ) 1, |term n x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn1 : 1 ≤ n := by omega
  have hcast : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact gap16 n x ε hn1 hx hε (lt_trans hN hcast)

theorem gap18 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap17 ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa using hN n hn x hx

theorem gap19 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  exact gap18

end

end ProofGap.Exercise2747
