import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1192

noncomputable section

open scoped BigOperators

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def cubeRoot (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def y (x : ℝ) : ℝ := x / cubeRoot (1 + x)

def stepProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n - 1), (3 * k + 1 : ℕ)

def firstCoeff (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, ((2 / 3 : ℝ) - (k : ℝ))

def secondCoeff (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (-(1 / 3 : ℝ) - (k : ℝ))

def rawClosed (n : ℕ) (x : ℝ) : ℝ :=
  firstCoeff n * Real.rpow (1 + x) ((2 / 3 : ℝ) - n) -
    secondCoeff n * Real.rpow (1 + x) (-(1 / 3 : ℝ) - n)

def compactClosed₁ (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * stepProduct n /
      (3 : ℝ) ^ n /
      Real.rpow (1 + x) ((n : ℝ) + 1 / 3) *
    (2 * (1 + x) + 3 * n - 2)

def compactClosed₂ (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * stepProduct n * (3 * n + 2 * x) /
    ((3 : ℝ) ^ n * Real.rpow (1 + x) ((n : ℝ) + 1 / 3))

private theorem firstCoeff_succ (n : ℕ) :
    firstCoeff (n + 1) =
      firstCoeff n * ((2 / 3 : ℝ) - (n : ℝ)) := by
  simp [firstCoeff, Finset.prod_range_succ]

private theorem secondCoeff_succ (n : ℕ) :
    secondCoeff (n + 1) =
      secondCoeff n * (-(1 / 3 : ℝ) - (n : ℝ)) := by
  simp [secondCoeff, Finset.prod_range_succ]

private theorem stepProduct_succ_succ (n : ℕ) :
    stepProduct (n + 2) =
      stepProduct (n + 1) * (3 * (n : ℝ) + 1) := by
  simp [stepProduct, Finset.prod_range_succ, Nat.cast_add, Nat.cast_mul]

private theorem firstCoeff_closed (m : ℕ) :
    firstCoeff (m + 1) =
      (-1 : ℝ) ^ (m + 2) * 2 * stepProduct (m + 1) /
        (3 : ℝ) ^ (m + 1) := by
  induction m with
  | zero => norm_num [firstCoeff, stepProduct]
  | succ m ih =>
      rw [firstCoeff_succ, ih, stepProduct_succ_succ]
      norm_num [pow_succ] <;> ring

private theorem secondCoeff_closed (m : ℕ) :
    secondCoeff (m + 1) =
      (-1 : ℝ) ^ (m + 1) * stepProduct (m + 1) *
        (3 * ((m + 1 : ℕ) : ℝ) - 2) /
        (3 : ℝ) ^ (m + 1) := by
  induction m with
  | zero => norm_num [secondCoeff, stepProduct]
  | succ m ih =>
      rw [secondCoeff_succ, ih, stepProduct_succ_succ]
      norm_num [pow_succ] <;> ring

private theorem hasDerivAt_shiftedRpow
    (p x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun z : ℝ => Real.rpow (1 + z) p)
      (p * Real.rpow (1 + x) (p - 1)) x := by
  have ha : 0 < 1 + x := by linarith
  have hb : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
    simpa using
      (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hr :=
    (Real.hasDerivAt_rpow_const (p := p)
      (Or.inl (ne_of_gt ha))).comp x hb
  simpa [Function.comp_def] using hr

private theorem hasDerivAt_rawClosed
    (n : ℕ) (x : ℝ) (hx : -1 < x) :
    HasDerivAt (rawClosed n) (rawClosed (n + 1) x) x := by
  have h1 :=
    hasDerivAt_shiftedRpow ((2 / 3 : ℝ) - (n : ℝ)) x hx
  have h2 :=
    hasDerivAt_shiftedRpow (-(1 / 3 : ℝ) - (n : ℝ)) x hx
  have hd :
      HasDerivAt (rawClosed n)
        (firstCoeff n *
            (((2 / 3 : ℝ) - (n : ℝ)) *
              Real.rpow (1 + x) (((2 / 3 : ℝ) - (n : ℝ)) - 1)) -
          secondCoeff n *
            ((-(1 / 3 : ℝ) - (n : ℝ)) *
              Real.rpow (1 + x) ((-(1 / 3 : ℝ) - (n : ℝ)) - 1))) x := by
    change HasDerivAt
      (fun y : ℝ =>
        firstCoeff n *
            Real.rpow (1 + y) ((2 / 3 : ℝ) - (n : ℝ)) -
          secondCoeff n *
            Real.rpow (1 + y) (-(1 / 3 : ℝ) - (n : ℝ)))
      (firstCoeff n *
          (((2 / 3 : ℝ) - (n : ℝ)) *
            Real.rpow (1 + x) (((2 / 3 : ℝ) - (n : ℝ)) - 1)) -
        secondCoeff n *
          ((-(1 / 3 : ℝ) - (n : ℝ)) *
            Real.rpow (1 + x) ((-(1 / 3 : ℝ) - (n : ℝ)) - 1))) x
    exact
      (h1.const_mul (firstCoeff n)).sub
        (h2.const_mul (secondCoeff n))
  have hp1 :
      ((2 / 3 : ℝ) - (n : ℝ)) - 1 =
        (2 / 3 : ℝ) - ((n + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hp2 :
      (-(1 / 3 : ℝ) - (n : ℝ)) - 1 =
        -(1 / 3 : ℝ) - ((n + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hval :
      firstCoeff n *
          (((2 / 3 : ℝ) - (n : ℝ)) *
            Real.rpow (1 + x) (((2 / 3 : ℝ) - (n : ℝ)) - 1)) -
        secondCoeff n *
          ((-(1 / 3 : ℝ) - (n : ℝ)) *
            Real.rpow (1 + x) ((-(1 / 3 : ℝ) - (n : ℝ)) - 1)) =
        rawClosed (n + 1) x := by
    rw [rawClosed, firstCoeff_succ, secondCoeff_succ, ← hp1, ← hp2]
    ring
  rw [hval] at hd
  exact hd

theorem gap1 (x : ℝ) (hx : -1 < x) :
    y x = (x + 1 - 1) / cubeRoot (1 + x) := by
  simpa [y]

theorem gap2 (x : ℝ) (hx : -1 < x) :
    (x + 1 - 1) / cubeRoot (1 + x) =
      Real.rpow (1 + x) (2 / 3 : ℝ) -
        Real.rpow (1 + x) (-(1 / 3 : ℝ)) := by
  have ha : 0 < 1 + x := by linarith
  have hpow :
      Real.rpow (1 + x) (2 / 3 : ℝ) =
        (1 + x) * Real.rpow (1 + x) (-(1 / 3 : ℝ)) := by
    calc
      Real.rpow (1 + x) (2 / 3 : ℝ) =
          Real.rpow (1 + x) (1 + (-(1 / 3 : ℝ))) := by
            congr 1
            ring
      _ = Real.rpow (1 + x) 1 *
          Real.rpow (1 + x) (-(1 / 3 : ℝ)) :=
            Real.rpow_add ha 1 (-(1 / 3 : ℝ))
      _ = (1 + x) * Real.rpow (1 + x) (-(1 / 3 : ℝ)) := by
            change ((1 + x) ^ (1 : ℝ)) *
                Real.rpow (1 + x) (-(1 / 3 : ℝ)) = _
            rw [Real.rpow_one]
  have hinv :
      Real.rpow (1 + x) (-(1 / 3 : ℝ)) =
        (Real.rpow (1 + x) (1 / 3 : ℝ))⁻¹ := by
    simpa using
      (Real.rpow_neg ha.le (1 / 3 : ℝ))
  have hne : Real.rpow (1 + x) (1 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  rw [cubeRoot, hpow, hinv]
  field_simp [hne]
  ring

theorem gap3 (x : ℝ) (hx : -1 < x) :
    y x =
      Real.rpow (1 + x) (2 / 3 : ℝ) -
        Real.rpow (1 + x) (-(1 / 3 : ℝ)) := by
  rw [gap1 x hx, gap2 x hx]

theorem gap4 (n : ℕ) (x : ℝ) (hx : -1 < x) :
    iterDeriv n y x = rawClosed n x := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv, rawClosed, firstCoeff, secondCoeff] using gap3 x hx
  | succ n ih =>
      rw [iterDeriv, Function.iterate_succ_apply']
      change deriv (iterDeriv n y) x = rawClosed (n + 1) x
      have hxmem : x ∈ Set.Ioi (-1) := hx
      have hmem : ∀ᶠ z in nhds x, z ∈ Set.Ioi (-1) :=
        isOpen_Ioi.mem_nhds hxmem
      have heq : iterDeriv n y =ᶠ[nhds x] rawClosed n := by
        filter_upwards [hmem] with z hz
        exact ih z hz
      exact
        ((hasDerivAt_rawClosed n x hx).congr_of_eventuallyEq heq).deriv

theorem gap5 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : -1 < x) :
    iterDeriv n y x = compactClosed₁ n x := by
  cases n with
  | zero => norm_num at hn
  | succ m =>
      have ha : 0 < 1 + x := by linarith
      have hpow1 :
          Real.rpow (1 + x) ((2 / 3 : ℝ) - (m + 1 : ℕ)) =
            (1 + x) *
              Real.rpow (1 + x) (-((m + 1 : ℕ) + (1 / 3 : ℝ))) := by
        calc
          Real.rpow (1 + x) ((2 / 3 : ℝ) - (m + 1 : ℕ)) =
              Real.rpow (1 + x)
                (1 + (-((m + 1 : ℕ) + (1 / 3 : ℝ)))) := by
                  congr 1
                  push_cast
                  ring
          _ = Real.rpow (1 + x) 1 *
              Real.rpow (1 + x) (-((m + 1 : ℕ) + (1 / 3 : ℝ))) :=
                Real.rpow_add ha 1 (-((m + 1 : ℕ) + (1 / 3 : ℝ)))
          _ = (1 + x) *
              Real.rpow (1 + x) (-((m + 1 : ℕ) + (1 / 3 : ℝ))) := by
                change ((1 + x) ^ (1 : ℝ)) *
                    Real.rpow (1 + x) (-((m + 1 : ℕ) + (1 / 3 : ℝ))) = _
                rw [Real.rpow_one]
      have hpow2 :
          Real.rpow (1 + x) (-(1 / 3 : ℝ) - (m + 1 : ℕ)) =
            Real.rpow (1 + x) (-((m + 1 : ℕ) + (1 / 3 : ℝ))) := by
        congr 1
        push_cast
        ring
      have hneg :
          Real.rpow (1 + x) (-((m + 1 : ℕ) + (1 / 3 : ℝ))) =
            (Real.rpow (1 + x) ((m + 1 : ℕ) + (1 / 3 : ℝ)))⁻¹ := by
        simpa using
          (Real.rpow_neg ha.le ((m + 1 : ℕ) + (1 / 3 : ℝ)))
      have hR :
          Real.rpow (1 + x) ((m + 1 : ℕ) + (1 / 3 : ℝ)) ≠ 0 :=
        (Real.rpow_pos_of_pos ha _).ne'
      have hsign :
          (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ (m + 2)) := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        ring
      rw [gap4 (m + 1) x hx]
      unfold rawClosed
      rw [firstCoeff_closed m, secondCoeff_closed m, hpow1, hpow2, hneg,
        hsign]
      unfold compactClosed₁
      field_simp [hR]
      ring

theorem gap6 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : -1 < x) :
    iterDeriv n y x = compactClosed₂ n x := by
  rw [gap5 n x hn hx]
  have ha : 0 < 1 + x := by linarith
  have hR : Real.rpow (1 + x) ((n : ℝ) + 1 / 3) ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  unfold compactClosed₁ compactClosed₂
  field_simp [hR]
  ring

end

end ProofGap.Exercise1192
