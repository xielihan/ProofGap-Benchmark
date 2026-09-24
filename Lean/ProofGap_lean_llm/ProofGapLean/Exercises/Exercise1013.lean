import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1013

noncomputable section

def inner (a b : ℝ) (x : ℝ) : ℝ := a + b * x ^ 2
def outer (m : ℝ) (x : ℝ) : ℝ := m ^ 2 / |x|

def matchingSystem (a b c m : ℝ) : Prop :=
  2 * b * c = -(m ^ 2 / c ^ 2) ∧
    a + b * c ^ 2 = m ^ 2 / c

def coefficientPair (c m : ℝ) : ℝ × ℝ :=
  (3 * m ^ 2 / (2 * c), -(m ^ 2 / (2 * c ^ 3)))

theorem gap1 (a b c m : ℝ) (hc : 0 < c)
    (h : matchingSystem a b c m) : 0 < c := by
  exact hc

theorem gap2 (a b c m : ℝ) (hc : 0 < c) :
    HasDerivAt (inner a b) (2 * b * c) c ∧
      HasDerivAt (outer m) (-(m ^ 2 / c ^ 2)) c := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * c) c := by
    simpa using (hasDerivAt_id c).pow 2
  have hinner : HasDerivAt (inner a b) (2 * b * c) c := by
    simpa [inner, mul_assoc, mul_comm, mul_left_comm] using
      (hasDerivAt_const c a).add (hsq.const_mul b)
  have hrat : HasDerivAt ((fun _ : ℝ => m ^ 2) / id)
      (-(m ^ 2 / c ^ 2)) c := by
    convert (hasDerivAt_const c (m ^ 2)).div (hasDerivAt_id c) hc0 using 1 <;>
      simp only [id_eq] <;> ring
  have heq : outer m =ᶠ[nhds c] ((fun _ : ℝ => m ^ 2) / id) := by
    filter_upwards [Ioi_mem_nhds hc] with x hx
    have hx0 : 0 < x := hx
    simp [outer, abs_of_pos hx0]
  exact ⟨hinner, hrat.congr_of_eventuallyEq heq⟩

theorem gap3 (a b c m : ℝ) (hc : 0 < c)
    (hvalue : a + b * c ^ 2 = m ^ 2 / c) :
    inner a b c = outer m c := by
  simpa [inner, outer, abs_of_pos hc] using hvalue

theorem gap4 (a b c m : ℝ) (hc : 0 < c) :
    deriv (inner a b) c = 2 * b * c ∧
      deriv (outer m) c = -(m ^ 2 / c ^ 2) := by
  rcases gap2 a b c m hc with ⟨hinner, houter⟩
  exact ⟨hinner.deriv, houter.deriv⟩

theorem gap5 (a b c m : ℝ) (hc : 0 < c)
    (hvalue : a + b * c ^ 2 = m ^ 2 / c) :
    inner a b c = outer m c := by
  exact gap3 a b c m hc hvalue

theorem gap6 (a b c m : ℝ) (hc : 0 < c) :
    (a, b) = coefficientPair c m ↔ matchingSystem a b c m := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  constructor
  · intro hab
    have ha : a = 3 * m ^ 2 / (2 * c) := by
      simpa [coefficientPair] using congrArg Prod.fst hab
    have hb : b = -(m ^ 2 / (2 * c ^ 3)) := by
      simpa [coefficientPair] using congrArg Prod.snd hab
    unfold matchingSystem
    rw [ha, hb]
    constructor <;> field_simp [hc0] <;> ring
  · intro hs
    rcases hs with ⟨hslope, hvalue⟩
    have hb : b = -(m ^ 2 / (2 * c ^ 3)) := by
      field_simp [hc0] at hslope ⊢ <;>
        ring_nf at hslope ⊢ <;>
        nlinarith
    have hbterm : b * c ^ 2 = -(m ^ 2 / (2 * c)) := by
      rw [hb]
      field_simp [hc0] <;> ring
    have ha : a = 3 * m ^ 2 / (2 * c) := by
      rw [hbterm] at hvalue
      field_simp [hc0] at hvalue ⊢ <;>
        ring_nf at hvalue ⊢ <;>
        linarith
    apply Prod.ext
    · simpa [coefficientPair] using ha
    · simpa [coefficientPair] using hb

theorem gap7 (a b c m : ℝ) (hc : 0 < c)
    (h : matchingSystem a b c m) :
    deriv (inner a b) c = deriv (outer m) c := by
  calc
    deriv (inner a b) c = 2 * b * c := (gap4 a b c m hc).1
    _ = -(m ^ 2 / c ^ 2) := h.1
    _ = deriv (outer m) c := (gap4 a b c m hc).2.symm

theorem gap8 (a b c m : ℝ) (hc : 0 < c)
    (h : matchingSystem a b c m) :
    inner a b (-c) = outer m (-c) := by
  simpa [inner, outer, abs_of_pos hc] using h.2

theorem gap9 (a b c m : ℝ) (hc : 0 < c)
    (h : (a, b) = coefficientPair c m) :
    matchingSystem a b c m := by
  exact (gap6 a b c m hc).mp h

end

end ProofGap.Exercise1013
