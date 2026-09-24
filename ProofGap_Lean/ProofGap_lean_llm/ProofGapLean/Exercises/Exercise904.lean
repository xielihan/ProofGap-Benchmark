import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise904

noncomputable section

def ratio (x : ℝ) : ℝ :=
  (1 - Real.sin x) / (1 + Real.sin x)

def y (x : ℝ) : ℝ := Real.log (Real.sqrt (ratio x))

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (-Real.cos x / (1 - Real.sin x) -
      Real.cos x / (1 + Real.sin x))

def finalDerivative (x : ℝ) : ℝ := -(1 / Real.cos x)

private theorem ratio_num_den_ne (x : ℝ) (h : 0 < ratio x) :
    (1 - Real.sin x ≠ 0) ∧ (1 + Real.sin x ≠ 0) := by
  have hrne : ratio x ≠ 0 := ne_of_gt h
  constructor
  · intro hn
    apply hrne
    simp [ratio, hn]
  · intro hd
    apply hrne
    simp [ratio, hd]

theorem gap1 (x : ℝ) (hratio : 0 < ratio x)
    (hcos : Real.cos x ≠ 0) :
    deriv y x = expandedDerivative x := by
  rcases ratio_num_den_ne x hratio with ⟨hnum, hden⟩
  have htop :
      HasDerivAt (fun z : ℝ => 1 - Real.sin z) (-Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_sub (1 : ℝ)
  have hbottom :
      HasDerivAt (fun z : ℝ => 1 + Real.sin z) (Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_add (1 : ℝ)
  have hratioDeriv :
      HasDerivAt ratio
        (((-Real.cos x) * (1 + Real.sin x) -
            (1 - Real.sin x) * Real.cos x) /
          (1 + Real.sin x) ^ 2) x := by
    simpa [ratio] using htop.div hbottom hden
  have hlog :
      HasDerivAt (fun z : ℝ => Real.log (ratio z))
        ((((-Real.cos x) * (1 + Real.sin x) -
              (1 - Real.sin x) * Real.cos x) /
            (1 + Real.sin x) ^ 2) /
          ratio x) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log (ne_of_gt hratio)).comp x hratioDeriv
  have hhalfLog :
      HasDerivAt (fun z : ℝ => (1 / 2 : ℝ) * Real.log (ratio z))
        ((1 / 2 : ℝ) *
          ((((-Real.cos x) * (1 + Real.sin x) -
                (1 - Real.sin x) * Real.cos x) /
              (1 + Real.sin x) ^ 2) /
            ratio x)) x := by
    simpa using hlog.const_mul (1 / 2 : ℝ)
  have hpos : ∀ᶠ z in nhds x, 0 < ratio z :=
    hratioDeriv.continuousAt.eventually (isOpen_Ioi.mem_nhds hratio)
  have heq :
      y =ᶠ[nhds x] (fun z : ℝ => (1 / 2 : ℝ) * Real.log (ratio z)) := by
    apply hpos.mono
    intro z hz
    unfold y
    rw [Real.log_sqrt (le_of_lt hz)]
    ring
  have hyDeriv :
      HasDerivAt y
        ((1 / 2 : ℝ) *
          ((((-Real.cos x) * (1 + Real.sin x) -
                (1 - Real.sin x) * Real.cos x) /
              (1 + Real.sin x) ^ 2) /
            ratio x)) x :=
    hhalfLog.congr_of_eventuallyEq heq
  rw [hyDeriv.deriv]
  unfold expandedDerivative ratio
  field_simp [hnum, hden]

theorem gap2 (x : ℝ) (hratio : 0 < ratio x)
    (hcos : Real.cos x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  rcases ratio_num_den_ne x hratio with ⟨hnum, hden⟩
  unfold expandedDerivative finalDerivative
  field_simp [hnum, hden, hcos] <;>
    nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap3 (x : ℝ) (hratio : 0 < ratio x)
    (hcos : Real.cos x ≠ 0) :
    deriv y x = finalDerivative x := by
  exact (gap1 x hratio hcos).trans (gap2 x hratio hcos)

end

end ProofGap.Exercise904
