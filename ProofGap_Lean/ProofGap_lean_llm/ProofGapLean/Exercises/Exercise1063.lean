import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1063

noncomputable section

def y (n x : ℝ) : ℝ := Real.arctan (n * x)
def θ (n : ℝ) : ℝ := Real.arctan n
def threshold : ℝ := 89 * Real.pi / 180
def zeroPoints (n : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 = y n p.1 ∧ p.2 = 0}
def admissibleN : Set ℝ := {n | Real.tan threshold < n}

theorem gap1 (n : ℝ) (hn : 0 < n) :
    zeroPoints n = ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := by
  ext p
  change (p.2 = y n p.1 ∧ p.2 = 0) ↔ p = (0, 0)
  constructor
  · rintro ⟨hy, hp⟩
    have hy0 : y n p.1 = 0 := hy.symm.trans hp
    have hprod : n * p.1 = 0 := by
      have htan := congrArg Real.tan hy0
      simpa [y] using htan
    have hx : p.1 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hn)
    apply Prod.ext
    · simpa using hx
    · simpa using hp
  · rintro rfl
    simp [y]

theorem gap2 (n x : ℝ) (hn : 0 < n) (hx0 : 0 ≤ x)
    (hxπ : x < Real.pi) (hzero : y n x = 0) :
    (x, y n x) = ((0 : ℝ), (0 : ℝ)) := by
  have htan := congrArg Real.tan hzero
  have hprod : n * x = 0 := by
    simpa [y] using htan
  have hx : x = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hn)
  subst x
  simp [y]

theorem gap3 (n : ℝ) (hn : 0 < n) :
    Real.tan (θ n) = deriv (y n) 0 := by
  have hinner : HasDerivAt (fun x : ℝ => n * x) n 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul n
  have hcomp :=
    (Real.hasDerivAt_arctan (n * (0 : ℝ))).comp (0 : ℝ) hinner
  calc
    Real.tan (θ n) = n := by
      simpa [θ] using Real.tan_arctan n
    _ = deriv (y n) 0 := by
      symm
      simpa [y, Function.comp_def] using hcomp.deriv

theorem gap4 (n : ℝ) :
    deriv (y n) 0 = n := by
  have hinner : HasDerivAt (fun x : ℝ => n * x) n 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul n
  have hcomp :=
    (Real.hasDerivAt_arctan (n * (0 : ℝ))).comp (0 : ℝ) hinner
  simpa [y, Function.comp_def] using hcomp.deriv

theorem gap5 (n : ℝ) (hn : 0 < n) :
    Real.tan (θ n) = n := by
  simpa [θ] using Real.tan_arctan n

theorem gap6 (n : ℝ) (hn : 0 < n) :
    θ n > threshold ↔ Real.tan (θ n) > Real.tan threshold := by
  have hθ : θ n ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa [θ] using Real.arctan_mem_Ioo n
  have ht : threshold ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · unfold threshold
      nlinarith [Real.pi_pos]
    · unfold threshold
      nlinarith [Real.pi_pos]
  constructor
  · intro h
    exact Real.strictMonoOn_tan ht hθ h
  · intro htan
    by_contra hnot
    have hle : θ n ≤ threshold := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · rw [heq] at htan
      exact lt_irrefl _ htan
    · have hrev := Real.strictMonoOn_tan hθ ht hlt
      exact (lt_asymm htan hrev)

theorem gap7 (n : ℝ) (hn : 0 < n) :
    θ n > threshold ↔ n > Real.tan threshold := by
  rw [gap6 n hn, gap5 n hn]

theorem gap8 (n : ℝ) (hn : 0 < n) :
    n ∈ admissibleN ↔ θ n > threshold := by
  change n > Real.tan threshold ↔ θ n > threshold
  exact (gap7 n hn).symm

end

end ProofGap.Exercise1063
