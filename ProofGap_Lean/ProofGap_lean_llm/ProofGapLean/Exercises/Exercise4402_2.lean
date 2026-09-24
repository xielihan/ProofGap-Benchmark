import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4402_2

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def u (p : Vec3) : ℝ :=
  p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3 -
    3 * p.1 * p.2.1 * p.2.2

def partialX (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => f (x, p.2.1, p.2.2)) p.1

def partialY (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => f (p.1, y, p.2.2)) p.2.1

def partialZ (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => f (p.1, p.2.1, z)) p.2.2

def gradient (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def xyCritical (p : Vec3) : Prop :=
  (gradient p).1 = 0 ∧ (gradient p).2.1 = 0

def xyCriticalLocus : Set Vec3 :=
  {p | (p.1 = 0 ∧ p.2.1 = 0) ∨
    (p.1 = p.2.1 ∧ p.2.1 = p.2.2)}

theorem gap1 (x y z : ℝ) :
    gradient (x, y, z) =
      (3 * x ^ 2 - 3 * y * z,
        3 * y ^ 2 - 3 * x * z,
        3 * z ^ 2 - 3 * x * y) := by
  have hx :
      HasDerivAt (fun t : ℝ => u (t, y, z))
        (3 * x ^ 2 - 3 * y * z) x := by
    have hcube :=
      ((hasDerivAt_id x).mul (hasDerivAt_id x)).mul
        (hasDerivAt_id x)
    have hlin :=
      (((hasDerivAt_const x (3 : ℝ)).mul (hasDerivAt_id x)).mul
        (hasDerivAt_const x y)).mul
          (hasDerivAt_const x z)
    have h :=
      ((hcube.add (hasDerivAt_const x (y ^ 3))).add
        (hasDerivAt_const x (z ^ 3))).sub hlin
    convert h using 1
    · funext t
      change
        t ^ 3 + y ^ 3 + z ^ 3 - 3 * t * y * z =
          t * t * t + y ^ 3 + z ^ 3 - 3 * t * y * z
      ring
    · simp <;> ring_nf
  have hy :
      HasDerivAt (fun t : ℝ => u (x, t, z))
        (3 * y ^ 2 - 3 * x * z) y := by
    have hcube :=
      ((hasDerivAt_id y).mul (hasDerivAt_id y)).mul
        (hasDerivAt_id y)
    have hlin :=
      (((hasDerivAt_const y (3 : ℝ)).mul
        (hasDerivAt_const y x)).mul
        (hasDerivAt_id y)).mul
          (hasDerivAt_const y z)
    have h :=
      (((hasDerivAt_const y (x ^ 3)).add hcube).add
        (hasDerivAt_const y (z ^ 3))).sub hlin
    convert h using 1
    · funext t
      change
        x ^ 3 + t ^ 3 + z ^ 3 - 3 * x * t * z =
          x ^ 3 + t * t * t + z ^ 3 - 3 * x * t * z
      ring
    · simp <;> ring_nf
  have hz :
      HasDerivAt (fun t : ℝ => u (x, y, t))
        (3 * z ^ 2 - 3 * x * y) z := by
    have hcube :=
      ((hasDerivAt_id z).mul (hasDerivAt_id z)).mul
        (hasDerivAt_id z)
    have hlin :=
      (((hasDerivAt_const z (3 : ℝ)).mul
        (hasDerivAt_const z x)).mul
        (hasDerivAt_const z y)).mul
          (hasDerivAt_id z)
    have h :=
      (((hasDerivAt_const z (x ^ 3)).add
        (hasDerivAt_const z (y ^ 3))).add hcube).sub hlin
    convert h using 1
    · funext t
      change
        x ^ 3 + y ^ 3 + t ^ 3 - 3 * x * y * t =
          x ^ 3 + y ^ 3 + t * t * t - 3 * x * y * t
      ring
    · simp <;> ring_nf
  unfold gradient partialX partialY partialZ
  apply Prod.ext
  · exact hx.deriv
  · apply Prod.ext
    · exact hy.deriv
    · exact hz.deriv

theorem gap2 (x y z : ℝ) :
    xyCritical (x, y, z) ↔
      3 * x ^ 2 - 3 * y * z = 0 ∧
        3 * y ^ 2 - 3 * x * z = 0 := by
  simp [xyCritical, gap1]

theorem gap3 (x y z : ℝ) :
    (3 * x ^ 2 - 3 * y * z = 0 ∧
        3 * y ^ 2 - 3 * x * z = 0) ↔
      (x = 0 ∧ y = 0) ∨ (x = y ∧ y = z) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : x ^ 2 = y * z := by
      nlinarith
    have h2' : y ^ 2 = x * z := by
      nlinarith
    by_cases hx : x = 0
    · left
      subst x
      refine ⟨rfl, ?_⟩
      have hymul : y * y = 0 := by
        simpa [pow_two] using h2'
      rcases mul_eq_zero.mp hymul with hy | hy
      · exact hy
      · exact hy
    · right
      have hcube : x ^ 3 = y ^ 3 := by
        calc
          x ^ 3 = x * (x ^ 2) := by ring
          _ = x * (y * z) := by rw [h1']
          _ = y * (x * z) := by ring
          _ = y * (y ^ 2) := by rw [← h2']
          _ = y ^ 3 := by ring
      have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by
        nlinarith [hcube]
      have hq : 0 < x ^ 2 + x * y + y ^ 2 := by
        have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
        nlinarith [sq_nonneg (x + y), sq_nonneg y]
      have hxy : x = y := by
        rcases mul_eq_zero.mp hfac with h | h
        · exact sub_eq_zero.mp h
        · exact False.elim ((ne_of_gt hq) h)
      subst y
      refine ⟨rfl, ?_⟩
      have hxz : x * (x - z) = 0 := by
        nlinarith [h1']
      rcases mul_eq_zero.mp hxz with h | h
      · exact False.elim (hx h)
      · exact sub_eq_zero.mp h
  · rintro (h | h)
    · rcases h with ⟨rfl, rfl⟩
      constructor <;> ring
    · rcases h with ⟨rfl, rfl⟩
      constructor <;> ring

theorem gap4 (x y z : ℝ) :
    (x, y, z) ∈ xyCriticalLocus ↔
      3 * x ^ 2 - 3 * y * z = 0 ∧
        3 * y ^ 2 - 3 * x * z = 0 := by
  simpa [xyCriticalLocus] using (gap3 x y z).symm

end

end ProofGap.Exercise4402_2
