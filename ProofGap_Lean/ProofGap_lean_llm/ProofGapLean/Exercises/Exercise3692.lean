import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3692

noncomputable section

def feasible (p : ℝ) (q : ℝ × ℝ) : Prop :=
  0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 = p

def volume (q : ℝ × ℝ) : ℝ :=
  Real.pi * q.2 ^ 2 * q.1

def critical (p x y μ : ℝ) : Prop :=
  Real.pi * y ^ 2 - μ = 0 ∧
    2 * Real.pi * x * y - μ = 0 ∧
    x + y = p

def candidate (p : ℝ) : ℝ × ℝ :=
  (p / 3, 2 * p / 3)

def maximizers (p : ℝ) : Set (ℝ × ℝ) :=
  {q | feasible p q ∧ ∀ r, feasible p r → volume r ≤ volume q}

private theorem volume_le_candidate_aux
    (p x y : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y = p) :
    volume (x, y) ≤ volume (candidate p) := by
  have hlinear : 0 ≤ 3 * y + p := by
    linarith
  have hfac : 0 ≤ (3 * y - 2 * p) ^ 2 * (3 * y + p) :=
    mul_nonneg (sq_nonneg _) hlinear
  have hid :
      volume (candidate p) - volume (x, y) =
        Real.pi / 27 * ((3 * y - 2 * p) ^ 2 * (3 * y + p)) := by
    simp [volume, candidate]
    rw [← hxy]
    ring
  have hcoef : 0 ≤ Real.pi / (27 : ℝ) :=
    div_nonneg (le_of_lt Real.pi_pos) (by norm_num)
  have hnonneg :
      0 ≤ Real.pi / 27 * ((3 * y - 2 * p) ^ 2 * (3 * y + p)) :=
    mul_nonneg hcoef hfac
  linarith [hid, hnonneg]

theorem gap1 (p x y μ : ℝ) (hp : 0 < p)
    (hxy : 0 < x ∧ 0 < y) (hcrit : critical p x y μ) :
    x = p / 3 := by
  rcases hcrit with ⟨hfirst, hsecond, hsum⟩
  have heq : Real.pi * y ^ 2 = 2 * Real.pi * x * y := by
    linarith [hfirst, hsecond]
  have heq' : (Real.pi * y) * y = (Real.pi * y) * (2 * x) := by
    calc
      (Real.pi * y) * y = Real.pi * y ^ 2 := by ring
      _ = 2 * Real.pi * x * y := heq
      _ = (Real.pi * y) * (2 * x) := by ring
  have hpos : 0 < Real.pi * y := mul_pos Real.pi_pos hxy.2
  have hzero : (Real.pi * y) * (y - 2 * x) = 0 := by
    calc
      (Real.pi * y) * (y - 2 * x) =
          (Real.pi * y) * y - (Real.pi * y) * (2 * x) := by ring
      _ = 0 := sub_eq_zero.mpr heq'
  have hyx : y - 2 * x = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hpos)
  linarith [hyx, hsum]

theorem gap2 (p x y μ : ℝ) (hp : 0 < p)
    (hxy : 0 < x ∧ 0 < y) (hcrit : critical p x y μ) :
    y = 2 * p / 3 := by
  have hx : x = p / 3 := gap1 p x y μ hp hxy hcrit
  linarith [hx, hcrit.2.2]

theorem gap3 (p : ℝ) (hp : 0 < p) :
    {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ ∃ μ, critical p q.1 q.2 μ} =
      ({candidate p} : Set (ℝ × ℝ)) := by
  apply Set.ext
  intro q
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hy, μ, hcrit⟩
    apply Prod.ext
    · simpa [candidate] using gap1 p q.1 q.2 μ hp ⟨hx, hy⟩ hcrit
    · simpa [candidate] using gap2 p q.1 q.2 μ hp ⟨hx, hy⟩ hcrit
  · rintro rfl
    dsimp [candidate]
    refine ⟨by linarith, by linarith, ?_⟩
    refine ⟨Real.pi * (2 * p / 3) ^ 2, ?_⟩
    unfold critical
    constructor
    · ring
    constructor <;> ring

theorem gap4 (p x y : ℝ) (hfeas : feasible p (x, y))
    (hboundary : x = 0 ∨ y = 0) :
    volume (x, y) = 0 := by
  rcases hboundary with hx | hy
  · simp [volume, hx]
  · simp [volume, hy]

theorem gap5 (p : ℝ) (hp : 0 < p) :
    maximizers p = ({candidate p} : Set (ℝ × ℝ)) := by
  apply Set.ext
  intro q
  simp only [maximizers, Set.mem_setOf_eq, Set.mem_singleton_iff]
  have hcand : feasible p (candidate p) := by
    change 0 ≤ p / 3 ∧ 0 ≤ 2 * p / 3 ∧ p / 3 + 2 * p / 3 = p
    constructor
    · linarith
    constructor
    · linarith
    · ring
  constructor
  · rintro ⟨hfeas, hmax⟩
    rcases hfeas with ⟨hx, hy, hsum⟩
    have hupper : volume q ≤ volume (candidate p) := by
      simpa using
        volume_le_candidate_aux p q.1 q.2 (le_of_lt hp) hx hy hsum
    have heq : volume q = volume (candidate p) :=
      le_antisymm hupper (hmax (candidate p) hcand)
    have hid :
        volume (candidate p) - volume q =
          Real.pi / 27 *
            ((3 * q.2 - 2 * p) ^ 2 * (3 * q.2 + p)) := by
      simp [volume, candidate]
      rw [← hsum]
      ring
    have hprod :
        Real.pi / 27 *
            ((3 * q.2 - 2 * p) ^ 2 * (3 * q.2 + p)) = 0 := by
      rw [← hid, heq]
      ring
    have hcoef_ne : Real.pi / (27 : ℝ) ≠ 0 :=
      div_ne_zero (ne_of_gt Real.pi_pos) (by norm_num)
    have hinner :
        (3 * q.2 - 2 * p) ^ 2 * (3 * q.2 + p) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hcoef_ne
    have hfactor_ne : 3 * q.2 + p ≠ 0 := by
      apply ne_of_gt
      linarith
    have hsquare : (3 * q.2 - 2 * p) ^ 2 = 0 :=
      (mul_eq_zero.mp hinner).resolve_right hfactor_ne
    have hbase : 3 * q.2 - 2 * p = 0 := by
      rw [pow_two] at hsquare
      rcases mul_eq_zero.mp hsquare with h | h
      · exact h
      · exact h
    have hy_eq : q.2 = 2 * p / 3 := by
      linarith
    have hx_eq : q.1 = p / 3 := by
      linarith [hsum, hy_eq]
    apply Prod.ext
    · simpa [candidate] using hx_eq
    · simpa [candidate] using hy_eq
  · rintro rfl
    refine ⟨hcand, ?_⟩
    intro r hr
    rcases hr with ⟨hrx, hry, hrsum⟩
    simpa using
      volume_le_candidate_aux p r.1 r.2 (le_of_lt hp) hrx hry hrsum

end

end ProofGap.Exercise3692
