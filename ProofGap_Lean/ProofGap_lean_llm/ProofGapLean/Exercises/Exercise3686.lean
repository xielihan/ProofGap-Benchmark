import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3686

noncomputable section

open scoped BigOperators

def totalMass {n : ℕ} (m : Fin n → ℝ) : ℝ :=
  ∑ i, m i

def cost {n : ℕ}
    (m xCoord yCoord : Fin n → ℝ) (q : ℝ × ℝ) : ℝ :=
  ∑ i, m i * ((q.1 - xCoord i) ^ 2 + (q.2 - yCoord i) ^ 2)

def centroid {n : ℕ}
    (m xCoord yCoord : Fin n → ℝ) : ℝ × ℝ :=
  ((totalMass m)⁻¹ * ∑ i, m i * xCoord i,
    (totalMass m)⁻¹ * ∑ i, m i * yCoord i)

def critical {n : ℕ}
    (m xCoord yCoord : Fin n → ℝ) (q : ℝ × ℝ) : Prop :=
  2 * ∑ i, m i * (q.1 - xCoord i) = 0 ∧
    2 * ∑ i, m i * (q.2 - yCoord i) = 0

def Coercive {n : ℕ}
    (m xCoord yCoord : Fin n → ℝ) : Prop :=
  ∀ B : ℝ, ∃ R : ℝ, ∀ q : ℝ × ℝ,
    R ≤ max |q.1| |q.2| → B ≤ cost m xCoord yCoord q

def minimizers {n : ℕ}
    (m xCoord yCoord : Fin n → ℝ) : Set (ℝ × ℝ) :=
  {q | ∀ r, cost m xCoord yCoord q ≤ cost m xCoord yCoord r}

private theorem totalMass_pos {n : ℕ} (hn : 0 < n)
    (m : Fin n → ℝ) (hm : ∀ i, 0 < m i) :
    0 < totalMass m := by
  let i : Fin n := ⟨0, hn⟩
  have hle : m i ≤ ∑ j, m j := by
    exact Finset.single_le_sum
      (fun j hj => (hm j).le) (Finset.mem_univ i)
  exact lt_of_lt_of_le (hm i) hle

private theorem weighted_sq_shift {n : ℕ}
    (m x : Fin n → ℝ) (q c : ℝ) :
    (∑ i, m i * (q - x i) ^ 2) =
      (∑ i, m i * (c - x i) ^ 2) +
        (q - c) ^ 2 * (∑ i, m i) +
        2 * (q - c) * (∑ i, m i * (c - x i)) := by
  calc
    (∑ i, m i * (q - x i) ^ 2) =
        ∑ i, (m i * (c - x i) ^ 2 +
          (q - c) ^ 2 * m i +
          (2 * (q - c)) * (m i * (c - x i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, m i * (c - x i) ^ 2) +
        (q - c) ^ 2 * (∑ i, m i) +
        2 * (q - c) * (∑ i, m i * (c - x i)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

private theorem centroid_balance {n : ℕ}
    (m x : Fin n → ℝ) (hM : totalMass m ≠ 0) :
    ∑ i, m i * ((totalMass m)⁻¹ * (∑ j, m j * x j) - x i) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change totalMass m * ((totalMass m)⁻¹ * (∑ j, m j * x j)) -
    (∑ i, m i * x i) = 0
  field_simp [hM]
  ring

private theorem centroid_critical {n : ℕ}
    (m xCoord yCoord : Fin n → ℝ) (hM : totalMass m ≠ 0) :
    critical m xCoord yCoord (centroid m xCoord yCoord) := by
  constructor
  · change 2 * (∑ i, m i *
      ((totalMass m)⁻¹ * (∑ j, m j * xCoord j) - xCoord i)) = 0
    rw [centroid_balance m xCoord hM]
    ring
  · change 2 * (∑ i, m i *
      ((totalMass m)⁻¹ * (∑ j, m j * yCoord j) - yCoord i)) = 0
    rw [centroid_balance m yCoord hM]
    ring

private theorem cost_centroid_decomp {n : ℕ}
    (m xCoord yCoord : Fin n → ℝ) (hM : totalMass m ≠ 0)
    (q : ℝ × ℝ) :
    cost m xCoord yCoord q =
      cost m xCoord yCoord (centroid m xCoord yCoord) +
        totalMass m *
          ((q.1 - (centroid m xCoord yCoord).1) ^ 2 +
           (q.2 - (centroid m xCoord yCoord).2) ^ 2) := by
  unfold cost
  simp_rw [mul_add]
  simp only [Finset.sum_add_distrib]
  rw [weighted_sq_shift m xCoord q.1
    (centroid m xCoord yCoord).1]
  rw [weighted_sq_shift m yCoord q.2
    (centroid m xCoord yCoord).2]
  dsimp only [centroid]
  rw [centroid_balance m xCoord hM, centroid_balance m yCoord hM]
  unfold totalMass
  ring

theorem gap1 {n : ℕ} (hn : 0 < n)
    (m xCoord yCoord : Fin n → ℝ) (q : ℝ × ℝ)
    (hm : ∀ i, 0 < m i) (hcrit : critical m xCoord yCoord q) :
    q.1 = (centroid m xCoord yCoord).1 := by
  have hM : 0 < totalMass m := totalMass_pos hn m hm
  have hx : 2 * ∑ i, m i * (q.1 - xCoord i) = 0 := hcrit.1
  simp_rw [mul_sub] at hx
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hx
  change 2 * (totalMass m * q.1 - ∑ i, m i * xCoord i) = 0 at hx
  have heq : totalMass m * q.1 = ∑ i, m i * xCoord i := by
    linarith
  change q.1 = (totalMass m)⁻¹ * ∑ i, m i * xCoord i
  rw [← heq]
  field_simp [ne_of_gt hM]

theorem gap2 {n : ℕ} (hn : 0 < n)
    (m xCoord yCoord : Fin n → ℝ) (q : ℝ × ℝ)
    (hm : ∀ i, 0 < m i) (hcrit : critical m xCoord yCoord q) :
    q.2 = (centroid m xCoord yCoord).2 := by
  have hM : 0 < totalMass m := totalMass_pos hn m hm
  have hy : 2 * ∑ i, m i * (q.2 - yCoord i) = 0 := hcrit.2
  simp_rw [mul_sub] at hy
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hy
  change 2 * (totalMass m * q.2 - ∑ i, m i * yCoord i) = 0 at hy
  have heq : totalMass m * q.2 = ∑ i, m i * yCoord i := by
    linarith
  change q.2 = (totalMass m)⁻¹ * ∑ i, m i * yCoord i
  rw [← heq]
  field_simp [ne_of_gt hM]

theorem gap3 {n : ℕ} (hn : 0 < n)
    (m xCoord yCoord : Fin n → ℝ) (hm : ∀ i, 0 < m i) :
    {q | critical m xCoord yCoord q} =
      ({centroid m xCoord yCoord} : Set (ℝ × ℝ)) := by
  apply Set.ext
  intro q
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hq
    apply Prod.ext
    · exact gap1 hn m xCoord yCoord q hm hq
    · exact gap2 hn m xCoord yCoord q hm hq
  · intro hq
    subst q
    exact centroid_critical m xCoord yCoord
      (ne_of_gt (totalMass_pos hn m hm))

theorem gap4 {n : ℕ} (hn : 0 < n)
    (m xCoord yCoord : Fin n → ℝ) (hm : ∀ i, 0 < m i) :
    Coercive m xCoord yCoord := by
  unfold Coercive
  let i : Fin n := ⟨0, hn⟩
  have hmi : 0 < m i := hm i
  intro B
  let d : ℝ := |B| / m i + 1
  have hd1 : 1 ≤ d := by
    dsimp [d]
    have hdiv : 0 ≤ |B| / m i := div_nonneg (abs_nonneg B) hmi.le
    linarith
  have hd : 0 ≤ d := by linarith
  have hdsq : d ≤ d ^ 2 := by
    nlinarith [sq_nonneg (d - 1)]
  have hmul : m i * d = |B| + m i := by
    dsimp [d]
    field_simp [ne_of_gt hmi] <;> ring
  have hB : B ≤ m i * d ^ 2 := by
    calc
      B ≤ |B| := le_abs_self B
      _ ≤ |B| + m i := by linarith
      _ = m i * d := hmul.symm
      _ ≤ m i * d ^ 2 := mul_le_mul_of_nonneg_left hdsq hmi.le
  refine ⟨max |xCoord i| |yCoord i| + d, ?_⟩
  intro q hq
  have hterm_nonneg :
      ∀ j, 0 ≤ m j * ((q.1 - xCoord j) ^ 2 + (q.2 - yCoord j) ^ 2) := by
    intro j
    exact mul_nonneg (hm j).le
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hselected :
      m i * ((q.1 - xCoord i) ^ 2 + (q.2 - yCoord i) ^ 2) ≤
        cost m xCoord yCoord q := by
    unfold cost
    exact Finset.single_le_sum
      (fun j hj => hterm_nonneg j) (Finset.mem_univ i)
  have lower_sq (u a : ℝ)
      (ha : |a| ≤ max |xCoord i| |yCoord i|)
      (hu : max |xCoord i| |yCoord i| + d ≤ |u|) :
      d ^ 2 ≤ (u - a) ^ 2 := by
    have htri : |u| ≤ |u - a| + |a| := by
      calc
        |u| = |(u - a) + a| := by congr 1 <;> ring
        _ ≤ |u - a| + |a| := abs_add_le _ _
    have hda : d ≤ |u - a| := by linarith
    have hprod : 0 ≤ (|u - a| - d) * (|u - a| + d) :=
      mul_nonneg (sub_nonneg.mpr hda)
        (add_nonneg (abs_nonneg _) hd)
    have hs : d ^ 2 ≤ |u - a| ^ 2 := by
      nlinarith
    simpa only [sq_abs] using hs
  rcases le_total |q.1| |q.2| with h12 | h21
  · have hR : max |xCoord i| |yCoord i| + d ≤ |q.2| := by
      simpa [max_eq_right h12] using hq
    have hs : d ^ 2 ≤ (q.2 - yCoord i) ^ 2 :=
      lower_sq q.2 (yCoord i) (le_max_right _ _) hR
    have hbase :
        d ^ 2 ≤ (q.1 - xCoord i) ^ 2 + (q.2 - yCoord i) ^ 2 := by
      nlinarith [sq_nonneg (q.1 - xCoord i)]
    have hweighted := mul_le_mul_of_nonneg_left hbase hmi.le
    exact hB.trans (hweighted.trans hselected)
  · have hR : max |xCoord i| |yCoord i| + d ≤ |q.1| := by
      simpa [max_eq_left h21] using hq
    have hs : d ^ 2 ≤ (q.1 - xCoord i) ^ 2 :=
      lower_sq q.1 (xCoord i) (le_max_left _ _) hR
    have hbase :
        d ^ 2 ≤ (q.1 - xCoord i) ^ 2 + (q.2 - yCoord i) ^ 2 := by
      nlinarith [sq_nonneg (q.2 - yCoord i)]
    have hweighted := mul_le_mul_of_nonneg_left hbase hmi.le
    exact hB.trans (hweighted.trans hselected)

theorem gap5 {n : ℕ} (hn : 0 < n)
    (m xCoord yCoord : Fin n → ℝ) (hm : ∀ i, 0 < m i) :
    minimizers m xCoord yCoord =
      ({centroid m xCoord yCoord} : Set (ℝ × ℝ)) := by
  have hM : 0 < totalMass m := totalMass_pos hn m hm
  apply Set.ext
  intro q
  simp only [minimizers, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hq
    have hc := hq (centroid m xCoord yCoord)
    have hdec := cost_centroid_decomp m xCoord yCoord
      (ne_of_gt hM) q
    rw [hdec] at hc
    have hDnonneg :
        0 ≤ (q.1 - (centroid m xCoord yCoord).1) ^ 2 +
          (q.2 - (centroid m xCoord yCoord).2) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hprodle :
        totalMass m *
          ((q.1 - (centroid m xCoord yCoord).1) ^ 2 +
           (q.2 - (centroid m xCoord yCoord).2) ^ 2) ≤ 0 := by
      linarith
    have hprodge :
        0 ≤ totalMass m *
          ((q.1 - (centroid m xCoord yCoord).1) ^ 2 +
           (q.2 - (centroid m xCoord yCoord).2) ^ 2) :=
      mul_nonneg hM.le hDnonneg
    have hprodzero :
        totalMass m *
          ((q.1 - (centroid m xCoord yCoord).1) ^ 2 +
           (q.2 - (centroid m xCoord yCoord).2) ^ 2) = 0 :=
      le_antisymm hprodle hprodge
    have hDzero :
        (q.1 - (centroid m xCoord yCoord).1) ^ 2 +
          (q.2 - (centroid m xCoord yCoord).2) ^ 2 = 0 :=
      (mul_eq_zero.mp hprodzero).resolve_left (ne_of_gt hM)
    apply Prod.ext
    · nlinarith [sq_nonneg (q.1 - (centroid m xCoord yCoord).1),
        sq_nonneg (q.2 - (centroid m xCoord yCoord).2)]
    · nlinarith [sq_nonneg (q.1 - (centroid m xCoord yCoord).1),
        sq_nonneg (q.2 - (centroid m xCoord yCoord).2)]
  · intro hq
    subst q
    intro r
    rw [cost_centroid_decomp m xCoord yCoord (ne_of_gt hM) r]
    exact le_add_of_nonneg_right
      (mul_nonneg hM.le
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))

end

end ProofGap.Exercise3686
