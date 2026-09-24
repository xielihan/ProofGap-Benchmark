import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1559

noncomputable section

def objective (a m n x : ℝ) : ℝ :=
  Real.rpow x m + Real.rpow (a / x) n

def optimizer (a m n : ℝ) : ℝ :=
  Real.rpow (n / m) (1 / (m + n)) *
    Real.rpow a (n / (m + n))

def minimumValue (a m n : ℝ) : ℝ :=
  (m + n) * Real.rpow
    (Real.rpow a (m * n) / (Real.rpow m m * Real.rpow n n))
    (1 / (m + n))

def IsMinimizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x₀ ≤ u x

private theorem rpow_one_exp (x : ℝ) :
    Real.rpow x (1 : ℝ) = x := by
  change x ^ (1 : ℝ) = x
  exact Real.rpow_one x

private theorem rpow_add_of_pos
    (x p q : ℝ) (hx : 0 < x) :
    Real.rpow x (p + q) = Real.rpow x p * Real.rpow x q := by
  exact Real.rpow_add hx p q

private theorem rpow_mul_of_pos
    (x y p : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.rpow (x * y) p = Real.rpow x p * Real.rpow y p := by
  exact Real.mul_rpow hx.le hy.le

private theorem rpow_div_of_pos
    (x y p : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.rpow (x / y) p = Real.rpow x p / Real.rpow y p := by
  exact Real.div_rpow hx.le hy.le p

private theorem rpow_rpow_of_pos
    (x p q : ℝ) (hx : 0 < x) :
    Real.rpow (Real.rpow x p) q = Real.rpow x (p * q) := by
  exact (Real.rpow_mul hx.le p q).symm

private theorem objective_hasDerivAt_raw
    (a m n x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (objective a m n)
      (m * Real.rpow x (m - 1) +
        n * Real.rpow (a / x) (n - 1) * (-a / x ^ 2)) x := by
  have hquot : HasDerivAt (fun y : ℝ => a / y) (-a / x ^ 2) x := by
    simpa using (hasDerivAt_const x a).div (hasDerivAt_id x) hx.ne'
  have hfirst :
      HasDerivAt (fun y : ℝ => Real.rpow y m)
        (m * Real.rpow x (m - 1)) x :=
    Real.hasDerivAt_rpow_const (p := m) (Or.inl hx.ne')
  have hax : 0 < a / x := div_pos ha hx
  have hbase :
      HasDerivAt (fun y : ℝ => Real.rpow y n)
        (n * Real.rpow (a / x) (n - 1)) (a / x) :=
    Real.hasDerivAt_rpow_const (p := n) (Or.inl hax.ne')
  have hsecond := hbase.comp x hquot
  simpa [objective] using hfirst.add hsecond

private theorem optimizer_rpow_sum
    (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    Real.rpow (optimizer a m n) (m + n) =
      (n / m) * Real.rpow a n := by
  have hs : 0 < m + n := add_pos hm hn
  have hp : 0 < n / m := div_pos hn hm
  have hu : 0 < Real.rpow (n / m) (1 / (m + n)) :=
    Real.rpow_pos_of_pos hp _
  have hv : 0 < Real.rpow a (n / (m + n)) :=
    Real.rpow_pos_of_pos ha _
  unfold optimizer
  rw [rpow_mul_of_pos _ _ _ hu hv]
  rw [rpow_rpow_of_pos (n / m) _ _ hp]
  rw [rpow_rpow_of_pos a _ _ ha]
  have he1 : (1 / (m + n)) * (m + n) = 1 := by
    field_simp [ne_of_gt hs]
  have he2 : (n / (m + n)) * (m + n) = n := by
    field_simp [ne_of_gt hs]
  rw [he1, he2, rpow_one_exp]

private theorem minimum_core_eq
    (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    Real.rpow
        (Real.rpow a (m * n) /
          (Real.rpow m m * Real.rpow n n))
        (1 / (m + n)) =
      Real.rpow (optimizer a m n) m / n := by
  have hs : 0 < m + n := add_pos hm hn
  have hp : 0 < n / m := div_pos hn hm
  let A := Real.rpow a (m * n / (m + n))
  let M := Real.rpow m (m / (m + n))
  let N := Real.rpow n (n / (m + n))
  let P := Real.rpow n (m / (m + n))
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hM : 0 < M := Real.rpow_pos_of_pos hm _
  have hN : 0 < N := Real.rpow_pos_of_pos hn _
  have hP : 0 < P := Real.rpow_pos_of_pos hn _
  have hPNraw :
      Real.rpow n (m / (m + n)) * Real.rpow n (n / (m + n)) = n := by
    rw [← rpow_add_of_pos n (m / (m + n)) (n / (m + n)) hn]
    have he : m / (m + n) + n / (m + n) = (1 : ℝ) := by
      field_simp [ne_of_gt hs]
    rw [he, rpow_one_exp]
  have hPN : P * N = n := hPNraw
  have haa : 0 < Real.rpow a (m * n) := Real.rpow_pos_of_pos ha _
  have hmm : 0 < Real.rpow m m := Real.rpow_pos_of_pos hm _
  have hnn : 0 < Real.rpow n n := Real.rpow_pos_of_pos hn _
  have hnum :
      Real.rpow (Real.rpow a (m * n)) (1 / (m + n)) = A := by
    rw [rpow_rpow_of_pos a (m * n) (1 / (m + n)) ha]
    dsimp [A]
    congr 1
    field_simp [ne_of_gt hs]
  have hmterm :
      Real.rpow (Real.rpow m m) (1 / (m + n)) = M := by
    rw [rpow_rpow_of_pos m m (1 / (m + n)) hm]
    dsimp [M]
    congr 1
    field_simp [ne_of_gt hs]
  have hnterm :
      Real.rpow (Real.rpow n n) (1 / (m + n)) = N := by
    rw [rpow_rpow_of_pos n n (1 / (m + n)) hn]
    dsimp [N]
    congr 1
    field_simp [ne_of_gt hs]
  have hleft :
      Real.rpow
          (Real.rpow a (m * n) /
            (Real.rpow m m * Real.rpow n n))
          (1 / (m + n)) = A / (M * N) := by
    rw [rpow_div_of_pos _ _ _ haa (mul_pos hmm hnn)]
    rw [rpow_mul_of_pos _ _ _ hmm hnn]
    rw [hnum, hmterm, hnterm]
  have hu :
      Real.rpow (Real.rpow (n / m) (1 / (m + n))) m = P / M := by
    rw [rpow_rpow_of_pos (n / m) (1 / (m + n)) m hp]
    rw [rpow_div_of_pos n m (1 / (m + n) * m) hn hm]
    have he : (1 / (m + n)) * m = m / (m + n) := by
      field_simp [ne_of_gt hs]
    dsimp [P, M]
    rw [he]
  have hv :
      Real.rpow (Real.rpow a (n / (m + n))) m = A := by
    rw [rpow_rpow_of_pos a (n / (m + n)) m ha]
    have he : n / (m + n) * m = m * n / (m + n) := by
      field_simp [ne_of_gt hs]
    dsimp [A]
    rw [he]
  have hprod :
      Real.rpow
          (Real.rpow (n / m) (1 / (m + n)) *
            Real.rpow a (n / (m + n))) m =
        Real.rpow (Real.rpow (n / m) (1 / (m + n))) m *
          Real.rpow (Real.rpow a (n / (m + n))) m :=
    rpow_mul_of_pos _ _ _
      (Real.rpow_pos_of_pos hp _)
      (Real.rpow_pos_of_pos ha _)
  have hright :
      Real.rpow (optimizer a m n) m / n = (P / M * A) / n := by
    unfold optimizer
    rw [hprod, hu, hv]
  rw [hleft, hright]
  rw [← hPN]
  field_simp [hM.ne', hN.ne', hP.ne'] <;> ring

theorem gap1 (a m n x : ℝ) :
    objective a m n x = Real.rpow x m + Real.rpow (a / x) n := by
  rfl

theorem gap2 (a m n x : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n)
    (hx : 0 < x) :
    deriv (objective a m n) x =
      (m * Real.rpow x (m + n) - n * Real.rpow a n) /
        Real.rpow x (n + 1) := by
  have hraw := objective_hasDerivAt_raw a m n x ha hx
  rw [hraw.deriv]
  have hdiv :
      Real.rpow (a / x) (n - 1) =
        Real.rpow a (n - 1) / Real.rpow x (n - 1) :=
    rpow_div_of_pos a x (n - 1) ha hx
  rw [hdiv]
  have hamul : Real.rpow a (n - 1) * a = Real.rpow a n := by
    calc
      Real.rpow a (n - 1) * a =
          Real.rpow a (n - 1) * Real.rpow a 1 := by
            rw [rpow_one_exp]
      _ = Real.rpow a ((n - 1) + 1) :=
        (rpow_add_of_pos a (n - 1) 1 ha).symm
      _ = Real.rpow a n := by
        congr 1
        ring
  have hx2 : Real.rpow x (2 : ℝ) = x ^ 2 := by
    calc
      Real.rpow x (2 : ℝ) = Real.rpow x ((1 : ℝ) + 1) := by
        congr 1
        ring
      _ = Real.rpow x 1 * Real.rpow x 1 :=
        rpow_add_of_pos x 1 1 hx
      _ = x ^ 2 := by
        rw [rpow_one_exp]
        ring
  have hxden : Real.rpow x (n - 1) * x ^ 2 = Real.rpow x (n + 1) := by
    calc
      Real.rpow x (n - 1) * x ^ 2 =
          Real.rpow x (n - 1) * Real.rpow x (2 : ℝ) := by
            rw [hx2]
      _ = Real.rpow x ((n - 1) + 2) :=
        (rpow_add_of_pos x (n - 1) 2 hx).symm
      _ = Real.rpow x (n + 1) := by
        congr 1
        ring
  have hxmul :
      Real.rpow x (m - 1) * Real.rpow x (n + 1) =
        Real.rpow x (m + n) := by
    calc
      Real.rpow x (m - 1) * Real.rpow x (n + 1) =
          Real.rpow x ((m - 1) + (n + 1)) :=
        (rpow_add_of_pos x (m - 1) (n + 1) hx).symm
      _ = Real.rpow x (m + n) := by
        congr 1
        ring
  have hxn1 : Real.rpow x (n - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hxnp1 : Real.rpow x (n + 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hsecond :
      n * (Real.rpow a (n - 1) / Real.rpow x (n - 1)) *
          (-a / x ^ 2) =
        -n * Real.rpow a n / Real.rpow x (n + 1) := by
    calc
      n * (Real.rpow a (n - 1) / Real.rpow x (n - 1)) *
          (-a / x ^ 2) =
          -(n * (Real.rpow a (n - 1) * a)) /
            (Real.rpow x (n - 1) * x ^ 2) := by
              field_simp [hxn1, hx.ne'] <;> ring
      _ = -(n * Real.rpow a n) / Real.rpow x (n + 1) := by
        rw [hamul, hxden]
      _ = -n * Real.rpow a n / Real.rpow x (n + 1) := by
        ring
  have hxmdiv :
      Real.rpow x (m - 1) =
        Real.rpow x (m + n) / Real.rpow x (n + 1) :=
    (eq_div_iff hxnp1).2 hxmul
  rw [hsecond, hxmdiv]
  ring

theorem gap3 (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    0 < optimizer a m n := by
  unfold optimizer
  exact mul_pos
    (Real.rpow_pos_of_pos (div_pos hn hm) _)
    (Real.rpow_pos_of_pos ha _)

theorem gap4 (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    deriv (objective a m n) (optimizer a m n) = 0 := by
  have ho : 0 < optimizer a m n := gap3 a m n ha hm hn
  rw [gap2 a m n (optimizer a m n) ha hm hn ho]
  rw [optimizer_rpow_sum a m n ha hm hn]
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hden : Real.rpow (optimizer a m n) (n + 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ho _)
  field_simp [hm0, hden] <;> ring

theorem gap5 (a m n x : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n)
    (hx : x ∈ Set.Ioo 0 (optimizer a m n)) :
    deriv (objective a m n) x < 0 := by
  have hx0 : 0 < x := hx.1
  have ho : 0 < optimizer a m n := gap3 a m n ha hm hn
  have hs : 0 < m + n := add_pos hm hn
  have hpows :
      Real.rpow x (m + n) <
        Real.rpow (optimizer a m n) (m + n) :=
    Real.rpow_lt_rpow hx0.le hx.2 hs
  rw [gap2 a m n x ha hm hn hx0]
  have hopt := optimizer_rpow_sum a m n ha hm hn
  rw [hopt] at hpows
  have hnum :
      m * Real.rpow x (m + n) - n * Real.rpow a n < 0 := by
    have hm0 : m ≠ 0 := ne_of_gt hm
    field_simp [hm0] at hpows
    nlinarith
  exact div_neg_of_neg_of_pos hnum (Real.rpow_pos_of_pos hx0 _)

theorem gap6 (a m n x : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n)
    (hx : x ∈ Set.Ioi (optimizer a m n)) :
    0 < deriv (objective a m n) x := by
  have ho : 0 < optimizer a m n := gap3 a m n ha hm hn
  have hx0 : 0 < x := lt_trans ho hx
  have hs : 0 < m + n := add_pos hm hn
  have hpows :
      Real.rpow (optimizer a m n) (m + n) <
        Real.rpow x (m + n) :=
    Real.rpow_lt_rpow ho.le hx hs
  rw [gap2 a m n x ha hm hn hx0]
  have hopt := optimizer_rpow_sum a m n ha hm hn
  rw [hopt] at hpows
  have hnum :
      0 < m * Real.rpow x (m + n) - n * Real.rpow a n := by
    have hm0 : m ≠ 0 := ne_of_gt hm
    field_simp [hm0] at hpows
    nlinarith
  exact div_pos hnum (Real.rpow_pos_of_pos hx0 _)

theorem gap7 (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    IsMinimizerOn (objective a m n) (Set.Ioi 0) (optimizer a m n) := by
  have ho : 0 < optimizer a m n := gap3 a m n ha hm hn
  constructor
  · exact ho
  · intro x hx
    rcases lt_trichotomy x (optimizer a m n) with hxo | hxo | hxo
    · have hcont :
          ContinuousOn (objective a m n)
            (Set.Icc x (optimizer a m n)) := by
        intro y hy
        have hy0 : 0 < y := lt_of_lt_of_le hx hy.1
        exact
          (objective_hasDerivAt_raw a m n y ha hy0).continuousAt.continuousWithinAt
      have hdiff :
          DifferentiableOn ℝ (objective a m n)
            (Set.Ioo x (optimizer a m n)) := by
        intro y hy
        have hy0 : 0 < y := lt_trans hx hy.1
        exact
          (objective_hasDerivAt_raw a m n y ha hy0).differentiableAt.differentiableWithinAt
      obtain ⟨c, hc, hcderiv⟩ :=
        exists_deriv_eq_slope (f := objective a m n) hxo hcont hdiff
      have hcneg : deriv (objective a m n) c < 0 :=
        gap5 a m n c ha hm hn ⟨lt_trans hx hc.1, hc.2⟩
      have hslope :
          (objective a m n (optimizer a m n) - objective a m n x) /
              (optimizer a m n - x) < 0 := by
        rw [← hcderiv]
        exact hcneg
      have hden : 0 < optimizer a m n - x := sub_pos.mpr hxo
      have hprod :
          ((objective a m n (optimizer a m n) - objective a m n x) /
              (optimizer a m n - x)) * (optimizer a m n - x) < 0 :=
        mul_neg_of_neg_of_pos hslope hden
      have hcancel :
          ((objective a m n (optimizer a m n) - objective a m n x) /
              (optimizer a m n - x)) * (optimizer a m n - x) =
            objective a m n (optimizer a m n) - objective a m n x := by
        field_simp [ne_of_gt hden]
      rw [hcancel] at hprod
      exact le_of_lt (sub_neg.mp hprod)
    · simpa [hxo]
    · have hcont :
          ContinuousOn (objective a m n)
            (Set.Icc (optimizer a m n) x) := by
        intro y hy
        have hy0 : 0 < y := lt_of_lt_of_le ho hy.1
        exact
          (objective_hasDerivAt_raw a m n y ha hy0).continuousAt.continuousWithinAt
      have hdiff :
          DifferentiableOn ℝ (objective a m n)
            (Set.Ioo (optimizer a m n) x) := by
        intro y hy
        have hy0 : 0 < y := lt_trans ho hy.1
        exact
          (objective_hasDerivAt_raw a m n y ha hy0).differentiableAt.differentiableWithinAt
      obtain ⟨c, hc, hcderiv⟩ :=
        exists_deriv_eq_slope (f := objective a m n) hxo hcont hdiff
      have hcpos : 0 < deriv (objective a m n) c :=
        gap6 a m n c ha hm hn hc.1
      have hslope :
          0 < (objective a m n x - objective a m n (optimizer a m n)) /
              (x - optimizer a m n) := by
        rw [← hcderiv]
        exact hcpos
      have hden : 0 < x - optimizer a m n := sub_pos.mpr hxo
      have hprod :
          0 < ((objective a m n x - objective a m n (optimizer a m n)) /
              (x - optimizer a m n)) * (x - optimizer a m n) :=
        mul_pos hslope hden
      have hcancel :
          ((objective a m n x - objective a m n (optimizer a m n)) /
              (x - optimizer a m n)) * (x - optimizer a m n) =
            objective a m n x - objective a m n (optimizer a m n) := by
        field_simp [ne_of_gt hden]
      rw [hcancel] at hprod
      exact le_of_lt (sub_pos.mp hprod)

theorem gap8 (a m n : ℝ) :
    minimumValue a m n =
      (m + n) * Real.rpow
        (Real.rpow a (m * n) / (Real.rpow m m * Real.rpow n n))
        (1 / (m + n)) := by
  rfl

theorem gap9 (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    objective a m n (optimizer a m n) = minimumValue a m n := by
  have ho : 0 < optimizer a m n := gap3 a m n ha hm hn
  have hopt := optimizer_rpow_sum a m n ha hm hn
  have hsplit :
      Real.rpow (optimizer a m n) (m + n) =
        Real.rpow (optimizer a m n) m *
          Real.rpow (optimizer a m n) n :=
    rpow_add_of_pos (optimizer a m n) m n ho
  have hrel :
      m * Real.rpow (optimizer a m n) (m + n) =
        n * Real.rpow a n := by
    rw [hopt]
    field_simp [ne_of_gt hm]
  have hsecond :
      Real.rpow (a / optimizer a m n) n =
        (m / n) * Real.rpow (optimizer a m n) m := by
    rw [rpow_div_of_pos a (optimizer a m n) n ha ho]
    have hon : Real.rpow (optimizer a m n) n ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos ho _)
    field_simp [ne_of_gt hn, hon]
    rw [hsplit] at hrel
    nlinarith
  rw [gap1, hsecond]
  rw [minimumValue, minimum_core_eq a m n ha hm hn]
  field_simp [ne_of_gt hn] <;> ring

end

end ProofGap.Exercise1559
