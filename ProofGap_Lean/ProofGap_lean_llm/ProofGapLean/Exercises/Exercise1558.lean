import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1558

noncomputable section

def objective (a m n x : ℝ) : ℝ :=
  Real.rpow x m * Real.rpow (a - x) n

def optimizer (a m n : ℝ) : ℝ := m * a / (m + n)

def IsMaximizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x ≤ u x₀

private theorem objective_hasDerivAt (a m n x : ℝ)
    (hx : x ∈ Set.Ioo 0 a) :
    HasDerivAt (objective a m n)
      (Real.rpow x (m - 1) * Real.rpow (a - x) (n - 1) *
        (m * a - (m + n) * x)) x := by
  have hxone : Real.rpow x (1 : ℝ) = x := by
    change x ^ (1 : ℝ) = x
    exact Real.rpow_one x
  have hxm : Real.rpow x m = Real.rpow x (m - 1) * x := by
    calc
      Real.rpow x m = Real.rpow x ((m - 1) + 1) := by
        exact congrArg (Real.rpow x) (by ring)
      _ = Real.rpow x (m - 1) * Real.rpow x 1 := by
        exact Real.rpow_add hx.1 (m - 1) 1
      _ = Real.rpow x (m - 1) * x := by
        rw [hxone]
  have hax : 0 < a - x := sub_pos.mpr hx.2
  have haone : Real.rpow (a - x) (1 : ℝ) = a - x := by
    change (a - x) ^ (1 : ℝ) = a - x
    exact Real.rpow_one (a - x)
  have han : Real.rpow (a - x) n =
      Real.rpow (a - x) (n - 1) * (a - x) := by
    calc
      Real.rpow (a - x) n = Real.rpow (a - x) ((n - 1) + 1) := by
        exact congrArg (Real.rpow (a - x)) (by ring)
      _ = Real.rpow (a - x) (n - 1) * Real.rpow (a - x) 1 := by
        exact Real.rpow_add hax (n - 1) 1
      _ = Real.rpow (a - x) (n - 1) * (a - x) := by
        rw [haone]
  have h₁ : HasDerivAt (fun y : ℝ => Real.rpow y m)
      (m * Real.rpow x (m - 1)) x := by
    exact Real.hasDerivAt_rpow_const (p := m) (Or.inl (ne_of_gt hx.1))
  have hinner : HasDerivAt (fun y : ℝ => a - y) (-1) x := by
    convert (hasDerivAt_const (x := x) a).sub (hasDerivAt_id x) using 1 <;> ring
  have hbase : HasDerivAt (fun z : ℝ => Real.rpow z n)
      (n * Real.rpow (a - x) (n - 1)) (a - x) := by
    exact Real.hasDerivAt_rpow_const (p := n) (Or.inl (ne_of_gt hax))
  have h₂ : HasDerivAt (fun y : ℝ => Real.rpow (a - y) n)
      (-n * Real.rpow (a - x) (n - 1)) x := by
    convert hbase.comp x hinner using 1 <;> ring
  convert h₁.mul h₂ using 1
  rw [hxm, han]
  ring

theorem gap1 (a m n x : ℝ) :
    objective a m n x = Real.rpow x m * Real.rpow (a - x) n := by
  rfl

theorem gap2 (a m n x : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n)
    (hx : x ∈ Set.Ioo 0 a) :
    deriv (objective a m n) x =
      Real.rpow x (m - 1) * Real.rpow (a - x) (n - 1) *
        (m * a - (m + n) * x) := by
  exact (objective_hasDerivAt a m n x hx).deriv

theorem gap3 (a m n x : ℝ) (hmn : m + n ≠ 0)
    (h : m * a - (m + n) * x = 0) :
    x = optimizer a m n := by
  unfold optimizer
  apply (eq_div_iff hmn).2
  linarith

theorem gap4 (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    optimizer a m n ∈ Set.Ioo 0 a := by
  have hs : 0 < m + n := add_pos hm hn
  constructor
  · unfold optimizer
    exact div_pos (mul_pos hm ha) hs
  · unfold optimizer
    rw [div_lt_iff₀ hs]
    nlinarith

theorem gap5 (a m n x : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n)
    (hx : x ∈ Set.Ioo 0 (optimizer a m n)) :
    0 < deriv (objective a m n) x := by
  have hs : 0 < m + n := add_pos hm hn
  have hop := gap4 a m n ha hm hn
  have hxa : x < a := lt_trans hx.2 hop.2
  have hxopt : x < m * a / (m + n) := by
    simpa [optimizer] using hx.2
  have hlin : 0 < m * a - (m + n) * x := by
    have hcross := (lt_div_iff₀ hs).mp hxopt
    nlinarith
  rw [gap2 a m n x ha hm hn ⟨hx.1, hxa⟩]
  have hp : 0 < Real.rpow x (m - 1) := Real.rpow_pos_of_pos hx.1 _
  have hq : 0 < Real.rpow (a - x) (n - 1) :=
    Real.rpow_pos_of_pos (sub_pos.mpr hxa) _
  positivity

theorem gap6 (a m n x : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n)
    (hx : x ∈ Set.Ioo (optimizer a m n) a) :
    deriv (objective a m n) x < 0 := by
  have hs : 0 < m + n := add_pos hm hn
  have hop := gap4 a m n ha hm hn
  have hx0 : 0 < x := lt_trans hop.1 hx.1
  have hoptx : m * a / (m + n) < x := by
    simpa [optimizer] using hx.1
  have hlin : m * a - (m + n) * x < 0 := by
    have hcross := (div_lt_iff₀ hs).mp hoptx
    nlinarith
  rw [gap2 a m n x ha hm hn ⟨hx0, hx.2⟩]
  have hp : 0 < Real.rpow x (m - 1) := Real.rpow_pos_of_pos hx0 _
  have hq : 0 < Real.rpow (a - x) (n - 1) :=
    Real.rpow_pos_of_pos (sub_pos.mpr hx.2) _
  nlinarith [mul_pos hp hq]

theorem gap7 (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    IsMaximizerOn (objective a m n) (Set.Ioo 0 a) (optimizer a m n) := by
  have hop := gap4 a m n ha hm hn
  refine ⟨hop, ?_⟩
  intro x hx
  rcases lt_trichotomy x (optimizer a m n) with hxo | hxe | hox
  · have hcont : ContinuousOn (objective a m n)
        (Set.Icc x (optimizer a m n)) := by
      intro y hy
      have hy' : y ∈ Set.Ioo 0 a :=
        ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hop.2⟩
      exact (objective_hasDerivAt a m n y hy').continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (objective a m n)
        (Set.Ioo x (optimizer a m n)) := by
      intro y hy
      have hy' : y ∈ Set.Ioo 0 a :=
        ⟨lt_trans hx.1 hy.1, lt_trans hy.2 hop.2⟩
      exact (objective_hasDerivAt a m n y hy').differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hder⟩ :=
      exists_deriv_eq_slope (objective a m n) hxo hcont hdiff
    have hslope : 0 <
        (objective a m n (optimizer a m n) - objective a m n x) /
          (optimizer a m n - x) := by
      rw [← hder]
      exact gap5 a m n c ha hm hn ⟨lt_trans hx.1 hc.1, hc.2⟩
    have hden : 0 < optimizer a m n - x := sub_pos.mpr hxo
    have hnum : 0 <
        objective a m n (optimizer a m n) - objective a m n x := by
      rcases (div_pos_iff.mp hslope) with h | h
      · exact h.1
      · exact (not_lt_of_ge hden.le h.2).elim
    exact (sub_pos.mp hnum).le
  · simpa [hxe]
  · have hcont : ContinuousOn (objective a m n)
        (Set.Icc (optimizer a m n) x) := by
      intro y hy
      have hy' : y ∈ Set.Ioo 0 a :=
        ⟨lt_of_lt_of_le hop.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
      exact (objective_hasDerivAt a m n y hy').continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (objective a m n)
        (Set.Ioo (optimizer a m n) x) := by
      intro y hy
      have hy' : y ∈ Set.Ioo 0 a :=
        ⟨lt_trans hop.1 hy.1, lt_trans hy.2 hx.2⟩
      exact (objective_hasDerivAt a m n y hy').differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hder⟩ :=
      exists_deriv_eq_slope (objective a m n) hox hcont hdiff
    have hslope :
        (objective a m n x - objective a m n (optimizer a m n)) /
            (x - optimizer a m n) < 0 := by
      rw [← hder]
      exact gap6 a m n c ha hm hn ⟨hc.1, lt_trans hc.2 hx.2⟩
    have hden : 0 < x - optimizer a m n := sub_pos.mpr hox
    have hnum :
        objective a m n x - objective a m n (optimizer a m n) < 0 := by
      rcases (div_neg_iff.mp hslope) with h | h
      · exact (not_lt_of_ge hden.le h.2).elim
      · exact h.1
    exact (sub_neg.mp hnum).le

theorem gap8 (a m n : ℝ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    objective a m n (optimizer a m n) =
      Real.rpow a (m + n) * Real.rpow m m * Real.rpow n n /
        Real.rpow (m + n) (m + n) := by
  have hs : 0 < m + n := add_pos hm hn
  have hopt : optimizer a m n = a * m / (m + n) := by
    unfold optimizer
    ring
  have hrem : a - a * m / (m + n) = a * n / (m + n) := by
    field_simp [ne_of_gt hs]
    ring
  rw [objective, hopt, hrem]
  have hdivm : Real.rpow (a * m / (m + n)) m =
      Real.rpow (a * m) m / Real.rpow (m + n) m := by
    change (a * m / (m + n)) ^ m = (a * m) ^ m / (m + n) ^ m
    exact Real.div_rpow (mul_nonneg ha.le hm.le) hs.le m
  have hdivn : Real.rpow (a * n / (m + n)) n =
      Real.rpow (a * n) n / Real.rpow (m + n) n := by
    change (a * n / (m + n)) ^ n = (a * n) ^ n / (m + n) ^ n
    exact Real.div_rpow (mul_nonneg ha.le hn.le) hs.le n
  have hmulm : Real.rpow (a * m) m = Real.rpow a m * Real.rpow m m := by
    change (a * m) ^ m = a ^ m * m ^ m
    exact Real.mul_rpow ha.le hm.le
  have hmuln : Real.rpow (a * n) n = Real.rpow a n * Real.rpow n n := by
    change (a * n) ^ n = a ^ n * n ^ n
    exact Real.mul_rpow ha.le hn.le
  have haadd : Real.rpow a (m + n) = Real.rpow a m * Real.rpow a n := by
    change a ^ (m + n) = a ^ m * a ^ n
    exact Real.rpow_add ha m n
  have hsadd : Real.rpow (m + n) (m + n) =
      Real.rpow (m + n) m * Real.rpow (m + n) n := by
    change (m + n) ^ (m + n) = (m + n) ^ m * (m + n) ^ n
    exact Real.rpow_add hs m n
  rw [hdivm, hdivn, hmulm, hmuln, haadd, hsadd]
  have hsm : Real.rpow (m + n) m ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hs m)
  have hsn : Real.rpow (m + n) n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hs n)
  field_simp [hsm, hsn]

end

end ProofGap.Exercise1558
