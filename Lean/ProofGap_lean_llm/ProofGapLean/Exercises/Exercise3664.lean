import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3664

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def objective (q : Point3) : ℝ :=
  Real.sin q.x * Real.sin q.y * Real.sin q.z

def constraint : Set Point3 :=
  {q | q.x + q.y + q.z = Real.pi / 2 ∧
    0 < q.x ∧ 0 < q.y ∧ 0 < q.z}

def logObjective (q : Point3) : ℝ :=
  Real.log (objective q)

def critical (q : Point3) (lambda : ℝ) : Prop :=
  Real.cot q.x + lambda = 0 ∧
    Real.cot q.y + lambda = 0 ∧
    Real.cot q.z + lambda = 0 ∧
    q ∈ constraint

def P₀ : Point3 :=
  ⟨Real.pi / 6, Real.pi / 6, Real.pi / 6⟩

def maximizers : Set Point3 :=
  {q | q ∈ constraint ∧ ∀ r ∈ constraint, objective r ≤ objective q}

def ApproachesBoundary (q : ℕ → Point3) : Prop :=
  (∀ k, q k ∈ constraint) ∧
    Filter.Tendsto
      (fun k => min (q k).x (min (q k).y (q k).z))
      Filter.atTop (nhds 0)

private theorem p0_mem_constraint : P₀ ∈ constraint := by
  constructor
  · dsimp [P₀]
    ring
  · have hp : 0 < Real.pi / 6 := by positivity
    exact ⟨hp, hp, hp⟩

private theorem point3_eq_p0 (q : Point3)
    (hx : q.x = Real.pi / 6) (hy : q.y = Real.pi / 6)
    (hz : q.z = Real.pi / 6) : q = P₀ := by
  rcases q with ⟨x, y, z⟩
  dsimp only at hx hy hz
  subst x
  subst y
  subst z
  rfl

private theorem acute_sin_injective {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < Real.pi / 2)
    (hy0 : 0 < y) (hy1 : y < Real.pi / 2)
    (h : Real.sin x = Real.sin y) : x = y := by
  apply Real.strictMonoOn_sin.injOn
  · constructor <;> nlinarith [Real.pi_pos]
  · constructor <;> nlinarith [Real.pi_pos]
  · exact h

private theorem acute_cot_injective {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < Real.pi / 2)
    (hy0 : 0 < y) (hy1 : y < Real.pi / 2)
    (h : Real.cot x = Real.cot y) : x = y := by
  have hxpi : x < Real.pi := by nlinarith [Real.pi_pos]
  have hypi : y < Real.pi := by nlinarith [Real.pi_pos]
  have hsx : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)
  have hsy : Real.sin y ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hy0 hypi)
  have hdiv : Real.cos x / Real.sin x = Real.cos y / Real.sin y := by
    simpa only [Real.cot_eq_cos_div_sin] using h
  have hcross : Real.cos x * Real.sin y = Real.cos y * Real.sin x :=
    (div_eq_div_iff hsx hsy).mp hdiv
  have hsin : Real.sin (y - x) = 0 := by
    rw [Real.sin_sub]
    nlinarith
  have hmem : y - x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hzero : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have heq : y - x = 0 := by
    apply Real.strictMonoOn_sin.injOn hmem hzero
    simpa using hsin
  linarith

private theorem designated_product_bound {x y z : ℝ}
    (hx0 : 0 < x) (hy0 : 0 < y) (hz0 : 0 < z)
    (hsum : x + y + z = Real.pi / 2) :
    Real.sin x * Real.sin y * Real.sin z ≤ 1 / 8 ∧
      ((1 / 8 : ℝ) ≤ Real.sin x * Real.sin y * Real.sin z →
        Real.sin z = 1 / 2) := by
  have hxpi : x < Real.pi := by nlinarith [Real.pi_pos]
  have hypi : y < Real.pi := by nlinarith [Real.pi_pos]
  have hzpi : z < Real.pi := by nlinarith [Real.pi_pos]
  have hsx : 0 ≤ Real.sin x :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)
  have hsy : 0 ≤ Real.sin y :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hy0 hypi)
  have hsz : 0 ≤ Real.sin z :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hz0 hzpi)
  let m : ℝ := (x + y) / 2
  let d : ℝ := (x - y) / 2
  have hm0 : 0 < m := by
    dsimp [m]
    linarith
  have hmpi : m < Real.pi := by
    dsimp [m]
    nlinarith [Real.pi_pos]
  have hsinm : 0 ≤ Real.sin m :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hm0 hmpi)
  have hcosd : Real.cos d ≤ 1 := Real.cos_le_one d
  have hxmd : x = m + d := by
    dsimp [m, d]
    ring
  have hymd : y = m - d := by
    dsimp [m, d]
    ring
  have hsumtrig : Real.sin x + Real.sin y =
      2 * Real.sin m * Real.cos d := by
    rw [hxmd, hymd, Real.sin_add, Real.sin_sub]
    ring
  have hmul : Real.sin m * Real.cos d ≤ Real.sin m := by
    simpa using mul_le_mul_of_nonneg_left hcosd hsinm
  have havg : (Real.sin x + Real.sin y) / 2 ≤ Real.sin m := by
    nlinarith
  have havg0 : 0 ≤ (Real.sin x + Real.sin y) / 2 := by
    linarith
  have hamgm : Real.sin x * Real.sin y ≤
      ((Real.sin x + Real.sin y) / 2) ^ 2 := by
    nlinarith [sq_nonneg (Real.sin x - Real.sin y)]
  have havgsq : ((Real.sin x + Real.sin y) / 2) ^ 2 ≤
      Real.sin m ^ 2 := by
    nlinarith [sq_nonneg (Real.sin m -
      (Real.sin x + Real.sin y) / 2)]
  have hpair : Real.sin x * Real.sin y ≤ Real.sin m ^ 2 :=
    hamgm.trans havgsq
  have hproduct : Real.sin x * Real.sin y * Real.sin z ≤
      Real.sin m ^ 2 * Real.sin z :=
    mul_le_mul_of_nonneg_right hpair hsz
  have htwom : 2 * m = Real.pi / 2 - z := by
    dsimp [m]
    linarith
  have hcosrel : Real.cos (2 * m) = Real.sin z := by
    calc
      Real.cos (2 * m) = Real.cos (Real.pi / 2 - z) :=
        congrArg Real.cos htwom
      _ = Real.sin z := by rw [Real.cos_pi_div_two_sub]
  have hcosadd : Real.cos (2 * m) =
      Real.cos m * Real.cos m - Real.sin m * Real.sin m := by
    calc
      Real.cos (2 * m) = Real.cos (m + m) := by
        exact congrArg Real.cos (by ring)
      _ = Real.cos m * Real.cos m - Real.sin m * Real.sin m := by
        rw [Real.cos_add]
  have hsquares := Real.sin_sq_add_cos_sq m
  have hmid : Real.sin m ^ 2 = (1 - Real.sin z) / 2 := by
    nlinarith only [hcosrel, hcosadd, hsquares]
  have hproduct' : Real.sin x * Real.sin y * Real.sin z ≤
      ((1 - Real.sin z) / 2) * Real.sin z := by
    calc
      Real.sin x * Real.sin y * Real.sin z ≤
          Real.sin m ^ 2 * Real.sin z := hproduct
      _ = ((1 - Real.sin z) / 2) * Real.sin z := by rw [hmid]
  have hscalar : ((1 - Real.sin z) / 2) * Real.sin z ≤ (1 / 8 : ℝ) := by
    nlinarith only [sq_nonneg (Real.sin z - 1 / 2)]
  constructor
  · exact hproduct'.trans hscalar
  · intro hlower
    have hsqueeze : (1 / 8 : ℝ) ≤
        ((1 - Real.sin z) / 2) * Real.sin z :=
      hlower.trans hproduct'
    set_option maxHeartbeats 1000000 in
      nlinarith only [hsqueeze, sq_nonneg (Real.sin z - 1 / 2)]

private theorem objective_le_eighth (q : Point3) (hq : q ∈ constraint) :
    objective q ≤ 1 / 8 := by
  rcases hq with ⟨hsum, hx, hy, hz⟩
  simpa [objective] using
    (designated_product_bound hx hy hz hsum).1

private theorem objective_eq_point_of_lower_bound (q : Point3)
    (hq : q ∈ constraint) (hlower : (1 / 8 : ℝ) ≤ objective q) : q = P₀ := by
  rcases hq with ⟨hsum, hx, hy, hz⟩
  have hxhalf : Real.sin q.x = 1 / 2 := by
    apply (designated_product_bound hy hz hx (by linarith)).2
    simpa [objective, mul_comm, mul_left_comm, mul_assoc] using hlower
  have hyhalf : Real.sin q.y = 1 / 2 := by
    apply (designated_product_bound hz hx hy (by linarith)).2
    simpa [objective, mul_comm, mul_left_comm, mul_assoc] using hlower
  have hzhalf : Real.sin q.z = 1 / 2 := by
    apply (designated_product_bound hx hy hz hsum).2
    simpa [objective] using hlower
  have hp0 : 0 < Real.pi / 6 := by positivity
  have hp1 : Real.pi / 6 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hx1 : q.x < Real.pi / 2 := by linarith
  have hy1 : q.y < Real.pi / 2 := by linarith
  have hz1 : q.z < Real.pi / 2 := by linarith
  have hxeq : q.x = Real.pi / 6 := by
    apply acute_sin_injective hx hx1 hp0 hp1
    simpa [Real.sin_pi_div_six] using hxhalf
  have hyeq : q.y = Real.pi / 6 := by
    apply acute_sin_injective hy hy1 hp0 hp1
    simpa [Real.sin_pi_div_six] using hyhalf
  have hzeq : q.z = Real.pi / 6 := by
    apply acute_sin_injective hz hz1 hp0 hp1
    simpa [Real.sin_pi_div_six] using hzhalf
  exact point3_eq_p0 q hxeq hyeq hzeq

private theorem objective_pos (q : Point3) (hq : q ∈ constraint) :
    0 < objective q := by
  rcases hq with ⟨hsum, hx, hy, hz⟩
  have hxpi : q.x < Real.pi := by nlinarith [Real.pi_pos]
  have hypi : q.y < Real.pi := by nlinarith [Real.pi_pos]
  have hzpi : q.z < Real.pi := by nlinarith [Real.pi_pos]
  have hsx := Real.sin_pos_of_pos_of_lt_pi hx hxpi
  have hsy := Real.sin_pos_of_pos_of_lt_pi hy hypi
  have hsz := Real.sin_pos_of_pos_of_lt_pi hz hzpi
  exact mul_pos (mul_pos hsx hsy) hsz

private theorem three_sines_le_factor {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ 1) (hc1 : c ≤ 1) : a * b * c ≤ a := by
  calc
    a * b * c ≤ a * b := mul_le_of_le_one_right (mul_nonneg ha hb) hc1
    _ ≤ a := mul_le_of_le_one_right ha hb1

private theorem objective_le_min (q : Point3) (hq : q ∈ constraint) :
    objective q ≤ min q.x (min q.y q.z) := by
  rcases hq with ⟨hsum, hx, hy, hz⟩
  have hxpi : q.x < Real.pi := by nlinarith [Real.pi_pos]
  have hypi : q.y < Real.pi := by nlinarith [Real.pi_pos]
  have hzpi : q.z < Real.pi := by nlinarith [Real.pi_pos]
  have hsx : 0 ≤ Real.sin q.x :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hx hxpi)
  have hsy : 0 ≤ Real.sin q.y :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hy hypi)
  have hsz : 0 ≤ Real.sin q.z :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hz hzpi)
  have hsx1 : Real.sin q.x ≤ 1 := Real.sin_le_one q.x
  have hsy1 : Real.sin q.y ≤ 1 := Real.sin_le_one q.y
  have hsz1 : Real.sin q.z ≤ 1 := Real.sin_le_one q.z
  have hsxx : Real.sin q.x ≤ q.x := Real.sin_le (le_of_lt hx)
  have hsyy : Real.sin q.y ≤ q.y := Real.sin_le (le_of_lt hy)
  have hszz : Real.sin q.z ≤ q.z := Real.sin_le (le_of_lt hz)
  apply le_min
  · exact (three_sines_le_factor hsx hsy hsz hsy1 hsz1).trans hsxx
  · apply le_min
    · have hprod : Real.sin q.x * Real.sin q.y * Real.sin q.z ≤ Real.sin q.y := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (three_sines_le_factor hsy hsx hsz hsx1 hsz1)
      exact hprod.trans hsyy
    · have hprod : Real.sin q.x * Real.sin q.y * Real.sin q.z ≤ Real.sin q.z := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (three_sines_le_factor hsz hsx hsy hsx1 hsy1)
      exact hprod.trans hszz

private theorem objective_p0 : objective P₀ = 1 / 8 := by
  norm_num [objective, P₀, Real.sin_pi_div_six]

theorem gap1 :
    ∀ q ∈ constraint, 0 < q.x := by
  intro q hq
  exact hq.2.1

theorem gap2 :
    ∀ q ∈ constraint, q.x < Real.pi / 2 := by
  intro q hq
  rcases hq with ⟨hsum, hx, hy, hz⟩
  linarith

theorem gap3 :
    ∀ q ∈ constraint, 0 < q.y := by
  intro q hq
  exact hq.2.2.1

theorem gap4 :
    ∀ q ∈ constraint, q.y < Real.pi / 2 := by
  intro q hq
  rcases hq with ⟨hsum, hx, hy, hz⟩
  linarith

theorem gap5 :
    ∀ q ∈ constraint, 0 < q.z := by
  intro q hq
  exact hq.2.2.2

theorem gap6 :
    ∀ q ∈ constraint, q.z < Real.pi / 2 := by
  intro q hq
  rcases hq with ⟨hsum, hx, hy, hz⟩
  linarith

theorem gap7 :
    ∀ q ∈ constraint,
      logObjective q =
        Real.log (Real.sin q.x) +
          Real.log (Real.sin q.y) + Real.log (Real.sin q.z) := by
  intro q hq
  have hxpi : q.x < Real.pi := by
    have hx := gap2 q hq
    nlinarith [Real.pi_pos]
  have hypi : q.y < Real.pi := by
    have hy := gap4 q hq
    nlinarith [Real.pi_pos]
  have hzpi : q.z < Real.pi := by
    have hz := gap6 q hq
    nlinarith [Real.pi_pos]
  have hsx : Real.sin q.x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (gap1 q hq) hxpi)
  have hsy : Real.sin q.y ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (gap3 q hq) hypi)
  have hsz : Real.sin q.z ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (gap5 q hq) hzpi)
  rw [logObjective, objective,
    Real.log_mul (mul_ne_zero hsx hsy) hsz, Real.log_mul hsx hsy]

theorem gap8 :
    ∃ P : Point3, P = P₀ := by
  exact ⟨P₀, rfl⟩

theorem gap9 :
    {q | ∃ lambda, critical q lambda} = ({P₀} : Set Point3) := by
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨lambda, hc⟩
    rcases hc with ⟨hcx, hcy, hcz, hq⟩
    have hxycot : Real.cot q.x = Real.cot q.y := by linarith
    have hxzcot : Real.cot q.x = Real.cot q.z := by linarith
    have hxy : q.x = q.y :=
      acute_cot_injective (gap1 q hq) (gap2 q hq)
        (gap3 q hq) (gap4 q hq) hxycot
    have hxz : q.x = q.z :=
      acute_cot_injective (gap1 q hq) (gap2 q hq)
        (gap5 q hq) (gap6 q hq) hxzcot
    rcases hq with ⟨hsum, hx, hy, hz⟩
    have hqx : q.x = Real.pi / 6 := by linarith
    have hqy : q.y = Real.pi / 6 := by linarith
    have hqz : q.z = Real.pi / 6 := by linarith
    exact point3_eq_p0 q hqx hqy hqz
  · intro hq
    subst q
    refine ⟨-Real.cot (Real.pi / 6), ?_⟩
    exact ⟨by simp [P₀], by simp [P₀], by simp [P₀], p0_mem_constraint⟩

theorem gap10 :
    ∀ q : ℕ → Point3, ApproachesBoundary q →
      Filter.Tendsto (fun k => objective (q k))
        Filter.atTop (nhds 0) := by
  intro q hq
  rcases hq with ⟨hqcon, hmin⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hmin
  · intro k
    exact le_of_lt (objective_pos (q k) (hqcon k))
  · intro k
    exact objective_le_min (q k) (hqcon k)

theorem gap11 :
    ∀ q ∈ constraint, objective q > 0 := by
  intro q hq
  exact objective_pos q hq

theorem gap12 :
    maximizers = ({P₀} : Set Point3) := by
  ext q
  simp only [maximizers, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hq
    have hlower : (1 / 8 : ℝ) ≤ objective q := by
      have hp := hq.2 P₀ p0_mem_constraint
      rw [objective_p0] at hp
      exact hp
    exact objective_eq_point_of_lower_bound q hq.1 hlower
  · intro hq
    subst q
    refine ⟨p0_mem_constraint, ?_⟩
    intro r hr
    rw [objective_p0]
    exact objective_le_eighth r hr

theorem gap13 :
    objective P₀ = 1 / 8 := by
  exact objective_p0

end

end ProofGap.Exercise3664
