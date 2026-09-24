import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3647

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def u (p : Point3) : ℝ :=
  Real.sin p.x + Real.sin p.y + Real.sin p.z -
    Real.sin (p.x + p.y + p.z)

def partialX (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun x => g ⟨x, p.y, p.z⟩) p.x

def partialY (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun y => g ⟨p.x, y, p.z⟩) p.y

def partialZ (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun z => g ⟨p.x, p.y, z⟩) p.z

def gradient (g : Point3 → ℝ) (p : Point3) : Point3 :=
  ⟨partialX g p, partialY g p, partialZ g p⟩

def cube : Set Point3 :=
  {p | 0 ≤ p.x ∧ p.x ≤ Real.pi ∧
    0 ≤ p.y ∧ p.y ≤ Real.pi ∧
    0 ≤ p.z ∧ p.z ≤ Real.pi}

def p₀ : Point3 :=
  ⟨0, 0, 0⟩

def p₁ : Point3 :=
  ⟨Real.pi / 2, Real.pi / 2, Real.pi / 2⟩

def p₂ : Point3 :=
  ⟨Real.pi, Real.pi, Real.pi⟩

def stationaryPointsInCube : Set Point3 :=
  {p | p ∈ cube ∧ gradient u p = ⟨0, 0, 0⟩}

def secondVariationAtP₁ (v : Point3) : ℝ :=
  -v.x ^ 2 - v.y ^ 2 - v.z ^ 2 - (v.x + v.y + v.z) ^ 2

def NegativeDefiniteAtP₁ : Prop :=
  ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ → secondVariationAtP₁ v < 0

def IsUniqueGlobalMaximizerOn (p : Point3) : Prop :=
  p ∈ cube ∧ (∀ q ∈ cube, u q ≤ u p) ∧
    (∀ q ∈ cube, u q = u p → q = p)

def maximumPointsOn : Set Point3 :=
  {p | p ∈ cube ∧ ∀ q ∈ cube, u q ≤ u p}

def zeroEdges : Set Point3 :=
  {p | p ∈ cube ∧
    ((p.x = 0 ∧ p.y = 0) ∨ (p.x = Real.pi ∧ p.y = Real.pi) ∨
      (p.y = 0 ∧ p.z = 0) ∨ (p.y = Real.pi ∧ p.z = Real.pi) ∨
      (p.z = 0 ∧ p.x = 0) ∨ (p.z = Real.pi ∧ p.x = Real.pi))}

def minimumPointsOn : Set Point3 :=
  {p | p ∈ cube ∧ ∀ q ∈ cube, u p ≤ u q}

private theorem point3_eq_of_coords {p q : Point3}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p with
  | mk px py pz =>
    cases q with
    | mk qx qy qz =>
      dsimp at hx hy hz
      subst qx
      subst qy
      subst qz
      rfl

private theorem p1_mem_cube : p₁ ∈ cube := by
  change 0 ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ Real.pi ∧
    0 ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ Real.pi ∧
    0 ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ Real.pi
  have h0 : 0 ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hpi : Real.pi / 2 ≤ Real.pi := by nlinarith [Real.pi_pos]
  exact ⟨h0, hpi, h0, hpi, h0, hpi⟩

private theorem cos_inj_on_zero_pi {a b : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi)
    (hb0 : 0 ≤ b) (hbpi : b ≤ Real.pi)
    (h : Real.cos a = Real.cos b) : a = b := by
  exact Real.strictAntiOn_cos.injOn ⟨ha0, hapi⟩ ⟨hb0, hbpi⟩ h

private theorem sin_eq_one_on_zero_pi {x : ℝ}
    (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi)
    (h : Real.sin x = 1) : x = Real.pi / 2 := by
  have hc : Real.cos x = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  apply cos_inj_on_zero_pi hx0 hxpi
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  simpa using hc

private theorem pair_endpoints_of_half_sum_sin_eq_zero
    {a b : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi)
    (hb0 : 0 ≤ b) (hbpi : b ≤ Real.pi)
    (h : Real.sin ((a + b) / 2) = 0) :
    (a = 0 ∧ b = 0) ∨ (a = Real.pi ∧ b = Real.pi) := by
  have havg0 : 0 ≤ (a + b) / 2 :=
    div_nonneg (add_nonneg ha0 hb0) (by norm_num)
  have havgpi : (a + b) / 2 ≤ Real.pi := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    linarith
  by_cases hzero : (a + b) / 2 = 0
  · left
    constructor <;> nlinarith
  by_cases hpi : (a + b) / 2 = Real.pi
  · right
    constructor <;> nlinarith
  have hpos : 0 < (a + b) / 2 :=
    lt_of_le_of_ne havg0 (Ne.symm hzero)
  have hlt : (a + b) / 2 < Real.pi :=
    lt_of_le_of_ne havgpi hpi
  have hspos := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  linarith

private theorem u_factor (p : Point3) :
    u p = 4 * Real.sin ((p.x + p.y) / 2) *
      Real.sin ((p.y + p.z) / 2) * Real.sin ((p.z + p.x) / 2) := by
  have sin_sum (a b : ℝ) :
      Real.sin a + Real.sin b =
        2 * Real.sin ((a + b) / 2) * Real.cos ((a - b) / 2) := by
    rw [show a = (a + b) / 2 + (a - b) / 2 by ring,
      show b = (a + b) / 2 - (a - b) / 2 by ring,
      Real.sin_add, Real.sin_sub]
    ring
  have sin_diff (a b : ℝ) :
      Real.sin a - Real.sin b =
        2 * Real.cos ((a + b) / 2) * Real.sin ((a - b) / 2) := by
    rw [show a = (a + b) / 2 + (a - b) / 2 by ring,
      show b = (a + b) / 2 - (a - b) / 2 by ring,
      Real.sin_add, Real.sin_sub]
    ring
  have cos_diff (a b : ℝ) :
      Real.cos a - Real.cos b =
        2 * Real.sin ((a + b) / 2) * Real.sin ((b - a) / 2) := by
    rw [show a = (a + b) / 2 - (b - a) / 2 by ring,
      show b = (a + b) / 2 + (b - a) / 2 by ring,
      Real.cos_sub, Real.cos_add]
    ring
  calc
    u p = (Real.sin p.x + Real.sin p.y) -
        (Real.sin (p.x + p.y + p.z) - Real.sin p.z) := by
          unfold u
          ring
    _ = 2 * Real.sin ((p.x + p.y) / 2) *
        (Real.cos ((p.x - p.y) / 2) -
          Real.cos ((p.x + p.y) / 2 + p.z)) := by
          rw [sin_sum, sin_diff]
          ring
    _ = 4 * Real.sin ((p.x + p.y) / 2) *
        Real.sin ((p.y + p.z) / 2) * Real.sin ((p.z + p.x) / 2) := by
          rw [cos_diff]
          ring

private theorem u_nonneg_of_mem_cube {p : Point3} (hp : p ∈ cube) : 0 ≤ u p := by
  change 0 ≤ p.x ∧ p.x ≤ Real.pi ∧
    0 ≤ p.y ∧ p.y ≤ Real.pi ∧
    0 ≤ p.z ∧ p.z ≤ Real.pi at hp
  rcases hp with ⟨hx0, hxpi, hy0, hypi, hz0, hzpi⟩
  have hxy : 0 ≤ Real.sin ((p.x + p.y) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hyz : 0 ≤ Real.sin ((p.y + p.z) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hzx : 0 ≤ Real.sin ((p.z + p.x) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [u_factor]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hxy) hyz) hzx

private theorem u_eq_zero_of_edge_condition (p : Point3)
    (h : (p.x = 0 ∧ p.y = 0) ∨
      (p.x = Real.pi ∧ p.y = Real.pi) ∨
      (p.y = 0 ∧ p.z = 0) ∨
      (p.y = Real.pi ∧ p.z = Real.pi) ∨
      (p.z = 0 ∧ p.x = 0) ∨
      (p.z = Real.pi ∧ p.x = Real.pi)) : u p = 0 := by
  rw [u_factor]
  rcases h with h | h | h | h | h | h
  · rw [h.1, h.2]
    norm_num
  · rw [h.1, h.2, show (Real.pi + Real.pi) / 2 = Real.pi by ring]
    simp
  · rw [h.1, h.2]
    norm_num
  · rw [h.1, h.2, show (Real.pi + Real.pi) / 2 = Real.pi by ring]
    simp
  · rw [h.1, h.2]
    norm_num
  · rw [h.1, h.2, show (Real.pi + Real.pi) / 2 = Real.pi by ring]
    simp

private theorem u_p0_value : u p₀ = 0 := by
  simp [u, p₀]

private theorem u_p1_value : u p₁ = 4 := by
  rw [u_factor]
  change 4 * Real.sin ((Real.pi / 2 + Real.pi / 2) / 2) *
    Real.sin ((Real.pi / 2 + Real.pi / 2) / 2) *
    Real.sin ((Real.pi / 2 + Real.pi / 2) / 2) = 4
  rw [show (Real.pi / 2 + Real.pi / 2) / 2 = Real.pi / 2 by ring]
  simp

private theorem u_p2_value : u p₂ = 0 := by
  rw [u_factor]
  change 4 * Real.sin ((Real.pi + Real.pi) / 2) *
    Real.sin ((Real.pi + Real.pi) / 2) *
    Real.sin ((Real.pi + Real.pi) / 2) = 0
  rw [show (Real.pi + Real.pi) / 2 = Real.pi by ring]
  simp

theorem gap1 :
    ∀ p : Point3,
      gradient u p =
        ⟨Real.cos p.x - Real.cos (p.x + p.y + p.z),
          Real.cos p.y - Real.cos (p.x + p.y + p.z),
          Real.cos p.z - Real.cos (p.x + p.y + p.z)⟩ := by
  intro p
  refine point3_eq_of_coords ?_ ?_ ?_
  · change deriv (fun x : ℝ => u ⟨x, p.y, p.z⟩) p.x =
      Real.cos p.x - Real.cos (p.x + p.y + p.z)
    simpa [u] using
      (((((Real.hasDerivAt_sin p.x).add_const (Real.sin p.y)).add_const
          (Real.sin p.z)).sub
        ((((hasDerivAt_id p.x).add_const p.y).add_const p.z).sin)).deriv)
  · change deriv (fun y : ℝ => u ⟨p.x, y, p.z⟩) p.y =
      Real.cos p.y - Real.cos (p.x + p.y + p.z)
    simpa [u] using
      (((((Real.hasDerivAt_sin p.y).const_add (Real.sin p.x)).add_const
          (Real.sin p.z)).sub
        ((((hasDerivAt_id p.y).const_add p.x).add_const p.z).sin)).deriv)
  · change deriv (fun z : ℝ => u ⟨p.x, p.y, z⟩) p.z =
      Real.cos p.z - Real.cos (p.x + p.y + p.z)
    simpa [u] using
      ((((Real.hasDerivAt_sin p.z).const_add
          (Real.sin p.x + Real.sin p.y)).sub
        (((hasDerivAt_id p.z).const_add (p.x + p.y)).sin)).deriv)

theorem gap2 :
    p₀ = ⟨0, 0, 0⟩ := by
  rfl

theorem gap3 :
    p₁ = ⟨Real.pi / 2, Real.pi / 2, Real.pi / 2⟩ := by
  rfl

theorem gap4 :
    p₂ = ⟨Real.pi, Real.pi, Real.pi⟩ := by
  rfl

theorem gap5 :
    stationaryPointsInCube = {p₀, p₁, p₂} := by
  ext p
  constructor
  · intro hp
    change p ∈ cube ∧ gradient u p = ⟨0, 0, 0⟩ at hp
    rcases hp.1 with ⟨hx0, hxpi, hy0, hypi, hz0, hzpi⟩
    rw [gap1] at hp
    have hx := congrArg Point3.x hp.2
    have hy := congrArg Point3.y hp.2
    have hz := congrArg Point3.z hp.2
    dsimp at hx hy hz
    have hcx : Real.cos p.x = Real.cos (p.x + p.y + p.z) := by linarith
    have hcy : Real.cos p.y = Real.cos (p.x + p.y + p.z) := by linarith
    have hcz : Real.cos p.z = Real.cos (p.x + p.y + p.z) := by linarith
    have hxy : p.x = p.y :=
      cos_inj_on_zero_pi hx0 hxpi hy0 hypi (hcx.trans hcy.symm)
    have hxz : p.x = p.z :=
      cos_inj_on_zero_pi hx0 hxpi hz0 hzpi (hcx.trans hcz.symm)
    have ht : Real.cos p.x = Real.cos (3 * p.x) := by
      calc
        Real.cos p.x = Real.cos (p.x + p.y + p.z) := hcx
        _ = Real.cos (3 * p.x) := by rw [← hxy, ← hxz]; congr 1 <;> ring
    rw [Real.cos_three_mul] at ht
    have hfac :
        Real.cos p.x * (Real.cos p.x - 1) * (Real.cos p.x + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with hc01 | hcm1
    · rcases mul_eq_zero.mp hc01 with hc0 | hc1
      · have hxt : p.x = Real.pi / 2 := by
          apply cos_inj_on_zero_pi hx0 hxpi
            (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          simpa using hc0
        have hp1 : p = p₁ := by
          refine point3_eq_of_coords ?_ ?_ ?_
          · simpa [p₁] using hxt
          · simpa [p₁] using hxy.symm.trans hxt
          · simpa [p₁] using hxz.symm.trans hxt
        simp [hp1]
      · have hc : Real.cos p.x = 1 := by linarith
        have hxt : p.x = 0 := by
          apply cos_inj_on_zero_pi hx0 hxpi (le_refl 0) Real.pi_pos.le
          simpa using hc
        have hp0 : p = p₀ := by
          refine point3_eq_of_coords ?_ ?_ ?_
          · simpa [p₀] using hxt
          · simpa [p₀] using hxy.symm.trans hxt
          · simpa [p₀] using hxz.symm.trans hxt
        simp [hp0]
    · have hc : Real.cos p.x = -1 := by linarith
      have hxt : p.x = Real.pi := by
        apply cos_inj_on_zero_pi hx0 hxpi Real.pi_pos.le (le_refl Real.pi)
        simpa using hc
      have hp2 : p = p₂ := by
        refine point3_eq_of_coords ?_ ?_ ?_
        · simpa [p₂] using hxt
        · simpa [p₂] using hxy.symm.trans hxt
        · simpa [p₂] using hxz.symm.trans hxt
      simp [hp2]
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · constructor
      · simp [cube, p₀, Real.pi_pos.le]
      · rw [gap1]
        simp [p₀]
    · constructor
      · exact p1_mem_cube
      · rw [gap1]
        simp only [p₁]
        rw [show Real.pi / 2 + Real.pi / 2 + Real.pi / 2 =
          Real.pi + Real.pi / 2 by ring]
        simp [Real.cos_add]
    · constructor
      · simp [cube, p₂, Real.pi_pos.le]
      · rw [gap1]
        simp only [p₂]
        rw [show Real.pi + Real.pi + Real.pi = Real.pi + (Real.pi + Real.pi) by ring]
        simp [Real.cos_add]

theorem gap6 :
    ∀ v : Point3,
      secondVariationAtP₁ v =
        -v.x ^ 2 - v.y ^ 2 - v.z ^ 2 -
          (v.x + v.y + v.z) ^ 2 := by
  intro v
  rfl

theorem gap7 :
    ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ →
      -v.x ^ 2 - v.y ^ 2 - v.z ^ 2 -
        (v.x + v.y + v.z) ^ 2 < 0 := by
  intro v hv
  rcases v with ⟨x, y, z⟩
  dsimp only [Point3.x, Point3.y, Point3.z] at hv ⊢
  have hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · by_cases hz : z = 0
        · exact False.elim (hv (by simp [hx, hy, hz]))
        · exact Or.inr (Or.inr hz)
      · exact Or.inr (Or.inl hy)
    · exact Or.inl hx
  rcases hne with hx | hy | hz
  · nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z,
      sq_nonneg (x + y + z), mul_self_pos.mpr hx]
  · nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z,
      sq_nonneg (x + y + z), mul_self_pos.mpr hy]
  · nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z,
      sq_nonneg (x + y + z), mul_self_pos.mpr hz]

theorem gap8 :
    NegativeDefiniteAtP₁ := by
  intro v hv
  rw [gap6 v]
  exact gap7 v hv

theorem gap9 :
    IsUniqueGlobalMaximizerOn p₁ := by
  refine ⟨p1_mem_cube, ?_, ?_⟩
  · intro q hq
    have hx := Real.sin_le_one q.x
    have hy := Real.sin_le_one q.y
    have hz := Real.sin_le_one q.z
    have hs := Real.neg_one_le_sin (q.x + q.y + q.z)
    rw [u_p1_value]
    unfold u
    linarith
  · intro q hq heq
    rcases hq with ⟨hx0, hxpi, hy0, hypi, hz0, hzpi⟩
    rw [u_p1_value] at heq
    change Real.sin q.x + Real.sin q.y + Real.sin q.z -
      Real.sin (q.x + q.y + q.z) = 4 at heq
    have hxle := Real.sin_le_one q.x
    have hyle := Real.sin_le_one q.y
    have hzle := Real.sin_le_one q.z
    have hslo := Real.neg_one_le_sin (q.x + q.y + q.z)
    have hsx : Real.sin q.x = 1 := by linarith
    have hsy : Real.sin q.y = 1 := by linarith
    have hsz : Real.sin q.z = 1 := by linarith
    have hqx := sin_eq_one_on_zero_pi hx0 hxpi hsx
    have hqy := sin_eq_one_on_zero_pi hy0 hypi hsy
    have hqz := sin_eq_one_on_zero_pi hz0 hzpi hsz
    refine point3_eq_of_coords ?_ ?_ ?_
    · simpa [p₁] using hqx
    · simpa [p₁] using hqy
    · simpa [p₁] using hqz

theorem gap10 :
    u p₁ = 4 := by
  exact u_p1_value

theorem gap11 :
    p₀ ∈ {p : Point3 | p ∈ cube ∧ u p = 0} := by
  constructor
  · simp [cube, p₀, Real.pi_pos.le]
  · exact u_p0_value

theorem gap12 :
    p₂ ∈ {p : Point3 | p ∈ cube ∧ u p = 0} := by
  constructor
  · simp [cube, p₂, Real.pi_pos.le]
  · exact u_p2_value

theorem gap13 :
    minimumPointsOn = zeroEdges := by
  ext p
  change (p ∈ cube ∧ ∀ q ∈ cube, u p ≤ u q) ↔
    (p ∈ cube ∧
      ((p.x = 0 ∧ p.y = 0) ∨
       (p.x = Real.pi ∧ p.y = Real.pi) ∨
       (p.y = 0 ∧ p.z = 0) ∨
       (p.y = Real.pi ∧ p.z = Real.pi) ∨
       (p.z = 0 ∧ p.x = 0) ∨
       (p.z = Real.pi ∧ p.x = Real.pi)))
  constructor
  · intro hp
    have hup0 := hp.2 p₀ gap11.1
    have hnon := u_nonneg_of_mem_cube hp.1
    have hu : u p = 0 := by
      rw [u_p0_value] at hup0
      linarith
    rw [u_factor] at hu
    rcases hp.1 with ⟨hx0, hxpi, hy0, hypi, hz0, hzpi⟩
    have hedge :
        (p.x = 0 ∧ p.y = 0) ∨
        (p.x = Real.pi ∧ p.y = Real.pi) ∨
        (p.y = 0 ∧ p.z = 0) ∨
        (p.y = Real.pi ∧ p.z = Real.pi) ∨
        (p.z = 0 ∧ p.x = 0) ∨
        (p.z = Real.pi ∧ p.x = Real.pi) := by
      rcases mul_eq_zero.mp hu with hleft | hzx
      · rcases mul_eq_zero.mp hleft with hleft | hyz
        · have hxy : Real.sin ((p.x + p.y) / 2) = 0 :=
            (mul_eq_zero.mp hleft).resolve_left (by norm_num)
          exact (pair_endpoints_of_half_sum_sin_eq_zero hx0 hxpi hy0 hypi hxy).imp
            id (fun h => Or.inl h)
        · rcases pair_endpoints_of_half_sum_sin_eq_zero hy0 hypi hz0 hzpi hyz with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases pair_endpoints_of_half_sum_sin_eq_zero hz0 hzpi hx0 hxpi hzx with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    exact ⟨⟨hx0, hxpi, hy0, hypi, hz0, hzpi⟩, hedge⟩
  · intro hp
    refine ⟨hp.1, ?_⟩
    have hup : u p = 0 := u_eq_zero_of_edge_condition p hp.2
    intro q hq
    rw [hup]
    exact u_nonneg_of_mem_cube hq

theorem gap14 :
    u p₀ = u p₂ := by
  rw [u_p0_value, u_p2_value]

theorem gap15 :
    u p₂ = 0 := by
  exact u_p2_value

theorem gap16 :
    maximumPointsOn = {p₁} := by
  ext p
  constructor
  · intro hp
    change p ∈ cube ∧ ∀ q ∈ cube, u q ≤ u p at hp
    have hp1cube := gap9.1
    have hle1 := gap9.2.1 p hp.1
    have hlep := hp.2 p₁ hp1cube
    have heq : u p = u p₁ := le_antisymm hle1 hlep
    have hpp1 := gap9.2.2 p hp.1 heq
    simpa [hpp1]
  · intro hp
    have hpp1 : p = p₁ := by simpa using hp
    subst p
    exact ⟨gap9.1, gap9.2.1⟩

end

end ProofGap.Exercise3647
