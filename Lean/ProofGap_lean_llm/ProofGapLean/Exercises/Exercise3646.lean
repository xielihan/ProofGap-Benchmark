import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3646

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def u (a b : ℝ) (p : Point3) : ℝ :=
  a ^ 2 / p.x + p.x ^ 2 / p.y + p.y ^ 2 / p.z + p.z ^ 2 / b

def partialX (a b : ℝ) (p : Point3) : ℝ :=
  deriv (fun x => u a b ⟨x, p.y, p.z⟩) p.x

def partialY (a b : ℝ) (p : Point3) : ℝ :=
  deriv (fun y => u a b ⟨p.x, y, p.z⟩) p.y

def partialZ (a b : ℝ) (p : Point3) : ℝ :=
  deriv (fun z => u a b ⟨p.x, p.y, z⟩) p.z

def gradient (a b : ℝ) (p : Point3) : Point3 :=
  ⟨partialX a b p, partialY a b p, partialZ a b p⟩

def positiveOctant : Set Point3 :=
  {p | 0 < p.x ∧ 0 < p.y ∧ 0 < p.z}

def root15 (x : ℝ) : ℝ :=
  Real.rpow x (1 / 15 : ℝ)

def root5 (x : ℝ) : ℝ :=
  Real.rpow x (1 / 5 : ℝ)

def p₀ (a b : ℝ) : Point3 :=
  ⟨(1 / 2 : ℝ) * root15 (16 * a ^ 14 * b),
    (1 / 4 : ℝ) * root5 (16 * a ^ 4 * b),
    (1 / 2 : ℝ) * root15 (a ^ 8 * b ^ 7 / 4)⟩

def Stationary (a b : ℝ) (p : Point3) : Prop :=
  gradient a b p = ⟨0, 0, 0⟩

def secondVariation (a b : ℝ) (p v : Point3) : ℝ :=
  2 * a ^ 2 / p.x ^ 3 * v.x ^ 2 +
    2 / p.y * (v.x - p.x / p.y * v.y) ^ 2 +
    2 / p.z * (v.y - p.y / p.z * v.z) ^ 2 +
    2 / b * v.z ^ 2

def PositiveDefiniteAt
    (a b : ℝ) (p : Point3) : Prop :=
  ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ → 0 < secondVariation a b p v

def IsUniqueGlobalMinimizerOn
    (a b : ℝ) (p : Point3) : Prop :=
  p ∈ positiveOctant ∧
    (∀ q ∈ positiveOctant, u a b p ≤ u a b q) ∧
    (∀ q ∈ positiveOctant, u a b q = u a b p → q = p)

def minimumPointsOn (a b : ℝ) : Set Point3 :=
  {p | p ∈ positiveOctant ∧
    ∀ q ∈ positiveOctant, u a b p ≤ u a b q}

def minimumValue (a b : ℝ) : ℝ :=
  (15 * a / 4) * root15 (a / (16 * b))

private theorem point3_eq {p q : Point3}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  simp_all

private theorem odd5 : Odd 5 := by
  use 2
  norm_num

private theorem odd15 : Odd 15 := by
  use 7
  norm_num

private theorem root15_pow (x : ℝ) (hx : 0 < x) :
    (root15 x) ^ 15 = x := by
  change (Real.rpow x (1 / 15 : ℝ)) ^ (15 : ℕ) = x
  calc
    (Real.rpow x (1 / 15 : ℝ)) ^ (15 : ℕ) =
        Real.rpow (Real.rpow x (1 / 15 : ℝ)) (15 : ℝ) := by
      exact (Real.rpow_natCast (Real.rpow x (1 / 15 : ℝ)) 15).symm
    _ = Real.rpow x ((1 / 15 : ℝ) * (15 : ℝ)) := by
      exact (Real.rpow_mul (le_of_lt hx) (1 / 15 : ℝ) (15 : ℝ)).symm
    _ = x := by norm_num

private theorem root5_pow (x : ℝ) (hx : 0 < x) :
    (root5 x) ^ 5 = x := by
  change (Real.rpow x (1 / 5 : ℝ)) ^ (5 : ℕ) = x
  calc
    (Real.rpow x (1 / 5 : ℝ)) ^ (5 : ℕ) =
        Real.rpow (Real.rpow x (1 / 5 : ℝ)) (5 : ℝ) := by
      exact (Real.rpow_natCast (Real.rpow x (1 / 5 : ℝ)) 5).symm
    _ = Real.rpow x ((1 / 5 : ℝ) * (5 : ℝ)) := by
      exact (Real.rpow_mul (le_of_lt hx) (1 / 5 : ℝ) (5 : ℝ)).symm
    _ = x := by norm_num

private theorem p₀_mem_positiveOctant (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    p₀ a b ∈ positiveOctant := by
  dsimp [p₀, positiveOctant, root15, root5]
  constructor
  · positivity
  constructor <;> positivity

private theorem p₀_power_specs (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (p₀ a b).x ^ 15 = a ^ 14 * b / 2048 ∧
    (p₀ a b).y ^ 5 = a ^ 4 * b / 64 ∧
    (p₀ a b).z ^ 15 = a ^ 8 * b ^ 7 / 131072 := by
  have h16 : 0 < 16 * a ^ 14 * b := by positivity
  have h5 : 0 < 16 * a ^ 4 * b := by positivity
  have hz : 0 < a ^ 8 * b ^ 7 / 4 := by positivity
  dsimp [p₀]
  constructor
  · rw [mul_pow, root15_pow _ h16]
    norm_num
    ring
  constructor
  · rw [mul_pow, root5_pow _ h5]
    norm_num
    ring
  · rw [mul_pow, root15_pow _ hz]
    norm_num
    ring

private theorem p₀_stationary_relations (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 * (p₀ a b).y = 2 * (p₀ a b).x ^ 3 ∧
    (p₀ a b).x ^ 2 * (p₀ a b).z = 2 * (p₀ a b).y ^ 3 ∧
    (p₀ a b).y ^ 2 * b = 2 * (p₀ a b).z ^ 3 := by
  rcases p₀_power_specs a b ha hb with ⟨hx, hy, hz⟩
  constructor
  · apply (Odd.strictMono_pow odd5).injective
    calc
      (a ^ 2 * (p₀ a b).y) ^ 5 = a ^ 10 * (p₀ a b).y ^ 5 := by ring
      _ = a ^ 14 * b / 64 := by rw [hy]; ring
      _ = 32 * (p₀ a b).x ^ 15 := by rw [hx]; ring
      _ = (2 * (p₀ a b).x ^ 3) ^ 5 := by ring
  constructor
  · apply (Odd.strictMono_pow odd15).injective
    calc
      ((p₀ a b).x ^ 2 * (p₀ a b).z) ^ 15 =
          ((p₀ a b).x ^ 15) ^ 2 * (p₀ a b).z ^ 15 := by ring
      _ = (a ^ 14 * b / 2048) ^ 2 * (a ^ 8 * b ^ 7 / 131072) := by rw [hx, hz]
      _ = 2 ^ 15 * ((p₀ a b).y ^ 5) ^ 9 := by rw [hy]; ring
      _ = (2 * (p₀ a b).y ^ 3) ^ 15 := by ring
  · apply (Odd.strictMono_pow odd5).injective
    calc
      ((p₀ a b).y ^ 2 * b) ^ 5 = ((p₀ a b).y ^ 5) ^ 2 * b ^ 5 := by ring
      _ = (a ^ 4 * b / 64) ^ 2 * b ^ 5 := by rw [hy]
      _ = 32 * (p₀ a b).z ^ 15 := by rw [hz]; ring
      _ = (2 * (p₀ a b).z ^ 3) ^ 5 := by ring

private theorem u_tangent_remainder
    (a b : ℝ) (p q : Point3)
    (hpx : p.x ≠ 0) (hpy : p.y ≠ 0) (hpz : p.z ≠ 0)
    (hqx : q.x ≠ 0) (hqy : q.y ≠ 0) (hqz : q.z ≠ 0)
    (hb : b ≠ 0) :
    u a b q - u a b p =
      (2 * p.x / p.y - a ^ 2 / p.x ^ 2) * (q.x - p.x) +
      (2 * p.y / p.z - p.x ^ 2 / p.y ^ 2) * (q.y - p.y) +
      (2 * p.z / b - p.y ^ 2 / p.z ^ 2) * (q.z - p.z) +
      a ^ 2 * (q.x - p.x) ^ 2 / (q.x * p.x ^ 2) +
      (p.y * q.x - p.x * q.y) ^ 2 / (q.y * p.y ^ 2) +
      (p.z * q.y - p.y * q.z) ^ 2 / (q.z * p.z ^ 2) +
      (q.z - p.z) ^ 2 / b := by
  dsimp [u]
  field_simp [hpx, hpy, hpz, hqx, hqy, hqz, hb]
  ring

private theorem p₀_gradient_coefficients
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * (p₀ a b).x / (p₀ a b).y - a ^ 2 / (p₀ a b).x ^ 2 = 0 ∧
    2 * (p₀ a b).y / (p₀ a b).z - (p₀ a b).x ^ 2 / (p₀ a b).y ^ 2 = 0 ∧
    2 * (p₀ a b).z / b - (p₀ a b).y ^ 2 / (p₀ a b).z ^ 2 = 0 := by
  rcases p₀_mem_positiveOctant a b ha hb with ⟨hx, hy, hz⟩
  rcases p₀_stationary_relations a b ha hb with ⟨h1, h2, h3⟩
  constructor
  · field_simp [ne_of_gt hx, ne_of_gt hy]
    nlinarith [h1]
  constructor
  · field_simp [ne_of_gt hy, ne_of_gt hz]
    nlinarith [h2]
  · field_simp [ne_of_gt hz, ne_of_gt hb]
    nlinarith [h3]

private theorem p₀_remainder_identity
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (q : Point3) (hq : q ∈ positiveOctant) :
    u a b q - u a b (p₀ a b) =
      a ^ 2 * (q.x - (p₀ a b).x) ^ 2 /
        (q.x * (p₀ a b).x ^ 2) +
      ((p₀ a b).y * q.x - (p₀ a b).x * q.y) ^ 2 /
        (q.y * (p₀ a b).y ^ 2) +
      ((p₀ a b).z * q.y - (p₀ a b).y * q.z) ^ 2 /
        (q.z * (p₀ a b).z ^ 2) +
      (q.z - (p₀ a b).z) ^ 2 / b := by
  rcases p₀_mem_positiveOctant a b ha hb with ⟨hpx, hpy, hpz⟩
  rcases hq with ⟨hqx, hqy, hqz⟩
  rcases p₀_gradient_coefficients a b ha hb with ⟨g1, g2, g3⟩
  have h := u_tangent_remainder a b (p₀ a b) q
    (ne_of_gt hpx) (ne_of_gt hpy) (ne_of_gt hpz)
    (ne_of_gt hqx) (ne_of_gt hqy) (ne_of_gt hqz) (ne_of_gt hb)
  rw [g1, g2, g3] at h
  simpa using h

theorem gap1 (a b : ℝ) :
    ∀ p : Point3, p ∈ positiveOctant → 0 < b →
      gradient a b p =
        ⟨2 * p.x / p.y - a ^ 2 / p.x ^ 2,
          2 * p.y / p.z - p.x ^ 2 / p.y ^ 2,
          2 * p.z / b - p.y ^ 2 / p.z ^ 2⟩ := by
  intro p hp hb
  rcases hp with ⟨hx, hy, hz⟩
  have hx0 : p.x ≠ 0 := ne_of_gt hx
  have hy0 : p.y ≠ 0 := ne_of_gt hy
  have hz0 : p.z ≠ 0 := ne_of_gt hz
  have hb0 : b ≠ 0 := ne_of_gt hb
  refine point3_eq ?_ ?_ ?_
  · change deriv (fun x : ℝ => a ^ 2 / x + x ^ 2 / p.y + p.y ^ 2 / p.z + p.z ^ 2 / b) p.x = _
    have hA := (hasDerivAt_const (x := p.x) (c := a ^ 2)).div
      (hasDerivAt_id p.x) hx0
    have hB : HasDerivAt (fun x : ℝ => x ^ 2 / p.y)
        (2 * p.x / p.y) p.x := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id p.x).mul (hasDerivAt_id p.x)).div_const p.y
    have hC := hasDerivAt_const (x := p.x) (c := p.y ^ 2 / p.z)
    have hD := hasDerivAt_const (x := p.x) (c := p.z ^ 2 / b)
    have h := ((hA.add hB).add hC).add hD
    have hd := h.deriv
    change deriv (fun x : ℝ => a ^ 2 / x + x ^ 2 / p.y + p.y ^ 2 / p.z + p.z ^ 2 / b) p.x = _ at hd
    rw [hd]
    simp only [id_eq]
    field_simp [hx0, hy0, hz0, hb0] <;> ring
  · change deriv (fun y : ℝ => a ^ 2 / p.x + p.x ^ 2 / y + y ^ 2 / p.z + p.z ^ 2 / b) p.y = _
    have hA := hasDerivAt_const (x := p.y) (c := a ^ 2 / p.x)
    have hB := (hasDerivAt_const (x := p.y) (c := p.x ^ 2)).div
      (hasDerivAt_id p.y) hy0
    have hC : HasDerivAt (fun y : ℝ => y ^ 2 / p.z)
        (2 * p.y / p.z) p.y := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id p.y).mul (hasDerivAt_id p.y)).div_const p.z
    have hD := hasDerivAt_const (x := p.y) (c := p.z ^ 2 / b)
    have h := ((hA.add hB).add hC).add hD
    have hd := h.deriv
    change deriv (fun y : ℝ => a ^ 2 / p.x + p.x ^ 2 / y + y ^ 2 / p.z + p.z ^ 2 / b) p.y = _ at hd
    rw [hd]
    simp only [id_eq]
    field_simp [hx0, hy0, hz0, hb0] <;> ring
  · change deriv (fun z : ℝ => a ^ 2 / p.x + p.x ^ 2 / p.y + p.y ^ 2 / z + z ^ 2 / b) p.z = _
    have hA := hasDerivAt_const (x := p.z) (c := a ^ 2 / p.x)
    have hB := hasDerivAt_const (x := p.z) (c := p.x ^ 2 / p.y)
    have hC := (hasDerivAt_const (x := p.z) (c := p.y ^ 2)).div
      (hasDerivAt_id p.z) hz0
    have hD : HasDerivAt (fun z : ℝ => z ^ 2 / b)
        (2 * p.z / b) p.z := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id p.z).mul (hasDerivAt_id p.z)).div_const b
    have h := ((hA.add hB).add hC).add hD
    have hd := h.deriv
    change deriv (fun z : ℝ => a ^ 2 / p.x + p.x ^ 2 / p.y + p.y ^ 2 / z + z ^ 2 / b) p.z = _ at hd
    rw [hd]
    simp only [id_eq]
    field_simp [hx0, hy0, hz0, hb0] <;> ring

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ p : Point3, p ∈ positiveOctant →
      (Stationary a b p ↔ p = p₀ a b) := by
  intro p hp
  have hp0 := p₀_mem_positiveOctant a b ha hb
  rcases p₀_stationary_relations a b ha hb with ⟨hs01, hs02, hs03⟩
  constructor
  · intro hs
    rcases hp with ⟨hx, hy, hz⟩
    have hx0 : p.x ≠ 0 := ne_of_gt hx
    have hy0 : p.y ≠ 0 := ne_of_gt hy
    have hz0 : p.z ≠ 0 := ne_of_gt hz
    have hb0 : b ≠ 0 := ne_of_gt hb
    have hg := gap1 a b p ⟨hx, hy, hz⟩ hb
    rw [Stationary, hg] at hs
    have hgx := congrArg Point3.x hs
    have hgy := congrArg Point3.y hs
    have hgz := congrArg Point3.z hs
    dsimp at hgx hgy hgz
    have h1 : a ^ 2 * p.y = 2 * p.x ^ 3 := by
      field_simp [hx0, hy0] at hgx
      nlinarith only [hgx]
    have h2 : p.x ^ 2 * p.z = 2 * p.y ^ 3 := by
      field_simp [hy0, hz0] at hgy
      nlinarith only [hgy]
    have h3 : p.y ^ 2 * b = 2 * p.z ^ 3 := by
      field_simp [hz0, hb0] at hgz
      nlinarith only [hgz]
    have hcommon : p.x ^ 6 * p.y ^ 9 * p.z ^ 3 ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero 6 hx0) (pow_ne_zero 9 hy0))
        (pow_ne_zero 3 hz0)
    have hcombined :
        (p.x ^ 6 * p.y ^ 9 * p.z ^ 3) * (a ^ 14 * b) =
          (p.x ^ 6 * p.y ^ 9 * p.z ^ 3) * (2048 * p.x ^ 15) := by
      calc
        (p.x ^ 6 * p.y ^ 9 * p.z ^ 3) * (a ^ 14 * b) =
            (a ^ 2 * p.y) ^ 7 * (p.x ^ 2 * p.z) ^ 3 * (p.y ^ 2 * b) := by ring
        _ = (2 * p.x ^ 3) ^ 7 * (2 * p.y ^ 3) ^ 3 * (2 * p.z ^ 3) := by
          rw [h1, h2, h3]
        _ = (p.x ^ 6 * p.y ^ 9 * p.z ^ 3) * (2048 * p.x ^ 15) := by ring
    have hbase : a ^ 14 * b = 2048 * p.x ^ 15 := by
      apply mul_left_cancel₀ hcommon
      exact hcombined
    have hx15 : p.x ^ 15 = a ^ 14 * b / 2048 := by
      apply (eq_div_iff (by norm_num : (2048 : ℝ) ≠ 0)).2
      calc
        p.x ^ 15 * 2048 = 2048 * p.x ^ 15 := by ring
        _ = a ^ 14 * b := hbase.symm
    rcases p₀_power_specs a b ha hb with ⟨hx15₀, hy5₀, hz15₀⟩
    have hpow : p.x ^ 15 = (p₀ a b).x ^ 15 := hx15.trans hx15₀.symm
    have hxeq : p.x = (p₀ a b).x :=
      (Odd.strictMono_pow odd15).injective hpow
    have hyeq : p.y = (p₀ a b).y := by
      rw [hxeq] at h1
      apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt ha))
      exact h1.trans hs01.symm
    have hzeq : p.z = (p₀ a b).z := by
      rw [hxeq, hyeq] at h2
      apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hp0.1))
      exact h2.trans hs02.symm
    exact point3_eq hxeq hyeq hzeq
  · intro hpEq
    subst p
    have hg := gap1 a b (p₀ a b) hp0 hb
    rw [Stationary, hg]
    rcases p₀_gradient_coefficients a b ha hb with ⟨g1, g2, g3⟩
    refine point3_eq ?_ ?_ ?_
    · exact g1
    · exact g2
    · exact g3

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    p₀ a b ∈ positiveOctant ∧ Stationary a b (p₀ a b) := by
  have hp := p₀_mem_positiveOctant a b ha hb
  refine ⟨hp, ?_⟩
  exact (gap2 a b ha hb (p₀ a b) hp).2 rfl

theorem gap4 (a b : ℝ) :
    ∀ p v : Point3,
      secondVariation a b p v =
        2 * a ^ 2 / p.x ^ 3 * v.x ^ 2 +
          2 / p.y * (v.x - p.x / p.y * v.y) ^ 2 +
          2 / p.z * (v.y - p.y / p.z * v.z) ^ 2 +
          2 / b * v.z ^ 2 := by
  intro p v
  rfl

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ p : Point3, p ∈ positiveOctant →
      ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ →
        0 < secondVariation a b p v := by
  intro p hp v hv
  rcases hp with ⟨hx, hy, hz⟩
  have h1 : 0 ≤ 2 * a ^ 2 / p.x ^ 3 * v.x ^ 2 := by positivity
  have h2 : 0 ≤ 2 / p.y * (v.x - p.x / p.y * v.y) ^ 2 := by positivity
  have h3 : 0 ≤ 2 / p.z * (v.y - p.y / p.z * v.z) ^ 2 := by positivity
  have h4 : 0 ≤ 2 / b * v.z ^ 2 := by positivity
  by_contra hn
  have hle : secondVariation a b p v ≤ 0 := le_of_not_gt hn
  rw [secondVariation] at hle
  have hzterm : 2 / b * v.z ^ 2 = 0 := by nlinarith
  have hzcoef : 2 / b ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt hb)
  have hzsq : v.z ^ 2 = 0 :=
    (mul_eq_zero.mp hzterm).resolve_left hzcoef
  have hvz : v.z = 0 := by
    nlinarith [hzsq, sq_nonneg v.z]
  have hyterm : 2 / p.z * (v.y - p.y / p.z * v.z) ^ 2 = 0 := by nlinarith
  have hycoef : 2 / p.z ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt hz)
  have hysq : (v.y - p.y / p.z * v.z) ^ 2 = 0 :=
    (mul_eq_zero.mp hyterm).resolve_left hycoef
  have hyrel : v.y - p.y / p.z * v.z = 0 := by
    nlinarith [hysq, sq_nonneg (v.y - p.y / p.z * v.z)]
  have hvy : v.y = 0 := by
    rw [hvz] at hyrel
    simpa using hyrel
  have hxterm : 2 / p.y * (v.x - p.x / p.y * v.y) ^ 2 = 0 := by nlinarith
  have hxcoef : 2 / p.y ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt hy)
  have hxsq : (v.x - p.x / p.y * v.y) ^ 2 = 0 :=
    (mul_eq_zero.mp hxterm).resolve_left hxcoef
  have hxrel : v.x - p.x / p.y * v.y = 0 := by
    nlinarith [hxsq, sq_nonneg (v.x - p.x / p.y * v.y)]
  have hvx : v.x = 0 := by
    rw [hvy] at hxrel
    simpa using hxrel
  apply hv
  exact point3_eq hvx hvy hvz

theorem gap6 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    PositiveDefiniteAt a b (p₀ a b) := by
  have hp := (gap3 a b ha hb).1
  intro v hv
  exact gap5 a b ha hb (p₀ a b) hp v hv

theorem gap7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IsUniqueGlobalMinimizerOn a b (p₀ a b) := by
  set_option maxHeartbeats 2000000 in
    have hp := p₀_mem_positiveOctant a b ha hb
    refine ⟨hp, ?_, ?_⟩
    · intro q hq
      rcases hp with ⟨hpx, hpy, hpz⟩
      rcases hq with ⟨hqx, hqy, hqz⟩
      have hid := p₀_remainder_identity a b ha hb q ⟨hqx, hqy, hqz⟩
      have hd1 : 0 ≤ a ^ 2 * (q.x - (p₀ a b).x) ^ 2 /
          (q.x * (p₀ a b).x ^ 2) := by positivity
      have hd2 : 0 ≤ ((p₀ a b).y * q.x - (p₀ a b).x * q.y) ^ 2 /
          (q.y * (p₀ a b).y ^ 2) := by positivity
      have hd3 : 0 ≤ ((p₀ a b).z * q.y - (p₀ a b).y * q.z) ^ 2 /
          (q.z * (p₀ a b).z ^ 2) := by positivity
      have hd4 : 0 ≤ (q.z - (p₀ a b).z) ^ 2 / b := by positivity
      linarith
    · intro q hq heq
      rcases hp with ⟨hpx, hpy, hpz⟩
      rcases hq with ⟨hqx, hqy, hqz⟩
      have hid := p₀_remainder_identity a b ha hb q ⟨hqx, hqy, hqz⟩
      have hd1 : 0 ≤ a ^ 2 * (q.x - (p₀ a b).x) ^ 2 /
          (q.x * (p₀ a b).x ^ 2) := by positivity
      have hd2 : 0 ≤ ((p₀ a b).y * q.x - (p₀ a b).x * q.y) ^ 2 /
          (q.y * (p₀ a b).y ^ 2) := by positivity
      have hd3 : 0 ≤ ((p₀ a b).z * q.y - (p₀ a b).y * q.z) ^ 2 /
          (q.z * (p₀ a b).z ^ 2) := by positivity
      have hd4 : 0 ≤ (q.z - (p₀ a b).z) ^ 2 / b := by positivity
      rw [heq] at hid
      have hd1z : a ^ 2 * (q.x - (p₀ a b).x) ^ 2 /
          (q.x * (p₀ a b).x ^ 2) = 0 := by linarith
      have hden1 : q.x * (p₀ a b).x ^ 2 ≠ 0 :=
        mul_ne_zero (ne_of_gt hqx) (pow_ne_zero 2 (ne_of_gt hpx))
      have hnum1 : a ^ 2 * (q.x - (p₀ a b).x) ^ 2 = 0 :=
        (div_eq_zero_iff.mp hd1z).resolve_right hden1
      have hsq1 : (q.x - (p₀ a b).x) ^ 2 = 0 :=
        (mul_eq_zero.mp hnum1).resolve_left (pow_ne_zero 2 (ne_of_gt ha))
      have hqxeq : q.x = (p₀ a b).x := by
        nlinarith [hsq1]
      have hd2z : ((p₀ a b).y * q.x - (p₀ a b).x * q.y) ^ 2 /
          (q.y * (p₀ a b).y ^ 2) = 0 := by linarith
      have hden2 : q.y * (p₀ a b).y ^ 2 ≠ 0 :=
        mul_ne_zero (ne_of_gt hqy) (pow_ne_zero 2 (ne_of_gt hpy))
      have harg2 : (p₀ a b).y * q.x - (p₀ a b).x * q.y = 0 := by
        have hs2 : ((p₀ a b).y * q.x - (p₀ a b).x * q.y) ^ 2 = 0 :=
          (div_eq_zero_iff.mp hd2z).resolve_right hden2
        exact eq_zero_of_pow_eq_zero hs2
      rw [hqxeq] at harg2
      have hqyeq : q.y = (p₀ a b).y := by
        apply mul_left_cancel₀ (ne_of_gt hpx)
        nlinarith only [harg2]
      have hd3z : ((p₀ a b).z * q.y - (p₀ a b).y * q.z) ^ 2 /
          (q.z * (p₀ a b).z ^ 2) = 0 := by linarith
      have hden3 : q.z * (p₀ a b).z ^ 2 ≠ 0 :=
        mul_ne_zero (ne_of_gt hqz) (pow_ne_zero 2 (ne_of_gt hpz))
      have harg3 : (p₀ a b).z * q.y - (p₀ a b).y * q.z = 0 := by
        have hs3 : ((p₀ a b).z * q.y - (p₀ a b).y * q.z) ^ 2 = 0 :=
          (div_eq_zero_iff.mp hd3z).resolve_right hden3
        exact eq_zero_of_pow_eq_zero hs3
      rw [hqyeq] at harg3
      have hqzeq : q.z = (p₀ a b).z := by
        apply mul_left_cancel₀ (ne_of_gt hpy)
        nlinarith only [harg3]
      exact point3_eq hqxeq hqyeq hqzeq

theorem gap8 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    u a b (p₀ a b) = minimumValue a b := by
  have hp := p₀_mem_positiveOctant a b ha hb
  rcases hp with ⟨hx, hy, hz⟩
  rcases p₀_stationary_relations a b ha hb with ⟨h1, h2, h3⟩
  have ht1 : a ^ 2 / (p₀ a b).x = 2 * ((p₀ a b).x ^ 2 / (p₀ a b).y) := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    nlinarith [h1]
  have ht2 : (p₀ a b).x ^ 2 / (p₀ a b).y =
      2 * ((p₀ a b).y ^ 2 / (p₀ a b).z) := by
    field_simp [ne_of_gt hy, ne_of_gt hz]
    nlinarith [h2]
  have ht3 : (p₀ a b).y ^ 2 / (p₀ a b).z =
      2 * ((p₀ a b).z ^ 2 / b) := by
    field_simp [ne_of_gt hz, ne_of_gt hb]
    nlinarith [h3]
  have hu : u a b (p₀ a b) = 15 * ((p₀ a b).z ^ 2 / b) := by
    dsimp [u]
    rw [ht1, ht2, ht3]
    ring
  rw [hu, minimumValue]
  have hr : 0 < a / (16 * b) := by positivity
  have hroot := root15_pow (a / (16 * b)) hr
  rcases p₀_power_specs a b ha hb with ⟨hx15, hy5, hz15⟩
  have hz30 : (p₀ a b).z ^ 30 =
      (a ^ 8 * b ^ 7 / 131072) ^ 2 := by
    calc
      (p₀ a b).z ^ 30 = ((p₀ a b).z ^ 15) ^ 2 := by ring
      _ = (a ^ 8 * b ^ 7 / 131072) ^ 2 := by rw [hz15]
  have hpow :
      ((p₀ a b).z ^ 2 / b) ^ 15 =
        (a / 4 * root15 (a / (16 * b))) ^ 15 := by
    rw [div_pow, mul_pow, hroot]
    field_simp [ne_of_gt ha, ne_of_gt hb]
    rw [hz30]
    ring
  have heq : (p₀ a b).z ^ 2 / b = a / 4 * root15 (a / (16 * b)) :=
    (Odd.strictMono_pow odd15).injective hpow
  rw [heq]
  ring

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    minimumPointsOn a b = {p₀ a b} := by
  apply Set.ext
  intro p
  constructor
  · intro hp
    rcases hp with ⟨hppos, hpmin⟩
    have hunique := (gap7 a b ha hb).2.2
    have hp0pos := (gap7 a b ha hb).1
    have hle := hpmin (p₀ a b) hp0pos
    have hge := (gap7 a b ha hb).2.1 p hppos
    have heq : u a b p = u a b (p₀ a b) := le_antisymm hle hge
    have hpEq : p = p₀ a b := hunique p hppos heq
    simpa [hpEq]
  · intro hp
    have hpEq : p = p₀ a b := by simpa using hp
    subst p
    refine ⟨(gap7 a b ha hb).1, ?_⟩
    exact (gap7 a b ha hb).2.1

end

end ProofGap.Exercise3646
