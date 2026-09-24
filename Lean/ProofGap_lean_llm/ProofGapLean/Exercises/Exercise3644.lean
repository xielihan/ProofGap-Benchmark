import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3644

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def u (p : Point3) : ℝ :=
  p.x + p.y ^ 2 / (4 * p.x) + p.z ^ 2 / p.y + 2 / p.z

def partialX (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun x => g ⟨x, p.y, p.z⟩) p.x

def partialY (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun y => g ⟨p.x, y, p.z⟩) p.y

def partialZ (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun z => g ⟨p.x, p.y, z⟩) p.z

def gradient (g : Point3 → ℝ) (p : Point3) : Point3 :=
  ⟨partialX g p, partialY g p, partialZ g p⟩

def positiveOctant : Set Point3 :=
  {p | 0 < p.x ∧ 0 < p.y ∧ 0 < p.z}

def basePoint : Point3 :=
  ⟨1 / 2, 1, 1⟩

def secondVariationAtBase (v : Point3) : ℝ :=
  (2 * v.x - v.y) ^ 2 + v.y ^ 2 +
    (v.y - 2 * v.z) ^ 2 + 2 * v.z ^ 2

def PositiveDefiniteAtBase : Prop :=
  ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ → 0 < secondVariationAtBase v

def IsUniqueGlobalMinimizerOn
    (g : Point3 → ℝ) (s : Set Point3) (p : Point3) : Prop :=
  p ∈ s ∧ (∀ q ∈ s, g p ≤ g q) ∧
    (∀ q ∈ s, g q = g p → q = p)

def minimumPointsOn : Set Point3 :=
  {p | p ∈ positiveOctant ∧ ∀ q ∈ positiveOctant, u p ≤ u q}

private theorem hasDerivAt_u_x (x y z : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => u ⟨t, y, z⟩)
      (1 - y ^ 2 / (4 * x ^ 2)) x := by
  have h :=
    (hasDerivAt_id x).add
      ((hasDerivAt_const x (y ^ 2)).div
        ((hasDerivAt_const x 4).mul (hasDerivAt_id x))
        (mul_ne_zero (by norm_num) hx))
  have h' := h.add_const (z ^ 2 / y + 2 / z)
  convert h' using 1
  · funext t
    simp [u]
    ring
  · simp only [id_eq, Pi.mul_apply]
    field_simp [hx]
    ring

private theorem hasDerivAt_u_y (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (fun t => u ⟨x, t, z⟩)
      (y / (2 * x) - z ^ 2 / y ^ 2) y := by
  have h :=
    (hasDerivAt_const y x).add
      ((hasDerivAt_pow 2 y).div_const (4 * x))
  have h' :=
    h.add ((hasDerivAt_const y (z ^ 2)).div (hasDerivAt_id y) hy)
  have h'' := h'.add_const (2 / z)
  convert h'' using 1
  simp only [id_eq, Nat.cast_ofNat, pow_one]
  field_simp [hx, hy]
  ring

private theorem hasDerivAt_u_z (x y z : ℝ) (hy : y ≠ 0) (hz : z ≠ 0) :
    HasDerivAt (fun t => u ⟨x, y, t⟩)
      (2 * z / y - 2 / z ^ 2) z := by
  have h :=
    (hasDerivAt_const z (x + y ^ 2 / (4 * x))).add
      ((hasDerivAt_pow 2 z).div_const y)
  have h' :=
    h.add ((hasDerivAt_const z 2).div (hasDerivAt_id z) hz)
  convert h' using 1
  simp only [id_eq, Nat.cast_ofNat, pow_one]
  field_simp [hy, hz]
  ring

theorem gap1 :
    ∀ p : Point3, p ∈ positiveOctant →
      gradient u p =
        ⟨1 - p.y ^ 2 / (4 * p.x ^ 2),
          p.y / (2 * p.x) - p.z ^ 2 / p.y ^ 2,
          2 * p.z / p.y - 2 / p.z ^ 2⟩ := by
  intro p hp
  rcases hp with ⟨hx, hy, hz⟩
  have hx0 : p.x ≠ 0 := ne_of_gt hx
  have hy0 : p.y ≠ 0 := ne_of_gt hy
  have hz0 : p.z ≠ 0 := ne_of_gt hz
  cases p
  congr 1 <;>
    simp [gradient, partialX, partialY, partialZ,
      (hasDerivAt_u_x _ _ _ hx0).deriv,
      (hasDerivAt_u_y _ _ _ hx0 hy0).deriv,
      (hasDerivAt_u_z _ _ _ hy0 hz0).deriv]

-- Statement correction: parenthesize the critical-point equivalence under the positive-octant hypothesis.
theorem gap2 :
    ∀ p : Point3, p ∈ positiveOctant →
      (gradient u p = ⟨0, 0, 0⟩ ↔ p = basePoint) := by
  intro p hp
  rcases hp with ⟨hx, hy, hz⟩
  have hx0 : p.x ≠ 0 := ne_of_gt hx
  have hy0 : p.y ≠ 0 := ne_of_gt hy
  have hz0 : p.z ≠ 0 := ne_of_gt hz
  constructor
  · intro hzero
    have hg := gap1 p ⟨hx, hy, hz⟩
    have h₁ := congrArg Point3.x (hg.symm.trans hzero)
    have h₂ := congrArg Point3.y (hg.symm.trans hzero)
    have h₃ := congrArg Point3.z (hg.symm.trans hzero)
    dsimp at h₁ h₂ h₃
    field_simp [hx0] at h₁
    have hyx : p.y = 2 * p.x := by
      have hs := sq_nonneg (p.y - 2 * p.x)
      nlinarith
    field_simp [hx0, hy0] at h₂
    rw [← hyx] at h₂
    have hsquare : p.y ^ 2 = p.z ^ 2 := by
      apply (mul_left_cancel₀ hy0)
      nlinarith
    have hzy : p.z = p.y := by
      exact (pow_left_inj₀ hz.le hy.le (by norm_num)).mp hsquare.symm
    field_simp [hy0, hz0] at h₃
    have hz1 : p.z = 1 := by
      nlinarith [mul_pos hz hz, hzy, hyx]
    have hy1 : p.y = 1 := by linarith
    have hxhalf : p.x = 1 / 2 := by linarith
    cases p
    simp_all [basePoint]
  · intro hp
    subst p
    have hb : basePoint ∈ positiveOctant := by
      norm_num [basePoint, positiveOctant]
    rw [gap1 basePoint hb]
    norm_num [basePoint]

theorem gap3 :
    ∀ p : Point3, p ∈ ({basePoint} : Set Point3) →
      partialX u p = 1 - p.y ^ 2 / (4 * p.x ^ 2) ∧
      1 - p.y ^ 2 / (4 * p.x ^ 2) = 0 ∧
      partialY u p = p.y / (2 * p.x) - p.z ^ 2 / p.y ^ 2 ∧
      p.y / (2 * p.x) - p.z ^ 2 / p.y ^ 2 = 0 ∧
      partialZ u p = 2 * p.z / p.y - 2 / p.z ^ 2 ∧
      2 * p.z / p.y - 2 / p.z ^ 2 = 0 := by
  intro p hp
  simp only [Set.mem_singleton_iff] at hp
  subst p
  have hdx : partialX u basePoint = 0 := by
    unfold partialX
    have h := (hasDerivAt_u_x (1 / 2) 1 1 (by norm_num)).deriv
    norm_num at h
    simpa [basePoint] using h
  have hdy : partialY u basePoint = 0 := by
    unfold partialY
    simpa [basePoint] using
      (hasDerivAt_u_y (1 / 2) 1 1 (by norm_num) (by norm_num)).deriv
  have hdz : partialZ u basePoint = 0 := by
    unfold partialZ
    simpa [basePoint] using
      (hasDerivAt_u_z (1 / 2) 1 1 (by norm_num) (by norm_num)).deriv
  refine ⟨?_, by norm_num [basePoint], ?_, by norm_num [basePoint],
    ?_, by norm_num [basePoint]⟩
  · simpa [partialX, basePoint] using
      (hasDerivAt_u_x (1 / 2) 1 1 (by norm_num)).deriv
  · simpa [partialY, basePoint] using
      (hasDerivAt_u_y (1 / 2) 1 1 (by norm_num) (by norm_num)).deriv
  · simpa [partialZ, basePoint] using
      (hasDerivAt_u_z (1 / 2) 1 1 (by norm_num) (by norm_num)).deriv

theorem gap4 :
    ∀ v : Point3,
      secondVariationAtBase v =
        (2 * v.x - v.y) ^ 2 + v.y ^ 2 +
          (v.y - 2 * v.z) ^ 2 + 2 * v.z ^ 2 := by
  intro v
  rfl

theorem gap5 :
    ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ →
      0 <
        (2 * v.x - v.y) ^ 2 + v.y ^ 2 +
          (v.y - 2 * v.z) ^ 2 + 2 * v.z ^ 2 := by
  rintro ⟨x, y, z⟩ hne
  by_contra h
  push_neg at h
  have hsum :
      (2 * x - y) ^ 2 + y ^ 2 + (y - 2 * z) ^ 2 + 2 * z ^ 2 = 0 := by
    nlinarith [sq_nonneg (2 * x - y), sq_nonneg y,
      sq_nonneg (y - 2 * z), sq_nonneg z]
  have hy0 : y = 0 := by
    nlinarith [sq_nonneg (2 * x - y), sq_nonneg y,
      sq_nonneg (y - 2 * z), sq_nonneg z]
  have hz0 : z = 0 := by
    nlinarith [sq_nonneg (2 * x - y), sq_nonneg y,
      sq_nonneg (y - 2 * z), sq_nonneg z]
  have hx0 : x = 0 := by
    nlinarith [sq_nonneg (2 * x - y), sq_nonneg y,
      sq_nonneg (y - 2 * z), sq_nonneg z]
  subst x
  subst y
  subst z
  exact hne rfl

theorem gap6 :
    PositiveDefiniteAtBase := by
  intro v hv
  exact gap5 v hv

private theorem u_decomposition (p : Point3)
    (hx : p.x ≠ 0) (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    u p - 4 =
      (2 * p.x - p.y) ^ 2 / (4 * p.x) +
      (p.y - p.z) ^ 2 / p.y +
      2 * (p.z - 1) ^ 2 / p.z := by
  unfold u
  field_simp [hx, hy, hz]
  ring

theorem gap7 :
    IsUniqueGlobalMinimizerOn u positiveOctant basePoint := by
  have hb : basePoint ∈ positiveOctant := by
    norm_num [basePoint, positiveOctant]
  have hub : u basePoint = 4 := by norm_num [u, basePoint]
  refine ⟨hb, ?_, ?_⟩
  · intro q hq
    rcases hq with ⟨hx, hy, hz⟩
    have hx0 := ne_of_gt hx
    have hy0 := ne_of_gt hy
    have hz0 := ne_of_gt hz
    have hA : 0 ≤ (2 * q.x - q.y) ^ 2 / (4 * q.x) := by positivity
    have hB : 0 ≤ (q.y - q.z) ^ 2 / q.y := by positivity
    have hC : 0 ≤ 2 * (q.z - 1) ^ 2 / q.z := by positivity
    rw [hub]
    rw [show u q = 4 +
        ((2 * q.x - q.y) ^ 2 / (4 * q.x) +
        (q.y - q.z) ^ 2 / q.y +
        2 * (q.z - 1) ^ 2 / q.z) by
      linarith [u_decomposition q hx0 hy0 hz0]]
    linarith
  · intro q hq heq
    rcases hq with ⟨hx, hy, hz⟩
    have hx0 := ne_of_gt hx
    have hy0 := ne_of_gt hy
    have hz0 := ne_of_gt hz
    have hA : 0 ≤ (2 * q.x - q.y) ^ 2 / (4 * q.x) := by positivity
    have hB : 0 ≤ (q.y - q.z) ^ 2 / q.y := by positivity
    have hC : 0 ≤ 2 * (q.z - 1) ^ 2 / q.z := by positivity
    have hsum :
        (2 * q.x - q.y) ^ 2 / (4 * q.x) +
        (q.y - q.z) ^ 2 / q.y +
        2 * (q.z - 1) ^ 2 / q.z = 0 := by
      rw [hub] at heq
      linarith [u_decomposition q hx0 hy0 hz0]
    have hA0 : (2 * q.x - q.y) ^ 2 / (4 * q.x) = 0 := by linarith
    have hB0 : (q.y - q.z) ^ 2 / q.y = 0 := by linarith
    have hC0 : 2 * (q.z - 1) ^ 2 / q.z = 0 := by linarith
    have hxy : 2 * q.x - q.y = 0 := by
      have hs : (2 * q.x - q.y) ^ 2 = 0 :=
        (div_eq_zero_iff).mp hA0 |>.resolve_right (by positivity)
      nlinarith
    have hyz : q.y - q.z = 0 := by
      have hs : (q.y - q.z) ^ 2 = 0 :=
        (div_eq_zero_iff).mp hB0 |>.resolve_right hy0
      nlinarith
    have hz1 : q.z - 1 = 0 := by
      have hs : 2 * (q.z - 1) ^ 2 = 0 :=
        (div_eq_zero_iff).mp hC0 |>.resolve_right hz0
      nlinarith
    have hxhalf : q.x = 1 / 2 := by linarith
    have hyone : q.y = 1 := by linarith
    have hzone : q.z = 1 := by linarith
    cases q
    simp_all [basePoint]

theorem gap8 :
    u basePoint = 4 := by
  norm_num [u, basePoint]

theorem gap9 :
    minimumPointsOn = {basePoint} := by
  ext p
  constructor
  · rintro ⟨hp, hmin⟩
    have hglobal := gap7
    rcases hglobal with ⟨hb, hlower, huniq⟩
    have h₁ := hmin basePoint hb
    have h₂ := hlower p hp
    simp only [Set.mem_singleton_iff]
    exact huniq p hp (le_antisymm h₁ h₂)
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst p
    exact ⟨gap7.1, gap7.2.1⟩

end

end ProofGap.Exercise3644
