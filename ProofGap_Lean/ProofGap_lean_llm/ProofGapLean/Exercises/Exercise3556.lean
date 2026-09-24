import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3556

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def levelFunction (p : Point3) : ℝ :=
  p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - p.x * p.y

def surface : Set Point3 :=
  {p | levelFunction p = 1}

def normalVector (p : Point3) : Point3 :=
  ⟨deriv (fun t => levelFunction ⟨t, p.y, p.z⟩) p.x,
    deriv (fun t => levelFunction ⟨p.x, t, p.z⟩) p.y,
    deriv (fun t => levelFunction ⟨p.x, p.y, t⟩) p.z⟩

def boundaryXY : Set Point3 :=
  {p | (normalVector p).z = 0 ∧ p ∈ surface}

def boundaryXZ : Set Point3 :=
  {p | (normalVector p).y = 0 ∧ p ∈ surface}

def boundaryYZ : Set Point3 :=
  {p | (normalVector p).x = 0 ∧ p ∈ surface}

def projectionXY : Set Point3 :=
  {q | q.z = 0 ∧ ∃ p : Point3,
    p ∈ surface ∧ q.x = p.x ∧ q.y = p.y}

def projectionYZ : Set Point3 :=
  {q | q.x = 0 ∧ ∃ p : Point3,
    p ∈ surface ∧ q.y = p.y ∧ q.z = p.z}

def projectionXZ : Set Point3 :=
  {q | q.y = 0 ∧ ∃ p : Point3,
    p ∈ surface ∧ q.x = p.x ∧ q.z = p.z}

theorem gap1 :
    ∀ p : Point3,
      normalVector p =
        ⟨2 * p.x - p.y, 2 * p.y - p.x, 2 * p.z⟩ := by
  intro p
  have hx :
      deriv (fun t : ℝ => levelFunction ⟨t, p.y, p.z⟩) p.x =
        2 * p.x - p.y := by
    have hx2 := (hasDerivAt_id p.x).pow 2
    have hy2 := hasDerivAt_const p.x (p.y ^ 2)
    have hz2 := hasDerivAt_const p.x (p.z ^ 2)
    have hxy :=
      (hasDerivAt_id p.x).mul (hasDerivAt_const p.x p.y)
    have h := ((hx2.add hy2).add hz2).sub hxy
    change
      deriv (fun t : ℝ =>
        t ^ 2 + p.y ^ 2 + p.z ^ 2 - t * p.y) p.x =
        2 * p.x - p.y
    have hd := h.deriv
    change
      deriv (fun t : ℝ =>
        t ^ 2 + p.y ^ 2 + p.z ^ 2 - t * p.y) p.x = _ at hd
    rw [hd] <;> simp [id]
  have hy :
      deriv (fun t : ℝ => levelFunction ⟨p.x, t, p.z⟩) p.y =
        2 * p.y - p.x := by
    have hx2 := hasDerivAt_const p.y (p.x ^ 2)
    have hy2 := (hasDerivAt_id p.y).pow 2
    have hz2 := hasDerivAt_const p.y (p.z ^ 2)
    have hxy :=
      (hasDerivAt_const p.y p.x).mul (hasDerivAt_id p.y)
    have h := ((hx2.add hy2).add hz2).sub hxy
    change
      deriv (fun t : ℝ =>
        p.x ^ 2 + t ^ 2 + p.z ^ 2 - p.x * t) p.y =
        2 * p.y - p.x
    have hd := h.deriv
    change
      deriv (fun t : ℝ =>
        p.x ^ 2 + t ^ 2 + p.z ^ 2 - p.x * t) p.y = _ at hd
    rw [hd] <;> simp [id]
  have hz :
      deriv (fun t : ℝ => levelFunction ⟨p.x, p.y, t⟩) p.z =
        2 * p.z := by
    have hx2 := hasDerivAt_const p.z (p.x ^ 2)
    have hy2 := hasDerivAt_const p.z (p.y ^ 2)
    have hz2 := (hasDerivAt_id p.z).pow 2
    have hxy := hasDerivAt_const p.z (p.x * p.y)
    have h := ((hx2.add hy2).add hz2).sub hxy
    change
      deriv (fun t : ℝ =>
        p.x ^ 2 + p.y ^ 2 + t ^ 2 - p.x * p.y) p.z =
        2 * p.z
    have hd := h.deriv
    change
      deriv (fun t : ℝ =>
        p.x ^ 2 + p.y ^ 2 + t ^ 2 - p.x * p.y) p.z = _ at hd
    rw [hd] <;> simp [id]
  unfold normalVector
  rw [hx, hy, hz]

theorem gap2 :
    boundaryXY =
      {p | 2 * p.z = 0 ∧
        p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - p.x * p.y = 1} := by
  ext p
  simp [boundaryXY, surface, levelFunction, gap1]

theorem gap3 :
    boundaryXY =
      {p | p.z = 0 ∧ p.x ^ 2 + p.y ^ 2 - p.x * p.y = 1} := by
  rw [gap2]
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, heq⟩
    have hz0 : p.z = 0 := by linarith
    exact ⟨hz0, by simpa [hz0] using heq⟩
  · rintro ⟨hz, heq⟩
    exact ⟨by simp [hz], by simpa [hz] using heq⟩

theorem gap4 :
    boundaryXZ =
      {p | 2 * p.y - p.x = 0 ∧
        p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - p.x * p.y = 1} := by
  ext p
  simp [boundaryXZ, surface, levelFunction, gap1]

theorem gap5 :
    boundaryXZ =
      {p | 2 * p.y - p.x = 0 ∧
        (3 * p.x ^ 2) / 4 + p.z ^ 2 = 1} := by
  rw [gap4]
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hlin, heq⟩
    refine ⟨hlin, ?_⟩
    have hid :
        p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - p.x * p.y =
          (3 * p.x ^ 2) / 4 + p.z ^ 2 + (2 * p.y - p.x) ^ 2 / 4 := by
      ring
    rw [hid] at heq
    simpa [hlin] using heq
  · rintro ⟨hlin, heq⟩
    refine ⟨hlin, ?_⟩
    have hid :
        p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - p.x * p.y =
          (3 * p.x ^ 2) / 4 + p.z ^ 2 + (2 * p.y - p.x) ^ 2 / 4 := by
      ring
    rw [hid]
    simpa [hlin] using heq

theorem gap6 :
    boundaryYZ =
      {p | 2 * p.x - p.y = 0 ∧
        (3 * p.y ^ 2) / 4 + p.z ^ 2 = 1} := by
  ext p
  change
    ((normalVector p).x = 0 ∧ levelFunction p = 1) ↔
      (2 * p.x - p.y = 0 ∧ (3 * p.y ^ 2) / 4 + p.z ^ 2 = 1)
  rw [gap1 p]
  change
    (2 * p.x - p.y = 0 ∧
        p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - p.x * p.y = 1) ↔
      (2 * p.x - p.y = 0 ∧ (3 * p.y ^ 2) / 4 + p.z ^ 2 = 1)
  constructor
  · rintro ⟨hlin, heq⟩
    refine ⟨hlin, ?_⟩
    have hid :
        p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - p.x * p.y =
          (3 * p.y ^ 2) / 4 + p.z ^ 2 + (2 * p.x - p.y) ^ 2 / 4 := by
      ring
    rw [hid] at heq
    simpa [hlin] using heq
  · rintro ⟨hlin, heq⟩
    refine ⟨hlin, ?_⟩
    have hid :
        p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - p.x * p.y =
          (3 * p.y ^ 2) / 4 + p.z ^ 2 + (2 * p.x - p.y) ^ 2 / 4 := by
      ring
    rw [hid]
    simpa [hlin] using heq

theorem gap7 :
    projectionXY =
      {p | p.x ^ 2 + p.y ^ 2 - p.x * p.y ≤ 1 ∧ p.z = 0} := by
  ext q
  change
    (q.z = 0 ∧ ∃ p : Point3,
      levelFunction p = 1 ∧ q.x = p.x ∧ q.y = p.y) ↔
      (q.x ^ 2 + q.y ^ 2 - q.x * q.y ≤ 1 ∧ q.z = 0)
  constructor
  · rintro ⟨hqz, p, hp, hx, hy⟩
    refine ⟨?_, hqz⟩
    rw [hx, hy]
    unfold levelFunction at hp
    nlinarith [sq_nonneg p.z]
  · rintro ⟨hbase, hqz⟩
    let r : ℝ := 1 - (q.x ^ 2 + q.y ^ 2 - q.x * q.y)
    have hr : 0 ≤ r := by
      dsimp [r]
      linarith
    refine ⟨hqz, ⟨⟨q.x, q.y, Real.sqrt r⟩, ?_, rfl, rfl⟩⟩
    unfold levelFunction
    dsimp
    rw [Real.sq_sqrt hr]
    dsimp [r]
    ring

theorem gap8 :
    projectionYZ =
      {p | (3 * p.y ^ 2) / 4 + p.z ^ 2 ≤ 1 ∧ p.x = 0} := by
  ext q
  change
    (q.x = 0 ∧ ∃ p : Point3,
      levelFunction p = 1 ∧ q.y = p.y ∧ q.z = p.z) ↔
      ((3 * q.y ^ 2) / 4 + q.z ^ 2 ≤ 1 ∧ q.x = 0)
  constructor
  · rintro ⟨hqx, p, hp, hy, hz⟩
    refine ⟨?_, hqx⟩
    rw [hy, hz]
    unfold levelFunction at hp
    nlinarith [sq_nonneg (2 * p.x - p.y)]
  · rintro ⟨hbase, hqx⟩
    let r : ℝ := 1 - (3 * q.y ^ 2) / 4 - q.z ^ 2
    have hr : 0 ≤ r := by
      dsimp [r]
      linarith
    refine ⟨hqx, ⟨⟨q.y / 2 + Real.sqrt r, q.y, q.z⟩, ?_, rfl, rfl⟩⟩
    have hident :
        levelFunction ⟨q.y / 2 + Real.sqrt r, q.y, q.z⟩ =
          (3 * q.y ^ 2) / 4 + q.z ^ 2 + (Real.sqrt r) ^ 2 := by
      unfold levelFunction
      dsimp
      ring
    rw [hident, Real.sq_sqrt hr]
    dsimp [r]
    ring

theorem gap9 :
    projectionXZ =
      {p | (3 * p.x ^ 2) / 4 + p.z ^ 2 ≤ 1 ∧ p.y = 0} := by
  ext q
  change
    (q.y = 0 ∧ ∃ p : Point3,
      levelFunction p = 1 ∧ q.x = p.x ∧ q.z = p.z) ↔
      ((3 * q.x ^ 2) / 4 + q.z ^ 2 ≤ 1 ∧ q.y = 0)
  constructor
  · rintro ⟨hqy, p, hp, hx, hz⟩
    refine ⟨?_, hqy⟩
    rw [hx, hz]
    unfold levelFunction at hp
    nlinarith [sq_nonneg (2 * p.y - p.x)]
  · rintro ⟨hbase, hqy⟩
    let r : ℝ := 1 - (3 * q.x ^ 2) / 4 - q.z ^ 2
    have hr : 0 ≤ r := by
      dsimp [r]
      linarith
    refine ⟨hqy, ⟨⟨q.x, q.x / 2 + Real.sqrt r, q.z⟩, ?_, rfl, rfl⟩⟩
    have hident :
        levelFunction ⟨q.x, q.x / 2 + Real.sqrt r, q.z⟩ =
          (3 * q.x ^ 2) / 4 + q.z ^ 2 + (Real.sqrt r) ^ 2 := by
      unfold levelFunction
      dsimp
      ring
    rw [hident, Real.sq_sqrt hr]
    dsimp [r]
    ring

end

end ProofGap.Exercise3556
