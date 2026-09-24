import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1155

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def x (ω t : ℝ) : ℝ := 4 * Real.sin (ω * t) - 3 * Real.cos (ω * t)
def y (ω t : ℝ) : ℝ := 3 * Real.sin (ω * t) + 4 * Real.cos (ω * t)
def vx (ω t : ℝ) : ℝ := deriv (x ω) t
def vy (ω t : ℝ) : ℝ := deriv (y ω) t
def speed (ω t : ℝ) : ℝ := Real.sqrt (vx ω t ^ 2 + vy ω t ^ 2)
def ax (ω t : ℝ) : ℝ := nthDeriv 2 (x ω) t
def ay (ω t : ℝ) : ℝ := nthDeriv 2 (y ω) t
def acceleration (ω t : ℝ) : ℝ := Real.sqrt (ax ω t ^ 2 + ay ω t ^ 2)

def expandedRadius (ω t : ℝ) : ℝ :=
  16 * Real.sin (ω * t) ^ 2 + 9 * Real.cos (ω * t) ^ 2 -
    24 * Real.sin (ω * t) * Real.cos (ω * t) +
    9 * Real.sin (ω * t) ^ 2 + 16 * Real.cos (ω * t) ^ 2 +
    24 * Real.sin (ω * t) * Real.cos (ω * t)

private theorem x_hasDerivAt (ω t : ℝ) :
    HasDerivAt (x ω)
      (4 * ω * Real.cos (ω * t) + 3 * ω * Real.sin (ω * t)) t := by
  unfold x
  convert
    ((((Real.hasDerivAt_sin (ω * t)).comp t
          ((hasDerivAt_id t).const_mul ω)).const_mul 4).sub
      (((Real.hasDerivAt_cos (ω * t)).comp t
          ((hasDerivAt_id t).const_mul ω)).const_mul 3)) using 1 <;>
    simp [id_eq] <;> ring

private theorem y_hasDerivAt (ω t : ℝ) :
    HasDerivAt (y ω)
      (3 * ω * Real.cos (ω * t) - 4 * ω * Real.sin (ω * t)) t := by
  unfold y
  convert
    ((((Real.hasDerivAt_sin (ω * t)).comp t
          ((hasDerivAt_id t).const_mul ω)).const_mul 3).add
      (((Real.hasDerivAt_cos (ω * t)).comp t
          ((hasDerivAt_id t).const_mul ω)).const_mul 4)) using 1 <;>
    simp [id_eq] <;> ring

private theorem vx_hasDerivAt (ω t : ℝ) :
    HasDerivAt (vx ω)
      (-4 * ω ^ 2 * Real.sin (ω * t) +
        3 * ω ^ 2 * Real.cos (ω * t)) t := by
  have hvx : vx ω = fun u =>
      4 * ω * Real.cos (ω * u) + 3 * ω * Real.sin (ω * u) := by
    funext u
    exact (x_hasDerivAt ω u).deriv
  rw [hvx]
  convert
    ((((Real.hasDerivAt_cos (ω * t)).comp t
          ((hasDerivAt_id t).const_mul ω)).const_mul (4 * ω)).add
      (((Real.hasDerivAt_sin (ω * t)).comp t
          ((hasDerivAt_id t).const_mul ω)).const_mul (3 * ω))) using 1 <;>
    simp [id_eq] <;> ring

private theorem vy_hasDerivAt (ω t : ℝ) :
    HasDerivAt (vy ω)
      (-4 * ω ^ 2 * Real.cos (ω * t) -
        3 * ω ^ 2 * Real.sin (ω * t)) t := by
  have hvy : vy ω = fun u =>
      3 * ω * Real.cos (ω * u) - 4 * ω * Real.sin (ω * u) := by
    funext u
    exact (y_hasDerivAt ω u).deriv
  rw [hvy]
  convert
    ((((Real.hasDerivAt_cos (ω * t)).comp t
          ((hasDerivAt_id t).const_mul ω)).const_mul (3 * ω)).sub
      (((Real.hasDerivAt_sin (ω * t)).comp t
          ((hasDerivAt_id t).const_mul ω)).const_mul (4 * ω))) using 1 <;>
    simp [id_eq] <;> ring

theorem gap1 (ω t : ℝ) :
    x ω t ^ 2 + y ω t ^ 2 = expandedRadius ω t := by
  unfold x y expandedRadius
  ring

theorem gap2 (ω t : ℝ) :
    expandedRadius ω t =
      25 * (Real.sin (ω * t) ^ 2 + Real.cos (ω * t) ^ 2) := by
  unfold expandedRadius
  ring

theorem gap3 (ω t : ℝ) :
    25 * (Real.sin (ω * t) ^ 2 + Real.cos (ω * t) ^ 2) = 25 := by
  rw [Real.sin_sq_add_cos_sq]
  ring

theorem gap4 (ω t : ℝ) :
    x ω t ^ 2 + y ω t ^ 2 = 25 := by
  rw [gap1, gap2, gap3]

theorem gap5 (ω : ℝ) (hω : ω ≠ 0) :
    Set.range (fun t => (x ω t, y ω t)) =
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 25} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    simpa using gap4 ω t
  · intro hp
    change p.1 ^ 2 + p.2 ^ 2 = 25 at hp
    let s : ℝ := (4 * p.1 + 3 * p.2) / 25
    let c : ℝ := (-3 * p.1 + 4 * p.2) / 25
    have hsc : s ^ 2 + c ^ 2 = 1 := by
      dsimp [s, c]
      nlinarith [hp]
    have hc_sq_le : c ^ 2 ≤ 1 := by
      nlinarith [hsc, sq_nonneg s]
    have hc_lower : -1 ≤ c := by
      nlinarith [hc_sq_le, sq_nonneg (c + 1)]
    have hc_upper : c ≤ 1 := by
      nlinarith [hc_sq_le, sq_nonneg (c - 1)]
    have hsquare : 1 - c ^ 2 = s ^ 2 := by
      nlinarith [hsc]
    let θ : ℝ := if 0 ≤ s then Real.arccos c else -Real.arccos c
    have hsinθ : Real.sin θ = s := by
      by_cases hs0 : 0 ≤ s
      · simp only [θ, if_pos hs0]
        rw [Real.sin_arccos, hsquare, Real.sqrt_sq hs0]
      · have hs_nonpos : s ≤ 0 := le_of_not_ge hs0
        have hroot : Real.sqrt (s ^ 2) = -s := by
          rw [show s ^ 2 = (-s) ^ 2 by ring,
            Real.sqrt_sq (neg_nonneg.mpr hs_nonpos)]
        simp only [θ, if_neg hs0, Real.sin_neg]
        rw [Real.sin_arccos, hsquare, hroot]
        ring
    have hcosθ : Real.cos θ = c := by
      by_cases hs0 : 0 ≤ s
      · simp only [θ, if_pos hs0]
        exact Real.cos_arccos hc_lower hc_upper
      · simp only [θ, if_neg hs0, Real.cos_neg]
        exact Real.cos_arccos hc_lower hc_upper
    have harg : ω * (θ / ω) = θ := by
      field_simp [hω]
    refine ⟨θ / ω, ?_⟩
    apply Prod.ext
    · dsimp [x]
      rw [harg, hsinθ, hcosθ]
      dsimp [s, c]
      ring
    · dsimp [y]
      rw [harg, hsinθ, hcosθ]
      dsimp [s, c]
      ring

theorem gap6 (ω t : ℝ) :
    speed ω t = Real.sqrt (vx ω t ^ 2 + vy ω t ^ 2) := by
  rfl

theorem gap7 (ω t : ℝ) :
    Real.sqrt (vx ω t ^ 2 + vy ω t ^ 2) =
      Real.sqrt (deriv (x ω) t ^ 2 + deriv (y ω) t ^ 2) := by
  rfl

theorem gap8 (ω t : ℝ) :
    Real.sqrt (deriv (x ω) t ^ 2 + deriv (y ω) t ^ 2) =
      Real.sqrt ((4 * ω * Real.cos (ω * t) + 3 * ω * Real.sin (ω * t)) ^ 2 +
        (3 * ω * Real.cos (ω * t) - 4 * ω * Real.sin (ω * t)) ^ 2) := by
  rw [(x_hasDerivAt ω t).deriv, (y_hasDerivAt ω t).deriv]

theorem gap9 (ω t : ℝ) :
    Real.sqrt ((4 * ω * Real.cos (ω * t) + 3 * ω * Real.sin (ω * t)) ^ 2 +
        (3 * ω * Real.cos (ω * t) - 4 * ω * Real.sin (ω * t)) ^ 2) =
      5 * |ω| := by
  have htrig := Real.sin_sq_add_cos_sq (ω * t)
  have hrad :
      (4 * ω * Real.cos (ω * t) + 3 * ω * Real.sin (ω * t)) ^ 2 +
          (3 * ω * Real.cos (ω * t) - 4 * ω * Real.sin (ω * t)) ^ 2 =
        25 * ω ^ 2 := by
    calc
      (4 * ω * Real.cos (ω * t) + 3 * ω * Real.sin (ω * t)) ^ 2 +
            (3 * ω * Real.cos (ω * t) - 4 * ω * Real.sin (ω * t)) ^ 2 =
          25 * ω ^ 2 *
            (Real.sin (ω * t) ^ 2 + Real.cos (ω * t) ^ 2) := by ring
      _ = 25 * ω ^ 2 := by rw [htrig]; ring
  rw [hrad]
  have hsquare : 25 * ω ^ 2 = (5 * |ω|) ^ 2 := by
    calc
      25 * ω ^ 2 = 25 * |ω| ^ 2 := by rw [sq_abs]
      _ = (5 * |ω|) ^ 2 := by ring
  have hnonneg : 0 ≤ 5 * |ω| :=
    mul_nonneg (by norm_num) (abs_nonneg ω)
  rw [hsquare, Real.sqrt_sq hnonneg]

theorem gap10 (ω t : ℝ) : speed ω t = 5 * |ω| := by
  rw [gap6, gap7, gap8, gap9]

theorem gap11 (ω t : ℝ) :
    acceleration ω t = Real.sqrt (ax ω t ^ 2 + ay ω t ^ 2) := by
  rfl

theorem gap12 (ω t : ℝ) :
    Real.sqrt (ax ω t ^ 2 + ay ω t ^ 2) =
      Real.sqrt (deriv (vx ω) t ^ 2 + deriv (vy ω) t ^ 2) := by
  rfl

theorem gap13 (ω t : ℝ) :
    Real.sqrt (deriv (vx ω) t ^ 2 + deriv (vy ω) t ^ 2) =
      Real.sqrt (nthDeriv 2 (x ω) t ^ 2 + nthDeriv 2 (y ω) t ^ 2) := by
  rfl

theorem gap14 (ω t : ℝ) :
    Real.sqrt (nthDeriv 2 (x ω) t ^ 2 + nthDeriv 2 (y ω) t ^ 2) =
      Real.sqrt ((-4 * ω ^ 2 * Real.sin (ω * t) +
          3 * ω ^ 2 * Real.cos (ω * t)) ^ 2 +
        (-4 * ω ^ 2 * Real.cos (ω * t) -
          3 * ω ^ 2 * Real.sin (ω * t)) ^ 2) := by
  have hx2 :
      nthDeriv 2 (x ω) t =
        -4 * ω ^ 2 * Real.sin (ω * t) +
          3 * ω ^ 2 * Real.cos (ω * t) := by
    change deriv (vx ω) t = _
    exact (vx_hasDerivAt ω t).deriv
  have hy2 :
      nthDeriv 2 (y ω) t =
        -4 * ω ^ 2 * Real.cos (ω * t) -
          3 * ω ^ 2 * Real.sin (ω * t) := by
    change deriv (vy ω) t = _
    exact (vy_hasDerivAt ω t).deriv
  rw [hx2, hy2]

theorem gap15 (ω t : ℝ) :
    Real.sqrt ((-4 * ω ^ 2 * Real.sin (ω * t) +
          3 * ω ^ 2 * Real.cos (ω * t)) ^ 2 +
        (-4 * ω ^ 2 * Real.cos (ω * t) -
          3 * ω ^ 2 * Real.sin (ω * t)) ^ 2) =
      5 * ω ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq (ω * t)
  have hrad :
      (-4 * ω ^ 2 * Real.sin (ω * t) +
            3 * ω ^ 2 * Real.cos (ω * t)) ^ 2 +
          (-4 * ω ^ 2 * Real.cos (ω * t) -
            3 * ω ^ 2 * Real.sin (ω * t)) ^ 2 =
        25 * (ω ^ 2) ^ 2 := by
    calc
      (-4 * ω ^ 2 * Real.sin (ω * t) +
              3 * ω ^ 2 * Real.cos (ω * t)) ^ 2 +
            (-4 * ω ^ 2 * Real.cos (ω * t) -
              3 * ω ^ 2 * Real.sin (ω * t)) ^ 2 =
          25 * (ω ^ 2) ^ 2 *
            (Real.sin (ω * t) ^ 2 + Real.cos (ω * t) ^ 2) := by ring
      _ = 25 * (ω ^ 2) ^ 2 := by rw [htrig]; ring
  rw [hrad]
  have hsquare : 25 * (ω ^ 2) ^ 2 = (5 * ω ^ 2) ^ 2 := by ring
  have hnonneg : 0 ≤ 5 * ω ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg ω)
  rw [hsquare, Real.sqrt_sq hnonneg]

theorem gap16 (ω t : ℝ) : acceleration ω t = 5 * ω ^ 2 := by
  rw [gap11, gap12, gap13, gap14, gap15]

end

end ProofGap.Exercise1155
