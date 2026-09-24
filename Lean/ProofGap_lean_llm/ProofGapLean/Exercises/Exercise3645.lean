import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.MeanInequalities

namespace ProofGap.Exercise3645

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def u (a : ℝ) (p : Point3) : ℝ :=
  p.x * p.y ^ 2 * p.z ^ 3 * (a - p.x - 2 * p.y - 3 * p.z)

def partialX (a : ℝ) (p : Point3) : ℝ :=
  deriv (fun x => u a ⟨x, p.y, p.z⟩) p.x

def partialY (a : ℝ) (p : Point3) : ℝ :=
  deriv (fun y => u a ⟨p.x, y, p.z⟩) p.y

def partialZ (a : ℝ) (p : Point3) : ℝ :=
  deriv (fun z => u a ⟨p.x, p.y, z⟩) p.z

def gradient (a : ℝ) (p : Point3) : Point3 :=
  ⟨partialX a p, partialY a p, partialZ a p⟩

def Stationary (a : ℝ) (p : Point3) : Prop :=
  gradient a p = ⟨0, 0, 0⟩

def positiveOctant : Set Point3 :=
  {p | 0 < p.x ∧ 0 < p.y ∧ 0 < p.z}

def p₀ (a : ℝ) : Point3 :=
  ⟨a / 7, a / 7, a / 7⟩

def stationaryDescription (a : ℝ) (p : Point3) : Prop :=
  p.z = 0 ∨
    p.y = 0 ∨
    (p.x = 0 ∧ a - 2 * p.y - 3 * p.z = 0) ∨
    p = p₀ a

def coefficientOnYZero (a : ℝ) (p : Point3) : ℝ :=
  p.x * p.z ^ 3 * (a - p.x - 3 * p.z)

def distanceSquared (p q : Point3) : ℝ :=
  (q.x - p.x) ^ 2 + (q.y - p.y) ^ 2 + (q.z - p.z) ^ 2

def IsLocalMinimum (a : ℝ) (p : Point3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : Point3, distanceSquared p q < ε ^ 2 → u a p ≤ u a q

def IsLocalMaximum (a : ℝ) (p : Point3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : Point3, distanceSquared p q < ε ^ 2 → u a q ≤ u a p

def IsStrictLocalMaximum (a : ℝ) (p : Point3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : Point3, q ≠ p → distanceSquared p q < ε ^ 2 →
      u a q < u a p

def secondVariationAtP₀ (a : ℝ) (v : Point3) : ℝ :=
  -(a ^ 5 / (7 : ℝ) ^ 5) *
    ((v.x + 2 * v.y + 3 * v.z) ^ 2 +
      v.x ^ 2 + 2 * v.y ^ 2 + 3 * v.z ^ 2)

def NegativeDefiniteAtP₀ (a : ℝ) : Prop :=
  ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ → secondVariationAtP₀ a v < 0

def localMaximumPoints (a : ℝ) : Set Point3 :=
  {p | IsLocalMaximum a p}

private theorem deriv_u_x (a : ℝ) (p : Point3) :
    partialX a p =
      p.y ^ 2 * p.z ^ 3 * (a - 2 * p.x - 2 * p.y - 3 * p.z) := by
  unfold partialX u
  have h :
      HasDerivAt
        (fun x : ℝ =>
          (x * (p.y ^ 2 * p.z ^ 3)) *
            ((a - 2 * p.y - 3 * p.z) - x))
        (p.y ^ 2 * p.z ^ 3 *
          (a - 2 * p.y - 3 * p.z - p.x) -
            p.x * (p.y ^ 2 * p.z ^ 3)) p.x := by
    convert
      ((hasDerivAt_id p.x).mul_const (p.y ^ 2 * p.z ^ 3)).mul
        ((hasDerivAt_const p.x (a - 2 * p.y - 3 * p.z)).sub
          (hasDerivAt_id p.x)) using 1 <;>
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq] <;> ring
  have heq :
      (fun x : ℝ =>
        x * p.y ^ 2 * p.z ^ 3 * (a - x - 2 * p.y - 3 * p.z)) =
      (fun x : ℝ =>
        (x * (p.y ^ 2 * p.z ^ 3)) *
          ((a - 2 * p.y - 3 * p.z) - x)) := by
    funext x
    ring
  rw [heq]
  convert h.deriv using 1 <;> ring

private theorem deriv_u_y (a : ℝ) (p : Point3) :
    partialY a p =
      2 * p.x * p.y * p.z ^ 3 *
        (a - p.x - 3 * p.y - 3 * p.z) := by
  unfold partialY u
  have h :
      HasDerivAt
        (fun y : ℝ =>
          (p.x * y ^ 2 * p.z ^ 3) *
            ((a - p.x - 3 * p.z) - 2 * y))
        ((2 * p.x * p.y * p.z ^ 3) *
            (a - p.x - 3 * p.z - 2 * p.y) -
          2 * (p.x * p.y ^ 2 * p.z ^ 3)) p.y := by
    convert
      (((hasDerivAt_const p.y p.x).mul ((hasDerivAt_id p.y).pow 2)).mul_const
          (p.z ^ 3)).mul
        ((hasDerivAt_const p.y (a - p.x - 3 * p.z)).sub
          ((hasDerivAt_id p.y).const_mul 2)) using 1 <;>
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq, Pi.pow_apply] <;> ring
  have heq :
      (fun y : ℝ =>
        p.x * y ^ 2 * p.z ^ 3 * (a - p.x - 2 * y - 3 * p.z)) =
      (fun y : ℝ =>
        (p.x * y ^ 2 * p.z ^ 3) *
          ((a - p.x - 3 * p.z) - 2 * y)) := by
    funext y
    ring
  rw [heq]
  convert h.deriv using 1 <;> ring

private theorem deriv_u_z (a : ℝ) (p : Point3) :
    partialZ a p =
      3 * p.x * p.y ^ 2 * p.z ^ 2 *
        (a - p.x - 2 * p.y - 4 * p.z) := by
  unfold partialZ u
  have h :
      HasDerivAt
        (fun z : ℝ =>
          (p.x * p.y ^ 2 * z ^ 3) *
            ((a - p.x - 2 * p.y) - 3 * z))
        ((3 * p.x * p.y ^ 2 * p.z ^ 2) *
            (a - p.x - 2 * p.y - 3 * p.z) -
          3 * (p.x * p.y ^ 2 * p.z ^ 3)) p.z := by
    convert
      (((hasDerivAt_const p.z (p.x * p.y ^ 2)).mul
          ((hasDerivAt_id p.z).pow 3)).mul
        ((hasDerivAt_const p.z (a - p.x - 2 * p.y)).sub
          ((hasDerivAt_id p.z).const_mul 3))) using 1 <;>
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq, Pi.pow_apply] <;> ring
  have heq :
      (fun z : ℝ =>
        p.x * p.y ^ 2 * z ^ 3 * (a - p.x - 2 * p.y - 3 * z)) =
      (fun z : ℝ =>
        (p.x * p.y ^ 2 * z ^ 3) *
          ((a - p.x - 2 * p.y) - 3 * z)) := by
    funext z
    ring
  rw [heq]
  convert h.deriv using 1 <;> ring

theorem gap1 :
    ∀ a : ℝ, ∀ p : Point3,
      gradient a p =
        ⟨p.y ^ 2 * p.z ^ 3 *
            (a - 2 * p.x - 2 * p.y - 3 * p.z),
          2 * p.x * p.y * p.z ^ 3 *
            (a - p.x - 3 * p.y - 3 * p.z),
          3 * p.x * p.y ^ 2 * p.z ^ 2 *
            (a - p.x - 2 * p.y - 4 * p.z)⟩ := by
  intro a p
  simp only [gradient, Point3.mk.injEq]
  exact ⟨deriv_u_x a p, deriv_u_y a p, deriv_u_z a p⟩

private theorem stationary_iff_components (a : ℝ) (p : Point3) :
    Stationary a p ↔
      p.y ^ 2 * p.z ^ 3 *
          (a - 2 * p.x - 2 * p.y - 3 * p.z) = 0 ∧
      2 * p.x * p.y * p.z ^ 3 *
          (a - p.x - 3 * p.y - 3 * p.z) = 0 ∧
      3 * p.x * p.y ^ 2 * p.z ^ 2 *
          (a - p.x - 2 * p.y - 4 * p.z) = 0 := by
  rw [Stationary, gap1 a p]
  simp only [Point3.mk.injEq]

-- Statement correction: parenthesize the intended equivalence under the octant hypothesis.
theorem gap2 (a : ℝ) (ha : 0 < a) :
    ∀ p : Point3, p ∈ positiveOctant →
      (Stationary a p ↔ p = p₀ a) := by
  intro p hp
  rcases hp with ⟨hx, hy, hz⟩
  constructor
  · intro hs
    rcases (stationary_iff_components a p).1 hs with ⟨he1, he2, he3⟩
    have hxy : p.y ^ 2 * p.z ^ 3 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 (ne_of_gt hy)) (pow_ne_zero 3 (ne_of_gt hz))
    have hxyz2 : 2 * p.x * p.y * p.z ^ 3 ≠ 0 := by positivity
    have hxyz3 : 3 * p.x * p.y ^ 2 * p.z ^ 2 ≠ 0 := by positivity
    have h1 : a - 2 * p.x - 2 * p.y - 3 * p.z = 0 :=
      (mul_eq_zero.mp he1).resolve_left hxy
    have h2 : a - p.x - 3 * p.y - 3 * p.z = 0 :=
      (mul_eq_zero.mp he2).resolve_left hxyz2
    have h3 : a - p.x - 2 * p.y - 4 * p.z = 0 :=
      (mul_eq_zero.mp he3).resolve_left hxyz3
    cases p with
    | mk x y z =>
        simp only [p₀, Point3.mk.injEq]
        constructor
        · linarith
        constructor <;> linarith
  · rintro rfl
    apply (stationary_iff_components a (p₀ a)).2
    simp only [p₀]
    constructor
    · ring
    constructor <;> ring

theorem gap3 (a : ℝ) :
    ∀ p : Point3, p.x = 0 → p.y ≠ 0 → p.z ≠ 0 →
      (Stationary a p ↔ 2 * p.y + 3 * p.z = a) := by
  intro p hx hy hz
  constructor
  · intro hs
    have he := (stationary_iff_components a p).1 hs |>.1
    have hfac : p.y ^ 2 * p.z ^ 3 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 3 hz)
    have : a - 2 * p.x - 2 * p.y - 3 * p.z = 0 :=
      (mul_eq_zero.mp he).resolve_left hfac
    linarith
  · intro h
    apply (stationary_iff_components a p).2
    rw [hx]
    constructor
    · have : a - 2 * p.y - 3 * p.z = 0 := by linarith
      simp [this]
    constructor <;> ring

theorem gap4 (a : ℝ) :
    ∀ p : Point3, p.x = 0 → 2 * p.y + 3 * p.z = a →
      Stationary a p := by
  intro p hx h
  apply (stationary_iff_components a p).2
  rw [hx]
  have hlin : a - 2 * p.y - 3 * p.z = 0 := by linarith
  constructor
  · simp [hlin]
  constructor <;> ring

theorem gap5 (a : ℝ) :
    ∀ p : Point3, p.y = 0 →
      Stationary a p := by
  intro p hy
  apply (stationary_iff_components a p).2
  rw [hy]
  constructor
  · ring
  constructor <;> ring

theorem gap6 (a : ℝ) :
    ∀ p : Point3, p.z = 0 → Stationary a p := by
  intro p hz
  apply (stationary_iff_components a p).2
  rw [hz]
  constructor
  · ring
  constructor <;> ring

theorem gap7 (a : ℝ) :
    {p : Point3 | Stationary a p} =
      {p : Point3 | stationaryDescription a p} := by
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hs
    rcases (stationary_iff_components a p).1 hs with ⟨he1, he2, he3⟩
    by_cases hz : p.z = 0
    · exact Or.inl hz
    by_cases hy : p.y = 0
    · exact Or.inr (Or.inl hy)
    by_cases hx : p.x = 0
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨hx, ?_⟩
      have hfac : p.y ^ 2 * p.z ^ 3 ≠ 0 :=
        mul_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 3 hz)
      have hlin : a - 2 * p.x - 2 * p.y - 3 * p.z = 0 :=
        (mul_eq_zero.mp he1).resolve_left hfac
      linarith
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      have hfac1 : p.y ^ 2 * p.z ^ 3 ≠ 0 :=
        mul_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 3 hz)
      have hfac2 : 2 * p.x * p.y * p.z ^ 3 ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hx) hy)
          (pow_ne_zero 3 hz)
      have hfac3 : 3 * p.x * p.y ^ 2 * p.z ^ 2 ≠ 0 := by
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) hx) (pow_ne_zero 2 hy))
          (pow_ne_zero 2 hz)
      have h1 : a - 2 * p.x - 2 * p.y - 3 * p.z = 0 :=
        (mul_eq_zero.mp he1).resolve_left hfac1
      have h2 : a - p.x - 3 * p.y - 3 * p.z = 0 :=
        (mul_eq_zero.mp he2).resolve_left hfac2
      have h3 : a - p.x - 2 * p.y - 4 * p.z = 0 :=
        (mul_eq_zero.mp he3).resolve_left hfac3
      cases p with
      | mk x y z =>
          simp only [p₀, Point3.mk.injEq]
          constructor
          · linarith
          constructor <;> linarith
  · intro hd
    rcases hd with hz | hy | hplane | hp
    · exact gap6 a p hz
    · exact gap5 a p hy
    · exact gap4 a p hplane.1 (by linarith [hplane.2])
    · subst p
      apply (stationary_iff_components a (p₀ a)).2
      simp only [p₀]
      constructor
      · ring
      constructor <;> ring

private theorem no_local_extrema_of_signed_points
    (a : ℝ) (p : Point3) (hzero : u a p = 0)
    (hsigned :
      ∀ ε : ℝ, 0 < ε →
        ∃ qpos qneg : Point3,
          distanceSquared p qpos < ε ^ 2 ∧
          0 < u a qpos ∧
          distanceSquared p qneg < ε ^ 2 ∧
          u a qneg < 0) :
    ¬ IsLocalMaximum a p ∧ ¬ IsLocalMinimum a p := by
  constructor
  · rintro ⟨ε, hε, hmax⟩
    obtain ⟨qpos, qneg, hdp, hup, hdn, hun⟩ := hsigned ε hε
    have := hmax qpos hdp
    rw [hzero] at this
    linarith
  · rintro ⟨ε, hε, hmin⟩
    obtain ⟨qpos, qneg, hdp, hup, hdn, hun⟩ := hsigned ε hε
    have := hmin qneg hdn
    rw [hzero] at this
    linarith

private theorem exists_tiny_positive (ε b : ℝ) (hε : 0 < ε) (hb : 0 < b) :
    ∃ t : ℝ, 0 < t ∧ 10 * t < ε ∧ 10 * t < b := by
  refine ⟨min ε b / 20, ?_⟩
  have hm : 0 < min ε b := lt_min hε hb
  have hmε : min ε b ≤ ε := min_le_left _ _
  have hmb : min ε b ≤ b := min_le_right _ _
  constructor
  · positivity
  constructor <;> linarith

theorem gap8 (a : ℝ) :
    ∀ p : Point3, p.x = 0 → 2 * p.y + 3 * p.z = a →
      ¬ IsLocalMaximum a p ∧ ¬ IsLocalMinimum a p := by
  intro p hx hplane
  have hzero : u a p = 0 := by simp [u, hx]
  apply no_local_extrema_of_signed_points a p hzero
  intro ε hε
  by_cases hy : p.y = 0
  · by_cases hz : p.z = 0
    · obtain ⟨t, ht, htε, htt⟩ :=
        exists_tiny_positive ε ε hε hε
      have ha0 : a = 0 := by linarith
      let qpos : Point3 := ⟨-t, t, t⟩
      let qneg : Point3 := ⟨t, t, t⟩
      have hup : u a qpos = 4 * t ^ 7 := by
        simp only [u, qpos, ha0]
        ring
      have hun : u a qneg = -6 * t ^ 7 := by
        simp only [u, qneg, ha0]
        ring
      refine ⟨qpos, qneg, ?_, ?_, ?_, ?_⟩
      · simp only [distanceSquared, qpos, hx, hy, hz]
        nlinarith
      · rw [hup]
        positivity
      · simp only [distanceSquared, qneg, hx, hy, hz]
        nlinarith
      · rw [hun]
        have ht7 : 0 < t ^ 7 := pow_pos ht _
        linarith
    · obtain ⟨t, ht, htε, htt⟩ :=
        exists_tiny_positive ε ε hε hε
      have hzsign : p.z < 0 ∨ 0 < p.z := lt_or_gt_of_ne hz
      let q₁ : Point3 := ⟨t, t, p.z⟩
      let q₂ : Point3 := ⟨t, -t, p.z⟩
      have hd₁ : distanceSquared p q₁ < ε ^ 2 := by
        simp only [distanceSquared, q₁, hx, hy]
        nlinarith
      have hd₂ : distanceSquared p q₂ < ε ^ 2 := by
        simp only [distanceSquared, q₂, hx, hy]
        nlinarith
      have hu₁ :
          u a q₁ = -3 * t ^ 4 * p.z ^ 3 := by
        simp only [u, q₁]
        rw [← hplane, hy]
        ring
      have hu₂ :
          u a q₂ = t ^ 4 * p.z ^ 3 := by
        simp only [u, q₂]
        rw [← hplane, hy]
        ring
      rcases hzsign with hzneg | hzpos
      · refine ⟨q₁, q₂, hd₁, ?_, hd₂, ?_⟩
        · rw [hu₁]
          have ht4 : 0 < t ^ 4 := pow_pos ht _
          have hz3 : p.z ^ 3 < 0 := (Odd.pow_neg (by decide) hzneg)
          have hm : t ^ 4 * p.z ^ 3 < 0 :=
            mul_neg_of_pos_of_neg ht4 hz3
          linarith
        · rw [hu₂]
          have ht4 : 0 < t ^ 4 := pow_pos ht _
          have hz3 : p.z ^ 3 < 0 := (Odd.pow_neg (by decide) hzneg)
          exact mul_neg_of_pos_of_neg ht4 hz3
      · refine ⟨q₂, q₁, hd₂, ?_, hd₁, ?_⟩
        · rw [hu₂]
          exact mul_pos (pow_pos ht _) (pow_pos hzpos _)
        · rw [hu₁]
          have hm : 0 < t ^ 4 * p.z ^ 3 :=
            mul_pos (pow_pos ht _) (pow_pos hzpos _)
          linarith
  · by_cases hz : p.z = 0
    · obtain ⟨t, ht, htε, htt⟩ :=
        exists_tiny_positive ε ε hε hε
      let qpos : Point3 := ⟨-t, p.y, t⟩
      let qneg : Point3 := ⟨t, p.y, t⟩
      have hup : u a qpos = 2 * t ^ 5 * p.y ^ 2 := by
        simp only [u, qpos]
        rw [← hplane, hz]
        ring
      have hun : u a qneg = -4 * t ^ 5 * p.y ^ 2 := by
        simp only [u, qneg]
        rw [← hplane, hz]
        ring
      refine ⟨qpos, qneg, ?_, ?_, ?_, ?_⟩
      · simp only [distanceSquared, qpos, hx, hz]
        nlinarith
      · rw [hup]
        have hy2 : 0 < p.y ^ 2 := sq_pos_of_ne_zero hy
        positivity
      · simp only [distanceSquared, qneg, hx, hz]
        nlinarith
      · rw [hun]
        have hm : 0 < t ^ 5 * p.y ^ 2 :=
          mul_pos (pow_pos ht _) (sq_pos_of_ne_zero hy)
        linarith
    · obtain ⟨t, ht, htε, hty⟩ :=
        exists_tiny_positive ε |p.y| hε (abs_pos.mpr hy)
      have hyt : p.y - t ≠ 0 := by
        rcases lt_or_gt_of_ne hy with hyneg | hypos
        · linarith
        · rw [abs_of_pos hypos] at hty
          linarith
      have hzsign : p.z < 0 ∨ 0 < p.z := lt_or_gt_of_ne hz
      let q₁ : Point3 := ⟨t, p.y, p.z⟩
      let q₂ : Point3 := ⟨t, p.y - t, p.z⟩
      have hd₁ : distanceSquared p q₁ < ε ^ 2 := by
        simp only [distanceSquared, q₁, hx]
        nlinarith
      have hd₂ : distanceSquared p q₂ < ε ^ 2 := by
        simp only [distanceSquared, q₂, hx]
        nlinarith
      have hu₁ :
          u a q₁ = -t ^ 2 * p.y ^ 2 * p.z ^ 3 := by
        simp only [u, q₁]
        rw [← hplane]
        ring
      have hu₂ :
          u a q₂ = t ^ 2 * (p.y - t) ^ 2 * p.z ^ 3 := by
        simp only [u, q₂]
        rw [← hplane]
        ring
      rcases hzsign with hzneg | hzpos
      · refine ⟨q₁, q₂, hd₁, ?_, hd₂, ?_⟩
        · rw [hu₁]
          have hz3 : p.z ^ 3 < 0 := (Odd.pow_neg (by decide) hzneg)
          have hm : t ^ 2 * p.y ^ 2 * p.z ^ 3 < 0 := by
            exact mul_neg_of_pos_of_neg
              (mul_pos (pow_pos ht _) (sq_pos_of_ne_zero hy)) hz3
          linarith
        · rw [hu₂]
          have hz3 : p.z ^ 3 < 0 := (Odd.pow_neg (by decide) hzneg)
          have hyt2 : 0 < (p.y - t) ^ 2 := sq_pos_of_ne_zero hyt
          exact mul_neg_of_pos_of_neg
            (mul_pos (pow_pos ht _) hyt2) hz3
      · refine ⟨q₂, q₁, hd₂, ?_, hd₁, ?_⟩
        · rw [hu₂]
          have hyt2 : 0 < (p.y - t) ^ 2 := sq_pos_of_ne_zero hyt
          exact mul_pos (mul_pos (pow_pos ht _) hyt2) (pow_pos hzpos _)
        · rw [hu₁]
          have hm : 0 < t ^ 2 * p.y ^ 2 * p.z ^ 3 := by
            exact mul_pos
              (mul_pos (pow_pos ht _) (sq_pos_of_ne_zero hy))
              (pow_pos hzpos _)
          linarith

theorem gap9 (a : ℝ) :
    ∀ p : Point3, p.z = 0 →
      ¬ IsLocalMaximum a p ∧ ¬ IsLocalMinimum a p := by
  intro p hz
  have hzero : u a p = 0 := by simp [u, hz]
  apply no_local_extrema_of_signed_points a p hzero
  intro ε hε
  let W : ℝ := a - p.x - 2 * p.y
  by_cases hW : W = 0
  · by_cases hy : p.y = 0
    · obtain ⟨t, ht, htε, htt⟩ :=
        exists_tiny_positive ε ε hε hε
      let xq : ℝ := if p.x = 0 then t else p.x
      let yp : ℝ := (a - xq - 3 * t - t) / 2
      let yn : ℝ := (a - xq + 3 * t - t) / 2
      let qplus : Point3 := ⟨xq, yp, t⟩
      let qminus : Point3 := ⟨xq, yn, -t⟩
      have hxq : xq ≠ 0 := by
        dsimp [xq]
        split_ifs with hx
        · exact ne_of_gt ht
        · exact hx
      have hyp : yp ≠ 0 := by
        dsimp [yp, xq, W] at *
        split_ifs with hx
        · linarith
        · linarith
      have hyn : yn ≠ 0 := by
        dsimp [yn, xq, W] at *
        split_ifs with hx
        · linarith
        · linarith
      have hdp : distanceSquared p qplus < ε ^ 2 := by
        simp only [distanceSquared, qplus, hz]
        dsimp [yp, xq, W] at *
        split_ifs with hx
        · nlinarith
        · nlinarith
      have hdn : distanceSquared p qminus < ε ^ 2 := by
        simp only [distanceSquared, qminus, hz]
        dsimp [yn, xq, W] at *
        split_ifs with hx
        · nlinarith
        · nlinarith
      have hup_eq : u a qplus = xq * yp ^ 2 * t ^ 4 := by
        simp only [u, qplus]
        dsimp [yp]
        ring
      have hun_eq : u a qminus = -(xq * yn ^ 2 * t ^ 4) := by
        simp only [u, qminus]
        dsimp [yn]
        ring
      rcases lt_or_gt_of_ne hxq with hxneg | hxpos
      · refine ⟨qminus, qplus, hdn, ?_, hdp, ?_⟩
        · rw [hun_eq]
          have hm : xq * yn ^ 2 * t ^ 4 < 0 :=
            mul_neg_of_neg_of_pos
              (mul_neg_of_neg_of_pos hxneg (sq_pos_of_ne_zero hyn))
              (pow_pos ht _)
          linarith
        · rw [hup_eq]
          exact mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos hxneg (sq_pos_of_ne_zero hyp))
            (pow_pos ht _)
      · refine ⟨qplus, qminus, hdp, ?_, hdn, ?_⟩
        · rw [hup_eq]
          positivity
        · rw [hun_eq]
          have hm : 0 < xq * yn ^ 2 * t ^ 4 := by positivity
          linarith
    · obtain ⟨t, ht, htε, hty⟩ :=
        exists_tiny_positive ε |p.y| hε (abs_pos.mpr hy)
      let xq : ℝ := if p.x = 0 then t else p.x
      let yp : ℝ := (a - xq - 3 * t - t) / 2
      let yn : ℝ := (a - xq + 3 * t - t) / 2
      let qplus : Point3 := ⟨xq, yp, t⟩
      let qminus : Point3 := ⟨xq, yn, -t⟩
      have hxq : xq ≠ 0 := by
        dsimp [xq]
        split_ifs with hx
        · exact ne_of_gt ht
        · exact hx
      have hyp : yp ≠ 0 := by
        dsimp [yp, xq, W] at *
        rcases lt_or_gt_of_ne hy with hyneg | hypos
        · rw [abs_of_neg hyneg] at hty
          split_ifs with hx
          · linarith
          · linarith
        · rw [abs_of_pos hypos] at hty
          split_ifs with hx
          · linarith
          · linarith
      have hyn : yn ≠ 0 := by
        dsimp [yn, xq, W] at *
        rcases lt_or_gt_of_ne hy with hyneg | hypos
        · rw [abs_of_neg hyneg] at hty
          split_ifs with hx
          · linarith
          · linarith
        · rw [abs_of_pos hypos] at hty
          split_ifs with hx
          · linarith
          · linarith
      have hdp : distanceSquared p qplus < ε ^ 2 := by
        simp only [distanceSquared, qplus, hz]
        dsimp [yp, xq, W] at *
        split_ifs with hx
        · nlinarith
        · nlinarith
      have hdn : distanceSquared p qminus < ε ^ 2 := by
        simp only [distanceSquared, qminus, hz]
        dsimp [yn, xq, W] at *
        split_ifs with hx
        · nlinarith
        · nlinarith
      have hup_eq : u a qplus = xq * yp ^ 2 * t ^ 4 := by
        simp only [u, qplus]
        dsimp [yp]
        ring
      have hun_eq : u a qminus = -(xq * yn ^ 2 * t ^ 4) := by
        simp only [u, qminus]
        dsimp [yn]
        ring
      rcases lt_or_gt_of_ne hxq with hxneg | hxpos
      · refine ⟨qminus, qplus, hdn, ?_, hdp, ?_⟩
        · rw [hun_eq]
          have hm : xq * yn ^ 2 * t ^ 4 < 0 :=
            mul_neg_of_neg_of_pos
              (mul_neg_of_neg_of_pos hxneg (sq_pos_of_ne_zero hyn))
              (pow_pos ht _)
          linarith
        · rw [hup_eq]
          exact mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos hxneg (sq_pos_of_ne_zero hyp))
            (pow_pos ht _)
      · refine ⟨qplus, qminus, hdp, ?_, hdn, ?_⟩
        · rw [hup_eq]
          positivity
        · rw [hun_eq]
          have hm : 0 < xq * yn ^ 2 * t ^ 4 := by positivity
          linarith
  · obtain ⟨t, ht, htε, htW⟩ :=
      exists_tiny_positive ε |W| hε (abs_pos.mpr hW)
    let xq : ℝ := if p.x = 0 then t else p.x
    let yq : ℝ := if p.y = 0 then t else p.y
    let wp : ℝ := a - xq - 2 * yq - 3 * t
    let wn : ℝ := a - xq - 2 * yq + 3 * t
    let qplus : Point3 := ⟨xq, yq, t⟩
    let qminus : Point3 := ⟨xq, yq, -t⟩
    have hxq : xq ≠ 0 := by
      dsimp [xq]
      split_ifs with hx
      · exact ne_of_gt ht
      · exact hx
    have hyq : yq ≠ 0 := by
      dsimp [yq]
      split_ifs with hy
      · exact ne_of_gt ht
      · exact hy
    have hdx0 : 0 ≤ xq - p.x := by
      dsimp [xq]
      split_ifs with hx
      · simpa [hx] using ht.le
      · simp
    have hdxt : xq - p.x ≤ t := by
      dsimp [xq]
      split_ifs with hx
      · simp [hx]
      · linarith
    have hdy0 : 0 ≤ yq - p.y := by
      dsimp [yq]
      split_ifs with hy
      · simpa [hy] using ht.le
      · simp
    have hdyt : yq - p.y ≤ t := by
      dsimp [yq]
      split_ifs with hy
      · simp [hy]
      · linarith
    have hdp : distanceSquared p qplus < ε ^ 2 := by
      simp only [distanceSquared, qplus, hz]
      nlinarith [sq_nonneg (xq - p.x), sq_nonneg (yq - p.y)]
    have hdn : distanceSquared p qminus < ε ^ 2 := by
      simp only [distanceSquared, qminus, hz]
      nlinarith [sq_nonneg (xq - p.x), sq_nonneg (yq - p.y)]
    have hwpwn :
        (0 < wp ∧ 0 < wn) ∨ (wp < 0 ∧ wn < 0) := by
      rcases lt_or_gt_of_ne hW with hWneg | hWpos
      · right
        rw [abs_of_neg hWneg] at htW
        constructor
        · dsimp [wp, W] at *
          linarith
        · dsimp [wn, W] at *
          linarith
      · left
        rw [abs_of_pos hWpos] at htW
        constructor
        · dsimp [wp, W] at *
          linarith
        · dsimp [wn, W] at *
          linarith
    let B : ℝ := xq * yq ^ 2
    have hB : B ≠ 0 := by
      exact mul_ne_zero hxq (pow_ne_zero 2 hyq)
    have hup_eq : u a qplus = B * t ^ 3 * wp := by
      simp only [u, qplus, B, wp]
    have hun_eq : u a qminus = -(B * t ^ 3 * wn) := by
      simp only [u, qminus, B, wn]
      ring
    rcases lt_or_gt_of_ne hB with hBneg | hBpos
    · rcases hwpwn with ⟨hwp, hwn⟩ | ⟨hwp, hwn⟩
      · refine ⟨qminus, qplus, hdn, ?_, hdp, ?_⟩
        · rw [hun_eq]
          have hm : B * t ^ 3 * wn < 0 := by
            exact mul_neg_of_neg_of_pos
              (mul_neg_of_neg_of_pos hBneg (pow_pos ht _)) hwn
          linarith
        · rw [hup_eq]
          exact mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos hBneg (pow_pos ht _)) hwp
      · refine ⟨qplus, qminus, hdp, ?_, hdn, ?_⟩
        · rw [hup_eq]
          exact mul_pos_of_neg_of_neg
            (mul_neg_of_neg_of_pos hBneg (pow_pos ht _)) hwp
        · rw [hun_eq]
          have hm : 0 < B * t ^ 3 * wn :=
            mul_pos_of_neg_of_neg
              (mul_neg_of_neg_of_pos hBneg (pow_pos ht _)) hwn
          linarith
    · rcases hwpwn with ⟨hwp, hwn⟩ | ⟨hwp, hwn⟩
      · refine ⟨qplus, qminus, hdp, ?_, hdn, ?_⟩
        · rw [hup_eq]
          positivity
        · rw [hun_eq]
          have hm : 0 < B * t ^ 3 * wn := by positivity
          linarith
      · refine ⟨qminus, qplus, hdn, ?_, hdp, ?_⟩
        · rw [hun_eq]
          have hm : B * t ^ 3 * wn < 0 := by
            exact mul_neg_of_pos_of_neg
              (mul_pos hBpos (pow_pos ht _)) hwn
          linarith
        · rw [hup_eq]
          exact mul_neg_of_pos_of_neg
            (mul_pos hBpos (pow_pos ht _)) hwp

private theorem triple_dist_lt_of_distanceSquared_lt
    (p q : Point3) (ε : ℝ) (hε : 0 < ε)
    (h : distanceSquared p q < ε ^ 2) :
    dist (q.x, q.y, q.z) (p.x, p.y, p.z) < ε := by
  unfold distanceSquared at h
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [Real.dist_eq]
  rw [max_lt_iff, max_lt_iff]
  constructor
  · rw [abs_lt]
    constructor <;>
      nlinarith [sq_nonneg (q.y - p.y), sq_nonneg (q.z - p.z)]
  · constructor
    · rw [abs_lt]
      constructor <;>
        nlinarith [sq_nonneg (q.x - p.x), sq_nonneg (q.z - p.z)]
    · rw [abs_lt]
      constructor <;>
        nlinarith [sq_nonneg (q.x - p.x), sq_nonneg (q.y - p.y)]

private def nearbyCoefficient (a : ℝ) (r : ℝ × ℝ × ℝ) : ℝ :=
  r.1 * r.2.2 ^ 3 * (a - r.1 - 2 * r.2.1 - 3 * r.2.2)

private theorem exists_positive_coefficient_neighborhood
    (a : ℝ) (p : Point3)
    (hp : 0 < nearbyCoefficient a (p.x, p.y, p.z)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : Point3, distanceSquared p q < ε ^ 2 →
        0 < nearbyCoefficient a (q.x, q.y, q.z) := by
  have hcont : Continuous (nearbyCoefficient a) := by
    unfold nearbyCoefficient
    fun_prop
  have hopen : IsOpen {r | 0 < nearbyCoefficient a r} :=
    isOpen_lt continuous_const hcont
  obtain ⟨ε, hε, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) (p.x, p.y, p.z) hp
  refine ⟨ε, hε, ?_⟩
  intro q hq
  apply hball
  exact triple_dist_lt_of_distanceSquared_lt p q ε hε hq

private theorem exists_negative_coefficient_neighborhood
    (a : ℝ) (p : Point3)
    (hp : nearbyCoefficient a (p.x, p.y, p.z) < 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : Point3, distanceSquared p q < ε ^ 2 →
        nearbyCoefficient a (q.x, q.y, q.z) < 0 := by
  have hcont : Continuous (nearbyCoefficient a) := by
    unfold nearbyCoefficient
    fun_prop
  have hopen : IsOpen {r | nearbyCoefficient a r < 0} :=
    isOpen_lt hcont continuous_const
  obtain ⟨ε, hε, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) (p.x, p.y, p.z) hp
  refine ⟨ε, hε, ?_⟩
  intro q hq
  apply hball
  exact triple_dist_lt_of_distanceSquared_lt p q ε hε hq

theorem gap10 (a : ℝ) :
    ∀ p : Point3, p.y = 0 → 0 < coefficientOnYZero a p →
      u a p = 0 ∧ IsLocalMinimum a p := by
  intro p hy hc
  have hc' : 0 < nearbyCoefficient a (p.x, p.y, p.z) := by
    simpa only [nearbyCoefficient, coefficientOnYZero, hy, mul_zero, sub_zero] using hc
  obtain ⟨ε, hε, hsign⟩ :=
    exists_positive_coefficient_neighborhood a p hc'
  constructor
  · simp [u, hy]
  · refine ⟨ε, hε, ?_⟩
    intro q hq
    have hcoef := hsign q hq
    have huq :
        u a q = q.y ^ 2 * nearbyCoefficient a (q.x, q.y, q.z) := by
      unfold u nearbyCoefficient
      ring
    rw [show u a p = 0 by simp [u, hy], huq]
    exact mul_nonneg (sq_nonneg q.y) hcoef.le

theorem gap11 (a : ℝ) :
    ∀ p : Point3, p.y = 0 → coefficientOnYZero a p < 0 →
      u a p = 0 ∧ IsLocalMaximum a p := by
  intro p hy hc
  have hc' : nearbyCoefficient a (p.x, p.y, p.z) < 0 := by
    simpa only [nearbyCoefficient, coefficientOnYZero, hy, mul_zero, sub_zero] using hc
  obtain ⟨ε, hε, hsign⟩ :=
    exists_negative_coefficient_neighborhood a p hc'
  constructor
  · simp [u, hy]
  · refine ⟨ε, hε, ?_⟩
    intro q hq
    have hcoef := hsign q hq
    have huq :
        u a q = q.y ^ 2 * nearbyCoefficient a (q.x, q.y, q.z) := by
      unfold u nearbyCoefficient
      ring
    rw [show u a p = 0 by simp [u, hy], huq]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg q.y) hcoef.le

theorem gap12 (a : ℝ) :
    ∀ p : Point3, p.y = 0 → coefficientOnYZero a p = 0 →
      ¬ IsLocalMaximum a p ∧ ¬ IsLocalMinimum a p := by
  intro p hy hc
  by_cases hz : p.z = 0
  · exact gap9 a p hz
  have hz3ne : p.z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  let W : ℝ := a - p.x - 3 * p.z
  have hc' : p.x * p.z ^ 3 * W = 0 := by
    simpa only [coefficientOnYZero, W] using hc
  have hzero : u a p = 0 := by simp [u, hy]
  apply no_local_extrema_of_signed_points a p hzero
  intro ε hε
  by_cases hx : p.x = 0
  · by_cases hW : W = 0
    · obtain ⟨t, ht, htε, htt⟩ :=
        exists_tiny_positive ε ε hε hε
      let q₁ : Point3 := ⟨t, t, p.z⟩
      let q₂ : Point3 := ⟨-t, t, p.z⟩
      have hd₁ : distanceSquared p q₁ < ε ^ 2 := by
        simp only [distanceSquared, q₁, hx, hy]
        nlinarith
      have hd₂ : distanceSquared p q₂ < ε ^ 2 := by
        simp only [distanceSquared, q₂, hx, hy]
        nlinarith
      have hu₁ : u a q₁ = -3 * t ^ 4 * p.z ^ 3 := by
        simp only [u, q₁]
        have haeq : a = 3 * p.z := by
          dsimp [W] at hW
          linarith [hW, hx]
        rw [haeq]
        ring
      have hu₂ : u a q₂ = t ^ 4 * p.z ^ 3 := by
        simp only [u, q₂]
        have haeq : a = 3 * p.z := by
          dsimp [W] at hW
          linarith [hW, hx]
        rw [haeq]
        ring
      rcases lt_or_gt_of_ne hz with hzneg | hzpos
      · refine ⟨q₁, q₂, hd₁, ?_, hd₂, ?_⟩
        · rw [hu₁]
          have hm : t ^ 4 * p.z ^ 3 < 0 :=
            mul_neg_of_pos_of_neg (pow_pos ht _) (Odd.pow_neg (by decide) hzneg)
          linarith
        · rw [hu₂]
          exact mul_neg_of_pos_of_neg
            (pow_pos ht _) (Odd.pow_neg (by decide) hzneg)
      · refine ⟨q₂, q₁, hd₂, ?_, hd₁, ?_⟩
        · rw [hu₂]
          positivity
        · rw [hu₁]
          have hm : 0 < t ^ 4 * p.z ^ 3 := by positivity
          linarith
    · obtain ⟨t, ht, htε, htW⟩ :=
        exists_tiny_positive ε |W| hε (abs_pos.mpr hW)
      let wp : ℝ := W - 3 * t
      let wn : ℝ := W - t
      let qplus : Point3 := ⟨t, t, p.z⟩
      let qminus : Point3 := ⟨-t, t, p.z⟩
      have hdp : distanceSquared p qplus < ε ^ 2 := by
        simp only [distanceSquared, qplus, hx, hy]
        nlinarith
      have hdn : distanceSquared p qminus < ε ^ 2 := by
        simp only [distanceSquared, qminus, hx, hy]
        nlinarith
      have hww :
          (0 < wp ∧ 0 < wn) ∨ (wp < 0 ∧ wn < 0) := by
        rcases lt_or_gt_of_ne hW with hWneg | hWpos
        · right
          rw [abs_of_neg hWneg] at htW
          dsimp [wp, wn]
          constructor <;> linarith
        · left
          rw [abs_of_pos hWpos] at htW
          dsimp [wp, wn]
          constructor <;> linarith
      have hup_eq : u a qplus = t ^ 3 * p.z ^ 3 * wp := by
        simp only [u, qplus, wp]
        dsimp [W]
        rw [hx]
        ring
      have hun_eq : u a qminus = -(t ^ 3 * p.z ^ 3 * wn) := by
        simp only [u, qminus, wn]
        dsimp [W]
        rw [hx]
        ring
      have hzsign : p.z ^ 3 < 0 ∨ 0 < p.z ^ 3 := lt_or_gt_of_ne hz3ne
      rcases hzsign with hzneg | hzpos
      · rcases hww with ⟨hwp, hwn⟩ | ⟨hwp, hwn⟩
        · refine ⟨qminus, qplus, hdn, ?_, hdp, ?_⟩
          · rw [hun_eq]
            have hm : t ^ 3 * p.z ^ 3 * wn < 0 :=
              mul_neg_of_neg_of_pos
                (mul_neg_of_pos_of_neg (pow_pos ht _) hzneg) hwn
            linarith
          · rw [hup_eq]
            exact mul_neg_of_neg_of_pos
              (mul_neg_of_pos_of_neg (pow_pos ht _) hzneg) hwp
        · refine ⟨qplus, qminus, hdp, ?_, hdn, ?_⟩
          · rw [hup_eq]
            exact mul_pos_of_neg_of_neg
              (mul_neg_of_pos_of_neg (pow_pos ht _) hzneg) hwp
          · rw [hun_eq]
            have hm : 0 < t ^ 3 * p.z ^ 3 * wn :=
              mul_pos_of_neg_of_neg
                (mul_neg_of_pos_of_neg (pow_pos ht _) hzneg) hwn
            linarith
      · rcases hww with ⟨hwp, hwn⟩ | ⟨hwp, hwn⟩
        · refine ⟨qplus, qminus, hdp, ?_, hdn, ?_⟩
          · rw [hup_eq]
            positivity
          · rw [hun_eq]
            have hm : 0 < t ^ 3 * p.z ^ 3 * wn := by positivity
            linarith
        · refine ⟨qminus, qplus, hdn, ?_, hdp, ?_⟩
          · rw [hun_eq]
            have hm : t ^ 3 * p.z ^ 3 * wn < 0 :=
              mul_neg_of_pos_of_neg
                (mul_pos (pow_pos ht _) hzpos) hwn
            linarith
          · rw [hup_eq]
            exact mul_neg_of_pos_of_neg
              (mul_pos (pow_pos ht _) hzpos) hwp
  · have hW : W = 0 :=
      (mul_eq_zero.mp hc').resolve_left (mul_ne_zero hx hz3ne)
    obtain ⟨t, ht, htε, htx⟩ :=
      exists_tiny_positive ε |p.x| hε (abs_pos.mpr hx)
    let xp : ℝ := p.x - 3 * t
    let xn : ℝ := p.x - t
    let qplus : Point3 := ⟨xp, t, p.z⟩
    let qminus : Point3 := ⟨xn, t, p.z⟩
    have hxp_sign :
        (0 < xp ∧ 0 < xn) ∨ (xp < 0 ∧ xn < 0) := by
      rcases lt_or_gt_of_ne hx with hxneg | hxpos
      · right
        dsimp [xp, xn]
        constructor <;> linarith
      · left
        rw [abs_of_pos hxpos] at htx
        dsimp [xp, xn]
        constructor <;> linarith
    have hdp : distanceSquared p qplus < ε ^ 2 := by
      simp only [distanceSquared, qplus, xp, hy]
      nlinarith
    have hdn : distanceSquared p qminus < ε ^ 2 := by
      simp only [distanceSquared, qminus, xn, hy]
      nlinarith
    have hup_eq : u a qplus = xp * t ^ 3 * p.z ^ 3 := by
      simp only [u, qplus, xp]
      have haeq : a = p.x + 3 * p.z := by
        dsimp [W] at hW
        linarith
      rw [haeq]
      ring
    have hun_eq : u a qminus = -(xn * t ^ 3 * p.z ^ 3) := by
      simp only [u, qminus, xn]
      have haeq : a = p.x + 3 * p.z := by
        dsimp [W] at hW
        linarith
      rw [haeq]
      ring
    have hzsign : p.z ^ 3 < 0 ∨ 0 < p.z ^ 3 := lt_or_gt_of_ne hz3ne
    rcases hxp_sign with ⟨hxp, hxn⟩ | ⟨hxp, hxn⟩
    · rcases hzsign with hzneg | hzpos
      · refine ⟨qminus, qplus, hdn, ?_, hdp, ?_⟩
        · rw [hun_eq]
          have hm : xn * t ^ 3 * p.z ^ 3 < 0 :=
            mul_neg_of_pos_of_neg (mul_pos hxn (pow_pos ht _)) hzneg
          linarith
        · rw [hup_eq]
          exact mul_neg_of_pos_of_neg (mul_pos hxp (pow_pos ht _)) hzneg
      · refine ⟨qplus, qminus, hdp, ?_, hdn, ?_⟩
        · rw [hup_eq]
          positivity
        · rw [hun_eq]
          have hm : 0 < xn * t ^ 3 * p.z ^ 3 := by positivity
          linarith
    · rcases hzsign with hzneg | hzpos
      · refine ⟨qplus, qminus, hdp, ?_, hdn, ?_⟩
        · rw [hup_eq]
          exact mul_pos_of_neg_of_neg
            (mul_neg_of_neg_of_pos hxp (pow_pos ht _)) hzneg
        · rw [hun_eq]
          have hm : 0 < xn * t ^ 3 * p.z ^ 3 :=
            mul_pos_of_neg_of_neg
              (mul_neg_of_neg_of_pos hxn (pow_pos ht _)) hzneg
          linarith
      · refine ⟨qminus, qplus, hdn, ?_, hdp, ?_⟩
        · rw [hun_eq]
          have hm : xn * t ^ 3 * p.z ^ 3 < 0 :=
            mul_neg_of_neg_of_pos
              (mul_neg_of_neg_of_pos hxn (pow_pos ht _)) hzpos
          linarith
        · rw [hup_eq]
          exact mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos hxp (pow_pos ht _)) hzpos

theorem gap13 (a : ℝ) :
    ∀ v : Point3,
      secondVariationAtP₀ a v =
        -(a ^ 5 / (7 : ℝ) ^ 5) *
          ((v.x + 2 * v.y + 3 * v.z) ^ 2 +
            v.x ^ 2 + 2 * v.y ^ 2 + 3 * v.z ^ 2) := by
  intro v
  rfl

private theorem coordinate_nonzero_of_point_ne_zero
    (v : Point3) (hv : v ≠ ⟨0, 0, 0⟩) :
    v.x ≠ 0 ∨ v.y ≠ 0 ∨ v.z ≠ 0 := by
  by_contra h
  push_neg at h
  apply hv
  cases v
  simp_all

theorem gap14 (a : ℝ) (ha : 0 < a) :
    ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ →
      -(a ^ 5 / (7 : ℝ) ^ 5) *
        ((v.x + 2 * v.y + 3 * v.z) ^ 2 +
          v.x ^ 2 + 2 * v.y ^ 2 + 3 * v.z ^ 2) < 0 := by
  intro v hv
  have hcoord := coordinate_nonzero_of_point_ne_zero v hv
  have hsum :
      0 < v.x ^ 2 + 2 * v.y ^ 2 + 3 * v.z ^ 2 := by
    rcases hcoord with hx | hy | hz
    · have hx2 : 0 < v.x ^ 2 := sq_pos_of_ne_zero hx
      positivity
    · have hy2 : 0 < v.y ^ 2 := sq_pos_of_ne_zero hy
      positivity
    · have hz2 : 0 < v.z ^ 2 := sq_pos_of_ne_zero hz
      positivity
  have hbig :
      0 < (v.x + 2 * v.y + 3 * v.z) ^ 2 +
        v.x ^ 2 + 2 * v.y ^ 2 + 3 * v.z ^ 2 := by
    nlinarith [sq_nonneg (v.x + 2 * v.y + 3 * v.z)]
  have hcoef : 0 < a ^ 5 / (7 : ℝ) ^ 5 := by positivity
  nlinarith

theorem gap15 (a : ℝ) (ha : 0 < a) :
    NegativeDefiniteAtP₀ a := by
  intro v hv
  rw [gap13 a v]
  exact gap14 a ha v hv

private theorem seven_amgm_strict
    (a x y z w : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    (hsum : x + 2 * y + 3 * z + w = a)
    (hneq : x ≠ a / 7 ∨ y ≠ a / 7 ∨ z ≠ a / 7) :
    x * y ^ 2 * z ^ 3 * w < (a / 7) ^ 7 := by
  let vals : Fin 7 → ℝ := ![x, y, y, z, z, z, w]
  let weights : Fin 7 → ℝ := fun _ => 1 / 7
  have hweights_pos : ∀ i ∈ Finset.univ, 0 < weights i := by
    intro i hi
    simp [weights]
  have hweights_sum : ∑ i ∈ Finset.univ, weights i = 1 := by
    simp [weights]
  have hvals_nonneg : ∀ i ∈ Finset.univ, 0 ≤ vals i := by
    intro i hi
    fin_cases i <;> simp [vals, hx.le, hy.le, hz.le, hw.le]
  have hpair :
      ∃ j ∈ Finset.univ, ∃ k ∈ Finset.univ, vals j ≠ vals k := by
    simp only [Finset.mem_univ, true_and]
    by_cases hxy : x = y
    · by_cases hyz : y = z
      · by_cases hzw : z = w
        · exfalso
          rcases hneq with hnx | hny | hnz
          · apply hnx
            linarith
          · apply hny
            linarith
          · apply hnz
            linarith
        · exact ⟨3, 6, by simpa [vals] using hzw⟩
      · exact ⟨1, 3, by simpa [vals] using hyz⟩
    · exact ⟨0, 1, by simpa [vals] using hxy⟩
  have hgm :=
    (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos
      Finset.univ weights vals hweights_pos hweights_sum hvals_nonneg).2 hpair
  have hleft :
      ∏ i ∈ Finset.univ, vals i ^ weights i =
        (x * y ^ 2 * z ^ 3 * w) ^ (1 / 7 : ℝ) := by
    rw [Real.finset_prod_rpow Finset.univ vals hvals_nonneg]
    congr 1
    dsimp [vals]
    simp [Fin.prod_univ_succ]
    ring
  have hright :
      ∑ i ∈ Finset.univ, weights i * vals i = a / 7 := by
    dsimp [weights, vals]
    simp [Fin.sum_univ_succ]
    linarith
  rw [hleft, hright] at hgm
  have hP : 0 ≤ x * y ^ 2 * z ^ 3 * w := by positivity
  have hroot : 0 ≤ (x * y ^ 2 * z ^ 3 * w) ^ (1 / 7 : ℝ) :=
    Real.rpow_nonneg hP _
  have hpow :=
    pow_lt_pow_left₀ hgm hroot (by norm_num : (7 : ℕ) ≠ 0)
  rw [show (1 / 7 : ℝ) = ((7 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_natCast_pow hP (by norm_num : (7 : ℕ) ≠ 0)] at hpow
  exact hpow

theorem gap16 (a : ℝ) (ha : 0 < a) :
    IsStrictLocalMaximum a (p₀ a) := by
  refine ⟨a / 100, by positivity, ?_⟩
  intro q hq hdist
  have hd :
      (q.x - a / 7) ^ 2 + (q.y - a / 7) ^ 2 +
          (q.z - a / 7) ^ 2 < (a / 100) ^ 2 := by
    simpa only [distanceSquared, p₀] using hdist
  have hdx2 : (q.x - a / 7) ^ 2 < (a / 100) ^ 2 := by
    nlinarith [sq_nonneg (q.y - a / 7), sq_nonneg (q.z - a / 7)]
  have hdy2 : (q.y - a / 7) ^ 2 < (a / 100) ^ 2 := by
    nlinarith [sq_nonneg (q.x - a / 7), sq_nonneg (q.z - a / 7)]
  have hdz2 : (q.z - a / 7) ^ 2 < (a / 100) ^ 2 := by
    nlinarith [sq_nonneg (q.x - a / 7), sq_nonneg (q.y - a / 7)]
  have hε : 0 < a / 100 := by positivity
  have hdxlo : -(a / 100) < q.x - a / 7 := by nlinarith
  have hdxhi : q.x - a / 7 < a / 100 := by nlinarith
  have hdylo : -(a / 100) < q.y - a / 7 := by nlinarith
  have hdyhi : q.y - a / 7 < a / 100 := by nlinarith
  have hdzlo : -(a / 100) < q.z - a / 7 := by nlinarith
  have hdzhi : q.z - a / 7 < a / 100 := by nlinarith
  have hx : 0 < q.x := by linarith
  have hy : 0 < q.y := by linarith
  have hz : 0 < q.z := by linarith
  let w : ℝ := a - q.x - 2 * q.y - 3 * q.z
  have hw : 0 < w := by
    dsimp [w]
    linarith
  have hsum : q.x + 2 * q.y + 3 * q.z + w = a := by
    dsimp [w]
    ring
  have hneq :
      q.x ≠ a / 7 ∨ q.y ≠ a / 7 ∨ q.z ≠ a / 7 := by
    by_contra h
    push_neg at h
    apply hq
    cases q with
    | mk x y z =>
        simp_all only [p₀, Point3.mk.injEq]
  have hamgm :=
    seven_amgm_strict a q.x q.y q.z w hx hy hz hw hsum hneq
  rw [show u a (p₀ a) = a ^ 7 / (7 : ℝ) ^ 7 by
    unfold u p₀
    ring]
  unfold u
  convert hamgm using 1 <;> dsimp [w] <;> ring

theorem gap17 (a : ℝ) :
    u a (p₀ a) = a ^ 7 / (7 : ℝ) ^ 7 := by
  unfold u p₀
  ring

theorem gap18 (a : ℝ) (ha : 0 < a) :
    p₀ a ∈ localMaximumPoints a := by
  rcases gap16 a ha with ⟨ε, hε, hstrict⟩
  refine ⟨ε, hε, ?_⟩
  intro q hdist
  by_cases hq : q = p₀ a
  · subst q
    exact le_rfl
  · exact (hstrict q hq hdist).le

end

end ProofGap.Exercise3645
