import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise4407

noncomputable section

open Filter

abbrev Vec3 := ℝ × ℝ × ℝ

def add (a b : Vec3) : Vec3 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def displacement (M₀ M₁ : Vec3) : Vec3 :=
  (M₁.1 - M₀.1, M₁.2.1 - M₀.2.1, M₁.2.2 - M₀.2.2)

def scale (t : ℝ) (v : Vec3) : Vec3 :=
  (t * v.1, t * v.2.1, t * v.2.2)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def distance (M₀ M₁ : Vec3) : ℝ :=
  norm3 (displacement M₀ M₁)

def levelChange (u : Vec3 → ℝ) (M₀ M₁ : Vec3) : ℝ :=
  u M₁ - u M₀

def linearizedChange (gradient : Vec3 → Vec3) (M₀ M₁ : Vec3) : ℝ :=
  dot (gradient M₀) (displacement M₀ M₁)

def approximationError (u : Vec3 → ℝ) (gradient : Vec3 → Vec3)
    (M₀ M₁ : Vec3) : ℝ :=
  levelChange u M₀ M₁ - linearizedChange gradient M₀ M₁

def RepresentsDerivative (u : Vec3 → ℝ) (gradient : Vec3 → Vec3)
    (M₀ : Vec3) : Prop :=
  ∀ v, fderiv ℝ u M₀ v = dot (gradient M₀) v

def IsFirstOrderApproximation (u : Vec3 → ℝ)
    (gradient : Vec3 → Vec3) (M₀ : Vec3) : Prop :=
  Tendsto
    (fun M₁ =>
      approximationError u gradient M₀ M₁ / distance M₀ M₁)
    (nhdsWithin M₀ {M₀}ᶜ) (nhds 0)

def IsNormalDisplacement (gradient : Vec3 → Vec3)
    (M₀ M₁ : Vec3) : Prop :=
  ∃ t : ℝ, displacement M₀ M₁ = scale t (gradient M₀)

private theorem norm3_nonneg_private (v : Vec3) : 0 ≤ norm3 v := by
  exact Real.sqrt_nonneg _

private theorem norm_le_norm3_private (v : Vec3) : ‖v‖ ≤ norm3 v := by
  rcases v with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  let s : ℝ := x ^ 2 + y ^ 2 + z ^ 2
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hsqrt : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs
  have hsqrt_nonneg : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hx2 : |x| ^ 2 = x ^ 2 := by simp
  have hy2 : |y| ^ 2 = y ^ 2 := by simp
  have hz2 : |z| ^ 2 = z ^ 2 := by simp
  have hx : |x| ≤ Real.sqrt s := by
    nlinarith [sq_nonneg y, sq_nonneg z, abs_nonneg x]
  have hy : |y| ≤ Real.sqrt s := by
    nlinarith [sq_nonneg x, sq_nonneg z, abs_nonneg y]
  have hz : |z| ≤ Real.sqrt s := by
    nlinarith [sq_nonneg x, sq_nonneg y, abs_nonneg z]
  change max ‖x‖ (max ‖y‖ ‖z‖) ≤
    Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)
  simpa [Real.norm_eq_abs, s] using max_le hx (max_le hy hz)

private theorem distance_pos_of_ne_private {M₀ M₁ : Vec3}
    (hne : M₁ ≠ M₀) : 0 < distance M₀ M₁ := by
  have hd : displacement M₀ M₁ ≠ 0 := by
    rw [show displacement M₀ M₁ = M₁ - M₀ by rfl]
    exact sub_ne_zero.mpr hne
  have hn : 0 < ‖displacement M₀ M₁‖ := norm_pos_iff.mpr hd
  unfold distance
  exact lt_of_lt_of_le hn (norm_le_norm3_private (displacement M₀ M₁))

private theorem dot_scale_self_private (t : ℝ) (v : Vec3) :
    dot v (scale t v) = t * dot v v := by
  rcases v with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  simp [dot, scale]
  ring

private theorem dot_self_private (v : Vec3) :
    dot v v = norm3 v ^ 2 := by
  rcases v with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  simp only [dot, norm3]
  rw [Real.sq_sqrt (by positivity : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2)]
  ring

private theorem norm3_scale_private (t : ℝ) (v : Vec3) :
    norm3 (scale t v) = |t| * norm3 v := by
  rcases v with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  change Real.sqrt ((t * x) ^ 2 + (t * y) ^ 2 + (t * z) ^ 2) =
    |t| * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)
  rw [show (t * x) ^ 2 + (t * y) ^ 2 + (t * z) ^ 2 =
      t ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) by ring]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

private theorem div_le_div_same_pos_private {a b c : ℝ} (hc : 0 < c) :
    a / c ≤ b / c ↔ a ≤ b := by
  constructor
  · intro h
    have hmul : a * c ≤ b * c :=
      (div_le_div_iff₀ hc hc).1 h
    by_contra hle
    have hba : b < a := lt_of_not_ge hle
    have hmul' : b * c < a * c :=
      mul_lt_mul_of_pos_right hba hc
    exact (not_lt_of_ge hmul) hmul'
  · intro h
    apply (div_le_div_iff₀ hc hc).2
    exact mul_le_mul_of_nonneg_right h (le_of_lt hc)

theorem gap1 (u : Vec3 → ℝ) (M₀ : Vec3) (c : ℝ)
    (hLevel : u M₀ = c) :
    u M₀ = c := by
  exact hLevel

theorem gap2 (u : Vec3 → ℝ) (M₀ M₁ : Vec3) (c : ℝ)
    (hLevel : u M₀ = c) :
    u M₁ = c + levelChange u M₀ M₁ := by
  rw [levelChange, hLevel]
  ring

theorem gap3 (M₀ M₁ : Vec3) :
    distance M₀ M₁ = norm3 (displacement M₀ M₁) := by
  rfl

theorem gap4 (u : Vec3 → ℝ) (M₀ M₁ : Vec3) :
    levelChange u M₀ M₁ = u M₁ - u M₀ := by
  rfl

theorem gap5 (u : Vec3 → ℝ) (gradient : Vec3 → Vec3) (M₀ : Vec3)
    (hDiff : DifferentiableAt ℝ u M₀)
    (hGradient : RepresentsDerivative u gradient M₀) :
    IsFirstOrderApproximation u gradient M₀ := by
  unfold IsFirstOrderApproximation
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hderiv : HasFDerivAt u (fderiv ℝ u M₀) M₀ :=
    hDiff.hasFDerivAt
  have hsmall :
      ∀ᶠ M₁ in nhds M₀,
        ‖u M₁ - u M₀ - fderiv ℝ u M₀ (M₁ - M₀)‖ ≤
          (ε / 2) * ‖M₁ - M₀‖ :=
    hderiv.isLittleO.def (by linarith)
  have hsmallWithin :
      ∀ᶠ M₁ in nhdsWithin M₀ {M₀}ᶜ,
        ‖u M₁ - u M₀ - fderiv ℝ u M₀ (M₁ - M₀)‖ ≤
          (ε / 2) * ‖M₁ - M₀‖ := by
    exact hsmall.filter_mono inf_le_left
  filter_upwards [hsmallWithin, self_mem_nhdsWithin] with M₁ hbound hmem
  have hne : M₁ ≠ M₀ := by
    simpa using hmem
  have hd : 0 < distance M₀ M₁ := distance_pos_of_ne_private hne
  have hdisp : M₁ - M₀ = displacement M₀ M₁ := by
    rfl
  have hlinear :
      fderiv ℝ u M₀ (M₁ - M₀) =
        dot (gradient M₀) (displacement M₀ M₁) := by
    calc
      fderiv ℝ u M₀ (M₁ - M₀) =
          dot (gradient M₀) (M₁ - M₀) := hGradient (M₁ - M₀)
      _ = dot (gradient M₀) (displacement M₀ M₁) := by
        rw [hdisp]
  rw [hlinear, hdisp] at hbound
  have hbound' :
      |approximationError u gradient M₀ M₁| ≤
        (ε / 2) * ‖displacement M₀ M₁‖ := by
    simpa only [approximationError, levelChange, linearizedChange,
      Real.norm_eq_abs] using hbound
  have hstrict :
      |approximationError u gradient M₀ M₁| <
        ε * distance M₀ M₁ := by
    calc
      |approximationError u gradient M₀ M₁| ≤
          (ε / 2) * ‖displacement M₀ M₁‖ := hbound'
      _ ≤ (ε / 2) * distance M₀ M₁ := by
        apply mul_le_mul_of_nonneg_left
        · simpa [distance] using
            norm_le_norm3_private (displacement M₀ M₁)
        · linarith
      _ < ε * distance M₀ M₁ := by
        nlinarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hd]
  exact (div_lt_iff₀ hd).2 hstrict

theorem gap6 (gradient : Vec3 → Vec3) (M₀ M₁ : Vec3) :
    linearizedChange gradient M₀ M₁ =
      dot (gradient M₀) (displacement M₀ M₁) := by
  rfl

theorem gap7 (gradient : Vec3 → Vec3) (M₀ M₁ : Vec3)
    (hNormal : IsNormalDisplacement gradient M₀ M₁) :
    |linearizedChange gradient M₀ M₁| =
      norm3 (gradient M₀) * distance M₀ M₁ := by
  rcases hNormal with ⟨t, ht⟩
  rw [linearizedChange, distance, ht, dot_scale_self_private,
    dot_self_private, norm3_scale_private]
  rw [abs_mul, abs_of_nonneg (sq_nonneg (norm3 (gradient M₀)))]
  ring

theorem gap8 (u : Vec3 → ℝ) (gradient : Vec3 → Vec3)
    (M₀ M₁ : Vec3) (ε : ℝ)
    (hGradient : 0 < norm3 (gradient M₀))
    (hNormal : IsNormalDisplacement gradient M₀ M₁)
    (hApprox :
      |approximationError u gradient M₀ M₁| ≤
        ε * distance M₀ M₁) :
    |distance M₀ M₁ -
        |levelChange u M₀ M₁| / norm3 (gradient M₀)| ≤
      ε * distance M₀ M₁ / norm3 (gradient M₀) := by
  have hg0 : norm3 (gradient M₀) ≠ 0 := ne_of_gt hGradient
  have hlin := gap7 gradient M₀ M₁ hNormal
  have hdrepr :
      distance M₀ M₁ =
        |linearizedChange gradient M₀ M₁| / norm3 (gradient M₀) := by
    symm
    apply (div_eq_iff hg0).2
    rw [hlin]
    ring
  have hre :
      abs (abs (linearizedChange gradient M₀ M₁) -
        abs (levelChange u M₀ M₁)) ≤
        abs (approximationError u gradient M₀ M₁) := by
    calc
      abs (abs (linearizedChange gradient M₀ M₁) -
          abs (levelChange u M₀ M₁)) ≤
          abs (linearizedChange gradient M₀ M₁ -
            levelChange u M₀ M₁) :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = abs (approximationError u gradient M₀ M₁) := by
        rw [abs_sub_comm]
        rfl
  calc
    |distance M₀ M₁ -
        |levelChange u M₀ M₁| / norm3 (gradient M₀)| =
        abs ((abs (linearizedChange gradient M₀ M₁) -
            abs (levelChange u M₀ M₁)) / norm3 (gradient M₀)) := by
      rw [hdrepr, sub_div]
    _ = abs (abs (linearizedChange gradient M₀ M₁) -
          abs (levelChange u M₀ M₁)) / norm3 (gradient M₀) := by
      rw [abs_div, abs_of_pos hGradient]
    _ ≤ abs (approximationError u gradient M₀ M₁) /
          norm3 (gradient M₀) :=
      (div_le_div_same_pos_private hGradient).2 hre
    _ ≤ ε * distance M₀ M₁ / norm3 (gradient M₀) :=
      (div_le_div_same_pos_private hGradient).2 hApprox

end

end ProofGap.Exercise4407
