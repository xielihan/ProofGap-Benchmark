import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3585

noncomputable section

open Filter Topology

structure Point2 where
  x : ℝ
  y : ℝ

def powerFunction (p : Point2) : ℝ :=
  p.x ^ p.y

def partialX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  deriv (fun t => f ⟨t, p.y⟩) p.x

def partialY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  deriv (fun t => f ⟨p.x, t⟩) p.y

def partialXX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialX (partialX f) p

def partialXY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialX f) p

def partialYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialY f) p

def partialXXX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialX (partialXX f) p

def partialXXY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialXX f) p

def partialXYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialXY f) p

def partialYYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialYY f) p

def quadraticTaylorAtOne (p : Point2) : ℝ :=
  1 + (p.x - 1) + (p.x - 1) * (p.y - 1)

def segmentPoint (p : Point2) (theta : ℝ) : Point2 :=
  ⟨1 + theta * (p.x - 1), 1 + theta * (p.y - 1)⟩

def thirdDirectionalTerm (p : Point2) (h k : ℝ) : ℝ :=
  (1 / 6 : ℝ) *
    (p.y * (p.y - 1) * (p.y - 2) * p.x ^ (p.y - 3) * h ^ 3 +
      3 * ((2 * p.y - 1) * p.x ^ (p.y - 2) +
        p.y * (p.y - 1) * p.x ^ (p.y - 2) * Real.log p.x) *
        h ^ 2 * k +
      3 * (p.y * p.x ^ (p.y - 1) * (Real.log p.x) ^ 2 +
        2 * p.x ^ (p.y - 1) * Real.log p.x) * h * k ^ 2 +
      p.x ^ p.y * (Real.log p.x) ^ 3 * k ^ 3)

def xIncrement (p : Point2) : ℝ :=
  p.x - 1

def yIncrement (p : Point2) : ℝ :=
  p.y - 1

theorem gap1 :
    ∀ p : Point2, 0 < p.x →
      partialX powerFunction p = p.y * p.x ^ (p.y - 1) := by
  intro p hp
  unfold partialX powerFunction
  exact Real.deriv_rpow_const p.x p.y

theorem gap2 :
    ∀ p : Point2, 0 < p.x →
      partialY powerFunction p = p.x ^ p.y * Real.log p.x := by
  intro p hp
  unfold partialY powerFunction
  have h := (hasDerivAt_id p.y).const_rpow hp
  simpa [id, mul_comm] using h.deriv

theorem gap3 :
    ∀ p : Point2, 0 < p.x →
      partialXX powerFunction p =
        p.y * (p.y - 1) * p.x ^ (p.y - 2) := by
  intro p hp
  change deriv (fun t => partialX powerFunction ⟨t, p.y⟩) p.x = _
  have heq :
      (fun t => partialX powerFunction ⟨t, p.y⟩) =ᶠ[nhds p.x]
        (fun t => p.y * t ^ (p.y - 1)) := by
    filter_upwards [eventually_gt_nhds hp] with t ht
    exact gap1 ⟨t, p.y⟩ ht
  have hpow :=
    Real.hasDerivAt_rpow_const
      (p := p.y - 1) (Or.inl hp.ne')
  have hderiv := hpow.const_mul p.y
  rw [heq.deriv_eq]
  convert hderiv.deriv using 1 <;> ring

theorem gap4 :
    ∀ p : Point2, 0 < p.x →
      partialXY powerFunction p =
        p.x ^ (p.y - 1) +
          p.y * p.x ^ (p.y - 1) * Real.log p.x := by
  intro p hp
  change deriv (fun t => partialX powerFunction ⟨p.x, t⟩) p.y = _
  have heq :
      (fun t => partialX powerFunction ⟨p.x, t⟩) =
        (fun t => t * p.x ^ (t - 1)) := by
    funext t
    exact gap1 ⟨p.x, t⟩ hp
  have hexp : HasDerivAt (fun t : ℝ => t - 1) 1 p.y := by
    simpa using (hasDerivAt_id p.y).sub_const 1
  have hpow := hexp.const_rpow hp
  have hderiv := (hasDerivAt_id p.y).mul hpow
  rw [heq]
  convert hderiv.deriv using 1 <;> simp [id] <;> ring

theorem gap5 :
    ∀ p : Point2, 0 < p.x →
      partialYY powerFunction p =
        p.x ^ p.y * (Real.log p.x) ^ 2 := by
  intro p hp
  change deriv (fun t => partialY powerFunction ⟨p.x, t⟩) p.y = _
  have heq :
      (fun t => partialY powerFunction ⟨p.x, t⟩) =
        (fun t => p.x ^ t * Real.log p.x) := by
    funext t
    exact gap2 ⟨p.x, t⟩ hp
  have hpow := (hasDerivAt_id p.y).const_rpow hp
  have hderiv := hpow.mul_const (Real.log p.x)
  rw [heq]
  convert hderiv.deriv using 1 <;> simp [id] <;> ring

theorem gap6 :
    ∀ p : Point2, 0 < p.x →
      partialXXX powerFunction p =
        p.y * (p.y - 1) * (p.y - 2) * p.x ^ (p.y - 3) := by
  intro p hp
  change deriv (fun t => partialXX powerFunction ⟨t, p.y⟩) p.x = _
  have heq :
      (fun t => partialXX powerFunction ⟨t, p.y⟩) =ᶠ[nhds p.x]
        (fun t => p.y * (p.y - 1) * t ^ (p.y - 2)) := by
    filter_upwards [eventually_gt_nhds hp] with t ht
    exact gap3 ⟨t, p.y⟩ ht
  have hpow :=
    Real.hasDerivAt_rpow_const
      (p := p.y - 2) (Or.inl hp.ne')
  have hderiv := hpow.const_mul (p.y * (p.y - 1))
  rw [heq.deriv_eq]
  convert hderiv.deriv using 1 <;> ring

theorem gap7 :
    ∀ p : Point2, 0 < p.x →
      partialYYY powerFunction p =
        p.x ^ p.y * (Real.log p.x) ^ 3 := by
  intro p hp
  change deriv (fun t => partialYY powerFunction ⟨p.x, t⟩) p.y = _
  have heq :
      (fun t => partialYY powerFunction ⟨p.x, t⟩) =
        (fun t => p.x ^ t * (Real.log p.x) ^ 2) := by
    funext t
    exact gap5 ⟨p.x, t⟩ hp
  have hpow := (hasDerivAt_id p.y).const_rpow hp
  have hderiv := hpow.mul_const ((Real.log p.x) ^ 2)
  rw [heq]
  convert hderiv.deriv using 1 <;> simp [id] <;> ring

theorem gap8 :
    ∀ p : Point2, 0 < p.x →
      partialXXY powerFunction p =
        (2 * p.y - 1) * p.x ^ (p.y - 2) +
          p.y * (p.y - 1) * p.x ^ (p.y - 2) * Real.log p.x := by
  intro p hp
  change deriv (fun t => partialXX powerFunction ⟨p.x, t⟩) p.y = _
  have heq :
      (fun t => partialXX powerFunction ⟨p.x, t⟩) =
        (fun t => (t * (t - 1)) * p.x ^ (t - 2)) := by
    funext t
    simpa [mul_assoc] using gap3 ⟨p.x, t⟩ hp
  have hpoly :
      HasDerivAt (fun t : ℝ => t * (t - 1)) (2 * p.y - 1) p.y := by
    convert (hasDerivAt_id p.y).mul
      ((hasDerivAt_id p.y).sub_const 1) using 1 <;>
      simp [id] <;> ring
  have hexp : HasDerivAt (fun t : ℝ => t - 2) 1 p.y := by
    simpa using (hasDerivAt_id p.y).sub_const 2
  have hpow := hexp.const_rpow hp
  have hderiv := hpoly.mul hpow
  rw [heq]
  convert hderiv.deriv using 1 <;> simp [id] <;> ring

theorem gap9 :
    ∀ p : Point2, 0 < p.x →
      partialXYY powerFunction p =
        p.y * p.x ^ (p.y - 1) * (Real.log p.x) ^ 2 +
          2 * p.x ^ (p.y - 1) * Real.log p.x := by
  intro p hp
  change deriv (fun t => partialXY powerFunction ⟨p.x, t⟩) p.y = _
  have heq :
      (fun t => partialXY powerFunction ⟨p.x, t⟩) =
        (fun t => p.x ^ (t - 1) +
          t * p.x ^ (t - 1) * Real.log p.x) := by
    funext t
    exact gap4 ⟨p.x, t⟩ hp
  have hexp : HasDerivAt (fun t : ℝ => t - 1) 1 p.y := by
    simpa using (hasDerivAt_id p.y).sub_const 1
  have hpow := hexp.const_rpow hp
  have hsecond :=
    ((hasDerivAt_id p.y).mul hpow).mul_const (Real.log p.x)
  have hderiv := hpow.add hsecond
  rw [heq]
  convert hderiv.deriv using 1 <;> simp [id] <;> ring

theorem gap10 :
    ∀ p : Point2, 0 < p.x →
      ∃ theta ∈ Set.Ioo (0 : ℝ) 1,
        powerFunction p =
          quadraticTaylorAtOne p +
            thirdDirectionalTerm (segmentPoint p theta)
              (p.x - 1) (p.y - 1) := by
  intro p hp
  let h : ℝ := p.x - 1
  let k : ℝ := p.y - 1
  let X : ℝ → ℝ := fun t => 1 + t * h
  let Y : ℝ → ℝ := fun t => 1 + t * k
  let g : ℝ → ℝ := fun t => X t ^ Y t
  let ell : ℝ → ℝ := fun t =>
    k * Real.log (X t) + Y t * h / X t
  let mell : ℝ → ℝ := fun t =>
    2 * k * h / X t - Y t * h ^ 2 / X t ^ 2
  let nell : ℝ → ℝ := fun t =>
    -3 * k * h ^ 2 / X t ^ 2 + 2 * Y t * h ^ 3 / X t ^ 3
  let q1 : ℝ → ℝ := fun t => g t * ell t
  let q2 : ℝ → ℝ := fun t => g t * (ell t ^ 2 + mell t)
  let q3 : ℝ → ℝ := fun t =>
    g t * (ell t ^ 3 + 3 * ell t * mell t + nell t)
  have hXderiv (t : ℝ) : HasDerivAt X h t := by
    dsimp [X]
    convert (hasDerivAt_const t 1).add
      ((hasDerivAt_id t).mul_const h) using 1 <;> simp
  have hYderiv (t : ℝ) : HasDerivAt Y k t := by
    dsimp [Y]
    convert (hasDerivAt_const t 1).add
      ((hasDerivAt_id t).mul_const k) using 1 <;> simp
  have hg1 (t : ℝ) (ht : 0 < X t) : HasDerivAt g (q1 t) t := by
    have hr := Real.rpow_sub_one ht.ne' (Y t)
    convert (hXderiv t).rpow (hYderiv t) ht using 1
    dsimp [g, q1, ell]
    rw [hr]
    field_simp [ht.ne']
    ring
  have hmell (t : ℝ) (ht : 0 < X t) :
      HasDerivAt ell (mell t) t := by
    have hfirst :=
      ((hXderiv t).log ht.ne').const_mul k
    have hsecond :=
      ((hYderiv t).mul_const h).div (hXderiv t) ht.ne'
    dsimp [ell, mell]
    convert hfirst.add hsecond using 1 <;>
      field_simp [ht.ne'] <;> ring
  have hnell (t : ℝ) (ht : 0 < X t) :
      HasDerivAt mell (nell t) t := by
    have hfirst :=
      (hasDerivAt_const t (2 * k * h)).div (hXderiv t) ht.ne'
    have hsecond :=
      ((hYderiv t).mul_const (h ^ 2)).div
        ((hXderiv t).pow 2) (pow_ne_zero 2 ht.ne')
    dsimp [mell, nell]
    convert hfirst.sub hsecond using 1 <;>
      try simp only [Pi.pow_apply] <;>
      field_simp [ht.ne'] <;> ring
  have hq1 (t : ℝ) (ht : 0 < X t) :
      HasDerivAt q1 (q2 t) t := by
    dsimp [q1, q2]
    convert (hg1 t ht).mul (hmell t ht) using 1 <;> ring
  have hq2 (t : ℝ) (ht : 0 < X t) :
      HasDerivAt q2 (q3 t) t := by
    dsimp [q1, q2, q3]
    convert (hg1 t ht).mul (((hmell t ht).pow 2).add (hnell t ht))
      using 1
    dsimp [q1]
    norm_num
    ring
  have hXcont : Continuous X := by
    dsimp [X]
    fun_prop
  have hi1 (t : ℝ) (ht : 0 < X t) :
      iteratedDeriv 1 g t = q1 t := by
    rw [iteratedDeriv_one]
    exact (hg1 t ht).deriv
  have hi2 (t : ℝ) (ht : 0 < X t) :
      iteratedDeriv 2 g t = q2 t := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
    have hpos : ∀ᶠ u in 𝓝 t, 0 < X u :=
      hXcont.continuousAt.eventually (Ioi_mem_nhds ht)
    have heq : iteratedDeriv 1 g =ᶠ[𝓝 t] q1 := by
      filter_upwards [hpos] with u hu
      exact hi1 u hu
    rw [heq.deriv_eq]
    exact (hq1 t ht).deriv
  have hi3 (t : ℝ) (ht : 0 < X t) :
      iteratedDeriv 3 g t = q3 t := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ]
    have hpos : ∀ᶠ u in 𝓝 t, 0 < X u :=
      hXcont.continuousAt.eventually (Ioi_mem_nhds ht)
    have heq : iteratedDeriv 2 g =ᶠ[𝓝 t] q2 := by
      filter_upwards [hpos] with u hu
      exact hi2 u hu
    rw [heq.deriv_eq]
    exact (hq2 t ht).deriv
  have hXpos (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < X t := by
    by_cases hpx : 1 ≤ p.x
    · have hmul : 0 ≤ t * (p.x - 1) :=
        mul_nonneg ht.1 (sub_nonneg.mpr hpx)
      dsimp [X, h]
      linarith
    · have hmul : 0 ≤ (1 - t) * (1 - p.x) :=
        mul_nonneg (sub_nonneg.mpr ht.2)
          (sub_nonneg.mpr (le_of_not_ge hpx))
      dsimp [X, h]
      nlinarith
  have hgdiff : ContDiffOn ℝ 3 g (Set.Icc (0 : ℝ) 1) := by
    dsimp [g]
    apply ContDiffOn.rpow
    · dsimp [X]
      fun_prop
    · dsimp [Y]
      fun_prop
    · intro t ht
      exact (hXpos t ht).ne'
  obtain ⟨theta, htheta, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := g) (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (n := 2)
      zero_lt_one hgdiff
  have hXzero : 0 < X 0 := hXpos 0 (by norm_num)
  have hXtheta : 0 < X theta :=
    hXpos theta ⟨htheta.1.le, htheta.2.le⟩
  have hgat0 : ContDiffAt ℝ 3 g 0 := by
    dsimp [g]
    apply ContDiffAt.rpow
    · dsimp [X]
      fun_prop
    · dsimp [Y]
      fun_prop
    · exact hXzero.ne'
  have hwithin1 :
      iteratedDerivWithin 1 g (Set.Icc (0 : ℝ) 1) 0 =
        iteratedDeriv 1 g 0 := by
    exact iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc zero_lt_one) (hgat0.of_le (by norm_num)) (by norm_num)
  have hwithin2 :
      iteratedDerivWithin 2 g (Set.Icc (0 : ℝ) 1) 0 =
        iteratedDeriv 2 g 0 := by
    exact iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc zero_lt_one) (hgat0.of_le (by norm_num)) (by norm_num)
  have htaylor :
      taylorWithinEval g 2 (Set.Icc (0 : ℝ) 1) 0 1 =
        quadraticTaylorAtOne p := by
    rw [show 2 = 1 + 1 by norm_num, taylorWithinEval_succ,
      show 1 = 0 + 1 by norm_num, taylorWithinEval_succ,
      taylor_within_zero_eval, hwithin1, hwithin2, hi1 0 hXzero,
      hi2 0 hXzero]
    dsimp [g, q1, q2, ell, mell, X, Y, h, k, quadraticTaylorAtOne]
    norm_num
    ring
  have hg1eq : g 1 = powerFunction p := by
    dsimp [g, X, Y, h, k, powerFunction]
    congr <;> ring
  have hq3eq :
      (1 / 6 : ℝ) * q3 theta =
        thirdDirectionalTerm (segmentPoint p theta)
          (p.x - 1) (p.y - 1) := by
    have hr1 :
        X theta ^ (Y theta - 1) = X theta ^ Y theta / X theta :=
      Real.rpow_sub_one hXtheta.ne' _
    have hr2 :
        X theta ^ (Y theta - 2) = X theta ^ Y theta / X theta ^ 2 := by
      simpa only [Real.rpow_two] using
        Real.rpow_sub hXtheta (Y theta) 2
    have hr3 :
        X theta ^ (Y theta - 3) = X theta ^ Y theta / X theta ^ 3 := by
      calc
        X theta ^ (Y theta - 3) =
            X theta ^ Y theta / X theta ^ (3 : ℝ) :=
          Real.rpow_sub hXtheta (Y theta) 3
        _ = X theta ^ Y theta / X theta ^ (3 : ℕ) :=
          congrArg (fun z : ℝ => X theta ^ Y theta / z)
            (Real.rpow_natCast (X theta) 3)
    dsimp [q3, g, ell, mell, nell, thirdDirectionalTerm, segmentPoint]
    rw [show 1 + theta * (p.x - 1) = X theta by rfl,
      show 1 + theta * (p.y - 1) = Y theta by rfl,
      hr1, hr2, hr3]
    field_simp [hXtheta.ne']
    dsimp [h, k]
    ring
  refine ⟨theta, htheta, ?_⟩
  rw [← hg1eq, ← htaylor, ← hq3eq]
  rw [hi3 theta hXtheta] at hrem
  norm_num at hrem ⊢
  linarith

theorem gap11 :
    ∀ p : Point2, 0 < p.x → ∀ h k : ℝ,
      thirdDirectionalTerm p h k =
        (1 / 6 : ℝ) *
          (p.y * (p.y - 1) * (p.y - 2) * p.x ^ (p.y - 3) * h ^ 3 +
            3 * ((2 * p.y - 1) * p.x ^ (p.y - 2) +
              p.y * (p.y - 1) * p.x ^ (p.y - 2) * Real.log p.x) *
              h ^ 2 * k +
            3 * (p.y * p.x ^ (p.y - 1) * (Real.log p.x) ^ 2 +
              2 * p.x ^ (p.y - 1) * Real.log p.x) * h * k ^ 2 +
            p.x ^ p.y * (Real.log p.x) ^ 3 * k ^ 3) := by
  intro p hp h k
  rfl

theorem gap12 :
    ∀ p : Point2, xIncrement p = p.x - 1 := by
  intro p
  rfl

theorem gap13 :
    ∀ p : Point2, yIncrement p = p.y - 1 := by
  intro p
  rfl

end

end ProofGap.Exercise3585
