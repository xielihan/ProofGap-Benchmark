import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3232

noncomputable section

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def eulerLHS (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x * partialX f x y z + y * partialY f x y z + z * partialZ f x y z

def Differentiable3 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ
    (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)

def admissible (f : ℝ → ℝ → ℝ → ℝ) (n : ℝ) : Prop :=
  Differentiable3 f ∧
    ∀ x y z : ℝ, eulerLHS f x y z = n * f x y z

def rayQuotient
    (f : ℝ → ℝ → ℝ → ℝ) (n x₀ y₀ z₀ t : ℝ) : ℝ :=
  f (t * x₀) (t * y₀) (t * z₀) / Real.rpow t n

private theorem rayNumerator_hasDerivAt
    (f : ℝ → ℝ → ℝ → ℝ) (hf : Differentiable3 f)
    (t x₀ y₀ z₀ : ℝ) :
    HasDerivAt
      (fun s : ℝ => f (s * x₀) (s * y₀) (s * z₀))
      (x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
        y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
        z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀)) t := by
  let F : ℝ × (ℝ × ℝ) → ℝ :=
    fun p => f p.1 p.2.1 p.2.2
  let v : ℝ × (ℝ × ℝ) := (x₀, (y₀, z₀))
  let ex : ℝ × (ℝ × ℝ) := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
  let ey : ℝ × (ℝ × ℝ) := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
  let ez : ℝ × (ℝ × ℝ) := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
  let A : ℝ →L[ℝ] (ℝ × (ℝ × ℝ)) :=
    ContinuousLinearMap.toSpanSingleton ℝ v
  let Ax : ℝ →L[ℝ] (ℝ × (ℝ × ℝ)) :=
    ContinuousLinearMap.toSpanSingleton ℝ ex
  let Ay : ℝ →L[ℝ] (ℝ × (ℝ × ℝ)) :=
    ContinuousLinearMap.toSpanSingleton ℝ ey
  let Az : ℝ →L[ℝ] (ℝ × (ℝ × ℝ)) :=
    ContinuousLinearMap.toSpanSingleton ℝ ez
  let p : ℝ × (ℝ × ℝ) := A t
  let L : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ := fderiv ℝ F p
  have hd : Differentiable ℝ F := by
    simpa [Differentiable3, F] using hf
  have hF : HasFDerivAt F L p := (hd p).hasFDerivAt
  have hx :
      partialX f (t * x₀) (t * y₀) (t * z₀) = L ex := by
    let cx : ℝ × (ℝ × ℝ) :=
      ((0 : ℝ), (t * y₀, t * z₀))
    have hinner :
        HasFDerivAt
          ((fun _ : ℝ => cx) + ⇑Ax)
          Ax (t * x₀) := by
      simpa only [zero_add] using
        (hasFDerivAt_const (x := t * x₀) cx).add Ax.hasFDerivAt
    have hFp : HasFDerivAt F L (cx + Ax (t * x₀)) := by
      simpa [p, A, v, cx, Ax, ex, smul_eq_mul] using hF
    have hcomp := hFp.comp (t * x₀) hinner
    simpa [partialX, F, Function.comp_def, cx, Ax, ex, smul_eq_mul] using
      hcomp.hasDerivAt.deriv
  have hy :
      partialY f (t * x₀) (t * y₀) (t * z₀) = L ey := by
    let cy : ℝ × (ℝ × ℝ) :=
      (t * x₀, ((0 : ℝ), t * z₀))
    have hinner :
        HasFDerivAt
          ((fun _ : ℝ => cy) + ⇑Ay)
          Ay (t * y₀) := by
      simpa only [zero_add] using
        (hasFDerivAt_const (x := t * y₀) cy).add Ay.hasFDerivAt
    have hFp : HasFDerivAt F L (cy + Ay (t * y₀)) := by
      simpa [p, A, v, cy, Ay, ey, smul_eq_mul] using hF
    have hcomp := hFp.comp (t * y₀) hinner
    simpa [partialY, F, Function.comp_def, cy, Ay, ey, smul_eq_mul] using
      hcomp.hasDerivAt.deriv
  have hz :
      partialZ f (t * x₀) (t * y₀) (t * z₀) = L ez := by
    let cz : ℝ × (ℝ × ℝ) :=
      (t * x₀, (t * y₀, (0 : ℝ)))
    have hinner :
        HasFDerivAt
          ((fun _ : ℝ => cz) + ⇑Az)
          Az (t * z₀) := by
      simpa only [zero_add] using
        (hasFDerivAt_const (x := t * z₀) cz).add Az.hasFDerivAt
    have hFp : HasFDerivAt F L (cz + Az (t * z₀)) := by
      simpa [p, A, v, cz, Az, ez, smul_eq_mul] using hF
    have hcomp := hFp.comp (t * z₀) hinner
    simpa [partialZ, F, Function.comp_def, cz, Az, ez, smul_eq_mul] using
      hcomp.hasDerivAt.deriv
  have hFpRay : HasFDerivAt F L (A t) := by
    simpa [p] using hF
  have hrF := hFpRay.comp t A.hasFDerivAt
  have hr :
      HasDerivAt
        (fun s : ℝ => f (s * x₀) (s * y₀) (s * z₀))
        (L v) t := by
    simpa [F, A, v, Function.comp_def, smul_eq_mul] using hrF.hasDerivAt
  have hdecomp :
      v = (x₀ • ex + y₀ • ey) + z₀ • ez := by
    simp [v, ex, ey, ez]
  have hL :
      L v = x₀ * L ex + y₀ * L ey + z₀ * L ez := by
    rw [hdecomp]
    simp [map_add, map_smul, smul_eq_mul]
  rw [hL, ← hx, ← hy, ← hz] at hr
  exact hr

theorem gap1 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n x₀ y₀ z₀ : ℝ),
      admissible f n →
        DifferentiableOn ℝ (rayQuotient f n x₀ y₀ z₀) (Set.Ioi 0) := by
  intro f n x₀ y₀ z₀ hf
  intro t ht
  have hnum :=
    rayNumerator_hasDerivAt f hf.1 t x₀ y₀ z₀
  have hpow :
      HasDerivAt (fun s : ℝ => Real.rpow s n)
        (n * Real.rpow t (n - 1)) t := by
    simpa [mul_comm] using
      (Real.hasDerivAt_rpow_const (p := n)
        (Or.inl (ne_of_gt ht)))
  have hpow0 : Real.rpow t n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht n)
  simpa only [rayQuotient] using
    (hnum.differentiableAt.div hpow.differentiableAt hpow0).differentiableWithinAt

theorem gap2 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x₀ y₀ z₀ : ℝ),
      admissible f n → 0 < t →
        deriv (rayQuotient f n x₀ y₀ z₀) t =
          (1 / Real.rpow t n) *
              (x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
                y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
                z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀)) -
            (n / Real.rpow t (n + 1)) *
              f (t * x₀) (t * y₀) (t * z₀) := by
  intro f n t x₀ y₀ z₀ hf ht
  have hnum :=
    rayNumerator_hasDerivAt f hf.1 t x₀ y₀ z₀
  have hpow :
      HasDerivAt (fun s : ℝ => Real.rpow s n)
        (n * Real.rpow t (n - 1)) t := by
    simpa [mul_comm] using
      (Real.hasDerivAt_rpow_const (p := n)
        (Or.inl (ne_of_gt ht)))
  have hqn0 : Real.rpow t n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht n)
  have hqsucc0 : Real.rpow t (n + 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht (n + 1))
  have hdef (a : ℝ) :
      Real.rpow t a = Real.exp (Real.log t * a) := by
    change t ^ a = Real.exp (Real.log t * a)
    exact Real.rpow_def_of_pos ht a
  have hprod :
      Real.rpow t (n - 1) * Real.rpow t (n + 1) =
        (Real.rpow t n) ^ 2 := by
    rw [hdef (n - 1), hdef (n + 1), hdef n]
    calc
      Real.exp (Real.log t * (n - 1)) *
            Real.exp (Real.log t * (n + 1)) =
          Real.exp
            (Real.log t * (n - 1) + Real.log t * (n + 1)) := by
              rw [Real.exp_add]
      _ = Real.exp (Real.log t * n + Real.log t * n) := by
            congr 1
            ring
      _ = Real.exp (Real.log t * n) * Real.exp (Real.log t * n) := by
            rw [Real.exp_add]
      _ = (Real.exp (Real.log t * n)) ^ 2 := by ring
  have hc1 :
      Real.rpow t n / (Real.rpow t n) ^ 2 =
        1 / Real.rpow t n := by
    field_simp [hqn0] <;> ring
  have hc2 :
      Real.rpow t (n - 1) / (Real.rpow t n) ^ 2 =
        1 / Real.rpow t (n + 1) := by
    field_simp [hqn0, hqsucc0] <;> nlinarith [hprod]
  have hquot := hnum.div hpow hqn0
  calc
    deriv (rayQuotient f n x₀ y₀ z₀) t =
        ((x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
              y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
              z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀)) *
              Real.rpow t n -
            f (t * x₀) (t * y₀) (t * z₀) *
              (n * Real.rpow t (n - 1))) /
          (Real.rpow t n) ^ 2 := by
            simpa only [rayQuotient] using hquot.deriv
    _ =
        (x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
              y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
              z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀)) *
            (Real.rpow t n / (Real.rpow t n) ^ 2) -
          (n * f (t * x₀) (t * y₀) (t * z₀)) *
            (Real.rpow t (n - 1) / (Real.rpow t n) ^ 2) := by
      ring
    _ =
        (1 / Real.rpow t n) *
              (x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
                y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
                z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀)) -
            (n / Real.rpow t (n + 1)) *
              f (t * x₀) (t * y₀) (t * z₀) := by
      rw [hc1, hc2]
      ring

theorem gap3 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x₀ y₀ z₀ : ℝ),
      admissible f n → 0 < t →
        deriv (rayQuotient f n x₀ y₀ z₀) t =
          (1 / Real.rpow t (n + 1)) *
            (t * x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
              t * y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
              t * z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀) -
              n * f (t * x₀) (t * y₀) (t * z₀)) := by
  intro f n t x₀ y₀ z₀ hf ht
  have hqn0 : Real.rpow t n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht n)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hdef (a : ℝ) :
      Real.rpow t a = Real.exp (Real.log t * a) := by
    change t ^ a = Real.exp (Real.log t * a)
    exact Real.rpow_def_of_pos ht a
  have hpow_succ :
      Real.rpow t (n + 1) = Real.rpow t n * t := by
    rw [hdef (n + 1), hdef n]
    calc
      Real.exp (Real.log t * (n + 1)) =
          Real.exp (Real.log t * n + Real.log t) := by
            congr 1
            ring
      _ = Real.exp (Real.log t * n) * Real.exp (Real.log t) := by
            rw [Real.exp_add]
      _ = Real.exp (Real.log t * n) * t := by
            rw [Real.exp_log ht]
  have hc :
      1 / Real.rpow t n = t / Real.rpow t (n + 1) := by
    rw [hpow_succ]
    field_simp [hqn0, ht0] <;> ring
  calc
    deriv (rayQuotient f n x₀ y₀ z₀) t =
        (1 / Real.rpow t n) *
              (x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
                y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
                z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀)) -
            (n / Real.rpow t (n + 1)) *
              f (t * x₀) (t * y₀) (t * z₀) :=
      gap2 f n t x₀ y₀ z₀ hf ht
    _ = (1 / Real.rpow t (n + 1)) *
            (t * x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
              t * y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
              t * z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀) -
              n * f (t * x₀) (t * y₀) (t * z₀)) := by
      rw [hc]
      ring

theorem gap4 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x₀ y₀ z₀ : ℝ),
      admissible f n → 0 < t →
        t * x₀ * partialX f (t * x₀) (t * y₀) (t * z₀) +
            t * y₀ * partialY f (t * x₀) (t * y₀) (t * z₀) +
            t * z₀ * partialZ f (t * x₀) (t * y₀) (t * z₀) =
          n * f (t * x₀) (t * y₀) (t * z₀) := by
  intro f n t x₀ y₀ z₀ hf _
  simpa [eulerLHS] using
    hf.2 (t * x₀) (t * y₀) (t * z₀)

theorem gap5 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x₀ y₀ z₀ : ℝ),
      admissible f n → 0 < t →
        deriv (rayQuotient f n x₀ y₀ z₀) t = 0 := by
  intro f n t x₀ y₀ z₀ hf ht
  rw [gap3 f n t x₀ y₀ z₀ hf ht]
  rw [gap4 f n t x₀ y₀ z₀ hf ht]
  ring

theorem gap6 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n x₀ y₀ z₀ : ℝ),
      admissible f n →
        ∃ c : ℝ, ∀ t : ℝ, 0 < t →
          rayQuotient f n x₀ y₀ z₀ t = c := by
  intro f n x₀ y₀ z₀ hf
  let g := rayQuotient f n x₀ y₀ z₀
  have hdiff : DifferentiableOn ℝ g (Set.Ioi 0) := by
    simpa [g] using gap1 f n x₀ y₀ z₀ hf
  have hzero : ∀ u ∈ Set.Ioi (0 : ℝ), deriv g u = 0 := by
    intro u hu
    simpa [g] using gap5 f n u x₀ y₀ z₀ hf hu
  refine ⟨g 1, ?_⟩
  intro t ht
  have ht' : t ∈ Set.Ioi (0 : ℝ) := ht
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    exact (show (0 : ℝ) < 1 from zero_lt_one)
  have hconst : g t = g 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero
      isPreconnected_Ioi hdiff hzero ht' h1
  exact hconst

theorem gap7 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n x₀ y₀ z₀ c : ℝ),
      (∀ t : ℝ, 0 < t → rayQuotient f n x₀ y₀ z₀ t = c) →
        c = f x₀ y₀ z₀ := by
  intro f n x₀ y₀ z₀ c h
  simpa [rayQuotient] using (h 1 zero_lt_one).symm

theorem gap8 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x₀ y₀ z₀ : ℝ),
      admissible f n → 0 < t →
        rayQuotient f n x₀ y₀ z₀ t = f x₀ y₀ z₀ := by
  intro f n t x₀ y₀ z₀ hf ht
  rcases gap6 f n x₀ y₀ z₀ hf with ⟨c, hc⟩
  calc
    rayQuotient f n x₀ y₀ z₀ t = c := hc t ht
    _ = f x₀ y₀ z₀ := gap7 f n x₀ y₀ z₀ c hc

theorem gap9 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x₀ y₀ z₀ : ℝ),
      admissible f n → 0 < t →
        f (t * x₀) (t * y₀) (t * z₀) =
          Real.rpow t n * f x₀ y₀ z₀ := by
  intro f n t x₀ y₀ z₀ hf ht
  have h := gap8 f n t x₀ y₀ z₀ hf ht
  unfold rayQuotient at h
  have hpow0 : Real.rpow t n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht n)
  calc
    f (t * x₀) (t * y₀) (t * z₀) =
        f x₀ y₀ z₀ * Real.rpow t n :=
      (div_eq_iff hpow0).mp h
    _ = Real.rpow t n * f x₀ y₀ z₀ := mul_comm _ _

theorem gap10 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n x y z t : ℝ),
      admissible f n → 0 < t →
        f (t * x) (t * y) (t * z) =
          Real.rpow t n * f x y z := by
  intro f n x y z t hf ht
  exact gap9 f n t x y z hf ht

theorem gap11 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n x y z t : ℝ),
      admissible f n → 0 < t →
        f (t * x) (t * y) (t * z) =
          Real.rpow t n * f x y z := by
  intro f n x y z t hf ht
  exact gap10 f n x y z t hf ht

end

end ProofGap.Exercise3232
