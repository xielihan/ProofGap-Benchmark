import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3384

noncomputable section

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z t y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z x t) y

def partialXX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z t y) x

def partialXY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z x t) y

def partialYY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY z x t) y

def IsC2Surface (a : ℝ) (D : Set (ℝ × ℝ))
    (z : ℝ → ℝ → ℝ) : Prop :=
  IsOpen D ∧ ContDiffOn ℝ 2 (Function.uncurry z) D ∧
    ∀ p ∈ D,
      z p.1 p.2 ^ 3 - 3 * p.1 * p.2 * z p.1 p.2 = a ^ 3 ∧
        z p.1 p.2 ^ 2 - p.1 * p.2 ≠ 0

private theorem surfaceDifferentiableAt
    (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) (p : ℝ × ℝ) (hp : p ∈ D) :
    DifferentiableAt ℝ (Function.uncurry z) p := by
  exact ((h.2.1.differentiableOn (by decide)) p hp).differentiableAt
    (h.1.mem_nhds hp)

theorem gap1 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      3 * z p.1 p.2 ^ 2 * partialX z p.1 p.2 -
        3 * p.2 * z p.1 p.2 -
        3 * p.1 * p.2 * partialX z p.1 p.2 = 0 := by
  intro p hp
  have hpair : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 := by
    fun_prop
  have hzline : DifferentiableAt ℝ (fun t : ℝ => z t p.2) p.1 := by
    simpa [Function.uncurry] using
      (surfaceDifferentiableAt a D z h p hp).comp p.1 hpair
  have hzder :
      HasDerivAt (fun t : ℝ => z t p.2)
        (partialX z p.1 p.2) p.1 := by
    simpa [partialX] using hzline.hasDerivAt
  have hopen : ∀ᶠ t : ℝ in nhds p.1, (t, p.2) ∈ D :=
    hpair.continuousAt.tendsto (h.1.mem_nhds hp)
  have heq :
      (fun t : ℝ => z t p.2 ^ 3 - 3 * t * p.2 * z t p.2) =ᶠ[nhds p.1]
        (fun _ : ℝ => a ^ 3) := by
    refine hopen.mono ?_
    intro t ht
    simpa using (h.2.2 (t, p.2) ht).1
  have hlhs :
      HasDerivAt
        (fun t : ℝ => z t p.2 ^ 3 - 3 * t * p.2 * z t p.2)
        (3 * z p.1 p.2 ^ 2 * partialX z p.1 p.2 -
          3 * p.2 * z p.1 p.2 -
          3 * p.1 * p.2 * partialX z p.1 p.2) p.1 := by
    convert (hzder.pow 3).sub
      ((((hasDerivAt_id p.1).const_mul (3 : ℝ)).mul_const p.2).mul hzder) using 1 <;>
      simp [id] <;> ring
  calc
    3 * z p.1 p.2 ^ 2 * partialX z p.1 p.2 -
          3 * p.2 * z p.1 p.2 -
          3 * p.1 * p.2 * partialX z p.1 p.2 =
        deriv (fun t : ℝ => z t p.2 ^ 3 - 3 * t * p.2 * z t p.2) p.1 :=
      hlhs.deriv.symm
    _ = deriv (fun _ : ℝ => a ^ 3) p.1 :=
      Filter.EventuallyEq.deriv_eq heq
    _ = 0 := (hasDerivAt_const p.1 (a ^ 3)).deriv

theorem gap2 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialX z p.1 p.2 =
        p.2 * z p.1 p.2 / (z p.1 p.2 ^ 2 - p.1 * p.2) := by
  intro p hp
  have hn : z p.1 p.2 ^ 2 - p.1 * p.2 ≠ 0 := (h.2.2 p hp).2
  apply (eq_div_iff hn).2
  nlinarith [gap1 a D z h p hp]

theorem gap3 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialY z p.1 p.2 =
        p.1 * z p.1 p.2 / (z p.1 p.2 ^ 2 - p.1 * p.2) := by
  intro p hp
  have hpair : DifferentiableAt ℝ (fun t : ℝ => (p.1, t)) p.2 := by
    fun_prop
  have hzline : DifferentiableAt ℝ (fun t : ℝ => z p.1 t) p.2 := by
    simpa [Function.uncurry] using
      (surfaceDifferentiableAt a D z h p hp).comp p.2 hpair
  have hzder :
      HasDerivAt (fun t : ℝ => z p.1 t)
        (partialY z p.1 p.2) p.2 := by
    simpa [partialY] using hzline.hasDerivAt
  have hopen : ∀ᶠ t : ℝ in nhds p.2, (p.1, t) ∈ D :=
    hpair.continuousAt.tendsto (h.1.mem_nhds hp)
  have heq :
      (fun t : ℝ => z p.1 t ^ 3 - 3 * p.1 * t * z p.1 t) =ᶠ[nhds p.2]
        (fun _ : ℝ => a ^ 3) := by
    refine hopen.mono ?_
    intro t ht
    simpa using (h.2.2 (p.1, t) ht).1
  have hlhs :
      HasDerivAt
        (fun t : ℝ => z p.1 t ^ 3 - 3 * p.1 * t * z p.1 t)
        (3 * z p.1 p.2 ^ 2 * partialY z p.1 p.2 -
          3 * p.1 * z p.1 p.2 -
          3 * p.1 * p.2 * partialY z p.1 p.2) p.2 := by
    convert (hzder.pow 3).sub
      (((hasDerivAt_id p.2).const_mul (3 * p.1)).mul hzder) using 1 <;>
      simp [id] <;> ring
  have hzero :
      3 * z p.1 p.2 ^ 2 * partialY z p.1 p.2 -
          3 * p.1 * z p.1 p.2 -
          3 * p.1 * p.2 * partialY z p.1 p.2 = 0 := by
    calc
      _ = deriv (fun t : ℝ => z p.1 t ^ 3 - 3 * p.1 * t * z p.1 t) p.2 :=
        hlhs.deriv.symm
      _ = deriv (fun _ : ℝ => a ^ 3) p.2 :=
        Filter.EventuallyEq.deriv_eq heq
      _ = 0 := (hasDerivAt_const p.2 (a ^ 3)).deriv
  have hn : z p.1 p.2 ^ 2 - p.1 * p.2 ≠ 0 := (h.2.2 p hp).2
  apply (eq_div_iff hn).2
  nlinarith [hzero]

theorem gap4 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      2 * z p.1 p.2 * partialX z p.1 p.2 ^ 2 +
        z p.1 p.2 ^ 2 * partialXX z p.1 p.2 -
        2 * p.2 * partialX z p.1 p.2 -
        p.1 * p.2 * partialXX z p.1 p.2 = 0 := by
  intro p hp
  have hpair : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 := by
    fun_prop
  have hzline : DifferentiableAt ℝ (fun t : ℝ => z t p.2) p.1 := by
    simpa [Function.uncurry] using
      (surfaceDifferentiableAt a D z h p hp).comp p.1 hpair
  have hzder :
      HasDerivAt (fun t : ℝ => z t p.2)
        (partialX z p.1 p.2) p.1 := by
    simpa [partialX] using hzline.hasDerivAt
  have hn : z p.1 p.2 ^ 2 - p.1 * p.2 ≠ 0 := (h.2.2 p hp).2
  have hopen : ∀ᶠ t : ℝ in nhds p.1, (t, p.2) ∈ D :=
    hpair.continuousAt.tendsto (h.1.mem_nhds hp)
  have heq :
      (fun t : ℝ => partialX z t p.2) =ᶠ[nhds p.1]
        (fun t : ℝ => p.2 * z t p.2 /
          (z t p.2 ^ 2 - t * p.2)) := by
    refine hopen.mono ?_
    intro t ht
    simpa using gap2 a D z h (t, p.2) ht
  have hnum :
      HasDerivAt (fun t : ℝ => p.2 * z t p.2)
        (p.2 * partialX z p.1 p.2) p.1 :=
    hzder.const_mul p.2
  have hden :
      HasDerivAt (fun t : ℝ => z t p.2 ^ 2 - t * p.2)
        (2 * z p.1 p.2 * partialX z p.1 p.2 - p.2) p.1 := by
    convert (hzder.pow 2).sub ((hasDerivAt_id p.1).mul_const p.2) using 1 <;>
      ring
  have hquot :
      HasDerivAt
        (fun t : ℝ => p.2 * z t p.2 /
          (z t p.2 ^ 2 - t * p.2))
        (((p.2 * partialX z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.2 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialX z p.1 p.2 - p.2)) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2) p.1 := by
    convert hnum.div hden hn using 1 <;> ring
  have hxx :
      partialXX z p.1 p.2 =
        ((p.2 * partialX z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.2 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialX z p.1 p.2 - p.2)) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by
    calc
      partialXX z p.1 p.2 =
          deriv (fun t : ℝ => partialX z t p.2) p.1 := rfl
      _ = deriv
          (fun t : ℝ => p.2 * z t p.2 /
            (z t p.2 ^ 2 - t * p.2)) p.1 :=
        Filter.EventuallyEq.deriv_eq heq
      _ = _ := hquot.deriv
  have hxxmul := (eq_div_iff (pow_ne_zero 2 hn)).mp hxx
  have hxmul := (eq_div_iff hn).mp (gap2 a D z h p hp)
  have hmul :
      ((z p.1 p.2 ^ 2 - p.1 * p.2) * partialXX z p.1 p.2 +
          2 * z p.1 p.2 * partialX z p.1 p.2 ^ 2 -
          2 * p.2 * partialX z p.1 p.2) *
        (z p.1 p.2 ^ 2 - p.1 * p.2) = 0 := by
    calc
      _ = partialXX z p.1 p.2 *
              (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 +
            2 * z p.1 p.2 * partialX z p.1 p.2 *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            2 * p.2 *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) := by ring
      _ = ((p.2 * partialX z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.2 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialX z p.1 p.2 - p.2)) +
            2 * z p.1 p.2 * partialX z p.1 p.2 *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            2 * p.2 *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) := by rw [hxxmul]
      _ = p.2 *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            (p.2 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialX z p.1 p.2 - p.2) +
            2 * z p.1 p.2 * partialX z p.1 p.2 *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            2 * p.2 *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) := by ring
      _ = 0 := by rw [hxmul]; ring
  have hcore := (mul_eq_zero.mp hmul).resolve_right hn
  nlinarith [hcore]

theorem gap5 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) *
          partialX z p.1 p.2 +
        (z p.1 p.2 ^ 2 - p.1 * p.2) * partialXY z p.1 p.2 -
        z p.1 p.2 - p.2 * partialY z p.1 p.2 = 0 := by
  intro p hp
  have hpair : DifferentiableAt ℝ (fun t : ℝ => (p.1, t)) p.2 := by
    fun_prop
  have hzline : DifferentiableAt ℝ (fun t : ℝ => z p.1 t) p.2 := by
    simpa [Function.uncurry] using
      (surfaceDifferentiableAt a D z h p hp).comp p.2 hpair
  have hzder :
      HasDerivAt (fun t : ℝ => z p.1 t)
        (partialY z p.1 p.2) p.2 := by
    simpa [partialY] using hzline.hasDerivAt
  have hn : z p.1 p.2 ^ 2 - p.1 * p.2 ≠ 0 := (h.2.2 p hp).2
  have hopen : ∀ᶠ t : ℝ in nhds p.2, (p.1, t) ∈ D :=
    hpair.continuousAt.tendsto (h.1.mem_nhds hp)
  have heq :
      (fun t : ℝ => partialX z p.1 t) =ᶠ[nhds p.2]
        (fun t : ℝ => t * z p.1 t /
          (z p.1 t ^ 2 - p.1 * t)) := by
    refine hopen.mono ?_
    intro t ht
    simpa using gap2 a D z h (p.1, t) ht
  have hnum :
      HasDerivAt (fun t : ℝ => t * z p.1 t)
        (z p.1 p.2 + p.2 * partialY z p.1 p.2) p.2 := by
    convert (hasDerivAt_id p.2).mul hzder using 1 <;>
      simp [id] <;> ring
  have hden :
      HasDerivAt (fun t : ℝ => z p.1 t ^ 2 - p.1 * t)
        (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) p.2 := by
    convert (hzder.pow 2).sub ((hasDerivAt_id p.2).const_mul p.1) using 1 <;>
      ring
  have hquot :
      HasDerivAt
        (fun t : ℝ => t * z p.1 t /
          (z p.1 t ^ 2 - p.1 * t))
        (((z p.1 p.2 + p.2 * partialY z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.2 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1)) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2) p.2 := by
    convert hnum.div hden hn using 1 <;> ring
  have hxy :
      partialXY z p.1 p.2 =
        ((z p.1 p.2 + p.2 * partialY z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.2 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1)) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by
    calc
      partialXY z p.1 p.2 =
          deriv (fun t : ℝ => partialX z p.1 t) p.2 := rfl
      _ = deriv
          (fun t : ℝ => t * z p.1 t /
            (z p.1 t ^ 2 - p.1 * t)) p.2 :=
        Filter.EventuallyEq.deriv_eq heq
      _ = _ := hquot.deriv
  have hxymul := (eq_div_iff (pow_ne_zero 2 hn)).mp hxy
  have hxmul := (eq_div_iff hn).mp (gap2 a D z h p hp)
  have hmul :
      ((2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) *
            partialX z p.1 p.2 +
          (z p.1 p.2 ^ 2 - p.1 * p.2) * partialXY z p.1 p.2 -
          z p.1 p.2 - p.2 * partialY z p.1 p.2) *
        (z p.1 p.2 ^ 2 - p.1 * p.2) = 0 := by
    calc
      _ = partialXY z p.1 p.2 *
              (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 +
            (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            (z p.1 p.2 + p.2 * partialY z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) := by ring
      _ = ((z p.1 p.2 + p.2 * partialY z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.2 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1)) +
            (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            (z p.1 p.2 + p.2 * partialY z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) := by rw [hxymul]
      _ = 0 := by rw [hxmul]; ring
  exact (mul_eq_zero.mp hmul).resolve_right hn

theorem gap6 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialXX z p.1 p.2 =
        -(2 * p.1 * p.2 ^ 3 * z p.1 p.2) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 3 := by
  intro p hp
  have hn : z p.1 p.2 ^ 2 - p.1 * p.2 ≠ 0 := (h.2.2 p hp).2
  have hxmul := (eq_div_iff hn).mp (gap2 a D z h p hp)
  have hbase :
      (z p.1 p.2 ^ 2 - p.1 * p.2) * partialXX z p.1 p.2 =
        2 * partialX z p.1 p.2 *
          (p.2 - z p.1 p.2 * partialX z p.1 p.2) := by
    nlinarith [gap4 a D z h p hp]
  have hminus :
      (p.2 - z p.1 p.2 * partialX z p.1 p.2) *
          (z p.1 p.2 ^ 2 - p.1 * p.2) =
        -(p.1 * p.2 ^ 2) := by
    calc
      _ = p.2 * (z p.1 p.2 ^ 2 - p.1 * p.2) -
            z p.1 p.2 *
              (partialX z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) := by ring
      _ = p.2 * (z p.1 p.2 ^ 2 - p.1 * p.2) -
            z p.1 p.2 * (p.2 * z p.1 p.2) := by rw [hxmul]
      _ = -(p.1 * p.2 ^ 2) := by ring
  apply (eq_div_iff (pow_ne_zero 3 hn)).2
  calc
    partialXX z p.1 p.2 *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 3 =
        ((z p.1 p.2 ^ 2 - p.1 * p.2) * partialXX z p.1 p.2) *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by ring
    _ = (2 * partialX z p.1 p.2 *
          (p.2 - z p.1 p.2 * partialX z p.1 p.2)) *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by rw [hbase]
    _ = 2 *
          (partialX z p.1 p.2 *
            (z p.1 p.2 ^ 2 - p.1 * p.2)) *
          ((p.2 - z p.1 p.2 * partialX z p.1 p.2) *
            (z p.1 p.2 ^ 2 - p.1 * p.2)) := by ring
    _ = 2 * (p.2 * z p.1 p.2) * (-(p.1 * p.2 ^ 2)) := by
      rw [hxmul, hminus]
    _ = -(2 * p.1 * p.2 ^ 3 * z p.1 p.2) := by ring

theorem gap7 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialXY z p.1 p.2 =
        z p.1 p.2 *
          (z p.1 p.2 ^ 4 -
            2 * p.1 * p.2 * z p.1 p.2 ^ 2 -
            p.1 ^ 2 * p.2 ^ 2) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 3 := by
  intro p hp
  have hn : z p.1 p.2 ^ 2 - p.1 * p.2 ≠ 0 := (h.2.2 p hp).2
  have hxmul := (eq_div_iff hn).mp (gap2 a D z h p hp)
  have hymul := (eq_div_iff hn).mp (gap3 a D z h p hp)
  have hbase :
      (z p.1 p.2 ^ 2 - p.1 * p.2) * partialXY z p.1 p.2 =
        z p.1 p.2 + p.2 * partialY z p.1 p.2 -
          (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) *
            partialX z p.1 p.2 := by
    nlinarith [gap5 a D z h p hp]
  apply (eq_div_iff (pow_ne_zero 3 hn)).2
  calc
    partialXY z p.1 p.2 *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 3 =
        ((z p.1 p.2 ^ 2 - p.1 * p.2) * partialXY z p.1 p.2) *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by ring
    _ = (z p.1 p.2 + p.2 * partialY z p.1 p.2 -
          (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) *
            partialX z p.1 p.2) *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by rw [hbase]
    _ = z p.1 p.2 * (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 +
          p.2 *
            (partialY z p.1 p.2 *
              (z p.1 p.2 ^ 2 - p.1 * p.2)) *
            (z p.1 p.2 ^ 2 - p.1 * p.2) -
          2 * z p.1 p.2 *
            (partialY z p.1 p.2 *
              (z p.1 p.2 ^ 2 - p.1 * p.2)) *
            (partialX z p.1 p.2 *
              (z p.1 p.2 ^ 2 - p.1 * p.2)) +
          p.1 *
            (partialX z p.1 p.2 *
              (z p.1 p.2 ^ 2 - p.1 * p.2)) *
            (z p.1 p.2 ^ 2 - p.1 * p.2) := by ring
    _ = z p.1 p.2 * (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 +
          p.2 * (p.1 * z p.1 p.2) *
            (z p.1 p.2 ^ 2 - p.1 * p.2) -
          2 * z p.1 p.2 * (p.1 * z p.1 p.2) *
            (p.2 * z p.1 p.2) +
          p.1 * (p.2 * z p.1 p.2) *
            (z p.1 p.2 ^ 2 - p.1 * p.2) := by rw [hymul, hxmul]
    _ = z p.1 p.2 *
          (z p.1 p.2 ^ 4 -
            2 * p.1 * p.2 * z p.1 p.2 ^ 2 -
            p.1 ^ 2 * p.2 ^ 2) := by ring

theorem gap8 (a : ℝ) (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface a D z) :
    ∀ p ∈ D,
      partialYY z p.1 p.2 =
        -(2 * p.1 ^ 3 * p.2 * z p.1 p.2) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 3 := by
  intro p hp
  have hpair : DifferentiableAt ℝ (fun t : ℝ => (p.1, t)) p.2 := by
    fun_prop
  have hzline : DifferentiableAt ℝ (fun t : ℝ => z p.1 t) p.2 := by
    simpa [Function.uncurry] using
      (surfaceDifferentiableAt a D z h p hp).comp p.2 hpair
  have hzder :
      HasDerivAt (fun t : ℝ => z p.1 t)
        (partialY z p.1 p.2) p.2 := by
    simpa [partialY] using hzline.hasDerivAt
  have hn : z p.1 p.2 ^ 2 - p.1 * p.2 ≠ 0 := (h.2.2 p hp).2
  have hopen : ∀ᶠ t : ℝ in nhds p.2, (p.1, t) ∈ D :=
    hpair.continuousAt.tendsto (h.1.mem_nhds hp)
  have heq :
      (fun t : ℝ => partialY z p.1 t) =ᶠ[nhds p.2]
        (fun t : ℝ => p.1 * z p.1 t /
          (z p.1 t ^ 2 - p.1 * t)) := by
    refine hopen.mono ?_
    intro t ht
    simpa using gap3 a D z h (p.1, t) ht
  have hnum :
      HasDerivAt (fun t : ℝ => p.1 * z p.1 t)
        (p.1 * partialY z p.1 p.2) p.2 :=
    hzder.const_mul p.1
  have hden :
      HasDerivAt (fun t : ℝ => z p.1 t ^ 2 - p.1 * t)
        (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) p.2 := by
    convert (hzder.pow 2).sub ((hasDerivAt_id p.2).const_mul p.1) using 1 <;>
      ring
  have hquot :
      HasDerivAt
        (fun t : ℝ => p.1 * z p.1 t /
          (z p.1 t ^ 2 - p.1 * t))
        (((p.1 * partialY z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.1 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1)) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2) p.2 := by
    convert hnum.div hden hn using 1 <;> ring
  have hyy :
      partialYY z p.1 p.2 =
        ((p.1 * partialY z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.1 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1)) /
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by
    calc
      partialYY z p.1 p.2 =
          deriv (fun t : ℝ => partialY z p.1 t) p.2 := rfl
      _ = deriv
          (fun t : ℝ => p.1 * z p.1 t /
            (z p.1 t ^ 2 - p.1 * t)) p.2 :=
        Filter.EventuallyEq.deriv_eq heq
      _ = _ := hquot.deriv
  have hyymul := (eq_div_iff (pow_ne_zero 2 hn)).mp hyy
  have hymul := (eq_div_iff hn).mp (gap3 a D z h p hp)
  have hmul :
      ((z p.1 p.2 ^ 2 - p.1 * p.2) * partialYY z p.1 p.2 +
          2 * z p.1 p.2 * partialY z p.1 p.2 ^ 2 -
          2 * p.1 * partialY z p.1 p.2) *
        (z p.1 p.2 ^ 2 - p.1 * p.2) = 0 := by
    calc
      _ = partialYY z p.1 p.2 *
              (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 +
            2 * z p.1 p.2 * partialY z p.1 p.2 *
              (partialY z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            2 * p.1 *
              (partialY z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) := by ring
      _ = ((p.1 * partialY z p.1 p.2) *
              (z p.1 p.2 ^ 2 - p.1 * p.2) -
            (p.1 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1)) +
            2 * z p.1 p.2 * partialY z p.1 p.2 *
              (partialY z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            2 * p.1 *
              (partialY z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) := by rw [hyymul]
      _ = p.1 *
              (partialY z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            (p.1 * z p.1 p.2) *
              (2 * z p.1 p.2 * partialY z p.1 p.2 - p.1) +
            2 * z p.1 p.2 * partialY z p.1 p.2 *
              (partialY z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) -
            2 * p.1 *
              (partialY z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) := by ring
      _ = 0 := by rw [hymul]; ring
  have hcore := (mul_eq_zero.mp hmul).resolve_right hn
  have hbase :
      (z p.1 p.2 ^ 2 - p.1 * p.2) * partialYY z p.1 p.2 =
        2 * partialY z p.1 p.2 *
          (p.1 - z p.1 p.2 * partialY z p.1 p.2) := by
    nlinarith [hcore]
  have hminus :
      (p.1 - z p.1 p.2 * partialY z p.1 p.2) *
          (z p.1 p.2 ^ 2 - p.1 * p.2) =
        -(p.1 ^ 2 * p.2) := by
    calc
      _ = p.1 * (z p.1 p.2 ^ 2 - p.1 * p.2) -
            z p.1 p.2 *
              (partialY z p.1 p.2 *
                (z p.1 p.2 ^ 2 - p.1 * p.2)) := by ring
      _ = p.1 * (z p.1 p.2 ^ 2 - p.1 * p.2) -
            z p.1 p.2 * (p.1 * z p.1 p.2) := by rw [hymul]
      _ = -(p.1 ^ 2 * p.2) := by ring
  apply (eq_div_iff (pow_ne_zero 3 hn)).2
  calc
    partialYY z p.1 p.2 *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 3 =
        ((z p.1 p.2 ^ 2 - p.1 * p.2) * partialYY z p.1 p.2) *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by ring
    _ = (2 * partialY z p.1 p.2 *
          (p.1 - z p.1 p.2 * partialY z p.1 p.2)) *
          (z p.1 p.2 ^ 2 - p.1 * p.2) ^ 2 := by rw [hbase]
    _ = 2 *
          (partialY z p.1 p.2 *
            (z p.1 p.2 ^ 2 - p.1 * p.2)) *
          ((p.1 - z p.1 p.2 * partialY z p.1 p.2) *
            (z p.1 p.2 ^ 2 - p.1 * p.2)) := by ring
    _ = 2 * (p.1 * z p.1 p.2) * (-(p.1 ^ 2 * p.2)) := by
      rw [hymul, hminus]
    _ = -(2 * p.1 ^ 3 * p.2 * z p.1 p.2) := by ring

end

end ProofGap.Exercise3384
