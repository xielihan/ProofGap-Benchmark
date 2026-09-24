import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3385

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

def firstDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialX z x y * dx + partialY z x y * dy

def secondDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialXX z x y * dx ^ 2 +
    2 * partialXY z x y * dx * dy +
      partialYY z x y * dy ^ 2

def IsC2Surface (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ) : Prop :=
  IsOpen D ∧ ContDiffOn ℝ 2 (Function.uncurry z) D ∧
    ∀ p ∈ D,
      p.1 + p.2 + z p.1 p.2 = Real.exp (z p.1 p.2) ∧
        Real.exp (z p.1 p.2) - 1 ≠ 0

private theorem surfaceDerivatives
    (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialX z p.1 p.2 =
          1 / (Real.exp (z p.1 p.2) - 1) ∧
      partialY z p.1 p.2 =
          1 / (Real.exp (z p.1 p.2) - 1) ∧
      partialXX z p.1 p.2 =
          -(Real.exp (z p.1 p.2) /
            (Real.exp (z p.1 p.2) - 1) ^ 3) ∧
      partialXY z p.1 p.2 =
          -(Real.exp (z p.1 p.2) /
            (Real.exp (z p.1 p.2) - 1) ^ 3) ∧
      partialYY z p.1 p.2 =
          -(Real.exp (z p.1 p.2) /
            (Real.exp (z p.1 p.2) - 1) ^ 3) := by
  have firstAt : ∀ q ∈ D,
      partialX z q.1 q.2 = 1 / (Real.exp (z q.1 q.2) - 1) ∧
      partialY z q.1 q.2 = 1 / (Real.exp (z q.1 q.2) - 1) := by
    intro q hq
    rcases q with ⟨a, b⟩
    have hz : DifferentiableAt ℝ (Function.uncurry z) (a, b) :=
      ((h.2.1 (a, b) hq).contDiffAt (h.1.mem_nhds hq)).differentiableAt
        (by decide)
    have hzx : DifferentiableAt ℝ (fun t : ℝ => z t b) a := by
      have hm : DifferentiableAt ℝ (fun t : ℝ => (t, b)) a := by
        fun_prop
      simpa [Function.uncurry] using hz.comp a hm
    have hzy : DifferentiableAt ℝ (fun t : ℝ => z a t) b := by
      have hm : DifferentiableAt ℝ (fun t : ℝ => (a, t)) b := by
        fun_prop
      simpa [Function.uncurry] using hz.comp b hm
    have hmemx : ∀ᶠ t in nhds a, (t, b) ∈ D :=
      (show ContinuousAt (fun t : ℝ => (t, b)) a by fun_prop)
        (h.1.mem_nhds hq)
    have hmemy : ∀ᶠ t in nhds b, (a, t) ∈ D :=
      (show ContinuousAt (fun t : ℝ => (a, t)) b by fun_prop)
        (h.1.mem_nhds hq)
    have heqx :
        (fun t : ℝ => t + b + z t b) =ᶠ[nhds a]
          (fun t : ℝ => Real.exp (z t b)) :=
      hmemx.mono fun t ht => (h.2.2 (t, b) ht).1
    have heqy :
        (fun t : ℝ => a + t + z a t) =ᶠ[nhds b]
          (fun t : ℝ => Real.exp (z a t)) :=
      hmemy.mono fun t ht => (h.2.2 (a, t) ht).1
    have hlx : HasDerivAt (fun t : ℝ => t + b + z t b)
        (1 + partialX z a b) a := by
      simpa [partialX] using
        (((hasDerivAt_id a).add
          (hasDerivAt_const (x := a) (c := b))).add hzx.hasDerivAt)
    have hrx : HasDerivAt (fun t : ℝ => Real.exp (z t b))
        (Real.exp (z a b) * partialX z a b) a := by
      simpa [partialX] using
        (Real.hasDerivAt_exp (z a b)).comp a hzx.hasDerivAt
    have hly : HasDerivAt (fun t : ℝ => a + t + z a t)
        (1 + partialY z a b) b := by
      simpa [partialY] using
        (((hasDerivAt_const (x := b) (c := a)).add
          (hasDerivAt_id b)).add hzy.hasDerivAt)
    have hry : HasDerivAt (fun t : ℝ => Real.exp (z a t))
        (Real.exp (z a b) * partialY z a b) b := by
      simpa [partialY] using
        (Real.hasDerivAt_exp (z a b)).comp b hzy.hasDerivAt
    have hxrel : 1 + partialX z a b =
        Real.exp (z a b) * partialX z a b := by
      calc
        1 + partialX z a b =
            deriv (fun t : ℝ => t + b + z t b) a := hlx.deriv.symm
        _ = deriv (fun t : ℝ => Real.exp (z t b)) a := heqx.deriv_eq
        _ = Real.exp (z a b) * partialX z a b := hrx.deriv
    have hyrel : 1 + partialY z a b =
        Real.exp (z a b) * partialY z a b := by
      calc
        1 + partialY z a b =
            deriv (fun t : ℝ => a + t + z a t) b := hly.deriv.symm
        _ = deriv (fun t : ℝ => Real.exp (z a t)) b := heqy.deriv_eq
        _ = Real.exp (z a b) * partialY z a b := hry.deriv
    have hne : Real.exp (z a b) - 1 ≠ 0 := (h.2.2 (a, b) hq).2
    have hx : partialX z a b = 1 / (Real.exp (z a b) - 1) := by
      apply (eq_div_iff hne).2
      nlinarith [hxrel]
    have hy : partialY z a b = 1 / (Real.exp (z a b) - 1) := by
      apply (eq_div_iff hne).2
      nlinarith [hyrel]
    exact ⟨hx, hy⟩
  intro p hp
  rcases p with ⟨x, y⟩
  rcases firstAt (x, y) hp with ⟨hx, hy⟩
  have hz : DifferentiableAt ℝ (Function.uncurry z) (x, y) :=
    ((h.2.1 (x, y) hp).contDiffAt (h.1.mem_nhds hp)).differentiableAt
      (by decide)
  have hzx : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    have hm : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
      fun_prop
    simpa [Function.uncurry] using hz.comp x hm
  have hzy : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    have hm : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
      fun_prop
    simpa [Function.uncurry] using hz.comp y hm
  have hmemx : ∀ᶠ t in nhds x, (t, y) ∈ D :=
    (show ContinuousAt (fun t : ℝ => (t, y)) x by fun_prop)
      (h.1.mem_nhds hp)
  have hmemy : ∀ᶠ t in nhds y, (x, t) ∈ D :=
    (show ContinuousAt (fun t : ℝ => (x, t)) y by fun_prop)
      (h.1.mem_nhds hp)
  have hpxx :
      (fun t : ℝ => partialX z t y) =ᶠ[nhds x]
        (fun t : ℝ => 1 / (Real.exp (z t y) - 1)) :=
    hmemx.mono fun t ht => (firstAt (t, y) ht).1
  have hpxy :
      (fun t : ℝ => partialX z x t) =ᶠ[nhds y]
        (fun t : ℝ => 1 / (Real.exp (z x t) - 1)) :=
    hmemy.mono fun t ht => (firstAt (x, t) ht).1
  have hpyy :
      (fun t : ℝ => partialY z x t) =ᶠ[nhds y]
        (fun t : ℝ => 1 / (Real.exp (z x t) - 1)) :=
    hmemy.mono fun t ht => (firstAt (x, t) ht).2
  have hne : Real.exp (z x y) - 1 ≠ 0 := (h.2.2 (x, y) hp).2
  have hexpx : HasDerivAt (fun t : ℝ => Real.exp (z t y))
      (Real.exp (z x y) * partialX z x y) x := by
    simpa [partialX] using
      (Real.hasDerivAt_exp (z x y)).comp x hzx.hasDerivAt
  have hexpy : HasDerivAt (fun t : ℝ => Real.exp (z x t))
      (Real.exp (z x y) * partialY z x y) y := by
    simpa [partialY] using
      (Real.hasDerivAt_exp (z x y)).comp y hzy.hasDerivAt
  have hrxx : HasDerivAt
      (fun t : ℝ => 1 / (Real.exp (z t y) - 1))
      (-(Real.exp (z x y) * partialX z x y) /
        (Real.exp (z x y) - 1) ^ 2) x := by
    simpa [one_div] using (hexpx.sub_const 1).inv hne
  have hrxy : HasDerivAt
      (fun t : ℝ => 1 / (Real.exp (z x t) - 1))
      (-(Real.exp (z x y) * partialY z x y) /
        (Real.exp (z x y) - 1) ^ 2) y := by
    simpa [one_div] using (hexpy.sub_const 1).inv hne
  have hxxRaw : partialXX z x y =
      -(Real.exp (z x y) * partialX z x y) /
        (Real.exp (z x y) - 1) ^ 2 := by
    simpa only [partialXX] using hpxx.deriv_eq.trans hrxx.deriv
  have hxyRaw : partialXY z x y =
      -(Real.exp (z x y) * partialY z x y) /
        (Real.exp (z x y) - 1) ^ 2 := by
    simpa only [partialXY] using hpxy.deriv_eq.trans hrxy.deriv
  have hyyRaw : partialYY z x y =
      -(Real.exp (z x y) * partialY z x y) /
        (Real.exp (z x y) - 1) ^ 2 := by
    simpa only [partialYY] using hpyy.deriv_eq.trans hrxy.deriv
  have hxx : partialXX z x y =
      -(Real.exp (z x y) / (Real.exp (z x y) - 1) ^ 3) := by
    calc
      partialXX z x y =
          -(Real.exp (z x y) * (1 / (Real.exp (z x y) - 1))) /
            (Real.exp (z x y) - 1) ^ 2 := by simpa [hx] using hxxRaw
      _ = -(Real.exp (z x y) / (Real.exp (z x y) - 1) ^ 3) := by
        field_simp [hne] <;> ring
  have hxy : partialXY z x y =
      -(Real.exp (z x y) / (Real.exp (z x y) - 1) ^ 3) := by
    calc
      partialXY z x y =
          -(Real.exp (z x y) * (1 / (Real.exp (z x y) - 1))) /
            (Real.exp (z x y) - 1) ^ 2 := by simpa [hy] using hxyRaw
      _ = -(Real.exp (z x y) / (Real.exp (z x y) - 1) ^ 3) := by
        field_simp [hne] <;> ring
  have hyy : partialYY z x y =
      -(Real.exp (z x y) / (Real.exp (z x y) - 1) ^ 3) := by
    calc
      partialYY z x y =
          -(Real.exp (z x y) * (1 / (Real.exp (z x y) - 1))) /
            (Real.exp (z x y) - 1) ^ 2 := by simpa [hy] using hyyRaw
      _ = -(Real.exp (z x y) / (Real.exp (z x y) - 1) ^ 3) := by
        field_simp [hne] <;> ring
  exact ⟨hx, hy, hxx, hxy, hyy⟩

theorem gap1 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      dx + dy + firstDifferential z p.1 p.2 dx dy =
        Real.exp (z p.1 p.2) *
          firstDifferential z p.1 p.2 dx dy := by
  intro p hp dx dy
  rcases surfaceDerivatives D z h p hp with ⟨hx, hy, _, _, _⟩
  rw [firstDifferential, hx, hy]
  have hne := (h.2.2 p hp).2
  field_simp [hne] <;> ring

theorem gap2 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      firstDifferential z p.1 p.2 dx dy =
        1 / (Real.exp (z p.1 p.2) - 1) * (dx + dy) := by
  intro p hp dx dy
  rcases surfaceDerivatives D z h p hp with ⟨hx, hy, _, _, _⟩
  rw [firstDifferential, hx, hy]
  ring

theorem gap3 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      1 / (Real.exp (z p.1 p.2) - 1) * (dx + dy) =
        1 / (p.1 + p.2 + z p.1 p.2 - 1) * (dx + dy) := by
  intro p hp dx dy
  have hsurf := (h.2.2 p hp).1
  simpa [hsurf]

theorem gap4 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      firstDifferential z p.1 p.2 dx dy =
        1 / (p.1 + p.2 + z p.1 p.2 - 1) * (dx + dy) := by
  intro p hp dx dy
  exact (gap2 D z h p hp dx dy).trans (gap3 D z h p hp dx dy)

theorem gap5 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, partialX z p.1 p.2 = partialY z p.1 p.2 := by
  intro p hp
  rcases surfaceDerivatives D z h p hp with ⟨hx, hy, _, _, _⟩
  exact hx.trans hy.symm

theorem gap6 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialY z p.1 p.2 =
        1 / (p.1 + p.2 + z p.1 p.2 - 1) := by
  intro p hp
  rcases surfaceDerivatives D z h p hp with ⟨_, hy, _, _, _⟩
  have hsurf := (h.2.2 p hp).1
  simpa [hsurf] using hy

theorem gap7 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialX z p.1 p.2 =
        1 / (p.1 + p.2 + z p.1 p.2 - 1) := by
  intro p hp
  rcases surfaceDerivatives D z h p hp with ⟨hx, _, _, _, _⟩
  have hsurf := (h.2.2 p hp).1
  simpa [hsurf] using hx

theorem gap8 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      secondDifferential z p.1 p.2 dx dy =
        Real.exp (z p.1 p.2) *
            secondDifferential z p.1 p.2 dx dy +
          Real.exp (z p.1 p.2) *
            (firstDifferential z p.1 p.2 dx dy) ^ 2 := by
  intro p hp dx dy
  rcases surfaceDerivatives D z h p hp with ⟨hx, hy, hxx, hxy, hyy⟩
  rw [secondDifferential, firstDifferential, hxx, hxy, hyy, hx, hy]
  have hne := (h.2.2 p hp).2
  field_simp [hne] <;> ring

theorem gap9 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      secondDifferential z p.1 p.2 dx dy =
        -(Real.exp (z p.1 p.2) /
          (Real.exp (z p.1 p.2) - 1)) *
            (firstDifferential z p.1 p.2 dx dy) ^ 2 := by
  intro p hp dx dy
  rcases surfaceDerivatives D z h p hp with ⟨hx, hy, hxx, hxy, hyy⟩
  rw [secondDifferential, firstDifferential, hxx, hxy, hyy, hx, hy]
  have hne := (h.2.2 p hp).2
  field_simp [hne] <;> ring

theorem gap10 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      -(Real.exp (z p.1 p.2) /
          (Real.exp (z p.1 p.2) - 1)) *
            (firstDifferential z p.1 p.2 dx dy) ^ 2 =
        -(Real.exp (z p.1 p.2) /
          (Real.exp (z p.1 p.2) - 1) ^ 3) *
            (dx ^ 2 + 2 * dx * dy + dy ^ 2) := by
  intro p hp dx dy
  rcases surfaceDerivatives D z h p hp with ⟨hx, hy, _, _, _⟩
  rw [firstDifferential, hx, hy]
  have hne := (h.2.2 p hp).2
  field_simp [hne] <;> ring

theorem gap11 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      secondDifferential z p.1 p.2 dx dy =
        -(Real.exp (z p.1 p.2) /
          (Real.exp (z p.1 p.2) - 1) ^ 3) *
            (dx ^ 2 + 2 * dx * dy + dy ^ 2) := by
  intro p hp dx dy
  exact (gap9 D z h p hp dx dy).trans (gap10 D z h p hp dx dy)

theorem gap12 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialXX z p.1 p.2 = partialXY z p.1 p.2 := by
  intro p hp
  rcases surfaceDerivatives D z h p hp with ⟨_, _, hxx, hxy, _⟩
  exact hxx.trans hxy.symm

theorem gap13 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialXY z p.1 p.2 = partialYY z p.1 p.2 := by
  intro p hp
  rcases surfaceDerivatives D z h p hp with ⟨_, _, _, hxy, hyy⟩
  exact hxy.trans hyy.symm

theorem gap14 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialYY z p.1 p.2 =
        -(Real.exp (z p.1 p.2) /
          (Real.exp (z p.1 p.2) - 1) ^ 3) := by
  intro p hp
  rcases surfaceDerivatives D z h p hp with ⟨_, _, _, _, hyy⟩
  exact hyy

theorem gap15 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      -(Real.exp (z p.1 p.2) /
          (Real.exp (z p.1 p.2) - 1) ^ 3) =
        -((p.1 + p.2 + z p.1 p.2) /
          (p.1 + p.2 + z p.1 p.2 - 1) ^ 3) := by
  intro p hp
  have hsurf := (h.2.2 p hp).1
  simpa [hsurf]

theorem gap16 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialXX z p.1 p.2 =
        -((p.1 + p.2 + z p.1 p.2) /
          (p.1 + p.2 + z p.1 p.2 - 1) ^ 3) := by
  intro p hp
  calc
    partialXX z p.1 p.2 = partialXY z p.1 p.2 := gap12 D z h p hp
    _ = partialYY z p.1 p.2 := gap13 D z h p hp
    _ = -(Real.exp (z p.1 p.2) /
          (Real.exp (z p.1 p.2) - 1) ^ 3) := gap14 D z h p hp
    _ = -((p.1 + p.2 + z p.1 p.2) /
          (p.1 + p.2 + z p.1 p.2 - 1) ^ 3) := gap15 D z h p hp

end

end ProofGap.Exercise3385
