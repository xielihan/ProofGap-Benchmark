import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4275

noncomputable section

abbrev Point := ℝ × ℝ

def partialX (f : Point → ℝ) (p : Point) : ℝ :=
  deriv (fun x => f (x, p.2)) p.1

def partialY (f : Point → ℝ) (p : Point) : ℝ :=
  deriv (fun y => f (p.1, y)) p.2

def iterX : ℕ → (Point → ℝ) → Point → ℝ
  | 0, f => f
  | n + 1, f => partialX (iterX n f)

def iterY : ℕ → (Point → ℝ) → Point → ℝ
  | 0, f => f
  | m + 1, f => partialY (iterY m f)

def mixedDerivative (u : Point → ℝ) (n m : ℕ) : Point → ℝ :=
  iterY m (iterX n u)

def statedField (u : Point → ℝ) (n m : ℕ) (p : Point) : Point :=
  (mixedDerivative u (n + 1) m p, mixedDerivative u n (m + 1) p)

def coordinateDifferential (V v : Point) : ℝ :=
  V.1 * v.1 + V.2 * v.2

def differential (f : Point → ℝ) (p v : Point) : ℝ :=
  partialX f p * v.1 + partialY f p * v.2

def HasCoordinateGradientAt
    (f : Point → ℝ) (V : Point) (p : Point) : Prop :=
  HasDerivAt (fun x => f (x, p.2)) V.1 p.1 ∧
    HasDerivAt (fun y => f (p.1, y)) V.2 p.2

def CompatibleMixedDerivatives (u : Point → ℝ) (n m : ℕ) : Prop :=
  ∀ p, HasCoordinateGradientAt (mixedDerivative u n m) (statedField u n m p) p

def IsSolution (z u : Point → ℝ) (n m : ℕ) : Prop :=
  ∀ p, HasCoordinateGradientAt z (statedField u n m p) p

private theorem solution_of_add_const (u : Point → ℝ) (n m : ℕ)
    (hcompat : CompatibleMixedDerivatives u n m) (C : ℝ) :
    IsSolution (fun p => mixedDerivative u n m p + C) u n m := by
  intro p
  constructor
  · simpa using (hcompat p).1.add_const C
  · simpa using (hcompat p).2.add_const C

theorem gap1 (u : Point → ℝ) (n m : ℕ) (p v : Point) :
    coordinateDifferential (statedField u n m p) v =
      mixedDerivative u (n + 1) m p * v.1 +
        mixedDerivative u n (m + 1) p * v.2 := by
  rfl

theorem gap2 (u : Point → ℝ) (n m : ℕ)
    (hcompat : CompatibleMixedDerivatives u n m) (p v : Point) :
    coordinateDifferential (statedField u n m p) v =
      differential (mixedDerivative u n m) p v := by
  unfold coordinateDifferential differential partialX partialY
  rw [(hcompat p).1.deriv, (hcompat p).2.deriv]

theorem gap3 (z u : Point → ℝ) (n m : ℕ)
    (hcompat : CompatibleMixedDerivatives u n m) (p v : Point) :
    differential z p v =
        coordinateDifferential (statedField u n m p) v ↔
      differential z p v = differential (mixedDerivative u n m) p v := by
  rw [gap2 u n m hcompat p v]

theorem gap4 (z u : Point → ℝ) (n m : ℕ)
    (hcompat : CompatibleMixedDerivatives u n m) :
    IsSolution z u n m ↔
      ∃ C : ℝ, ∀ p, z p = mixedDerivative u n m p + C := by
  constructor
  · intro hz
    have hdx (y x : ℝ) :
        HasDerivAt
          (fun t => z (t, y) - mixedDerivative u n m (t, y)) 0 x := by
      simpa using (hz (x, y)).1.sub (hcompat (x, y)).1
    have hdy (x y : ℝ) :
        HasDerivAt
          (fun t => z (x, t) - mixedDerivative u n m (x, t)) 0 y := by
      simpa using (hz (x, y)).2.sub (hcompat (x, y)).2
    refine ⟨z (0, 0) - mixedDerivative u n m (0, 0), ?_⟩
    rintro ⟨x, y⟩
    have hx :
        z (x, y) - mixedDerivative u n m (x, y) =
          z (0, y) - mixedDerivative u n m (0, y) :=
      is_const_of_deriv_eq_zero
        (fun t => (hdx y t).differentiableAt)
        (fun t => (hdx y t).deriv) x 0
    have hy :
        z (0, y) - mixedDerivative u n m (0, y) =
          z (0, 0) - mixedDerivative u n m (0, 0) :=
      is_const_of_deriv_eq_zero
        (fun t => (hdy 0 t).differentiableAt)
        (fun t => (hdy 0 t).deriv) y 0
    have hsub :
        z (x, y) - mixedDerivative u n m (x, y) =
          z (0, 0) - mixedDerivative u n m (0, 0) :=
      hx.trans hy
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hsub)
  · rintro ⟨C, hC⟩
    have hz : z = fun p => mixedDerivative u n m p + C := funext hC
    rw [hz]
    exact solution_of_add_const u n m hcompat C

theorem gap5 (u : Point → ℝ) (n m : ℕ)
    (hcompat : CompatibleMixedDerivatives u n m) (C : ℝ) :
    IsSolution (fun p => mixedDerivative u n m p + C) u n m := by
  exact solution_of_add_const u n m hcompat C

end

end ProofGap.Exercise4275
