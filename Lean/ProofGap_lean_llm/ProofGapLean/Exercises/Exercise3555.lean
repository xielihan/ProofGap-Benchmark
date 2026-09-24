import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3555

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def radius (p : Point3) : ℝ :=
  Real.sqrt (p.x ^ 2 + p.y ^ 2)

def graphFunction (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  f (Real.sqrt (x ^ 2 + y ^ 2))

def surface (f : ℝ → ℝ) : Set Point3 :=
  {p | p.z = graphFunction f p.x p.y}

def partialX (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => graphFunction f t y) x

def partialY (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => graphFunction f x t) y

def normalVector (f : ℝ → ℝ) (p : Point3) : Point3 :=
  ⟨partialX f p.x p.y, partialY f p.x p.y, -1⟩

def scaledNormal (f : ℝ → ℝ) (p : Point3) : Point3 :=
  ⟨p.x * deriv f (radius p), p.y * deriv f (radius p), -radius p⟩

def normalLine (f : ℝ → ℝ) (p : Point3) : Set Point3 :=
  {q | ∃ t : ℝ,
    q = ⟨p.x + t * (normalVector f p).x,
      p.y + t * (normalVector f p).y,
      p.z + t * (normalVector f p).z⟩}

def axisIntersection (f : ℝ → ℝ) (p : Point3) : Point3 :=
  ⟨0, 0, f (radius p) + radius p / deriv f (radius p)⟩

def zAxis : Set Point3 :=
  {p | p.x = 0 ∧ p.y = 0}

private theorem point3_extensionality {p q : Point3}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p with
  | mk px py pz =>
    cases q with
    | mk qx qy qz =>
      simp_all

private theorem radial_deriv_formula
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x c : ℝ)
    (hr : Real.sqrt (x ^ 2 + c) ≠ 0) :
    deriv (fun t : ℝ => f (Real.sqrt (t ^ 2 + c))) x =
      (x * deriv f (Real.sqrt (x ^ 2 + c))) /
        Real.sqrt (x ^ 2 + c) := by
  have hbase : x ^ 2 + c ≠ 0 := by
    intro h
    apply hr
    simp [h]
  have hinner :
      HasDerivAt (fun t : ℝ => t ^ 2 + c) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).add_const c
  have hsqrt0 :=
    (Real.hasDerivAt_sqrt hbase).comp x hinner
  have hcoef :
      1 / (2 * Real.sqrt (x ^ 2 + c)) * (2 * x) =
        x / Real.sqrt (x ^ 2 + c) := by
    field_simp [hr] <;> ring
  rw [hcoef] at hsqrt0
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + c))
        (x / Real.sqrt (x ^ 2 + c)) x := by
    simpa [Function.comp_def] using hsqrt0
  have hcomp :=
    (hf (Real.sqrt (x ^ 2 + c))).hasDerivAt.comp x hsqrt
  have hcoef' :
      deriv f (Real.sqrt (x ^ 2 + c)) *
          (x / Real.sqrt (x ^ 2 + c)) =
        (x * deriv f (Real.sqrt (x ^ 2 + c))) /
          Real.sqrt (x ^ 2 + c) := by
    ring
  simpa [Function.comp_def, hcoef'] using hcomp.deriv

theorem gap1 (f : ℝ → ℝ) :
    ∀ p : Point3, p ∈ surface f →
      normalVector f p =
        ⟨partialX f p.x p.y, partialY f p.x p.y, -1⟩ := by
  intro p hp
  rfl

theorem gap2 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ p : Point3, p ∈ surface f → radius p ≠ 0 →
      normalVector f p =
        ⟨(p.x * deriv f (radius p)) / radius p,
          (p.y * deriv f (radius p)) / radius p, -1⟩ := by
  intro p hp hr
  apply point3_extensionality
  · change partialX f p.x p.y =
      (p.x * deriv f (radius p)) / radius p
    simpa [partialX, graphFunction, radius] using
      (radial_deriv_formula f hf p.x (p.y ^ 2) (by
        simpa only [radius] using hr))
  · change deriv (fun t : ℝ => f (Real.sqrt (p.x ^ 2 + t ^ 2))) p.y =
      (p.y * deriv f (radius p)) / radius p
    have hrad :
        Real.sqrt (p.y ^ 2 + p.x ^ 2) = radius p := by
      simp only [radius]
      rw [add_comm]
    have hformula :=
      radial_deriv_formula f hf p.y (p.x ^ 2) (by
        simpa only [hrad] using hr)
    rw [hrad] at hformula
    have hfun :
        (fun t : ℝ => f (Real.sqrt (p.x ^ 2 + t ^ 2))) =
          (fun t : ℝ => f (Real.sqrt (t ^ 2 + p.x ^ 2))) := by
      funext t
      rw [add_comm]
    rw [hfun]
    exact hformula
  · rfl

theorem gap3 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ p : Point3, p ∈ surface f → radius p ≠ 0 →
      normalVector f p =
        ⟨(scaledNormal f p).x / radius p,
          (scaledNormal f p).y / radius p,
          (scaledNormal f p).z / radius p⟩ := by
  intro p hp hr
  rw [gap2 f hf p hp hr]
  apply point3_extensionality <;> simp [scaledNormal, hr]

theorem gap4 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ p : Point3, p ∈ surface f → radius p ≠ 0 →
      normalLine f p =
        {q | ∃ t : ℝ,
          q = ⟨p.x + t * (p.x * deriv f (radius p)),
            p.y + t * (p.y * deriv f (radius p)),
            p.z - t * radius p⟩} := by
  intro p hp hr
  apply Set.ext
  intro q
  change
    (∃ t : ℝ,
      q = ⟨p.x + t * (normalVector f p).x,
        p.y + t * (normalVector f p).y,
        p.z + t * (normalVector f p).z⟩) ↔
      ∃ t : ℝ,
        q = ⟨p.x + t * (p.x * deriv f (radius p)),
          p.y + t * (p.y * deriv f (radius p)),
          p.z - t * radius p⟩
  rw [gap3 f hf p hp hr]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t / radius p, ?_⟩
    rw [ht]
    apply point3_extensionality <;> dsimp [scaledNormal] <;>
      field_simp [hr] <;> ring
  · rintro ⟨t, ht⟩
    refine ⟨t * radius p, ?_⟩
    rw [ht]
    apply point3_extensionality <;> dsimp [scaledNormal] <;>
      field_simp [hr] <;> ring

theorem gap5 (f : ℝ → ℝ) :
    ∀ p : Point3, p ∈ surface f → deriv f (radius p) ≠ 0 →
      axisIntersection f p =
        ⟨0, 0, f (radius p) + radius p / deriv f (radius p)⟩ := by
  intro p hp hd
  rfl

theorem gap6 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ p : Point3, p ∈ surface f → radius p ≠ 0 →
      deriv f (radius p) ≠ 0 →
      axisIntersection f p ∈ normalLine f p := by
  intro p hp hr hd
  have hpz : p.z = f (radius p) := by
    change p.z = f (radius p) at hp
    exact hp
  rw [gap4 f hf p hp hr]
  change
    ∃ t : ℝ,
      axisIntersection f p =
        ⟨p.x + t * (p.x * deriv f (radius p)),
          p.y + t * (p.y * deriv f (radius p)),
          p.z - t * radius p⟩
  refine ⟨-1 / deriv f (radius p), ?_⟩
  apply point3_extensionality
  · dsimp [axisIntersection]
    field_simp [hd] <;> ring
  · dsimp [axisIntersection]
    field_simp [hd] <;> ring
  · dsimp [axisIntersection]
    rw [hpz]
    field_simp [hd] <;> ring

theorem gap7 (f : ℝ → ℝ) :
    ∀ p : Point3, p ∈ surface f →
      axisIntersection f p ∈ zAxis := by
  intro p hp
  exact ⟨rfl, rfl⟩

theorem gap8 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ p : Point3, p ∈ surface f → radius p ≠ 0 →
      deriv f (radius p) ≠ 0 →
      ∃ q : Point3, q ∈ normalLine f p ∧ q ∈ zAxis := by
  intro p hp hr hd
  refine ⟨axisIntersection f p, ?_, ?_⟩
  · exact gap6 f hf p hp hr hd
  · exact gap7 f p hp

end

end ProofGap.Exercise3555
