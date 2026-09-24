import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3415

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def jacobian2 (φ ψ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  partialX φ a b * partialY ψ a b -
    partialY φ a b * partialX ψ a b

def phiA (a b : ℝ) : ℝ :=
  a * Real.cos (b / a)

def psiA (a b : ℝ) : ℝ :=
  a * Real.sin (b / a)

def phiB (a b : ℝ) : ℝ :=
  Real.exp a + a * Real.sin b

def psiB (a b : ℝ) : ℝ :=
  Real.exp a - a * Real.cos b

def denominatorB (a b : ℝ) : ℝ :=
  Real.exp a * (Real.sin b - Real.cos b) + 1

def LocalInverse (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  DifferentiableAt ℝ (Function.uncurry u) (x, y) ∧
  DifferentiableAt ℝ (Function.uncurry v) (x, y) ∧
  (∀ᶠ p : ℝ × ℝ in nhds (x, y),
    p.1 = φ (u p.1 p.2) (v p.1 p.2)) ∧
  (∀ᶠ p : ℝ × ℝ in nhds (x, y),
    p.2 = ψ (u p.1 p.2) (v p.1 p.2))

private theorem hasDerivAt_phiA_comp
    {U V : ℝ → ℝ} {x U' V' : ℝ}
    (hU : HasDerivAt U U' x) (hV : HasDerivAt V V' x)
    (hU0 : U x ≠ 0) :
    HasDerivAt (fun t => phiA (U t) (V t))
      ((Real.cos (V x / U x) + (V x / U x) * Real.sin (V x / U x)) * U' +
        (-Real.sin (V x / U x)) * V') x := by
  unfold phiA
  have hq := hV.div hU hU0
  have hc := (Real.hasDerivAt_cos (V x / U x)).comp x hq
  convert hU.mul hc using 1 <;>
    simp only [Function.comp_apply, Pi.div_apply] <;>
    field_simp [hU0] <;> ring_nf

private theorem hasDerivAt_psiA_comp
    {U V : ℝ → ℝ} {x U' V' : ℝ}
    (hU : HasDerivAt U U' x) (hV : HasDerivAt V V' x)
    (hU0 : U x ≠ 0) :
    HasDerivAt (fun t => psiA (U t) (V t))
      ((Real.sin (V x / U x) - (V x / U x) * Real.cos (V x / U x)) * U' +
        Real.cos (V x / U x) * V') x := by
  unfold psiA
  have hq := hV.div hU hU0
  have hs := (Real.hasDerivAt_sin (V x / U x)).comp x hq
  convert hU.mul hs using 1 <;>
    simp only [Function.comp_apply, Pi.div_apply] <;>
    field_simp [hU0] <;> ring_nf

private theorem hasDerivAt_phiB_comp
    {U V : ℝ → ℝ} {x U' V' : ℝ}
    (hU : HasDerivAt U U' x) (hV : HasDerivAt V V' x) :
    HasDerivAt (fun t => phiB (U t) (V t))
      ((Real.exp (U x) + Real.sin (V x)) * U' +
        (U x * Real.cos (V x)) * V') x := by
  unfold phiB
  have he := (Real.hasDerivAt_exp (U x)).comp x hU
  have hs := (Real.hasDerivAt_sin (V x)).comp x hV
  convert he.add (hU.mul hs) using 1 <;>
    simp only [Function.comp_apply] <;> ring

private theorem hasDerivAt_psiB_comp
    {U V : ℝ → ℝ} {x U' V' : ℝ}
    (hU : HasDerivAt U U' x) (hV : HasDerivAt V V' x) :
    HasDerivAt (fun t => psiB (U t) (V t))
      ((Real.exp (U x) - Real.cos (V x)) * U' +
        (U x * Real.sin (V x)) * V') x := by
  unfold psiB
  have he := (Real.hasDerivAt_exp (U x)).comp x hU
  have hc := (Real.hasDerivAt_cos (V x)).comp x hV
  convert he.sub (hU.mul hc) using 1 <;>
    simp only [Function.comp_apply] <;> ring

private theorem inverseA_equations
    {u v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hLocal : LocalInverse phiA psiA u v x y)
    (hu : u x y ≠ 0) :
    ((Real.cos (v x y / u x y) +
          (v x y / u x y) * Real.sin (v x y / u x y)) * partialX u x y +
        (-Real.sin (v x y / u x y)) * partialX v x y = 1) ∧
    ((Real.cos (v x y / u x y) +
          (v x y / u x y) * Real.sin (v x y / u x y)) * partialY u x y +
        (-Real.sin (v x y / u x y)) * partialY v x y = 0) ∧
    ((Real.sin (v x y / u x y) -
          (v x y / u x y) * Real.cos (v x y / u x y)) * partialX u x y +
        Real.cos (v x y / u x y) * partialX v x y = 0) ∧
    ((Real.sin (v x y / u x y) -
          (v x y / u x y) * Real.cos (v x y / u x y)) * partialY u x y +
        Real.cos (v x y / u x y) * partialY v x y = 1) := by
  rcases hLocal with ⟨hdu, hdv, hφ, hψ⟩
  have hpairX : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hpairY : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hux : HasDerivAt (fun t => u t y) (partialX u x y) x := by
    apply DifferentiableAt.hasDerivAt
    simpa [Function.uncurry] using hdu.comp x hpairX
  have hvx : HasDerivAt (fun t => v t y) (partialX v x y) x := by
    apply DifferentiableAt.hasDerivAt
    simpa [Function.uncurry] using hdv.comp x hpairX
  have huy : HasDerivAt (fun t => u x t) (partialY u x y) y := by
    apply DifferentiableAt.hasDerivAt
    simpa [Function.uncurry] using hdu.comp y hpairY
  have hvy : HasDerivAt (fun t => v x t) (partialY v x y) y := by
    apply DifferentiableAt.hasDerivAt
    simpa [Function.uncurry] using hdv.comp y hpairY
  have hxφ : (fun t : ℝ => t) =ᶠ[nhds x]
      (fun t => phiA (u t y) (v t y)) :=
    hpairX.continuousAt.eventually hφ
  have hyφ : (fun _ : ℝ => x) =ᶠ[nhds y]
      (fun t => phiA (u x t) (v x t)) :=
    hpairY.continuousAt.eventually hφ
  have hxψ : (fun _ : ℝ => y) =ᶠ[nhds x]
      (fun t => psiA (u t y) (v t y)) :=
    hpairX.continuousAt.eventually hψ
  have hyψ : (fun t : ℝ => t) =ᶠ[nhds y]
      (fun t => psiA (u x t) (v x t)) :=
    hpairY.continuousAt.eventually hψ
  have eφx := (hasDerivAt_phiA_comp hux hvx hu).unique
    ((hasDerivAt_id x).congr_of_eventuallyEq hxφ.symm)
  have eφy := (hasDerivAt_phiA_comp huy hvy hu).unique
    ((hasDerivAt_const y x).congr_of_eventuallyEq hyφ.symm)
  have eψx := (hasDerivAt_psiA_comp hux hvx hu).unique
    ((hasDerivAt_const x y).congr_of_eventuallyEq hxψ.symm)
  have eψy := (hasDerivAt_psiA_comp huy hvy hu).unique
    ((hasDerivAt_id y).congr_of_eventuallyEq hyψ.symm)
  exact ⟨eφx, eφy, eψx, eψy⟩

private theorem inverseB_equations
    {u v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hLocal : LocalInverse phiB psiB u v x y) :
    ((Real.exp (u x y) + Real.sin (v x y)) * partialX u x y +
        (u x y * Real.cos (v x y)) * partialX v x y = 1) ∧
    ((Real.exp (u x y) + Real.sin (v x y)) * partialY u x y +
        (u x y * Real.cos (v x y)) * partialY v x y = 0) ∧
    ((Real.exp (u x y) - Real.cos (v x y)) * partialX u x y +
        (u x y * Real.sin (v x y)) * partialX v x y = 0) ∧
    ((Real.exp (u x y) - Real.cos (v x y)) * partialY u x y +
        (u x y * Real.sin (v x y)) * partialY v x y = 1) := by
  rcases hLocal with ⟨hdu, hdv, hφ, hψ⟩
  have hpairX : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hpairY : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hux : HasDerivAt (fun t => u t y) (partialX u x y) x := by
    apply DifferentiableAt.hasDerivAt
    simpa [Function.uncurry] using hdu.comp x hpairX
  have hvx : HasDerivAt (fun t => v t y) (partialX v x y) x := by
    apply DifferentiableAt.hasDerivAt
    simpa [Function.uncurry] using hdv.comp x hpairX
  have huy : HasDerivAt (fun t => u x t) (partialY u x y) y := by
    apply DifferentiableAt.hasDerivAt
    simpa [Function.uncurry] using hdu.comp y hpairY
  have hvy : HasDerivAt (fun t => v x t) (partialY v x y) y := by
    apply DifferentiableAt.hasDerivAt
    simpa [Function.uncurry] using hdv.comp y hpairY
  have hxφ : (fun t : ℝ => t) =ᶠ[nhds x]
      (fun t => phiB (u t y) (v t y)) :=
    hpairX.continuousAt.eventually hφ
  have hyφ : (fun _ : ℝ => x) =ᶠ[nhds y]
      (fun t => phiB (u x t) (v x t)) :=
    hpairY.continuousAt.eventually hφ
  have hxψ : (fun _ : ℝ => y) =ᶠ[nhds x]
      (fun t => psiB (u t y) (v t y)) :=
    hpairX.continuousAt.eventually hψ
  have hyψ : (fun t : ℝ => t) =ᶠ[nhds y]
      (fun t => psiB (u x t) (v x t)) :=
    hpairY.continuousAt.eventually hψ
  have eφx := (hasDerivAt_phiB_comp hux hvx).unique
    ((hasDerivAt_id x).congr_of_eventuallyEq hxφ.symm)
  have eφy := (hasDerivAt_phiB_comp huy hvy).unique
    ((hasDerivAt_const y x).congr_of_eventuallyEq hyφ.symm)
  have eψx := (hasDerivAt_psiB_comp hux hvx).unique
    ((hasDerivAt_const x y).congr_of_eventuallyEq hxψ.symm)
  have eψy := (hasDerivAt_psiB_comp huy hvy).unique
    ((hasDerivAt_id y).congr_of_eventuallyEq hyψ.symm)
  exact ⟨eφx, eφy, eψx, eψy⟩

private theorem solve_inverse11 {p q r s α β : ℝ}
    (h1 : p * α + q * β = 1) (h2 : r * α + s * β = 0)
    (hdet : p * s - q * r ≠ 0) :
    α = s / (p * s - q * r) := by
  apply (eq_div_iff hdet).2
  calc
    α * (p * s - q * r) =
        s * (p * α + q * β) - q * (r * α + s * β) := by ring
    _ = s := by rw [h1, h2]; ring

private theorem solve_inverse12 {p q r s α β : ℝ}
    (h1 : p * α + q * β = 0) (h2 : r * α + s * β = 1)
    (hdet : p * s - q * r ≠ 0) :
    α = -q / (p * s - q * r) := by
  apply (eq_div_iff hdet).2
  calc
    α * (p * s - q * r) =
        s * (p * α + q * β) - q * (r * α + s * β) := by ring
    _ = -q := by rw [h1, h2]; ring

private theorem solve_inverse21 {p q r s α β : ℝ}
    (h1 : p * α + q * β = 1) (h2 : r * α + s * β = 0)
    (hdet : p * s - q * r ≠ 0) :
    β = -r / (p * s - q * r) := by
  apply (eq_div_iff hdet).2
  calc
    β * (p * s - q * r) =
        -r * (p * α + q * β) + p * (r * α + s * β) := by ring
    _ = -r := by rw [h1, h2]; ring

private theorem solve_inverse22 {p q r s α β : ℝ}
    (h1 : p * α + q * β = 0) (h2 : r * α + s * β = 1)
    (hdet : p * s - q * r ≠ 0) :
    β = p / (p * s - q * r) := by
  apply (eq_div_iff hdet).2
  calc
    β * (p * s - q * r) =
        -r * (p * α + q * β) + p * (r * α + s * β) := by ring
    _ = p := by rw [h1, h2]; ring

theorem gap1 (a b : ℝ) (ha : a ≠ 0) :
    partialX phiA a b =
      Real.cos (b / a) + (b / a) * Real.sin (b / a) := by
  simpa [partialX] using
    (hasDerivAt_phiA_comp (hasDerivAt_id a) (hasDerivAt_const a b) ha).deriv

theorem gap2 (a b : ℝ) (ha : a ≠ 0) :
    partialY phiA a b = -Real.sin (b / a) := by
  simpa [partialY] using
    (hasDerivAt_phiA_comp (hasDerivAt_const b a) (hasDerivAt_id b) ha).deriv

theorem gap3 (a b : ℝ) (ha : a ≠ 0) :
    partialX psiA a b =
      Real.sin (b / a) - (b / a) * Real.cos (b / a) := by
  simpa [partialX] using
    (hasDerivAt_psiA_comp (hasDerivAt_id a) (hasDerivAt_const a b) ha).deriv

theorem gap4 (a b : ℝ) (ha : a ≠ 0) :
    partialY psiA a b = Real.cos (b / a) := by
  simpa [partialY] using
    (hasDerivAt_psiA_comp (hasDerivAt_const b a) (hasDerivAt_id b) ha).deriv

theorem gap5 (a b : ℝ) :
    jacobian2 phiA psiA a b =
      partialX phiA a b * partialY psiA a b -
        partialY phiA a b * partialX psiA a b := by
  rfl

theorem gap6 (a b : ℝ) (ha : a ≠ 0)
    (hφa : partialX phiA a b =
      Real.cos (b / a) + (b / a) * Real.sin (b / a))
    (hφb : partialY phiA a b = -Real.sin (b / a))
    (hψa : partialX psiA a b =
      Real.sin (b / a) - (b / a) * Real.cos (b / a))
    (hψb : partialY psiA a b = Real.cos (b / a)) :
    partialX phiA a b * partialY psiA a b -
      partialY phiA a b * partialX psiA a b = 1 := by
  rw [hφa, hφb, hψa, hψb]
  nlinarith [Real.sin_sq_add_cos_sq (b / a)]

theorem gap7 (a b I : ℝ)
    (hI : I = jacobian2 phiA psiA a b)
    (hJac : jacobian2 phiA psiA a b = 1) :
    I = 1 := by
  exact hI.trans hJac

theorem gap8 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hLocal : LocalInverse phiA psiA u v x y)
    (hu : u x y ≠ 0)
    (hJac : jacobian2 phiA psiA (u x y) (v x y) ≠ 0) :
    partialX u x y =
      partialY psiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) := by
  rcases inverseA_equations hLocal hu with ⟨eφx, eφy, eψx, eψy⟩
  have h1 :
      partialX phiA (u x y) (v x y) * partialX u x y +
        partialY phiA (u x y) (v x y) * partialX v x y = 1 := by
    simpa [gap1 (u x y) (v x y) hu, gap2 (u x y) (v x y) hu] using eφx
  have h2 :
      partialX psiA (u x y) (v x y) * partialX u x y +
        partialY psiA (u x y) (v x y) * partialX v x y = 0 := by
    simpa [gap3 (u x y) (v x y) hu, gap4 (u x y) (v x y) hu] using eψx
  exact solve_inverse11 h1 h2 hJac

theorem gap9 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : u x y ≠ 0)
    (hJac : jacobian2 phiA psiA (u x y) (v x y) = 1)
    (hψ : partialY psiA (u x y) (v x y) =
      Real.cos (v x y / u x y)) :
    partialY psiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) =
      Real.cos (v x y / u x y) := by
  simpa [hJac] using hψ

theorem gap10 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialX u x y =
      partialY psiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y))
    (h2 : partialY psiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) =
      Real.cos (v x y / u x y)) :
    partialX u x y = Real.cos (v x y / u x y) := by
  exact h1.trans h2

theorem gap11 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hLocal : LocalInverse phiA psiA u v x y)
    (hu : u x y ≠ 0)
    (hJac : jacobian2 phiA psiA (u x y) (v x y) ≠ 0) :
    partialY u x y =
      -partialY phiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) := by
  rcases inverseA_equations hLocal hu with ⟨eφx, eφy, eψx, eψy⟩
  have h1 :
      partialX phiA (u x y) (v x y) * partialY u x y +
        partialY phiA (u x y) (v x y) * partialY v x y = 0 := by
    simpa [gap1 (u x y) (v x y) hu, gap2 (u x y) (v x y) hu] using eφy
  have h2 :
      partialX psiA (u x y) (v x y) * partialY u x y +
        partialY psiA (u x y) (v x y) * partialY v x y = 1 := by
    simpa [gap3 (u x y) (v x y) hu, gap4 (u x y) (v x y) hu] using eψy
  exact solve_inverse12 h1 h2 hJac

theorem gap12 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : u x y ≠ 0)
    (hJac : jacobian2 phiA psiA (u x y) (v x y) = 1)
    (hφ : partialY phiA (u x y) (v x y) =
      -Real.sin (v x y / u x y)) :
    -partialY phiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) =
      Real.sin (v x y / u x y) := by
  rw [hJac, hφ]
  ring

theorem gap13 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialY u x y =
      -partialY phiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y))
    (h2 : -partialY phiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) =
      Real.sin (v x y / u x y)) :
    partialY u x y = Real.sin (v x y / u x y) := by
  exact h1.trans h2

theorem gap14 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hLocal : LocalInverse phiA psiA u v x y)
    (hu : u x y ≠ 0)
    (hJac : jacobian2 phiA psiA (u x y) (v x y) ≠ 0) :
    partialX v x y =
      -partialX psiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) := by
  rcases inverseA_equations hLocal hu with ⟨eφx, eφy, eψx, eψy⟩
  have h1 :
      partialX phiA (u x y) (v x y) * partialX u x y +
        partialY phiA (u x y) (v x y) * partialX v x y = 1 := by
    simpa [gap1 (u x y) (v x y) hu, gap2 (u x y) (v x y) hu] using eφx
  have h2 :
      partialX psiA (u x y) (v x y) * partialX u x y +
        partialY psiA (u x y) (v x y) * partialX v x y = 0 := by
    simpa [gap3 (u x y) (v x y) hu, gap4 (u x y) (v x y) hu] using eψx
  exact solve_inverse21 h1 h2 hJac

theorem gap15 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : u x y ≠ 0)
    (hJac : jacobian2 phiA psiA (u x y) (v x y) = 1)
    (hψ : partialX psiA (u x y) (v x y) =
      Real.sin (v x y / u x y) -
        (v x y / u x y) * Real.cos (v x y / u x y)) :
    -partialX psiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) =
      (v x y / u x y) * Real.cos (v x y / u x y) -
        Real.sin (v x y / u x y) := by
  rw [hJac, hψ]
  ring

theorem gap16 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialX v x y =
      -partialX psiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y))
    (h2 : -partialX psiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) =
      (v x y / u x y) * Real.cos (v x y / u x y) -
        Real.sin (v x y / u x y)) :
    partialX v x y =
      (v x y / u x y) * Real.cos (v x y / u x y) -
        Real.sin (v x y / u x y) := by
  exact h1.trans h2

theorem gap17 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hLocal : LocalInverse phiA psiA u v x y)
    (hu : u x y ≠ 0)
    (hJac : jacobian2 phiA psiA (u x y) (v x y) ≠ 0) :
    partialY v x y =
      partialX phiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) := by
  rcases inverseA_equations hLocal hu with ⟨eφx, eφy, eψx, eψy⟩
  have h1 :
      partialX phiA (u x y) (v x y) * partialY u x y +
        partialY phiA (u x y) (v x y) * partialY v x y = 0 := by
    simpa [gap1 (u x y) (v x y) hu, gap2 (u x y) (v x y) hu] using eφy
  have h2 :
      partialX psiA (u x y) (v x y) * partialY u x y +
        partialY psiA (u x y) (v x y) * partialY v x y = 1 := by
    simpa [gap3 (u x y) (v x y) hu, gap4 (u x y) (v x y) hu] using eψy
  exact solve_inverse22 h1 h2 hJac

theorem gap18 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : u x y ≠ 0)
    (hJac : jacobian2 phiA psiA (u x y) (v x y) = 1)
    (hφ : partialX phiA (u x y) (v x y) =
      Real.cos (v x y / u x y) +
        (v x y / u x y) * Real.sin (v x y / u x y)) :
    partialX phiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) =
      (v x y / u x y) * Real.sin (v x y / u x y) +
        Real.cos (v x y / u x y) := by
  rw [hJac, hφ]
  ring

theorem gap19 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialY v x y =
      partialX phiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y))
    (h2 : partialX phiA (u x y) (v x y) /
        jacobian2 phiA psiA (u x y) (v x y) =
      (v x y / u x y) * Real.sin (v x y / u x y) +
        Real.cos (v x y / u x y)) :
    partialY v x y =
      (v x y / u x y) * Real.sin (v x y / u x y) +
        Real.cos (v x y / u x y) := by
  exact h1.trans h2

theorem gap20 (a b : ℝ) :
    partialX phiB a b = Real.exp a + Real.sin b := by
  simpa [partialX] using
    (hasDerivAt_phiB_comp (hasDerivAt_id a) (hasDerivAt_const a b)).deriv

theorem gap21 (a b : ℝ) :
    partialY phiB a b = a * Real.cos b := by
  simpa [partialY] using
    (hasDerivAt_phiB_comp (hasDerivAt_const b a) (hasDerivAt_id b)).deriv

theorem gap22 (a b : ℝ) :
    partialX psiB a b = Real.exp a - Real.cos b := by
  simpa [partialX] using
    (hasDerivAt_psiB_comp (hasDerivAt_id a) (hasDerivAt_const a b)).deriv

theorem gap23 (a b : ℝ) :
    partialY psiB a b = a * Real.sin b := by
  simpa [partialY] using
    (hasDerivAt_psiB_comp (hasDerivAt_const b a) (hasDerivAt_id b)).deriv

theorem gap24 (a b : ℝ)
    (hφa : partialX phiB a b = Real.exp a + Real.sin b)
    (hφb : partialY phiB a b = a * Real.cos b)
    (hψa : partialX psiB a b = Real.exp a - Real.cos b)
    (hψb : partialY psiB a b = a * Real.sin b) :
    jacobian2 phiB psiB a b =
      (Real.exp a + Real.sin b) * (a * Real.sin b) -
        (a * Real.cos b) * (Real.exp a - Real.cos b) := by
  unfold jacobian2
  rw [hφa, hφb, hψa, hψb]

theorem gap25 (a b : ℝ) :
    (Real.exp a + Real.sin b) * (a * Real.sin b) -
        (a * Real.cos b) * (Real.exp a - Real.cos b) =
      a * denominatorB a b := by
  unfold denominatorB
  calc
    (Real.exp a + Real.sin b) * (a * Real.sin b) -
        (a * Real.cos b) * (Real.exp a - Real.cos b) =
      a * (Real.exp a * (Real.sin b - Real.cos b) +
        (Real.sin b ^ 2 + Real.cos b ^ 2)) := by ring
    _ = a * (Real.exp a * (Real.sin b - Real.cos b) + 1) := by
      rw [Real.sin_sq_add_cos_sq]

theorem gap26 (a b : ℝ)
    (h1 : jacobian2 phiB psiB a b =
      (Real.exp a + Real.sin b) * (a * Real.sin b) -
        (a * Real.cos b) * (Real.exp a - Real.cos b))
    (h2 : (Real.exp a + Real.sin b) * (a * Real.sin b) -
        (a * Real.cos b) * (Real.exp a - Real.cos b) =
      a * denominatorB a b) :
    jacobian2 phiB psiB a b = a * denominatorB a b := by
  exact h1.trans h2

theorem gap27 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hLocal : LocalInverse phiB psiB u v x y)
    (hu : u x y ≠ 0)
    (hDen : denominatorB (u x y) (v x y) ≠ 0) :
    partialX u x y =
      Real.sin (v x y) / denominatorB (u x y) (v x y) := by
  rcases inverseB_equations hLocal with ⟨eφx, eφy, eψx, eψy⟩
  have h1 :
      partialX phiB (u x y) (v x y) * partialX u x y +
        partialY phiB (u x y) (v x y) * partialX v x y = 1 := by
    simpa [gap20 (u x y) (v x y), gap21 (u x y) (v x y)] using eφx
  have h2 :
      partialX psiB (u x y) (v x y) * partialX u x y +
        partialY psiB (u x y) (v x y) * partialX v x y = 0 := by
    simpa [gap22 (u x y) (v x y), gap23 (u x y) (v x y)] using eψx
  have hJ : jacobian2 phiB psiB (u x y) (v x y) =
      u x y * denominatorB (u x y) (v x y) := by
    exact gap26 _ _ (gap24 _ _ (gap20 _ _) (gap21 _ _) (gap22 _ _) (gap23 _ _)) (gap25 _ _)
  have hJne : jacobian2 phiB psiB (u x y) (v x y) ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero hu hDen
  calc
    partialX u x y =
        partialY psiB (u x y) (v x y) /
          jacobian2 phiB psiB (u x y) (v x y) :=
      solve_inverse11 h1 h2 hJne
    _ = Real.sin (v x y) / denominatorB (u x y) (v x y) := by
      rw [gap23, hJ]
      field_simp [hu, hDen]

theorem gap28 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hLocal : LocalInverse phiB psiB u v x y)
    (hu : u x y ≠ 0)
    (hDen : denominatorB (u x y) (v x y) ≠ 0) :
    partialY u x y =
      -Real.cos (v x y) / denominatorB (u x y) (v x y) := by
  rcases inverseB_equations hLocal with ⟨eφx, eφy, eψx, eψy⟩
  have h1 :
      partialX phiB (u x y) (v x y) * partialY u x y +
        partialY phiB (u x y) (v x y) * partialY v x y = 0 := by
    simpa [gap20 (u x y) (v x y), gap21 (u x y) (v x y)] using eφy
  have h2 :
      partialX psiB (u x y) (v x y) * partialY u x y +
        partialY psiB (u x y) (v x y) * partialY v x y = 1 := by
    simpa [gap22 (u x y) (v x y), gap23 (u x y) (v x y)] using eψy
  have hJ : jacobian2 phiB psiB (u x y) (v x y) =
      u x y * denominatorB (u x y) (v x y) := by
    exact gap26 _ _ (gap24 _ _ (gap20 _ _) (gap21 _ _) (gap22 _ _) (gap23 _ _)) (gap25 _ _)
  have hJne : jacobian2 phiB psiB (u x y) (v x y) ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero hu hDen
  calc
    partialY u x y =
        -partialY phiB (u x y) (v x y) /
          jacobian2 phiB psiB (u x y) (v x y) :=
      solve_inverse12 h1 h2 hJne
    _ = -Real.cos (v x y) / denominatorB (u x y) (v x y) := by
      rw [gap21, hJ]
      field_simp [hu, hDen]

theorem gap29 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hLocal : LocalInverse phiB psiB u v x y)
    (hu : u x y ≠ 0)
    (hDen : denominatorB (u x y) (v x y) ≠ 0) :
    partialX v x y =
      -(Real.exp (u x y) - Real.cos (v x y)) /
        (u x y * denominatorB (u x y) (v x y)) := by
  rcases inverseB_equations hLocal with ⟨eφx, eφy, eψx, eψy⟩
  have h1 :
      partialX phiB (u x y) (v x y) * partialX u x y +
        partialY phiB (u x y) (v x y) * partialX v x y = 1 := by
    simpa [gap20 (u x y) (v x y), gap21 (u x y) (v x y)] using eφx
  have h2 :
      partialX psiB (u x y) (v x y) * partialX u x y +
        partialY psiB (u x y) (v x y) * partialX v x y = 0 := by
    simpa [gap22 (u x y) (v x y), gap23 (u x y) (v x y)] using eψx
  have hJ : jacobian2 phiB psiB (u x y) (v x y) =
      u x y * denominatorB (u x y) (v x y) := by
    exact gap26 _ _ (gap24 _ _ (gap20 _ _) (gap21 _ _) (gap22 _ _) (gap23 _ _)) (gap25 _ _)
  have hJne : jacobian2 phiB psiB (u x y) (v x y) ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero hu hDen
  calc
    partialX v x y =
        -partialX psiB (u x y) (v x y) /
          jacobian2 phiB psiB (u x y) (v x y) :=
      solve_inverse21 h1 h2 hJne
    _ = -(Real.exp (u x y) - Real.cos (v x y)) /
          (u x y * denominatorB (u x y) (v x y)) := by
      rw [gap22, hJ]

theorem gap30 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hLocal : LocalInverse phiB psiB u v x y)
    (hu : u x y ≠ 0)
    (hDen : denominatorB (u x y) (v x y) ≠ 0) :
    partialY v x y =
      (Real.exp (u x y) + Real.sin (v x y)) /
        (u x y * denominatorB (u x y) (v x y)) := by
  rcases inverseB_equations hLocal with ⟨eφx, eφy, eψx, eψy⟩
  have h1 :
      partialX phiB (u x y) (v x y) * partialY u x y +
        partialY phiB (u x y) (v x y) * partialY v x y = 0 := by
    simpa [gap20 (u x y) (v x y), gap21 (u x y) (v x y)] using eφy
  have h2 :
      partialX psiB (u x y) (v x y) * partialY u x y +
        partialY psiB (u x y) (v x y) * partialY v x y = 1 := by
    simpa [gap22 (u x y) (v x y), gap23 (u x y) (v x y)] using eψy
  have hJ : jacobian2 phiB psiB (u x y) (v x y) =
      u x y * denominatorB (u x y) (v x y) := by
    exact gap26 _ _ (gap24 _ _ (gap20 _ _) (gap21 _ _) (gap22 _ _) (gap23 _ _)) (gap25 _ _)
  have hJne : jacobian2 phiB psiB (u x y) (v x y) ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero hu hDen
  calc
    partialY v x y =
        partialX phiB (u x y) (v x y) /
          jacobian2 phiB psiB (u x y) (v x y) :=
      solve_inverse22 h1 h2 hJne
    _ = (Real.exp (u x y) + Real.sin (v x y)) /
          (u x y * denominatorB (u x y) (v x y)) := by
      rw [gap20, hJ]

end

end ProofGap.Exercise3415
