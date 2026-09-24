import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3458

noncomputable section

def px (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f s y) x

def py (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f x s) y

private theorem deriv_comp_pair
    (F : ℝ × ℝ → ℝ) (a b : ℝ → ℝ) (x : ℝ)
    (hF : DifferentiableAt ℝ F (a x, b x))
    (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    deriv (fun s => F (a s, b s)) x =
      deriv (fun u => F (u, b x)) (a x) * deriv a x +
        deriv (fun v => F (a x, v)) (b x) * deriv b x := by
  have hab :
      fderiv ℝ (fun s => (a s, b s)) x 1 =
        (deriv a x, deriv b x) := by
    rw [(ha.hasFDerivAt.prodMk hb.hasFDerivAt).fderiv]
    rfl
  have htotal :
      deriv (fun s => F (a s, b s)) x =
        fderiv ℝ F (a x, b x) (deriv a x, deriv b x) := by
    change
      fderiv ℝ (fun s => F (a s, b s)) x 1 =
        fderiv ℝ F (a x, b x) (deriv a x, deriv b x)
    rw [show (fun s => F (a s, b s)) =
        F ∘ (fun s => (a s, b s)) by rfl]
    rw [fderiv_comp x hF (ha.prodMk hb)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hab]
  have hxpart :
      deriv (fun u => F (u, b x)) (a x) =
        fderiv ℝ F (a x, b x) (1, 0) := by
    have hc : DifferentiableAt ℝ (fun _ : ℝ => b x) (a x) :=
      differentiableAt_const (c := b x)
    have hid : DifferentiableAt ℝ (fun u : ℝ => u) (a x) :=
      differentiableAt_id
    have hin : DifferentiableAt ℝ (fun u : ℝ => (u, b x)) (a x) :=
      hid.prodMk hc
    have hinner :
        fderiv ℝ (fun u : ℝ => (u, b x)) (a x) 1 = (1, 0) := by
      rw [(hid.hasFDerivAt.prodMk hc.hasFDerivAt).fderiv]
      change
        (deriv (id : ℝ → ℝ) (a x),
          deriv (fun _ : ℝ => b x) (a x)) = (1, 0)
      rw [(hasDerivAt_id (a x)).deriv,
        (hasDerivAt_const (x := a x) (c := b x)).deriv]
    change
      fderiv ℝ (fun u => F (u, b x)) (a x) 1 =
        fderiv ℝ F (a x, b x) (1, 0)
    rw [show (fun u => F (u, b x)) =
        F ∘ (fun u => (u, b x)) by rfl]
    rw [fderiv_comp (a x) hF hin]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hinner]
  have hypart :
      deriv (fun v => F (a x, v)) (b x) =
        fderiv ℝ F (a x, b x) (0, 1) := by
    have hc : DifferentiableAt ℝ (fun _ : ℝ => a x) (b x) :=
      differentiableAt_const (c := a x)
    have hid : DifferentiableAt ℝ (fun v : ℝ => v) (b x) :=
      differentiableAt_id
    have hin : DifferentiableAt ℝ (fun v : ℝ => (a x, v)) (b x) :=
      hc.prodMk hid
    have hinner :
        fderiv ℝ (fun v : ℝ => (a x, v)) (b x) 1 = (0, 1) := by
      rw [(hc.hasFDerivAt.prodMk hid.hasFDerivAt).fderiv]
      change
        (deriv (fun _ : ℝ => a x) (b x),
          deriv (id : ℝ → ℝ) (b x)) = (0, 1)
      rw [(hasDerivAt_const (x := b x) (c := a x)).deriv,
        (hasDerivAt_id (b x)).deriv]
    change
      fderiv ℝ (fun v => F (a x, v)) (b x) 1 =
        fderiv ℝ F (a x, b x) (0, 1)
    rw [show (fun v => F (a x, v)) =
        F ∘ (fun v => (a x, v)) by rfl]
    rw [fderiv_comp (b x) hF hin]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hinner]
  rw [htotal]
  rw [show (deriv a x, deriv b x) =
      (deriv a x) • (1, 0) + (deriv b x) • (0, 1) by
        ext <;> simp]
  rw [map_add, map_smul, map_smul, ← hxpart, ← hypart]
  simpa [smul_eq_mul, mul_comm]

theorem gap1 (z Z ξ η : ℝ → ℝ → ℝ)
    (hCompose : ∀ x y, z x y = Z (ξ x y) (η x y))
    (hZ : ContDiff ℝ 1 (Function.uncurry Z))
    (hξ : ContDiff ℝ 1 (Function.uncurry ξ))
    (hη : ContDiff ℝ 1 (Function.uncurry η)) :
    ∀ x y,
      px z x y =
        px Z (ξ x y) (η x y) * px ξ x y +
          py Z (ξ x y) (η x y) * px η x y := by
  intro x y
  unfold px py
  have hz :
      (fun s => z s y) =
        (fun s => Z (ξ s y) (η s y)) := by
    funext s
    exact hCompose s y
  rw [hz]
  have hy : DifferentiableAt ℝ (fun _ : ℝ => y) x :=
    differentiableAt_const (c := y)
  have hpair : DifferentiableAt ℝ (fun s : ℝ => (s, y)) x :=
    differentiableAt_id.prodMk hy
  have hξ' : DifferentiableAt ℝ (fun s => ξ s y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      ((hξ.differentiable one_ne_zero) (x, y)).comp x hpair
  have hη' : DifferentiableAt ℝ (fun s => η s y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      ((hη.differentiable one_ne_zero) (x, y)).comp x hpair
  exact deriv_comp_pair
    (F := Function.uncurry Z) (a := fun s => ξ s y)
    (b := fun s => η s y) (x := x)
    ((hZ.differentiable one_ne_zero) (ξ x y, η x y)) hξ' hη'

theorem gap2 (z Z ξ η : ℝ → ℝ → ℝ)
    (hCompose : ∀ x y, z x y = Z (ξ x y) (η x y))
    (hZ : ContDiff ℝ 1 (Function.uncurry Z))
    (hξ : ContDiff ℝ 1 (Function.uncurry ξ))
    (hη : ContDiff ℝ 1 (Function.uncurry η)) :
    ∀ x y,
      py z x y =
        px Z (ξ x y) (η x y) * py ξ x y +
          py Z (ξ x y) (η x y) * py η x y := by
  intro x y
  unfold px py
  have hz :
      (fun s => z x s) =
        (fun s => Z (ξ x s) (η x s)) := by
    funext s
    exact hCompose x s
  rw [hz]
  have hx : DifferentiableAt ℝ (fun _ : ℝ => x) y :=
    differentiableAt_const (c := x)
  have hpair : DifferentiableAt ℝ (fun s : ℝ => (x, s)) y :=
    hx.prodMk differentiableAt_id
  have hξ' : DifferentiableAt ℝ (fun s => ξ x s) y := by
    simpa [Function.comp_def, Function.uncurry] using
      ((hξ.differentiable one_ne_zero) (x, y)).comp y hpair
  have hη' : DifferentiableAt ℝ (fun s => η x s) y := by
    simpa [Function.comp_def, Function.uncurry] using
      ((hη.differentiable one_ne_zero) (x, y)).comp y hpair
  exact deriv_comp_pair
    (F := Function.uncurry Z) (a := fun s => ξ x s)
    (b := fun s => η x s) (x := y)
    ((hZ.differentiable one_ne_zero) (ξ x y, η x y)) hξ' hη'

theorem gap3 (ξ : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x + y) :
    ∀ x y, px ξ x y = py ξ x y := by
  intro x y
  unfold px py
  rw [show (fun s => ξ s y) = (fun s => s + y) by
    funext s
    exact hξ s y]
  rw [show (fun s => ξ x s) = (fun s => x + s) by
    funext s
    exact hξ x s]
  have hx : deriv (fun s : ℝ => s + y) x = 1 :=
    ((hasDerivAt_id x).add_const y).deriv
  have hy : deriv (fun s : ℝ => x + s) y = 1 := by
    simpa [add_comm] using ((hasDerivAt_id y).add_const x).deriv
  rw [hx, hy]

theorem gap4 (ξ η : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x + y)
    (hη : ∀ x y, η x y = x - y) :
    ∀ x y, py ξ x y = px η x y := by
  intro x y
  unfold px py
  rw [show (fun s => ξ x s) = (fun s => x + s) by
    funext s
    exact hξ x s]
  rw [show (fun s => η s y) = (fun s => s - y) by
    funext s
    exact hη s y]
  have hleft : deriv (fun s : ℝ => x + s) y = 1 := by
    simpa [add_comm] using ((hasDerivAt_id y).add_const x).deriv
  have hright : deriv (fun s : ℝ => s - y) x = 1 :=
    ((hasDerivAt_id x).sub_const y).deriv
  rw [hleft, hright]

theorem gap5 (η : ℝ → ℝ → ℝ)
    (hη : ∀ x y, η x y = x - y) :
    ∀ x y, px η x y = 1 := by
  intro x y
  unfold px
  rw [show (fun s => η s y) = (fun s => s - y) by
    funext s
    exact hη s y]
  exact ((hasDerivAt_id x).sub_const y).deriv

theorem gap6 (ξ : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x + y) :
    ∀ x y, px ξ x y = 1 := by
  intro x y
  unfold px
  rw [show (fun s => ξ s y) = (fun s => s + y) by
    funext s
    exact hξ s y]
  exact ((hasDerivAt_id x).add_const y).deriv

theorem gap7 (η : ℝ → ℝ → ℝ)
    (hη : ∀ x y, η x y = x - y) :
    ∀ x y, py η x y = -1 := by
  intro x y
  unfold py
  rw [show (fun s => η x s) = (fun s => x - s) by
    funext s
    exact hη x s]
  exact ((hasDerivAt_id y).const_sub x).deriv

theorem gap8 (z Z ξ η : ℝ → ℝ → ℝ)
    (hChain :
      ∀ x y,
        px z x y =
          px Z (ξ x y) (η x y) * px ξ x y +
            py Z (ξ x y) (η x y) * px η x y)
    (hξx : ∀ x y, px ξ x y = 1)
    (hηx : ∀ x y, px η x y = 1) :
    ∀ x y,
      px z x y =
        px Z (ξ x y) (η x y) +
          py Z (ξ x y) (η x y) := by
  intro x y
  rw [hChain x y, hξx x y, hηx x y]
  ring

theorem gap9 (z Z ξ η : ℝ → ℝ → ℝ)
    (hChain :
      ∀ x y,
        py z x y =
          px Z (ξ x y) (η x y) * py ξ x y +
            py Z (ξ x y) (η x y) * py η x y)
    (hξy : ∀ x y, py ξ x y = 1)
    (hηy : ∀ x y, py η x y = -1) :
    ∀ x y,
      py z x y =
        px Z (ξ x y) (η x y) -
          py Z (ξ x y) (η x y) := by
  intro x y
  rw [hChain x y, hξy x y, hηy x y]
  ring

theorem gap10 (z Z ξ η : ℝ → ℝ → ℝ)
    (hPDE : ∀ x y, px z x y = py z x y)
    (hX :
      ∀ x y,
        px z x y =
          px Z (ξ x y) (η x y) +
            py Z (ξ x y) (η x y))
    (hY :
      ∀ x y,
        py z x y =
          px Z (ξ x y) (η x y) -
            py Z (ξ x y) (η x y))
    (hξ : ∀ x y, ξ x y = x + y)
    (hη : ∀ x y, η x y = x - y) :
    ∀ u v, py Z u v = 0 := by
  intro u v
  let x : ℝ := (u + v) / 2
  let y : ℝ := (u - v) / 2
  have hξuv : ξ x y = u := by
    rw [hξ x y]
    dsimp [x, y]
    ring
  have hηuv : η x y = v := by
    rw [hη x y]
    dsimp [x, y]
    ring
  have h := hPDE x y
  rw [hX x y, hY x y, hξuv, hηuv] at h
  linarith

theorem gap11 (z Z ξ η : ℝ → ℝ → ℝ)
    (hCompose : ∀ x y, z x y = Z (ξ x y) (η x y))
    (hEtaZero : ∀ u v, py Z u v = 0)
    (hZ : Differentiable ℝ (Function.uncurry Z)) :
    ∃ φ : ℝ → ℝ, ∀ x y, z x y = φ (ξ x y) := by
  refine ⟨fun u => Z u 0, ?_⟩
  intro x y
  rw [hCompose x y]
  have hdiff : Differentiable ℝ (fun v => Z (ξ x y) v) := by
    intro v
    have hc : DifferentiableAt ℝ (fun _ : ℝ => ξ x y) v :=
      differentiableAt_const (c := ξ x y)
    have hpair :
        DifferentiableAt ℝ (fun t : ℝ => (ξ x y, t)) v :=
      hc.prodMk differentiableAt_id
    simpa [Function.comp_def, Function.uncurry] using
      (hZ (ξ x y, v)).comp v hpair
  have hzero : ∀ v, deriv (fun t => Z (ξ x y) t) v = 0 := by
    intro v
    exact hEtaZero (ξ x y) v
  exact is_const_of_deriv_eq_zero hdiff hzero (η x y) 0

theorem gap12 (z ξ : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x + y)
    (hExists : ∃ φ : ℝ → ℝ, ∀ x y, z x y = φ (ξ x y)) :
    ∃ φ : ℝ → ℝ, ∀ x y, φ (ξ x y) = φ (x + y) := by
  rcases hExists with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x y
  rw [hξ x y]

theorem gap13 (z ξ : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x + y)
    (hForm : ∃ φ : ℝ → ℝ, ∀ x y, z x y = φ (ξ x y)) :
    ∃ φ : ℝ → ℝ, ∀ x y, z x y = φ (x + y) := by
  rcases hForm with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x y
  simpa [hξ x y] using hφ x y

end

end ProofGap.Exercise3458
