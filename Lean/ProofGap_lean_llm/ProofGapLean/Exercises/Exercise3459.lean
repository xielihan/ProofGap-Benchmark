import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3459

noncomputable section

def px (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f s y) x

def py (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f x s) y

def upper (y : ℝ) : Prop :=
  0 < y

private theorem hasDerivAt_square_local (x : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
  have hid : HasDerivAt (fun s : ℝ => s) 1 x := by
    simpa [id_eq] using (hasDerivAt_id x)
  simpa [pow_two, two_mul] using (hid.mul hid)

private theorem hasDerivAt_square_add_const_local (x c : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 2 + c) (2 * x) x := by
  have hsum :
      HasDerivAt
        ((fun s : ℝ => s ^ 2) + (fun _ : ℝ => c))
        (2 * x + 0) x :=
    (hasDerivAt_square_local x).add (hasDerivAt_const x c)
  have hfun :
      ((fun s : ℝ => s ^ 2) + (fun _ : ℝ => c)) =
        (fun s : ℝ => s ^ 2 + c) := by
    funext s
    rfl
  rw [hfun] at hsum
  simpa only [add_zero] using hsum

private theorem hasDerivAt_const_add_square_local (c x : ℝ) :
    HasDerivAt (fun s : ℝ => c + s ^ 2) (2 * x) x := by
  have hsum :
      HasDerivAt
        ((fun _ : ℝ => c) + (fun s : ℝ => s ^ 2))
        (0 + 2 * x) x :=
    (hasDerivAt_const x c).add (hasDerivAt_square_local x)
  have hfun :
      ((fun _ : ℝ => c) + (fun s : ℝ => s ^ 2)) =
        (fun s : ℝ => c + s ^ 2) := by
    funext s
    rfl
  rw [hfun] at hsum
  simpa only [zero_add] using hsum

private theorem parabola_derivatives
    (Z : ℝ → ℝ → ℝ)
    (hZ : Differentiable ℝ (Function.uncurry Z))
    (x y : ℝ) :
    deriv (fun s : ℝ => Z s (s ^ 2 + y ^ 2)) x =
        px Z x (x ^ 2 + y ^ 2) +
          2 * x * py Z x (x ^ 2 + y ^ 2) ∧
      deriv (fun s : ℝ => Z x (x ^ 2 + s ^ 2)) y =
        2 * y * py Z x (x ^ 2 + y ^ 2) := by
  let F := fderiv ℝ (Function.uncurry Z) (x, x ^ 2 + y ^ 2)
  have hF :
      HasFDerivAt (Function.uncurry Z) F (x, x ^ 2 + y ^ 2) :=
    (hZ (x, x ^ 2 + y ^ 2)).hasFDerivAt
  have hx2 :
      HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2) (2 * x) x :=
    hasDerivAt_square_add_const_local x (y ^ 2)
  have hy2 :
      HasDerivAt (fun s : ℝ => x ^ 2 + s ^ 2) (2 * y) y :=
    hasDerivAt_const_add_square_local (x ^ 2) y
  have hpathx :
      HasDerivAt (fun s : ℝ => (s, s ^ 2 + y ^ 2)) ((1 : ℝ), 2 * x) x := by
    simpa [id_eq] using (hasDerivAt_id x).prodMk hx2
  have hpathy :
      HasDerivAt (fun s : ℝ => (x, x ^ 2 + s ^ 2)) ((0 : ℝ), 2 * y) y := by
    simpa [id_eq] using (hasDerivAt_const y x).prodMk hy2
  have hchainx :
      HasDerivAt (fun s : ℝ => Z s (s ^ 2 + y ^ 2))
        (F ((1 : ℝ), 2 * x)) x := by
    simpa [F, Function.comp_def, Function.uncurry] using
      hF.comp_hasDerivAt x hpathx
  have hchainy :
      HasDerivAt (fun s : ℝ => Z x (x ^ 2 + s ^ 2))
        (F ((0 : ℝ), 2 * y)) y := by
    simpa [F, Function.comp_def, Function.uncurry] using
      hF.comp_hasDerivAt y hpathy
  have hpartialx :
      px Z x (x ^ 2 + y ^ 2) = F ((1 : ℝ), 0) := by
    have hp : HasDerivAt (fun s : ℝ => (s, x ^ 2 + y ^ 2)) ((1 : ℝ), 0) x := by
      simpa [id_eq] using
        (hasDerivAt_id x).prodMk
          (hasDerivAt_const x (x ^ 2 + y ^ 2))
    have hc := hF.comp_hasDerivAt x hp
    simpa [F, px, Function.comp_def, Function.uncurry] using hc.deriv
  have hpartialy :
      py Z x (x ^ 2 + y ^ 2) = F ((0 : ℝ), 1) := by
    have hp :
        HasDerivAt (fun s : ℝ => (x, s)) ((0 : ℝ), 1)
          (x ^ 2 + y ^ 2) := by
      simpa [id_eq] using
        (hasDerivAt_const (x ^ 2 + y ^ 2) x).prodMk
          (hasDerivAt_id (x ^ 2 + y ^ 2))
    have hc := hF.comp_hasDerivAt (x ^ 2 + y ^ 2) hp
    simpa [F, py, Function.comp_def, Function.uncurry] using hc.deriv
  have hpairx :
      ((1 : ℝ), 2 * x) = ((1 : ℝ), 0) + (2 * x) • ((0 : ℝ), 1) := by
    ext <;> simp
  have hpairy :
      ((0 : ℝ), 2 * y) = (2 * y) • ((0 : ℝ), 1) := by
    ext <;> simp
  have hlinearx :
      F ((1 : ℝ), 2 * x) = F ((1 : ℝ), 0) + 2 * x * F ((0 : ℝ), 1) := by
    calc
      F ((1 : ℝ), 2 * x) = F (((1 : ℝ), 0) + (2 * x) • ((0 : ℝ), 1)) := by rw [← hpairx]
      _ = F ((1 : ℝ), 0) + F ((2 * x) • ((0 : ℝ), 1)) := F.map_add _ _
      _ = F ((1 : ℝ), 0) + (2 * x) • F ((0 : ℝ), 1) := by rw [F.map_smul]
      _ = F ((1 : ℝ), 0) + 2 * x * F ((0 : ℝ), 1) := by simp [smul_eq_mul]
  have hlineary :
      F ((0 : ℝ), 2 * y) = 2 * y * F ((0 : ℝ), 1) := by
    calc
      F ((0 : ℝ), 2 * y) = F ((2 * y) • ((0 : ℝ), 1)) := by rw [← hpairy]
      _ = (2 * y) • F ((0 : ℝ), 1) := F.map_smul _ _
      _ = 2 * y * F ((0 : ℝ), 1) := by simp [smul_eq_mul]
  constructor
  · calc
      deriv (fun s : ℝ => Z s (s ^ 2 + y ^ 2)) x = F ((1 : ℝ), 2 * x) := hchainx.deriv
      _ = F ((1 : ℝ), 0) + 2 * x * F ((0 : ℝ), 1) := hlinearx
      _ = px Z x (x ^ 2 + y ^ 2) + 2 * x * py Z x (x ^ 2 + y ^ 2) := by
        rw [← hpartialx, ← hpartialy]
  · calc
      deriv (fun s : ℝ => Z x (x ^ 2 + s ^ 2)) y = F ((0 : ℝ), 2 * y) := hchainy.deriv
      _ = 2 * y * F ((0 : ℝ), 1) := hlineary
      _ = 2 * y * py Z x (x ^ 2 + y ^ 2) := by rw [← hpartialy]

private theorem horizontal_const_of_px_zero_above_square
    (Z : ℝ → ℝ → ℝ)
    (hZ : Differentiable ℝ (Function.uncurry Z))
    (hzero : ∀ a b : ℝ, a ^ 2 < b → px Z a b = 0)
    (x b : ℝ) (hxb : x ^ 2 < b) :
    Z x b = Z 0 b := by
  have hbpos : 0 < b := lt_of_le_of_lt (sq_nonneg x) hxb
  have hb : 0 ≤ b := le_of_lt hbpos
  have hsqrt_pos : 0 < Real.sqrt b := Real.sqrt_pos.2 hbpos
  have hsqrt_sq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  have hxmem : x ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) := by
    constructor <;> nlinarith
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) := by
    constructor <;> linarith
  have hdiff :
      DifferentiableOn ℝ (fun a : ℝ => Z a b)
        (Set.Ioo (-Real.sqrt b) (Real.sqrt b)) := by
    intro a ha
    have hp : HasDerivAt (fun s : ℝ => (s, b)) ((1 : ℝ), 0) a := by
      simpa [id_eq] using
        (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
    have hc := (hZ (a, b)).hasFDerivAt.comp_hasDerivAt a hp
    have hda : DifferentiableAt ℝ (fun s : ℝ => Z s b) a := by
      simpa [Function.comp_def, Function.uncurry] using hc.differentiableAt
    exact hda.differentiableWithinAt
  have hderiv :
      ∀ a ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b),
        deriv (fun s : ℝ => Z s b) a = 0 := by
    intro a ha
    have hleft : 0 < a + Real.sqrt b := by linarith [ha.1]
    have hright : 0 < Real.sqrt b - a := by linarith [ha.2]
    have hprod : 0 < (a + Real.sqrt b) * (Real.sqrt b - a) :=
      mul_pos hleft hright
    have hab : a ^ 2 < b := by
      nlinarith
    simpa [px] using hzero a b hab
  exact
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hderiv hxmem h0mem

theorem gap1 (ξ : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x) :
    ∀ x y, px ξ x y = 1 := by
  intro x y
  have hfun : (fun s : ℝ => ξ s y) = fun s => s := by
    funext s
    exact hξ s y
  unfold px
  rw [hfun]
  simpa using (hasDerivAt_id x).deriv

theorem gap2 (ξ : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x) :
    ∀ x y, py ξ x y = 0 := by
  intro x y
  have hfun : (fun s : ℝ => ξ x s) = fun _ => x := by
    funext s
    exact hξ x s
  unfold py
  rw [hfun]
  simpa using (hasDerivAt_const y x).deriv

theorem gap3 (η : ℝ → ℝ → ℝ)
    (hη : ∀ x y, η x y = x ^ 2 + y ^ 2) :
    ∀ x y, px η x y = 2 * x := by
  intro x y
  have hfun : (fun s : ℝ => η s y) = fun s => s ^ 2 + y ^ 2 := by
    funext s
    exact hη s y
  unfold px
  rw [hfun]
  exact (hasDerivAt_square_add_const_local x (y ^ 2)).deriv

theorem gap4 (η : ℝ → ℝ → ℝ)
    (hη : ∀ x y, η x y = x ^ 2 + y ^ 2) :
    ∀ x y, py η x y = 2 * y := by
  intro x y
  have hfun : (fun s : ℝ => η x s) = fun s => x ^ 2 + s ^ 2 := by
    funext s
    exact hη x s
  unfold py
  rw [hfun]
  exact (hasDerivAt_const_add_square_local (x ^ 2) y).deriv

theorem gap5 (z Z ξ η : ℝ → ℝ → ℝ)
    (hCompose :
      ∀ x y, upper y →
        z x y = Z (ξ x y) (η x y))
    (hξ : ∀ x y, ξ x y = x)
    (hη : ∀ x y, η x y = x ^ 2 + y ^ 2)
    (hZ : ContDiff ℝ 1 (Function.uncurry Z)) :
    ∀ x y, upper y →
      px z x y =
        px Z (ξ x y) (η x y) +
          2 * x * py Z (ξ x y) (η x y) := by
  intro x y hy
  have hfun :
      (fun s : ℝ => z s y) = fun s => Z s (s ^ 2 + y ^ 2) := by
    funext s
    rw [hCompose s y hy, hξ s y, hη s y]
  have hZd : Differentiable ℝ (Function.uncurry Z) :=
    hZ.differentiable (by norm_num)
  unfold px
  rw [hfun]
  simpa [hξ x y, hη x y] using
    (parabola_derivatives Z hZd x y).1

theorem gap6 (z Z ξ η : ℝ → ℝ → ℝ)
    (hCompose :
      ∀ x y, upper y →
        z x y = Z (ξ x y) (η x y))
    (hξ : ∀ x y, ξ x y = x)
    (hη : ∀ x y, η x y = x ^ 2 + y ^ 2)
    (hZ : ContDiff ℝ 1 (Function.uncurry Z)) :
    ∀ x y, upper y →
      py z x y =
        2 * y * py Z (ξ x y) (η x y) := by
  intro x y hy
  have hev :
      (fun s : ℝ => z x s) =ᶠ[nhds y]
        fun s => Z x (x ^ 2 + s ^ 2) := by
    filter_upwards [Ioi_mem_nhds hy] with s hs
    rw [hCompose x s hs, hξ x s, hη x s]
  have hZd : Differentiable ℝ (Function.uncurry Z) :=
    hZ.differentiable (by norm_num)
  calc
    py z x y = deriv (fun s : ℝ => z x s) y := rfl
    _ = deriv (fun s : ℝ => Z x (x ^ 2 + s ^ 2)) y := hev.deriv_eq
    _ = 2 * y * py Z x (x ^ 2 + y ^ 2) :=
      (parabola_derivatives Z hZd x y).2
    _ = 2 * y * py Z (ξ x y) (η x y) := by
      rw [hξ x y, hη x y]

theorem gap7 (z Z ξ η : ℝ → ℝ → ℝ)
    (hPDE :
      ∀ x y, y * px z x y - x * py z x y = 0)
    (hX :
      ∀ x y, upper y →
        px z x y =
          px Z (ξ x y) (η x y) +
            2 * x * py Z (ξ x y) (η x y))
    (hY :
      ∀ x y, upper y →
        py z x y =
          2 * y * py Z (ξ x y) (η x y)) :
    ∀ x y, upper y →
      y * px Z (ξ x y) (η x y) = 0 := by
  intro x y hy
  calc
    y * px Z (ξ x y) (η x y) =
        y * (px Z (ξ x y) (η x y) +
          2 * x * py Z (ξ x y) (η x y)) -
        x * (2 * y * py Z (ξ x y) (η x y)) := by ring
    _ = y * px z x y - x * py z x y := by
      rw [hX x y hy, hY x y hy]
    _ = 0 := hPDE x y

theorem gap8 (Z ξ η : ℝ → ℝ → ℝ)
    (hProduct :
      ∀ x y, upper y →
        y * px Z (ξ x y) (η x y) = 0) :
    ∀ x y, upper y →
      px Z (ξ x y) (η x y) = 0 := by
  intro x y hy
  rcases mul_eq_zero.mp (hProduct x y hy) with hy0 | hzero
  · exact (ne_of_gt hy hy0).elim
  · exact hzero

theorem gap9 (z Z ξ η : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x)
    (hη : ∀ x y, η x y = x ^ 2 + y ^ 2)
    (hCompose :
      ∀ x y, upper y →
        z x y = Z (ξ x y) (η x y))
    (hXiZero :
      ∀ x y, upper y →
        px Z (ξ x y) (η x y) = 0)
    (hZ : Differentiable ℝ (Function.uncurry Z)) :
    ∃ φ : ℝ → ℝ, ∀ x y, upper y →
      z x y = φ (η x y) := by
  have hzero : ∀ a b : ℝ, a ^ 2 < b → px Z a b = 0 := by
    intro a b hab
    let v : ℝ := Real.sqrt (b - a ^ 2)
    have hv : 0 < v := by
      dsimp [v]
      exact Real.sqrt_pos.2 (sub_pos.mpr hab)
    have hz := hXiZero a v hv
    rw [hξ a v, hη a v] at hz
    have hv2 : v ^ 2 = b - a ^ 2 := by
      dsimp [v]
      exact Real.sq_sqrt (le_of_lt (sub_pos.mpr hab))
    have heq : a ^ 2 + v ^ 2 = b := by
      nlinarith
    simpa [heq] using hz
  refine ⟨fun t => Z 0 t, ?_⟩
  intro x y hy
  rw [hCompose x y hy, hξ x y]
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  have hlt : x ^ 2 < η x y := by
    rw [hη x y]
    nlinarith
  exact horizontal_const_of_px_zero_above_square Z hZ hzero x (η x y) hlt

theorem gap10 (z η : ℝ → ℝ → ℝ)
    (hη : ∀ x y, η x y = x ^ 2 + y ^ 2)
    (hExists :
      ∃ φ : ℝ → ℝ, ∀ x y, upper y →
        z x y = φ (η x y)) :
    ∃ φ : ℝ → ℝ, ∀ x y, upper y →
      φ (η x y) = φ (x ^ 2 + y ^ 2) := by
  rcases hExists with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x y hy
  rw [hη x y]

theorem gap11 (z η : ℝ → ℝ → ℝ)
    (hη : ∀ x y, η x y = x ^ 2 + y ^ 2)
    (hForm :
      ∃ φ : ℝ → ℝ, ∀ x y, upper y →
        z x y = φ (η x y)) :
    ∃ φ : ℝ → ℝ, ∀ x y, upper y →
      z x y = φ (x ^ 2 + y ^ 2) := by
  rcases hForm with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x y hy
  simpa [hη x y] using hφ x y hy

end

end ProofGap.Exercise3459
