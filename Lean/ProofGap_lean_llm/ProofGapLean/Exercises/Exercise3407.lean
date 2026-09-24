import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise3407

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => f x t) y
def closedZ (x y : ℝ) := x / 2 * (3 * y - x ^ 2)

private theorem hasDerivAt_partialX
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f t y) (partialX f x y) x := by
  have hc : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hs := hf.fun_comp' x hc
  simpa [partialX, Function.uncurry] using hs.hasDerivAt

private theorem hasDerivAt_partialY
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f x t) (partialY f x y) y := by
  have hc : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hs := hf.fun_comp' y hc
  simpa [partialY, Function.uncurry] using hs.hasDerivAt

private theorem eventuallyEq_coordX
    {F G : ℝ × ℝ → ℝ} {x y : ℝ}
    (h : F =ᶠ[nhds (x, y)] G) :
    (fun t => F (t, y)) =ᶠ[nhds x] fun t => G (t, y) := by
  have hc : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) := by
    exact continuousAt_id.prodMk continuousAt_const
  simpa [Function.comp_def] using h.comp_tendsto hc

private theorem eventuallyEq_coordY
    {F G : ℝ × ℝ → ℝ} {x y : ℝ}
    (h : F =ᶠ[nhds (x, y)] G) :
    (fun t => F (x, t)) =ᶠ[nhds y] fun t => G (x, t) := by
  have hc : Filter.Tendsto (fun t : ℝ => (x, t))
      (nhds y) (nhds (x, y)) := by
    exact continuousAt_const.prodMk continuousAt_id
  simpa [Function.comp_def] using h.comp_tendsto hc

theorem gap1 (x y u v : ℝ)
    (hSum : x = u + v) (hSq : y = u ^ 2 + v ^ 2) :
    (u = (x + Real.sqrt (2 * y - x ^ 2)) / 2 ∧
      v = (x - Real.sqrt (2 * y - x ^ 2)) / 2) ∨
    (u = (x - Real.sqrt (2 * y - x ^ 2)) / 2 ∧
      v = (x + Real.sqrt (2 * y - x ^ 2)) / 2) := by
  have hdisc : 2 * y - x ^ 2 = (u - v) ^ 2 := by
    rw [hSum, hSq]
    ring
  rcases le_total v u with hvu | huv
  · left
    have hsqrt : Real.sqrt (2 * y - x ^ 2) = u - v := by
      rw [hdisc, Real.sqrt_sq_eq_abs, abs_of_nonneg (sub_nonneg.mpr hvu)]
    constructor <;> rw [hsqrt, hSum] <;> ring
  · right
    have hsqrt : Real.sqrt (2 * y - x ^ 2) = v - u := by
      rw [hdisc, Real.sqrt_sq_eq_abs, abs_of_nonpos (sub_nonpos.mpr huv)]
      ring
    constructor <;> rw [hsqrt, hSum] <;> ring

theorem gap2 (x y : ℝ) :
    0 ≤ 2 * y - x ^ 2 ↔ x ^ 2 / 2 ≤ y := by
  constructor <;> intro h <;> linarith

theorem gap3 :
    {p : ℝ × ℝ | ∃ u v : ℝ, p.1 = u + v ∧ p.2 = u ^ 2 + v ^ 2} =
      {p : ℝ × ℝ | p.1 ^ 2 / 2 ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨u, v, hsum, hsq⟩
    change p.1 ^ 2 / 2 ≤ p.2
    rw [← gap2]
    rw [hsum, hsq]
    nlinarith [sq_nonneg (u - v)]
  · intro hp
    change p.1 ^ 2 / 2 ≤ p.2 at hp
    have hdisc : 0 ≤ 2 * p.2 - p.1 ^ 2 := (gap2 p.1 p.2).2 hp
    refine ⟨(p.1 + Real.sqrt (2 * p.2 - p.1 ^ 2)) / 2,
      (p.1 - Real.sqrt (2 * p.2 - p.1 ^ 2)) / 2, ?_, ?_⟩
    · ring
    · have hsqrt :=
        Real.sq_sqrt hdisc
      nlinarith

theorem gap4 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hSum : ∀ᶠ p : ℝ × ℝ in nhds (x, y), p.1 = u p.1 p.2 + v p.1 p.2) :
    1 = partialX u x y + partialX v x y := by
  have hlocal :
      (fun t : ℝ => t) =ᶠ[nhds x] fun t => u t y + v t y := by
    simpa using eventuallyEq_coordX hSum
  have hd := (hasDerivAt_partialX u x y huDiff).add
    (hasDerivAt_partialX v x y hvDiff)
  calc
    1 = deriv (fun t : ℝ => t) x := by simp
    _ = deriv (fun t => u t y + v t y) x := hlocal.deriv_eq
    _ = partialX u x y + partialX v x y := hd.deriv

theorem gap5 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hSq : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = (u p.1 p.2) ^ 2 + (v p.1 p.2) ^ 2) :
    0 = 2 * u x y * partialX u x y + 2 * v x y * partialX v x y := by
  have hlocal :
      (fun _ : ℝ => y) =ᶠ[nhds x]
        fun t => (u t y) ^ 2 + (v t y) ^ 2 := by
    simpa using eventuallyEq_coordX hSq
  have hd := (hasDerivAt_partialX u x y huDiff).pow 2 |>.add
    ((hasDerivAt_partialX v x y hvDiff).pow 2)
  calc
    0 = deriv (fun _ : ℝ => y) x := by simp
    _ = deriv (fun t => (u t y) ^ 2 + (v t y) ^ 2) x := hlocal.deriv_eq
    _ = 2 * u x y * partialX u x y +
        2 * v x y * partialX v x y := by
      have h := hd.deriv
      simp only [Pi.add_apply, Pi.pow_apply] at h
      convert h using 1 <;> ring

theorem gap6 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : v x y - u x y ≠ 0)
    (h1 : 1 = partialX u x y + partialX v x y)
    (h2 : 0 = 2 * u x y * partialX u x y + 2 * v x y * partialX v x y) :
    partialX u x y = v x y / (v x y - u x y) := by
  apply (eq_div_iff hNonzero).2
  have hv :
      partialX v x y = 1 - partialX u x y := by
    linarith
  rw [hv] at h2
  nlinarith

theorem gap7 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : v x y - u x y ≠ 0)
    (h1 : 1 = partialX u x y + partialX v x y)
    (h2 : 0 = 2 * u x y * partialX u x y + 2 * v x y * partialX v x y) :
    partialX v x y = -u x y / (v x y - u x y) := by
  apply (eq_div_iff hNonzero).2
  have hu :
      partialX u x y = 1 - partialX v x y := by
    linarith
  rw [hu] at h2
  nlinarith

theorem gap8 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = (u p.1 p.2) ^ 3 + (v p.1 p.2) ^ 3) :
    partialX z x y =
      3 * (u x y) ^ 2 * partialX u x y +
      3 * (v x y) ^ 2 * partialX v x y := by
  have hlocal :
      (fun t : ℝ => z t y) =ᶠ[nhds x]
        fun t => (u t y) ^ 3 + (v t y) ^ 3 := by
    simpa using eventuallyEq_coordX hZ
  have hd := (hasDerivAt_partialX u x y huDiff).pow 3 |>.add
    ((hasDerivAt_partialX v x y hvDiff).pow 3)
  calc
    partialX z x y = deriv (fun t => z t y) x := rfl
    _ = deriv (fun t => (u t y) ^ 3 + (v t y) ^ 3) x :=
      hlocal.deriv_eq
    _ = 3 * (u x y) ^ 2 * partialX u x y +
        3 * (v x y) ^ 2 * partialX v x y := by
      have h := hd.deriv
      simp only [Pi.add_apply, Pi.pow_apply] at h
      convert h using 1 <;> ring

theorem gap9 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : partialX u x y = v x y / (v x y - u x y))
    (hv : partialX v x y = -u x y / (v x y - u x y)) :
    3 * (u x y) ^ 2 * partialX u x y + 3 * (v x y) ^ 2 * partialX v x y =
      3 * (u x y) ^ 2 * (v x y / (v x y - u x y)) -
      3 * (v x y) ^ 2 * (u x y / (v x y - u x y)) := by
  rw [hu, hv]
  ring

theorem gap10 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : v x y - u x y ≠ 0) :
    3 * (u x y) ^ 2 * (v x y / (v x y - u x y)) -
        3 * (v x y) ^ 2 * (u x y / (v x y - u x y)) =
      -3 * u x y * v x y := by
  field_simp [hNonzero]
  ring

theorem gap11 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hChain : partialX z x y =
      3 * (u x y) ^ 2 * partialX u x y + 3 * (v x y) ^ 2 * partialX v x y)
    (hSub : 3 * (u x y) ^ 2 * partialX u x y + 3 * (v x y) ^ 2 * partialX v x y =
      -3 * u x y * v x y) :
    partialX z x y = -3 * u x y * v x y := by
  exact hChain.trans hSub

theorem gap12 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : v x y - u x y ≠ 0)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hSum : ∀ᶠ p : ℝ × ℝ in nhds (x, y), p.1 = u p.1 p.2 + v p.1 p.2)
    (hSq : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = (u p.1 p.2) ^ 2 + (v p.1 p.2) ^ 2)
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = (u p.1 p.2) ^ 3 + (v p.1 p.2) ^ 3) :
    partialY z x y = (3 / 2 : ℝ) * (u x y + v x y) := by
  have hSumLocal :
      (fun _ : ℝ => x) =ᶠ[nhds y] fun t => u x t + v x t := by
    simpa using eventuallyEq_coordY hSum
  have hsumDeriv := (hasDerivAt_partialY u x y huDiff).add
    (hasDerivAt_partialY v x y hvDiff)
  have hsumY : 0 = partialY u x y + partialY v x y := by
    calc
      0 = deriv (fun _ : ℝ => x) y := by simp
      _ = deriv (fun t => u x t + v x t) y := hSumLocal.deriv_eq
      _ = partialY u x y + partialY v x y := hsumDeriv.deriv
  have hSqLocal :
      (fun t : ℝ => t) =ᶠ[nhds y]
        fun t => (u x t) ^ 2 + (v x t) ^ 2 := by
    simpa using eventuallyEq_coordY hSq
  have hsqDeriv := (hasDerivAt_partialY u x y huDiff).pow 2 |>.add
    ((hasDerivAt_partialY v x y hvDiff).pow 2)
  have hsqY :
      1 = 2 * u x y * partialY u x y +
        2 * v x y * partialY v x y := by
    calc
      1 = deriv (fun t : ℝ => t) y := by simp
      _ = deriv (fun t => (u x t) ^ 2 + (v x t) ^ 2) y :=
        hSqLocal.deriv_eq
      _ = 2 * u x y * partialY u x y +
          2 * v x y * partialY v x y := by
        have h := hsqDeriv.deriv
        simp only [Pi.add_apply, Pi.pow_apply] at h
        convert h using 1 <;> ring
  have hZLocal :
      (fun t : ℝ => z x t) =ᶠ[nhds y]
        fun t => (u x t) ^ 3 + (v x t) ^ 3 := by
    simpa using eventuallyEq_coordY hZ
  have hzDeriv := (hasDerivAt_partialY u x y huDiff).pow 3 |>.add
    ((hasDerivAt_partialY v x y hvDiff).pow 3)
  have hchain :
      partialY z x y =
        3 * (u x y) ^ 2 * partialY u x y +
          3 * (v x y) ^ 2 * partialY v x y := by
    calc
      partialY z x y = deriv (fun t => z x t) y := rfl
      _ = deriv (fun t => (u x t) ^ 3 + (v x t) ^ 3) y :=
        hZLocal.deriv_eq
      _ = 3 * (u x y) ^ 2 * partialY u x y +
          3 * (v x y) ^ 2 * partialY v x y := by
        have h := hzDeriv.deriv
        simp only [Pi.add_apply, Pi.pow_apply] at h
        convert h using 1 <;> ring
  have hden : 2 * (v x y - u x y) ≠ 0 :=
    mul_ne_zero (by norm_num) hNonzero
  have hvOpp : partialY v x y = -partialY u x y := by
    linarith
  have huY :
      partialY u x y = -1 / (2 * (v x y - u x y)) := by
    apply (eq_div_iff hden).2
    rw [hvOpp] at hsqY
    nlinarith
  have hvY :
      partialY v x y = 1 / (2 * (v x y - u x y)) := by
    rw [hvOpp, huY]
    ring
  calc
    partialY z x y =
        3 * (u x y) ^ 2 * partialY u x y +
          3 * (v x y) ^ 2 * partialY v x y := hchain
    _ = (3 / 2 : ℝ) * (u x y + v x y) := by
      rw [huY, hvY]
      field_simp [hNonzero] <;> ring

theorem gap13 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : x = u x y + v x y)
    (hSq : y = (u x y) ^ 2 + (v x y) ^ 2) :
    x ^ 2 - y = 2 * u x y * v x y := by
  let U := u x y
  let V := v x y
  change x = U + V at hSum
  change y = U ^ 2 + V ^ 2 at hSq
  change x ^ 2 - y = 2 * U * V
  rw [hSum, hSq]
  ring

theorem gap14 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZ : z x y = (u x y) ^ 3 + (v x y) ^ 3) :
    z x y = (u x y + v x y) *
      ((u x y) ^ 2 - u x y * v x y + (v x y) ^ 2) := by
  rw [hZ]
  ring

theorem gap15 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : x = u x y + v x y)
    (hSq : y = (u x y) ^ 2 + (v x y) ^ 2) :
    (u x y + v x y) * ((u x y) ^ 2 - u x y * v x y + (v x y) ^ 2) =
      x * ((3 / 2 : ℝ) * y - x ^ 2 / 2) := by
  let U := u x y
  let V := v x y
  change x = U + V at hSum
  change y = U ^ 2 + V ^ 2 at hSq
  change (U + V) * (U ^ 2 - U * V + V ^ 2) =
    x * ((3 / 2 : ℝ) * y - x ^ 2 / 2)
  rw [hSum, hSq]
  ring

theorem gap16 (x y : ℝ) :
    x * ((3 / 2 : ℝ) * y - x ^ 2 / 2) = closedZ x y := by
  unfold closedZ
  ring

theorem gap17 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : z x y = (u x y + v x y) *
      ((u x y) ^ 2 - u x y * v x y + (v x y) ^ 2))
    (h2 : (u x y + v x y) *
      ((u x y) ^ 2 - u x y * v x y + (v x y) ^ 2) =
      x * ((3 / 2 : ℝ) * y - x ^ 2 / 2))
    (h3 : x * ((3 / 2 : ℝ) * y - x ^ 2 / 2) = closedZ x y) :
    z x y = closedZ x y := by
  exact h1.trans (h2.trans h3)

theorem gap18 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hClosed : ∀ᶠ p : ℝ × ℝ in nhds (x, y), z p.1 p.2 = closedZ p.1 p.2) :
    partialX z x y = (3 / 2 : ℝ) * y - (3 / 2 : ℝ) * x ^ 2 := by
  have hlocal :
      (fun t : ℝ => z t y) =ᶠ[nhds x] fun t => closedZ t y := by
    simpa using eventuallyEq_coordX hClosed
  have hclosed :
      HasDerivAt (fun t : ℝ => closedZ t y)
        ((3 / 2 : ℝ) * y - (3 / 2 : ℝ) * x ^ 2) x := by
    convert ((hasDerivAt_id x).div_const 2).mul
      ((hasDerivAt_const x (3 * y)).sub ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp [closedZ, id] <;> ring
  calc
    partialX z x y = deriv (fun t => z t y) x := rfl
    _ = deriv (fun t => closedZ t y) x := hlocal.deriv_eq
    _ = (3 / 2 : ℝ) * y - (3 / 2 : ℝ) * x ^ 2 := hclosed.deriv

theorem gap19 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : x = u x y + v x y)
    (hSq : y = (u x y) ^ 2 + (v x y) ^ 2) :
    (3 / 2 : ℝ) * y - (3 / 2 : ℝ) * x ^ 2 =
      -3 * u x y * v x y := by
  let U := u x y
  let V := v x y
  change x = U + V at hSum
  change y = U ^ 2 + V ^ 2 at hSq
  change (3 / 2 : ℝ) * y - (3 / 2 : ℝ) * x ^ 2 = -3 * U * V
  rw [hSum, hSq]
  ring

theorem gap20 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialX z x y = (3 / 2 : ℝ) * y - (3 / 2 : ℝ) * x ^ 2)
    (h2 : (3 / 2 : ℝ) * y - (3 / 2 : ℝ) * x ^ 2 = -3 * u x y * v x y) :
    partialX z x y = -3 * u x y * v x y := by
  exact h1.trans h2

theorem gap21 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hClosed : ∀ᶠ p : ℝ × ℝ in nhds (x, y), z p.1 p.2 = closedZ p.1 p.2) :
    partialY z x y = (3 / 2 : ℝ) * x := by
  have hlocal :
      (fun t : ℝ => z x t) =ᶠ[nhds y] fun t => closedZ x t := by
    simpa using eventuallyEq_coordY hClosed
  have hclosed :
      HasDerivAt (fun t : ℝ => closedZ x t) ((3 / 2 : ℝ) * x) y := by
    convert (((hasDerivAt_id y).const_mul 3).sub_const (x ^ 2)).const_mul
      (x / 2) using 1 <;>
      simp [closedZ, id] <;> ring
  calc
    partialY z x y = deriv (fun t => z x t) y := rfl
    _ = deriv (fun t => closedZ x t) y := hlocal.deriv_eq
    _ = (3 / 2 : ℝ) * x := hclosed.deriv

theorem gap22 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : x = u x y + v x y) :
    (3 / 2 : ℝ) * x = (3 / 2 : ℝ) * (u x y + v x y) := by
  let U := u x y
  let V := v x y
  change x = U + V at hSum
  change (3 / 2 : ℝ) * x = (3 / 2 : ℝ) * (U + V)
  rw [hSum]

theorem gap23 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialY z x y = (3 / 2 : ℝ) * x)
    (h2 : (3 / 2 : ℝ) * x = (3 / 2 : ℝ) * (u x y + v x y)) :
    partialY z x y = (3 / 2 : ℝ) * (u x y + v x y) := by
  exact h1.trans h2

end

end ProofGap.Exercise3407
