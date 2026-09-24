import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3226

noncomputable section

def u (x y z : ℝ) : ℝ :=
  Real.rpow (x / y) z

def factorized (x y z : ℝ) : ℝ :=
  Real.rpow x z * Real.rpow y (-z)

def admissible (x y : ℝ) : Prop :=
  0 < x ∧ 0 < y

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def secondXX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f t y z) x

def secondYY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x t z) y

def secondZZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ f x y t) z

def mixedXY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f x t z) y

def mixedYZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x y t) z

def mixedZX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ f t y z) x

private theorem rpow_sub_one_of_pos {x a : ℝ} (hx : 0 < x) :
    Real.rpow x (a - 1) = Real.rpow x a / x := by
  change x ^ (a - 1) = x ^ a / x
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx]
  rw [show Real.log x * (a - 1) =
      Real.log x * a - Real.log x by ring]
  rw [Real.exp_sub, Real.exp_log hx]

theorem gap1 :
    ∀ x y z : ℝ, admissible x y →
      u x y z = factorized x y z := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  unfold u factorized
  change (x / y) ^ z = x ^ z * y ^ (-z)
  calc
    (x / y) ^ z = x ^ z / y ^ z :=
      Real.div_rpow hx.le hy.le z
    _ = x ^ z * y ^ (-z) := by
      rw [Real.rpow_neg hy.le]
      rfl

theorem gap2 :
    ∀ x y z : ℝ, admissible x y →
      partialX u x y z =
        z * Real.rpow x (z - 1) * Real.rpow y (-z) := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have heq :
      (fun t : ℝ => u t y z) =ᶠ[nhds x]
        (fun t : ℝ => factorized t y z) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact gap1 t y z ⟨ht, hy⟩
  have hd : HasDerivAt (fun t : ℝ => Real.rpow t z)
      (z * Real.rpow x (z - 1)) x :=
    Real.hasDerivAt_rpow_const (p := z) (Or.inl (ne_of_gt hx))
  change deriv (fun t : ℝ => u t y z) x = _
  rw [heq.deriv_eq]
  simpa [factorized] using
    (hd.mul_const (Real.rpow y (-z))).deriv

theorem gap3 :
    ∀ z x y : ℝ, admissible x y →
      z * Real.rpow x (z - 1) * Real.rpow y (-z) =
        (z / x) * u x y z := by
  intro z x y h
  rcases h with ⟨hx, hy⟩
  rw [gap1 x y z ⟨hx, hy⟩]
  unfold factorized
  rw [rpow_sub_one_of_pos hx]
  field_simp [ne_of_gt hx]
  <;> ring

theorem gap4 :
    ∀ x y z : ℝ, admissible x y →
      partialX u x y z = (z / x) * u x y z := by
  intro x y z h
  rw [gap2 x y z h, gap3 z x y h]

theorem gap5 :
    ∀ x y z : ℝ, admissible x y →
      partialY u x y z =
        -z * Real.rpow x z * Real.rpow y (-z - 1) := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have heq :
      (fun t : ℝ => u x t z) =ᶠ[nhds y]
        (fun t : ℝ => factorized x t z) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact gap1 x t z ⟨hx, ht⟩
  have hd : HasDerivAt (fun t : ℝ => Real.rpow t (-z))
      ((-z) * Real.rpow y (-z - 1)) y :=
    Real.hasDerivAt_rpow_const (p := -z) (Or.inl (ne_of_gt hy))
  change deriv (fun t : ℝ => u x t z) y = _
  rw [heq.deriv_eq]
  calc
    deriv (fun t : ℝ => factorized x t z) y =
        Real.rpow x z * ((-z) * Real.rpow y (-z - 1)) := by
      simpa [factorized] using (hd.const_mul (Real.rpow x z)).deriv
    _ = -z * Real.rpow x z * Real.rpow y (-z - 1) := by ring

theorem gap6 :
    ∀ z x y : ℝ, admissible x y →
      -z * Real.rpow x z * Real.rpow y (-z - 1) =
        -(z / y) * u x y z := by
  intro z x y h
  rcases h with ⟨hx, hy⟩
  rw [gap1 x y z ⟨hx, hy⟩]
  unfold factorized
  rw [rpow_sub_one_of_pos hy]
  field_simp [ne_of_gt hy]
  <;> ring

theorem gap7 :
    ∀ x y z : ℝ, admissible x y →
      partialY u x y z = -(z / y) * u x y z := by
  intro x y z h
  rw [gap5 x y z h, gap6 z x y h]

theorem gap8 :
    ∀ x y z : ℝ, admissible x y →
      partialZ u x y z = u x y z * Real.log (x / y) := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have hq : 0 < x / y := div_pos hx hy
  have hlin : HasDerivAt
      (fun t : ℝ => Real.log (x / y) * t) (Real.log (x / y)) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.log (x / y))
  have hexp : HasDerivAt
      (fun t : ℝ => Real.exp (Real.log (x / y) * t))
      (Real.exp (Real.log (x / y) * z) * Real.log (x / y)) z :=
    (Real.hasDerivAt_exp (Real.log (x / y) * z)).comp z hlin
  have hd : HasDerivAt
      (fun t : ℝ => Real.rpow (x / y) t)
      (Real.rpow (x / y) z * Real.log (x / y)) z := by
    simpa [Real.rpow_def_of_pos hq] using hexp
  change deriv (fun t : ℝ => Real.rpow (x / y) t) z = _
  exact hd.deriv

theorem gap9 :
    ∀ x y z : ℝ, admissible x y →
      secondXX u x y z =
        z * (z - 1) * Real.rpow x (z - 2) * Real.rpow y (-z) := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have heq :
      (fun t : ℝ => partialX u t y z) =ᶠ[nhds x]
        (fun t : ℝ => z * Real.rpow t (z - 1) * Real.rpow y (-z)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact gap2 t y z ⟨ht, hy⟩
  have hd : HasDerivAt (fun t : ℝ => Real.rpow t (z - 1))
      ((z - 1) * Real.rpow x ((z - 1) - 1)) x :=
    Real.hasDerivAt_rpow_const (p := z - 1) (Or.inl (ne_of_gt hx))
  change deriv (fun t : ℝ => partialX u t y z) x = _
  rw [heq.deriv_eq]
  calc
    deriv (fun t : ℝ => z * Real.rpow t (z - 1) * Real.rpow y (-z)) x =
        (z * ((z - 1) * Real.rpow x ((z - 1) - 1))) *
          Real.rpow y (-z) := by
      simpa using
        ((hd.const_mul z).mul_const (Real.rpow y (-z))).deriv
    _ = z * (z - 1) * Real.rpow x (z - 2) * Real.rpow y (-z) := by ring

theorem gap10 :
    ∀ z x y : ℝ, admissible x y →
      z * (z - 1) * Real.rpow x (z - 2) * Real.rpow y (-z) =
        (z * (z - 1) / x ^ 2) * u x y z := by
  intro z x y h
  rcases h with ⟨hx, hy⟩
  have hp : Real.rpow x (z - 2) = Real.rpow x z / x / x := by
    calc
      Real.rpow x (z - 2) = Real.rpow x ((z - 1) - 1) := by
        congr 1
        ring
      _ = Real.rpow x (z - 1) / x := rpow_sub_one_of_pos hx
      _ = (Real.rpow x z / x) / x := by rw [rpow_sub_one_of_pos hx]
  rw [gap1 x y z ⟨hx, hy⟩, hp]
  unfold factorized
  field_simp [ne_of_gt hx]
  <;> ring

theorem gap11 :
    ∀ x y z : ℝ, admissible x y →
      secondXX u x y z =
        (z * (z - 1) / x ^ 2) * u x y z := by
  intro x y z h
  rw [gap9 x y z h, gap10 z x y h]

theorem gap12 :
    ∀ x y z : ℝ, admissible x y →
      secondYY u x y z =
        -z * (-z - 1) * Real.rpow x z * Real.rpow y (-z - 2) := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have heq :
      (fun t : ℝ => partialY u x t z) =ᶠ[nhds y]
        (fun t : ℝ => -z * Real.rpow x z * Real.rpow t (-z - 1)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact gap5 x t z ⟨hx, ht⟩
  have hd : HasDerivAt (fun t : ℝ => Real.rpow t (-z - 1))
      ((-z - 1) * Real.rpow y ((-z - 1) - 1)) y :=
    Real.hasDerivAt_rpow_const (p := -z - 1) (Or.inl (ne_of_gt hy))
  change deriv (fun t : ℝ => partialY u x t z) y = _
  rw [heq.deriv_eq]
  calc
    deriv (fun t : ℝ => -z * Real.rpow x z * Real.rpow t (-z - 1)) y =
        (-z * Real.rpow x z) *
          ((-z - 1) * Real.rpow y ((-z - 1) - 1)) := by
      simpa using (hd.const_mul (-z * Real.rpow x z)).deriv
    _ = -z * (-z - 1) * Real.rpow x z * Real.rpow y (-z - 2) := by ring

theorem gap13 :
    ∀ z x y : ℝ, admissible x y →
      -z * (-z - 1) * Real.rpow x z * Real.rpow y (-z - 2) =
        (z * (z + 1) / y ^ 2) * u x y z := by
  intro z x y h
  rcases h with ⟨hx, hy⟩
  have hp : Real.rpow y (-z - 2) = Real.rpow y (-z) / y / y := by
    calc
      Real.rpow y (-z - 2) = Real.rpow y ((-z - 1) - 1) := by
        congr 1
        ring
      _ = Real.rpow y (-z - 1) / y := rpow_sub_one_of_pos hy
      _ = (Real.rpow y (-z) / y) / y := by rw [rpow_sub_one_of_pos hy]
  rw [gap1 x y z ⟨hx, hy⟩, hp]
  unfold factorized
  field_simp [ne_of_gt hy]
  <;> ring

theorem gap14 :
    ∀ x y z : ℝ, admissible x y →
      secondYY u x y z =
        (z * (z + 1) / y ^ 2) * u x y z := by
  intro x y z h
  rw [gap12 x y z h, gap13 z x y h]

theorem gap15 :
    ∀ x y z : ℝ, admissible x y →
      secondZZ u x y z =
        u x y z * Real.log (x / y) ^ 2 := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have hadm : admissible x y := ⟨hx, hy⟩
  have hq : 0 < x / y := div_pos hx hy
  have heq :
      (fun t : ℝ => partialZ u x y t) =ᶠ[nhds z]
        (fun t : ℝ => u x y t * Real.log (x / y)) :=
    Filter.Eventually.of_forall (fun t => gap8 x y t hadm)
  have hlin : HasDerivAt
      (fun t : ℝ => Real.log (x / y) * t) (Real.log (x / y)) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.log (x / y))
  have hexp : HasDerivAt
      (fun t : ℝ => Real.exp (Real.log (x / y) * t))
      (Real.exp (Real.log (x / y) * z) * Real.log (x / y)) z :=
    (Real.hasDerivAt_exp (Real.log (x / y) * z)).comp z hlin
  have hd : HasDerivAt (fun t : ℝ => u x y t)
      (u x y z * Real.log (x / y)) z := by
    simpa [u, Real.rpow_def_of_pos hq] using hexp
  change deriv (fun t : ℝ => partialZ u x y t) z = _
  rw [heq.deriv_eq]
  calc
    deriv (fun t : ℝ => u x y t * Real.log (x / y)) z =
        (u x y z * Real.log (x / y)) * Real.log (x / y) :=
      (hd.mul_const (Real.log (x / y))).deriv
    _ = u x y z * Real.log (x / y) ^ 2 := by ring

theorem gap16 :
    ∀ x y z : ℝ, admissible x y →
      mixedXY u x y z =
        (z / x) * (-(z / y)) * u x y z := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have hadm : admissible x y := ⟨hx, hy⟩
  have heq :
      (fun t : ℝ => partialX u x t z) =ᶠ[nhds y]
        (fun t : ℝ => z * Real.rpow x (z - 1) * Real.rpow t (-z)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact gap2 x t z ⟨hx, ht⟩
  have hd : HasDerivAt (fun t : ℝ => Real.rpow t (-z))
      ((-z) * Real.rpow y (-z - 1)) y :=
    Real.hasDerivAt_rpow_const (p := -z) (Or.inl (ne_of_gt hy))
  change deriv (fun t : ℝ => partialX u x t z) y = _
  rw [heq.deriv_eq]
  calc
    deriv (fun t : ℝ => z * Real.rpow x (z - 1) * Real.rpow t (-z)) y =
        (z * Real.rpow x (z - 1)) *
          ((-z) * Real.rpow y (-z - 1)) := by
      simpa using (hd.const_mul (z * Real.rpow x (z - 1))).deriv
    _ = (z * Real.rpow x (z - 1) * Real.rpow y (-z)) * (-(z / y)) := by
      rw [rpow_sub_one_of_pos hy]
      field_simp [ne_of_gt hy]
      <;> ring
    _ = (z / x) * (-(z / y)) * u x y z := by
      rw [gap3 z x y hadm]
      ring

theorem gap17 :
    ∀ z x y : ℝ, admissible x y →
      (z / x) * (-(z / y)) * u x y z =
        -(z ^ 2 / (x * y)) * u x y z := by
  intro z x y h
  rcases h with ⟨hx, hy⟩
  field_simp [ne_of_gt hx, ne_of_gt hy]
  <;> ring

theorem gap18 :
    ∀ x y z : ℝ, admissible x y →
      mixedXY u x y z =
        -(z ^ 2 / (x * y)) * u x y z := by
  intro x y z h
  rw [gap16 x y z h, gap17 z x y h]

theorem gap19 :
    ∀ x y z : ℝ, admissible x y →
      mixedYZ u x y z =
        -(z / y) * u x y z * Real.log (x / y) -
          (1 / y) * u x y z := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have hadm : admissible x y := ⟨hx, hy⟩
  have hq : 0 < x / y := div_pos hx hy
  have heq :
      (fun t : ℝ => partialY u x y t) =ᶠ[nhds z]
        (fun t : ℝ => -(t / y) * u x y t) :=
    Filter.Eventually.of_forall (fun t => gap7 x y t hadm)
  have hlin : HasDerivAt (fun t : ℝ => -(t / y)) (-(1 / y)) z := by
    simpa using ((hasDerivAt_id z).div_const y).neg
  have hexpLin : HasDerivAt
      (fun t : ℝ => Real.log (x / y) * t) (Real.log (x / y)) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.log (x / y))
  have hexp : HasDerivAt
      (fun t : ℝ => Real.exp (Real.log (x / y) * t))
      (Real.exp (Real.log (x / y) * z) * Real.log (x / y)) z :=
    (Real.hasDerivAt_exp (Real.log (x / y) * z)).comp z hexpLin
  have hu : HasDerivAt (fun t : ℝ => u x y t)
      (u x y z * Real.log (x / y)) z := by
    simpa [u, Real.rpow_def_of_pos hq] using hexp
  change deriv (fun t : ℝ => partialY u x y t) z = _
  rw [heq.deriv_eq]
  calc
    deriv (fun t : ℝ => -(t / y) * u x y t) z =
        (-(1 / y)) * u x y z +
          (-(z / y)) * (u x y z * Real.log (x / y)) :=
      (hlin.mul hu).deriv
    _ = -(z / y) * u x y z * Real.log (x / y) -
          (1 / y) * u x y z := by ring

theorem gap20 :
    ∀ z y x : ℝ, admissible x y →
      -(z / y) * u x y z * Real.log (x / y) -
          (1 / y) * u x y z =
        -((1 + z * Real.log (x / y)) / y) * u x y z := by
  intro z y x h
  rcases h with ⟨hx, hy⟩
  field_simp [ne_of_gt hy]
  <;> ring

theorem gap21 :
    ∀ x y z : ℝ, admissible x y →
      mixedYZ u x y z =
        -((1 + z * Real.log (x / y)) / y) * u x y z := by
  intro x y z h
  rw [gap19 x y z h, gap20 z y x h]

theorem gap22 :
    ∀ x y z : ℝ, admissible x y →
      mixedZX u x y z =
        (z / x) * u x y z * Real.log (x / y) +
          (1 / x) * u x y z := by
  intro x y z h
  rcases h with ⟨hx, hy⟩
  have hadm : admissible x y := ⟨hx, hy⟩
  have heq :
      (fun t : ℝ => partialZ u t y z) =ᶠ[nhds x]
        (fun t : ℝ => factorized t y z * Real.log (t / y)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    rw [gap8 t y z ⟨ht, hy⟩, gap1 t y z ⟨ht, hy⟩]
  have hpow : HasDerivAt (fun t : ℝ => Real.rpow t z)
      (z * Real.rpow x (z - 1)) x :=
    Real.hasDerivAt_rpow_const (p := z) (Or.inl (ne_of_gt hx))
  have hf : HasDerivAt (fun t : ℝ => factorized t y z)
      (z * Real.rpow x (z - 1) * Real.rpow y (-z)) x := by
    simpa [factorized] using
      hpow.mul_const (Real.rpow y (-z))
  have hquot : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
    simpa using (hasDerivAt_id x).div_const y
  have hlogBase : HasDerivAt Real.log (1 / (x / y)) (x / y) := by
    simpa using Real.hasDerivAt_log (div_ne_zero (ne_of_gt hx) (ne_of_gt hy))
  have hlog : HasDerivAt (fun t : ℝ => Real.log (t / y)) (1 / x) x := by
    have hc := hlogBase.comp x hquot
    convert hc using 1
    field_simp [ne_of_gt hx, ne_of_gt hy]
  change deriv (fun t : ℝ => partialZ u t y z) x = _
  rw [heq.deriv_eq]
  calc
    deriv (fun t : ℝ => factorized t y z * Real.log (t / y)) x =
        (z * Real.rpow x (z - 1) * Real.rpow y (-z)) *
            Real.log (x / y) + factorized x y z * (1 / x) :=
      (hf.mul hlog).deriv
    _ = (z / x) * u x y z * Real.log (x / y) +
          (1 / x) * u x y z := by
      rw [gap3 z x y hadm, ← gap1 x y z hadm]
      ring

theorem gap23 :
    ∀ z x y : ℝ, admissible x y →
      (z / x) * u x y z * Real.log (x / y) +
          (1 / x) * u x y z =
        ((1 + z * Real.log (x / y)) / x) * u x y z := by
  intro z x y h
  rcases h with ⟨hx, hy⟩
  field_simp [ne_of_gt hx]
  <;> ring

theorem gap24 :
    ∀ x y z : ℝ, admissible x y →
      mixedZX u x y z =
        ((1 + z * Real.log (x / y)) / x) * u x y z := by
  intro x y z h
  rw [gap22 x y z h, gap23 z x y h]

end

end ProofGap.Exercise3226
