import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3444

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

def dByX (f x : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 f t / d1 x t

def d2ByX (f x : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 (dByX f x) t / d1 x t

def regular (a b : ℝ) (x : ℝ → ℝ) (t : ℝ) : Prop :=
  x t ≠ a ∧ x t ≠ b ∧ a ≠ b

private theorem eventually_regular {a b : ℝ} {x : ℝ → ℝ} {t : ℝ}
    (hx : Continuous x) (ht : regular a b x t) :
    ∀ᶠ s in nhds t, regular a b x s := by
  have ha : ∀ᶠ s in nhds t, x s - a ≠ 0 :=
    (hx.continuousAt.sub continuousAt_const).eventually_ne
      (sub_ne_zero.mpr ht.1)
  have hb : ∀ᶠ s in nhds t, x s - b ≠ 0 :=
    (hx.continuousAt.sub continuousAt_const).eventually_ne
      (sub_ne_zero.mpr ht.2.1)
  filter_upwards [ha, hb] with s hsa hsb
  exact ⟨sub_ne_zero.mp hsa, sub_ne_zero.mp hsb, ht.2.2⟩

theorem gap1 (a b : ℝ) (x : ℝ → ℝ)
    (hTransform :
      ∀ t, regular a b x t →
        t = Real.log |(x t - a) / (x t - b)|) :
    ∀ t, regular a b x t →
      t = Real.log |x t - a| - Real.log |x t - b| := by
  intro t ht
  have hxa : x t - a ≠ 0 := sub_ne_zero.mpr ht.1
  have hxb : x t - b ≠ 0 := sub_ne_zero.mpr ht.2.1
  calc
    t = Real.log |(x t - a) / (x t - b)| := hTransform t ht
    _ = Real.log |x t - a| - Real.log |x t - b| := by
      rw [abs_div, Real.log_div (abs_ne_zero.mpr hxa) (abs_ne_zero.mpr hxb)]

theorem gap2 (a b : ℝ) (x : ℝ → ℝ)
    (hLogDifference :
      ∀ t, regular a b x t →
        t = Real.log |x t - a| - Real.log |x t - b|)
    (hx : ContDiff ℝ 1 x) :
    ∀ t, regular a b x t →
      dByX id x t =
        1 / (x t - a) - 1 / (x t - b) := by
  intro t ht
  have hxa : x t - a ≠ 0 := sub_ne_zero.mpr ht.1
  have hxb : x t - b ≠ 0 := sub_ne_zero.mpr ht.2.1
  have hdx : HasDerivAt x (d1 x t) t := by
    simpa [d1] using
      (hx.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have heq :
      id =ᶠ[nhds t]
        fun s => Real.log (x s - a) - Real.log (x s - b) := by
    filter_upwards [eventually_regular hx.continuous ht] with s hs
    simpa [id, Real.log_abs] using hLogDifference s hs
  have hright :=
    ((Real.hasDerivAt_log hxa).comp t (hdx.sub_const a)).sub
      ((Real.hasDerivAt_log hxb).comp t (hdx.sub_const b))
  have hd :
      1 = d1 x t / (x t - a) - d1 x t / (x t - b) := by
    calc
      1 = deriv id t := by simp
      _ = deriv (fun s => Real.log (x s - a) - Real.log (x s - b)) t :=
        heq.deriv_eq
      _ = d1 x t / (x t - a) - d1 x t / (x t - b) := by
        simpa [d1, div_eq_mul_inv, mul_comm] using hright.deriv
  have hdx0 : d1 x t ≠ 0 := by
    intro hz
    simp [hz] at hd
  have hrecip :
      1 / d1 x t = 1 / (x t - a) - 1 / (x t - b) := by
    calc
      1 / d1 x t = (1 / d1 x t) * 1 := by ring
      _ = (1 / d1 x t) *
          (d1 x t / (x t - a) - d1 x t / (x t - b)) := by rw [hd]
      _ = 1 / (x t - a) - 1 / (x t - b) := by
        field_simp [hdx0, hxa, hxb]
        <;> ring
  simpa [dByX, d1] using hrecip

theorem gap3 (a b : ℝ) (x : ℝ → ℝ) :
    ∀ t, regular a b x t →
      1 / (x t - a) - 1 / (x t - b) =
        (a - b) / ((x t - a) * (x t - b)) := by
  intro t ht
  have hxa : x t - a ≠ 0 := sub_ne_zero.mpr ht.1
  have hxb : x t - b ≠ 0 := sub_ne_zero.mpr ht.2.1
  field_simp [hxa, hxb]
  ring

theorem gap4 (a b : ℝ) (x : ℝ → ℝ)
    (hDifferentiate :
      ∀ t, regular a b x t →
        dByX id x t =
          1 / (x t - a) - 1 / (x t - b))
    (hCollect :
      ∀ t, regular a b x t →
        1 / (x t - a) - 1 / (x t - b) =
          (a - b) / ((x t - a) * (x t - b))) :
    ∀ t, regular a b x t →
      dByX id x t =
        (a - b) / ((x t - a) * (x t - b)) := by
  intro t ht
  exact (hDifferentiate t ht).trans (hCollect t ht)

theorem gap5 (a b : ℝ) (x : ℝ → ℝ)
    (hReciprocal :
      ∀ t, regular a b x t →
        dByX id x t =
          (a - b) / ((x t - a) * (x t - b))) :
    ∀ t, regular a b x t →
      d1 x t =
        ((x t - a) * (x t - b)) / (a - b) := by
  intro t ht
  have hi := congrArg (fun z : ℝ => z⁻¹) (hReciprocal t ht)
  simpa [dByX, d1, inv_div] using hi

theorem gap6 (a b : ℝ) (x y u : ℝ → ℝ)
    (hU :
      ∀ t, regular a b x t →
        u t = y t / (x t - b)) :
    ∀ t, regular a b x t →
      y t = u t * (x t - b) := by
  intro t ht
  have hxb : x t - b ≠ 0 := sub_ne_zero.mpr ht.2.1
  rw [hU t ht]
  field_simp [hxb]

theorem gap7 (a b : ℝ) (x y u : ℝ → ℝ)
    (hY :
      ∀ t, regular a b x t →
        y t = u t * (x t - b))
    (hXDerivative :
      ∀ t, regular a b x t →
        d1 x t =
          ((x t - a) * (x t - b)) / (a - b))
    (hx : ContDiff ℝ 1 x)
    (hu : ContDiff ℝ 1 u) :
    ∀ t, regular a b x t →
      dByX y x t =
        (x t - b) * dByX u x t + u t := by
  intro t ht
  have hxa : x t - a ≠ 0 := sub_ne_zero.mpr ht.1
  have hxb : x t - b ≠ 0 := sub_ne_zero.mpr ht.2.1
  have hab : a - b ≠ 0 := sub_ne_zero.mpr ht.2.2
  have hdx : HasDerivAt x (d1 x t) t := by
    simpa [d1] using
      (hx.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdu : HasDerivAt u (d1 u t) t := by
    simpa [d1] using
      (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have heq : y =ᶠ[nhds t] fun s => u s * (x s - b) := by
    filter_upwards [eventually_regular hx.continuous ht] with s hs
    exact hY s hs
  have hder :
      d1 y t = d1 u t * (x t - b) + u t * d1 x t := by
    calc
      d1 y t = deriv (fun s => u s * (x s - b)) t := by
        simpa [d1] using heq.deriv_eq
      _ = d1 u t * (x t - b) + u t * d1 x t := by
        simpa [d1] using (hdu.mul (hdx.sub_const b)).deriv
  have hdx0 : d1 x t ≠ 0 := by
    rw [hXDerivative t ht]
    exact div_ne_zero (mul_ne_zero hxa hxb) hab
  change d1 y t / d1 x t =
    (x t - b) * (d1 u t / d1 x t) + u t
  rw [hder]
  field_simp [hdx0]

theorem gap8 (a b : ℝ) (x u : ℝ → ℝ)
    (hXDerivative :
      ∀ t, regular a b x t →
        d1 x t =
          ((x t - a) * (x t - b)) / (a - b)) :
    ∀ t, regular a b x t →
      (x t - b) * dByX u x t + u t =
        (a - b) * d1 u t / (x t - a) + u t := by
  intro t ht
  have hxa : x t - a ≠ 0 := sub_ne_zero.mpr ht.1
  have hxb : x t - b ≠ 0 := sub_ne_zero.mpr ht.2.1
  have hab : a - b ≠ 0 := sub_ne_zero.mpr ht.2.2
  change (x t - b) * (d1 u t / d1 x t) + u t =
    (a - b) * d1 u t / (x t - a) + u t
  rw [hXDerivative t ht]
  field_simp [hxa, hxb, hab]

theorem gap9 (a b : ℝ) (x y u : ℝ → ℝ)
    (hProduct :
      ∀ t, regular a b x t →
        dByX y x t =
          (x t - b) * dByX u x t + u t)
    (hConvert :
      ∀ t, regular a b x t →
        (x t - b) * dByX u x t + u t =
          (a - b) * d1 u t / (x t - a) + u t) :
    ∀ t, regular a b x t →
      dByX y x t =
        (a - b) * d1 u t / (x t - a) + u t := by
  intro t ht
  exact (hProduct t ht).trans (hConvert t ht)

theorem gap10 (a b : ℝ) (x y u : ℝ → ℝ)
    (hXDerivative :
      ∀ t, regular a b x t →
        d1 x t =
          ((x t - a) * (x t - b)) / (a - b))
    (hFirst :
      ∀ t, regular a b x t →
        dByX y x t =
          (a - b) * d1 u t / (x t - a) + u t)
    (hx : ContDiff ℝ 2 x)
    (hu : ContDiff ℝ 2 u) :
    ∀ t, regular a b x t →
      d2ByX y x t =
        (a - b) ^ 2 * (d2 u t - d1 u t) /
          ((x t - a) ^ 2 * (x t - b)) := by
  intro t ht
  have hxa : x t - a ≠ 0 := sub_ne_zero.mpr ht.1
  have hxb : x t - b ≠ 0 := sub_ne_zero.mpr ht.2.1
  have hab : a - b ≠ 0 := sub_ne_zero.mpr ht.2.2
  have hxFull := (contDiff_succ_iff_deriv (n := 1)).mp hx
  have huFull := (contDiff_succ_iff_deriv (n := 1)).mp hu
  have hxData :
      Differentiable ℝ x ∧ ContDiff ℝ 1 (deriv x) :=
    ⟨hxFull.1, hxFull.2.2⟩
  have huData :
      Differentiable ℝ u ∧ ContDiff ℝ 1 (deriv u) :=
    ⟨huFull.1, huFull.2.2⟩
  have hduDiff : Differentiable ℝ (deriv u) := by
    exact ((contDiff_succ_iff_deriv (n := 0)).mp huData.2).1
  have hdx : HasDerivAt x (d1 x t) t := by
    simpa [d1] using hxData.1.differentiableAt.hasDerivAt
  have hdu : HasDerivAt u (d1 u t) t := by
    simpa [d1] using huData.1.differentiableAt.hasDerivAt
  have hdu2 : HasDerivAt (deriv u) (d2 u t) t := by
    simpa [d2] using hduDiff.differentiableAt.hasDerivAt
  have heq :
      dByX y x =ᶠ[nhds t]
        fun s => (a - b) * d1 u s / (x s - a) + u s := by
    filter_upwards [eventually_regular hx.continuous ht] with s hs
    exact hFirst s hs
  have hformula :
      HasDerivAt
        (fun s => (a - b) * d1 u s / (x s - a) + u s)
        (((a - b) * d2 u t * (x t - a) -
            (a - b) * d1 u t * d1 x t) / (x t - a) ^ 2 + d1 u t) t := by
    simpa [d1, d2, mul_assoc] using
      (((hdu2.const_mul (a - b)).div (hdx.sub_const a) hxa).add hdu)
  have hmain :
      d1 (dByX y x) t =
        ((a - b) * d2 u t * (x t - a) -
            (a - b) * d1 u t * d1 x t) / (x t - a) ^ 2 + d1 u t := by
    calc
      d1 (dByX y x) t =
          deriv (fun s => (a - b) * d1 u s / (x s - a) + u s) t := by
        simpa [d1] using heq.deriv_eq
      _ = ((a - b) * d2 u t * (x t - a) -
            (a - b) * d1 u t * d1 x t) / (x t - a) ^ 2 + d1 u t :=
        hformula.deriv
  unfold d2ByX
  rw [hmain, hXDerivative t ht]
  field_simp [hxa, hxb, hab] <;> ring

theorem gap11 (A a b : ℝ) (x y u : ℝ → ℝ)
    (hODE :
      ∀ t, regular a b x t →
        d2ByX y x t =
          A * y t / ((x t - a) ^ 2 * (x t - b) ^ 2))
    (hY :
      ∀ t, regular a b x t →
        y t = u t * (x t - b))
    (hSecond :
      ∀ t, regular a b x t →
        d2ByX y x t =
          (a - b) ^ 2 * (d2 u t - d1 u t) /
            ((x t - a) ^ 2 * (x t - b))) :
    ∀ t, regular a b x t →
      d2 u t - d1 u t = A * u t / (a - b) ^ 2 := by
  intro t ht
  have hxa : x t - a ≠ 0 := sub_ne_zero.mpr ht.1
  have hxb : x t - b ≠ 0 := sub_ne_zero.mpr ht.2.1
  have hab : a - b ≠ 0 := sub_ne_zero.mpr ht.2.2
  let den : ℝ := (x t - a) ^ 2 * (x t - b)
  have hden : den ≠ 0 := by
    dsimp [den]
    exact mul_ne_zero (pow_ne_zero 2 hxa) hxb
  have hcommon :
      (a - b) ^ 2 * (d2 u t - d1 u t) / den =
        A * u t / den := by
    calc
      (a - b) ^ 2 * (d2 u t - d1 u t) / den = d2ByX y x t := by
        simpa [den] using (hSecond t ht).symm
      _ = A * y t / ((x t - a) ^ 2 * (x t - b) ^ 2) := hODE t ht
      _ = A * (u t * (x t - b)) /
          ((x t - a) ^ 2 * (x t - b) ^ 2) := by rw [hY t ht]
      _ = A * u t / den := by
        dsimp [den]
        field_simp [hxa, hxb]
  have hnum := congrArg (fun z : ℝ => z * den) hcommon
  field_simp [hden] at hnum
  apply (eq_div_iff (pow_ne_zero 2 hab)).2
  simpa [mul_comm] using hnum

end

end ProofGap.Exercise3444
