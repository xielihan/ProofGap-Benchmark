import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2085
noncomputable section

def xOfT (t : ℝ) := 6 * Real.log t
def f (x : ℝ) :=
  1 / (1 + Real.exp (x / 2) + Real.exp (x / 3) + Real.exp (x / 6))
def tKernel (t : ℝ) := 1 / (t * (t + 1) * (t ^ 2 + 1))
def partialKernel (t : ℝ) :=
  1 / t - 1 / (2 * (t + 1)) - (t + 1) / (2 * (t ^ 2 + 1))
def tPrimitive (t : ℝ) :=
  6 * Real.log t - 3 * Real.log (t + 1) -
    (3 / 2 : ℝ) * Real.log (1 + t ^ 2) - 3 * Real.arctan t
def xPrimitive (x : ℝ) :=
  x - 3 * Real.log ((1 + Real.exp (x / 6)) * Real.sqrt (1 + Real.exp (x / 3))) -
    3 * Real.arctan (Real.exp (x / 6))
def Family (U : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def PullbackFamily (A : Set (ℝ → ℝ)) :=
  {G : ℝ → ℝ | ∃ F ∈ A, ∀ t ∈ Set.Ioi (0 : ℝ), G t = F (xOfT t)}
def ScaledFamily (g : ℝ → ℝ) :=
  {G : ℝ → ℝ | ∃ H ∈ Family (Set.Ioi 0) g, ∃ C,
    ∀ t ∈ Set.Ioi (0 : ℝ), G t = 6 * H t + C}
def TTranslates := {G : ℝ → ℝ | ∃ C,
  ∀ t ∈ Set.Ioi (0 : ℝ), G t = tPrimitive t + C}
def XTranslates := {F : ℝ → ℝ | ∃ C, ∀ x, F x = xPrimitive x + C}

private lemma exp_xOfT_div_six (t : ℝ) (ht : 0 < t) :
    Real.exp (xOfT t / 6) = t := by
  unfold xOfT
  convert Real.exp_log ht using 1 <;> ring

private lemma f_exp_form (x : ℝ) :
    f x = 1 / (1 + (Real.exp (x / 6)) ^ 3 +
      (Real.exp (x / 6)) ^ 2 + Real.exp (x / 6)) := by
  have h2 : Real.exp (x / 3) = (Real.exp (x / 6)) ^ 2 := by
    calc
      Real.exp (x / 3) = Real.exp (x / 6 + x / 6) := by congr 1 <;> ring
      _ = (Real.exp (x / 6)) ^ 2 := by rw [Real.exp_add]; ring
  have h3 : Real.exp (x / 2) = (Real.exp (x / 6)) ^ 3 := by
    calc
      Real.exp (x / 2) = Real.exp (x / 6 + x / 6 + x / 6) := by
        congr 1 <;> ring
      _ = (Real.exp (x / 6)) ^ 3 := by
        rw [Real.exp_add, Real.exp_add]
        ring
  unfold f
  rw [h3, h2]

private lemma f_xOfT (t : ℝ) (ht : 0 < t) :
    f (xOfT t) = 1 / (1 + t ^ 3 + t ^ 2 + t) := by
  rw [f_exp_form, exp_xOfT_div_six t ht]

private lemma hasDerivAt_exp_div_six (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (y / 6))
      (Real.exp (x / 6) / 6) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
    simpa using hasDerivAt_id x
  have hlin : HasDerivAt (fun y : ℝ => y / 6) (1 / 6 : ℝ) x := by
    convert hid.const_mul (1 / 6 : ℝ) using 1 <;> ring
  convert (Real.hasDerivAt_exp (x / 6)).comp x hlin using 1 <;> ring

private lemma tKernel_eq_partialKernel {t : ℝ} (ht : 0 < t) :
    tKernel t = partialKernel t := by
  have ht1 : t + 1 ≠ 0 := by linarith
  have ht2 : t ^ 2 + 1 ≠ 0 := by positivity
  unfold tKernel partialKernel
  field_simp [ht.ne', ht1, ht2]
  <;> ring

private lemma hasDerivAt_tPrimitive (t : ℝ) (ht : 0 < t) :
    HasDerivAt tPrimitive (6 * partialKernel t) t := by
  have ht1 : t + 1 ≠ 0 := by linarith
  have ht2 : 1 + t ^ 2 ≠ 0 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 t := by
    simpa using hasDerivAt_id t
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log (x + 1))
      (1 / (t + 1)) t := by
    convert (Real.hasDerivAt_log ht1).comp t
      (hid.add_const 1) using 1 <;> ring
  have hpoly : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * t) t := by
    convert (hid.pow 2).add_const 1 using 1 <;> try ring
    apply funext
    intro x
    simp
  have hlog2 : HasDerivAt (fun x : ℝ => Real.log (1 + x ^ 2))
      ((1 / (1 + t ^ 2)) * (2 * t)) t := by
    convert (Real.hasDerivAt_log ht2).comp t hpoly using 1 <;> ring
  have h :=
    ((((Real.hasDerivAt_log ht.ne').const_mul 6).sub
      (hlog1.const_mul 3)).sub
      (hlog2.const_mul (3 / 2 : ℝ))).sub
      ((Real.hasDerivAt_arctan t).const_mul 3)
  unfold tPrimitive
  convert h using 1
  unfold partialKernel
  field_simp [ht.ne', ht1, ht2]
  <;> ring

private lemma tKernel_mul_exp_eq_f (x : ℝ) :
    tKernel (Real.exp (x / 6)) * Real.exp (x / 6) = f x := by
  let t := Real.exp (x / 6)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t + 1 ≠ 0 := by linarith
  have ht2 : t ^ 2 + 1 ≠ 0 := by positivity
  have hden : 1 + t ^ 3 + t ^ 2 + t ≠ 0 := by positivity
  rw [f_exp_form]
  change tKernel t * t = 1 / (1 + t ^ 3 + t ^ 2 + t)
  unfold tKernel
  field_simp [ht.ne', ht1, ht2, hden]
  <;> ring

private lemma tPrimitive_exp_eq_xPrimitive (x : ℝ) :
    tPrimitive (Real.exp (x / 6)) = xPrimitive x := by
  have h2 : Real.exp (x / 3) = (Real.exp (x / 6)) ^ 2 := by
    calc
      Real.exp (x / 3) = Real.exp (x / 6 + x / 6) := by congr 1 <;> ring
      _ = (Real.exp (x / 6)) ^ 2 := by rw [Real.exp_add]; ring
  have hadd : Real.exp (x / 6) + 1 = 1 + Real.exp (x / 6) := by ring
  unfold tPrimitive xPrimitive
  rw [Real.log_exp]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_sqrt (by positivity)]
  rw [h2, hadd]
  ring

private lemma hasDerivAt_xPrimitive (x : ℝ) :
    HasDerivAt xPrimitive (f x) x := by
  have hfun : xPrimitive = fun y => tPrimitive (Real.exp (y / 6)) := by
    funext y
    exact (tPrimitive_exp_eq_xPrimitive y).symm
  rw [hfun]
  let t := Real.exp (x / 6)
  have ht : 0 < t := Real.exp_pos _
  have hd := (hasDerivAt_tPrimitive t ht).comp x (hasDerivAt_exp_div_six x)
  have hk : partialKernel t = tKernel t := (tKernel_eq_partialKernel ht).symm
  have hf : tKernel t * t = f x := by
    dsimp [t]
    exact tKernel_mul_exp_eq_f x
  have hcoef :
      (6 * partialKernel t) * (Real.exp (x / 6) / 6) = f x := by
    change (6 * partialKernel t) * (t / 6) = f x
    rw [hk]
    calc
      (6 * tKernel t) * (t / 6) = tKernel t * t := by ring
      _ = f x := hf
  convert hd using 1
  exact hcoef.symm

private lemma scaledPartial_eq_TTranslates :
    ScaledFamily partialKernel = TTranslates := by
  ext G
  constructor
  · rintro ⟨H, hH, C, hG⟩
    let D : ℝ → ℝ := fun t => 6 * H t - tPrimitive t
    have hD : ∀ t, t ∈ Set.Ioi (0 : ℝ) → HasDerivAt D 0 t := by
      intro t ht
      dsimp [D]
      convert ((hH t ht).const_mul 6).sub (hasDerivAt_tPrimitive t ht) using 1
      <;> ring
    have hK : ∀ x : ℝ, HasDerivAt (fun y => D (Real.exp y)) 0 x := by
      intro x
      simpa using (hD (Real.exp x) (Real.exp_pos x)).comp x
        (Real.hasDerivAt_exp x)
    have hconst : ∀ t : ℝ, 0 < t → D t = D 1 := by
      intro t ht
      have hc := is_const_of_deriv_eq_zero
        (fun x => (hK x).differentiableAt)
        (fun x => (hK x).deriv) (Real.log t) 0
      simpa [Real.exp_log ht] using hc
    refine ⟨C + D 1, ?_⟩
    intro t ht
    have hd := hconst t ht
    rw [hG t ht]
    dsimp [D] at hd ⊢
    linarith
  · rintro ⟨C, hG⟩
    refine ⟨(fun t => (1 / 6 : ℝ) * tPrimitive t), ?_, C, ?_⟩
    · intro t ht
      convert (hasDerivAt_tPrimitive t ht).const_mul (1 / 6 : ℝ) using 1
      <;> ring
    · intro t ht
      rw [hG t ht]
      ring

theorem gap1 (t : ℝ) : xOfT t = 6 * Real.log t := by
  rfl
theorem gap2 (t : ℝ) (ht : 0 < t) :
    HasDerivAt xOfT (6 / t) t := by
  unfold xOfT
  convert (Real.hasDerivAt_log ht.ne').const_mul 6 using 1 <;> ring
theorem gap3 :
    PullbackFamily (Family Set.univ f) =
      ScaledFamily (fun t => 1 / (t * (1 + t ^ 3 + t ^ 2 + t))) := by
  ext G
  constructor
  · rintro ⟨F, hF, hG⟩
    refine ⟨(fun t => (1 / 6 : ℝ) * F (xOfT t)), ?_, 0, ?_⟩
    · intro t ht
      have ht0 : 0 < t := ht
      have ht3 : 0 < t ^ 3 := pow_pos ht0 3
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      have hden : 1 + t ^ 3 + t ^ 2 + t ≠ 0 := by linarith
      have hd :=
        ((hF (xOfT t) (Set.mem_univ _)).comp t (gap2 t ht0)).const_mul
          (1 / 6 : ℝ)
      convert hd using 1
      rw [f_xOfT t ht0]
      field_simp [ht0.ne', hden]
      <;> ring
    · intro t ht
      rw [hG t ht]
      ring
  · rintro ⟨H, hH, C, hG⟩
    refine ⟨(fun x => 6 * H (Real.exp (x / 6)) + C), ?_, ?_⟩
    · intro x hx
      let s := Real.exp (x / 6)
      have hs : 0 < s := Real.exp_pos _
      have hs3 : 0 < s ^ 3 := pow_pos hs 3
      have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
      have hden : 1 + s ^ 3 + s ^ 2 + s ≠ 0 := by linarith
      have hd :=
        (((hH s hs).comp x (hasDerivAt_exp_div_six x)).const_mul 6).add_const C
      convert hd using 1
      rw [f_exp_form]
      dsimp [s]
      field_simp [hs.ne', hden]
      <;> ring
    · intro t ht
      have ht0 : 0 < t := ht
      rw [hG t ht]
      change 6 * H t + C = 6 * H (Real.exp (xOfT t / 6)) + C
      rw [exp_xOfT_div_six t ht0]
theorem gap4 :
    PullbackFamily (Family Set.univ f) = ScaledFamily tKernel := by
  have hfun :
      (fun t : ℝ => 1 / (t * (1 + t ^ 3 + t ^ 2 + t))) = tKernel := by
    funext t
    unfold tKernel
    congr 1
    ring
  rw [gap3, hfun]
theorem gap5 : ScaledFamily tKernel = ScaledFamily partialKernel := by
  have hfamily :
      Family (Set.Ioi 0) tKernel = Family (Set.Ioi 0) partialKernel := by
    ext H
    constructor
    · intro h t ht
      simpa only [tKernel_eq_partialKernel ht] using h t ht
    · intro h t ht
      simpa only [tKernel_eq_partialKernel ht] using h t ht
  unfold ScaledFamily
  rw [hfamily]
theorem gap6 :
    PullbackFamily (Family Set.univ f) = ScaledFamily partialKernel := by
  calc
    PullbackFamily (Family Set.univ f) = ScaledFamily tKernel := gap4
    _ = ScaledFamily partialKernel := gap5
theorem gap7 : PullbackFamily (Family Set.univ f) = TTranslates := by
  calc
    PullbackFamily (Family Set.univ f) = ScaledFamily partialKernel := gap6
    _ = TTranslates := scaledPartial_eq_TTranslates
theorem gap8 : Family Set.univ f = XTranslates := by
  ext F
  constructor
  · intro hF
    have hPull :
        (fun t => F (xOfT t)) ∈ PullbackFamily (Family Set.univ f) :=
      ⟨F, hF, fun t ht => rfl⟩
    have hTrans : (fun t => F (xOfT t)) ∈ TTranslates := by
      rw [← gap7]
      exact hPull
    rcases hTrans with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x
    have hx : xOfT (Real.exp (x / 6)) = x := by
      unfold xOfT
      rw [Real.log_exp]
      ring
    calc
      F x = F (xOfT (Real.exp (x / 6))) := by rw [hx]
      _ = tPrimitive (Real.exp (x / 6)) + C :=
        hC (Real.exp (x / 6)) (Real.exp_pos _)
      _ = xPrimitive x + C := by rw [tPrimitive_exp_eq_xPrimitive]
  · rintro ⟨C, hF⟩
    have hfun : F = fun x => xPrimitive x + C := funext hF
    rw [hfun]
    intro x hx
    exact (hasDerivAt_xPrimitive x).add_const C

end
end ProofGap.Exercise2085
