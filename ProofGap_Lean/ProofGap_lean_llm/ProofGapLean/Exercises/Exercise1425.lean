import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1425

noncomputable section

def f (x : ℝ) : ℝ :=
  if x = 0 then 2 else 2 - x ^ 2 * (2 + Real.sin (1 / x))

private theorem trig_turn (n : ℕ) :
    Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 ∧
      Real.cos ((n : ℝ) * (2 * Real.pi)) = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      constructor
      · rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add,
          ih.1, ih.2, Real.sin_two_pi, Real.cos_two_pi]
        norm_num
      · rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add,
          ih.1, ih.2, Real.sin_two_pi, Real.cos_two_pi]
        norm_num

private theorem exists_small_turn (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ,
      0 < (n : ℝ) * (2 * Real.pi) ∧
      1 / ((n : ℝ) * (2 * Real.pi)) < δ ∧
      4 < (n : ℝ) * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / (2 * Real.pi * δ)) 1)
  have hnfrac : 1 / (2 * Real.pi * δ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : 1 < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hscale : 0 < 2 * Real.pi * δ := by positivity
  have hden : 0 < (n : ℝ) * (2 * Real.pi) := by positivity
  have hone : 1 < (n : ℝ) * (2 * Real.pi * δ) :=
    (div_lt_iff₀ hscale).mp hnfrac
  have hone' : 1 < δ * ((n : ℝ) * (2 * Real.pi)) := by
    convert hone using 1 <;> ring
  have hsmall : 1 / ((n : ℝ) * (2 * Real.pi)) < δ :=
    (div_lt_iff₀ hden).2 hone'
  have hmul : 0 < ((n : ℝ) - 1) * Real.pi :=
    mul_pos (sub_pos.mpr hn1) Real.pi_pos
  have hfour : 4 < (n : ℝ) * (2 * Real.pi) := by
    nlinarith [Real.pi_gt_three]
  exact ⟨n, hden, hsmall, hfour⟩

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    f x - f 0 = -x ^ 2 * (2 + Real.sin (1 / x)) := by
  simp [f, hx]
  <;> ring

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    -x ^ 2 * (2 + Real.sin (1 / x)) < 0 := by
  have hs : 0 < 2 + Real.sin (1 / x) := by
    nlinarith [Real.neg_one_le_sin (1 / x)]
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hp : 0 < x ^ 2 * (2 + Real.sin (1 / x)) := mul_pos hx2 hs
  nlinarith

theorem gap3 (x : ℝ) (hx : x ≠ 0) : f x - f 0 < 0 := by
  rw [gap1 x hx]
  exact gap2 x hx

theorem gap4 : IsMaxOn f Set.univ 0 := by
  intro x hx
  change f x ≤ f 0
  by_cases h0 : x = 0
  · subst x
    exact le_rfl
  · have h := gap3 x h0
    linarith

theorem gap5 : f 0 = 2 := by
  simp [f]

theorem gap6 (x : ℝ) (hx : x ≠ 0) :
    deriv f x =
      Real.cos (1 / x) - 2 * x * (2 + Real.sin (1 / x)) := by
  have hinv :
      HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
      simp [one_div]
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num <;> ring
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (1 / y))
        (Real.cos (1 / x) * (-1 / x ^ 2)) x :=
    (Real.hasDerivAt_sin (1 / x)).comp x hinv
  have hmain :
      HasDerivAt
        (fun y : ℝ => 2 - y ^ 2 * (2 + Real.sin (1 / y)))
        (0 - (2 * x * (2 + Real.sin (1 / x)) +
          x ^ 2 * (0 + Real.cos (1 / x) * (-1 / x ^ 2)))) x :=
    (hasDerivAt_const x (2 : ℝ)).sub
      (hpow.mul ((hasDerivAt_const x (2 : ℝ)).add hsin))
  have hcoeff :
      0 - (2 * x * (2 + Real.sin (1 / x)) +
          x ^ 2 * (0 + Real.cos (1 / x) * (-1 / x ^ 2))) =
        Real.cos (1 / x) - 2 * x * (2 + Real.sin (1 / x)) := by
    field_simp [hx]
    ring
  rw [hcoeff] at hmain
  have hopen : IsOpen (({0} : Set ℝ)ᶜ) := isClosed_singleton.isOpen_compl
  have hmem : x ∈ (({0} : Set ℝ)ᶜ) := by
    simpa using hx
  have heq :
      f =ᶠ[nhds x] (fun y : ℝ => 2 - y ^ 2 * (2 + Real.sin (1 / y))) := by
    filter_upwards [hopen.mem_nhds hmem] with y hy
    have hy0 : y ≠ 0 := by
      simpa using hy
    simp [f, hy0]
  calc
    deriv f x = deriv (fun y : ℝ => 2 - y ^ 2 * (2 + Real.sin (1 / y))) x :=
      heq.deriv_eq
    _ = Real.cos (1 / x) - 2 * x * (2 + Real.sin (1 / x)) := hmain.deriv

theorem gap7 :
    ∀ δ > 0, ∃ x₁ ∈ Set.Ioo (-δ) δ, ∃ x₂ ∈ Set.Ioo (-δ) δ,
      0 < deriv f x₁ ∧ deriv f x₂ < 0 := by
  intro δ hδ
  obtain ⟨n, htpos, htδ, ht4⟩ := exists_small_turn δ hδ
  let t : ℝ := (n : ℝ) * (2 * Real.pi)
  let u : ℝ := t + Real.pi
  have htpos' : 0 < t := by simpa [t] using htpos
  have htδ' : 1 / t < δ := by simpa [t] using htδ
  have ht4' : 4 < t := by simpa [t] using ht4
  have hturn : Real.sin t = 0 ∧ Real.cos t = 1 := by
    simpa [t] using trig_turn n
  have hupos : 0 < u := by
    dsimp [u]
    linarith [Real.pi_pos]
  have htu : t < u := by
    dsimp [u]
    linarith [Real.pi_pos]
  have huδ : 1 / u < δ := by
    have hrev : 1 / u < 1 / t := by
      apply (div_lt_div_iff₀ hupos htpos').2
      simpa using htu
    exact lt_trans hrev htδ'
  have hsu : Real.sin u = 0 := by
    change Real.sin (t + Real.pi) = 0
    rw [Real.sin_add, hturn.1, hturn.2, Real.sin_pi, Real.cos_pi]
    norm_num
  have hcu : Real.cos u = -1 := by
    change Real.cos (t + Real.pi) = -1
    rw [Real.cos_add, hturn.1, hturn.2, Real.sin_pi, Real.cos_pi]
    norm_num
  have hinvt : 1 / (1 / t) = t := by
    field_simp [ne_of_gt htpos']
  have hinvu : 1 / (1 / u) = u := by
    field_simp [ne_of_gt hupos]
  have hxt : 0 < 1 / t := one_div_pos.mpr htpos'
  have hxu : 0 < 1 / u := one_div_pos.mpr hupos
  have hsmall : 4 * (1 / t) < 1 := by
    have hquot : 4 / t < 1 := (div_lt_one htpos').2 ht4'
    simpa [div_eq_mul_inv] using hquot
  have hd1 := gap6 (1 / t) (ne_of_gt hxt)
  rw [hinvt, hturn.1, hturn.2] at hd1
  have hd1pos : 0 < deriv f (1 / t) := by
    rw [hd1]
    nlinarith
  have hd2 := gap6 (1 / u) (ne_of_gt hxu)
  rw [hinvu, hsu, hcu] at hd2
  have hd2neg : deriv f (1 / u) < 0 := by
    rw [hd2]
    nlinarith
  refine ⟨1 / t, ⟨?_, htδ'⟩, 1 / u, ⟨?_, huδ⟩, hd1pos, hd2neg⟩
  · linarith
  · linarith

theorem gap8 :
    ∀ δ > 0,
      ¬ (MonotoneOn f (Set.Ioo (-δ) 0) ∧
        AntitoneOn f (Set.Ioo 0 δ)) := by
  intro δ hδ hmon
  obtain ⟨n, htpos, htδ, ht4⟩ := exists_small_turn δ hδ
  let t : ℝ := (n : ℝ) * (2 * Real.pi)
  let a : ℝ := t + Real.pi + Real.pi / 2
  let b : ℝ := a + Real.pi
  have htpos' : 0 < t := by simpa [t] using htpos
  have htδ' : 1 / t < δ := by simpa [t] using htδ
  have hturn : Real.sin t = 0 ∧ Real.cos t = 1 := by
    simpa [t] using trig_turn n
  have hapos : 0 < a := by
    dsimp [a]
    nlinarith [Real.pi_pos]
  have hbpos : 0 < b := by
    dsimp [b]
    linarith [hapos, Real.pi_pos]
  have hta : t < a := by
    dsimp [a]
    nlinarith [Real.pi_pos]
  have hab : a < b := by
    dsimp [b]
    linarith [Real.pi_pos]
  have hxaδ : 1 / a < δ := by
    have hrev : 1 / a < 1 / t := by
      apply (div_lt_div_iff₀ hapos htpos').2
      simpa using hta
    exact lt_trans hrev htδ'
  have hxbδ : 1 / b < δ := by
    have hrev : 1 / b < 1 / a := by
      apply (div_lt_div_iff₀ hbpos hapos).2
      simpa using hab
    exact lt_trans hrev hxaδ
  have hxa : 0 < 1 / a := one_div_pos.mpr hapos
  have hxb : 0 < 1 / b := one_div_pos.mpr hbpos
  have hsina : Real.sin a = -1 := by
    dsimp [a]
    rw [Real.sin_add, Real.sin_add, Real.cos_add]
    rw [hturn.1, hturn.2, Real.sin_pi, Real.cos_pi,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
    norm_num
  have hsinb : Real.sin b = 1 := by
    change Real.sin (a + Real.pi) = 1
    rw [Real.sin_add, hsina, Real.sin_pi, Real.cos_pi]
    norm_num
  have hinva : 1 / (1 / a) = a := by
    field_simp [ne_of_gt hapos]
  have hinvb : 1 / (1 / b) = b := by
    field_simp [ne_of_gt hbpos]
  have hfa : f (1 / a) = 2 - (1 / a) ^ 2 := by
    rw [f, if_neg hxa.ne', hinva, hsina]
    ring
  have hfb : f (1 / b) = 2 - 3 * (1 / b) ^ 2 := by
    rw [f, if_neg hxb.ne', hinvb, hsinb]
    ring
  have hba_sq : b ^ 2 < 3 * a ^ 2 := by
    dsimp [a, b]
    nlinarith [sq_nonneg t, sq_pos_of_pos Real.pi_pos,
      mul_nonneg (le_of_lt htpos') (le_of_lt Real.pi_pos)]
  have hdiv : 1 / a ^ 2 < 3 / b ^ 2 := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hapos) (sq_pos_of_pos hbpos)).2
    simpa using hba_sq
  have hisq : (1 / a) ^ 2 < 3 * (1 / b) ^ 2 := by
    calc
      (1 / a) ^ 2 = 1 / a ^ 2 := by ring
      _ < 3 / b ^ 2 := hdiv
      _ = 3 * (1 / b) ^ 2 := by ring
  have hba : 1 / b < 1 / a := by
    apply (div_lt_div_iff₀ hbpos hapos).2
    simpa using hab
  have hmb : 1 / b ∈ Set.Ioo 0 δ := ⟨hxb, hxbδ⟩
  have hma : 1 / a ∈ Set.Ioo 0 δ := ⟨hxa, hxaδ⟩
  have hord := hmon.2 hmb hma (le_of_lt hba)
  rw [hfa, hfb] at hord
  nlinarith

theorem gap9 :
    ∃ g : ℝ → ℝ,
      (∃ δ > 0, ∀ x ∈ Set.Ioo (-δ) δ, g x ≤ g 0) ∧
      ¬ (∃ δ > 0,
        MonotoneOn g (Set.Ioo (-δ) 0) ∧
        AntitoneOn g (Set.Ioo 0 δ)) := by
  refine ⟨f, ?_, ?_⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact gap4 (Set.mem_univ x)
  · rintro ⟨δ, hδ, hmon⟩
    exact gap8 δ hδ hmon

end
end ProofGap.Exercise1425
