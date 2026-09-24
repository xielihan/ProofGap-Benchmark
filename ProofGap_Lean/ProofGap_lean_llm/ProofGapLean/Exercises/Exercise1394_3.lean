import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1394_3

noncomputable section

def f (x : ℝ) : ℝ := Real.tan x
def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def taylorPolynomial (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m,
    iterDeriv k f 0 / (Nat.factorial k : ℝ) * x ^ k

def remainder (m : ℕ) (x : ℝ) : ℝ := f x - taylorPolynomial m x

def RemainderFormula (n : ℕ) (x : ℝ) : Prop :=
  ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
    remainder (n + 1) x =
      iterDeriv (n + 1) f (θ * x) / (Nat.factorial (n + 1) : ℝ) *
        x ^ (n + 1)

def fifthBound : ℝ :=
  16 / (0.9 : ℝ) + 120 * (0.1 : ℝ) ^ 2 / (0.9 : ℝ) ^ 3

private def d1 (x : ℝ) := 1 / Real.cos x ^ 2
private def d2 (x : ℝ) := 2 * Real.sin x / Real.cos x ^ 3
private def d3 (x : ℝ) := 6 / Real.cos x ^ 4 - 4 / Real.cos x ^ 2
private def d4 (x : ℝ) :=
  24 * Real.sin x / Real.cos x ^ 5 -
    8 * Real.sin x / Real.cos x ^ 3
private def d5 (x : ℝ) :=
  16 / Real.cos x ^ 2 +
    120 * Real.sin x ^ 2 / Real.cos x ^ 6
private def d6 (x : ℝ) :=
  32 * Real.sin x / Real.cos x ^ 3 +
    240 * Real.sin x / Real.cos x ^ 5 +
    720 * Real.sin x ^ 3 / Real.cos x ^ 7

private theorem iterDeriv_succ (n : ℕ) (g : ℝ → ℝ) :
    iterDeriv (n + 1) g = deriv (iterDeriv n g) := by
  rw [iterDeriv, iterDeriv, ← iteratedDeriv_eq_iterate,
    ← iteratedDeriv_eq_iterate, iteratedDeriv_succ]

private theorem iterDeriv_one_f :
    iterDeriv 1 f = d1 := by
  funext x
  change deriv Real.tan x = 1 / Real.cos x ^ 2
  exact Real.deriv_tan x

private theorem hasDerivAt_d1 (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt d1 (d2 x) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).div
    ((Real.hasDerivAt_cos x).pow 2) (pow_ne_zero 2 hc)
  dsimp [d1, d2] at *
  convert h using 1 <;> field_simp [hc] <;> ring

private theorem hasDerivAt_d2 (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt d2 (d3 x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul 2).div
    ((Real.hasDerivAt_cos x).pow 3) (pow_ne_zero 3 hc)
  dsimp [d2, d3] at *
  convert h using 1
  field_simp [hc]
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem hasDerivAt_d3 (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt d3 (d4 x) x := by
  have h4 := (hasDerivAt_const x (6 : ℝ)).div
    ((Real.hasDerivAt_cos x).pow 4) (pow_ne_zero 4 hc)
  have h2 := (hasDerivAt_const x (4 : ℝ)).div
    ((Real.hasDerivAt_cos x).pow 2) (pow_ne_zero 2 hc)
  have h := h4.sub h2
  dsimp [d3, d4] at *
  convert h using 1 <;> field_simp [hc] <;> ring

private theorem hasDerivAt_d4 (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt d4 (d5 x) x := by
  have h24 := ((Real.hasDerivAt_sin x).const_mul 24).div
    ((Real.hasDerivAt_cos x).pow 5) (pow_ne_zero 5 hc)
  have h8 := ((Real.hasDerivAt_sin x).const_mul 8).div
    ((Real.hasDerivAt_cos x).pow 3) (pow_ne_zero 3 hc)
  have h := h24.sub h8
  dsimp [d4, d5] at *
  convert h using 1
  field_simp [hc]
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem hasDerivAt_d5 (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt d5 (d6 x) x := by
  have h16 := (hasDerivAt_const x (16 : ℝ)).div
    ((Real.hasDerivAt_cos x).pow 2) (pow_ne_zero 2 hc)
  have h120 := (((Real.hasDerivAt_sin x).pow 2).const_mul 120).div
    ((Real.hasDerivAt_cos x).pow 6) (pow_ne_zero 6 hc)
  have h := h16.add h120
  dsimp [d5, d6] at *
  convert h using 1 <;> field_simp [hc] <;> ring

private theorem cos_eventually_ne {x : ℝ} (hc : Real.cos x ≠ 0) :
    ∀ᶠ y in nhds x, Real.cos y ≠ 0 :=
  Real.continuous_cos.continuousAt.eventually_ne hc

private theorem remainderFormula_pos (n : ℕ) {x : ℝ}
    (hx : 0 < x) (hxsmall : x ≤ (0.1 : ℝ)) :
    RemainderFormula n x := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hf : ContDiffOn ℝ (n + 1) f (Set.Icc 0 x) := by
    intro t ht
    have hc : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, ht.1],
          by linarith [ht.2, hxsmall]⟩
    exact
      ((Real.contDiffAt_tan (n := ((n + 1 : ℕ) : WithTop ℕ∞))).mpr
        hc.ne').contDiffWithinAt
  rcases taylor_mean_remainder_lagrange_iteratedDeriv hx hf with
    ⟨c, hc, hrem⟩
  have heval :
      taylorWithinEval f n (Set.Icc 0 x) 0 x =
        taylorPolynomial (n + 1) x := by
    rw [taylor_within_apply]
    dsimp [taylorPolynomial]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hx)
      (show ContDiffAt ℝ k f 0 by
        simpa only [f] using
          (Real.contDiffAt_tan (n := (k : WithTop ℕ∞))).mpr
            (by norm_num))
      ⟨le_rfl, hx.le⟩]
    rw [iteratedDeriv_eq_iterate]
    simp only [iterDeriv, smul_eq_mul]
    ring
  refine ⟨c / x, ⟨div_pos hc.1 hx, (div_lt_one hx).2 hc.2⟩, ?_⟩
  rw [heval] at hrem
  rw [remainder]
  rw [show c / x * x = c by field_simp]
  rw [iterDeriv, ← iteratedDeriv_eq_iterate]
  rw [hrem]
  ring

theorem gap1 (x : ℝ) (hx : |x| ≤ (0.1 : ℝ)) :
    ∀ n : ℕ, RemainderFormula n x := by
  intro n
  by_cases hx0 : x = 0
  · subst x
    have hpoly : taylorPolynomial (n + 1) 0 = 0 := by
      rw [taylorPolynomial]
      rw [Finset.sum_eq_single 0]
      · simp [iterDeriv, f]
      · intro k hk hk0
        simp [hk0]
      · simp
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [remainder, hpoly]
    simp [f]
  · by_cases hxpos : 0 < x
    · apply remainderFormula_pos n hxpos
      simpa [abs_of_pos hxpos] using hx
    · have hxneg : x < 0 := lt_of_le_of_ne
        (le_of_not_gt hxpos) hx0
      let y : ℝ := -x
      let g : ℝ → ℝ := fun t => f (-t)
      have hy : 0 < y := by
        dsimp [y]
        linarith
      have hysmall : y ≤ (0.1 : ℝ) := by
        dsimp [y]
        rw [← abs_of_neg hxneg]
        exact hx
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hfy : ContDiffOn ℝ (n + 1) f (Set.Icc 0 y) := by
        intro t ht
        have hc : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo
            ⟨by linarith [Real.pi_pos, ht.1],
              by linarith [ht.2, hysmall]⟩
        exact
          ((Real.contDiffAt_tan (n := ((n + 1 : ℕ) : WithTop ℕ∞))).mpr
            hc.ne').contDiffWithinAt
      have hgfun : g = -f := by
        funext t
        simp [g, f]
      have hg : ContDiffOn ℝ (n + 1) g (Set.Icc 0 y) := by
        rw [hgfun]
        exact hfy.neg
      rcases taylor_mean_remainder_lagrange_iteratedDeriv hy hg with
        ⟨c, hc, hrem⟩
      have heval :
          taylorWithinEval g n (Set.Icc 0 y) 0 y =
            taylorPolynomial (n + 1) x := by
        rw [taylor_within_apply]
        dsimp [taylorPolynomial]
        apply Finset.sum_congr rfl
        intro k hk
        rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc hy)
          (show ContDiffAt ℝ k g 0 by
            rw [hgfun]
            exact
              ((Real.contDiffAt_tan (n := (k : WithTop ℕ∞))).mpr
                (by norm_num)).neg)
          ⟨le_rfl, hy.le⟩]
        dsimp [g, y]
        rw [iteratedDeriv_comp_neg, iteratedDeriv_eq_iterate]
        simp only [iterDeriv, neg_zero, smul_eq_mul]
        rw [sub_zero, neg_pow]
        ring_nf
        rw [Even.neg_one_pow
          (show Even (k * 2) by exact ⟨k, by omega⟩)]
        ring
      rw [heval] at hrem
      rw [iteratedDeriv_comp_neg] at hrem
      dsimp [g, y] at hrem
      simp only [neg_neg, smul_eq_mul] at hrem
      refine ⟨c / y, ⟨div_pos hc.1 hy, (div_lt_one hy).2 hc.2⟩, ?_⟩
      rw [remainder]
      rw [show c / y * x = -c by
        dsimp [y]
        field_simp]
      rw [iterDeriv, ← iteratedDeriv_eq_iterate]
      rw [hrem]
      rw [sub_zero, neg_pow]
      ring_nf
      rw [Even.neg_one_pow
        (show Even (n * 2) by exact ⟨n, by omega⟩)]
      ring

theorem gap2 (x : ℝ) (hcos : Real.cos x ≠ 0) :
    iterDeriv 1 f x = 1 / Real.cos x ^ 2 := by
  rw [iterDeriv_one_f]
  rfl

theorem gap3 (x : ℝ) (hcos : Real.cos x ≠ 0) :
    iterDeriv 2 f x = 2 * Real.sin x / Real.cos x ^ 3 := by
  rw [iterDeriv_succ, iterDeriv_one_f]
  exact (hasDerivAt_d1 x hcos).deriv

theorem gap4 (x : ℝ) (hcos : Real.cos x ≠ 0) :
    iterDeriv 3 f x = 6 / Real.cos x ^ 4 - 4 / Real.cos x ^ 2 := by
  have heq : iterDeriv 2 f =ᶠ[nhds x] d2 :=
    (cos_eventually_ne hcos).mono fun y hy => gap3 y hy
  rw [iterDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_d2 x hcos).deriv

theorem gap5 (x : ℝ) (hcos : Real.cos x ≠ 0)
    (hsmooth : ContDiffAt ℝ 4 f x) :
    iterDeriv 4 f x =
      24 * Real.sin x / Real.cos x ^ 5 -
        8 * Real.sin x / Real.cos x ^ 3 := by
  have heq : iterDeriv 3 f =ᶠ[nhds x] d3 :=
    (cos_eventually_ne hcos).mono fun y hy => gap4 y hy
  rw [iterDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_d3 x hcos).deriv

theorem gap6 (x : ℝ) (hcos : Real.cos x ≠ 0)
    (hsmooth : ContDiffAt ℝ 5 f x) :
    iterDeriv 5 f x =
      16 / Real.cos x ^ 2 +
        120 * Real.sin x ^ 2 / Real.cos x ^ 6 := by
  have heq : iterDeriv 4 f =ᶠ[nhds x] d4 :=
    (cos_eventually_ne hcos).mono fun y hy =>
      gap5 y hy (by
        have htan : ContDiffAt ℝ 4 Real.tan y :=
          Real.contDiffAt_tan.mpr hy
        simpa only [f] using htan)
  rw [iterDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_d4 x hcos).deriv

theorem gap7 (x : ℝ) (hcos : Real.cos x ≠ 0)
    (hsmooth : ContDiffAt ℝ 6 f x) :
    iterDeriv 6 f x =
      32 * Real.sin x / Real.cos x ^ 3 +
        240 * Real.sin x / Real.cos x ^ 5 +
        720 * Real.sin x ^ 3 / Real.cos x ^ 7 := by
  have heq : iterDeriv 5 f =ᶠ[nhds x] d5 :=
    (cos_eventually_ne hcos).mono fun y hy =>
      gap6 y hy (by
        have htan : ContDiffAt ℝ 5 Real.tan y :=
          Real.contDiffAt_tan.mpr hy
        simpa only [f] using htan)
  rw [iterDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_d5 x hcos).deriv

theorem gap8 :
    Function.Even (iterDeriv 5 f) := by
  intro x
  have hfun : (fun t : ℝ => f (-t)) = fun t => -f t := by
    funext t
    simp [f]
  have h := congrArg
    (fun g : ℝ → ℝ => iteratedDeriv 5 g x) hfun
  change iteratedDeriv 5 (fun t => f (-t)) x =
    iteratedDeriv 5 (-f) x at h
  rw [iteratedDeriv_comp_neg, iteratedDeriv_neg] at h
  norm_num at h
  change (deriv^[5]) f (-x) = (deriv^[5]) f x
  simpa only [iteratedDeriv_eq_iterate] using h

theorem gap9 :
    ∀ x ∈ Set.Icc (0 : ℝ) 0.1, 0 ≤ iterDeriv 6 f x := by
  intro x hx
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcospos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hx.1], by linarith [hx.2]⟩
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2])
  have hs : ContDiffAt ℝ 6 f x := by
    simpa only [f] using
      (Real.contDiffAt_tan (n := (6 : WithTop ℕ∞))).mpr hcospos.ne'
  rw [gap7 x hcospos.ne' hs]
  positivity

theorem gap10 :
    ∃ z ∈ ({(-0.1 : ℝ), (0.1 : ℝ)} : Set ℝ),
      ∀ y ∈ Set.Icc (-0.1 : ℝ) 0.1, iterDeriv 5 f y ≤ iterDeriv 5 f z := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcos_pos : ∀ t ∈ Set.Icc (0 : ℝ) 0.1, 0 < Real.cos t := by
    intro t ht
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], by linarith [ht.2]⟩
  have hmono : MonotoneOn d5 (Set.Icc (0 : ℝ) 0.1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 0.1)
    · intro t ht
      exact
        (hasDerivAt_d5 t (hcos_pos t ht).ne').continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 0.1 := interior_subset ht
      exact
        (hasDerivAt_d5 t (hcos_pos t ht').ne').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 0.1 := interior_subset ht
      have hc : 0 < Real.cos t := hcos_pos t ht'
      rw [(hasDerivAt_d5 t hc.ne').deriv]
      have hsin : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 (by linarith [ht'.2])
      dsimp [d6]
      exact add_nonneg
        (add_nonneg
          (div_nonneg (mul_nonneg (by norm_num) hsin)
            (pow_nonneg hc.le 3))
          (div_nonneg (mul_nonneg (by norm_num) hsin)
            (pow_nonneg hc.le 5)))
        (div_nonneg
          (mul_nonneg (by norm_num) (pow_nonneg hsin 3))
          (pow_nonneg hc.le 7))
  refine ⟨0.1, by simp, ?_⟩
  intro y hy
  have hyabs : |y| ≤ (0.1 : ℝ) := abs_le.mpr hy
  have habs_mem : |y| ∈ Set.Icc (0 : ℝ) 0.1 :=
    ⟨abs_nonneg y, hyabs⟩
  have heven : iterDeriv 5 f y = iterDeriv 5 f |y| := by
    by_cases hy0 : 0 ≤ y
    · rw [abs_of_nonneg hy0]
    · rw [abs_of_neg (lt_of_not_ge hy0)]
      exact (gap8 y).symm
  have hvalue : ∀ t ∈ Set.Icc (0 : ℝ) 0.1, iterDeriv 5 f t = d5 t := by
    intro t ht
    have hc := hcos_pos t ht
    have hs : ContDiffAt ℝ 5 f t := by
      simpa only [f] using
        (Real.contDiffAt_tan (n := (5 : WithTop ℕ∞))).mpr hc.ne'
    exact gap6 t hc.ne' hs
  have hend : (0.1 : ℝ) ∈ Set.Icc (0 : ℝ) 0.1 := by norm_num
  rw [heven, hvalue |y| habs_mem, hvalue 0.1 hend]
  exact hmono habs_mem hend hyabs

theorem gap11 :
    iterDeriv 1 f 0 = 1 := by
  have h := gap2 0 (by norm_num)
  norm_num at h
  exact h

theorem gap12 :
    iterDeriv 2 f 0 = 0 := by
  have h := gap3 0 (by norm_num)
  norm_num at h
  exact h

theorem gap13 :
    iterDeriv 3 f 0 = 2 := by
  have h := gap4 0 (by norm_num)
  norm_num at h
  exact h

theorem gap14 :
    iterDeriv 4 f 0 = 0 := by
  have hs : ContDiffAt ℝ 4 f 0 := by
    simpa only [f] using
      (Real.contDiffAt_tan (n := (4 : WithTop ℕ∞))).mpr
        (by norm_num)
  have h := gap5 0 (by norm_num) hs
  norm_num at h
  exact h

theorem gap15 :
    Real.cos (0.1 : ℝ) ^ 2 = 1 - Real.sin (0.1 : ℝ) ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq (0.1 : ℝ)]

theorem gap16 :
    1 - Real.sin (0.1 : ℝ) ^ 2 > (0.9 : ℝ) := by
  have h : Real.sin (0.1 : ℝ) ^ 2 ≤ (0.1 : ℝ) ^ 2 :=
    Real.sin_sq_le_sq
  norm_num at h ⊢
  linarith

theorem gap17 :
    Real.cos (0.1 : ℝ) ^ 2 > (0.9 : ℝ) := by
  rw [gap15]
  exact gap16

theorem gap18 (x : ℝ) (hx : |x| ≤ (0.1 : ℝ)) :
    |iterDeriv 5 f x| ≤ fifthBound := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hxi : x ∈ Set.Icc (-0.1 : ℝ) 0.1 := abs_le.mp hx
  have hcosx : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hxi.1], by linarith [hxi.2]⟩
  have hsx : ContDiffAt ℝ 5 f x := by
    simpa only [f] using
      (Real.contDiffAt_tan (n := (5 : WithTop ℕ∞))).mpr hcosx.ne'
  have hnonneg : 0 ≤ iterDeriv 5 f x := by
    rw [gap6 x hcosx.ne' hsx]
    positivity
  rcases gap10 with ⟨z, hz, hmax⟩
  have hle : iterDeriv 5 f x ≤ iterDeriv 5 f 0.1 := by
    have h := hmax x hxi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · calc
        iterDeriv 5 f x ≤ iterDeriv 5 f (-0.1) := h
        _ = iterDeriv 5 f 0.1 := gap8 (0.1 : ℝ)
    · exact h
  have hc : 0 < Real.cos (0.1 : ℝ) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs : ContDiffAt ℝ 5 f 0.1 := by
    simpa only [f] using
      (Real.contDiffAt_tan (n := (5 : WithTop ℕ∞))).mpr hc.ne'
  have hsin2 : Real.sin (0.1 : ℝ) ^ 2 ≤ (0.1 : ℝ) ^ 2 :=
    Real.sin_sq_le_sq
  have hc6 : (0.9 : ℝ) ^ 3 < Real.cos (0.1 : ℝ) ^ 6 := by
    have hpow := pow_lt_pow_left₀ gap17 (by norm_num : (0 : ℝ) ≤ 0.9)
      (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith
  have hterm1 :
      16 / Real.cos (0.1 : ℝ) ^ 2 ≤ (16 : ℝ) / 0.9 := by
    exact div_le_div₀ (by norm_num) (by norm_num) (by norm_num) gap17.le
  have hterm2 :
      120 * Real.sin (0.1 : ℝ) ^ 2 / Real.cos (0.1 : ℝ) ^ 6 ≤
        120 * (0.1 : ℝ) ^ 2 / 0.9 ^ 3 := by
    apply div_le_div₀ (by positivity) ?_ (by norm_num) hc6.le
    gcongr
  rw [abs_of_nonneg hnonneg]
  calc
    iterDeriv 5 f x ≤ iterDeriv 5 f 0.1 := hle
    _ = d5 0.1 := gap6 0.1 hc.ne' hs
    _ ≤ fifthBound := by
      dsimp [d5, fifthBound]
      linarith

theorem gap19 :
    fifthBound < 20 := by
  norm_num [fifthBound]

theorem gap20 (x : ℝ) (hx : |x| ≤ (0.1 : ℝ)) :
    |iterDeriv 5 f x| < 20 := by
  exact lt_of_le_of_lt (gap18 x hx) gap19

theorem gap21 (x : ℝ) (hx : |x| ≤ (0.1 : ℝ))
    (hR : RemainderFormula 4 x) :
    |remainder 5 x| ≤ (0.1 : ℝ) ^ 5 / (Nat.factorial 5 : ℝ) * 20 := by
  rcases hR with ⟨θ, hθ, hrem⟩
  have hθ0 : 0 ≤ θ := hθ.1.le
  have hθ1 : θ ≤ 1 := hθ.2.le
  have htx : |θ * x| ≤ (0.1 : ℝ) := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact
      (mul_le_of_le_one_left (abs_nonneg x) hθ1).trans hx
  have hd : |iterDeriv 5 f (θ * x)| ≤ 20 :=
    (gap20 (θ * x) htx).le
  have hpow : |x| ^ 5 ≤ (0.1 : ℝ) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg x) hx 5
  rw [hrem, abs_mul, abs_div, abs_pow]
  have hfact : (0 : ℝ) < Nat.factorial 5 := by positivity
  calc
    |iterDeriv 5 f (θ * x)| / |(Nat.factorial 5 : ℝ)| * |x| ^ 5 ≤
        20 / |(Nat.factorial 5 : ℝ)| * (0.1 : ℝ) ^ 5 := by
      apply mul_le_mul
        (div_le_div_of_nonneg_right hd (abs_nonneg (Nat.factorial 5 : ℝ)))
        hpow (pow_nonneg (abs_nonneg x) 5)
      positivity
    _ = (0.1 : ℝ) ^ 5 / (Nat.factorial 5 : ℝ) * 20 := by
      norm_num [Nat.factorial]

theorem gap22 :
    (0.1 : ℝ) ^ 5 / (Nat.factorial 5 : ℝ) * 20 <
      (2 / 10 ^ 6 : ℝ) := by
  norm_num [Nat.factorial]

theorem gap23 (x : ℝ) (hx : |x| ≤ (0.1 : ℝ))
    (hR : RemainderFormula 4 x) :
    |remainder 5 x| < (2 / 10 ^ 6 : ℝ) := by
  exact lt_of_le_of_lt (gap21 x hx hR) gap22

end

end ProofGap.Exercise1394_3
