import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace ProofGap.Exercise1396_8

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε
def arcsinCoeff (k : ℕ) : ℝ :=
  (Nat.factorial (2 * k) : ℝ) /
    (4 ^ k * (Nat.factorial k : ℝ) ^ 2 * (2 * k + 1))
def arcsinPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, arcsinCoeff k * x ^ (2 * k + 1)
def remainder : ℝ := |Real.arcsin 0.45 - arcsinPartial 0.45 7|
def firstOmitted : ℝ := arcsinCoeff 7 * 0.45 ^ 15
def geometricBound : ℝ :=
  (1 / 15 : ℝ) * 0.45 ^ 15 / (1 - 0.45 ^ 2)

private theorem one_div_lt_of_one_lt_mul {d b : ℝ}
    (hd : 0 < d) (h : 1 < d * b) :
    1 / d < b := by
  apply (div_lt_iff₀ hd).2
  simpa [mul_comm] using h

private theorem div_le_div_same_num {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcb : c ≤ b) :
    a / b ≤ a / c :=
  (div_le_div_iff_of_pos_left ha hb hc).2 hcb

private theorem invSqrt_sub_lt_geometric {u a : ℝ}
    (hu : 0 < u) (hden : 0 < 1 - u) (ha : 0 < a)
    (hid :
      ((1 - u) *
          (a + (231 / 1024 : ℝ) * u ^ 7 / (1 - u)) ^ 2 - 1) *
          (1 - u) =
        u ^ 7 *
          (441 * u ^ 5 + 1176 * u ^ 4 + 2464 * u ^ 3 +
            4928 * u ^ 2 + 10560 * u + 33792) / 1048576) :
    1 / Real.sqrt (1 - u) - a <
      (231 / 1024 : ℝ) * u ^ 7 / (1 - u) := by
  let c : ℝ := (231 / 1024 : ℝ) * u ^ 7 / (1 - u)
  let d : ℝ := Real.sqrt (1 - u)
  let b : ℝ := a + c
  have hdpos : 0 < d := Real.sqrt_pos.2 hden
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hbpos : 0 < b := by
    dsimp [b]
    linarith
  have hright : 0 <
      u ^ 7 *
        (441 * u ^ 5 + 1176 * u ^ 4 + 2464 * u ^ 3 +
          4928 * u ^ 2 + 10560 * u + 33792) / 1048576 := by
    positivity
  have hleftprod : 0 < ((1 - u) * b ^ 2 - 1) * (1 - u) := by
    rw [show ((1 - u) * b ^ 2 - 1) * (1 - u) =
        u ^ 7 *
          (441 * u ^ 5 + 1176 * u ^ 4 + 2464 * u ^ 3 +
            4928 * u ^ 2 + 10560 * u + 33792) / 1048576 by
      simpa [b, c] using hid]
    exact hright
  have hleft : 0 < (1 - u) * b ^ 2 - 1 := by
    rcases mul_pos_iff.mp hleftprod with h | h
    · exact h.1
    · linarith [h.2, hden]
  have hdsq : d ^ 2 = 1 - u := Real.sq_sqrt hden.le
  have hprodsq : 1 < (d * b) ^ 2 := by
    rw [mul_pow, hdsq]
    linarith
  have hprod : 1 < d * b := by
    have hdbpos : 0 < d * b := mul_pos hdpos hbpos
    nlinarith [sq_nonneg (d * b + 1)]
  have hdiv : 1 / d < b :=
    one_div_lt_of_one_lt_mul hdpos hprod
  dsimp [b] at hdiv
  have : 1 / d - a < c := by
    apply sub_lt_iff_lt_add.mpr
    simpa [add_comm] using hdiv
  simpa [c, d] using this

private theorem arcsin_point_estimate :
    0 ≤ Real.arcsin 0.45 - arcsinPartial 0.45 7 ∧
      Real.arcsin 0.45 - arcsinPartial 0.45 7 <
        (231 / (1024 * 15) : ℝ) * 0.45 ^ 15 /
          (1 - 0.45 ^ 2) := by
  let x : ℝ := 9 / 20
  let p : ℝ → ℝ := fun t =>
    t + (1 / 6 : ℝ) * t ^ 3 + (3 / 40 : ℝ) * t ^ 5 +
      (5 / 112 : ℝ) * t ^ 7 + (35 / 1152 : ℝ) * t ^ 9 +
      (63 / 2816 : ℝ) * t ^ 11 + (231 / 13312 : ℝ) * t ^ 13
  let s : ℝ → ℝ := fun t =>
    1 + (1 / 2 : ℝ) * t ^ 2 + (3 / 8 : ℝ) * t ^ 4 +
      (5 / 16 : ℝ) * t ^ 6 + (35 / 128 : ℝ) * t ^ 8 +
      (63 / 256 : ℝ) * t ^ 10 + (231 / 1024 : ℝ) * t ^ 12
  let e : ℝ → ℝ := fun t => Real.arcsin t - p t
  let g : ℝ → ℝ := fun t =>
    (231 / 1024 : ℝ) * t ^ 15 / (15 * (1 - x ^ 2))
  have hpartial (t : ℝ) : arcsinPartial t 7 = p t := by
    norm_num [arcsinPartial, arcsinCoeff, Finset.sum_range_succ, p]
  have hp (t : ℝ) : HasDerivAt p (s t) t := by
    dsimp [p, s]
    convert ((((((hasDerivAt_id t).add
      (((hasDerivAt_id t).pow 3).const_mul (1 / 6 : ℝ))).add
      (((hasDerivAt_id t).pow 5).const_mul (3 / 40 : ℝ))).add
      (((hasDerivAt_id t).pow 7).const_mul (5 / 112 : ℝ))).add
      (((hasDerivAt_id t).pow 9).const_mul (35 / 1152 : ℝ))).add
      (((hasDerivAt_id t).pow 11).const_mul (63 / 2816 : ℝ))).add
      (((hasDerivAt_id t).pow 13).const_mul (231 / 13312 : ℝ))
      using 1 <;> simp only [id_eq] <;> ring
  have he (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) x) :
      HasDerivAt e (1 / Real.sqrt (1 - t ^ 2) - s t) t := by
    have htneg : t ≠ -1 := by
      intro h
      linarith [ht.1]
    have htpos : t ≠ 1 := by
      intro h
      subst t
      norm_num [x] at ht
    exact (Real.hasDerivAt_arcsin htneg htpos).sub (hp t)
  have hlower (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) x) :
      0 ≤ 1 / Real.sqrt (1 - t ^ 2) - s t := by
    let u : ℝ := t ^ 2
    let a : ℝ := s t
    let d : ℝ := Real.sqrt (1 - u)
    have hu : 0 ≤ u := by positivity
    have hut : u ≤ x ^ 2 := by
      dsimp [u]
      have hxpos : 0 < x := by
        change 0 < (9 / 20 : ℝ)
        norm_num
      have hxnonneg : 0 ≤ x := hxpos.le
      have hsum : 0 ≤ x + t := add_nonneg hxnonneg ht.1
      have hprod := mul_nonneg (sub_nonneg.mpr ht.2) hsum
      nlinarith
    have hden : 0 < 1 - u := by
      norm_num [x] at hut
      linarith
    have hdpos : 0 < d := Real.sqrt_pos.2 hden
    have hapos : 0 < a := by
      dsimp [a, s]
      positivity
    have hid :
        1 - (1 - u) * a ^ 2 =
          u ^ 7 *
            (53361 * u ^ 6 + 63063 * u ^ 5 + 76440 * u ^ 4 +
              96096 * u ^ 3 + 128128 * u ^ 2 + 192192 * u +
              439296) / 1048576 := by
      dsimp [u, a, s]
      ring
    have hpoly : 0 ≤
        53361 * u ^ 6 + 63063 * u ^ 5 + 76440 * u ^ 4 +
          96096 * u ^ 3 + 128128 * u ^ 2 + 192192 * u +
          439296 := by positivity
    have hasq : (1 - u) * a ^ 2 ≤ 1 := by
      have : 0 ≤
          u ^ 7 *
            (53361 * u ^ 6 + 63063 * u ^ 5 + 76440 * u ^ 4 +
              96096 * u ^ 3 + 128128 * u ^ 2 + 192192 * u +
              439296) / 1048576 := by positivity
      linarith
    have hdsq : d ^ 2 = 1 - u := Real.sq_sqrt hden.le
    have hprodsq : (d * a) ^ 2 ≤ 1 := by
      rw [mul_pow, hdsq]
      exact hasq
    have hprod : d * a ≤ 1 := by
      have hdapos : 0 ≤ d * a := (mul_pos hdpos hapos).le
      nlinarith [sq_nonneg (d * a + 1)]
    have ha : a ≤ 1 / d := by
      apply (le_div_iff₀ hdpos).2
      simpa [mul_comm] using hprod
    simpa [u, a, d] using sub_nonneg.mpr ha
  have hupper (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) x) :
      1 / Real.sqrt (1 - t ^ 2) - s t <
        (231 / 1024 : ℝ) * t ^ 14 / (1 - x ^ 2) := by
    let u : ℝ := t ^ 2
    let a : ℝ := s t
    have hu : 0 < u := by
      dsimp [u]
      exact pow_pos ht.1 2
    have hut : u ≤ x ^ 2 := by
      dsimp [u]
      have hxpos : 0 < x := by
        change 0 < (9 / 20 : ℝ)
        norm_num
      have hsum : 0 ≤ x + t := add_nonneg hxpos.le ht.1.le
      have hprod := mul_nonneg (sub_nonneg.mpr ht.2.le) hsum
      nlinarith
    have hden : 0 < 1 - u := by
      norm_num [x] at hut
      linarith
    have hxden : 0 < 1 - x ^ 2 := by norm_num [x]
    have hapos : 0 < a := by
      dsimp [a, s]
      positivity
    have hid :
        ((1 - u) *
            (a + (231 / 1024 : ℝ) * u ^ 7 / (1 - u)) ^ 2 - 1) *
            (1 - u) =
          u ^ 7 *
            (441 * u ^ 5 + 1176 * u ^ 4 + 2464 * u ^ 3 +
              4928 * u ^ 2 + 10560 * u + 33792) / 1048576 := by
      dsimp [a, s]
      field_simp [ne_of_gt hden]
      ring
    have hraw : 1 / Real.sqrt (1 - u) - a <
        (231 / 1024 : ℝ) * u ^ 7 / (1 - u) := by
      exact invSqrt_sub_lt_geometric hu hden hapos hid
    have hdenord : 1 - x ^ 2 ≤ 1 - u := by linarith
    have hfrac :
        (231 / 1024 : ℝ) * u ^ 7 / (1 - u) ≤
          (231 / 1024 : ℝ) * u ^ 7 / (1 - x ^ 2) := by
      exact div_le_div_same_num
        (mul_pos (by norm_num) (pow_pos hu 7)) hden hxden hdenord
    calc
      1 / Real.sqrt (1 - t ^ 2) - s t =
          1 / Real.sqrt (1 - u) - a := by rfl
      _ < (231 / 1024 : ℝ) * u ^ 7 / (1 - u) := hraw
      _ ≤ (231 / 1024 : ℝ) * u ^ 7 / (1 - x ^ 2) := hfrac
      _ = (231 / 1024 : ℝ) * t ^ 14 / (1 - x ^ 2) := by
        dsimp [u]
        ring
  have hg (t : ℝ) :
      HasDerivAt g ((231 / 1024 : ℝ) * t ^ 14 / (1 - x ^ 2)) t := by
    dsimp [g]
    convert ((((hasDerivAt_id t).pow 15).const_mul
      (231 / 1024 : ℝ)).div_const (15 * (1 - x ^ 2))) using 1 <;>
      simp only [id_eq] <;> field_simp <;> ring
  have hezero : e 0 = 0 := by
    norm_num [e, p]
  have hqzero : g 0 - e 0 = 0 := by
    norm_num [g, hezero]
  have hcontE : ContinuousOn e (Set.Icc (0 : ℝ) x) := by
    intro t ht
    exact (he t ht).continuousAt.continuousWithinAt
  have hmonoE : MonotoneOn e (Set.Icc (0 : ℝ) x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
      hcontE
    · intro t ht
      rw [interior_Icc] at ht
      exact (he t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hlower t ⟨ht.1.le, ht.2.le⟩
  have he_nonneg : 0 ≤ e x := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := by norm_num [x]
    have hx : x ∈ Set.Icc (0 : ℝ) x := by norm_num [x]
    have h0x : (0 : ℝ) ≤ x := by norm_num [x]
    have := hmonoE h0 hx h0x
    simpa [hezero] using this
  have hcontQ : ContinuousOn (fun t => g t - e t) (Set.Icc (0 : ℝ) x) := by
    intro t ht
    exact ((hg t).sub (he t ht)).continuousAt.continuousWithinAt
  have hstrictQ :
      StrictMonoOn (fun t => g t - e t) (Set.Icc (0 : ℝ) x) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) x)
      hcontQ
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hg t).sub (he t ⟨ht.1.le, ht.2.le⟩)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact sub_pos.mpr (hupper t ht)
  have hqpos : 0 < g x - e x := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := by norm_num [x]
    have hx : x ∈ Set.Icc (0 : ℝ) x := by norm_num [x]
    have h0x : (0 : ℝ) < x := by norm_num [x]
    have := hstrictQ h0 hx h0x
    simpa [hqzero] using this
  have he_upper : e x < g x := by linarith
  have he_nonneg' :
      0 ≤ Real.arcsin x - arcsinPartial x 7 := by
    simpa [e, hpartial x] using he_nonneg
  have he_upper' :
      Real.arcsin x - arcsinPartial x 7 <
        (231 / (1024 * 15) : ℝ) * x ^ 15 /
          (1 - x ^ 2) := by
    simp only [e, g] at he_upper
    rw [hpartial x]
    convert he_upper using 1 <;> ring
  norm_num [x] at he_nonneg' he_upper' ⊢
  exact ⟨he_nonneg', he_upper'⟩

theorem gap1 :
    Approx (Real.arcsin 0.45) (arcsinPartial 0.45 7)
      (2 / 10000000 : ℝ) := by
  rcases arcsin_point_estimate with ⟨hzero, hupper⟩
  unfold Approx
  rw [abs_of_nonneg hzero]
  exact hupper.trans (by norm_num)
theorem gap2 :
    Approx (Real.arcsin 0.45) 0.46676 (6 / 1000000 : ℝ) := by
  have htail := gap1
  unfold Approx at htail ⊢
  have hpartial :
      |arcsinPartial 0.45 7 - 0.46676| < (58 / 10000000 : ℝ) := by
    norm_num [arcsinPartial, arcsinCoeff, Finset.sum_range_succ]
  have htriangle :
      |Real.arcsin 0.45 - 0.46676| ≤
        |Real.arcsin 0.45 - arcsinPartial 0.45 7| +
          |arcsinPartial 0.45 7 - 0.46676| :=
    abs_sub_le _ _ _
  linarith
theorem gap3 : ∃ Δ : ℝ, Δ = remainder ∧ 0 ≤ Δ := by
  exact ⟨remainder, rfl, abs_nonneg _⟩
theorem gap4 : remainder < geometricBound := by
  rcases arcsin_point_estimate with ⟨hzero, hupper⟩
  unfold remainder geometricBound
  rw [abs_of_nonneg hzero]
  exact hupper.trans (by norm_num)
theorem gap5 : firstOmitted < geometricBound := by
  norm_num [firstOmitted, geometricBound, arcsinCoeff]
theorem gap6 :
    Approx geometricBound (5.26 * 10 ^ (-7 : ℤ))
      (1 / 1000000000 : ℝ) := by
  norm_num [Approx, geometricBound, abs_lt]

end
end ProofGap.Exercise1396_8
