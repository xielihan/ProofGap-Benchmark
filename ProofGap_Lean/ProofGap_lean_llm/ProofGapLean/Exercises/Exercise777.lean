import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise777

noncomputable section

def u (x y : ℝ) : ℝ := Real.arcsin x + Real.arcsin y
def w (x y : ℝ) : ℝ :=
  x * Real.sqrt (1 - y ^ 2) + y * Real.sqrt (1 - x ^ 2)
def v (x y : ℝ) : ℝ := Real.arcsin (w x y)
def ε (x y : ℝ) : ℤ :=
  if x * y ≤ 0 ∨ x ^ 2 + y ^ 2 ≤ 1 then 0 else if 0 < x then 1 else -1

private theorem arcsin_add_le_pi_div_two_iff_sq_add_le_one
    (x y : ℝ) (hx₀ : 0 ≤ x) (hy₀ : 0 ≤ y)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    u x y ≤ Real.pi / 2 ↔ x ^ 2 + y ^ 2 ≤ 1 := by
  rcases abs_le.mp hx with ⟨hx₁, hx₂⟩
  rcases abs_le.mp hy with ⟨hy₁, hy₂⟩
  have hrad : 0 ≤ 1 - y ^ 2 := by nlinarith
  have hsqrt : 0 ≤ Real.sqrt (1 - y ^ 2) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
    Real.sq_sqrt hrad
  have hax_mem : Real.arcsin x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact Real.neg_pi_div_two_le_arcsin x
    · exact Real.arcsin_le_pi_div_two x
  have hac_mem : Real.arccos y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.arccos_nonneg y, Real.pi_pos]
    · rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      nlinarith [Real.arcsin_nonneg.mpr hy₀]
  have hsin_arcsin : Real.sin (Real.arcsin x) = x :=
    Real.sin_arcsin hx₁ hx₂
  have hsin_arccos : Real.sin (Real.arccos y) = Real.sqrt (1 - y ^ 2) :=
    Real.sin_arccos y
  constructor
  · intro hu
    have harc : Real.arcsin x ≤ Real.arccos y := by
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      unfold u at hu
      linarith
    have hmono := Real.strictMonoOn_sin.monotoneOn hax_mem hac_mem harc
    have hs : x ≤ Real.sqrt (1 - y ^ 2) := by
      calc
        x = Real.sin (Real.arcsin x) := hsin_arcsin.symm
        _ ≤ Real.sin (Real.arccos y) := hmono
        _ = Real.sqrt (1 - y ^ 2) := hsin_arccos
    have hprod : 0 ≤
        (Real.sqrt (1 - y ^ 2) - x) * (Real.sqrt (1 - y ^ 2) + x) :=
      mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hsqrt hx₀)
    nlinarith
  · intro hs
    have hxs : x ≤ Real.sqrt (1 - y ^ 2) := by
      by_contra hnot
      have hlt : Real.sqrt (1 - y ^ 2) < x := lt_of_not_ge hnot
      have hsum : 0 < x + Real.sqrt (1 - y ^ 2) := by linarith
      have hprod : 0 <
          (x - Real.sqrt (1 - y ^ 2)) * (x + Real.sqrt (1 - y ^ 2)) :=
        mul_pos (sub_pos.mpr hlt) hsum
      nlinarith
    have harc : Real.arcsin x ≤ Real.arccos y := by
      by_contra hnot
      have hlt : Real.arccos y < Real.arcsin x := lt_of_not_ge hnot
      have hmono := Real.strictMonoOn_sin hac_mem hax_mem hlt
      have hslt : Real.sqrt (1 - y ^ 2) < x := by
        calc
          Real.sqrt (1 - y ^ 2) = Real.sin (Real.arccos y) := hsin_arccos.symm
          _ < Real.sin (Real.arcsin x) := hmono
          _ = x := hsin_arcsin
      exact (not_lt_of_ge hxs) hslt
    rw [Real.arccos_eq_pi_div_two_sub_arcsin] at harc
    unfold u
    linarith

theorem gap1 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    Real.sin (u x y) = w x y := by
  rcases abs_le.mp hx with ⟨hx₁, hx₂⟩
  rcases abs_le.mp hy with ⟨hy₁, hy₂⟩
  unfold u w
  rw [Real.sin_add, Real.sin_arcsin hx₁ hx₂, Real.sin_arcsin hy₁ hy₂,
    Real.cos_arcsin, Real.cos_arcsin]
  ring
theorem gap2 (x y : ℝ) : -Real.pi / 2 ≤ v x y := by
  unfold v
  simpa only [neg_div] using Real.neg_pi_div_two_le_arcsin (w x y)
theorem gap3 (x y : ℝ) : v x y ≤ Real.pi / 2 := by
  unfold v
  exact Real.arcsin_le_pi_div_two (w x y)
theorem gap4 : -Real.pi / 2 ≤ Real.pi / 2 := by
  nlinarith [Real.pi_pos]
theorem gap5 (x y : ℝ) (hxy : x * y ≤ 0) :
    -Real.pi / 2 ≤ Real.arcsin x + Real.arcsin y := by
  by_cases hx₀ : 0 ≤ x
  · have hax : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx₀
    nlinarith [Real.neg_pi_div_two_le_arcsin y]
  · have hxneg : x < 0 := lt_of_not_ge hx₀
    have hy₀ : 0 ≤ y := by
      by_contra hny
      have hyneg : y < 0 := lt_of_not_ge hny
      exact (not_lt_of_ge hxy) (mul_pos_of_neg_of_neg hxneg hyneg)
    have hay : 0 ≤ Real.arcsin y := Real.arcsin_nonneg.mpr hy₀
    nlinarith [Real.neg_pi_div_two_le_arcsin x]
theorem gap6 (x y : ℝ) (hxy : x * y ≤ 0) :
    Real.arcsin x + Real.arcsin y ≤ Real.pi / 2 := by
  by_cases hx₀ : x ≤ 0
  · have hax : Real.arcsin x ≤ 0 := Real.arcsin_nonpos.mpr hx₀
    nlinarith [Real.arcsin_le_pi_div_two y]
  · have hxpos : 0 < x := lt_of_not_ge hx₀
    have hy₀ : y ≤ 0 := by
      by_contra hny
      have hypos : 0 < y := lt_of_not_ge hny
      exact (not_lt_of_ge hxy) (mul_pos hxpos hypos)
    have hay : Real.arcsin y ≤ 0 := Real.arcsin_nonpos.mpr hy₀
    nlinarith [Real.arcsin_le_pi_div_two x]
theorem gap7 (x y : ℝ) (hxy : x * y ≤ 0) :
    -Real.pi / 2 ≤ Real.pi / 2 := by
  exact gap4
theorem gap8 (x y : ℝ) (hxy : x * y ≤ 0) : -Real.pi / 2 ≤ u x y := by
  simpa [u] using gap5 x y hxy
theorem gap9 (x y : ℝ) (hxy : x * y ≤ 0) : u x y ≤ Real.pi / 2 := by
  simpa [u] using gap6 x y hxy
theorem gap10 (x y : ℝ) (hxy : x * y ≤ 0) :
    -Real.pi / 2 ≤ Real.pi / 2 := by
  exact gap4
theorem gap11 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 ≤ u x y := by
  have hax : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr (le_of_lt hx)
  have hay : 0 ≤ Real.arcsin y := Real.arcsin_nonneg.mpr (le_of_lt hy)
  simp only [u]
  linarith
theorem gap12 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    u x y ≤ Real.pi / 2 ↔ Real.arcsin x ≤ Real.pi / 2 - Real.arcsin y := by
  simp only [u]
  constructor <;> intro h <;> linarith

/-- Source gap 13 needs the preceding upper-bound premise. -/
theorem gap13 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hu : u x y ≤ Real.pi / 2) :
    Real.arcsin x ≤ Real.arccos y := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  simpa [u] using (gap12 x y hx hy).mp hu

/-- Source gap 14 needs the comparison obtained in gap 13. -/
theorem gap14 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hx₀ : 0 ≤ x) (hy₀ : 0 ≤ y)
    (h : Real.arcsin x ≤ Real.arccos y) :
    x ≤ Real.sqrt (1 - y ^ 2) := by
  rcases abs_le.mp hx with ⟨hx₁, hx₂⟩
  rcases abs_le.mp hy with ⟨hy₁, hy₂⟩
  have hax_mem : Real.arcsin x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin x, Real.arcsin_le_pi_div_two x⟩
  have hac_mem : Real.arccos y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.arccos_nonneg y, Real.pi_pos]
    · rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      nlinarith [Real.arcsin_nonneg.mpr hy₀]
  have hmono := Real.strictMonoOn_sin.monotoneOn hax_mem hac_mem h
  calc
    x = Real.sin (Real.arcsin x) := (Real.sin_arcsin hx₁ hx₂).symm
    _ ≤ Real.sin (Real.arccos y) := hmono
    _ = Real.sqrt (1 - y ^ 2) := Real.sin_arccos y

/-- Source gap 15 needs the inequality obtained in gap 14. -/
theorem gap15 (x y : ℝ) (hx₀ : 0 ≤ x) (hy : |y| ≤ 1)
    (h : x ≤ Real.sqrt (1 - y ^ 2)) :
    x ^ 2 + y ^ 2 ≤ 1 := by
  rcases abs_le.mp hy with ⟨hy₁, hy₂⟩
  have hrad : 0 ≤ 1 - y ^ 2 := by nlinarith
  have hsqrt : 0 ≤ Real.sqrt (1 - y ^ 2) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
    Real.sq_sqrt hrad
  have hprod : 0 ≤
      (Real.sqrt (1 - y ^ 2) - x) * (Real.sqrt (1 - y ^ 2) + x) :=
    mul_nonneg (sub_nonneg.mpr h) (add_nonneg hsqrt hx₀)
  nlinarith

theorem gap16 (x y : ℝ) (hx : x < 0) (hy : y < 0) : u x y ≤ 0 := by
  have hax : Real.arcsin x ≤ 0 := Real.arcsin_nonpos.mpr (le_of_lt hx)
  have hay : Real.arcsin y ≤ 0 := Real.arcsin_nonpos.mpr (le_of_lt hy)
  simp only [u]
  linarith
theorem gap17 (x y : ℝ) (hx : x < 0) (hy : y < 0)
    (hxb : |x| ≤ 1) (hyb : |y| ≤ 1) :
    -Real.pi / 2 ≤ u x y ↔ x ^ 2 + y ^ 2 ≤ 1 := by
  have hnx : 0 ≤ -x := by linarith
  have hny : 0 ≤ -y := by linarith
  have hnxb : |-x| ≤ 1 := by simpa only [abs_neg] using hxb
  have hnyb : |-y| ≤ 1 := by simpa only [abs_neg] using hyb
  have hi := arcsin_add_le_pi_div_two_iff_sq_add_le_one
    (-x) (-y) hnx hny hnxb hnyb
  have hu_neg : u (-x) (-y) = -u x y := by
    simp only [u, Real.arcsin_neg]
    ring
  constructor
  · intro hlo
    have hu : u (-x) (-y) ≤ Real.pi / 2 := by linarith
    have hs := hi.mp hu
    simpa only [neg_sq] using hs
  · intro hs
    have hs' : (-x) ^ 2 + (-y) ^ 2 ≤ 1 := by
      simpa only [neg_sq] using hs
    have hu := hi.mpr hs'
    linarith
theorem gap18 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (h : x * y ≤ 0 ∨ (0 < x * y ∧ x ^ 2 + y ^ 2 ≤ 1)) :
    -Real.pi / 2 ≤ u x y ∧ u x y ≤ Real.pi / 2 := by
  rcases h with hxy | hsame
  · exact ⟨gap8 x y hxy, gap9 x y hxy⟩
  · rcases hsame with ⟨hxy, hs⟩
    rcases mul_pos_iff.mp hxy with hp | hn
    · have hu := (arcsin_add_le_pi_div_two_iff_sq_add_le_one
        x y (le_of_lt hp.1) (le_of_lt hp.2) hx hy).mpr hs
      constructor
      · nlinarith [gap11 x y hp.1 hp.2, Real.pi_pos]
      · exact hu
    · have hlo := (gap17 x y hn.1 hn.2 hx hy).mpr hs
      have hzero := gap16 x y hn.1 hn.2
      constructor
      · exact hlo
      · nlinarith [Real.pi_pos]
theorem gap19 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 < x ^ 2 + y ^ 2) : Real.pi / 2 < u x y := by
  by_cases hx₁ : x ≤ 1
  · by_cases hy₁ : y ≤ 1
    · have hxb : |x| ≤ 1 := abs_le.mpr ⟨by linarith, hx₁⟩
      have hyb : |y| ≤ 1 := abs_le.mpr ⟨by linarith, hy₁⟩
      by_contra hnot
      have hu : u x y ≤ Real.pi / 2 := le_of_not_gt hnot
      have hs := (arcsin_add_le_pi_div_two_iff_sq_add_le_one
        x y (le_of_lt hx) (le_of_lt hy) hxb hyb).mp hu
      linarith
    · have hay : Real.arcsin y = Real.pi / 2 :=
        (Real.arcsin_eq_pi_div_two).2 (le_of_lt (lt_of_not_ge hy₁))
      have hax : 0 < Real.arcsin x := Real.arcsin_pos.mpr hx
      simp only [u, hay]
      linarith
  · have hax : Real.arcsin x = Real.pi / 2 :=
      (Real.arcsin_eq_pi_div_two).2 (le_of_lt (lt_of_not_ge hx₁))
    have hay : 0 < Real.arcsin y := Real.arcsin_pos.mpr hy
    simp only [u, hax]
    linarith
theorem gap20 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hxp : 0 < x) (hyp : 0 < y) (h : 1 < x ^ 2 + y ^ 2) :
    u x y ≤ Real.pi := by
  have hax := Real.arcsin_le_pi_div_two x
  have hay := Real.arcsin_le_pi_div_two y
  simp only [u]
  linarith
theorem gap21 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 < x ^ 2 + y ^ 2) : Real.pi / 2 < Real.pi := by
  nlinarith [Real.pi_pos]
theorem gap22 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hxn : x < 0) (hyn : y < 0) (h : 1 < x ^ 2 + y ^ 2) :
    -Real.pi ≤ u x y := by
  have hax := Real.neg_pi_div_two_le_arcsin x
  have hay := Real.neg_pi_div_two_le_arcsin y
  simp only [u]
  linarith
theorem gap23 (x y : ℝ) (hx : x < 0) (hy : y < 0)
    (h : 1 < x ^ 2 + y ^ 2) : u x y < -Real.pi / 2 := by
  have hp := gap19 (-x) (-y) (by linarith) (by linarith)
    (by simpa only [neg_sq] using h)
  have hu_neg : u (-x) (-y) = -u x y := by
    simp only [u, Real.arcsin_neg]
    ring
  linarith
theorem gap24 (x y : ℝ) (hx : x < 0) (hy : y < 0)
    (h : 1 < x ^ 2 + y ^ 2) : -Real.pi < -Real.pi / 2 := by
  nlinarith [Real.pi_pos]
theorem gap25 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (h₁ : -Real.pi / 2 ≤ u x y) (h₂ : u x y ≤ Real.pi / 2) :
    u x y = v x y := by
  have hlo : -(Real.pi / 2) ≤ u x y := by simpa only [neg_div] using h₁
  unfold v
  rw [← gap1 x y hx hy]
  exact (Real.arcsin_sin hlo h₂).symm
theorem gap26 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (h₁ : Real.pi / 2 < u x y) (h₂ : u x y ≤ Real.pi) :
    u x y = Real.pi - v x y := by
  have htlo : -(Real.pi / 2) ≤ Real.pi - u x y := by
    nlinarith [Real.pi_pos]
  have hthi : Real.pi - u x y ≤ Real.pi / 2 := by linarith
  have hv : v x y = Real.pi - u x y := by
    unfold v
    rw [← gap1 x y hx hy, ← Real.sin_pi_sub (u x y)]
    exact Real.arcsin_sin htlo hthi
  linarith
theorem gap27 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (h₁ : -Real.pi ≤ u x y) (h₂ : u x y < -Real.pi / 2) :
    u x y = -Real.pi - v x y := by
  have htlo : -(Real.pi / 2) ≤ -Real.pi - u x y := by linarith
  have hthi : -Real.pi - u x y ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (-Real.pi - u x y) = Real.sin (u x y) := by
    rw [show -Real.pi - u x y = -(Real.pi + u x y) by ring]
    simp [Real.sin_add]
  have hv : v x y = -Real.pi - u x y := by
    unfold v
    rw [← gap1 x y hx hy, ← hsin]
    exact Real.arcsin_sin htlo hthi
  linarith

theorem gap28 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    u x y =
      if x * y ≤ 0 ∨ x ^ 2 + y ^ 2 ≤ 1 then v x y
      else if 0 < x ∧ 0 < y then Real.pi - v x y
      else -Real.pi - v x y := by
  by_cases hm : x * y ≤ 0 ∨ x ^ 2 + y ^ 2 ≤ 1
  · rw [if_pos hm]
    have hmain : x * y ≤ 0 ∨ (0 < x * y ∧ x ^ 2 + y ^ 2 ≤ 1) := by
      rcases hm with hxy | hs
      · exact Or.inl hxy
      · by_cases hxy : x * y ≤ 0
        · exact Or.inl hxy
        · exact Or.inr ⟨lt_of_not_ge hxy, hs⟩
    have hb := gap18 x y hx hy hmain
    have hlo : -(Real.pi / 2) ≤ u x y := by
      simpa only [neg_div] using hb.1
    unfold v
    rw [← gap1 x y hx hy]
    exact (Real.arcsin_sin hlo hb.2).symm
  · rw [if_neg hm]
    have hparts := not_or.mp hm
    have hxy : 0 < x * y := lt_of_not_ge hparts.1
    have hs : 1 < x ^ 2 + y ^ 2 := lt_of_not_ge hparts.2
    rcases mul_pos_iff.mp hxy with hp | hn
    · rw [if_pos hp]
      have hlo := gap19 x y hp.1 hp.2 hs
      have hhi := gap20 x y hx hy hp.1 hp.2 hs
      have htlo : -(Real.pi / 2) ≤ Real.pi - u x y := by
        nlinarith [Real.pi_pos]
      have hthi : Real.pi - u x y ≤ Real.pi / 2 := by linarith
      have hv : v x y = Real.pi - u x y := by
        unfold v
        rw [← gap1 x y hx hy, ← Real.sin_pi_sub (u x y)]
        exact Real.arcsin_sin htlo hthi
      linarith
    · have hnp : ¬(0 < x ∧ 0 < y) := by
        intro hp
        exact (not_lt_of_ge (le_of_lt hn.1)) hp.1
      rw [if_neg hnp]
      have hlo := gap22 x y hx hy hn.1 hn.2 hs
      have hhi := gap23 x y hn.1 hn.2 hs
      have htlo : -(Real.pi / 2) ≤ -Real.pi - u x y := by linarith
      have hthi : -Real.pi - u x y ≤ Real.pi / 2 := by
        nlinarith [Real.pi_pos]
      have hsin : Real.sin (-Real.pi - u x y) = Real.sin (u x y) := by
        rw [show -Real.pi - u x y = -(Real.pi + u x y) by ring]
        simp [Real.sin_add]
      have hv : v x y = -Real.pi - u x y := by
        unfold v
        rw [← gap1 x y hx hy, ← hsin]
        exact Real.arcsin_sin htlo hthi
      linarith

theorem gap29 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    u x y = (-1 : ℝ) ^ ε x y * v x y + (ε x y : ℝ) * Real.pi := by
  rw [gap28 x y hx hy]
  by_cases hm : x * y ≤ 0 ∨ x ^ 2 + y ^ 2 ≤ 1
  · simp [ε, hm]
  · have hparts := not_or.mp hm
    have hxy : 0 < x * y := lt_of_not_ge hparts.1
    rcases mul_pos_iff.mp hxy with hp | hn
    · norm_num [ε, hm, hp] <;> ring
    · have hnp : ¬(0 < x ∧ 0 < y) := by
        intro hp
        exact (not_lt_of_ge (le_of_lt hn.1)) hp.1
      have hnx : ¬0 < x := not_lt.mpr (le_of_lt hn.1)
      norm_num [ε, hm, hnp, hnx] <;> ring

theorem gap30 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    Real.arcsin x + Real.arcsin y =
      (-1 : ℝ) ^ ε x y * Real.arcsin (w x y) + (ε x y : ℝ) * Real.pi := by
  simpa only [u, v] using gap29 x y hx hy

end

end ProofGap.Exercise777
