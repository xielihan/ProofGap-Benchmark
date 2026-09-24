import ProofGapLean.Prelude.Core
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise759

noncomputable section

def mobius (a b c d x : ℝ) : ℝ := (a * x + b) / (c * x + d)

private theorem inverse_comp_mobius (a b c d x : ℝ)
    (hdet : a * d - b * c ≠ 0) (hx : c * x + d ≠ 0) :
    mobius (-d) b c (-a) (mobius a b c d x) = x := by
  unfold mobius
  have hinv : c * ((a * x + b) / (c * x + d)) - a ≠ 0 := by
    intro hzero
    apply hdet
    field_simp [hx] at hzero
    nlinarith
  change (-d * ((a * x + b) / (c * x + d)) + b) /
      (c * ((a * x + b) / (c * x + d)) - a) = x
  apply (div_eq_iff hinv).2
  have hfrac : (c * x + d) * ((a * x + b) / (c * x + d)) = a * x + b :=
    mul_div_cancel₀ _ hx
  ring_nf at hfrac ⊢
  linarith

private theorem mobius_eq_inverse_iff (a b c d : ℝ)
    (hdet : a * d - b * c ≠ 0) :
    (∀ x, c * x + d ≠ 0 → c * x - a ≠ 0 →
        mobius a b c d x = mobius (-d) b c (-a) x) ↔
      a + d = 0 ∨ (b = 0 ∧ c = 0 ∧ a = d) := by
  constructor
  · intro h
    by_cases htrace : a + d = 0
    · exact Or.inl htrace
    · right
      let q : Polynomial ℝ :=
        Polynomial.C c * Polynomial.X ^ 2 +
          Polynomial.C (d - a) * Polynomial.X - Polynomial.C b
      have hvalid : Set.Infinite {x : ℝ | c * x + d ≠ 0 ∧ c * x - a ≠ 0} := by
        by_cases hc : c = 0
        · have ha : a ≠ 0 := by
            intro ha
            apply hdet
            simp [ha, hc]
          have hd : d ≠ 0 := by
            intro hd
            apply hdet
            simp [hd, hc]
          simpa [hc, ha, hd] using
            (Set.infinite_univ : Set.Infinite (Set.univ : Set ℝ))
        · have hpair : Set.Infinite (({-d / c, a / c} : Set ℝ)ᶜ) :=
            ((Set.finite_singleton (a / c)).insert (-d / c)).infinite_compl
          refine hpair.mono ?_
          intro x hx
          have hx₁ : x ≠ -d / c := by
            intro heq
            exact hx (by simp [heq])
          have hx₂ : x ≠ a / c := by
            intro heq
            exact hx (by simp [heq])
          constructor
          · intro hzero
            apply hx₁
            apply (eq_div_iff hc).2
            calc
              x * c = c * x := mul_comm _ _
              _ = -d := by linarith
          · intro hzero
            apply hx₂
            apply (eq_div_iff hc).2
            calc
              x * c = c * x := mul_comm _ _
              _ = a := by linarith
      have hroots : Set.Infinite {x : ℝ | Polynomial.IsRoot q x} := by
        refine hvalid.mono ?_
        intro x hx
        have heq : (a * x + b) / (c * x + d) =
            (-d * x + b) / (c * x - a) := by
          simpa only [mobius, sub_eq_add_neg] using h x hx.1 hx.2
        have hcross := (div_eq_div_iff hx.1 hx.2).mp heq
        have hfactor :
            (a + d) * (c * x ^ 2 + (d - a) * x - b) = 0 := by
          calc
            (a + d) * (c * x ^ 2 + (d - a) * x - b) =
                (a * x + b) * (c * x - a) -
                  (-d * x + b) * (c * x + d) := by ring
            _ = 0 := sub_eq_zero.mpr hcross
        have hqeval : c * x ^ 2 + (d - a) * x - b = 0 :=
          (mul_eq_zero.mp hfactor).resolve_left htrace
        simpa [q, Polynomial.IsRoot] using hqeval
      have hqzero : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q hroots
      have hc : c = 0 := by
        have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 2) hqzero
        simpa [q] using hcoeff
      have hda : d - a = 0 := by
        have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 1) hqzero
        simpa [q] using hcoeff
      have hb : b = 0 := by
        have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 0) hqzero
        simp [q] at hcoeff
        linarith
      exact ⟨hb, hc, by linarith⟩
  · rintro (htrace | ⟨hb, hc, had⟩) x hx₁ hx₂
    · have ha : -d = a := by linarith
      have hd : -a = d := by linarith
      simp [mobius, ha, hd]
    · subst d
      have ha : a ≠ 0 := by
        intro ha
        apply hdet
        simp [ha, hb, hc]
      simp [mobius, hb, hc, ha]

/-- Exercise 759, gap 1; bind `y` as the value `f x`. -/
theorem gap1 (a b c d x y : ℝ) (hy : y = mobius a b c d x) :
    y = (a * x + b) / (c * x + d) := by
  simpa [mobius] using hy

/-- Exercise 759, gap 2; require the denominator used when solving for `x`. -/
theorem gap2 (a b c d x y : ℝ) (hy : y = mobius a b c d x)
    (hdom : c * x + d ≠ 0)
    (hden : y * c - a ≠ 0) :
    x = (-y * d + b) / (y * c - a) := by
  rw [mobius] at hy
  have hy' : y * (c * x + d) = a * x + b := (eq_div_iff hdom).mp hy
  apply (eq_div_iff hden).2
  ring_nf at hy' ⊢
  linarith

/-- Exercise 759, gap 3; state the inverse formula on points where it is defined. -/
theorem gap3 (a b c d x : ℝ) (hdet : a * d - b * c ≠ 0)
    (hden : c * x - a ≠ 0) :
    mobius (-d) b c (-a) x = (-d * x + b) / (c * x - a) := by
  simpa only [mobius, sub_eq_add_neg]

/-- Exercise 759, gap 4; interpret “inverse equals itself” as involutivity. -/
theorem gap4 (a b c d : ℝ) (hdet : a * d - b * c ≠ 0)
    (h : ∀ x, mobius a b c d x = mobius (-d) b c (-a) x) :
    ∀ x, c * x + d ≠ 0 →
      mobius a b c d (mobius a b c d x) = x := by
  intro x hx
  rw [h (mobius a b c d x)]
  exact inverse_comp_mobius a b c d x hdet hx

/-- Exercise 759, gap 5; add the nonzero denominators needed by division. -/
theorem gap5 (a b c d x : ℝ) (htrace : a + d = 0) :
    mobius a b c d x = mobius (-d) b c (-a) x := by
  have ha : -d = a := by
    linarith
  have hd : -a = d := by
    linarith
  simp [mobius, ha, hd]

/-- Exercise 759, gap 6; retain the intended sufficient direction. -/
theorem gap6 (a b c d : ℝ) (hdet : a * d - b * c ≠ 0)
    (htrace : a + d = 0) :
    ∀ x, c * x + d ≠ 0 →
      mobius a b c d (mobius a b c d x) = x := by
  apply gap4 a b c d hdet
  exact fun x => gap5 a b c d x htrace

/-- Exercise 759, gap 7; state the pointwise self-inverse
characterization on its common domain, including scalar identity maps. -/
theorem gap7 (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) :
    (∀ x, c * x + d ≠ 0 → c * x - a ≠ 0 →
        mobius a b c d x = mobius (-d) b c (-a) x) ↔
      a + d = 0 ∨ (b = 0 ∧ c = 0 ∧ a = d) := by
  exact mobius_eq_inverse_iff a b c d hdet

end

end ProofGap.Exercise759
