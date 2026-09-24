import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise778

noncomputable section

def u (x y : ℝ) : ℝ := Real.arccos x + Real.arccos y

def cosineArgument (x y : ℝ) : ℝ :=
  x * y - Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - y ^ 2)

def v (x y : ℝ) : ℝ := Real.arccos (cosineArgument x y)

def ε (x y : ℝ) : ℕ := if 0 ≤ x + y then 0 else 1

/-- Exercise 778, gap 1. -/
theorem gap1 (x : ℝ) (hx : |x| ≤ 1) : 0 ≤ Real.arccos x := by
  exact Real.arccos_nonneg x

/-- Exercise 778, gap 2. -/
theorem gap2 (x : ℝ) (hx : |x| ≤ 1) : Real.arccos x ≤ Real.pi := by
  exact Real.arccos_le_pi x

/-- Exercise 778, gap 3. -/
theorem gap3 : 0 ≤ Real.pi := by
  exact le_of_lt Real.pi_pos

/-- Exercise 778, gap 4. -/
theorem gap4 (y : ℝ) (hy : |y| ≤ 1) : 0 ≤ Real.arccos y := by
  exact Real.arccos_nonneg y

/-- Exercise 778, gap 5. -/
theorem gap5 (y : ℝ) (hy : |y| ≤ 1) : Real.arccos y ≤ Real.pi := by
  exact Real.arccos_le_pi y

/-- Exercise 778, gap 6. -/
theorem gap6 : 0 ≤ Real.pi := by
  exact gap3

/-- Exercise 778, gap 7. -/
theorem gap7 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) : 0 ≤ u x y := by
  unfold u
  exact add_nonneg (gap1 x hx) (gap4 y hy)

/-- Exercise 778, gap 8. -/
theorem gap8 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    u x y ≤ 2 * Real.pi := by
  unfold u
  linarith [gap2 x hx, gap5 y hy]

/-- Exercise 778, gap 9. -/
theorem gap9 : 0 ≤ 2 * Real.pi := by
  linarith [gap3]

/-- Exercise 778, gap 10. -/
theorem gap10 (x y : ℝ) (hu0 : 0 ≤ u x y) (huπ : u x y ≤ Real.pi) :
    Real.arccos x ≤ Real.pi - Real.arccos y := by
  unfold u at huπ
  linarith

/-- Exercise 778, gap 11. -/
theorem gap11 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (huπ : u x y ≤ Real.pi) :
    x ≥ Real.cos (Real.pi - Real.arccos y) := by
  have hxy : Real.arccos x ≤ Real.pi - Real.arccos y :=
    gap10 x y (gap7 x y hx hy) huπ
  have hsub0 : 0 ≤ Real.pi - Real.arccos y := by
    linarith [gap5 y hy]
  have hsubπ : Real.pi - Real.arccos y ≤ Real.pi := by
    linarith [gap4 y hy]
  have hcos :
      Real.cos (Real.pi - Real.arccos y) ≤ Real.cos (Real.arccos x) :=
    Real.strictAntiOn_cos.antitoneOn
      ⟨gap1 x hx, gap2 x hx⟩ ⟨hsub0, hsubπ⟩ hxy
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  have hcx : Real.cos (Real.arccos x) = x :=
    Real.cos_arccos hxlo hxhi
  rwa [hcx] at hcos

/-- Exercise 778, gap 12. -/
theorem gap12 (y : ℝ) (hy : |y| ≤ 1) :
    Real.cos (Real.pi - Real.arccos y) = -y := by
  rcases abs_le.mp hy with ⟨hylo, hyhi⟩
  rw [Real.cos_sub, Real.cos_pi, Real.sin_pi,
    Real.cos_arccos hylo hyhi]
  ring

/-- Exercise 778, gap 13. -/
theorem gap13 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (huπ : u x y ≤ Real.pi) :
    x ≥ -y := by
  have h := gap11 x y hx hy huπ
  rw [gap12 y hy] at h
  exact h

/-- Exercise 778, gap 14. -/
theorem gap14 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (huπ : u x y ≤ Real.pi) :
    x + y ≥ 0 := by
  linarith [gap13 x y hx hy huπ]

/-- Exercise 778, gap 15. -/
theorem gap15 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hπu : Real.pi < u x y) :
    x + y < 0 := by
  by_contra hnot
  have hsum : 0 ≤ x + y := not_lt.mp hnot
  have hlt : Real.pi - Real.arccos y < Real.arccos x := by
    unfold u at hπu
    linarith
  have hsub0 : 0 ≤ Real.pi - Real.arccos y := by
    linarith [gap5 y hy]
  have hsubπ : Real.pi - Real.arccos y ≤ Real.pi := by
    linarith [gap4 y hy]
  have hcos :
      Real.cos (Real.arccos x) <
        Real.cos (Real.pi - Real.arccos y) :=
    Real.strictAntiOn_cos
      ⟨hsub0, hsubπ⟩ ⟨gap1 x hx, gap2 x hx⟩ hlt
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  rw [Real.cos_arccos hxlo hxhi, gap12 y hy] at hcos
  linarith

/-- Exercise 778, gap 16. -/
theorem gap16 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    Real.cos (Real.arccos x + Real.arccos y) = cosineArgument x y := by
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hy with ⟨hylo, hyhi⟩
  unfold cosineArgument
  rw [Real.cos_add, Real.cos_arccos hxlo hxhi,
    Real.cos_arccos hylo hyhi, Real.sin_arccos, Real.sin_arccos]

/-- Exercise 778, gap 17. -/
theorem gap17 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    Real.cos (u x y) = Real.cos (v x y) := by
  have harg : cosineArgument x y = Real.cos (u x y) := by
    symm
    simpa [u] using gap16 x y hx hy
  unfold v
  rw [harg]
  rw [Real.cos_arccos (Real.neg_one_le_cos (u x y))
    (Real.cos_le_one (u x y))]

/-- Exercise 778, gap 18. -/
theorem gap18 (x y : ℝ) : 0 ≤ v x y := by
  exact Real.arccos_nonneg (cosineArgument x y)

/-- Exercise 778, gap 19. -/
theorem gap19 (x y : ℝ) : v x y ≤ Real.pi := by
  exact Real.arccos_le_pi (cosineArgument x y)

/-- Exercise 778, gap 20. -/
theorem gap20 : 0 ≤ Real.pi := by
  exact gap3

/-- Exercise 778, gap 21. -/
theorem gap21 (x y : ℝ) (hu0 : 0 ≤ u x y) (huπ : u x y ≤ Real.pi)
    (hcos : Real.cos (u x y) = Real.cos (v x y)) :
    u x y = v x y := by
  apply Real.strictAntiOn_cos.injOn
  · exact ⟨hu0, huπ⟩
  · exact ⟨gap18 x y, gap19 x y⟩
  · exact hcos

/-- Exercise 778, gap 22. -/
theorem gap22 (x y : ℝ) (hπu : Real.pi ≤ u x y)
    (hu2π : u x y ≤ 2 * Real.pi)
    (hcos : Real.cos (u x y) = Real.cos (v x y)) :
    u x y = 2 * Real.pi - v x y := by
  have hv0 : 0 ≤ v x y := gap18 x y
  have hvπ : v x y ≤ Real.pi := gap19 x y
  have hw0 : 0 ≤ 2 * Real.pi - u x y := by
    linarith
  have hwπ : 2 * Real.pi - u x y ≤ Real.pi := by
    linarith
  have hreflect :
      Real.cos (2 * Real.pi - u x y) = Real.cos (u x y) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    ring
  have hwcos :
      Real.cos (2 * Real.pi - u x y) = Real.cos (v x y) :=
    hreflect.trans hcos
  have hw : 2 * Real.pi - u x y = v x y :=
    Real.strictAntiOn_cos.injOn
      ⟨hw0, hwπ⟩ ⟨hv0, hvπ⟩ hwcos
  linarith

/-- Exercise 778, gap 23; encode the two source cases with `if`. -/
theorem gap23 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    u x y = if 0 ≤ x + y then v x y else 2 * Real.pi - v x y := by
  have hu0 : 0 ≤ u x y := gap7 x y hx hy
  have hu2 : u x y ≤ 2 * Real.pi := gap8 x y hx hy
  have hcos : Real.cos (u x y) = Real.cos (v x y) :=
    gap17 x y hx hy
  by_cases hxy : 0 ≤ x + y
  · rw [if_pos hxy]
    have huπ : u x y ≤ Real.pi := by
      by_contra hnot
      have hπu : Real.pi < u x y := lt_of_not_ge hnot
      have hneg : x + y < 0 := gap15 x y hx hy hπu
      exact (not_lt_of_ge hxy) hneg
    exact gap21 x y hu0 huπ hcos
  · rw [if_neg hxy]
    have hπu : Real.pi ≤ u x y := by
      by_contra hnot
      have huπ : u x y ≤ Real.pi := le_of_lt (lt_of_not_ge hnot)
      exact hxy (gap14 x y hx hy huπ)
    exact gap22 x y hπu hu2 hcos

/-- Exercise 778, gap 24; give the exponent and indicator natural-number types. -/
theorem gap24 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    u x y = (-1 : ℝ) ^ (ε x y) * v x y + 2 * (ε x y : ℝ) * Real.pi := by
  rw [gap23 x y hx hy]
  by_cases hxy : 0 ≤ x + y
  · simp [hxy, ε]
  · simp [hxy, ε, sub_eq_add_neg, add_comm]

/-- Exercise 778, gap 25. -/
theorem gap25 (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    Real.arccos x + Real.arccos y =
      (-1 : ℝ) ^ (ε x y) * Real.arccos (cosineArgument x y) +
        2 * (ε x y : ℝ) * Real.pi := by
  simpa [u, v] using gap24 x y hx hy

end

end ProofGap.Exercise778
