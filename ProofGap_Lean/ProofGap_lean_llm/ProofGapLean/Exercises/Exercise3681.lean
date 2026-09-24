import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3681

noncomputable section

def objective (q : ℝ × ℝ) : ℝ :=
  (1 + Real.exp q.2) * Real.cos q.1 - q.2 * Real.exp q.2

def critical (q : ℝ × ℝ) : Prop :=
  -(1 + Real.exp q.2) * Real.sin q.1 = 0 ∧
    Real.exp q.2 * (Real.cos q.1 - 1 - q.2) = 0

def criticalPoint (k : ℤ) : ℝ × ℝ :=
  ((k : ℝ) * Real.pi, (-1 : ℝ) ^ k - 1)

def evenPoint (m : ℤ) : ℝ × ℝ :=
  ((2 * m : ℤ) * Real.pi, 0)

def oddPoint (m : ℤ) : ℝ × ℝ :=
  (((2 * m + 1 : ℤ) : ℝ) * Real.pi, -2)

def hessianA (q : ℝ × ℝ) : ℝ :=
  -(1 + Real.exp q.2) * Real.cos q.1

def hessianB (q : ℝ × ℝ) : ℝ :=
  -Real.exp q.2 * Real.sin q.1

def hessianC (q : ℝ × ℝ) : ℝ :=
  Real.exp q.2 * (Real.cos q.1 - 2 - q.2)

def hessianDiscriminant (q : ℝ × ℝ) : ℝ :=
  hessianA q * hessianC q - hessianB q ^ 2

def maximizers : Set (ℝ × ℝ) :=
  {q | ∀ r, objective r ≤ objective q}

def minimizers : Set (ℝ × ℝ) :=
  {q | ∀ r, objective q ≤ objective r}

private lemma even_sin_pi (m : ℤ) :
    Real.sin (((2 * m : ℤ) : ℝ) * Real.pi) = 0 := by
  simpa using Real.sin_int_mul_pi (2 * m)

private lemma even_cos_pi (m : ℤ) :
    Real.cos (((2 * m : ℤ) : ℝ) * Real.pi) = 1 := by
  have hs : Real.sin ((m : ℝ) * Real.pi) = 0 := by
    simpa using Real.sin_int_mul_pi m
  have ht := Real.sin_sq_add_cos_sq ((m : ℝ) * Real.pi)
  rw [hs] at ht
  have ha : (((2 * m : ℤ) : ℝ) * Real.pi) =
      2 * ((m : ℝ) * Real.pi) := by
    norm_num [Int.cast_mul] <;> ring
  rw [ha, Real.cos_two_mul]
  nlinarith

private lemma odd_sin_pi (m : ℤ) :
    Real.sin ((((2 * m + 1 : ℤ) : ℝ)) * Real.pi) = 0 := by
  have ha : (((2 * m + 1 : ℤ) : ℝ) * Real.pi) =
      (((2 * m : ℤ) : ℝ) * Real.pi) + Real.pi := by
    norm_num [Int.cast_add, Int.cast_mul] <;> ring
  rw [ha, Real.sin_add, even_sin_pi m, even_cos_pi m]
  simp

private lemma odd_cos_pi (m : ℤ) :
    Real.cos ((((2 * m + 1 : ℤ) : ℝ)) * Real.pi) = -1 := by
  have ha : (((2 * m + 1 : ℤ) : ℝ) * Real.pi) =
      (((2 * m : ℤ) : ℝ) * Real.pi) + Real.pi := by
    norm_num [Int.cast_add, Int.cast_mul] <;> ring
  rw [ha, Real.cos_add, even_sin_pi m, even_cos_pi m]
  simp

private lemma objective_le_two (q : ℝ × ℝ) : objective q ≤ 2 := by
  have hcoef : 0 ≤ 1 + Real.exp q.2 := by
    linarith [Real.exp_pos q.2]
  have hcosmul :=
    mul_le_mul_of_nonneg_left (Real.cos_le_one q.1) hcoef
  have hlin := Real.add_one_le_exp (-q.2)
  have hmul :=
    mul_le_mul_of_nonneg_left hlin (le_of_lt (Real.exp_pos q.2))
  have hone : Real.exp q.2 * Real.exp (-q.2) = 1 := by
    calc
      Real.exp q.2 * Real.exp (-q.2) = Real.exp (q.2 + -q.2) :=
        (Real.exp_add q.2 (-q.2)).symm
      _ = 1 := by simp
  have htail : Real.exp q.2 * (1 - q.2) ≤ 1 := by
    calc
      Real.exp q.2 * (1 - q.2) = Real.exp q.2 * (-q.2 + 1) := by ring
      _ ≤ Real.exp q.2 * Real.exp (-q.2) := hmul
      _ = 1 := hone
  unfold objective
  calc
    (1 + Real.exp q.2) * Real.cos q.1 - q.2 * Real.exp q.2
        ≤ (1 + Real.exp q.2) * 1 - q.2 * Real.exp q.2 :=
      sub_le_sub_right hcosmul _
    _ = 1 + Real.exp q.2 * (1 - q.2) := by ring
    _ ≤ 1 + 1 := by
      simpa [add_comm] using (add_le_add_left htail 1)
    _ = 2 := by norm_num

theorem gap1 :
    ∀ q, critical q → ∃ k : ℤ, q.1 = (k : ℝ) * Real.pi := by
  intro q hq
  have hfactor : -(1 + Real.exp q.2) ≠ 0 := by
    linarith [Real.exp_pos q.2]
  have hsin : Real.sin q.1 = 0 :=
    (mul_eq_zero.mp hq.1).resolve_left hfactor
  rcases Real.sin_eq_zero_iff.mp hsin with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  linarith [hk]

theorem gap2 :
    ∀ q, critical q → ∃ k : ℤ, q.2 = (-1 : ℝ) ^ k - 1 := by
  intro q hq
  obtain ⟨k, hk⟩ := gap1 q hq
  refine ⟨k, ?_⟩
  have hcos : Real.cos q.1 - 1 - q.2 = 0 :=
    (mul_eq_zero.mp hq.2).resolve_left (Real.exp_ne_zero q.2)
  rw [hk, Real.cos_int_mul_pi] at hcos
  linarith

theorem gap3 :
    {q | critical q} = Set.range criticalPoint := by
  ext q
  constructor
  · intro hq
    change critical q at hq
    obtain ⟨k, hk⟩ := gap1 q hq
    have hcos : Real.cos q.1 - 1 - q.2 = 0 :=
      (mul_eq_zero.mp hq.2).resolve_left (Real.exp_ne_zero q.2)
    have hy : q.2 = (-1 : ℝ) ^ k - 1 := by
      rw [hk, Real.cos_int_mul_pi] at hcos
      linarith
    refine ⟨k, ?_⟩
    apply Prod.ext
    · simpa [criticalPoint] using hk.symm
    · simpa [criticalPoint] using hy.symm
  · rintro ⟨k, rfl⟩
    unfold critical criticalPoint
    dsimp
    constructor
    · simp [Real.sin_int_mul_pi]
    · rw [Real.cos_int_mul_pi]
      ring

theorem gap4 :
    ∀ q, hessianA q = -(1 + Real.exp q.2) * Real.cos q.1 := by
  intro q
  rfl

theorem gap5 :
    ∀ q, hessianB q = -Real.exp q.2 * Real.sin q.1 := by
  intro q
  rfl

theorem gap6 :
    ∀ q, hessianC q =
      Real.exp q.2 * (Real.cos q.1 - 2 - q.2) := by
  intro q
  rfl

theorem gap7 :
    ∀ m : ℤ, hessianA (evenPoint m) = -2 := by
  intro m
  unfold hessianA evenPoint
  dsimp
  rw [even_cos_pi]
  norm_num

theorem gap8 :
    ∀ m : ℤ, hessianB (evenPoint m) = 0 := by
  intro m
  unfold hessianB evenPoint
  dsimp
  rw [even_sin_pi]
  ring

theorem gap9 :
    ∀ m : ℤ, hessianC (evenPoint m) = -1 := by
  intro m
  unfold hessianC evenPoint
  dsimp
  rw [even_cos_pi]
  norm_num

theorem gap10 :
    ∀ m : ℤ, hessianDiscriminant (evenPoint m) = 2 := by
  intro m
  unfold hessianDiscriminant
  rw [gap7 m, gap8 m, gap9 m]
  norm_num

theorem gap11 :
    (2 : ℝ) > 0 := by
  norm_num

theorem gap12 :
    ∀ m : ℤ, hessianDiscriminant (evenPoint m) > 0 := by
  intro m
  rw [gap10 m]
  exact gap11

theorem gap13 :
    ∀ m : ℤ, evenPoint m ∈ maximizers := by
  intro m
  change ∀ r, objective r ≤ objective (evenPoint m)
  intro r
  have heven : objective (evenPoint m) = 2 := by
    unfold objective evenPoint
    dsimp
    rw [even_cos_pi]
    norm_num
  rw [heven]
  exact objective_le_two r

theorem gap14 :
    ∀ m : ℤ, hessianA (oddPoint m) = 1 + Real.exp (-2) := by
  intro m
  unfold hessianA oddPoint
  dsimp
  rw [odd_cos_pi]
  ring

theorem gap15 :
    ∀ m : ℤ, hessianB (oddPoint m) = 0 := by
  intro m
  unfold hessianB oddPoint
  dsimp
  rw [odd_sin_pi]
  ring

theorem gap16 :
    ∀ m : ℤ, hessianC (oddPoint m) = -Real.exp (-2) := by
  intro m
  unfold hessianC oddPoint
  dsimp
  rw [odd_cos_pi]
  ring

theorem gap17 :
    ∀ m : ℤ, hessianDiscriminant (oddPoint m) =
      -Real.exp (-2) - Real.exp (-4) := by
  intro m
  unfold hessianDiscriminant
  rw [gap14 m, gap15 m, gap16 m]
  rw [show (-4 : ℝ) = -2 + -2 by norm_num, Real.exp_add]
  ring

theorem gap18 :
    -Real.exp (-2) - Real.exp (-4) < 0 := by
  linarith [Real.exp_pos (-2), Real.exp_pos (-4)]

theorem gap19 :
    ∀ m : ℤ, hessianDiscriminant (oddPoint m) < 0 := by
  intro m
  rw [gap17 m]
  exact gap18

theorem gap20 :
    ∀ m : ℤ, oddPoint m ∉ minimizers := by
  intro m hm
  change ∀ r, objective (oddPoint m) ≤ objective r at hm
  have hodd : objective (oddPoint m) = -1 + Real.exp (-2) := by
    unfold objective oddPoint
    dsimp
    rw [odd_cos_pi]
    ring
  have href : objective (Real.pi, 0) = -2 := by
    norm_num [objective]
  have hle := hm (Real.pi, 0)
  rw [hodd, href] at hle
  linarith [Real.exp_pos (-2)]

theorem gap21 :
    maximizers.Infinite := by
  have hinj : Function.Injective evenPoint := by
    intro a b hab
    have hfst := congrArg Prod.fst hab
    change ((2 * a : ℤ) : ℝ) * Real.pi = ((2 * b : ℤ) : ℝ) * Real.pi at hfst
    norm_num [Int.cast_mul] at hfst
    exact hfst
  have hrange : (Set.range evenPoint).Infinite :=
    Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro q ⟨m, rfl⟩
  exact gap13 m

theorem gap22 :
    minimizers = ∅ := by
  ext q
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hq
  change ∀ r, objective q ≤ objective r at hq
  let y : ℝ := |objective q| + 1
  have hydef : y = |objective q| + 1 := rfl
  have hy : 0 ≤ y := by
    rw [hydef]
    linarith [abs_nonneg (objective q)]
  have hlin := Real.add_one_le_exp y
  have hexp : 1 ≤ Real.exp y := by
    linarith
  have hfactor : 0 ≤ 1 + y := by linarith
  have hprod : (1 + y) * 1 ≤ (1 + y) * Real.exp y :=
    mul_le_mul_of_nonneg_left hexp hfactor
  have hr : objective (Real.pi, y) = -1 - (1 + y) * Real.exp y := by
    simp [objective]
    ring
  have hle := hq (Real.pi, y)
  rw [hr] at hle
  nlinarith [neg_abs_le (objective q)]

theorem gap23 :
    maximizers.Infinite ∧ minimizers = ∅ := by
  exact ⟨gap21, gap22⟩

end

end ProofGap.Exercise3681
