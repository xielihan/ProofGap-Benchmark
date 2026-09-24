import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1460

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2
def g (x₁ x₂ b x : ℝ) : ℝ := (x₁ + x₂) * x + b
def error (x₁ x₂ b x : ℝ) : ℝ := f x - g x₁ x₂ b x

def uniformError (x₁ x₂ b : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x ∈ Set.Icc x₁ x₂, y = |error x₁ x₂ b x|}

def IsBest (x₁ x₂ b : ℝ) : Prop :=
  ∀ b' : ℝ, uniformError x₁ x₂ b ≤ uniformError x₁ x₂ b'

def optimalB (x₁ x₂ : ℝ) : ℝ :=
  -(1 / 8 : ℝ) * (x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂)

def IsMinimizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x₀ ≤ u x

theorem gap1 (x₁ x₂ b x : ℝ) :
    error x₁ x₂ b x = x ^ 2 - ((x₁ + x₂) * x + b) := by
  rfl

theorem gap2 (x₁ x₂ b x : ℝ) :
    deriv f x - deriv (g x₁ x₂ b) x = 2 * x - (x₁ + x₂) := by
  have hf_eq : f = fun y : ℝ => y * y := by
    funext y
    simp [f, pow_two]
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x :=
    hid.mul hid
  have hfderiv : deriv (fun y : ℝ => y * y) x = 2 * x := by
    rw [hsq.deriv]
    ring
  have hc : HasDerivAt (fun _ : ℝ => x₁ + x₂) 0 x :=
    hasDerivAt_const x (x₁ + x₂)
  have hmul : HasDerivAt (fun y : ℝ => (x₁ + x₂) * y) (x₁ + x₂) x := by
    simpa using hc.mul hid
  have hb : HasDerivAt (fun _ : ℝ => b) 0 x :=
    hasDerivAt_const x b
  have hg : HasDerivAt (g x₁ x₂ b) (x₁ + x₂) x := by
    simpa [g] using hmul.add hb
  rw [hf_eq, hfderiv, hg.deriv]

theorem gap3 (x₁ x₂ b x : ℝ)
    (hzero : deriv f x - deriv (g x₁ x₂ b) x = 0) :
    x = (x₁ + x₂) / 2 := by
  rw [gap2 x₁ x₂ b x] at hzero
  linarith

theorem gap4 (x₁ x₂ b x : ℝ) :
    deriv (deriv f) x - deriv (deriv (g x₁ x₂ b)) x = 2 := by
  have hf_eq : f = fun z : ℝ => z * z := by
    funext z
    simp [f, pow_two]
  have hdf : deriv (fun z : ℝ => z * z) = fun y : ℝ => 2 * y := by
    funext y
    have hid : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
    have hsq : HasDerivAt (fun z : ℝ => z * z) (1 * y + y * 1) y :=
      hid.mul hid
    rw [hsq.deriv]
    ring
  have hdg : deriv (g x₁ x₂ b) = fun _ : ℝ => x₁ + x₂ := by
    funext y
    have hid : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
    have hc : HasDerivAt (fun _ : ℝ => x₁ + x₂) 0 y :=
      hasDerivAt_const y (x₁ + x₂)
    have hmul : HasDerivAt (fun z : ℝ => (x₁ + x₂) * z) (x₁ + x₂) y := by
      simpa using hc.mul hid
    have hb : HasDerivAt (fun _ : ℝ => b) 0 y :=
      hasDerivAt_const y b
    have hy : HasDerivAt (g x₁ x₂ b) (x₁ + x₂) y := by
      simpa [g] using hmul.add hb
    exact hy.deriv
  rw [hf_eq, hdf, hdg]
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have htwo : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x :=
    hasDerivAt_const x (2 : ℝ)
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using htwo.mul hid
  have hconst : HasDerivAt (fun _ : ℝ => x₁ + x₂) 0 x :=
    hasDerivAt_const x (x₁ + x₂)
  rw [hlin.deriv, hconst.deriv]
  norm_num

theorem gap5 :
    (2 : ℝ) > 0 := by
  norm_num

theorem gap6 (x₁ x₂ b x : ℝ) :
    deriv (deriv f) x - deriv (deriv (g x₁ x₂ b)) x > 0 := by
  rw [gap4 x₁ x₂ b x]
  exact gap5

theorem gap7 (x₁ x₂ b : ℝ) (h12 : x₁ ≤ x₂) :
    IsMinimizerOn (error x₁ x₂ b) (Set.Icc x₁ x₂) ((x₁ + x₂) / 2) := by
  unfold IsMinimizerOn
  constructor
  · constructor <;> linarith
  · intro y hy
    simp only [error, f, g]
    nlinarith [sq_nonneg (2 * y - (x₁ + x₂))]

theorem gap8 (x₁ x₂ b : ℝ) (h12 : x₁ ≤ x₂) :
    uniformError x₁ x₂ b =
      max |error x₁ x₂ b ((x₁ + x₂) / 2)|
        (max |error x₁ x₂ b x₁| |error x₁ x₂ b x₂|) := by
  have hmid : (x₁ + x₂) / 2 ∈ Set.Icc x₁ x₂ :=
    (gap7 x₁ x₂ b h12).1
  have hbound : ∀ x ∈ Set.Icc x₁ x₂,
      |error x₁ x₂ b x| ≤
        max |error x₁ x₂ b ((x₁ + x₂) / 2)|
          (max |error x₁ x₂ b x₁| |error x₁ x₂ b x₂|) := by
    intro x hx
    have hmin : error x₁ x₂ b ((x₁ + x₂) / 2) ≤ error x₁ x₂ b x :=
      (gap7 x₁ x₂ b h12).2 x hx
    have hprod : (x - x₁) * (x - x₂) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2)
    have hmax : error x₁ x₂ b x ≤ error x₁ x₂ b x₁ := by
      simp only [error, f, g]
      nlinarith [hprod]
    have hleft :
        |error x₁ x₂ b ((x₁ + x₂) / 2)| ≤
          max |error x₁ x₂ b ((x₁ + x₂) / 2)|
            (max |error x₁ x₂ b x₁| |error x₁ x₂ b x₂|) :=
      le_max_left _ _
    have hright :
        |error x₁ x₂ b x₁| ≤
          max |error x₁ x₂ b ((x₁ + x₂) / 2)|
            (max |error x₁ x₂ b x₁| |error x₁ x₂ b x₂|) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    apply (abs_le).2
    constructor
    · have ha := neg_abs_le (error x₁ x₂ b ((x₁ + x₂) / 2))
      linarith
    · have hc := le_abs_self (error x₁ x₂ b x₁)
      linarith
  have hne :
      ({y : ℝ | ∃ x ∈ Set.Icc x₁ x₂,
        y = |error x₁ x₂ b x|} : Set ℝ).Nonempty := by
    exact ⟨|error x₁ x₂ b x₁|, x₁, ⟨le_rfl, h12⟩, rfl⟩
  have hbdd : BddAbove
      {y : ℝ | ∃ x ∈ Set.Icc x₁ x₂,
        y = |error x₁ x₂ b x|} := by
    refine ⟨max |error x₁ x₂ b ((x₁ + x₂) / 2)|
      (max |error x₁ x₂ b x₁| |error x₁ x₂ b x₂|), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hbound x hx
  apply le_antisymm
  · apply csSup_le hne
    rintro y ⟨x, hx, rfl⟩
    exact hbound x hx
  · apply max_le
    · apply le_csSup hbdd
      exact ⟨(x₁ + x₂) / 2, hmid, rfl⟩
    · apply max_le
      · apply le_csSup hbdd
        exact ⟨x₁, ⟨le_rfl, h12⟩, rfl⟩
      · apply le_csSup hbdd
        exact ⟨x₂, ⟨h12, le_rfl⟩, rfl⟩

theorem gap9 (x₁ x₂ b : ℝ) (h12 : x₁ ≤ x₂) :
    uniformError x₁ x₂ b =
      max |b + (x₁ + x₂) ^ 2 / 4| |b + x₁ * x₂| := by
  rw [gap8 x₁ x₂ b h12]
  have hm : error x₁ x₂ b ((x₁ + x₂) / 2) =
      -(b + (x₁ + x₂) ^ 2 / 4) := by
    simp only [error, f, g]
    ring
  have h1 : error x₁ x₂ b x₁ = -(b + x₁ * x₂) := by
    simp only [error, f, g]
    ring
  have h2 : error x₁ x₂ b x₂ = -(b + x₁ * x₂) := by
    simp only [error, f, g]
    ring
  rw [hm, h1, h2]
  simp only [abs_neg, max_self]

theorem gap10 (x₁ x₂ b : ℝ) (h12 : x₁ < x₂)
    (heq : |b + (x₁ + x₂) ^ 2 / 4| = |b + x₁ * x₂|) :
    IsBest x₁ x₂ b := by
  let A : ℝ := (x₁ + x₂) ^ 2 / 4
  let B : ℝ := x₁ * x₂
  change |b + A| = |b + B| at heq
  have hAB : B < A := by
    have hd : x₁ - x₂ < 0 := sub_neg.mpr h12
    dsimp [A, B]
    nlinarith [mul_pos_of_neg_of_neg hd hd]
  have hbmid : b = -(A + B) / 2 := by
    rcases (abs_eq_abs.mp heq) with hsame | hopp
    · exfalso
      linarith
    · linarith
  have hcurarg : b + A = (A - B) / 2 := by
    rw [hbmid]
    ring
  have hcur : |b + A| = (A - B) / 2 := by
    rw [hcurarg, abs_of_pos]
    linarith
  unfold IsBest
  intro b'
  rw [gap9 x₁ x₂ b (le_of_lt h12), gap9 x₁ x₂ b' (le_of_lt h12)]
  change max |b + A| |b + B| ≤ max |b' + A| |b' + B|
  rw [← heq, max_self, hcur]
  have ht := abs_add_le (b' + A) (-(b' + B))
  have habs : A - B ≤ |b' + A| + |b' + B| := by
    have hsum : (b' + A) + -(b' + B) = A - B := by ring
    rw [hsum, abs_of_pos (sub_pos.mpr hAB), abs_neg] at ht
    exact ht
  have hl : |b' + A| ≤ max |b' + A| |b' + B| := le_max_left _ _
  have hr : |b' + B| ≤ max |b' + A| |b' + B| := le_max_right _ _
  linarith

theorem gap11 (x₁ x₂ b : ℝ) (hb : b = optimalB x₁ x₂) :
    |b + (x₁ + x₂) ^ 2 / 4| = |b + x₁ * x₂| := by
  rw [hb]
  have h : optimalB x₁ x₂ + (x₁ + x₂) ^ 2 / 4 =
      -(optimalB x₁ x₂ + x₁ * x₂) := by
    unfold optimalB
    ring
  rw [h, abs_neg]

theorem gap12 (x₁ x₂ b : ℝ) (h12 : x₁ ≤ x₂)
    (hb : b = optimalB x₁ x₂) :
    IsBest x₁ x₂ b := by
  rcases eq_or_lt_of_le h12 with heq | hlt
  · subst x₂
    unfold IsBest
    intro b'
    rw [gap9 x₁ x₁ b le_rfl, gap9 x₁ x₁ b' le_rfl]
    have hA : (x₁ + x₁) ^ 2 / 4 = x₁ * x₁ := by ring
    have hopt : optimalB x₁ x₁ = -(x₁ * x₁) := by
      unfold optimalB
      ring
    rw [hA, hb, hopt]
    simp
  · exact gap10 x₁ x₂ b hlt (gap11 x₁ x₂ b hb)

theorem gap13 (x₁ x₂ b x : ℝ) (hb : b = optimalB x₁ x₂) :
    g x₁ x₂ b x = (x₁ + x₂) * x + optimalB x₁ x₂ := by
  simp [g, hb]

theorem gap14 (x₁ x₂ : ℝ) (h12 : x₁ ≤ x₂) :
    uniformError x₁ x₂ (optimalB x₁ x₂) = (1 / 8 : ℝ) * (x₁ - x₂) ^ 2 := by
  rw [gap9 x₁ x₂ (optimalB x₁ x₂) h12]
  have heq := gap11 x₁ x₂ (optimalB x₁ x₂) rfl
  rw [heq, max_self]
  have harg : optimalB x₁ x₂ + x₁ * x₂ =
      -((1 / 8 : ℝ) * (x₁ - x₂) ^ 2) := by
    unfold optimalB
    ring
  have hnonneg : 0 ≤ (1 / 8 : ℝ) * (x₁ - x₂) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg (x₁ - x₂))
  rw [harg, abs_neg, abs_of_nonneg hnonneg]

theorem gap15 (x₁ x₂ b : ℝ) (h12 : x₁ ≤ x₂)
    (hb : b ∈ ({optimalB x₁ x₂} : Set ℝ)) :
    IsBest x₁ x₂ b := by
  have hb' : b = optimalB x₁ x₂ := by
    simpa using hb
  exact gap12 x₁ x₂ b h12 hb'

end

end ProofGap.Exercise1460
