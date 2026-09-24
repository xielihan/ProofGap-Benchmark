import Mathlib

/- Functions carry their actual domains and values only on those domains.
   Composition includes definedness of the inner expression.
   LogBand interprets the source's real ln inequalities on the natural domain
   of ln, rather than using Mathlib's extension to negative arguments. -/
namespace Exercise203

structure RealFunction where
  dom : Set ℝ
  value : dom → ℝ

noncomputable def compose (f : RealFunction) (s : Set ℝ) (g : ℝ → ℝ) : RealFunction where
  dom := {x | x ∈ s ∧ g x ∈ f.dom}
  value := fun x => f.value ⟨g x.val, x.property.2⟩

noncomputable def sinComp (f : RealFunction) : RealFunction :=
  compose f Set.univ Real.sin

noncomputable def logComp (f : RealFunction) : RealFunction :=
  compose f (Set.Ioi 0) Real.log

noncomputable def floorRatio (x : ℝ) : ℝ := (⌊x⌋ : ℝ) / x

noncomputable def ratioComp (f : RealFunction) : RealFunction :=
  compose f {x | x ≠ 0} floorRatio

def SinBand (x : ℝ) : Prop := 0 < Real.sin x ∧ Real.sin x < 1

def SinRegion (x : ℝ) : Prop :=
  ∃ k : ℤ, 2 * (k : ℝ) * Real.pi < x ∧
    x < Real.pi + 2 * (k : ℝ) * Real.pi ∧
    x ≠ ((4 * (k : ℝ) + 1) / 2) * Real.pi

-- Definedness is part of satisfaction of inequalities containing real ln.
def LogBand (x : ℝ) : Prop :=
  0 < x ∧ 0 < Real.log x ∧ Real.log x < 1

def ExpRegion (x : ℝ) : Prop := 1 < x ∧ x < Real.exp 1

def RatioBand (x : ℝ) : Prop :=
  x ≠ 0 ∧ 0 < floorRatio x ∧ floorRatio x < 1

def RatioRegion (x : ℝ) : Prop :=
  x > 1 ∧ ¬ (∃ k : ℕ, 0 < k ∧ k ≥ 2 ∧ x = (k : ℝ))

end Exercise203

open Exercise203

-- Exercise 203, gap 1
-- SHA-256: b239f45cd7bd2f1ad3060bc8e6904da2363140b05598111559e08f68cbbb1015
theorem proof_gap_exercise_203_1
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  : ∀ x : ℝ, SinBand x → x ∈ F1.dom := by
  sorry

-- Exercise 203, gap 2
-- SHA-256: bc25d83bc7aeb6776c65f31e2af1a262f2147e576d02672ac78a255e9d973022
theorem proof_gap_exercise_203_2
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  : ∀ x : ℝ, SinRegion x → SinBand x := by
  sorry

-- Exercise 203, gap 3
-- SHA-256: f59b9d4de98639d3e3d7b1a20408922c49b0726e526a817be752644047290b2c
theorem proof_gap_exercise_203_3
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  : ∀ x : ℝ, SinRegion x → x ∈ F1.dom := by
  sorry

-- Exercise 203, gap 4
-- SHA-256: 706a9513456d25149f82ea7ef49e1e2e6de10f9b6e9e3bed12f9779b086f3f62
theorem proof_gap_exercise_203_4
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  : F1.dom = {x : ℝ | SinRegion x} := by
  sorry

-- Exercise 203, gap 5
-- SHA-256: a4fb14ccf40accd6b7d17898356dfa4862e926ddc389ed0cd45cff392d557040
theorem proof_gap_exercise_203_5
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  (h12 : F1.dom = {x : ℝ | SinRegion x})
  : ∀ x : ℝ, LogBand x → x ∈ F2.dom := by
  sorry

-- Exercise 203, gap 6
-- SHA-256: 49d041353b0d0be91f36feeaa5877269aee8816a7eab92844123d00edefd641d
theorem proof_gap_exercise_203_6
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  (h12 : F1.dom = {x : ℝ | SinRegion x})
  (h13 : ∀ x : ℝ, LogBand x → x ∈ F2.dom)
  : ∀ x : ℝ, ExpRegion x → LogBand x := by
  sorry

-- Exercise 203, gap 7
-- SHA-256: 9b44c2fddee717a886f9513604169b63ba539cb35b7f2612f0bd5673fdc228ec
theorem proof_gap_exercise_203_7
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  (h12 : F1.dom = {x : ℝ | SinRegion x})
  (h13 : ∀ x : ℝ, LogBand x → x ∈ F2.dom)
  (h14 : ∀ x : ℝ, ExpRegion x → LogBand x)
  : ∀ x : ℝ, ExpRegion x → x ∈ F2.dom := by
  sorry

-- Exercise 203, gap 8
-- SHA-256: d8193bd9d64b3dc8575e505c3ead5f6f5c3dd4a8294218dd36aa161187422f87
theorem proof_gap_exercise_203_8
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  (h12 : F1.dom = {x : ℝ | SinRegion x})
  (h13 : ∀ x : ℝ, LogBand x → x ∈ F2.dom)
  (h14 : ∀ x : ℝ, ExpRegion x → LogBand x)
  (h15 : ∀ x : ℝ, ExpRegion x → x ∈ F2.dom)
  : F2.dom = Set.Ioo 1 (Real.exp 1) := by
  sorry

-- Exercise 203, gap 9
-- SHA-256: 52cf8123f5ecddff17dab2eb98c4617ec8a96880afd2a334e437bbe8d18be211
theorem proof_gap_exercise_203_9
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  (h12 : F1.dom = {x : ℝ | SinRegion x})
  (h13 : ∀ x : ℝ, LogBand x → x ∈ F2.dom)
  (h14 : ∀ x : ℝ, ExpRegion x → LogBand x)
  (h15 : ∀ x : ℝ, ExpRegion x → x ∈ F2.dom)
  (h16 : F2.dom = Set.Ioo 1 (Real.exp 1))
  : ∀ x : ℝ, RatioBand x → x ∈ F3.dom := by
  sorry

-- Exercise 203, gap 10
-- SHA-256: 8b32531f1da7367d32b90a6538617fb4985ef39e7525ed78946d04586a520fde
theorem proof_gap_exercise_203_10
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  (h12 : F1.dom = {x : ℝ | SinRegion x})
  (h13 : ∀ x : ℝ, LogBand x → x ∈ F2.dom)
  (h14 : ∀ x : ℝ, ExpRegion x → LogBand x)
  (h15 : ∀ x : ℝ, ExpRegion x → x ∈ F2.dom)
  (h16 : F2.dom = Set.Ioo 1 (Real.exp 1))
  (h17 : ∀ x : ℝ, RatioBand x → x ∈ F3.dom)
  : ∀ x : ℝ, RatioRegion x → RatioBand x := by
  sorry

-- Exercise 203, gap 11
-- SHA-256: 929cdb0f9c04d83385df0410a9d37fcd2e1d59d401d2ea02d11de4dc87d4554d
theorem proof_gap_exercise_203_11
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  (h12 : F1.dom = {x : ℝ | SinRegion x})
  (h13 : ∀ x : ℝ, LogBand x → x ∈ F2.dom)
  (h14 : ∀ x : ℝ, ExpRegion x → LogBand x)
  (h15 : ∀ x : ℝ, ExpRegion x → x ∈ F2.dom)
  (h16 : F2.dom = Set.Ioo 1 (Real.exp 1))
  (h17 : ∀ x : ℝ, RatioBand x → x ∈ F3.dom)
  (h18 : ∀ x : ℝ, RatioRegion x → RatioBand x)
  : ∀ x : ℝ, RatioRegion x → x ∈ F3.dom := by
  sorry

-- Exercise 203, gap 12
-- SHA-256: e467a7714dff065dc2338dc009211d09e789654622ac1c6553dcd5b656723316
theorem proof_gap_exercise_203_12
  (f F1 F2 F3 : RealFunction)
  (h5 : f.dom = Set.Ioo 0 1)
  (h6 : F1 = sinComp f)
  (h7 : F2 = logComp f)
  (h8 : F3 = ratioComp f)
  (h9 : ∀ x : ℝ, SinBand x → x ∈ F1.dom)
  (h10 : ∀ x : ℝ, SinRegion x → SinBand x)
  (h11 : ∀ x : ℝ, SinRegion x → x ∈ F1.dom)
  (h12 : F1.dom = {x : ℝ | SinRegion x})
  (h13 : ∀ x : ℝ, LogBand x → x ∈ F2.dom)
  (h14 : ∀ x : ℝ, ExpRegion x → LogBand x)
  (h15 : ∀ x : ℝ, ExpRegion x → x ∈ F2.dom)
  (h16 : F2.dom = Set.Ioo 1 (Real.exp 1))
  (h17 : ∀ x : ℝ, RatioBand x → x ∈ F3.dom)
  (h18 : ∀ x : ℝ, RatioRegion x → RatioBand x)
  (h19 : ∀ x : ℝ, RatioRegion x → x ∈ F3.dom)
  : F3.dom = {x : ℝ | RatioRegion x} := by
  sorry

