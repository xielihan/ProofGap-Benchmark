import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise406

noncomputable section

def AbsAtInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → E < |f x|
def NegAtInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → f x < -E
def PosAtInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → E < f x

def AbsAtNegInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, x < -N → E < |f x|
def NegAtNegInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, x < -N → f x < -E
def PosAtNegInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, x < -N → E < f x

def AbsAtPosInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, N < x → E < |f x|
def NegAtPosInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, N < x → f x < -E
def PosAtPosInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, N < x → E < f x

def identity (x : ℝ) : ℝ := x
def negAbs (x : ℝ) : ℝ := -|x|
def absFn (x : ℝ) : ℝ := |x|
def negIdentity (x : ℝ) : ℝ := -x

/-- Exercise 406, gap 1; remove the shadowed threshold `N`. -/
theorem gap1 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < |x| → E < |identity x| := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [identity] using hx

/-- Exercise 406, gap 2; replace the false universal function claim by the definition. -/
theorem gap2 (f : ℝ → ℝ) : AbsAtInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → E < |f x| := by
  rfl

/-- Exercise 406, gap 3; define the example. -/
theorem gap3 : AbsAtInfinity identity := by
  simpa only [AbsAtInfinity] using gap1

/-- Exercise 406, gap 4. -/
theorem gap4 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < |x| → negAbs x < -E := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [negAbs] using (neg_lt_neg hx)

/-- Exercise 406, gap 5. -/
theorem gap5 (f : ℝ → ℝ) : NegAtInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → f x < -E := by
  rfl

/-- Exercise 406, gap 6. -/
theorem gap6 : NegAtInfinity negAbs := by
  simpa only [NegAtInfinity] using gap4

/-- Exercise 406, gap 7. -/
theorem gap7 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < |x| → E < absFn x := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [absFn] using hx

/-- Exercise 406, gap 8. -/
theorem gap8 (f : ℝ → ℝ) : PosAtInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → E < f x := by
  rfl

/-- Exercise 406, gap 9. -/
theorem gap9 : PosAtInfinity absFn := by
  simpa only [PosAtInfinity] using gap7

/-- Exercise 406, gap 10. -/
theorem gap10 : ∀ E > 0, ∃ N > 0, ∀ x,
    x < -N → E < |identity x| := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  have hx0 : x < 0 := lt_trans hx (neg_lt_zero.mpr hE)
  simpa only [identity, abs_of_neg hx0, neg_neg] using (neg_lt_neg hx)

/-- Exercise 406, gap 11. -/
theorem gap11 (f : ℝ → ℝ) : AbsAtNegInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, x < -N → E < |f x| := by
  rfl

/-- Exercise 406, gap 12. -/
theorem gap12 : AbsAtNegInfinity identity := by
  simpa only [AbsAtNegInfinity] using gap10

/-- Exercise 406, gap 13. -/
theorem gap13 : ∀ E > 0, ∃ N > 0, ∀ x,
    x < -N → identity x < -E := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [identity] using hx

/-- Exercise 406, gap 14. -/
theorem gap14 (f : ℝ → ℝ) : NegAtNegInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, x < -N → f x < -E := by
  rfl

/-- Exercise 406, gap 15. -/
theorem gap15 : NegAtNegInfinity identity := by
  simpa only [NegAtNegInfinity] using gap13

/-- Exercise 406, gap 16. -/
theorem gap16 : ∀ E > 0, ∃ N > 0, ∀ x,
    x < -N → E < negIdentity x := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [negIdentity, neg_neg] using (neg_lt_neg hx)

/-- Exercise 406, gap 17. -/
theorem gap17 (f : ℝ → ℝ) : PosAtNegInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, x < -N → E < f x := by
  rfl

/-- Exercise 406, gap 18. -/
theorem gap18 : PosAtNegInfinity negIdentity := by
  simpa only [PosAtNegInfinity] using gap16

/-- Exercise 406, gap 19. -/
theorem gap19 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < x → E < |identity x| := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [identity] using (lt_of_lt_of_le hx (le_abs_self x))

/-- Exercise 406, gap 20. -/
theorem gap20 (f : ℝ → ℝ) : AbsAtPosInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < x → E < |f x| := by
  rfl

/-- Exercise 406, gap 21. -/
theorem gap21 : AbsAtPosInfinity identity := by
  simpa only [AbsAtPosInfinity] using gap19

/-- Exercise 406, gap 22. -/
theorem gap22 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < x → negIdentity x < -E := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [negIdentity] using (neg_lt_neg hx)

/-- Exercise 406, gap 23. -/
theorem gap23 (f : ℝ → ℝ) : NegAtPosInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < x → f x < -E := by
  rfl

/-- Exercise 406, gap 24. -/
theorem gap24 : NegAtPosInfinity negIdentity := by
  simpa only [NegAtPosInfinity] using gap22

/-- Exercise 406, gap 25. -/
theorem gap25 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < x → E < identity x := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [identity] using hx

/-- Exercise 406, gap 26. -/
theorem gap26 (f : ℝ → ℝ) : PosAtPosInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < x → E < f x := by
  rfl

/-- Exercise 406, gap 27. -/
theorem gap27 : PosAtPosInfinity identity := by
  simpa only [PosAtPosInfinity] using gap25

end

end ProofGap.Exercise406
