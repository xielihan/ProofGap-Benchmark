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

/-- Source: `proof_gap/exercise_406/1.txt`; remove the shadowed threshold `N`. -/
theorem gap1 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < |x| → E < |identity x| := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [identity] using hx

/-- Source: `proof_gap/exercise_406/2.txt`; replace the false universal function claim by the definition. -/
theorem gap2 (f : ℝ → ℝ) : AbsAtInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → E < |f x| := by
  rfl

/-- Source: `proof_gap/exercise_406/3.txt`; define the example. -/
theorem gap3 : AbsAtInfinity identity := by
  simpa only [AbsAtInfinity] using gap1

/-- Source: `proof_gap/exercise_406/4.txt`. -/
theorem gap4 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < |x| → negAbs x < -E := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [negAbs] using (neg_lt_neg hx)

/-- Source: `proof_gap/exercise_406/5.txt`. -/
theorem gap5 (f : ℝ → ℝ) : NegAtInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → f x < -E := by
  rfl

/-- Source: `proof_gap/exercise_406/6.txt`. -/
theorem gap6 : NegAtInfinity negAbs := by
  simpa only [NegAtInfinity] using gap4

/-- Source: `proof_gap/exercise_406/7.txt`. -/
theorem gap7 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < |x| → E < absFn x := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [absFn] using hx

/-- Source: `proof_gap/exercise_406/8.txt`. -/
theorem gap8 (f : ℝ → ℝ) : PosAtInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → E < f x := by
  rfl

/-- Source: `proof_gap/exercise_406/9.txt`. -/
theorem gap9 : PosAtInfinity absFn := by
  simpa only [PosAtInfinity] using gap7

/-- Source: `proof_gap/exercise_406/10.txt`. -/
theorem gap10 : ∀ E > 0, ∃ N > 0, ∀ x,
    x < -N → E < |identity x| := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  have hx0 : x < 0 := lt_trans hx (neg_lt_zero.mpr hE)
  simpa only [identity, abs_of_neg hx0, neg_neg] using (neg_lt_neg hx)

/-- Source: `proof_gap/exercise_406/11.txt`. -/
theorem gap11 (f : ℝ → ℝ) : AbsAtNegInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, x < -N → E < |f x| := by
  rfl

/-- Source: `proof_gap/exercise_406/12.txt`. -/
theorem gap12 : AbsAtNegInfinity identity := by
  simpa only [AbsAtNegInfinity] using gap10

/-- Source: `proof_gap/exercise_406/13.txt`. -/
theorem gap13 : ∀ E > 0, ∃ N > 0, ∀ x,
    x < -N → identity x < -E := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [identity] using hx

/-- Source: `proof_gap/exercise_406/14.txt`. -/
theorem gap14 (f : ℝ → ℝ) : NegAtNegInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, x < -N → f x < -E := by
  rfl

/-- Source: `proof_gap/exercise_406/15.txt`. -/
theorem gap15 : NegAtNegInfinity identity := by
  simpa only [NegAtNegInfinity] using gap13

/-- Source: `proof_gap/exercise_406/16.txt`. -/
theorem gap16 : ∀ E > 0, ∃ N > 0, ∀ x,
    x < -N → E < negIdentity x := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [negIdentity, neg_neg] using (neg_lt_neg hx)

/-- Source: `proof_gap/exercise_406/17.txt`. -/
theorem gap17 (f : ℝ → ℝ) : PosAtNegInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, x < -N → E < f x := by
  rfl

/-- Source: `proof_gap/exercise_406/18.txt`. -/
theorem gap18 : PosAtNegInfinity negIdentity := by
  simpa only [PosAtNegInfinity] using gap16

/-- Source: `proof_gap/exercise_406/19.txt`. -/
theorem gap19 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < x → E < |identity x| := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [identity] using (lt_of_lt_of_le hx (le_abs_self x))

/-- Source: `proof_gap/exercise_406/20.txt`. -/
theorem gap20 (f : ℝ → ℝ) : AbsAtPosInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < x → E < |f x| := by
  rfl

/-- Source: `proof_gap/exercise_406/21.txt`. -/
theorem gap21 : AbsAtPosInfinity identity := by
  simpa only [AbsAtPosInfinity] using gap19

/-- Source: `proof_gap/exercise_406/22.txt`. -/
theorem gap22 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < x → negIdentity x < -E := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [negIdentity] using (neg_lt_neg hx)

/-- Source: `proof_gap/exercise_406/23.txt`. -/
theorem gap23 (f : ℝ → ℝ) : NegAtPosInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < x → f x < -E := by
  rfl

/-- Source: `proof_gap/exercise_406/24.txt`. -/
theorem gap24 : NegAtPosInfinity negIdentity := by
  simpa only [NegAtPosInfinity] using gap22

/-- Source: `proof_gap/exercise_406/25.txt`. -/
theorem gap25 : ∀ E > 0, ∃ N > 0, ∀ x,
    N < x → E < identity x := by
  intro E hE
  refine ⟨E, hE, ?_⟩
  intro x hx
  simpa only [identity] using hx

/-- Source: `proof_gap/exercise_406/26.txt`. -/
theorem gap26 (f : ℝ → ℝ) : PosAtPosInfinity f ↔
    ∀ E > 0, ∃ N > 0, ∀ x, N < x → E < f x := by
  rfl

/-- Source: `proof_gap/exercise_406/27.txt`. -/
theorem gap27 : PosAtPosInfinity identity := by
  simpa only [PosAtPosInfinity] using gap25

end

end ProofGap.Exercise406
