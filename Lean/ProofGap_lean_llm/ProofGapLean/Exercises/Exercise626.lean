import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise626

noncomputable section

def residual (f : ℝ → ℝ) (k b x : ℝ) : ℝ := f x - (k * x + b)
def slopeQuotient (f : ℝ → ℝ) (x : ℝ) : ℝ := f x / x
def interceptResidual (f : ℝ → ℝ) (k x : ℝ) : ℝ := f x - k * x
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)
def HasLimitAtNegInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atBot (nhds L)
def IsRightAsymptote (f : ℝ → ℝ) (k b : ℝ) : Prop :=
  HasLimitAtPosInfinity (residual f k b) 0
def IsLeftAsymptote (f : ℝ → ℝ) (k b : ℝ) : Prop :=
  HasLimitAtNegInfinity (residual f k b) 0

/-- Exercise 626, gap 1; remove the shadowed limit variable and exclude `x=0`. -/
theorem gap1 (f : ℝ → ℝ) (k b x : ℝ) (hx : x ≠ 0) :
    slopeQuotient f x = residual f k b x / x + k + b / x := by
  unfold slopeQuotient residual
  field_simp [hx] <;> ring

/-- Exercise 626, gap 2. -/
theorem gap2 (f : ℝ → ℝ) (k b : ℝ)
    (h : IsRightAsymptote f k b) :
    HasLimitAtPosInfinity (slopeQuotient f) k := by
  unfold IsRightAsymptote HasLimitAtPosInfinity at h
  unfold HasLimitAtPosInfinity
  have hr :
      Filter.Tendsto (fun x : ℝ => residual f k b x / x)
        Filter.atTop (nhds 0) :=
    h.div_atTop Filter.tendsto_id
  have hbconst :
      Filter.Tendsto (fun _ : ℝ => b) Filter.atTop (nhds b) :=
    tendsto_const_nhds
  have hb :
      Filter.Tendsto (fun x : ℝ => b / x)
        Filter.atTop (nhds 0) :=
    hbconst.div_atTop Filter.tendsto_id
  have ht :
      Filter.Tendsto
        (fun x : ℝ => residual f k b x / x + k + b / x)
        Filter.atTop (nhds k) := by
    simpa using (hr.add_const k).add hb
  have heq :
      (fun x : ℝ => residual f k b x / x + k + b / x) =ᶠ[Filter.atTop]
        slopeQuotient f := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    exact (gap1 f k b x (ne_of_gt hx)).symm
  exact ht.congr' heq

/-- Exercise 626, gap 3. -/
theorem gap3 (f : ℝ → ℝ) (k b : ℝ)
    (h : IsRightAsymptote f k b) :
    HasLimitAtPosInfinity (interceptResidual f k) b := by
  unfold IsRightAsymptote HasLimitAtPosInfinity at h
  unfold HasLimitAtPosInfinity
  have heq :
      interceptResidual f k = fun x => residual f k b x + b := by
    funext x
    unfold interceptResidual residual
    ring
  rw [heq]
  simpa using h.add_const b

/-- Exercise 626, gap 4. -/
theorem gap4 (f : ℝ → ℝ) (k b : ℝ)
    (hk : HasLimitAtPosInfinity (slopeQuotient f) k)
    (hb : HasLimitAtPosInfinity (interceptResidual f k) b) :
    IsRightAsymptote f k b := by
  unfold HasLimitAtPosInfinity at hb
  unfold IsRightAsymptote HasLimitAtPosInfinity
  have heq :
      residual f k b = fun x => interceptResidual f k x - b := by
    funext x
    unfold residual interceptResidual
    ring
  rw [heq]
  simpa using hb.sub_const b

/-- Exercise 626, gap 5; replace the free `y` equation by the actual line-asymptote statement. -/
theorem gap5 (f : ℝ → ℝ) (k b : ℝ)
    (hk : HasLimitAtPosInfinity (slopeQuotient f) k)
    (hb : HasLimitAtPosInfinity (interceptResidual f k) b) :
    IsRightAsymptote f k b := by
  exact gap4 f k b hk hb

/-- Exercise 626, gap 6; left-tail conclusions require left-tail hypotheses. -/
theorem gap6 (f : ℝ → ℝ) (k b : ℝ)
    (hk : HasLimitAtNegInfinity (slopeQuotient f) k)
    (hb : HasLimitAtNegInfinity (interceptResidual f k) b) :
    IsLeftAsymptote f k b := by
  unfold HasLimitAtNegInfinity at hb
  unfold IsLeftAsymptote HasLimitAtNegInfinity
  have heq :
      residual f k b = fun x => interceptResidual f k x - b := by
    funext x
    unfold residual interceptResidual
    ring
  rw [heq]
  simpa using hb.sub_const b

/-- Exercise 626, gap 7; bind the two limits instead of placing limit expressions inside a singleton. -/
theorem gap7 (f : ℝ → ℝ) (k b : ℝ)
    (hk : HasLimitAtPosInfinity (slopeQuotient f) k)
    (hb : HasLimitAtPosInfinity (interceptResidual f k) b) :
    IsRightAsymptote f k b := by
  exact gap4 f k b hk hb

end

end ProofGap.Exercise626
