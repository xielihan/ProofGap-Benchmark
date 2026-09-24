import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1221_2

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def f (m x : ℝ) : ℝ := Real.sin (m * Real.arcsin x)
def y (m x : ℝ) : ℝ := f m x

def oddProduct (m : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (m ^ 2 - (2 * j + 1 : ℝ) ^ 2)

private theorem iterDeriv_succ_eval (r : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    iterDeriv (r + 1) g x = deriv (iterDeriv r g) x := by
  simp [iterDeriv, Function.iterate_succ_apply']

theorem gap1 (m x : ℝ) :
    deriv (y m) x = deriv (f m) x := by
  rfl

theorem gap2 (m x : ℝ) (hx : |x| < 1) :
    deriv (f m) x =
      m / Real.sqrt (1 - x ^ 2) * Real.cos (m * Real.arcsin x) := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hxneg : x ≠ -1 := ne_of_gt hx'.1
  have hxone : x ≠ 1 := ne_of_lt hx'.2
  have hi := (Real.hasDerivAt_arcsin hxneg hxone).const_mul m
  have hs := (Real.hasDerivAt_sin (m * Real.arcsin x)).comp x hi
  change deriv (Real.sin ∘ fun y : ℝ => m * Real.arcsin y) x = _
  rw [hs.deriv]
  simp only [one_mul, div_eq_mul_inv]
  ring

theorem gap3 (m x : ℝ) (hx : |x| < 1) :
    deriv (y m) x =
      m / Real.sqrt (1 - x ^ 2) * Real.cos (m * Real.arcsin x) := by
  simpa only [y] using gap2 m x hx

theorem gap4 (m x : ℝ) :
    iterDeriv 2 (y m) x = iterDeriv 2 (f m) x := by
  rfl

theorem gap5 (m x : ℝ) (hx : |x| < 1) :
    iterDeriv 2 (f m) x =
      -m ^ 2 / (1 - x ^ 2) * Real.sin (m * Real.arcsin x) +
        m * x / Real.sqrt (1 - x ^ 2) ^ 3 * Real.cos (m * Real.arcsin x) := by
  have hq : 0 < 1 - x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith [sq_nonneg x]
  have hqn : 1 - x ^ 2 ≠ 0 := ne_of_gt hq
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hq)
  have hs3 : Real.sqrt (1 - x ^ 2) ^ 3 =
      Real.sqrt (1 - x ^ 2) * (1 - x ^ 2) := by
    calc
      Real.sqrt (1 - x ^ 2) ^ 3 =
          Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) ^ 2 := by ring
      _ = Real.sqrt (1 - x ^ 2) * (1 - x ^ 2) := by rw [hs2]
  have hpoly : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hsqrt := (Real.hasDerivAt_sqrt hqn).comp x hpoly
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hxneg : x ≠ -1 := ne_of_gt hx'.1
  have hxone : x ≠ 1 := ne_of_lt hx'.2
  have hi := (Real.hasDerivAt_arcsin hxneg hxone).const_mul m
  have hc := (Real.hasDerivAt_cos (m * Real.arcsin x)).comp x hi
  have hcalc := ((hasDerivAt_const x m).div hsqrt hs).mul hc
  have hd :
      deriv (fun z : ℝ =>
        m / Real.sqrt (1 - z ^ 2) * Real.cos (m * Real.arcsin z)) x =
        (0 * Real.sqrt (1 - x ^ 2) -
            m * (1 / (2 * Real.sqrt (1 - x ^ 2)) * (-2 * x))) /
              Real.sqrt (1 - x ^ 2) ^ 2 *
                Real.cos (m * Real.arcsin x) +
          m / Real.sqrt (1 - x ^ 2) *
            (-Real.sin (m * Real.arcsin x) *
              (m * (1 / Real.sqrt (1 - x ^ 2)))) := by
    simpa only [Function.comp_apply] using hcalc.deriv
  have hopen : IsOpen {z : ℝ | |z| < 1} :=
    isOpen_lt continuous_abs continuous_const
  have hnhds : ∀ᶠ z : ℝ in nhds x, |z| < 1 := hopen.mem_nhds hx
  have heq :
      deriv (f m) =ᶠ[nhds x]
        (fun z : ℝ => m / Real.sqrt (1 - z ^ 2) *
          Real.cos (m * Real.arcsin z)) := by
    filter_upwards [hnhds] with z hz
    exact gap2 m z hz
  change deriv (deriv (f m)) x = _
  rw [heq.deriv_eq]
  rw [hd]
  field_simp [hs, hqn]
  rw [hs2, hs3]
  ring

theorem gap6 (m x : ℝ) (hx : |x| < 1) :
    iterDeriv 2 (y m) x =
      -m ^ 2 / (1 - x ^ 2) * Real.sin (m * Real.arcsin x) +
        m * x / Real.sqrt (1 - x ^ 2) ^ 3 * Real.cos (m * Real.arcsin x) := by
  simpa only [y] using gap5 m x hx

theorem gap7 (m : ℝ) :
    deriv (y m) 0 = deriv (f m) 0 := by
  rfl

theorem gap8 (m : ℝ) :
    deriv (f m) 0 = m := by
  have h := gap2 m 0 (by norm_num)
  norm_num [f] at h ⊢
  exact h

theorem gap9 (m : ℝ) :
    iterDeriv 2 (y m) 0 = iterDeriv 2 (f m) 0 := by
  rfl

theorem gap10 (m : ℝ) :
    iterDeriv 2 (f m) 0 = 0 := by
  have h := gap5 m 0 (by norm_num)
  norm_num [f] at h ⊢
  exact h

theorem gap11 (m x : ℝ) (hx : |x| < 1) :
    (1 - x ^ 2) * iterDeriv 2 (y m) x -
        x * deriv (y m) x + m ^ 2 * y m x = 0 := by
  have hq : 0 < 1 - x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith [sq_nonneg x]
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hq)
  rw [gap6 m x hx, gap3 m x hx]
  simp only [y, f]
  field_simp [hs, ne_of_gt hq]
  rw [hs2]
  ring

theorem gap12 (m : ℝ) (n : ℕ) :
    iterDeriv (n + 2) (y m) 0 +
        (m ^ 2 - (n : ℝ) ^ 2) * iterDeriv n (y m) 0 = 0 := by
  let A : ℕ → ℝ → ℝ := fun r => iterDeriv r (y m)
  let E : ℕ → ℝ → ℝ := fun r z =>
    (1 - z ^ 2) * A (r + 2) z -
      (2 * (r : ℝ) + 1) * z * A (r + 1) z +
      (m ^ 2 - (r : ℝ) ^ 2) * A r z
  let P : ℕ → Prop := fun r =>
    (∀ z, |z| < 1 → E r z = 0) ∧
    (∀ z, |z| < 1 →
      DifferentiableAt ℝ (A r) z ∧
      DifferentiableAt ℝ (A (r + 1)) z ∧
      DifferentiableAt ℝ (A (r + 2)) z)
  have hP : ∀ r, P r := by
    intro r
    induction r with
    | zero =>
        constructor
        · intro z hz
          simpa [E, A] using gap11 m z hz
        · intro z hz
          have hzI : z ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hz
          have hzneg : z ≠ -1 := ne_of_gt hzI.1
          have hzone : z ≠ 1 := ne_of_lt hzI.2
          have hq : 0 < 1 - z ^ 2 := by
            have hz' := abs_lt.mp hz
            nlinarith [sq_nonneg z]
          have hqn : 1 - z ^ 2 ≠ 0 := ne_of_gt hq
          have hs : Real.sqrt (1 - z ^ 2) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.2 hq)
          have hopen : IsOpen {w : ℝ | |w| < 1} :=
            isOpen_lt continuous_abs continuous_const
          have hnhds : ∀ᶠ w : ℝ in nhds z, |w| < 1 := hopen.mem_nhds hz
          have hpoly : HasDerivAt (fun w : ℝ => 1 - w ^ 2) (-2 * z) z := by
            convert (hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).pow 2) using 1 <;>
              simp <;> ring
          have hsqrt := (Real.hasDerivAt_sqrt hqn).comp z hpoly
          have hi := (Real.hasDerivAt_arcsin hzneg hzone).const_mul m
          have hsin := (Real.hasDerivAt_sin (m * Real.arcsin z)).comp z hi
          have hcos := (Real.hasDerivAt_cos (m * Real.arcsin z)).comp z hi
          have hd0 : DifferentiableAt ℝ (A 0) z := by
            simpa [A, y, f, Function.comp_apply] using hsin.differentiableAt
          let g1 : ℝ → ℝ := fun w =>
            m / Real.sqrt (1 - w ^ 2) * Real.cos (m * Real.arcsin w)
          have heq1 : A 1 =ᶠ[nhds z] g1 := by
            filter_upwards [hnhds] with w hw
            simpa [A, g1] using gap3 m w hw
          have hdg1 : DifferentiableAt ℝ g1 z := by
            have hg1 := ((hasDerivAt_const z m).div hsqrt hs).mul hcos
            simpa [g1, Function.comp_apply] using hg1.differentiableAt
          have hd1 : DifferentiableAt ℝ (A 1) z :=
            heq1.differentiableAt_iff.mpr hdg1
          let g2 : ℝ → ℝ := fun w =>
            -m ^ 2 / (1 - w ^ 2) * Real.sin (m * Real.arcsin w) +
              m * w / Real.sqrt (1 - w ^ 2) ^ 3 *
                Real.cos (m * Real.arcsin w)
          have heq2 : A 2 =ᶠ[nhds z] g2 := by
            filter_upwards [hnhds] with w hw
            simpa [A, g2] using gap6 m w hw
          have hdg2 : DifferentiableAt ℝ g2 z := by
            have hfirst :=
              ((hasDerivAt_const z (-m ^ 2)).div hpoly hqn).mul hsin
            have hnum := (hasDerivAt_const z m).mul (hasDerivAt_id z)
            have hden := hsqrt.pow 3
            have hsecond :=
              (hnum.div hden (pow_ne_zero 3 hs)).mul hcos
            have hsum := hfirst.add hsecond
            simpa [g2, Function.comp_apply] using hsum.differentiableAt
          have hd2 : DifferentiableAt ℝ (A 2) z :=
            heq2.differentiableAt_iff.mpr hdg2
          simpa using ⟨hd0, hd1, hd2⟩
    | succ r ihr =>
        rcases ihr with ⟨hrel, hdiff⟩
        have hrelNext : ∀ z, |z| < 1 → E (r + 1) z = 0 := by
          intro z hz
          rcases hdiff z hz with ⟨hd0, hd1, hd2⟩
          have hA0 : HasDerivAt (A r) (A (r + 1) z) z := by
            convert hd0.hasDerivAt using 1
            simp [A, iterDeriv_succ_eval]
          have hA1 : HasDerivAt (A (r + 1)) (A (r + 2) z) z := by
            convert hd1.hasDerivAt using 1
            simp [A, iterDeriv_succ_eval]
          have hA2 : HasDerivAt (A (r + 2)) (A (r + 3) z) z := by
            convert hd2.hasDerivAt using 1
            simp [A, iterDeriv_succ_eval]
          have hqD : HasDerivAt (fun w : ℝ => 1 - w ^ 2) (-2 * z) z := by
            convert (hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).pow 2) using 1 <;>
              simp <;> ring
          have hcD := hasDerivAt_const z (2 * (r : ℝ) + 1)
          have hdD := hasDerivAt_const z (m ^ 2 - (r : ℝ) ^ 2)
          have hterm1 := hqD.mul hA2
          have hterm2 := (hcD.mul (hasDerivAt_id z)).mul hA1
          have hterm3 := hdD.mul hA0
          have hED := (hterm1.sub hterm2).add hterm3
          have hopen : IsOpen {w : ℝ | |w| < 1} :=
            isOpen_lt continuous_abs continuous_const
          have hnhds : ∀ᶠ w : ℝ in nhds z, |w| < 1 := hopen.mem_nhds hz
          have heq0 : E r =ᶠ[nhds z] (fun _ : ℝ => 0) := by
            filter_upwards [hnhds] with w hw
            exact hrel w hw
          have hzero : deriv (E r) z = 0 := by
            rw [heq0.deriv_eq]
            simp
          have hraw :
              (-2 * z) * A (r + 2) z +
                  (1 - z ^ 2) * A (r + 3) z -
                ((2 * (r : ℝ) + 1) * A (r + 1) z +
                  (2 * (r : ℝ) + 1) * z * A (r + 2) z) +
                (m ^ 2 - (r : ℝ) ^ 2) * A (r + 1) z = 0 := by
            have hh := hED.deriv
            change deriv (E r) z = _ at hh
            rw [hzero] at hh
            simp at hh
            linarith
          dsimp [E]
          norm_num [Nat.cast_add, Nat.cast_one]
          ring_nf at hraw ⊢
          exact hraw
        constructor
        · exact hrelNext
        · intro z hz
          rcases hdiff z hz with ⟨hd0, hd1, hd2⟩
          have hq : 0 < 1 - z ^ 2 := by
            have hz' := abs_lt.mp hz
            nlinarith [sq_nonneg z]
          have hqne : 1 - z ^ 2 ≠ 0 := ne_of_gt hq
          let c : ℝ := 2 * ((r + 1 : ℕ) : ℝ) + 1
          let d : ℝ := m ^ 2 - ((r + 1 : ℕ) : ℝ) ^ 2
          let B : ℝ → ℝ := fun w =>
            (c * w * A (r + 2) w - d * A (r + 1) w) / (1 - w ^ 2)
          have hdB : DifferentiableAt ℝ B z := by
            dsimp [B]
            fun_prop (disch := assumption)
          have hopen : IsOpen {w : ℝ | |w| < 1} :=
            isOpen_lt continuous_abs continuous_const
          have hnhds : ∀ᶠ w : ℝ in nhds z, |w| < 1 := hopen.mem_nhds hz
          have heq3 : A (r + 3) =ᶠ[nhds z] B := by
            filter_upwards [hnhds] with w hw
            have hqw : 1 - w ^ 2 ≠ 0 := by
              have hw' := abs_lt.mp hw
              nlinarith [sq_nonneg w]
            have hr := hrelNext w hw
            dsimp [E] at hr
            dsimp [B, c, d]
            apply (eq_div_iff hqw).2
            norm_num [Nat.cast_add, Nat.cast_one] at hr ⊢
            linarith
          have hd3 : DifferentiableAt ℝ (A (r + 3)) z :=
            heq3.differentiableAt_iff.mpr hdB
          simpa [Nat.add_assoc] using ⟨hd1, hd2, hd3⟩
  have hn := (hP n).1 0 (by norm_num)
  simpa [E, A] using hn

theorem gap13 (m : ℝ) (k : ℕ) :
    iterDeriv (2 * k) (y m) 0 = iterDeriv (2 * k) (f m) 0 := by
  rfl

theorem gap14 (m : ℝ) (k : ℕ) :
    iterDeriv (2 * k) (f m) 0 = 0 := by
  induction k with
  | zero =>
      simp [iterDeriv, f]
  | succ k ih =>
      have h := gap12 m (2 * k)
      have ihy : iterDeriv (2 * k) (y m) 0 = 0 := by
        rw [gap13 m k]
        exact ih
      rw [ihy] at h
      simp only [mul_zero, add_zero] at h
      rw [← gap13 m (k + 1)]
      simpa [Nat.mul_add] using h

theorem gap15 (m : ℝ) (k : ℕ) :
    iterDeriv (2 * k) (y m) 0 = 0 := by
  rw [gap13]
  exact gap14 m k

theorem gap16 (m : ℝ) (k : ℕ) :
    iterDeriv (2 * k + 1) (y m) 0 = iterDeriv (2 * k + 1) (f m) 0 := by
  rfl

theorem gap17 (m : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k + 1) (f m) 0 =
      -(m ^ 2 - (2 * k - 1 : ℕ) ^ 2) * iterDeriv (2 * k - 1) (y m) 0 := by
  have h := gap12 m (2 * k - 1)
  have hi : 2 * k - 1 + 2 = 2 * k + 1 := by omega
  rw [hi, gap16 m k] at h
  norm_num [Nat.cast_pow] at h ⊢
  linarith

theorem gap18 (m : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    -(m ^ 2 - (2 * k - 1 : ℕ) ^ 2) *
        ((-1 : ℝ) ^ (k - 1) * m * oddProduct m (k - 1)) =
      (-1 : ℝ) ^ k * m * oddProduct m k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hi : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
  rw [hi]
  simp [oddProduct, Finset.prod_range_succ, pow_succ]
  push_cast
  ring

theorem gap19 (m : ℝ) (k : ℕ) :
    (-1 : ℝ) ^ k * m * oddProduct m k =
      (-1 : ℝ) ^ k * m *
        ∏ j ∈ Finset.range k, (m ^ 2 - (2 * j + 1 : ℝ) ^ 2) := by
  rfl

theorem gap20 (m : ℝ) (k : ℕ) :
    iterDeriv (2 * k + 1) (y m) 0 =
      (-1 : ℝ) ^ k * m * oddProduct m k := by
  induction k with
  | zero =>
      simpa [iterDeriv, oddProduct, y] using gap8 m
  | succ k ih =>
      have hk : 1 ≤ k + 1 := by omega
      rw [gap16 m (k + 1)]
      have hr := gap17 m (k + 1) hk
      have hi : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [hi] at hr
      rw [hr, ih]
      have hp := gap18 m (k + 1) hk
      have hprev : k + 1 - 1 = k := by omega
      rw [hprev, hi] at hp
      exact hp

end

end ProofGap.Exercise1221_2
