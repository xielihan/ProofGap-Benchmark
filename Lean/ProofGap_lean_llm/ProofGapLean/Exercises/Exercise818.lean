import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Arcosh

namespace ProofGap.Exercise818

noncomputable section

def DAlambert (f : ℝ → ℝ) : Prop :=
  ∀ x y, f (x + y) + f (x - y) = 2 * f x * f y

def Classified (f : ℝ → ℝ) : Prop :=
  f = (fun _ => 0) ∨
  (∃ a : ℝ, f = fun x => Real.cos (a * x)) ∨
  ∃ a : ℝ, f = fun x => Real.cosh (a * x)

/-- Source: `proof_gap/exercise_818/1.txt`. -/
theorem gap1 (a : ℝ) : DAlambert (fun x => Real.cos (a * x)) := by
  intro x y
  dsimp
  rw [show a * (x + y) = a * x + a * y by ring,
      show a * (x - y) = a * x - a * y by ring,
      Real.cos_add, Real.cos_sub]
  ring

/-- Source: `proof_gap/exercise_818/2.txt`. -/
theorem gap2 (a : ℝ) : DAlambert (fun x => Real.cosh (a * x)) := by
  intro x y
  dsimp
  rw [show a * (x + y) = a * x + a * y by ring,
      show a * (x - y) = a * x - a * y by ring,
      Real.cosh_add, Real.cosh_sub]
  ring

/-- Source: `proof_gap/exercise_818/3.txt`. -/
theorem gap3 (f : ℝ → ℝ) (hfun : DAlambert f) :
    ∀ x, 2 * f x = 2 * f x * f 0 := by
  intro x
  have h := hfun x 0
  simpa only [add_zero, sub_zero, two_mul] using h

/-- Source: `proof_gap/exercise_818/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (hfun : DAlambert f) (hnz : ¬ ∀ x, f x = 0) :
    f 0 = 1 := by
  by_contra hne
  apply hnz
  intro x
  have h := gap3 f hfun x
  have hp : f x * (2 - 2 * f 0) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hp with hx | hx
  · exact hx
  · exfalso
    apply hne
    linarith

/-- Source: `proof_gap/exercise_818/5.txt`. -/
theorem gap5 (f : ℝ → ℝ) (hfun : DAlambert f) (h0 : f 0 = 1) :
    ∀ y, f y + f (-y) = 2 * f y := by
  intro y
  simpa [h0] using hfun 0 y

/-- Source: `proof_gap/exercise_818/6.txt`. -/
theorem gap6 (f : ℝ → ℝ) (hfun : DAlambert f) (h0 : f 0 = 1) :
    ∀ y, f (-y) = f y := by
  intro y
  have h := gap5 f hfun h0 y
  linarith

/-- Source: `proof_gap/exercise_818/7.txt`; restrict continuity to the source's full real domain. -/
theorem gap7 (f : ℝ → ℝ) (hf : Continuous f) (h0 : f 0 = 1) :
    ∃ c > 0, ∀ x ∈ Set.Icc (0 : ℝ) c, 0 < f x := by
  have hopen : IsOpen (f ⁻¹' Set.Ioi (0 : ℝ)) := isOpen_Ioi.preimage hf
  have hmem : (0 : ℝ) ∈ f ⁻¹' Set.Ioi (0 : ℝ) := by
    simp [h0]
  rcases Metric.isOpen_iff.mp hopen 0 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε / 2, by positivity, ?_⟩
  intro x hx
  have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    linarith [hx.2]
  exact hball hxball

/-- Source: `proof_gap/exercise_818/8.txt`; define `θ` as `arccos A`. -/
theorem gap8 (A : ℝ) (hA0 : 0 < A) (hA1 : A ≤ 1) :
    0 ≤ Real.arccos A := by
  exact Real.arccos_nonneg A

/-- Source: `proof_gap/exercise_818/9.txt`; define `θ` as `arccos A`. -/
theorem gap9 (A : ℝ) (hA0 : 0 < A) (hA1 : A ≤ 1) :
    Real.arccos A < Real.pi / 2 := by
  exact Real.arccos_lt_pi_div_two.mpr hA0

/-- Source: `proof_gap/exercise_818/10.txt`. -/
theorem gap10 : 0 < Real.pi / 2 := by
  positivity

/-- Source: `proof_gap/exercise_818/11.txt`; add the omitted definitions `f(c)=A`, `θ=arccos A`. -/
theorem gap11 (f : ℝ → ℝ) (c A θ : ℝ)
    (hfc : f c = A) (hθ : θ = Real.arccos A) (hA0 : 0 < A) (hA1 : A ≤ 1) :
    f c = Real.cos θ := by
  rw [hfc, hθ, Real.cos_arccos (by linarith) hA1]

/-- Source: `proof_gap/exercise_818/12.txt`. -/
theorem gap12 (f : ℝ → ℝ) (c : ℝ) (hfun : DAlambert f) :
    f (2 * c) = 2 * f c ^ 2 - f 0 := by
  have h := hfun c c
  rw [show c + c = 2 * c by ring, sub_self] at h
  nlinarith [h]

/-- Source: `proof_gap/exercise_818/13.txt`. -/
theorem gap13 (f : ℝ → ℝ) (c θ : ℝ) (h0 : f 0 = 1)
    (hc : f c = Real.cos θ) :
    2 * f c ^ 2 - f 0 = 2 * Real.cos θ ^ 2 - 1 := by
  simp [h0, hc]

/-- Source: `proof_gap/exercise_818/14.txt`. -/
theorem gap14 (θ : ℝ) : 2 * Real.cos θ ^ 2 - 1 = Real.cos (2 * θ) := by
  simpa using (Real.cos_two_mul θ).symm

/-- Source: `proof_gap/exercise_818/15.txt`. -/
theorem gap15 (f : ℝ → ℝ) (c θ : ℝ) (hfun : DAlambert f)
    (h0 : f 0 = 1) (hc : f c = Real.cos θ) :
    f (2 * c) = Real.cos (2 * θ) := by
  calc
    f (2 * c) = 2 * f c ^ 2 - f 0 := gap12 f c hfun
    _ = 2 * Real.cos θ ^ 2 - 1 := gap13 f c θ h0 hc
    _ = Real.cos (2 * θ) := gap14 θ

/-- Source: `proof_gap/exercise_818/16.txt`. -/
theorem gap16 (f : ℝ → ℝ) (c : ℝ) (hfun : DAlambert f) :
    f (3 * c) = 2 * f (2 * c) * f c - f c := by
  have h := hfun (2 * c) c
  rw [show 2 * c + c = 3 * c by ring,
      show 2 * c - c = c by ring] at h
  linarith

/-- Source: `proof_gap/exercise_818/17.txt`. -/
theorem gap17 (f : ℝ → ℝ) (c θ : ℝ)
    (hc : f c = Real.cos θ) (h2c : f (2 * c) = Real.cos (2 * θ)) :
    2 * f (2 * c) * f c - f c =
      2 * Real.cos (2 * θ) * Real.cos θ - Real.cos θ := by
  simp [hc, h2c]

/-- Source: `proof_gap/exercise_818/18.txt`. -/
theorem gap18 (θ : ℝ) :
    2 * Real.cos (2 * θ) * Real.cos θ - Real.cos θ = Real.cos (3 * θ) := by
  have h := (gap1 (1 : ℝ)) (2 * θ) θ
  rw [show 2 * θ + θ = 3 * θ by ring,
      show 2 * θ - θ = θ by ring] at h
  norm_num only [one_mul] at h
  linarith

/-- Source: `proof_gap/exercise_818/19.txt`. -/
theorem gap19 (f : ℝ → ℝ) (c θ : ℝ) (hfun : DAlambert f)
    (h0 : f 0 = 1) (hc : f c = Real.cos θ) :
    f (3 * c) = Real.cos (3 * θ) := by
  calc
    f (3 * c) = 2 * f (2 * c) * f c - f c := gap16 f c hfun
    _ = 2 * Real.cos (2 * θ) * Real.cos θ - Real.cos θ :=
      gap17 f c θ hc (gap15 f c θ hfun h0 hc)
    _ = Real.cos (3 * θ) := gap18 θ

/-- Source: `proof_gap/exercise_818/20.txt`; type positive indices as naturals. -/
theorem gap20 (f : ℝ → ℝ) (c θ : ℝ) (hfun : DAlambert f)
    (h0 : f 0 = 1) (hc : f c = Real.cos θ) :
    ∀ n : ℕ, 1 ≤ n → f ((n : ℝ) * c) = Real.cos ((n : ℝ) * θ) := by
  have hall : ∀ n : ℕ, f ((n : ℝ) * c) = Real.cos ((n : ℝ) * θ) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [h0]
    | one => simpa using hc
    | more n ih0 ih1 =>
        have hfc := hfun (((n + 1 : ℕ) : ℝ) * c) c
        rw [show (((n + 1 : ℕ) : ℝ) * c) + c = ((n + 2 : ℕ) : ℝ) * c by
              norm_num [Nat.cast_add] <;> ring,
            show (((n + 1 : ℕ) : ℝ) * c) - c = (n : ℝ) * c by
              norm_num [Nat.cast_add] <;> ring] at hfc
        have hcos := (gap1 (1 : ℝ)) (((n + 1 : ℕ) : ℝ) * θ) θ
        rw [show (((n + 1 : ℕ) : ℝ) * θ) + θ = ((n + 2 : ℕ) : ℝ) * θ by
              norm_num [Nat.cast_add] <;> ring,
            show (((n + 1 : ℕ) : ℝ) * θ) - θ = (n : ℝ) * θ by
              norm_num [Nat.cast_add] <;> ring] at hcos
        norm_num only [one_mul] at hcos
        rw [ih0, ih1, hc] at hfc
        linarith
  intro n hn
  exact hall n

/-- Source: `proof_gap/exercise_818/21.txt`. -/
theorem gap21 (f : ℝ → ℝ) (c : ℝ) (hfun : DAlambert f) :
    f ((1 / 2 : ℝ) * c) ^ 2 = (1 / 2 : ℝ) * (f 0 + f c) := by
  have h := hfun ((1 / 2 : ℝ) * c) ((1 / 2 : ℝ) * c)
  rw [show (1 / 2 : ℝ) * c + (1 / 2 : ℝ) * c = c by ring,
      show (1 / 2 : ℝ) * c - (1 / 2 : ℝ) * c = 0 by ring] at h
  nlinarith [h]

/-- Source: `proof_gap/exercise_818/22.txt`. -/
theorem gap22 (f : ℝ → ℝ) (c θ : ℝ) (h0 : f 0 = 1)
    (hc : f c = Real.cos θ) :
    (1 / 2 : ℝ) * (f 0 + f c) = (1 / 2 : ℝ) * (1 + Real.cos θ) := by
  simp [h0, hc]

/-- Source: `proof_gap/exercise_818/23.txt`. -/
theorem gap23 (θ : ℝ) :
    (1 / 2 : ℝ) * (1 + Real.cos θ) = Real.cos (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  nlinarith [h]

/-- Source: `proof_gap/exercise_818/24.txt`. -/
theorem gap24 (f : ℝ → ℝ) (c θ : ℝ) (hfun : DAlambert f)
    (h0 : f 0 = 1) (hc : f c = Real.cos θ) :
    f ((1 / 2 : ℝ) * c) ^ 2 = Real.cos (θ / 2) ^ 2 := by
  calc
    f ((1 / 2 : ℝ) * c) ^ 2 = (1 / 2 : ℝ) * (f 0 + f c) := gap21 f c hfun
    _ = (1 / 2 : ℝ) * (1 + Real.cos θ) := gap22 f c θ h0 hc
    _ = Real.cos (θ / 2) ^ 2 := gap23 θ

/-- Source: `proof_gap/exercise_818/25.txt`; add the omitted positivity selecting the square root. -/
theorem gap25 (f : ℝ → ℝ) (c θ : ℝ)
    (hsq : f ((1 / 2 : ℝ) * c) ^ 2 = Real.cos (θ / 2) ^ 2)
    (hfpos : 0 ≤ f ((1 / 2 : ℝ) * c)) (hcospos : 0 ≤ Real.cos (θ / 2)) :
    f ((1 / 2 : ℝ) * c) = Real.cos (θ / 2) := by
  nlinarith

/-- Source: `proof_gap/exercise_818/26.txt`; type the index as a natural. -/
theorem gap26 (f : ℝ → ℝ) (c θ : ℝ) (hfun : DAlambert f)
    (h0 : f 0 = 1) (hc : f c = Real.cos θ)
    (hfpos : ∀ n : ℕ, 0 ≤ f (c / (2 : ℝ) ^ n))
    (hcospos : ∀ n : ℕ, 0 ≤ Real.cos (θ / (2 : ℝ) ^ n)) :
    ∀ n : ℕ, f (c / (2 : ℝ) ^ n) = Real.cos (θ / (2 : ℝ) ^ n) := by
  intro n
  induction n with
  | zero => simpa using hc
  | succ n ih =>
      have hsq := gap24 f (c / (2 : ℝ) ^ n) (θ / (2 : ℝ) ^ n)
        hfun h0 ih
      have hhalf := gap25 f (c / (2 : ℝ) ^ n) (θ / (2 : ℝ) ^ n)
        hsq (by
          convert hfpos (n + 1) using 1 <;>
            simp only [pow_succ] <;> ring)
        (by
          convert hcospos (n + 1) using 1 <;>
            simp only [pow_succ] <;> ring)
      convert hhalf using 1 <;>
        simp only [pow_succ] <;> ring

/-- Source: `proof_gap/exercise_818/27.txt`; type both indices as naturals. -/
theorem gap27 (f : ℝ → ℝ) (c θ : ℝ) (hfun : DAlambert f)
    (h0 : f 0 = 1) (hdyadic : ∀ n : ℕ,
    f (c / (2 : ℝ) ^ n) = Real.cos (θ / (2 : ℝ) ^ n)) :
    ∀ m n : ℕ,
      f ((m : ℝ) * c / (2 : ℝ) ^ n) =
        Real.cos ((m : ℝ) * θ / (2 : ℝ) ^ n) := by
  intro m n
  by_cases hm : m = 0
  · subst m
    simp [h0]
  · have hmul := gap20 f (c / (2 : ℝ) ^ n) (θ / (2 : ℝ) ^ n)
        hfun h0 (hdyadic n) m (Nat.one_le_iff_ne_zero.mpr hm)
    convert hmul using 1 <;> ring

/-- Source: `proof_gap/exercise_818/28.txt`; bind the intended dyadic approximating sequence. -/
theorem gap28 (f : ℝ → ℝ) (c θ : ℝ) (q : ℕ → ℝ)
    (hq : ∀ n, ∃ m k : ℕ, q n = (m : ℝ) / (2 : ℝ) ^ k)
    (hdyadic : ∀ m k : ℕ,
      f ((m : ℝ) * c / (2 : ℝ) ^ k) =
        Real.cos ((m : ℝ) * θ / (2 : ℝ) ^ k)) :
    ∀ n, f (c * q n) = Real.cos (θ * q n) := by
  intro n
  rcases hq n with ⟨m, k, hqmk⟩
  have hx : c * q n = (m : ℝ) * c / (2 : ℝ) ^ k := by
    rw [hqmk]
    ring
  have hy : θ * q n = (m : ℝ) * θ / (2 : ℝ) ^ k := by
    rw [hqmk]
    ring
  rw [hx, hy]
  exact hdyadic m k

/-- Source: `proof_gap/exercise_818/29.txt`; add convergence of the dyadic approximants and continuity. -/
theorem gap29 (f : ℝ → ℝ) (c θ x : ℝ) (q : ℕ → ℝ)
    (hf : Continuous f) (hq : Filter.Tendsto q Filter.atTop (nhds x))
    (hvals : ∀ n, f (c * q n) = Real.cos (θ * q n)) :
    f (c * x) = Real.cos (θ * x) := by
  have hleft_cont : Continuous (fun t : ℝ => f (c * t)) :=
    hf.comp (continuous_const.mul continuous_id)
  have hright_cont : Continuous (fun t : ℝ => Real.cos (θ * t)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hleft := (hleft_cont.tendsto x).comp hq
  have hright := (hright_cont.tendsto x).comp hq
  change Filter.Tendsto (fun n => f (c * q n)) Filter.atTop
      (nhds (f (c * x))) at hleft
  change Filter.Tendsto (fun n => Real.cos (θ * q n)) Filter.atTop
      (nhds (Real.cos (θ * x))) at hright
  have heq : (fun n => f (c * q n)) = fun n => Real.cos (θ * q n) := by
    funext n
    exact hvals n
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Source: `proof_gap/exercise_818/30.txt`. -/
theorem gap30 (f : ℝ → ℝ) (c θ : ℝ)
    (hscaled : ∀ x, f (c * x) = Real.cos (θ * x)) :
    ∀ x, f (c * x) = Real.cos (θ * x) := by
  exact hscaled

/-- Source: `proof_gap/exercise_818/31.txt`; define `a=θ/c` and require `c≠0`. -/
theorem gap31 (f : ℝ → ℝ) (c θ : ℝ) (hc : c ≠ 0)
    (hscaled : ∀ x, f (c * x) = Real.cos (θ * x)) :
    ∀ x, f x = Real.cos ((θ / c) * x) := by
  intro x
  have hcx : c * (x / c) = x := by
    field_simp [hc]
  have harg : θ * (x / c) = (θ / c) * x := by
    ring
  calc
    f x = f (c * (x / c)) := by rw [hcx]
    _ = Real.cos (θ * (x / c)) := hscaled (x / c)
    _ = Real.cos ((θ / c) * x) := by rw [harg]

/-- Source: `proof_gap/exercise_818/32.txt`. -/
theorem gap32 (f : ℝ → ℝ) (c A : ℝ) (hfc : f c = A) (hA : 1 < A) :
    f c = A := by
  exact hfc

/-- Source: `proof_gap/exercise_818/33.txt`; define `θ` as `arcosh A`. -/
theorem gap33 (A : ℝ) (hA : 1 < A) : A = Real.cosh (Real.arcosh A) := by
  exact (Real.cosh_arcosh (by linarith)).symm

/-- Source: `proof_gap/exercise_818/34.txt`; add the omitted definitions. -/
theorem gap34 (f : ℝ → ℝ) (c A θ : ℝ) (hfc : f c = A)
    (hθ : θ = Real.arcosh A) (hA : 1 < A) :
    f c = Real.cosh θ := by
  simpa [hfc, hθ] using gap33 A hA

/-- Source: `proof_gap/exercise_818/35.txt`; bind the scale `a`. -/
theorem gap35 (f : ℝ → ℝ) (a : ℝ)
    (hform : ∀ x, f x = Real.cosh (a * x)) :
    ∀ x, f x = Real.cosh (a * x) := by
  exact hform

/-- Source: `proof_gap/exercise_818/36.txt`; preserve the source's constant-one branch. -/
theorem gap36 (f : ℝ → ℝ) (hbranch : ∀ x, f x = 1) :
    ∀ x, f x = 1 := by
  exact hbranch

private theorem one_le_two_pow (n : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
  exact_mod_cast Nat.one_le_pow n 2 (by norm_num)

private theorem dyadic_point_mem (c : ℝ) (hc : 0 < c) (n : ℕ) :
    c / (2 : ℝ) ^ n ∈ Set.Icc (0 : ℝ) c := by
  exact ⟨div_nonneg hc.le (by positivity),
    div_le_self hc.le (one_le_two_pow n)⟩

private theorem nonnegative_dyadic_approximation (x : ℝ) (hx : 0 ≤ x) :
    ∃ q : ℕ → ℝ,
      Filter.Tendsto q Filter.atTop (nhds x) ∧
      ∀ n, ∃ m : ℕ, q n = (m : ℝ) / (2 : ℝ) ^ n := by
  let q : ℕ → ℝ :=
    fun n => (Nat.floor (x * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n
  refine ⟨q, ?_, ?_⟩
  · have hpow :
        Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n)
          Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hfloor :=
      (tendsto_nat_floor_mul_div_atTop (R := ℝ) hx).comp hpow
    simpa [q, Function.comp_def] using hfloor
  · intro n
    exact ⟨Nat.floor (x * (2 : ℝ) ^ n), rfl⟩

private theorem even_of_dalembert (g : ℝ → ℝ) (hfun : DAlambert g)
    (h0 : g 0 = 1) :
    ∀ x, g (-x) = g x := by
  intro x
  have h := hfun 0 x
  simp [h0] at h
  linarith

private theorem model_dyadic_agreement (f g : ℝ → ℝ) (c : ℝ)
    (hfun : DAlambert f) (hgun : DAlambert g)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1) (hbase : f c = g c)
    (hfpos : ∀ n : ℕ, 0 ≤ f (c / (2 : ℝ) ^ n))
    (hgpos : ∀ n : ℕ, 0 ≤ g (c / (2 : ℝ) ^ n)) :
    ∀ n : ℕ, f (c / (2 : ℝ) ^ n) = g (c / (2 : ℝ) ^ n) := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
      let z := c / (2 : ℝ) ^ (n + 1)
      have hsum : z + z = c / (2 : ℝ) ^ n := by
        dsimp [z]
        simp only [pow_succ]
        ring
      have hfrec := hfun z z
      have hgrec := hgun z z
      rw [hsum, sub_self, hf0, ih] at hfrec
      rw [hsum, sub_self, hg0] at hgrec
      change f z = g z
      nlinarith [hfpos (n + 1), hgpos (n + 1)]

private theorem model_natural_agreement (f g : ℝ → ℝ) (c : ℝ)
    (hfun : DAlambert f) (hgun : DAlambert g)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1) (hbase : f c = g c) :
    ∀ n : ℕ, f ((n : ℝ) * c) = g ((n : ℝ) * c) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [hf0, hg0]
  | one => simpa using hbase
  | more n ih0 ih1 =>
      have hfrec := hfun (((n + 1 : ℕ) : ℝ) * c) c
      have hgrec := hgun (((n + 1 : ℕ) : ℝ) * c) c
      rw [show (((n + 1 : ℕ) : ℝ) * c) + c =
            ((n + 2 : ℕ) : ℝ) * c by
              norm_num [Nat.cast_add] <;> ring,
          show (((n + 1 : ℕ) : ℝ) * c) - c =
            (n : ℝ) * c by
              norm_num [Nat.cast_add] <;> ring] at hfrec hgrec
      rw [ih0, ih1, hbase] at hfrec
      linarith

private theorem model_ext (f g : ℝ → ℝ) (c : ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfun : DAlambert f) (hgun : DAlambert g)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1) (hc : 0 < c)
    (hdyadic : ∀ n : ℕ,
      f (c / (2 : ℝ) ^ n) = g (c / (2 : ℝ) ^ n)) :
    f = g := by
  have hmult : ∀ m n : ℕ,
      f ((m : ℝ) * c / (2 : ℝ) ^ n) =
        g ((m : ℝ) * c / (2 : ℝ) ^ n) := by
    intro m n
    have h := model_natural_agreement f g (c / (2 : ℝ) ^ n)
      hfun hgun hf0 hg0 (hdyadic n) m
    convert h using 1 <;> ring
  have hnonneg : ∀ x : ℝ, 0 ≤ x → f x = g x := by
    intro x hx
    let t := x / c
    have ht : 0 ≤ t := div_nonneg hx hc.le
    obtain ⟨q, hq, hqform⟩ := nonnegative_dyadic_approximation t ht
    have hvals : ∀ n, f (c * q n) = g (c * q n) := by
      intro n
      obtain ⟨m, hm⟩ := hqform n
      rw [hm]
      convert hmult m n using 1 <;> ring
    have hleft :
        Filter.Tendsto (fun n : ℕ => f (c * q n))
          Filter.atTop (nhds (f (c * t))) :=
      ((hf.comp (continuous_const.mul continuous_id)).tendsto t).comp hq
    have hright :
        Filter.Tendsto (fun n : ℕ => g (c * q n))
          Filter.atTop (nhds (g (c * t))) :=
      ((hg.comp (continuous_const.mul continuous_id)).tendsto t).comp hq
    have heq :
        (fun n : ℕ => f (c * q n)) = fun n : ℕ => g (c * q n) := by
      funext n
      exact hvals n
    rw [heq] at hleft
    have hlimit : f (c * t) = g (c * t) :=
      tendsto_nhds_unique hleft hright
    have hct : c * t = x := by
      dsimp [t]
      field_simp [hc.ne']
    rw [hct] at hlimit
    exact hlimit
  have hfeven := even_of_dalembert f hfun hf0
  have hgeven := even_of_dalembert g hgun hg0
  funext x
  by_cases hx : 0 ≤ x
  · exact hnonneg x hx
  · have hnx : 0 ≤ -x := by linarith
    calc
      f x = f (-x) := (hfeven x).symm
      _ = g (-x) := hnonneg (-x) hnx
      _ = g x := hgeven x

/-- Source: `proof_gap/exercise_818/37.txt`; quantify the scale and include the omitted zero solution. -/
theorem gap37 (f : ℝ → ℝ) :
    Classified f ↔ Continuous f ∧ DAlambert f := by
  constructor
  · rintro (rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨continuous_const, by intro x y; ring⟩
    · exact ⟨Real.continuous_cos.comp (continuous_const.mul continuous_id), gap1 a⟩
    · exact ⟨Real.continuous_cosh.comp (continuous_const.mul continuous_id), gap2 a⟩
  · rintro ⟨hf, hfun⟩
    by_cases hz : ∀ x, f x = 0
    · exact Or.inl (funext hz)
    · have h0 : f 0 = 1 := gap4 f hfun hz
      obtain ⟨c, hc, hpos⟩ := gap7 f hf h0
      have hfpos : ∀ n : ℕ, 0 ≤ f (c / (2 : ℝ) ^ n) := by
        intro n
        exact (hpos _ (dyadic_point_mem c hc n)).le
      by_cases hA : f c ≤ 1
      · let θ := Real.arccos (f c)
        let g : ℝ → ℝ := fun x => Real.cos ((θ / c) * x)
        have hfcpos : 0 < f c := hpos c ⟨hc.le, le_rfl⟩
        have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
        have hθle : θ ≤ Real.pi / 2 :=
          Real.arccos_le_pi_div_two.mpr hfcpos.le
        have hg : Continuous g :=
          Real.continuous_cos.comp (continuous_const.mul continuous_id)
        have hgun : DAlambert g := gap1 (θ / c)
        have hg0 : g 0 = 1 := by simp [g]
        have hbase : f c = g c := by
          have harg : (θ / c) * c = θ := by field_simp [hc.ne']
          change f c = Real.cos ((θ / c) * c)
          rw [harg]
          dsimp [θ]
          rw [Real.cos_arccos (by linarith) hA]
        have hgpos : ∀ n : ℕ, 0 ≤ g (c / (2 : ℝ) ^ n) := by
          intro n
          have harg :
              (θ / c) * (c / (2 : ℝ) ^ n) =
                θ / (2 : ℝ) ^ n := by
            field_simp [hc.ne']
          rw [show g (c / (2 : ℝ) ^ n) =
              Real.cos (θ / (2 : ℝ) ^ n) by simp [g, harg]]
          apply Real.cos_nonneg_of_mem_Icc
          constructor
          · have hden : 0 < (2 : ℝ) ^ n := by positivity
            exact (neg_nonpos.mpr (Real.pi_div_two_pos.le)).trans
              (div_nonneg hθ0 hden.le)
          · exact (div_le_self hθ0 (one_le_two_pow n)).trans hθle
        have hdyadic := model_dyadic_agreement f g c hfun hgun h0 hg0
          hbase hfpos hgpos
        have hfg : f = g :=
          model_ext f g c hf hg hfun hgun h0 hg0 hc hdyadic
        exact Or.inr (Or.inl ⟨θ / c, hfg⟩)
      · have hA' : 1 < f c := lt_of_not_ge hA
        let θ := Real.arcosh (f c)
        let g : ℝ → ℝ := fun x => Real.cosh ((θ / c) * x)
        have hg : Continuous g :=
          Real.continuous_cosh.comp (continuous_const.mul continuous_id)
        have hgun : DAlambert g := gap2 (θ / c)
        have hg0 : g 0 = 1 := by simp [g]
        have hbase : f c = g c := by
          have harg : (θ / c) * c = θ := by field_simp [hc.ne']
          simp [g, harg, θ, Real.cosh_arcosh hA'.le]
        have hgpos : ∀ n : ℕ, 0 ≤ g (c / (2 : ℝ) ^ n) := by
          intro n
          exact (Real.cosh_pos _).le
        have hdyadic := model_dyadic_agreement f g c hfun hgun h0 hg0
          hbase hfpos hgpos
        have hfg : f = g :=
          model_ext f g c hf hg hfun hgun h0 hg0 hc hdyadic
        exact Or.inr (Or.inr ⟨θ / c, hfg⟩)

end

end ProofGap.Exercise818
