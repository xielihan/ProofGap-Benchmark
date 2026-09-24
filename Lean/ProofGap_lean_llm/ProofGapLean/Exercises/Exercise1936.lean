import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1936

noncomputable section

def powRat (z : ℝ) (p : ℤ) (n : ℕ) :=
  Real.rpow z ((p : ℝ) / (n : ℝ))
def xOf (a b y : ℝ) := (a - b * y) / (1 - y)
def yOf (n : ℕ) (t : ℝ) := t ^ n
def xBranch (a b : ℝ) : Set ℝ := {x | 0 < x - a ∧ 0 < x - b}
def yBranch (a b : ℝ) : Set ℝ :=
  {y | 0 < y ∧ y ≠ 1 ∧ 0 < (a - b) / (1 - y)}
def tBranch (a b : ℝ) (n : ℕ) : Set ℝ :=
  {t | 0 < t ∧ t ^ n ≠ 1 ∧ 0 < (a - b) / (1 - t ^ n)}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def ElementaryIntegrableOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ F : ℝ → ℝ, ∀ x ∈ s, HasDerivAt F (f x) x
def sourceIntegrand (R : ℝ → ℝ → ℝ) (a b : ℝ)
    (p q : ℤ) (n : ℕ) (x : ℝ) :=
  R x (powRat (x - a) p n * powRat (x - b) q n)
def yParamIntegrand (R : ℝ → ℝ → ℝ) (a b : ℝ)
    (p q k : ℤ) (n : ℕ) (y : ℝ) :=
  R (xOf a b y)
      (powRat y p n * ((a - b) / (1 - y)) ^ k) /
    (1 - y) ^ 2
def YScaledFamily (R : ℝ → ℝ → ℝ) (a b : ℝ)
    (p q k : ℤ) (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (yBranch a b) (yParamIntegrand R a b p q k n),
    ∀ y ∈ yBranch a b, F y = (a - b) * G y}
def tParamIntegrand (R : ℝ → ℝ → ℝ) (a b : ℝ)
    (p k : ℤ) (n : ℕ) (t : ℝ) :=
  R ((a - b * t ^ n) / (1 - t ^ n))
      (t ^ p * ((a - b) / (1 - t ^ n)) ^ k) *
    t ^ (n - 1) / (1 - t ^ n) ^ 2
def TScaledFamily (R : ℝ → ℝ → ℝ) (a b : ℝ)
    (p k : ℤ) (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (tBranch a b n) (tParamIntegrand R a b p k n),
    ∀ t ∈ tBranch a b n, F t = (n : ℝ) * (a - b) * G t}

theorem gap1 (a b x : ℝ) (p q k : ℤ) (n : ℕ) (hn : 0 < n)
    (hsum : p + q = k * (n : ℤ)) (hab : a = b) (hx : 0 < x - a) :
    powRat (x - a) p n * powRat (x - b) q n = (x - a) ^ k := by
  subst b
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hcast : (p : ℝ) + (q : ℝ) = (k : ℝ) * (n : ℝ) := by
    exact_mod_cast hsum
  have hfrac :
      (p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ) = (k : ℝ) := by
    field_simp [hn0]
    linarith
  unfold powRat
  calc
    Real.rpow (x - a) ((p : ℝ) / (n : ℝ)) *
          Real.rpow (x - a) ((q : ℝ) / (n : ℝ)) =
        Real.rpow (x - a)
          ((p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ)) :=
      (Real.rpow_add hx _ _).symm
    _ = Real.rpow (x - a) (k : ℝ) := by rw [hfrac]
    _ = (x - a) ^ k := Real.rpow_intCast _ _
theorem gap2 (R : ℝ → ℝ → ℝ) (a b : ℝ) (p q k : ℤ) (n : ℕ)
    (hn : 0 < n) (hsum : p + q = k * (n : ℤ)) (hab : a = b)
    (hreduced : ElementaryIntegrableOn (xBranch a b)
      (fun x => R x ((x - a) ^ k))) :
    ElementaryIntegrableOn (xBranch a b) (sourceIntegrand R a b p q n) := by
  rcases hreduced with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  intro x hx
  have hxa : 0 < x - a := hx.1
  unfold sourceIntegrand
  rw [gap1 a b x p q k n hn hsum hab hxa]
  exact hF x hx
theorem gap3 (a b y : ℝ) (hab : a ≠ b) (hy : y ∈ yBranch a b) :
    y ≠ 1 := by
  exact hy.2.1
theorem gap4 (a b y : ℝ) (hab : a ≠ b) (hy : y ∈ yBranch a b) :
    xOf a b y = (a - b * y) / (1 - y) := by
  rfl
theorem gap5 (a b y : ℝ) (hab : a ≠ b) (hy : y ∈ yBranch a b) :
    HasDerivAt (xOf a b) ((a - b) / (1 - y) ^ 2) y := by
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.mpr hy.2.1.symm
  unfold xOf
  have hnum : HasDerivAt (fun z : ℝ => a - b * z) (-b) y := by
    convert (hasDerivAt_const y a).sub
      ((hasDerivAt_const y b).mul (hasDerivAt_id y)) using 1 <;>
      simp only [id_eq] <;> ring
  have hden : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      (hasDerivAt_const y 1).sub (hasDerivAt_id y)
  have h := hnum.div hden hy1
  convert h using 1 <;>
    field_simp [hy1] <;>
    ring
theorem gap6 (a b y : ℝ) (hab : a ≠ b) (hy : y ∈ yBranch a b) :
    xOf a b y - a = (a - b) * y / (1 - y) := by
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.mpr hy.2.1.symm
  unfold xOf
  field_simp [hy1]
  ring
theorem gap7 (a b y : ℝ) (hab : a ≠ b) (hy : y ∈ yBranch a b) :
    xOf a b y - b = (a - b) / (1 - y) := by
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.mpr hy.2.1.symm
  unfold xOf
  field_simp [hy1]
  ring

private theorem yBranch_isOpen (a b : ℝ) (hab : a ≠ b) :
    IsOpen (yBranch a b) := by
  rcases lt_trichotomy a b with hablt | heq | hbalt
  · have hset : yBranch a b = Set.Ioi 1 := by
      ext y
      constructor
      · intro hy
        rcases (div_pos_iff.mp hy.2.2) with hpos | hneg
        · linarith
        · exact sub_neg.mp hneg.2
      · intro hy
        change 1 < y at hy
        exact ⟨by linarith, ne_of_gt hy,
          div_pos_of_neg_of_neg (sub_neg.mpr hablt) (sub_neg.mpr hy)⟩
    rw [hset]
    exact isOpen_Ioi
  · exact (hab heq).elim
  · have hset : yBranch a b = Set.Ioo 0 1 := by
      ext y
      constructor
      · intro hy
        refine ⟨hy.1, ?_⟩
        rcases (div_pos_iff.mp hy.2.2) with hpos | hneg
        · linarith
        · linarith
      · intro hy
        rcases hy with ⟨hy0, hy1⟩
        exact ⟨hy0, ne_of_lt hy1,
          div_pos (sub_pos.mpr hbalt) (sub_pos.mpr hy1)⟩
    rw [hset]
    exact isOpen_Ioo

private theorem tBranch_isOpen (a b : ℝ) (n : ℕ) (hab : a ≠ b) :
    IsOpen (tBranch a b n) := by
  rcases lt_trichotomy a b with hablt | heq | hbalt
  · have hset : tBranch a b n = {t : ℝ | 0 < t ∧ 1 < t ^ n} := by
      ext t
      constructor
      · intro ht
        refine ⟨ht.1, ?_⟩
        rcases (div_pos_iff.mp ht.2.2) with hpos | hneg
        · linarith
        · exact sub_neg.mp hneg.2
      · intro ht
        rcases ht with ⟨ht0, ht1⟩
        exact ⟨ht0, ne_of_gt ht1,
          div_pos_of_neg_of_neg (sub_neg.mpr hablt) (sub_neg.mpr ht1)⟩
    rw [hset]
    exact isOpen_Ioi.inter (isOpen_lt continuous_const (continuous_id.pow n))
  · exact (hab heq).elim
  · have hset : tBranch a b n = {t : ℝ | 0 < t ∧ t ^ n < 1} := by
      ext t
      constructor
      · intro ht
        refine ⟨ht.1, ?_⟩
        rcases (div_pos_iff.mp ht.2.2) with hpos | hneg
        · exact sub_pos.mp hpos.2
        · linarith
      · intro ht
        rcases ht with ⟨ht0, ht1⟩
        exact ⟨ht0, ne_of_lt ht1,
          div_pos (sub_pos.mpr hbalt) (sub_pos.mpr ht1)⟩
    rw [hset]
    exact isOpen_Ioi.inter (isOpen_lt (continuous_id.pow n) continuous_const)

private theorem antiderivatives_scale
    {s : Set ℝ} (hopen : IsOpen s) (f g : ℝ → ℝ) (k : ℝ) (hk : k ≠ 0)
    (hfg : ∀ x ∈ s, f x = k * g x) :
    AntiderivativesOn s f =
      {F | ∃ G ∈ AntiderivativesOn s g, ∀ x ∈ s, F x = k * G x} := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => F x / k, ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).div_const k
      convert h using 1
      rw [hfg x hx]
      field_simp [hk]
    · intro x hx
      field_simp [hk]
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => k * G y := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    have h := (hG x hx).const_mul k
    rw [← hfg x hx] at h
    exact h.congr_of_eventuallyEq heq

private theorem powRat_mul_factor (y c : ℝ) (p q k : ℤ) (n : ℕ)
    (hn : 0 < n) (hsum : p + q = k * (n : ℤ))
    (hy : 0 < y) (hc : 0 < c) :
    powRat (y * c) p n * powRat c q n = powRat y p n * c ^ k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hfrac : (p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ) = (k : ℝ) := by
    have hcast : (p : ℝ) + (q : ℝ) = (k : ℝ) * (n : ℝ) := by
      exact_mod_cast hsum
    field_simp [hn0]
    linarith
  unfold powRat
  change (y * c) ^ ((p : ℝ) / (n : ℝ)) * c ^ ((q : ℝ) / (n : ℝ)) =
    y ^ ((p : ℝ) / (n : ℝ)) * c ^ k
  rw [Real.mul_rpow hy.le hc.le]
  calc
    y ^ ((p : ℝ) / (n : ℝ)) * c ^ ((p : ℝ) / (n : ℝ)) *
          c ^ ((q : ℝ) / (n : ℝ)) =
        y ^ ((p : ℝ) / (n : ℝ)) *
          (c ^ ((p : ℝ) / (n : ℝ)) * c ^ ((q : ℝ) / (n : ℝ))) := by ring
    _ = y ^ ((p : ℝ) / (n : ℝ)) *
        c ^ ((p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ)) := by
      rw [Real.rpow_add hc]
    _ = y ^ ((p : ℝ) / (n : ℝ)) * c ^ k := by
      rw [hfrac, Real.rpow_intCast]

private theorem power_product_pos
    (t c : ℝ) (p q k : ℤ) (n : ℕ) (hn : 0 < n)
    (hsum : p + q = k * (n : ℤ)) (ht : 0 < t) (hc : 0 < c) :
    powRat (t ^ n * c) p n * powRat c q n = t ^ p * c ^ k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnp : (n : ℝ) * ((p : ℝ) / (n : ℝ)) = (p : ℝ) := by
    field_simp [hn0]
  have hpq : (p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ) = (k : ℝ) := by
    have hcast : (p : ℝ) + (q : ℝ) = (k : ℝ) * (n : ℝ) := by
      exact_mod_cast hsum
    field_simp [hn0]
    linarith
  unfold powRat
  change (t ^ n * c) ^ ((p : ℝ) / (n : ℝ)) * c ^ ((q : ℝ) / (n : ℝ)) =
    t ^ p * c ^ k
  rw [Real.mul_rpow (pow_nonneg ht.le n) hc.le]
  rw [← Real.rpow_natCast_mul ht.le n ((p : ℝ) / (n : ℝ)), hnp,
    Real.rpow_intCast]
  calc
    t ^ p * c ^ ((p : ℝ) / (n : ℝ)) * c ^ ((q : ℝ) / (n : ℝ)) =
        t ^ p * (c ^ ((p : ℝ) / (n : ℝ)) *
          c ^ ((q : ℝ) / (n : ℝ))) := by ring
    _ = t ^ p * c ^ ((p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ)) := by
      rw [Real.rpow_add hc]
    _ = t ^ p * c ^ k := by rw [hpq, Real.rpow_intCast]
theorem gap8 (R : ℝ → ℝ → ℝ) (a b : ℝ) (p q k : ℤ) (n : ℕ)
    (hn : 0 < n) (hsum : p + q = k * (n : ℤ)) (hab : a ≠ b) :
    AntiderivativesOn (yBranch a b)
        (fun y => sourceIntegrand R a b p q n (xOf a b y) *
          deriv (xOf a b) y) =
      YScaledFamily R a b p q k n := by
  unfold YScaledFamily
  apply antiderivatives_scale (yBranch_isOpen a b hab)
  · exact sub_ne_zero.mpr hab
  · intro y hy
    have hc : 0 < (a - b) / (1 - y) := hy.2.2
    have hxa : xOf a b y - a = y * ((a - b) / (1 - y)) := by
      rw [gap6 a b y hab hy]
      ring
    have hxb : xOf a b y - b = (a - b) / (1 - y) :=
      gap7 a b y hab hy
    unfold sourceIntegrand yParamIntegrand
    rw [(gap5 a b y hab hy).deriv, hxa, hxb]
    rw [powRat_mul_factor y ((a - b) / (1 - y)) p q k n hn hsum hy.1 hc]
    ring
theorem gap9 (a b t : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b)
    (ht : t ∈ tBranch a b n) :
    yOf n t = t ^ n := by
  rfl
theorem gap10 (a b t : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b)
    (ht : t ∈ tBranch a b n) :
    HasDerivAt (yOf n) ((n : ℝ) * t ^ (n - 1)) t := by
  simpa [yOf] using (hasDerivAt_id t).pow n
theorem gap11 (R : ℝ → ℝ → ℝ) (a b : ℝ) (p q k : ℤ) (n : ℕ)
    (hn : 0 < n) (hsum : p + q = k * (n : ℤ)) (hab : a ≠ b) :
    AntiderivativesOn (tBranch a b n)
        (fun t => sourceIntegrand R a b p q n (xOf a b (yOf n t)) *
          deriv (fun u => xOf a b (yOf n u)) t) =
      TScaledFamily R a b p k n := by
  unfold TScaledFamily
  apply antiderivatives_scale (tBranch_isOpen a b n hab)
  · exact mul_ne_zero (by exact_mod_cast hn.ne') (sub_ne_zero.mpr hab)
  · intro t ht
    have hy : yOf n t ∈ yBranch a b := by
      exact ⟨pow_pos ht.1 n, by simpa [yOf] using ht.2.1,
        by simpa [yOf] using ht.2.2⟩
    have hc : 0 < (a - b) / (1 - t ^ n) := ht.2.2
    have hxa : xOf a b (yOf n t) - a =
        t ^ n * ((a - b) / (1 - t ^ n)) := by
      rw [gap6 a b (yOf n t) hab hy]
      simp [yOf]
      ring
    have hxb : xOf a b (yOf n t) - b = (a - b) / (1 - t ^ n) := by
      simpa [yOf] using gap7 a b (yOf n t) hab hy
    have hcomp := (gap5 a b (yOf n t) hab hy).comp t
      (gap10 a b t n hn hab ht)
    have hcomp' : HasDerivAt (fun u => xOf a b (yOf n u))
        ((a - b) / (1 - yOf n t) ^ 2 * ((n : ℝ) * t ^ (n - 1))) t := by
      simpa [Function.comp_def] using hcomp
    have hxform : xOf a b (yOf n t) =
        (a - b * t ^ n) / (1 - t ^ n) := by
      rfl
    unfold sourceIntegrand tParamIntegrand
    rw [hcomp'.deriv, hxa, hxb, hxform]
    rw [power_product_pos t ((a - b) / (1 - t ^ n)) p q k n
      hn hsum ht.1 hc]
    simp [yOf]
    ring

private def yFromX (a b x : ℝ) := (x - a) / (x - b)

private def tFromX (a b : ℝ) (n : ℕ) (x : ℝ) :=
  Real.rpow (yFromX a b x) (1 / (n : ℝ))

private theorem xBranch_isOpen (a b : ℝ) : IsOpen (xBranch a b) := by
  unfold xBranch
  have ha : IsOpen {x : ℝ | 0 < x - a} :=
    isOpen_Ioi.preimage (continuous_id.sub continuous_const)
  have hb : IsOpen {x : ℝ | 0 < x - b} :=
    isOpen_Ioi.preimage (continuous_id.sub continuous_const)
  exact ha.inter hb

private theorem yFromX_pos
    {a b x : ℝ} (hx : x ∈ xBranch a b) :
    0 < yFromX a b x := by
  exact div_pos hx.1 hx.2

private theorem yFromX_ne_one
    {a b x : ℝ} (hab : a ≠ b) (hx : x ∈ xBranch a b) :
    yFromX a b x ≠ 1 := by
  have hxb : x - b ≠ 0 := ne_of_gt hx.2
  intro heq
  unfold yFromX at heq
  have : x - a = x - b := (div_eq_one_iff_eq hxb).mp heq
  apply hab
  linarith

private theorem tFromX_pos
    {a b x : ℝ} {n : ℕ} (hx : x ∈ xBranch a b) :
    0 < tFromX a b n x := by
  exact Real.rpow_pos_of_pos (yFromX_pos hx) _

private theorem tFromX_pow
    {a b x : ℝ} {n : ℕ} (hn : 0 < n) (hx : x ∈ xBranch a b) :
    tFromX a b n x ^ n = yFromX a b x := by
  unfold tFromX
  simpa [one_div] using
    (Real.rpow_inv_natCast_pow (le_of_lt (yFromX_pos hx))
      (ne_of_gt hn))

private theorem tFromX_mem
    {a b x : ℝ} {n : ℕ} (hn : 0 < n) (hab : a ≠ b)
    (hx : x ∈ xBranch a b) :
    tFromX a b n x ∈ tBranch a b n := by
  refine ⟨tFromX_pos hx, ?_, ?_⟩
  · rw [tFromX_pow hn hx]
    exact yFromX_ne_one hab hx
  · rw [tFromX_pow hn hx]
    have hxb : x - b ≠ 0 := ne_of_gt hx.2
    have habsub : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hy1 : 1 - yFromX a b x ≠ 0 :=
      sub_ne_zero.mpr (yFromX_ne_one hab hx).symm
    have heq : (a - b) / (1 - yFromX a b x) = x - b := by
      unfold yFromX
      field_simp [hxb, hy1, habsub]
      ring
    rw [heq]
    exact hx.2

private theorem xOf_yFromX
    {a b x : ℝ} (hab : a ≠ b) (hx : x ∈ xBranch a b) :
    xOf a b (yFromX a b x) = x := by
  have hxb : x - b ≠ 0 := ne_of_gt hx.2
  have hy1 : 1 - yFromX a b x ≠ 0 :=
    sub_ne_zero.mpr (yFromX_ne_one hab hx).symm
  have habsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  unfold xOf yFromX
  field_simp [hxb, hy1, habsub]
  ring

private theorem hasDerivAt_yFromX
    {a b x : ℝ} (hx : x ∈ xBranch a b) :
    HasDerivAt (yFromX a b) ((a - b) / (x - b) ^ 2) x := by
  have hxb : x - b ≠ 0 := ne_of_gt hx.2
  unfold yFromX
  have hnum := (hasDerivAt_id x).sub_const a
  have hden := (hasDerivAt_id x).sub_const b
  convert hnum.div hden hxb using 1 <;>
    simp only [id_eq] <;>
    ring

private theorem hasDerivAt_tFromX
    {a b x : ℝ} {n : ℕ} (hn : 0 < n) (hx : x ∈ xBranch a b) :
    HasDerivAt (tFromX a b n)
      ((1 / (n : ℝ)) *
        (yFromX a b x) ^ ((1 / (n : ℝ)) - 1) *
        ((a - b) / (x - b) ^ 2)) x := by
  have hy0 : yFromX a b x ≠ 0 := ne_of_gt (yFromX_pos hx)
  unfold tFromX
  exact (Real.hasDerivAt_rpow_const
    (p := (1 / (n : ℝ))) (Or.inl hy0)).comp x
      (hasDerivAt_yFromX hx)

private theorem xOf_tFromX
    {a b x : ℝ} {n : ℕ} (hn : 0 < n) (hab : a ≠ b)
    (hx : x ∈ xBranch a b) :
    xOf a b (yOf n (tFromX a b n x)) = x := by
  rw [gap9 a b (tFromX a b n x) n hn hab (tFromX_mem hn hab hx),
    tFromX_pow hn hx]
  exact xOf_yFromX hab hx

private theorem inverse_derivative
    {a b x : ℝ} {n : ℕ} (hn : 0 < n) (hab : a ≠ b)
    (hx : x ∈ xBranch a b) :
    1 =
      ((n : ℝ) * (a - b) * tFromX a b n x ^ (n - 1) /
        (1 - tFromX a b n x ^ n) ^ 2) *
      deriv (tFromX a b n) x := by
  let τ := tFromX a b n x
  have hτmem : τ ∈ tBranch a b n := tFromX_mem hn hab hx
  have hy : yOf n τ ∈ yBranch a b := by
    refine ⟨pow_pos hτmem.1 n, ?_, ?_⟩
    · simpa [yOf] using hτmem.2.1
    · simpa [yOf] using hτmem.2.2
  have houter :=
    (gap5 a b (yOf n τ) hab hy).comp τ
      (gap10 a b τ n hn hab hτmem)
  have hinner := hasDerivAt_tFromX hn hx
  have hcomp := houter.comp x hinner
  have heq :
      (fun z => xOf a b (yOf n (tFromX a b n z))) =ᶠ[nhds x]
        fun z => z := by
    filter_upwards [(xBranch_isOpen a b).mem_nhds hx] with z hz
    exact xOf_tFromX hn hab hz
  have hid := hcomp.congr_of_eventuallyEq heq.symm
  have huniq := hid.unique (hasDerivAt_id x)
  dsimp [τ] at huniq
  rw [(hasDerivAt_tFromX hn hx).deriv]
  simp only [yOf] at huniq
  convert huniq.symm using 1 <;> ring

private theorem x_sub_factor
    {a b x : ℝ} {n : ℕ} (hn : 0 < n) (hx : x ∈ xBranch a b) :
    x - a = tFromX a b n x ^ n * (x - b) := by
  have hxb : x - b ≠ 0 := ne_of_gt hx.2
  rw [tFromX_pow hn hx]
  unfold yFromX
  field_simp [hxb]

private theorem power_product
    (t c : ℝ) (p q k : ℤ) (n : ℕ) (hn : 0 < n)
    (hsum : p + q = k * (n : ℤ)) (ht : 0 < t) (hc : 0 < c) :
    powRat (t ^ n * c) p n * powRat c q n = t ^ p * c ^ k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hcast : (p : ℝ) + (q : ℝ) = (k : ℝ) * (n : ℝ) := by
    exact_mod_cast hsum
  have hnp : (n : ℝ) * ((p : ℝ) / (n : ℝ)) = (p : ℝ) := by
    field_simp [hn0]
  have hpq :
      (p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ) = (k : ℝ) := by
    field_simp [hn0]
    linarith
  unfold powRat
  change
    (t ^ n * c) ^ ((p : ℝ) / (n : ℝ)) *
        c ^ ((q : ℝ) / (n : ℝ)) =
      t ^ p * c ^ k
  rw [Real.mul_rpow (pow_nonneg ht.le n) hc.le]
  rw [← Real.rpow_natCast_mul ht.le n ((p : ℝ) / (n : ℝ)), hnp,
    Real.rpow_intCast]
  calc
    t ^ p * c ^ ((p : ℝ) / (n : ℝ)) *
          c ^ ((q : ℝ) / (n : ℝ)) =
        t ^ p * (c ^ ((p : ℝ) / (n : ℝ)) *
          c ^ ((q : ℝ) / (n : ℝ))) := by ring
    _ = t ^ p *
        c ^ ((p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ)) := by
      rw [Real.rpow_add hc]
    _ = t ^ p * c ^ k := by
      rw [hpq, Real.rpow_intCast]

private theorem source_factor_at_tFromX
    {a b x : ℝ} {p q k : ℤ} {n : ℕ}
    (hn : 0 < n) (hsum : p + q = k * (n : ℤ))
    (hx : x ∈ xBranch a b) :
    powRat (x - a) p n * powRat (x - b) q n =
      tFromX a b n x ^ p * (x - b) ^ k := by
  rw [x_sub_factor hn hx]
  exact power_product _ _ p q k n hn hsum (tFromX_pos hx) hx.2
theorem gap12 (R : ℝ → ℝ → ℝ) (a b : ℝ) (p q k : ℤ) (n : ℕ)
    (hn : 0 < n) (hsum : p + q = k * (n : ℤ)) (hab : a ≠ b)
    (htransformed : ElementaryIntegrableOn (tBranch a b n)
      (tParamIntegrand R a b p k n)) :
    ElementaryIntegrableOn (xBranch a b) (sourceIntegrand R a b p q n) := by
  rcases htransformed with ⟨G, hG⟩
  let H : ℝ → ℝ := fun x =>
    (n : ℝ) * (a - b) * G (tFromX a b n x)
  refine ⟨H, ?_⟩
  intro x hx
  let τ := tFromX a b n x
  have hτmem : τ ∈ tBranch a b n := tFromX_mem hn hab hx
  have hφ := hasDerivAt_tFromX hn hx
  have hGφ := (hG τ hτmem).comp x hφ
  have hH := hGφ.const_mul ((n : ℝ) * (a - b))
  have hxrec : (a - b * τ ^ n) / (1 - τ ^ n) = x := by
    change xOf a b (yOf n τ) = x
    exact xOf_tFromX hn hab hx
  have hy : τ ^ n ∈ yBranch a b := by
    exact ⟨pow_pos hτmem.1 n, hτmem.2.1, hτmem.2.2⟩
  have hc :
      (a - b) / (1 - τ ^ n) = x - b := by
    have h := gap7 a b (τ ^ n) hab hy
    rw [show xOf a b (τ ^ n) = x by
      simpa [yOf] using xOf_tFromX hn hab hx] at h
    linarith
  have hfactor := source_factor_at_tFromX
    (p := p) (q := q) (k := k) hn hsum hx
  have hinv := inverse_derivative hn hab hx
  unfold H
  convert hH using 1
  unfold tParamIntegrand sourceIntegrand
  dsimp [τ] at hxrec hc hfactor hinv ⊢
  rw [← hφ.deriv]
  rw [hxrec, hc, hfactor]
  let V := R x (tFromX a b n x ^ p * (x - b) ^ k)
  have hscale :
      (n : ℝ) * (a - b) *
          (V * tFromX a b n x ^ (n - 1) /
            (1 - tFromX a b n x ^ n) ^ 2 *
            deriv (tFromX a b n) x) = V := by
    calc
      (n : ℝ) * (a - b) *
          (V * tFromX a b n x ^ (n - 1) /
            (1 - tFromX a b n x ^ n) ^ 2 *
            deriv (tFromX a b n) x) =
        V * (((n : ℝ) * (a - b) * tFromX a b n x ^ (n - 1) /
          (1 - tFromX a b n x ^ n) ^ 2) *
          deriv (tFromX a b n) x) := by ring
      _ = V * 1 := by rw [← hinv]
      _ = V := by ring
  exact hscale.symm
theorem gap13 (R : ℝ → ℝ → ℝ) (a b : ℝ) (p q k : ℤ) (n : ℕ)
    (hn : 0 < n) (hsum : p + q = k * (n : ℤ))
    (hsame : a = b → ElementaryIntegrableOn (xBranch a b)
      (fun x => R x ((x - a) ^ k)))
    (hdistinct : a ≠ b → ElementaryIntegrableOn (tBranch a b n)
      (tParamIntegrand R a b p k n)) :
    ElementaryIntegrableOn (xBranch a b) (sourceIntegrand R a b p q n) := by
  by_cases hab : a = b
  · exact gap2 R a b p q k n hn hsum hab (hsame hab)
  · exact gap12 R a b p q k n hn hsum hab (hdistinct hab)

end
end ProofGap.Exercise1936
