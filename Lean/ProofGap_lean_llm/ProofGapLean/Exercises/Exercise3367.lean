import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3367

noncomputable section

abbrev UnitInterval :=
  {x : ℝ // x ∈ Set.Icc (-1 : ℝ) 1}

def curvePolynomial (x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) ^ 2 - x ^ 2 + y ^ 2

def CurveEquation (x y : ℝ) : Prop :=
  curvePolynomial x y = 0

def discriminantRoot (x : ℝ) : ℝ :=
  Real.sqrt (8 * x ^ 2 + 1)

def squareProfile (x : ℝ) : ℝ :=
  (discriminantRoot x - (1 + 2 * x ^ 2)) / 2

def baseBranch (x : UnitInterval) : ℝ :=
  Real.sqrt (squareProfile x)

def negBaseBranch (x : UnitInterval) : ℝ :=
  -baseBranch x

def signBranch (x : UnitInterval) : ℝ :=
  Real.sign (x : ℝ) * baseBranch x

def negSignBranch (x : UnitInterval) : ℝ :=
  -Real.sign (x : ℝ) * baseBranch x

def IsContinuousBranch (y : UnitInterval → ℝ) : Prop :=
  Continuous y ∧ ∀ x : UnitInterval, CurveEquation x (y x)

def continuousBranches : Set (UnitInterval → ℝ) :=
  {y | IsContinuousBranch y}

def partialY (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => F x t) y

def criticalPoints : Set (ℝ × ℝ) :=
  {p | CurveEquation p.1 p.2 ∧
    partialY curvePolynomial p.1 p.2 = 0}

theorem gap1 (x y : ℝ) (hcurve : CurveEquation x y) :
    y ^ 2 = squareProfile x := by
  unfold CurveEquation curvePolynomial at hcurve
  unfold squareProfile discriminantRoot
  have hD : 0 ≤ 8 * x ^ 2 + 1 := by positivity
  have hsqrt := Real.sq_sqrt hD
  have hsqrt_nonneg := Real.sqrt_nonneg (8 * x ^ 2 + 1)
  have hrhs_nonneg : 0 ≤ 1 + 2 * x ^ 2 + 2 * y ^ 2 := by positivity
  have hrhs_sq : (1 + 2 * x ^ 2 + 2 * y ^ 2) ^ 2 = 8 * x ^ 2 + 1 := by
    nlinarith
  have hsqrt_eq : Real.sqrt (8 * x ^ 2 + 1) = 1 + 2 * x ^ 2 + 2 * y ^ 2 := by
    nlinarith
  nlinarith

theorem gap2 :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      discriminantRoot x ≥ 1 + 2 * x ^ 2 := by
  intro x hx
  have hx_sq : x ^ 2 ≤ 1 := by
    rcases hx with ⟨hxlo, hxhi⟩
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
  have hprod : 0 ≤ x ^ 2 * (1 - x ^ 2) :=
    mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx_sq)
  have hD : 0 ≤ 8 * x ^ 2 + 1 := by positivity
  have hsqrt := Real.sq_sqrt hD
  have hsqrt_nonneg := Real.sqrt_nonneg (8 * x ^ 2 + 1)
  have hrhs_nonneg : 0 ≤ 1 + 2 * x ^ 2 := by positivity
  unfold discriminantRoot
  nlinarith

theorem gap3 (y : UnitInterval → ℝ)
    (hy : IsContinuousBranch y) :
    ∃ ε : UnitInterval → ℝ,
      (∀ x, ε x = 1 ∨ ε x = -1) ∧
        ∀ x, y x = ε x * baseBranch x := by
  refine ⟨fun x => if 0 ≤ y x then 1 else -1, ?_, ?_⟩
  · intro x
    by_cases hx : 0 ≤ y x <;> simp [hx]
  · intro x
    have hy_sq : y x ^ 2 = squareProfile x := gap1 (x : ℝ) (y x) (hy.2 x)
    have hdisc := gap2 (x : ℝ) x.property
    have hprofile : 0 ≤ squareProfile x := by
      unfold squareProfile
      linarith
    have hbase_sq : baseBranch x ^ 2 = squareProfile x := by
      unfold baseBranch
      exact Real.sq_sqrt hprofile
    have hbase_nonneg : 0 ≤ baseBranch x := Real.sqrt_nonneg _
    by_cases hx : 0 ≤ y x
    · have heq : y x = baseBranch x := by nlinarith
      calc
        y x = baseBranch x := heq
        _ = (if 0 ≤ y x then 1 else -1) * baseBranch x := by simp [hx]
    · have hyneg : y x < 0 := lt_of_not_ge hx
      have heq : y x = -baseBranch x := by nlinarith
      calc
        y x = -baseBranch x := heq
        _ = (if 0 ≤ y x then 1 else -1) * baseBranch x := by simp [hx]

theorem gap4 (y : UnitInterval → ℝ)
    (hy : IsContinuousBranch y) :
    y = baseBranch ∨ y = negBaseBranch ∨
      y = signBranch ∨ y = negSignBranch := by
  rcases gap3 y hy with ⟨ε, hε, hyrepr⟩
  have hchoices (x : UnitInterval) :
      y x = baseBranch x ∨ y x = -baseBranch x := by
    rcases hε x with hx | hx
    · left
      rw [hyrepr x, hx]
      ring
    · right
      rw [hyrepr x, hx]
      ring
  have hsign_neg (t : ℝ) (ht : t < 0) : Real.sign t = -1 := by
    unfold Real.sign
    simp [ht]
  have hsign_pos (t : ℝ) (ht : 0 < t) : Real.sign t = 1 := by
    have hnot : ¬t < 0 := not_lt_of_ge (le_of_lt ht)
    unfold Real.sign
    simp [hnot, ht]
  have hnozero (x : UnitInterval)
      (hlo : (-1 : ℝ) < (x : ℝ)) (hhi : (x : ℝ) < 1)
      (hne : (x : ℝ) ≠ 0) : y x ≠ 0 := by
    intro hyzero
    have hc := hy.2 x
    unfold CurveEquation curvePolynomial at hc
    rw [hyzero] at hc
    have hxpos : 0 < (x : ℝ) ^ 2 := sq_pos_of_ne_zero hne
    have hxlt : (x : ℝ) ^ 2 < 1 := by nlinarith
    norm_num at hc
    nlinarith [sq_nonneg ((x : ℝ) ^ 2)]
  let proj : ℝ → UnitInterval := fun t =>
    ⟨max (-1) (min 1 t), by
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_left _ _)⟩
  have hclamp_cont :
      Continuous (fun t : ℝ => max (-1 : ℝ) (min 1 t)) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hproj_cont : Continuous proj := by
    unfold proj
    continuity
  have hproj_eq (x : UnitInterval) : proj (x : ℝ) = x := by
    apply Subtype.ext
    simp [proj, x.property.1, x.property.2]
  have hg_cont : Continuous (fun t : ℝ => y (proj t)) :=
    hy.1.comp hproj_cont
  have hnot_opposite (a b : UnitInterval)
      (halo : (-1 : ℝ) < (a : ℝ)) (hahi : (a : ℝ) < 1)
      (hblo : (-1 : ℝ) < (b : ℝ)) (hbhi : (b : ℝ) < 1)
      (hside : (0 < (a : ℝ) ∧ 0 < (b : ℝ)) ∨
        ((a : ℝ) < 0 ∧ (b : ℝ) < 0))
      (hya : 0 < y a) (hyb : y b < 0) : False := by
    rcases le_total a b with hab | hba
    · have hbmem : (b : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨hab, le_rfl⟩
      have hamem : (a : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨le_rfl, hab⟩
      have hz : (0 : ℝ) ∈ Set.Icc (y b) (y a) :=
        ⟨le_of_lt hyb, le_of_lt hya⟩
      have hgb : y (proj (b : ℝ)) = y b := by rw [hproj_eq b]
      have hga : y (proj (a : ℝ)) = y a := by rw [hproj_eq a]
      have hz' : (0 : ℝ) ∈ Set.Icc
          ((fun t : ℝ => y (proj t)) (b : ℝ))
          ((fun t : ℝ => y (proj t)) (a : ℝ)) := by
        simpa [hgb, hga] using hz
      rcases (isPreconnected_Icc.intermediate_value hbmem hamem
          hg_cont.continuousOn hz') with ⟨t, ht, hyt⟩
      let c : UnitInterval :=
        ⟨t, ⟨le_trans a.property.1 ht.1, le_trans ht.2 b.property.2⟩⟩
      have hpc : proj t = c := by
        simpa [c] using hproj_eq c
      change y (proj t) = 0 at hyt
      rw [hpc] at hyt
      have hclo : (-1 : ℝ) < (c : ℝ) := by
        change (-1 : ℝ) < t
        exact lt_of_lt_of_le halo ht.1
      have hchi : (c : ℝ) < 1 := by
        change t < (1 : ℝ)
        exact lt_of_le_of_lt ht.2 hbhi
      have hcne : (c : ℝ) ≠ 0 := by
        change t ≠ 0
        rcases hside with hpos | hneg
        · nlinarith [ht.1, hpos.1]
        · nlinarith [ht.2, hneg.2]
      exact hnozero c hclo hchi hcne hyt
    · have hbmem : (b : ℝ) ∈ Set.Icc (b : ℝ) (a : ℝ) := ⟨le_rfl, hba⟩
      have hamem : (a : ℝ) ∈ Set.Icc (b : ℝ) (a : ℝ) := ⟨hba, le_rfl⟩
      have hz : (0 : ℝ) ∈ Set.Icc (y b) (y a) :=
        ⟨le_of_lt hyb, le_of_lt hya⟩
      have hgb : y (proj (b : ℝ)) = y b := by rw [hproj_eq b]
      have hga : y (proj (a : ℝ)) = y a := by rw [hproj_eq a]
      have hz' : (0 : ℝ) ∈ Set.Icc
          ((fun t : ℝ => y (proj t)) (b : ℝ))
          ((fun t : ℝ => y (proj t)) (a : ℝ)) := by
        simpa [hgb, hga] using hz
      rcases (isPreconnected_Icc.intermediate_value hbmem hamem
          hg_cont.continuousOn hz') with ⟨t, ht, hyt⟩
      let c : UnitInterval :=
        ⟨t, ⟨le_trans b.property.1 ht.1, le_trans ht.2 a.property.2⟩⟩
      have hpc : proj t = c := by
        simpa [c] using hproj_eq c
      change y (proj t) = 0 at hyt
      rw [hpc] at hyt
      have hclo : (-1 : ℝ) < (c : ℝ) := by
        change (-1 : ℝ) < t
        exact lt_of_lt_of_le hblo ht.1
      have hchi : (c : ℝ) < 1 := by
        change t < (1 : ℝ)
        exact lt_of_le_of_lt ht.2 hahi
      have hcne : (c : ℝ) ≠ 0 := by
        change t ≠ 0
        rcases hside with hpos | hneg
        · nlinarith [ht.1, hpos.2]
        · nlinarith [ht.2, hneg.1]
      exact hnozero c hclo hchi hcne hyt
  have hsame (a b : UnitInterval)
      (halo : (-1 : ℝ) < (a : ℝ)) (hahi : (a : ℝ) < 1)
      (hblo : (-1 : ℝ) < (b : ℝ)) (hbhi : (b : ℝ) < 1)
      (hside : (0 < (a : ℝ) ∧ 0 < (b : ℝ)) ∨
        ((a : ℝ) < 0 ∧ (b : ℝ) < 0)) :
      (0 < y a ↔ 0 < y b) := by
    have hane : y a ≠ 0 := by
      apply hnozero a halo hahi
      rcases hside with hpos | hneg <;> nlinarith
    have hbne : y b ≠ 0 := by
      apply hnozero b hblo hbhi
      rcases hside with hpos | hneg <;> nlinarith
    constructor
    · intro hya
      by_contra hnot
      have hyb : y b < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hbne
      exact hnot_opposite a b halo hahi hblo hbhi hside hya hyb
    · intro hyb
      by_contra hnot
      have hya : y a < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hane
      exact hnot_opposite b a hblo hbhi halo hahi
        (hside.elim (fun h => Or.inl ⟨h.2, h.1⟩)
          (fun h => Or.inr ⟨h.2, h.1⟩)) hyb hya
  have hfrom_pos (x : UnitInterval) (hx : 0 < y x) :
      y x = baseBranch x := by
    rcases hchoices x with h | h
    · exact h
    · have hb : 0 ≤ baseBranch x := Real.sqrt_nonneg _
      nlinarith
  have hfrom_neg (x : UnitInterval) (hx : y x < 0) :
      y x = -baseBranch x := by
    rcases hchoices x with h | h
    · have hb : 0 ≤ baseBranch x := Real.sqrt_nonneg _
      nlinarith
    · exact h
  have hendpoint (x : UnitInterval)
      (hx : (x : ℝ) = -1 ∨ (x : ℝ) = 0 ∨ (x : ℝ) = 1) :
      y x = 0 ∧ baseBranch x = 0 := by
    have hsq := gap1 (x : ℝ) (y x) (hy.2 x)
    have hs9 : Real.sqrt (9 : ℝ) = 3 := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 9 by norm_num)
      have hn := Real.sqrt_nonneg (9 : ℝ)
      nlinarith
    have hs1 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    have hp : squareProfile (x : ℝ) = 0 := by
      rcases hx with hx | hx | hx <;>
        norm_num [squareProfile, discriminantRoot, hx, hs9, hs1]
    have hyzero : y x = 0 := by
      rw [hp] at hsq
      nlinarith
    have hbzero : baseBranch x = 0 := by simp [baseBranch, hp]
    exact ⟨hyzero, hbzero⟩
  let p : UnitInterval := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  let m : UnitInterval := ⟨(-1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hpne : y p ≠ 0 := by
    apply hnozero p <;> norm_num [p]
  have hmne : y m ≠ 0 := by
    apply hnozero m <;> norm_num [m]
  have hright_base (hp : 0 < y p) (x : UnitInterval)
      (hx : 0 < (x : ℝ)) : y x = baseBranch x := by
    by_cases hx1 : (x : ℝ) = 1
    · have h := hendpoint x (Or.inr (Or.inr hx1))
      rw [h.1, h.2]
    · have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 hx1
      apply hfrom_pos x
      exact (hsame x p (by nlinarith [x.property.1]) hxlt
        (by norm_num [p]) (by norm_num [p])
        (Or.inl ⟨hx, by norm_num [p]⟩)).2 hp
  have hright_neg (hp : y p < 0) (x : UnitInterval)
      (hx : 0 < (x : ℝ)) : y x = -baseBranch x := by
    by_cases hx1 : (x : ℝ) = 1
    · have h := hendpoint x (Or.inr (Or.inr hx1))
      rw [h.1, h.2]
      simp
    · have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 hx1
      apply hfrom_neg x
      have hpos_iff := hsame x p (by nlinarith [x.property.1]) hxlt
        (by norm_num [p]) (by norm_num [p])
        (Or.inl ⟨hx, by norm_num [p]⟩)
      have hxne := hnozero x (by nlinarith [x.property.1]) hxlt (ne_of_gt hx)
      have hnpos : ¬0 < y x := by
        intro hpos
        exact (not_lt_of_ge (le_of_lt hp)) (hpos_iff.mp hpos)
      exact lt_of_le_of_ne (le_of_not_gt hnpos) hxne
  have hleft_base (hm : 0 < y m) (x : UnitInterval)
      (hx : (x : ℝ) < 0) : y x = baseBranch x := by
    by_cases hxm : (x : ℝ) = -1
    · have h := hendpoint x (Or.inl hxm)
      rw [h.1, h.2]
    · have hxlo : (-1 : ℝ) < (x : ℝ) :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxm)
      apply hfrom_pos x
      exact (hsame x m hxlo (by nlinarith [x.property.2])
        (by norm_num [m]) (by norm_num [m])
        (Or.inr ⟨hx, by norm_num [m]⟩)).2 hm
  have hleft_neg (hm : y m < 0) (x : UnitInterval)
      (hx : (x : ℝ) < 0) : y x = -baseBranch x := by
    by_cases hxm : (x : ℝ) = -1
    · have h := hendpoint x (Or.inl hxm)
      rw [h.1, h.2]
      simp
    · have hxlo : (-1 : ℝ) < (x : ℝ) :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxm)
      apply hfrom_neg x
      have hpos_iff := hsame x m hxlo (by nlinarith [x.property.2])
        (by norm_num [m]) (by norm_num [m])
        (Or.inr ⟨hx, by norm_num [m]⟩)
      have hxne := hnozero x hxlo (by nlinarith [x.property.2]) (ne_of_lt hx)
      have hnpos : ¬0 < y x := by
        intro hpos
        exact (not_lt_of_ge (le_of_lt hm)) (hpos_iff.mp hpos)
      exact lt_of_le_of_ne (le_of_not_gt hnpos) hxne
  by_cases hp : 0 < y p
  · by_cases hm : 0 < y m
    · left
      funext x
      rcases lt_trichotomy (x : ℝ) 0 with hx | hx | hx
      · exact hleft_base hm x hx
      · have hz := hendpoint x (Or.inr (Or.inl hx))
        exact hz.1.trans hz.2.symm
      · exact hright_base hp x hx
    · have hmneg : y m < 0 := lt_of_le_of_ne (le_of_not_gt hm) hmne
      right
      right
      left
      funext x
      rcases lt_trichotomy (x : ℝ) 0 with hx | hx | hx
      · have hs : Real.sign (x : ℝ) = -1 := hsign_neg (x : ℝ) hx
        calc
          y x = -baseBranch x := hleft_neg hmneg x hx
          _ = signBranch x := by
            unfold signBranch
            rw [hs]
            ring
      · have hz := hendpoint x (Or.inr (Or.inl hx))
        calc
          y x = 0 := hz.1
          _ = signBranch x := by
            unfold signBranch
            rw [hx]
            norm_num [Real.sign]
      · have hs : Real.sign (x : ℝ) = 1 := hsign_pos (x : ℝ) hx
        calc
          y x = baseBranch x := hright_base hp x hx
          _ = signBranch x := by
            unfold signBranch
            rw [hs]
            ring
  · have hpneg : y p < 0 := lt_of_le_of_ne (le_of_not_gt hp) hpne
    by_cases hm : 0 < y m
    · right
      right
      right
      funext x
      rcases lt_trichotomy (x : ℝ) 0 with hx | hx | hx
      · have hs : Real.sign (x : ℝ) = -1 := hsign_neg (x : ℝ) hx
        calc
          y x = baseBranch x := hleft_base hm x hx
          _ = negSignBranch x := by
            unfold negSignBranch
            rw [hs]
            ring
      · have hz := hendpoint x (Or.inr (Or.inl hx))
        calc
          y x = 0 := hz.1
          _ = negSignBranch x := by
            unfold negSignBranch
            rw [hx]
            norm_num [Real.sign]
      · have hs : Real.sign (x : ℝ) = 1 := hsign_pos (x : ℝ) hx
        calc
          y x = -baseBranch x := hright_neg hpneg x hx
          _ = negSignBranch x := by
            unfold negSignBranch
            rw [hs]
            ring
    · have hmneg : y m < 0 := lt_of_le_of_ne (le_of_not_gt hm) hmne
      right
      left
      funext x
      rcases lt_trichotomy (x : ℝ) 0 with hx | hx | hx
      · simpa [negBaseBranch] using hleft_neg hmneg x hx
      · have hz := hendpoint x (Or.inr (Or.inl hx))
        simp [negBaseBranch, hz.1, hz.2]
      · simpa [negBaseBranch] using hright_neg hpneg x hx

theorem gap5 :
    continuousBranches =
      {baseBranch, negBaseBranch, signBranch, negSignBranch} := by
  have hsign_neg (t : ℝ) (ht : t < 0) : Real.sign t = -1 := by
    unfold Real.sign
    simp [ht]
  have hsign_pos (t : ℝ) (ht : 0 < t) : Real.sign t = 1 := by
    have hnot : ¬t < 0 := not_lt_of_ge (le_of_lt ht)
    unfold Real.sign
    simp [hnot, ht]
  have hsign_abs (t : ℝ) : |Real.sign t| ≤ 1 := by
    rcases lt_trichotomy t 0 with ht | ht | ht
    · rw [hsign_neg t ht]
      norm_num
    · subst t
      norm_num [Real.sign]
    · rw [hsign_pos t ht]
      norm_num
  have hbase_cont : Continuous baseBranch := by
    unfold baseBranch squareProfile discriminantRoot
    continuity
  have hbase_zero (x : UnitInterval) (hx : (x : ℝ) = 0) :
      baseBranch x = 0 := by
    simp [baseBranch, squareProfile, discriminantRoot, hx]
  have hsign_cont : Continuous signBranch := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [Metric.continuousAt_iff]
    intro e he
    have hb : ContinuousAt baseBranch x := hbase_cont.continuousAt
    rw [Metric.continuousAt_iff] at hb
    rcases hb e he with ⟨d, hdpos, hd⟩
    rcases lt_trichotomy (x : ℝ) 0 with hx | hx | hx
    · refine ⟨min d (-(x : ℝ)), lt_min hdpos (by linarith), ?_⟩
      intro z hz
      have hzd : dist z x < d := lt_of_lt_of_le hz (min_le_left _ _)
      have hzreal : dist (z : ℝ) (x : ℝ) < -(x : ℝ) := by
        simpa using lt_of_lt_of_le hz (min_le_right _ _)
      have hzneg : (z : ℝ) < 0 := by
        rw [Real.dist_eq] at hzreal
        have hu := (abs_lt.mp hzreal).2
        linarith
      have hsx : Real.sign (x : ℝ) = -1 := hsign_neg (x : ℝ) hx
      have hsz : Real.sign (z : ℝ) = -1 := hsign_neg (z : ℝ) hzneg
      simpa [signBranch, hsx, hsz] using hd hzd
    · refine ⟨d, hdpos, ?_⟩
      intro z hz
      have hbx : baseBranch x = 0 := hbase_zero x hx
      have hsx : signBranch x = 0 := by simp [signBranch, hbx]
      have hsbound : |Real.sign (z : ℝ)| ≤ 1 := hsign_abs (z : ℝ)
      calc
        dist (signBranch z) (signBranch x) =
            |Real.sign (z : ℝ) * baseBranch z| := by
              rw [hsx]
              simp [signBranch]
        _ ≤ |baseBranch z| := by
              rw [abs_mul]
              exact mul_le_of_le_one_left (abs_nonneg _) hsbound
        _ = dist (baseBranch z) (baseBranch x) := by
              rw [hbx]
              simp
        _ < e := hd hz
    · refine ⟨min d (x : ℝ), lt_min hdpos hx, ?_⟩
      intro z hz
      have hzd : dist z x < d := lt_of_lt_of_le hz (min_le_left _ _)
      have hzreal : dist (z : ℝ) (x : ℝ) < (x : ℝ) := by
        simpa using lt_of_lt_of_le hz (min_le_right _ _)
      have hzpos : 0 < (z : ℝ) := by
        rw [Real.dist_eq] at hzreal
        have hl := (abs_lt.mp hzreal).1
        linarith
      have hsx : Real.sign (x : ℝ) = 1 := hsign_pos (x : ℝ) hx
      have hsz : Real.sign (z : ℝ) = 1 := hsign_pos (z : ℝ) hzpos
      simpa [signBranch, hsx, hsz] using hd hzd
  have hneg_cont : Continuous negBaseBranch := by
    simpa only [negBaseBranch] using hbase_cont.neg
  have hnegsign_cont : Continuous negSignBranch := by
    have h : negSignBranch = fun x => -signBranch x := by
      funext x
      simp [negSignBranch, signBranch]
    rw [h]
    exact hsign_cont.neg
  have hbase_curve (x : UnitInterval) : CurveEquation x (baseBranch x) := by
    have hdisc := gap2 (x : ℝ) x.property
    have hp : 0 ≤ squareProfile (x : ℝ) := by
      unfold squareProfile
      linarith
    have hb : baseBranch x ^ 2 = squareProfile (x : ℝ) := by
      unfold baseBranch
      exact Real.sq_sqrt hp
    have hD : 0 ≤ 8 * (x : ℝ) ^ 2 + 1 := by positivity
    have hsqrt := Real.sq_sqrt hD
    unfold CurveEquation curvePolynomial
    rw [hb]
    unfold squareProfile discriminantRoot
    nlinarith
  have hneg_curve (x : UnitInterval) : CurveEquation x (negBaseBranch x) := by
    simpa [CurveEquation, curvePolynomial, negBaseBranch] using hbase_curve x
  have hsign_curve (x : UnitInterval) : CurveEquation x (signBranch x) := by
    rcases lt_trichotomy (x : ℝ) 0 with hx | hx | hx
    · have hs : Real.sign (x : ℝ) = -1 := hsign_neg (x : ℝ) hx
      simpa [signBranch, hs] using hneg_curve x
    · have hb := hbase_zero x hx
      simp [signBranch, hx, hb, CurveEquation, curvePolynomial]
    · have hs : Real.sign (x : ℝ) = 1 := hsign_pos (x : ℝ) hx
      simpa [signBranch, hs] using hbase_curve x
  have hnegsign_curve (x : UnitInterval) : CurveEquation x (negSignBranch x) := by
    rcases lt_trichotomy (x : ℝ) 0 with hx | hx | hx
    · have hs : Real.sign (x : ℝ) = -1 := hsign_neg (x : ℝ) hx
      simpa [negSignBranch, hs] using hbase_curve x
    · have hb := hbase_zero x hx
      simp [negSignBranch, hx, hb, CurveEquation, curvePolynomial]
    · have hs : Real.sign (x : ℝ) = 1 := hsign_pos (x : ℝ) hx
      simpa [negSignBranch, hs] using hneg_curve x
  ext y
  constructor
  · intro hyset
    rcases gap4 y hyset with h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · simp [h]
  · intro hyset
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyset
    rcases hyset with h | h | h | h
    · subst y
      exact ⟨hbase_cont, hbase_curve⟩
    · subst y
      exact ⟨hneg_cont, hneg_curve⟩
    · subst y
      exact ⟨hsign_cont, hsign_curve⟩
    · subst y
      exact ⟨hnegsign_cont, hnegsign_curve⟩

theorem gap6 :
    ∀ x y,
      partialY curvePolynomial x y =
        2 * (x ^ 2 + y ^ 2) * (2 * y) + 2 * y := by
  intro x y
  unfold partialY
  have hd : HasDerivAt
      (fun t : ℝ => (x ^ 2 + t ^ 2) ^ 2 - x ^ 2 + t ^ 2)
      (2 * (x ^ 2 + y ^ 2) * (2 * y) + 2 * y) y := by
    convert (((hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).pow 2)).pow 2).sub_const (x ^ 2) |>.add
        ((hasDerivAt_id y).pow 2) using 1 <;> norm_num <;> ring
  simpa [curvePolynomial] using hd.deriv

theorem gap7 (x y : ℝ)
    (hcritical : (x, y) ∈ criticalPoints) :
    2 * (x ^ 2 + y ^ 2) * (2 * y) + 2 * y = 0 := by
  rw [← gap6 x y]
  exact hcritical.2

theorem gap8 (x y : ℝ)
    (hcritical : (x, y) ∈ criticalPoints) :
    partialY curvePolynomial x y = 0 := by
  exact hcritical.2

theorem gap9 (x y : ℝ)
    (hcritical : (x, y) ∈ criticalPoints) :
    y = 0 := by
  have h := gap7 x y hcritical
  have hnonneg : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  nlinarith [sq_nonneg x, sq_nonneg y]

theorem gap10 (x y : ℝ)
    (hcritical : (x, y) ∈ criticalPoints) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hy : y = 0 := gap9 x y hcritical
  have hc := hcritical.1
  unfold CurveEquation curvePolynomial at hc
  rw [hy] at hc
  norm_num at hc
  have hfac : x ^ 2 * (x ^ 2 - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with hx | hx
  · left
    nlinarith [sq_nonneg x]
  · have hfac' : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac' with hx1 | hxm1
    · right
      left
      linarith
    · right
      right
      linarith

theorem gap11 :
    criticalPoints = {(0, 0), (1, 0), (-1, 0)} := by
  ext p
  constructor
  · intro hp
    rcases p with ⟨x, y⟩
    have hy : y = 0 := gap9 x y hp
    have hx := gap10 x y hp
    rcases hx with hx | hx | hx
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp
    · subst p
      norm_num [criticalPoints, CurveEquation, curvePolynomial, gap6]
    · subst p
      norm_num [criticalPoints, CurveEquation, curvePolynomial, gap6]
    · subst p
      norm_num [criticalPoints, CurveEquation, curvePolynomial, gap6]

end

end ProofGap.Exercise3367
