import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1383

noncomputable section

open Filter

def realCubeRoot (y : ℝ) : ℝ :=
  Real.sign y * Real.rpow |y| (1 / 3 : ℝ)

def f (x : ℝ) : ℝ := realCubeRoot (Real.sin (x ^ 3))

def sineSeries (x : ℝ) : ℝ :=
  x ^ 3 - x ^ 9 / (Nat.factorial 3 : ℝ) +
    x ^ 15 / (Nat.factorial 5 : ℝ)

def factoredSeries (x : ℝ) : ℝ :=
  x * realCubeRoot (1 + x ^ 12 / 120 - x ^ 6 / 6)

def binomialSeries (x : ℝ) : ℝ :=
  x * (1 + (1 / 3 : ℝ) * (x ^ 12 / 120 - x ^ 6 / 6) -
    (1 / 9 : ℝ) * (x ^ 12 / 120 - x ^ 6 / 6) ^ 2)

def finalPolynomial (x : ℝ) : ℝ :=
  x - (1 / 18 : ℝ) * x ^ 7 - (1 / 3240 : ℝ) * x ^ 13

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

private abbrev punctured : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ

private def seriesFactor (x : ℝ) : ℝ :=
  1 + x ^ 12 / 120 - x ^ 6 / 6

private theorem rpow_third_cube (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (1 / 3 : ℝ) ^ 3 = x := by
  calc
    Real.rpow x (1 / 3 : ℝ) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
      exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
      exact (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

private theorem realCubeRoot_cube (x : ℝ) : realCubeRoot x ^ 3 = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [realCubeRoot, Real.sign_of_neg hx, abs_of_neg hx]
    change (-1 * Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 = x
    rw [show (-1 * Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 =
      -(Real.rpow (-x) (1 / 3 : ℝ) ^ 3) by ring,
      rpow_third_cube (-x) (by linarith)]
    ring
  · norm_num [realCubeRoot]
  · rw [realCubeRoot, Real.sign_of_pos hx, abs_of_pos hx, one_mul]
    exact rpow_third_cube x hx.le

private theorem cube_pow_injective {u v : ℝ} (h : u ^ 3 = v ^ 3) : u = v :=
  (show Odd 3 by decide).strictMono_pow.injective h

private theorem realCubeRoot_mul (u v : ℝ) :
    realCubeRoot (u * v) = realCubeRoot u * realCubeRoot v := by
  apply cube_pow_injective
  rw [realCubeRoot_cube, mul_pow, realCubeRoot_cube, realCubeRoot_cube]

private theorem realCubeRoot_cube_input (x : ℝ) :
    realCubeRoot (x ^ 3) = x := by
  apply cube_pow_injective
  rw [realCubeRoot_cube]

private theorem sineSeries_factor (x : ℝ) :
    sineSeries x = x ^ 3 * seriesFactor x := by
  unfold sineSeries seriesFactor
  norm_num
  ring

private theorem root_sineSeries_factor (x : ℝ) :
    realCubeRoot (sineSeries x) = x * realCubeRoot (seriesFactor x) := by
  rw [sineSeries_factor, realCubeRoot_mul, realCubeRoot_cube_input]

private theorem realCubeRoot_tendsto_one {L : Filter ℝ} {g : ℝ → ℝ}
    (hg : Tendsto g L (nhds 1)) :
    Tendsto (fun x => realCubeRoot (g x)) L (nhds 1) := by
  have hp : ∀ᶠ x in L, 0 < g x :=
    hg.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq : (fun x => realCubeRoot (g x)) =ᶠ[L]
      (fun x => Real.rpow (g x) (1 / 3 : ℝ)) := by
    filter_upwards [hp] with x hx
    simp [realCubeRoot, Real.sign_of_pos hx, abs_of_pos hx]
  have ht := (Real.continuousAt_rpow_const 1 (1 / 3 : ℝ)
    (Or.inl one_ne_zero)).tendsto.comp hg
  have ht' : Tendsto (fun x => Real.rpow (g x) (1 / 3 : ℝ)) L (nhds 1) := by
    convert ht using 1 <;> norm_num [Function.comp_def]
  exact ht'.congr' heq.symm

private theorem sinc_tendsto :
    Tendsto (fun x : ℝ => Real.sin (x ^ 3) / x ^ 3)
      punctured (nhds 1) := by
  have hp : Tendsto (fun x : ℝ => x ^ 3) punctured (nhds 0) := by
    have h := (tendsto_id :
      Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).pow 3
    convert h.mono_left
      (show punctured ≤ nhds 0 from nhdsWithin_le_nhds) using 1 <;> norm_num
  have he := Real.isEquivalent_sin.isLittleO.comp_tendsto hp
  have he0 :
      (fun x : ℝ => Real.sin (x ^ 3) - x ^ 3) =o[punctured]
        (fun x : ℝ => x ^ 3) := by
    convert he using 1 <;> simp [Function.comp_def]
  have hd := he0.tendsto_div_nhds_zero
  have hs : Tendsto
      (fun x : ℝ => (Real.sin (x ^ 3) - x ^ 3) / x ^ 3 + 1)
      punctured (nhds 1) := by
    convert hd.add_const 1 using 1 <;> norm_num
  refine hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

private theorem seriesFactor_tendsto :
    Tendsto seriesFactor punctured (nhds 1) := by
  have hc : ContinuousAt seriesFactor 0 := by
    unfold seriesFactor
    fun_prop
  convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;>
    norm_num [seriesFactor]

private theorem sine_remainder :
    (fun x : ℝ => Real.sin (x ^ 3) - sineSeries x)
      =o[nhds 0] (fun x : ℝ => x ^ 18) := by
  have hs :
      (fun z : ℝ => Real.sin z - (z - z ^ 3 / 6 + z ^ 5 / 120))
        =o[nhds 0] (fun z : ℝ => z ^ 6) := by
    have h := taylor_isLittleO_univ
      (x₀ := 0) (n := 6) Real.contDiff_sin
    convert h using 1
    · funext z
      simp [taylorWithinEval, taylorWithin, taylorCoeffWithin]
      norm_num [Finset.sum_range_succ, Real.iteratedDeriv_even_sin,
        Real.iteratedDeriv_odd_sin]
      ring
    · funext z
      ring
  have hp : Tendsto (fun x : ℝ => x ^ 3) (nhds 0) (nhds 0) := by
    convert (tendsto_id :
      Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).pow 3
      using 1 <;> norm_num
  have hc := hs.comp_tendsto hp
  convert hc using 1
  · funext x
    unfold sineSeries
    norm_num
    ring
  · funext x
    simp [Function.comp_def]
    ring

private theorem normalized_remainder :
    (fun x : ℝ => Real.sin (x ^ 3) / x ^ 3 - seriesFactor x)
      =o[punctured] (fun x : ℝ => x ^ 15) := by
  have h :
      (fun x : ℝ => Real.sin (x ^ 3) - sineSeries x)
        =o[punctured] (fun x : ℝ => x ^ 18) :=
    sine_remainder.mono nhdsWithin_le_nhds
  have hd := h.tendsto_div_nhds_zero
  have ht : Tendsto
      (fun x : ℝ =>
        (Real.sin (x ^ 3) / x ^ 3 - seriesFactor x) / x ^ 15)
      punctured (nhds 0) := by
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [sineSeries_factor]
    field_simp [hx0]
  have hz : ∀ᶠ x : ℝ in punctured,
      x ^ 15 = 0 →
        Real.sin (x ^ 3) / x ^ 3 - seriesFactor x = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    intro hp
    have hx0 : x ≠ 0 := by simpa using hx
    exact False.elim (hx0 (eq_zero_of_pow_eq_zero hp))
  exact (Asymptotics.isLittleO_iff_tendsto' hz).2 ht

private theorem gap1_helper :
    AgreesToOrderAt f (fun x => realCubeRoot (sineSeries x)) 0 15 := by
  have hsroot := realCubeRoot_tendsto_one sinc_tendsto
  have haroot := realCubeRoot_tendsto_one seriesFactor_tendsto
  have hden : Tendsto
      (fun x : ℝ =>
        realCubeRoot (Real.sin (x ^ 3) / x ^ 3) ^ 2 +
          realCubeRoot (Real.sin (x ^ 3) / x ^ 3) *
            realCubeRoot (seriesFactor x) +
          realCubeRoot (seriesFactor x) ^ 2)
      punctured (nhds 3) := by
    convert (hsroot.pow 2).add (hsroot.mul haroot) |>.add
      (haroot.pow 2) using 1 <;> norm_num
  have hinv : Tendsto
      (fun x : ℝ => (realCubeRoot (Real.sin (x ^ 3) / x ^ 3) ^ 2 +
        realCubeRoot (Real.sin (x ^ 3) / x ^ 3) *
          realCubeRoot (seriesFactor x) +
        realCubeRoot (seriesFactor x) ^ 2)⁻¹)
      punctured (nhds (3 : ℝ)⁻¹) :=
    hden.inv₀ (by norm_num)
  have hroot0 :=
    normalized_remainder.mul_isBigO (hinv.isBigO_one ℝ)
  have hroot :
      (fun x : ℝ =>
        realCubeRoot (Real.sin (x ^ 3) / x ^ 3) -
          realCubeRoot (seriesFactor x))
        =o[punctured] (fun x : ℝ => x ^ 15) := by
    refine hroot0.congr' ?_ (Eventually.of_forall (fun x => by simp))
    filter_upwards [self_mem_nhdsWithin,
      hden.eventually_ne (by norm_num : (3 : ℝ) ≠ 0)] with x hx hne
    have hdne :
        realCubeRoot (Real.sin (x ^ 3) / x ^ 3) ^ 2 +
          realCubeRoot (Real.sin (x ^ 3) / x ^ 3) *
            realCubeRoot (seriesFactor x) +
          realCubeRoot (seriesFactor x) ^ 2 ≠ 0 := hne
    rw [← div_eq_mul_inv]
    apply (div_eq_iff hdne).2
    calc
      Real.sin (x ^ 3) / x ^ 3 - seriesFactor x =
          realCubeRoot (Real.sin (x ^ 3) / x ^ 3) ^ 3 -
            realCubeRoot (seriesFactor x) ^ 3 := by
        rw [realCubeRoot_cube, realCubeRoot_cube]
      _ = (realCubeRoot (Real.sin (x ^ 3) / x ^ 3) -
            realCubeRoot (seriesFactor x)) *
          (realCubeRoot (Real.sin (x ^ 3) / x ^ 3) ^ 2 +
            realCubeRoot (Real.sin (x ^ 3) / x ^ 3) *
              realCubeRoot (seriesFactor x) +
            realCubeRoot (seriesFactor x) ^ 2) := by ring
  have hxO : (fun x : ℝ => x) =O[punctured] (fun _ : ℝ => (1 : ℝ)) :=
    ((tendsto_id : Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0))
      |>.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have hfinal0 := hroot.mul_isBigO hxO
  have hfinal :
      (fun x : ℝ => f x - realCubeRoot (sineSeries x))
        =o[punctured] (fun x : ℝ => x ^ 15) := by
    refine hfinal0.congr' ?_ (Eventually.of_forall (fun x => by simp))
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hf :
        f x = x * realCubeRoot (Real.sin (x ^ 3) / x ^ 3) := by
      calc
        f x = realCubeRoot
            (x ^ 3 * (Real.sin (x ^ 3) / x ^ 3)) := by
          unfold f
          congr 1
          field_simp [hx0]
        _ = x * realCubeRoot (Real.sin (x ^ 3) / x ^ 3) := by
          rw [realCubeRoot_mul, realCubeRoot_cube_input]
    rw [hf, root_sineSeries_factor]
    ring
  unfold AgreesToOrderAt
  simp only [sub_zero]
  have hTVS :
      (fun x : ℝ => f x - realCubeRoot (sineSeries x))
        =o[ℝ; punctured] (fun x : ℝ => x ^ 15) :=
    hfinal.isLittleOTVS
  have hins := hTVS.insert (s := ({0} : Set ℝ)ᶜ)
    (by norm_num [f, realCubeRoot, sineSeries])
  have hset : insert (0 : ℝ) ({0} : Set ℝ)ᶜ = Set.univ := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact eq_or_ne x 0
  have hfilter :
      nhdsWithin 0 (insert (0 : ℝ) ({0} : Set ℝ)ᶜ) = nhds 0 := by
    rw [hset, nhdsWithin_univ]
  rw [hfilter] at hins
  exact Asymptotics.isLittleOTVS_iff_isLittleO.mp hins

private theorem rpow_quadratic :
    (fun u : ℝ => Real.rpow (1 + u) (1 / 3 : ℝ) -
      (1 + u / 3 - u ^ 2 / 9))
      =o[nhds 0] (fun u : ℝ => u ^ 2) := by
  let F : ℝ → ℝ := fun u => Real.rpow (1 + u) (1 / 3 : ℝ)
  let G : ℝ → ℝ := fun u =>
    (1 / 3 : ℝ) * Real.rpow (1 + u) (-2 / 3 : ℝ)
  have hF (u : ℝ) (hu : u ∈ Set.Ioi (-1)) :
      HasDerivWithinAt F (G u) (Set.Ioi (-1)) u := by
    have hne : 1 + u ≠ 0 := by
      have : -1 < u := hu
      linarith
    have hr := Real.hasDerivAt_rpow_const
      (x := 1 + u) (p := (1 / 3 : ℝ)) (Or.inl hne)
    have hi : HasDerivAt (fun z : ℝ => 1 + z) 1 u := by
      convert (hasDerivAt_const u (1 : ℝ)).add
        (hasDerivAt_id u) using 1 <;> norm_num
    have hc := hr.comp u hi
    convert hc.hasDerivWithinAt using 1 <;>
      norm_num [F, G] <;> ring
  have hG0 :
      HasDerivWithinAt G (-2 / 9 : ℝ) (Set.Ioi (-1)) 0 := by
    have hr := Real.hasDerivAt_rpow_const
      (x := (1 + 0 : ℝ)) (p := (-2 / 3 : ℝ))
        (Or.inl (by norm_num))
    have hi : HasDerivAt (fun z : ℝ => 1 + z) 1 0 := by
      convert (hasDerivAt_const 0 (1 : ℝ)).add
        (hasDerivAt_id 0) using 1 <;> norm_num
    have hc := (hr.comp 0 hi).const_mul (1 / 3 : ℝ)
    convert hc.hasDerivWithinAt using 1 <;>
      norm_num [G] <;> ring
  have hcd : ContDiffOn ℝ 2 (fun u : ℝ =>
      Real.rpow (1 + u) (1 / 3 : ℝ)) (Set.Ioi (-1)) := by
    intro u hu
    have hne : 1 + u ≠ 0 := by
      have : -1 < u := hu
      linarith
    have hiCD : ContDiffAt ℝ 2 (fun z : ℝ => 1 + z) u := by
      fun_prop
    exact (Real.contDiffAt_rpow_const_of_ne hne).comp u
      hiCD |>.contDiffWithinAt
  have huniq (u : ℝ) (hu : u ∈ Set.Ioi (-1)) :
      UniqueDiffWithinAt ℝ (Set.Ioi (-1)) u :=
    (uniqueDiffOn_Ioi (-1 : ℝ)).uniqueDiffWithinAt hu
  have hi0 :
      iteratedDerivWithin 0 F (Set.Ioi (-1)) 0 = 1 := by
    simp [F]
  have hi1 :
      iteratedDerivWithin 1 F (Set.Ioi (-1)) 0 = 1 / 3 := by
    rw [iteratedDerivWithin_succ (n := 0)]
    simp only [iteratedDerivWithin_zero]
    simpa [G] using (hF 0 (by norm_num)).derivWithin
      (huniq 0 (by norm_num))
  have heq : Set.EqOn
      (iteratedDerivWithin 1 F (Set.Ioi (-1))) G
      (Set.Ioi (-1)) := by
    intro u hu
    rw [iteratedDerivWithin_succ (n := 0)]
    simp only [iteratedDerivWithin_zero]
    exact (hF u hu).derivWithin (huniq u hu)
  have hi2 :
      iteratedDerivWithin 2 F (Set.Ioi (-1)) 0 = -2 / 9 := by
    rw [iteratedDerivWithin_succ (n := 1)]
    rw [derivWithin_congr heq (heq (by norm_num))]
    exact hG0.derivWithin (huniq 0 (by norm_num))
  have h := taylor_isLittleO
    (f := fun u : ℝ => Real.rpow (1 + u) (1 / 3 : ℝ))
    (x₀ := 0) (n := 2) (convex_Ioi (-1 : ℝ)) (by norm_num) hcd
  rw [isOpen_Ioi.nhdsWithin_eq
    (by norm_num : (0 : ℝ) ∈ Set.Ioi (-1))] at h
  convert h using 1
  · funext u
    change F u - (1 + u / 3 - u ^ 2 / 9) =
      F u - taylorWithinEval F 2 (Set.Ioi (-1)) 0 u
    simp [taylorWithinEval, taylorWithin, taylorCoeffWithin,
      Finset.sum_range_succ, hi0, hi1, hi2]
    ring
  · funext u
    ring

private theorem seriesFactor_pos (x : ℝ) : 0 < seriesFactor x := by
  unfold seriesFactor
  nlinarith [sq_nonneg (x ^ 6 - 10)]

private theorem root_seriesFactor_rpow (x : ℝ) :
    realCubeRoot (seriesFactor x) =
      Real.rpow (seriesFactor x) (1 / 3 : ℝ) := by
  have hp := seriesFactor_pos x
  simp [realCubeRoot, Real.sign_of_pos hp, abs_of_pos hp]

private theorem factored_binomial_agrees13 :
    AgreesToOrderAt factoredSeries binomialSeries 0 13 := by
  let u : ℝ → ℝ := fun x => x ^ 12 / 120 - x ^ 6 / 6
  have hu : Tendsto u (nhds 0) (nhds 0) := by
    have hc : ContinuousAt u 0 := by
      dsimp [u]
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [u]
  have hc : Tendsto (fun x : ℝ => x ^ 6 / 120 - 1 / 6)
      (nhds 0) (nhds (-1 / 6 : ℝ)) := by
    have hcont :
        ContinuousAt (fun x : ℝ => x ^ 6 / 120 - 1 / 6) 0 := by
      fun_prop
    convert hcont.tendsto using 1 <;> norm_num
  have huO : u =O[nhds 0] (fun x : ℝ => x ^ 6) := by
    have hp :=
      (Asymptotics.isBigO_refl (fun x : ℝ => x ^ 6) (nhds 0)).mul
        (hc.isBigO_one ℝ)
    refine hp.congr' (Eventually.of_forall ?_)
      (Eventually.of_forall ?_)
    · intro x
      dsimp [u]
      ring
    · intro x
      simp
  have hu2O := huO.mul huO
  have hcomp := rpow_quadratic.comp_tendsto hu
  have hroot :
      (fun x : ℝ => realCubeRoot (seriesFactor x) -
        (1 + u x / 3 - (u x) ^ 2 / 9))
        =o[nhds 0] (fun x : ℝ => (u x) ^ 2) := by
    refine hcomp.congr' (Eventually.of_forall ?_)
      (Eventually.of_forall (fun x => rfl))
    intro x
    simp only [Function.comp_apply]
    rw [root_seriesFactor_rpow]
    congr 2
    unfold seriesFactor
    dsimp [u]
    ring
  have h12 :
      (fun x : ℝ => realCubeRoot (seriesFactor x) -
        (1 + u x / 3 - (u x) ^ 2 / 9))
        =o[nhds 0] (fun x : ℝ => x ^ 12) := by
    have hu2O' :
        (fun x : ℝ => (u x) ^ 2) =O[nhds 0]
          (fun x : ℝ => x ^ 12) := by
      convert hu2O using 1 <;> funext x <;> ring
    exact hroot.trans_isBigO hu2O'
  have hxO :=
    Asymptotics.isBigO_refl (fun x : ℝ => x) (nhds 0)
  have h13raw := h12.mul_isBigO hxO
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine h13raw.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall ?_)
  · intro x
    unfold factoredSeries binomialSeries seriesFactor
    dsimp [u]
    ring
  · intro x
    ring

private theorem f_factored_agrees13 :
    AgreesToOrderAt f factoredSeries 0 13 := by
  have h := gap1_helper
  unfold AgreesToOrderAt at h ⊢
  simp only [sub_zero] at h ⊢
  have h13 := h.trans
    (Asymptotics.isLittleO_pow_pow (by norm_num : 13 < 15))
  refine h13.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => rfl))
  intro x
  change f x - realCubeRoot (sineSeries x) = f x - factoredSeries x
  rw [root_sineSeries_factor]
  simp [factoredSeries, seriesFactor]

private theorem f_binomial_agrees13 :
    AgreesToOrderAt f binomialSeries 0 13 := by
  have h1 := f_factored_agrees13
  have h2 := factored_binomial_agrees13
  unfold AgreesToOrderAt at h1 h2 ⊢
  have hs := h1.add h2
  refine hs.congr' (Eventually.of_forall (fun x => by ring))
    (Eventually.of_forall (fun x => rfl))

private theorem binomial_final_agrees13 :
    AgreesToOrderAt binomialSeries finalPolynomial 0 13 := by
  have h19 := (Asymptotics.isLittleO_pow_pow
    (by norm_num : 13 < 19)).const_mul_left (1 / 3240 : ℝ)
  have h25 := (Asymptotics.isLittleO_pow_pow
    (by norm_num : 13 < 25)).const_mul_left (-1 / 129600 : ℝ)
  have hs := h19.add h25
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine hs.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => rfl))
  intro x
  unfold binomialSeries finalPolynomial
  ring

theorem gap1 :
    AgreesToOrderAt f (fun x => realCubeRoot (sineSeries x)) 0 15 := by
  exact gap1_helper

theorem gap2 :
    AgreesToOrderAt (fun x => realCubeRoot (sineSeries x))
      factoredSeries 0 12 := by
  unfold AgreesToOrderAt
  have heq : (fun x : ℝ =>
      realCubeRoot (sineSeries x) - factoredSeries x) =
      (fun _ : ℝ => 0) := by
    funext x
    rw [root_sineSeries_factor]
    simp [factoredSeries, seriesFactor]
  rw [heq]
  exact Asymptotics.isLittleO_zero _ _

theorem gap3 :
    AgreesToOrderAt f factoredSeries 0 12 := by
  have h := gap1_helper
  unfold AgreesToOrderAt at h ⊢
  simp only [sub_zero] at h ⊢
  have h12 := h.trans
    (Asymptotics.isLittleO_pow_pow (by norm_num : 12 < 15))
  refine h12.congr' ?_ (Eventually.of_forall (fun x => rfl))
  exact Eventually.of_forall (fun x => by
    change f x - realCubeRoot (sineSeries x) = f x - factoredSeries x
    rw [root_sineSeries_factor]
    simp [factoredSeries, seriesFactor])

theorem gap4 :
    AgreesToOrderAt f binomialSeries 0 12 := by
  have h := f_binomial_agrees13
  unfold AgreesToOrderAt at h ⊢
  simp only [sub_zero] at h ⊢
  exact h.trans
    (Asymptotics.isLittleO_pow_pow (by norm_num : 12 < 13))

theorem gap5 :
    AgreesToOrderAt f finalPolynomial 0 13 := by
  have h1 := f_binomial_agrees13
  have h2 := binomial_final_agrees13
  unfold AgreesToOrderAt at h1 h2 ⊢
  have hs := h1.add h2
  refine hs.congr' (Eventually.of_forall (fun x => by ring))
    (Eventually.of_forall (fun x => rfl))

end

end ProofGap.Exercise1383
