import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise1382

noncomputable section

open Filter

def delta (x : ℝ) : ℝ := (Real.exp x - 1) / x - 1
def reciprocal (x : ℝ) : ℝ := x / (Real.exp x - 1)

def deltaPolynomial (x : ℝ) : ℝ :=
  x / 2 + x ^ 2 / 6 + x ^ 3 / 24 + x ^ 4 / 120

def geometricPolynomial (x : ℝ) : ℝ :=
  1 - delta x + delta x ^ 2 - delta x ^ 3 + delta x ^ 4

def squarePolynomial (x : ℝ) : ℝ :=
  x ^ 2 / 4 + x ^ 3 / 6 + 5 * x ^ 4 / 72

def cubePolynomial (x : ℝ) : ℝ := x ^ 3 / 8 + x ^ 4 / 8
def fourthPolynomial (x : ℝ) : ℝ := x ^ 4 / 16

def finalPolynomial (x : ℝ) : ℝ :=
  1 - x / 2 + x ^ 2 / 12 - x ^ 4 / 720

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhdsWithin a ({a} : Set ℝ)ᶜ)
    (fun x => g x - p x)
    (fun x => (x - a) ^ n)

private abbrev punctured : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ

private theorem littleO4_of_tendsto_div {u : ℝ → ℝ}
    (h : Tendsto (fun x => u x / x ^ 4) punctured (nhds 0)) :
    u =o[punctured] (fun x : ℝ => x ^ 4) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2 h
  filter_upwards [self_mem_nhdsWithin] with x hx
  intro hz
  have : x = 0 := by simpa using (pow_eq_zero hz)
  exact (by simpa [this] using hx)

private theorem delta_agrees :
    AgreesToOrderAt delta deltaPolynomial 0 4 := by
  have hrem := (Real.exp_sub_sum_range_succ_isLittleO_pow 5)
    |>.tendsto_div_nhds_zero
  have hrem' : Tendsto
      (fun x : ℝ =>
        (Real.exp x - ∑ i ∈ Finset.range 6, x ^ i / (i.factorial : ℝ)) /
          x ^ 5)
      punctured (nhds 0) :=
    hrem.mono_left nhdsWithin_le_nhds
  unfold AgreesToOrderAt
  simp only [sub_zero]
  apply littleO4_of_tendsto_div
  refine hrem'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  unfold delta deltaPolynomial
  norm_num [Finset.sum_range_succ]
  field_simp [hx0]
  ring

private theorem delta_error_div_tendsto :
    Tendsto (fun x : ℝ =>
      (delta x - deltaPolynomial x) / x ^ 4) punctured (nhds 0) := by
  have h := delta_agrees
  unfold AgreesToOrderAt at h
  simpa using h.tendsto_div_nhds_zero

private theorem deltaPolynomial_tendsto :
    Tendsto deltaPolynomial punctured (nhds 0) := by
  have hc : ContinuousAt deltaPolynomial 0 := by
    unfold deltaPolynomial
    fun_prop
  convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;>
    norm_num [deltaPolynomial]

private theorem delta_tendsto :
    Tendsto delta punctured (nhds 0) := by
  have hx4 : Tendsto (fun x : ℝ => x ^ 4) punctured (nhds 0) := by
    have hbase := (tendsto_id :
      Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).pow 4
    convert hbase.mono_left
      (show punctured ≤ nhds 0 from nhdsWithin_le_nhds) using 1 <;> norm_num
  have he : Tendsto (fun x : ℝ => delta x - deltaPolynomial x)
      punctured (nhds 0) := by
    have h := delta_agrees
    unfold AgreesToOrderAt at h
    have h' : (fun x : ℝ => delta x - deltaPolynomial x) =o[punctured]
        (fun x : ℝ => x ^ 4) := by simpa using h
    exact h'.tendsto_zero_of_tendsto hx4
  convert he.add deltaPolynomial_tendsto using 1 <;> ring

private theorem delta_div_x_tendsto :
    Tendsto (fun x : ℝ => delta x / x) punctured (nhds (1 / 2 : ℝ)) := by
  have hx3 : Tendsto (fun x : ℝ => x ^ 3) punctured (nhds 0) := by
    have hbase := (tendsto_id :
      Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).pow 3
    convert hbase.mono_left
      (show punctured ≤ nhds 0 from nhdsWithin_le_nhds) using 1 <;> norm_num
  have he0 := delta_error_div_tendsto.mul hx3
  have hp : Tendsto
      (fun x : ℝ => (1 / 2 : ℝ) + x / 6 + x ^ 2 / 24 + x ^ 3 / 120)
      punctured (nhds (1 / 2 : ℝ)) := by
    have hc : ContinuousAt
        (fun x : ℝ => (1 / 2 : ℝ) + x / 6 + x ^ 2 / 24 + x ^ 3 / 120) 0 := by
      fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
  have hs := he0.add hp
  have hs' : Tendsto
      (fun x : ℝ => (delta x - deltaPolynomial x) / x ^ 4 * x ^ 3 +
        ((1 / 2 : ℝ) + x / 6 + x ^ 2 / 24 + x ^ 3 / 120))
      punctured (nhds (1 / 2 : ℝ)) := by
    convert hs using 1 <;> norm_num
  refine hs'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  unfold delta deltaPolynomial
  field_simp [hx0]
  ring

private theorem inverse_geometric_agrees :
    AgreesToOrderAt (fun x : ℝ => 1 / (1 + delta x))
      geometricPolynomial 0 4 := by
  have hd4 := delta_div_x_tendsto.pow 4
  have hden : Tendsto (fun x : ℝ => 1 + delta x)
      punctured (nhds 1) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) punctured (nhds 1)).add
        delta_tendsto using 1 <;> norm_num
  have hfrac : Tendsto (fun x : ℝ => delta x / (1 + delta x))
      punctured (nhds 0) := by
    simpa using delta_tendsto.div hden (by norm_num)
  have hprod := hd4.mul hfrac
  have hprod0 : Tendsto
      (fun x : ℝ => (delta x / x) ^ 4 * (delta x / (1 + delta x)))
      punctured (nhds 0) := by
    convert hprod using 1 <;> norm_num
  unfold AgreesToOrderAt
  simp only [sub_zero]
  apply littleO4_of_tendsto_div
  have hneg : Tendsto
      (fun x : ℝ => -((delta x / x) ^ 4 *
        (delta x / (1 + delta x)))) punctured (nhds 0) := by
    convert hprod0.neg using 1 <;> norm_num
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    hden.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with x hx hne
  have hx0 : x ≠ 0 := by simpa using hx
  unfold geometricPolynomial
  field_simp [hx0, hne]
  ring

private theorem square_agrees :
    AgreesToOrderAt (fun x : ℝ => delta x ^ 2) squarePolynomial 0 4 := by
  have hsum : Tendsto (fun x : ℝ => delta x + deltaPolynomial x)
      punctured (nhds 0) := by
    convert delta_tendsto.add deltaPolynomial_tendsto using 1 <;> norm_num
  have hmain := delta_error_div_tendsto.mul hsum
  let r : ℝ → ℝ := fun x =>
    x ^ 4 / 14400 + x ^ 3 / 1440 + 13 * x ^ 2 / 2880 + x / 45
  have hr : Tendsto r punctured (nhds 0) := by
    have hc : ContinuousAt r 0 := by
      dsimp [r]
      fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num [r]
  have ht := hmain.add hr
  unfold AgreesToOrderAt
  simp only [sub_zero]
  apply littleO4_of_tendsto_div
  have ht0 : Tendsto
      (fun x : ℝ =>
        (delta x - deltaPolynomial x) / x ^ 4 *
          (delta x + deltaPolynomial x) + r x)
      punctured (nhds 0) := by
    convert ht using 1 <;> norm_num
  refine ht0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  dsimp [r]
  unfold squarePolynomial deltaPolynomial
  field_simp [hx0]
  ring

private theorem cube_agrees :
    AgreesToOrderAt (fun x : ℝ => delta x ^ 3) cubePolynomial 0 4 := by
  have hbracket : Tendsto
      (fun x : ℝ => delta x ^ 2 + delta x * deltaPolynomial x +
        deltaPolynomial x ^ 2) punctured (nhds 0) := by
    convert (delta_tendsto.pow 2).add
      (delta_tendsto.mul deltaPolynomial_tendsto) |>.add
        (deltaPolynomial_tendsto.pow 2) using 1 <;> norm_num
  have hmain := delta_error_div_tendsto.mul hbracket
  let r : ℝ → ℝ := fun x =>
    x ^ 8 / 1728000 + x ^ 7 / 115200 + x ^ 6 / 12800 +
      181 * x ^ 5 / 345600 + x ^ 4 / 384 + 59 * x ^ 3 / 5760 +
      137 * x ^ 2 / 4320 + 7 * x / 96
  have hr : Tendsto r punctured (nhds 0) := by
    have hc : ContinuousAt r 0 := by
      dsimp [r]
      fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num [r]
  have ht := hmain.add hr
  unfold AgreesToOrderAt
  simp only [sub_zero]
  apply littleO4_of_tendsto_div
  have ht0 : Tendsto
      (fun x : ℝ => (delta x - deltaPolynomial x) / x ^ 4 *
        (delta x ^ 2 + delta x * deltaPolynomial x +
          deltaPolynomial x ^ 2) + r x) punctured (nhds 0) := by
    convert ht using 1 <;> norm_num
  refine ht0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  dsimp [r]
  unfold cubePolynomial deltaPolynomial
  field_simp [hx0]
  ring

private theorem fourth_agrees :
    AgreesToOrderAt (fun x : ℝ => delta x ^ 4) fourthPolynomial 0 4 := by
  have hbracket : Tendsto
      (fun x : ℝ => delta x ^ 3 + delta x ^ 2 * deltaPolynomial x +
        delta x * deltaPolynomial x ^ 2 + deltaPolynomial x ^ 3)
      punctured (nhds 0) := by
    convert (((delta_tendsto.pow 3).add
      ((delta_tendsto.pow 2).mul deltaPolynomial_tendsto)).add
        (delta_tendsto.mul (deltaPolynomial_tendsto.pow 2))).add
          (deltaPolynomial_tendsto.pow 3) using 1 <;> norm_num
  have hmain := delta_error_div_tendsto.mul hbracket
  let r : ℝ → ℝ := fun x =>
    x ^ 12 / 207360000 + x ^ 11 / 10368000 +
      23 * x ^ 10 / 20736000 + 97 * x ^ 9 / 10368000 +
      101 * x ^ 8 / 1658880 + 83 * x ^ 7 / 259200 +
      719 * x ^ 6 / 518400 + 2 * x ^ 5 / 405 +
      751 * x ^ 4 / 51840 + 37 * x ^ 3 / 1080 +
      x ^ 2 / 16 + x / 12
  have hr : Tendsto r punctured (nhds 0) := by
    have hc : ContinuousAt r 0 := by
      dsimp [r]
      fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num [r]
  have ht := hmain.add hr
  unfold AgreesToOrderAt
  simp only [sub_zero]
  apply littleO4_of_tendsto_div
  have ht0 : Tendsto
      (fun x : ℝ => (delta x - deltaPolynomial x) / x ^ 4 *
        (delta x ^ 3 + delta x ^ 2 * deltaPolynomial x +
          delta x * deltaPolynomial x ^ 2 + deltaPolynomial x ^ 3) + r x)
      punctured (nhds 0) := by
    convert ht using 1 <;> norm_num
  refine ht0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  dsimp [r]
  unfold fourthPolynomial deltaPolynomial
  field_simp [hx0]
  ring

private theorem reciprocal_as_inverse (x : ℝ) (hx : x ≠ 0)
    (hexp : Real.exp x - 1 ≠ 0) :
    reciprocal x = 1 / ((Real.exp x - 1) / x) := by
  unfold reciprocal
  field_simp

private theorem quotient_as_delta (x : ℝ) :
    1 / ((Real.exp x - 1) / x) = 1 / (1 + delta x) := by
  unfold delta
  ring

private theorem reciprocal_geometric_agrees :
    AgreesToOrderAt reciprocal geometricPolynomial 0 4 := by
  have h := inverse_geometric_agrees
  unfold AgreesToOrderAt at h ⊢
  refine h.congr' ?_ (Eventually.of_forall (fun x => rfl))
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hexp : Real.exp x - 1 ≠ 0 := by
    intro he
    have he1 : Real.exp x = 1 := by linarith
    exact hx0 (Real.exp_injective (by simpa using he1))
  rw [reciprocal_as_inverse x hx0 hexp, quotient_as_delta x]

theorem gap1 :
    AgreesToOrderAt delta deltaPolynomial 0 4 := by
  exact delta_agrees

theorem gap2 (x : ℝ) (hx : x ≠ 0) (hexp : Real.exp x - 1 ≠ 0) :
    reciprocal x = 1 / ((Real.exp x - 1) / x) := by
  exact reciprocal_as_inverse x hx hexp

theorem gap3 (x : ℝ) :
    1 / ((Real.exp x - 1) / x) = 1 / (1 + delta x) := by
  exact quotient_as_delta x

theorem gap4 :
    AgreesToOrderAt (fun x : ℝ => 1 / (1 + delta x))
      geometricPolynomial 0 4 := by
  exact inverse_geometric_agrees

theorem gap5 :
    AgreesToOrderAt reciprocal geometricPolynomial 0 4 := by
  exact reciprocal_geometric_agrees

theorem gap6 :
    AgreesToOrderAt (fun x : ℝ => delta x ^ 2) squarePolynomial 0 4 := by
  exact square_agrees

theorem gap7 :
    AgreesToOrderAt (fun x : ℝ => delta x ^ 3) cubePolynomial 0 4 := by
  exact cube_agrees

theorem gap8 :
    AgreesToOrderAt (fun x : ℝ => delta x ^ 4) fourthPolynomial 0 4 := by
  exact fourth_agrees

theorem gap9 :
    AgreesToOrderAt reciprocal finalPolynomial 0 4 := by
  have h1 := delta_agrees
  have h2 := square_agrees
  have h3 := cube_agrees
  have h4 := fourth_agrees
  unfold AgreesToOrderAt at h1 h2 h3 h4 ⊢
  have hgeo := ((h1.neg_left.add h2).sub h3).add h4
  have hgeo' :
      (fun x : ℝ => geometricPolynomial x - finalPolynomial x) =o[punctured]
        (fun x : ℝ => x ^ 4) := by
    refine hgeo.congr' (Eventually.of_forall ?_) (Eventually.of_forall ?_)
    · intro x
      unfold geometricPolynomial finalPolynomial deltaPolynomial
        squarePolynomial cubePolynomial fourthPolynomial
      ring
    · intro x
      simp
  have hr := reciprocal_geometric_agrees
  unfold AgreesToOrderAt at hr
  have hr' :
      (fun x : ℝ => reciprocal x - geometricPolynomial x) =o[punctured]
        (fun x : ℝ => x ^ 4) := by
    simpa [punctured] using hr
  have hs := hr'.add hgeo'
  refine hs.congr' (Eventually.of_forall ?_) (Eventually.of_forall ?_)
  · intro x
    ring
  · intro x
    simp

end

end ProofGap.Exercise1382
