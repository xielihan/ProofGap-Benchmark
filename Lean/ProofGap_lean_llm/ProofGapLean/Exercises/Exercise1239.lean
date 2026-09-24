import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1239

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def EndpointZero (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : Prop :=
  ∀ j ≤ n, iterDeriv j f x = 0

private structure RootChain (f : ℝ → ℝ) (a b : ℝ) (r L : ℕ) where
  point : ℕ → ℝ
  mem : ∀ i, i ≤ L → point i ∈ Set.Icc a b
  mono : ∀ i j, i ≤ j → j ≤ L → point i ≤ point j
  endpoint_lt : 1 ≤ L → point 0 < point L
  zeroAt : ∀ i, i ≤ L → iterDeriv r f (point i) = 0
  repeated : ∀ i j, i ≤ j → j ≤ L → point i = point j →
    iterDeriv (r + (j - i)) f (point i) = 0

private structure NextSpec {f : ℝ → ℝ} {a b : ℝ} {r L : ℕ}
    (C : RootChain f a b r L) (i : ℕ) (z : ℝ) : Prop where
  mem : z ∈ Set.Icc a b
  left_le : C.point i ≤ z
  le_right : z ≤ C.point (i + 1)
  zeroAt : iterDeriv (r + 1) f z = 0
  strict : C.point i < C.point (i + 1) →
    z ∈ Set.Ioo (C.point i) (C.point (i + 1))

private noncomputable def rootChain_step {f : ℝ → ℝ} {a b : ℝ} {r L : ℕ}
    (hL : 1 ≤ L) (hcont : Continuous (iterDeriv r f))
    (C : RootChain f a b r L) :
    RootChain f a b (r + 1) (L - 1) := by
  classical
  have hexists : ∀ i : ℕ, ∃ z : ℝ, i < L → NextSpec C i z := by
    intro i
    by_cases hi : i < L
    · have hiL : i ≤ L := by omega
      have hi1L : i + 1 ≤ L := by omega
      by_cases heq : C.point i = C.point (i + 1)
      · refine ⟨C.point i, fun _ => ?_⟩
        refine ⟨C.mem i hiL, le_rfl, heq.le, ?_, ?_⟩
        · have hz := C.repeated i (i + 1) (by omega) hi1L heq
          simpa using hz
        · intro hlt
          exact (heq.not_lt hlt).elim
      · have hle := C.mono i (i + 1) (by omega) hi1L
        have hlt : C.point i < C.point (i + 1) := lt_of_le_of_ne hle heq
        obtain ⟨z, hz, hzder⟩ :=
          exists_deriv_eq_zero hlt hcont.continuousOn
            ((C.zeroAt i hiL).trans (C.zeroAt (i + 1) hi1L).symm)
        have hz0 : iterDeriv (r + 1) f z = 0 := by
          simpa [iterDeriv, Function.iterate_succ_apply'] using hzder
        refine ⟨z, fun _ => ⟨?_, hz.1.le, hz.2.le, hz0, fun _ => hz⟩⟩
        exact ⟨(C.mem i hiL).1.trans hz.1.le,
          hz.2.le.trans (C.mem (i + 1) hi1L).2⟩
    · exact ⟨a, fun hil => (hi hil).elim⟩
  choose y hy using hexists
  have hymono : ∀ i j, i ≤ j → j ≤ L - 1 → y i ≤ y j := by
    intro i j hij hj
    by_cases hij' : i = j
    · subst j
      exact le_rfl
    · have hilt : i < L := by omega
      have hjlt : j < L := by omega
      have hs_i := hy i hilt
      have hs_j := hy j hjlt
      calc
        y i ≤ C.point (i + 1) := hs_i.le_right
        _ ≤ C.point j := C.mono (i + 1) j (by omega) (by omega)
        _ ≤ y j := hs_j.left_le
  refine
    { point := y
      mem := ?_
      mono := hymono
      endpoint_lt := ?_
      zeroAt := ?_
      repeated := ?_ }
  · intro i hi
    exact (hy i (by omega)).mem
  · intro hnew
    have h0lt : 0 < L := by omega
    have hlastlt : L - 1 < L := by omega
    have hs0 := hy 0 h0lt
    have hsLast := hy (L - 1) hlastlt
    have hle : y 0 ≤ y (L - 1) := hymono 0 (L - 1) (by omega) le_rfl
    apply lt_of_le_of_ne hle
    intro heq
    have hmiddle :
        C.point 1 = y 0 := by
      apply le_antisymm
      · calc
          C.point 1 ≤ C.point (L - 1) :=
            C.mono 1 (L - 1) (by omega) (by omega)
          _ ≤ y (L - 1) := hsLast.left_le
          _ = y 0 := heq.symm
      · exact hs0.le_right
    have hmiddleLast : C.point (L - 1) = C.point 1 := by
      apply le_antisymm
      · calc
          C.point (L - 1) ≤ y (L - 1) := hsLast.left_le
          _ = y 0 := heq.symm
          _ = C.point 1 := hmiddle.symm
      · exact C.mono 1 (L - 1) (by omega) (by omega)
    have hleft : C.point 0 = C.point 1 := by
      apply le_antisymm (C.mono 0 1 (by omega) (by omega))
      by_contra hne
      have hlt : C.point 0 < C.point 1 :=
        lt_of_not_ge hne
      have := (hs0.strict hlt).2
      rw [hmiddle] at this
      exact lt_irrefl _ this
    have hright : C.point (L - 1) = C.point L := by
      apply le_antisymm (C.mono (L - 1) L (by omega) le_rfl)
      by_contra hne
      have hlt : C.point (L - 1) < C.point L :=
        lt_of_not_ge hne
      have hlt' : C.point (L - 1) < C.point ((L - 1) + 1) := by
        simpa [Nat.sub_add_cancel hL] using hlt
      have hslt := (hsLast.strict hlt').1
      have : y (L - 1) = C.point (L - 1) := by
        calc
          y (L - 1) = y 0 := heq.symm
          _ = C.point 1 := hmiddle.symm
          _ = C.point (L - 1) := hmiddleLast.symm
      rw [this] at hslt
      exact lt_irrefl _ hslt
    have hfirstLast : C.point 0 = C.point L := by
      calc
        C.point 0 = C.point 1 := hleft
        _ = C.point (L - 1) := hmiddleLast.symm
        _ = C.point L := hright
    exact (C.endpoint_lt (by omega)).ne hfirstLast
  · intro i hi
    exact (hy i (by omega)).zeroAt
  · intro i j hij hj heq
    have hilt : i < L := by omega
    have hjlt : j < L := by omega
    have hs_i := hy i hilt
    have hs_j := hy j hjlt
    by_cases hij' : i = j
    · subst j
      simpa using hs_i.zeroAt
    · have hijlt : i < j := lt_of_le_of_ne hij hij'
      have hchain :
          y i ≤ C.point (i + 1) ∧
          C.point (i + 1) ≤ C.point j ∧
          C.point j ≤ y j := by
        exact ⟨hs_i.le_right,
          C.mono (i + 1) j (by omega) (by omega), hs_j.left_le⟩
      have hi1eq : C.point (i + 1) = y i := by
        apply le_antisymm
        · calc
            C.point (i + 1) ≤ C.point j := hchain.2.1
            _ ≤ y j := hchain.2.2
            _ = y i := heq.symm
        · exact hchain.1
      have hijeq : C.point (i + 1) = C.point j := by
        apply le_antisymm hchain.2.1
        calc
          C.point j ≤ y j := hchain.2.2
          _ = y i := heq.symm
          _ = C.point (i + 1) := hi1eq.symm
      have hleft : C.point i = C.point (i + 1) := by
        apply le_antisymm (C.mono i (i + 1) (by omega) (by omega))
        by_contra hne
        have hlt : C.point i < C.point (i + 1) :=
          lt_of_not_ge hne
        have hslt := (hs_i.strict hlt).2
        rw [hi1eq] at hslt
        exact lt_irrefl _ hslt
      have hright : C.point j = C.point (j + 1) := by
        apply le_antisymm (C.mono j (j + 1) (by omega) (by omega))
        by_contra hne
        have hlt : C.point j < C.point (j + 1) :=
          lt_of_not_ge hne
        have hslt := (hs_j.strict hlt).1
        have : y j = C.point j := by
          calc
            y j = y i := heq.symm
            _ = C.point (i + 1) := hi1eq.symm
            _ = C.point j := hijeq
        rw [this] at hslt
        exact lt_irrefl _ hslt
      have hold := C.repeated i (j + 1) (by omega) (by omega)
        (by rw [hleft, hijeq, hright])
      have hyi : y i = C.point i := by
        rw [hleft, hi1eq]
      have horder : r + ((j + 1) - i) = (r + 1) + (j - i) := by
        omega
      simpa [hyi, horder] using hold

private def initialRootChain (f : ℝ → ℝ) (a b : ℝ) (p q : ℕ)
    (hab : a < b) (ha : EndpointZero f a p) (hb : EndpointZero f b q) :
    RootChain f a b 0 (p + q + 1) where
  point i := if i ≤ p then a else b
  mem i hi := by
    by_cases hip : i ≤ p
    · simp [hip, hab.le]
    · simp [hip, hab.le]
  mono i j hij hj := by
    by_cases hip : i ≤ p
    · by_cases hjp : j ≤ p
      · simp [hip, hjp]
      · simp [hip, hjp, hab.le]
    · have hjp : ¬j ≤ p := by omega
      simp [hip, hjp]
  endpoint_lt hL := by
    have hlast : ¬p + q + 1 ≤ p := by omega
    simpa [hlast] using hab
  zeroAt i hi := by
    by_cases hip : i ≤ p
    · simpa [hip, iterDeriv] using ha 0 (Nat.zero_le p)
    · simpa [hip, iterDeriv] using hb 0 (Nat.zero_le q)
  repeated i j hij hj heq := by
    by_cases hip : i ≤ p
    · by_cases hjp : j ≤ p
      · have hz := ha (j - i) (by omega)
        simpa [hip, hjp] using hz
      · have hab' : a = b := by simpa [hip, hjp] using heq
        exact (hab.ne hab').elim
    · have hjp : ¬j ≤ p := by omega
      have hz := hb (j - i) (by omega)
      simpa [hip, hjp] using hz

private theorem rootChain_iterate {f : ℝ → ℝ} {a b : ℝ}
    {r L M : ℕ} (hcont : ∀ s ≤ M, Continuous (iterDeriv s f))
    (C : RootChain f a b r L) (m : ℕ) (hm : m ≤ L)
    (hrm : r + m ≤ M) :
    Nonempty (RootChain f a b (r + m) (L - m)) := by
  induction m generalizing r L with
  | zero =>
      exact ⟨by simpa using C⟩
  | succ m ih =>
      obtain ⟨Cm⟩ := ih (r := r) (L := L) C (by omega) (by omega)
      have hlen : 1 ≤ L - m := by omega
      have hc := rootChain_step hlen (hcont (r + m) (by omega)) Cm
      exact ⟨by convert hc using 1 <;> omega⟩

private theorem generalized_rolle (f : ℝ → ℝ) (a b : ℝ) (p q : ℕ)
    (hab : a < b) (ha : EndpointZero f a p) (hb : EndpointZero f b q)
    (hf : ContDiff ℝ (p + q + 1) f) :
    ∃ c ∈ Set.Ioo a b, iterDeriv (p + q + 1) f c = 0 := by
  let N := p + q
  have hcont : ∀ s ≤ N, Continuous (iterDeriv s f) := by
    intro s hs
    have hs' : s ≤ p + q + 1 := by
      dsimp [N] at hs
      omega
    have h :=
      hf.continuous_iteratedDeriv s
        (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hs'))
    simpa [iterDeriv, ← iteratedDeriv_eq_iterate] using h
  have C0 : RootChain f a b 0 (N + 1) := by
    simpa [N, Nat.add_assoc] using initialRootChain f a b p q hab ha hb
  obtain ⟨CN⟩ := rootChain_iterate hcont C0 N (by omega) (by omega)
  have CN' : RootChain f a b N 1 := by
    convert CN using 1 <;> omega
  have hpoints : CN'.point 0 < CN'.point 1 := CN'.endpoint_lt (by norm_num)
  obtain ⟨c, hc, hder⟩ :=
    exists_deriv_eq_zero hpoints (hcont N le_rfl).continuousOn
      ((CN'.zeroAt 0 (by norm_num)).trans (CN'.zeroAt 1 le_rfl).symm)
  have hmem0 := CN'.mem 0 (by norm_num)
  have hmem1 := CN'.mem 1 le_rfl
  refine ⟨c, ⟨by linarith [hmem0.1, hc.1], by linarith [hmem1.2, hc.2]⟩, ?_⟩
  simpa [N, iterDeriv, Function.iterate_succ_apply'] using hder

private theorem contDiff_nat_of_le {f : ℝ → ℝ} {m n : ℕ}
    (hf : ContDiff ℝ n f) (hmn : m ≤ n) :
    ContDiff ℝ m f :=
  hf.of_le (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hmn))

theorem gap1 (f : ℝ → ℝ) (a b : ℝ) (p q : ℕ) (hab : a < b)
    (hpq : p = q) (ha : EndpointZero f a p) (hb : EndpointZero f b q)
    (hf : ContDiffOn ℝ (p + q + 1) f (Set.Icc a b)) :
    ∃ x ∈ Set.Ioo a b, deriv f x = 0 := by
  have hfa : f a = 0 := ha 0 (Nat.zero_le p)
  have hfb : f b = 0 := hb 0 (Nat.zero_le q)
  exact exists_deriv_eq_zero hab hf.continuousOn (hfa.trans hfb.symm)

theorem gap2 (f : ℝ → ℝ) (a b : ℝ) (p : ℕ) (hab : a < b)
    (ha : EndpointZero f a p) (hb : EndpointZero f b p)
    (hf : ContDiff ℝ (2 * p + 1) f) :
    ∃ x : ℕ → ℝ, ∀ k < p, x k ∈ Set.Ioo a b ∧
      iterDeriv p f (x k) = 0 := by
  by_cases hp0 : p = 0
  · subst p
    exact ⟨fun _ => a, by intro k hk; omega⟩
  · have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp0
    have ha' : EndpointZero f a (p - 1) :=
      fun j hj => ha j (by omega)
    have hb' : EndpointZero f b 0 :=
      fun j hj => hb j (by omega)
    have hsmooth : ContDiff ℝ ((p - 1) + 0 + 1) f :=
      contDiff_nat_of_le hf (by simp; omega)
    obtain ⟨c, hc, hzero⟩ :=
      generalized_rolle f a b (p - 1) 0 hab ha' hb' hsmooth
    refine ⟨fun _ => c, ?_⟩
    intro k hk
    exact ⟨hc, by simpa [Nat.sub_add_cancel hp] using hzero⟩

theorem gap3 (f : ℝ → ℝ) (a : ℝ) (p : ℕ) (ha : EndpointZero f a p) :
    iterDeriv p f a = 0 := by
  exact ha p le_rfl

theorem gap4 (f : ℝ → ℝ) (b : ℝ) (p : ℕ) (hb : EndpointZero f b p) :
    iterDeriv p f b = 0 := by
  exact hb p le_rfl

theorem gap5 (f : ℝ → ℝ) (a b : ℝ) (p q : ℕ) (hab : a < b)
    (ha : EndpointZero f a p) (hb : EndpointZero f b q)
    (hf : ContDiff ℝ (p + q + 1) f) :
    ∃ c ∈ Set.Ioo a b, iterDeriv (p + q + 1) f c = 0 := by
  exact generalized_rolle f a b p q hab ha hb hf

theorem gap6 (f : ℝ → ℝ) (a b : ℝ) (p k : ℕ) (hab : a < b)
    (hk : 1 ≤ k) (ha : EndpointZero f a p)
    (hb : EndpointZero f b (p + k))
    (hf : ContDiffOn ℝ (2 * p + k + 1) f (Set.Icc a b)) :
    ∃ ξ : ℕ → ℝ, ∀ j ≤ p, ξ j ∈ Set.Icc a b ∧
      iterDeriv (p + 1) f (ξ j) = 0 := by
  refine ⟨fun _ => b, ?_⟩
  intro j hj
  constructor
  · exact ⟨hab.le, le_rfl⟩
  · exact hb (p + 1) (by omega)

theorem gap7 (f : ℝ → ℝ) (b : ℝ) (p : ℕ)
    (hb : EndpointZero f b (p + 2)) :
    iterDeriv (p + 1) f b = iterDeriv (p + 2) f b := by
  rw [hb (p + 1) (by omega), hb (p + 2) le_rfl]

theorem gap8 (f : ℝ → ℝ) (b : ℝ) (p : ℕ)
    (hb : EndpointZero f b (p + 2)) :
    iterDeriv (p + 2) f b = 0 := by
  exact hb (p + 2) le_rfl

theorem gap9 (f : ℝ → ℝ) (b : ℝ) (p k : ℕ)
    (hk : 1 ≤ k) (hb : EndpointZero f b (p + k)) :
    iterDeriv (p + 1) f b = iterDeriv (p + k) f b := by
  rw [hb (p + 1) (by omega), hb (p + k) le_rfl]

theorem gap10 (f : ℝ → ℝ) (b : ℝ) (p k : ℕ)
    (hb : EndpointZero f b (p + k)) :
    iterDeriv (p + k) f b = 0 := by
  exact hb (p + k) le_rfl

theorem gap11 (f : ℝ → ℝ) (b : ℝ) (p k : ℕ)
    (hk : 1 ≤ k) (hb : EndpointZero f b (p + k)) :
    iterDeriv (p + 1) f b = 0 := by
  exact hb (p + 1) (by omega)

theorem gap12 (f : ℝ → ℝ) (a b : ℝ) (p k : ℕ) (hab : a < b)
    (hk : 1 ≤ k) (ha : EndpointZero f a p)
    (hb : EndpointZero f b (p + k))
    (hf : ContDiff ℝ (2 * p + k + 1) f) :
    ∃ ξ : ℕ → ℝ, ∀ j ≤ p, ξ j ∈ Set.Icc a b ∧
      iterDeriv (p + k + 1) f (ξ j) = 0 := by
  have ha0 : EndpointZero f a 0 :=
    fun j hj => ha j (by omega)
  have hsmooth : ContDiff ℝ (0 + (p + k) + 1) f :=
    contDiff_nat_of_le hf (by simp; omega)
  obtain ⟨c, hc, hzero⟩ :=
    generalized_rolle f a b 0 (p + k) hab ha0 hb hsmooth
  refine ⟨fun _ => c, ?_⟩
  intro j hj
  exact ⟨⟨hc.1.le, hc.2.le⟩, by simpa using hzero⟩

theorem gap13 (f : ℝ → ℝ) (a b : ℝ) (p k : ℕ) (hab : a < b)
    (hk : 1 ≤ k) (ha : EndpointZero f a p)
    (hb : EndpointZero f b (p + k))
    (hf : ContDiff ℝ (2 * p + k + 1) f) :
    ∃ c ∈ Set.Ioo a b, iterDeriv (p + k + p + 1) f c = 0 := by
  have h :=
    generalized_rolle f a b p (p + k) hab ha hb
      (contDiff_nat_of_le hf (by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        omega))
  rcases h with ⟨c, hc, hzero⟩
  refine ⟨c, hc, ?_⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzero

theorem gap14 (f : ℝ → ℝ) (a b : ℝ) (p q k : ℕ) (hab : a < b)
    (hq : q = p + k) (hk : 1 ≤ k)
    (ha : EndpointZero f a p) (hb : EndpointZero f b q)
    (hf : ContDiff ℝ (p + q + 1) f) :
    ∃ c ∈ Set.Ioo a b, iterDeriv (p + q + 1) f c = 0 := by
  exact generalized_rolle f a b p q hab ha hb hf

theorem gap15 (f : ℝ → ℝ) (a b : ℝ) (p q : ℕ) (hab : a < b)
    (ha : EndpointZero f a p) (hb : EndpointZero f b q)
    (hf : ContDiff ℝ (p + q + 1) f) :
    ∃ c ∈ Set.Ioo a b, iterDeriv (p + q + 1) f c = 0 := by
  exact generalized_rolle f a b p q hab ha hb hf

end

end ProofGap.Exercise1239
