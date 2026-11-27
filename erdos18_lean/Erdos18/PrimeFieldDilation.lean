import Erdos18.PrimeFieldEntropy
import Erdos18.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Erdos18/PrimeFieldDilation.lean — Elementary 2-Factor Smooth Pigeonhole Dilator (Module 2)

Formalizes Lemma 3 (zero character sums / zero Pólya–Vinogradov!) using the 2-factor smooth
pigeonhole dilator:
- `smoothSet m`: `{a ∈ Icc 1 (14 * m / 25) | ∀ p ∈ range (a + 1), p.Prime → p ∣ a → p ≤ 7 * m / 25}`.
- `smoothSet_mul_lt_sq`: `c₁ * c₂ < m^2` for all `c₁, c₂ ∈ smoothSet m` (`2 ≤ m`).
- `smoothSet_mul_dvd_factorial`: `c₁ * c₂ ∣ m!` for all `c₁, c₂ ∈ smoothSet m` (`16 ≤ m`).
- `smoothSet_card_ge`: `44 * (14 * m / 25) ≤ 45 * |smoothSet m|` for `m ≥ 4 * 4 ^ 45` (via `primorial_le_four_pow`).
- `two_factor_smooth_pigeonhole_count`: for prime `q` with `14 * m / 25 < q ≤ m` and `x ≠ 0` in `ZMod q`,
    `#{(c₁, c₂) ∈ smoothSet m ×ˢ smoothSet m | (c₁ : ZMod q) * (c₂ : ZMod q) = x} ≥ q / 20`.
- `two_factor_smooth_dilator_prob`: `dilatorWeight m q x ≥ (1 / 40) / (q - 1)` for all `x ≠ 0`.
- `two_factor_smooth_entropy_gain`: combines Lemma 2 (`PrimeFieldEntropy`) with Lemma 3.
-/

namespace Erdos18

open Finset Nat Real

/-! ## Definition and Elementary Arithmetic Properties of `smoothSet m` -/

/-- The `0.28 m`-smooth integers in `[1, ⌊0.56 m⌋]` (decidably filtered). -/
def smoothSet (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (14 * m / 25)).filter
    (fun a => ∀ p ∈ a.primeFactors, p ≤ 7 * m / 25)

lemma smoothSet_pos {m a : ℕ} (ha : a ∈ smoothSet m) : 0 < a := by
  unfold smoothSet at ha
  have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  omega

lemma smoothSet_le {m a : ℕ} (ha : a ∈ smoothSet m) : a ≤ 14 * m / 25 := by
  unfold smoothSet at ha
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2

lemma smoothSet_prime_dvd_le {m a p : ℕ} (ha : a ∈ smoothSet m) (hp : p.Prime) (hdvd : p ∣ a) :
    p ≤ 7 * m / 25 := by
  have ha_ne : a ≠ 0 := (smoothSet_pos ha).ne'
  have hp_mem : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, ha_ne⟩
  unfold smoothSet at ha
  exact (Finset.mem_filter.mp ha).2 p hp_mem

/-- Size bound: every 2-factor smooth product satisfies `c₁ * c₂ < m^2`. -/
theorem smoothSet_mul_lt_sq {m c₁ c₂ : ℕ} (hm : 2 ≤ m)
    (h1 : c₁ ∈ smoothSet m) (h2 : c₂ ∈ smoothSet m) :
    c₁ * c₂ < m ^ 2 := by
  have hc1 : c₁ < m := by have := smoothSet_le h1; omega
  have hc2 : c₂ < m := by have := smoothSet_le h2; omega
  rw [sq]
  exact Nat.mul_lt_mul'' hc1 hc2

/-- Helper: `p ^ (m / p) ∣ m!` for every `p, m : ℕ` (6-line induction). -/
private lemma pow_div_dvd_factorial (p m : ℕ) :
    p ^ (m / p) ∣ m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.succ_div]
    split_ifs with h
    · rw [_root_.pow_succ, mul_comm (p ^ (m / p)) p]
      exact mul_dvd_mul h ih
    · rw [add_zero]
      exact dvd_mul_of_dvd_right ih (m + 1)

/-- Helper: `2 * k ≤ p ^ (k - 1)` for `3 ≤ p` and `3 ≤ k`. -/
private lemma two_mul_le_pow_pred {p k : ℕ} (hp : 3 ≤ p) (hk : 3 ≤ k) :
    2 * k ≤ p ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    change 2 * 3 ≤ p ^ 2
    nlinarith
  | succ k hk ih =>
    have hstep : p ^ (k + 1 - 1) = p * p ^ (k - 1) := by
      have : k + 1 - 1 = (k - 1) + 1 := by omega
      rw [this, _root_.pow_succ']
    rw [hstep]
    nlinarith

/-- Helper: `4 * k ≤ 2 ^ k` for `4 ≤ k`. -/
private lemma four_mul_le_two_pow {k : ℕ} (hk : 4 ≤ k) : 4 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [_root_.pow_succ']
    omega

/-- Helper: if `m ≥ 16`, `p` is prime with `p ≤ 7 * m / 25`, and `p ^ k ≤ m`, then `2 * k ≤ m / p`. -/
private lemma two_mul_exp_le_div {m p k : ℕ} (hm : 16 ≤ m) (hp : p.Prime)
    (hp_le : p ≤ 7 * m / 25) (hpk : p ^ k ≤ m) :
    2 * k ≤ m / p := by
  rw [Nat.le_div_iff_mul_le hp.pos]
  by_cases hk0 : k = 0
  · subst hk0; simp
  by_cases hk1 : k = 1
  · subst hk1; omega
  by_cases hk2 : k = 2
  · subst hk2
    rw [pow_two] at hpk
    by_cases hp4 : 4 ≤ p
    · nlinarith
    · omega
  have hk3 : 3 ≤ k := by omega
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hk3' : k = 3
    · subst hk3'; omega
    · have hk4 : 4 ≤ k := by omega
      have := four_mul_le_two_pow hk4
      omega
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h1 := two_mul_le_pow_pred hp3 hk3
    have h2 : 2 * k * p ≤ p ^ (k - 1) * p := Nat.mul_le_mul_right p h1
    have h3 : p ^ (k - 1) * p = p ^ k := by
      have : k = (k - 1) + 1 := by omega
      conv_rhs => rw [this, _root_.pow_succ]
    omega

/-- Divisibility: every 2-factor smooth product divides `m!` for all `m ≥ 16`. -/
theorem smoothSet_mul_dvd_factorial {m c₁ c₂ : ℕ} (hm : 16 ≤ m)
    (h1 : c₁ ∈ smoothSet m) (h2 : c₂ ∈ smoothSet m) :
    c₁ * c₂ ∣ m.factorial := by
  have hc1_ne : c₁ ≠ 0 := (smoothSet_pos h1).ne'
  have hc2_ne : c₂ ≠ 0 := (smoothSet_pos h2).ne'
  rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hc1_ne hc2_ne) (Nat.factorial_ne_zero m)]
  intro p
  rw [Nat.factorization_mul hc1_ne hc2_ne, Finsupp.add_apply]
  by_cases hp : p.Prime
  · by_cases hd : p ∣ c₁ * c₂
    · have hp_le : p ≤ 7 * m / 25 := by
        rcases hp.dvd_mul.mp hd with hd1 | hd2
        · exact smoothSet_prime_dvd_le h1 hp hd1
        · exact smoothSet_prime_dvd_le h2 hp hd2
      set k := max (c₁.factorization p) (c₂.factorization p)
      have hpk : p ^ k ≤ m := by
        by_cases hmax : c₁.factorization p ≤ c₂.factorization p
        · have hk_eq : k = c₂.factorization p := max_eq_right hmax
          rw [hk_eq]
          have hdvd : p ^ (c₂.factorization p) ∣ c₂ := Nat.ordProj_dvd c₂ p
          exact (Nat.le_of_dvd (smoothSet_pos h2) hdvd).trans (by have := smoothSet_le h2; omega)
        · have hk_eq : k = c₁.factorization p := max_eq_left (le_of_not_ge hmax)
          rw [hk_eq]
          have hdvd : p ^ (c₁.factorization p) ∣ c₁ := Nat.ordProj_dvd c₁ p
          exact (Nat.le_of_dvd (smoothSet_pos h1) hdvd).trans (by have := smoothSet_le h1; omega)
      have h2k : c₁.factorization p + c₂.factorization p ≤ 2 * k := by omega
      have hle_div : 2 * k ≤ m / p := two_mul_exp_le_div hm hp hp_le hpk
      have hdiv_le_fac : m / p ≤ m.factorial.factorization p :=
        (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero m)).mp
          (pow_div_dvd_factorial p m)
      omega
    · have hd1 : ¬ (p ∣ c₁) := fun h => hd (dvd_mul_of_dvd_left h c₂)
      have hd2 : ¬ (p ∣ c₂) := fun h => hd (dvd_mul_of_dvd_right h c₁)
      rw [Nat.factorization_eq_zero_of_not_dvd hd1, Nat.factorization_eq_zero_of_not_dvd hd2]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime c₁ hp, Nat.factorization_eq_zero_of_not_prime c₂ hp]
    exact Nat.zero_le _

/-! ## Elementary Cardinality Lower Bound via `primorial_le_four_pow` -/

/-- Threshold for the elementary 2-factor smooth pigeonhole dilator: `m₁ = 4 * 4^45`. -/
def m1_pigeonhole : ℕ := 4 * 4 ^ 45

/-- Every element of `Icc 1 (14*m/25) \ smoothSet m` is a prime in `(7*m/25, 14*m/25]`. -/
private lemma sdiff_smoothSet_subset_primes (m : ℕ) :
    Finset.Icc 1 (14 * m / 25) \ smoothSet m ⊆
      (Finset.Ioc (7 * m / 25) (14 * m / 25)).filter Nat.Prime := by
  intro a ha
  rw [Finset.mem_sdiff] at ha
  have ha_icc : 1 ≤ a ∧ a ≤ 14 * m / 25 := Finset.mem_Icc.mp ha.1
  have hnot : ¬ ∀ p ∈ a.primeFactors, p ≤ 7 * m / 25 := fun hall =>
    ha.2 (Finset.mem_filter.mpr ⟨ha.1, hall⟩)
  push Not at hnot
  rcases hnot with ⟨p, hp_mem, hp_gt⟩
  rcases Nat.mem_primeFactors.mp hp_mem with ⟨hp, hdvd, _⟩
  rcases hdvd with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this, mul_zero] at hk
    omega
  have hk_eq1 : k = 1 := by
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    have h2p : 2 * p ≤ a := by rw [hk]; nlinarith
    omega
  rw [hk_eq1, mul_one] at hk
  subst hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp_gt, ha_icc.2⟩, hp⟩

/-- Chebyshev/primorial upper bound on the prime band `(7*m/25, 14*m/25]`:
for `m ≥ 4 * 4^45`, `45 * |primes in (7*m/25, 14*m/25]| ≤ 14 * m / 25`. -/
private lemma prime_band_card_le {m : ℕ} (hm : m1_pigeonhole ≤ m) :
    45 * ((Finset.Ioc (7 * m / 25) (14 * m / 25)).filter Nat.Prime).card ≤ 14 * m / 25 := by
  set S := (Finset.Ioc (7 * m / 25) (14 * m / 25)).filter Nat.Prime
  have hB_ge : 4 ^ 45 ≤ 7 * m / 25 := by
    unfold m1_pigeonhole at hm
    omega
  have hpow_le_prod : (4 ^ 45) ^ S.card ≤ ∏ p ∈ S, p := by
    calc (4 ^ 45) ^ S.card = ∏ _p ∈ S, 4 ^ 45 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ S, p := by
        apply Finset.prod_le_prod
        intro p hp
        have hp_gt : 7 * m / 25 < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        omega
  have hprod_le_prim : ∏ p ∈ S, p ≤ primorial (14 * m / 25) := by
    apply Nat.le_of_dvd (primorial_pos (14 * m / 25))
    unfold primorial
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hp ⊢
    exact ⟨Nat.lt_succ_of_le hp.1.2, hp.2⟩
  have hprim_le : primorial (14 * m / 25) ≤ 4 ^ (14 * m / 25) :=
    primorial_le_four_pow (14 * m / 25)
  have hpow : 4 ^ (45 * S.card) ≤ 4 ^ (14 * m / 25) := by
    rw [pow_mul]
    exact hpow_le_prod.trans (hprod_le_prim.trans hprim_le)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 4)).mp hpow

/-- Cardinality lower bound: for `m ≥ 4 * 4^45`, `45 * |smoothSet m| ≥ 44 * (14 * m / 25)`. -/
theorem smoothSet_card_ge {m : ℕ} (hm : m1_pigeonhole ≤ m) :
    44 * (14 * m / 25) ≤ 45 * (smoothSet m).card := by
  have hsub : smoothSet m ⊆ Finset.Icc 1 (14 * m / 25) := by
    unfold smoothSet; exact Finset.filter_subset _ _
  have hcard_sdiff : (Finset.Icc 1 (14 * m / 25) \ smoothSet m).card + (smoothSet m).card =
      (Finset.Icc 1 (14 * m / 25)).card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hcard_icc : (Finset.Icc 1 (14 * m / 25)).card = 14 * m / 25 := by
    rw [Nat.card_Icc]; omega
  have hsdiff_le : (Finset.Icc 1 (14 * m / 25) \ smoothSet m).card ≤
      ((Finset.Ioc (7 * m / 25) (14 * m / 25)).filter Nat.Prime).card :=
    Finset.card_le_card (sdiff_smoothSet_subset_primes m)
  have hband := prime_band_card_le hm
  have hle_tot : (smoothSet m).card ≤ 14 * m / 25 := by
    have := Finset.card_le_card hsub
    rwa [hcard_icc] at this
  omega

/-! ## 2-Factor Smooth Pigeonhole in `(ZMod q)ˣ` (Lemma 3) -/

/-- Exact 2-factor smooth pigeonhole count in `(ZMod q)ˣ`:
for prime `q` with `14 * m / 25 < q ≤ m` and `m ≥ 4 * 4^45`, every `x ≠ 0` in `ZMod q` has
at least `q / 20` representations `c₁ * c₂ ≡ x (mod q)` with `c₁, c₂ ∈ smoothSet m`. -/
theorem two_factor_smooth_pigeonhole_count {m q : ℕ} [Fact q.Prime]
    (hm : m1_pigeonhole ≤ m) (hq_lo : 14 * m / 25 < q) (hq_hi : q ≤ m)
    (x : ZMod q) (hx : x ≠ 0) :
    q / 20 ≤
      (((smoothSet m) ×ˢ (smoothSet m)).filter
        (fun p => ((p.1 : ZMod q) * (p.2 : ZMod q)) = x)).card := by
  set nz : Finset (ZMod q) := Finset.univ.filter (fun z : ZMod q => z ≠ 0)
  have hnz_card : nz.card = q - 1 := by
    have hfilt : nz = Finset.univ.erase (0 : ZMod q) := by ext z; simp [nz]
    rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod q)) (smoothSet m : Set ℕ) := by
    intro a ha b hb hab
    have ha_lt : a < q := lt_of_le_of_lt (smoothSet_le ha) hq_lo
    have hb_lt : b < q := lt_of_le_of_lt (smoothSet_le hb) hq_lo
    have hval := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hb_lt] at hval
  set Aq : Finset (ZMod q) := (smoothSet m).image (fun a : ℕ => (a : ZMod q))
  have hAq_card : Aq.card = (smoothSet m).card := Finset.card_image_of_injOn hinj
  have hAq_sub : Aq ⊆ nz := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro h0
    have ha_pos : 0 < a := smoothSet_pos ha
    have ha_lt : a < q := lt_of_le_of_lt (smoothSet_le ha) hq_lo
    have hval := congrArg ZMod.val h0
    rw [ZMod.val_natCast_of_lt ha_lt, ZMod.val_zero] at hval
    omega
  have hunit_of_mem : ∀ z ∈ Aq, IsUnit z := fun z hz =>
    zmod_isUnit_of_ne_zero (Finset.mem_filter.mp (hAq_sub hz)).2
  set Bq : Finset (ZMod q) := nz.filter (fun z => ∃ w ∈ Aq, z * w = x)
  have hBq_sub : Bq ⊆ nz := Finset.filter_subset _ _
  have hBq_card : Aq.card ≤ Bq.card := by
    -- Use Finset.card_le_card_of_injOn via noncomputable classical choice of unit inverse
    classical
    let f : ZMod q → ZMod q := fun w =>
      if hw : IsUnit w then x * ((hw.unit⁻¹ : (ZMod q)ˣ) : ZMod q) else 0
    have hf_mul : ∀ w ∈ Aq, f w * w = x := by
      intro w hw
      have hu : IsUnit w := hunit_of_mem w hw
      have hfw : f w = x * ((hu.unit⁻¹ : (ZMod q)ˣ) : ZMod q) := by
        simp [f, hu]
      rw [hfw, mul_assoc]
      have h1 : ((hu.unit⁻¹ : (ZMod q)ˣ) : ZMod q) * w = 1 := by
        have hspec : (hu.unit : ZMod q) = w := hu.unit_spec
        calc ((hu.unit⁻¹ : (ZMod q)ˣ) : ZMod q) * w
            = ((hu.unit⁻¹ : (ZMod q)ˣ) : ZMod q) * (hu.unit : ZMod q) := by rw [hspec]
          _ = (((hu.unit⁻¹ * hu.unit : (ZMod q)ˣ) : ZMod q)) := (Units.val_mul _ _).symm
          _ = 1 := by rw [inv_mul_cancel, Units.val_one]
      rw [h1, mul_one]
    have hf_maps : ∀ w ∈ Aq, f w ∈ Bq := by
      intro w hw
      have hmul := hf_mul w hw
      have hfw_ne : f w ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hmul; exact hx hmul.symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfw_ne⟩, ⟨w, hw, hmul⟩⟩
    have hf_inj : Set.InjOn f (Aq : Set (ZMod q)) := by
      intro w₁ hw₁ w₂ hw₂ heq
      have h1 := hf_mul w₁ hw₁
      have h2 := hf_mul w₂ hw₂
      have hfw_ne : f w₁ ≠ 0 := by
        intro h0; rw [h0, zero_mul] at h1; exact hx h1.symm
      rcases zmod_isUnit_of_ne_zero hfw_ne with ⟨uf, huf⟩
      have heq_mul : (uf : ZMod q) * w₁ = (uf : ZMod q) * w₂ := by
        rw [huf, h1, heq, h2]
      have hmul_inv := congrArg (fun z => ((uf⁻¹ : (ZMod q)ˣ) : ZMod q) * z) heq_mul
      simp only [← mul_assoc] at hmul_inv
      have hinv : ((uf⁻¹ : (ZMod q)ˣ) : ZMod q) * (uf : ZMod q) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      simpa [hinv] using hmul_inv
    calc Aq.card = (Aq.image f).card := (Finset.card_image_of_injOn hf_inj).symm
      _ ≤ Bq.card := Finset.card_le_card (Finset.image_subset_iff.mpr hf_maps)
  have hpigeon : 2 * Aq.card ≤ (Aq ∩ Bq).card + nz.card := by
    have hu := Finset.card_union_add_card_inter Aq Bq
    have hunion_le : (Aq ∪ Bq).card ≤ nz.card :=
      Finset.card_le_card (Finset.union_subset hAq_sub hBq_sub)
    omega
  set P := ((smoothSet m) ×ˢ (smoothSet m)).filter
    (fun p => ((p.1 : ZMod q) * (p.2 : ZMod q)) = x)
  have hinter_le_P : (Aq ∩ Bq).card ≤ P.card := by
    have hsurj : Aq ∩ Bq ⊆ P.image (fun p => (p.1 : ZMod q)) := by
      intro z hz
      rcases Finset.mem_inter.mp hz with ⟨hzA, hzB⟩
      rcases Finset.mem_image.mp hzA with ⟨c₁, hc₁, rfl⟩
      rcases (Finset.mem_filter.mp hzB).2 with ⟨w, hwA, hzw⟩
      rcases Finset.mem_image.mp hwA with ⟨c₂, hc₂, rfl⟩
      exact Finset.mem_image.mpr
        ⟨(c₁, c₂), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc₁, hc₂⟩, hzw⟩, rfl⟩
    exact (Finset.card_le_card hsurj).trans Finset.card_image_le
  have hcard_ge := smoothSet_card_ge hm
  have hm_big : 10000 ≤ m := by
    unfold m1_pigeonhole at hm
    have : 10000 ≤ 4 * 4 ^ 45 := by norm_num
    omega
  omega

/-- Normalized 2-factor smooth dilator probability weight on `ZMod q`:
`dilatorWeight m q x = #{(c₁, c₂) ∈ A × A | c₁ * c₂ = x mod q} / |A|^2`. -/
noncomputable def dilatorWeight (m q : ℕ) (x : ZMod q) : ℝ :=
  ((((smoothSet m) ×ˢ (smoothSet m)).filter
    (fun p => ((p.1 : ZMod q) * (p.2 : ZMod q)) = x)).card : ℝ) /
    ((smoothSet m).card : ℝ) ^ 2

/-- **Lemma 3a (Uniform Lower Bound for 2-Factor Smooth Dilator):**
For `m ≥ 4 * 4^45` and prime `q` with `14 * m / 25 < q ≤ m`, every `x ≠ 0` in `ZMod q`
satisfies `dilatorWeight m q x ≥ (1 / 40) / (q - 1)`. -/
theorem two_factor_smooth_dilator_prob {m q : ℕ} [Fact q.Prime]
    (hm : m1_pigeonhole ≤ m) (hq_lo : 14 * m / 25 < q) (hq_hi : q ≤ m)
    (x : ZMod q) (hx : x ≠ 0) :
    (1 / 40 : ℝ) / ((q : ℝ) - 1) ≤ dilatorWeight m q x := by
  have hcount := two_factor_smooth_pigeonhole_count hm hq_lo hq_hi x hx
  have hcard_ge := smoothSet_card_ge hm
  have hm_big : 10000 ≤ m := by
    unfold m1_pigeonhole at hm
    have : 10000 ≤ 4 * 4 ^ 45 := by norm_num
    omega
  have hq_big : 1000 ≤ q := by omega
  have hA_pos : (0 : ℝ) < ((smoothSet m).card : ℝ) := by
    have : 0 < (smoothSet m).card := by omega
    exact_mod_cast this
  have hA_le_q : ((smoothSet m).card : ℝ) ≤ (q : ℝ) := by
    have hsub : smoothSet m ⊆ Finset.Icc 1 (14 * m / 25) := by
      unfold smoothSet; exact Finset.filter_subset _ _
    have hcard : (smoothSet m).card ≤ 14 * m / 25 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this; omega
    exact_mod_cast (le_trans hcard hq_lo.le)
  have hq_real : (1000 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_big
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hcount_real : ((q / 20 : ℕ) : ℝ) ≤
      ((((smoothSet m) ×ˢ (smoothSet m)).filter
        (fun p => ((p.1 : ZMod q) * (p.2 : ZMod q)) = x)).card : ℝ) := by
    exact_mod_cast hcount
  have hq21 : (q : ℝ) / 21 ≤ ((q / 20 : ℕ) : ℝ) := by
    have : q ≤ 20 * (q / 20) + 19 := by omega
    have hcast : (q : ℝ) ≤ 20 * ((q / 20 : ℕ) : ℝ) + 19 := by exact_mod_cast this
    linarith
  unfold dilatorWeight
  have h1 : (1 / 40 : ℝ) / ((q : ℝ) - 1) ≤ ((q : ℝ) / 21) / ((q : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ hq1_pos (by positivity)]
    nlinarith
  have h2 : ((q : ℝ) / 21) / ((q : ℝ) ^ 2) ≤ ((q / 20 : ℕ) : ℝ) / ((smoothSet m).card : ℝ) ^ 2 := by
    apply div_le_div₀ (by positivity) hq21 (by positivity)
    exact pow_le_pow_left₀ hA_pos.le hA_le_q 2
  have h3 : ((q / 20 : ℕ) : ℝ) / ((smoothSet m).card : ℝ) ^ 2 ≤
      ((((smoothSet m) ×ˢ (smoothSet m)).filter
        (fun p => ((p.1 : ZMod q) * (p.2 : ZMod q)) = x)).card : ℝ) /
        ((smoothSet m).card : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hcount_real (sq_nonneg _)
  exact h1.trans (h2.trans h3)

/-- **Lemma 3b (2-Factor Smooth Dilator Entropy-Gain Theorem):**
Combines `fq_general_dilation_entropy_gain` (Lemma 2) with `two_factor_smooth_dilator_prob` (Lemma 3a):
for `m ≥ 4 * 4^45`, prime `q` with `14 * m / 25 < q ≤ m`, and independent `U, V` on `ZMod q`,
`((1 / 40) / (2420 * log q)) * (Hnat(V) - 5 * log q / q) * deficit(U) ≤
  ∑_{c ≠ 0} dilatorWeight m q c * (Hnat(U + cV) - Hnat(U))`. -/
theorem two_factor_smooth_entropy_gain {m q : ℕ} [Fact q.Prime]
    (hm : m1_pigeonhole ≤ m) (hq_lo : 14 * m / 25 < q) (hq_hi : q ≤ m)
    (U V : PMF_ZMod q) :
    ((1 / 40 : ℝ) / (2420 * Real.log (q : ℝ))) *
        (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) * deficit_zmod U ≤
      ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0),
        dilatorWeight m q c * (Hnat_zmod (conv_dilate U V c) - Hnat_zmod U) := by
  have hq3 : 3 ≤ q := by
    unfold m1_pigeonhole at hm
    have : 10000 ≤ 4 * 4 ^ 45 := by norm_num
    omega
  exact fq_general_dilation_entropy_gain hq3 U V (dilatorWeight m q) (by norm_num)
    (fun c hc => two_factor_smooth_dilator_prob hm hq_lo hq_hi c hc)

end Erdos18
