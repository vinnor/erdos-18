import Erdos18.PrimeFieldCovering
import Erdos18.MainTheorem
import Erdos18.Alpha3Main

/-!
# Erdos18/PrimeFieldMain.lean — Unconditional `h(n!) = O((log n)^3 log log(n + 16))`

Completes the Lean 4 formalization of the prime-field dilation proof for Erdős Problem #18:
1. `M_core_practical`: `M_core m` is practical for every `m ≥ 20`.
2. `exists_primefield_threshold`: constructs a clean threshold `m_pf` above which
   - `2 * R_cover m ≤ Q_tag.card`,
   - `2 ^ (⌊(c_band / 8) * m⌋) ≤ ((∏ q ∈ Q_strip, q) / m ^ 5) / m`,
   - `2 * R_cover m + (16 * Nat.log 2 m + 18) ≤ C_dig * (Real.log m) ^ 2 * Real.log (Real.log (m + 16))`.
3. `stage2_tail_recursion_primefield`: strong induction `m → m / 2` with Branch A (small digit),
   Branch B (11-prime strip), and Branch C (`mod_Mprime_covering` + `mixed_radix_stage1` on `U_extra`).
4. `Erdos18.erdos18_alpha3_loglog1`: headline theorem `h(n!) = O((log n)^3 log log(n + 16))`.
-/

namespace Erdos18

open Finset Nat Real

/-! ## Part 1: Practicality of `M_core m` for `m ≥ 20` -/

/-- If `M` is practical and every prime factor of `N ≥ 1` is `≤ M`, then `M * N` is practical. -/
private lemma practical_mul_of_primes_le : ∀ (N M : ℕ),
    1 ≤ N →
    (∀ x < M, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = x) →
    (∀ p : ℕ, p.Prime → p ∣ N → p ≤ M) →
    ∀ x < M * N, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M * N) ∧ S.sum id = x := by
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro M hN hM hP x hx
    by_cases hN1 : N = 1
    · subst hN1; simpa using hM x (by simpa using hx)
    · set p : ℕ := N.minFac
      have hp_prime : p.Prime := Nat.minFac_prime hN1
      have hp_dvd : p ∣ N := Nat.minFac_dvd N
      have hp_le : p ≤ M := hP p hp_prime hp_dvd
      have hMp : ∀ y < M * p, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M * p) ∧ S.sum id = y :=
        practical_mul_step hp_prime.pos hp_le hM
      set N' : ℕ := N / p
      have hN_eq : p * N' = N := Nat.mul_div_cancel' hp_dvd
      have hN'_pos : 1 ≤ N' := by
        by_contra h0; push Not at h0
        have h0' : N' = 0 := Nat.lt_one_iff.mp h0
        rw [h0', mul_zero] at hN_eq; omega
      have hN'_lt : N' < N := by
        have h2 : 2 ≤ p := hp_prime.two_le
        have hle : 2 * N' ≤ p * N' := Nat.mul_le_mul_right N' h2
        rw [hN_eq] at hle; omega
      have hP' : ∀ q : ℕ, q.Prime → q ∣ N' → q ≤ M * p := fun q hq hqd =>
        le_trans (hP q hq (dvd_trans hqd ⟨p, by linarith⟩)) (Nat.le_mul_of_pos_right M hp_prime.pos)
      have hrew : M * N = (M * p) * N' := by rw [← hN_eq]; ring
      rw [hrew] at hx ⊢
      exact ih N' hN'_lt (M * p) hN'_pos hMp hP' x hx

/-- For every `k ≥ 5`, `4 * k + 3 ≤ 2 ^ k`. -/
private lemma four_mul_add_three_le_two_pow {k : ℕ} (hk : 5 ≤ k) : 4 * k + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [_root_.pow_succ']; omega

/-- For every `m ≥ 20`, `m ≤ 2 ^ (m / 4)`. -/
private lemma le_two_pow_div4 {m : ℕ} (hm : 20 ≤ m) : m ≤ 2 ^ (m / 4) := by
  have hk : 5 ≤ m / 4 := by omega
  have h1 := four_mul_add_three_le_two_pow hk
  omega

/-- If a prime `p` divides `∏ q ∈ s, q`, then `p ∣ q` for some `q ∈ s`. -/
private lemma prime_dvd_finset_prod_pf {p : ℕ} (hp : p.Prime) {s : Finset ℕ} (h : p ∣ ∏ q ∈ s, q) :
    ∃ q ∈ s, p ∣ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h; exact absurd h hp.ne_one
  | insert a t ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a t, h1⟩
    · rcases ih h2 with ⟨q, hq, hpq⟩
      exact ⟨q, Finset.mem_insert_of_mem hq, hpq⟩

/-- Every prime dividing `primorial n` is `≤ n`. -/
private lemma prime_dvd_primorial_le {n p : ℕ} (hp : p.Prime) (hdvd : p ∣ primorial n) : p ≤ n := by
  unfold primorial at hdvd
  rcases prime_dvd_finset_prod_pf hp hdvd with ⟨q, hq_mem, hpq⟩
  have hq_p : q.Prime := (Finset.mem_filter.mp hq_mem).2
  have hq_le : q ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hq_mem).1)
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_p).mp hpq
  omega

/-- `M_core m` is practical for every `m ≥ 20`. -/
lemma M_core_practical {m : ℕ} (hm : 20 ≤ m) :
    ∀ x < M_core m, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M_core m) ∧ S.sum id = x := by
  set M : ℕ := 2 ^ (m / 4)
  set N : ℕ := primorial m * (primorial (m / 3)) ^ 2 * (primorial (Nat.sqrt m)) ^ (2 * Nat.log 2 m)
  have hM_core : M_core m = M * N := by unfold M_core; dsimp [M, N]; ring
  rw [hM_core]
  refine practical_mul_of_primes_le N M ?_ ?_ ?_
  · exact mul_pos (mul_pos (primorial_pos m) (pow_pos (primorial_pos _) 2))
      (pow_pos (primorial_pos _) _)
  · intro x hx
    rcases binary_rep_pow2 (m / 4) x hx with ⟨S, _, hprop, hsum⟩
    exact ⟨S, fun d hd => ⟨(hprop d hd).1, (hprop d hd).2.1⟩, hsum⟩
  · intro p hp hpd
    have hp_le_m : p ≤ m := by
      rcases hp.dvd_mul.mp hpd with h1 | h3
      · rcases hp.dvd_mul.mp h1 with hm_d | h3_d
        · exact prime_dvd_primorial_le hp hm_d
        · exact le_trans (prime_dvd_primorial_le hp (hp.dvd_of_dvd_pow h3_d)) (Nat.div_le_self m 3)
      · exact le_trans (prime_dvd_primorial_le hp (hp.dvd_of_dvd_pow h3)) (Nat.sqrt_le_self m)
    exact le_trans hp_le_m (le_two_pow_div4 hm)

/-! ## Part 2: Asymptotic Thresholds & Helper Bounds -/

/-- Upper bound on `R_cover m` in terms of `(log m)^2 * log log (m + 16)` for `m ≥ 4096`. -/
private lemma R_cover_le_const {m : ℕ} (hm4096 : 4096 ≤ m) :
    (2 * R_cover m + (16 * Nat.log 2 m + 18) : ℝ) ≤
      6000000 * (Real.log (m : ℝ)) ^ 2 * Real.log (Real.log ((m : ℝ) + 16)) := by
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogm_ge4 : (4 : ℝ) ≤ Real.log (m : ℝ) := by
    have h1 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    have h2 : Real.log ((2 : ℝ) ^ 12) ≤ Real.log (m : ℝ) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow] at h2; push_cast at h2; linarith [Real.log_two_gt_d9]
  have hll_gt1 : 1 < Real.log (Real.log ((m : ℝ) + 16)) := one_lt_log_log_add16_all m
  have hlog12m : Real.log (12 * (m : ℝ)) ≤ 2 * Real.log (m : ℝ) := by
    rw [Real.log_mul (by norm_num) hm_pos.ne']
    have h12 : Real.log (12 : ℝ) < 3 := by
      have h := Real.log_lt_log (by norm_num) (show (12 : ℝ) < 2 ^ 4 by norm_num)
      rw [Real.log_pow] at h; push_cast at h; linarith [Real.log_two_lt_d9]
    linarith
  have hll_plus4 : Real.log (Real.log ((m : ℝ) + 16)) + 4 ≤ 5 * Real.log (Real.log ((m : ℝ) + 16)) := by
    linarith
  have hR_le : (R_cover m : ℝ) ≤
      193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) * Real.log (12 * (m : ℝ)) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) (Real.log_nonneg (by linarith)))).le
  have hprod : Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) * Real.log (12 * (m : ℝ)) ≤
      10 * (Real.log (m : ℝ)) ^ 2 * Real.log (Real.log ((m : ℝ) + 16)) := by
    have h1 : Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) ≤
        Real.log (m : ℝ) * (5 * Real.log (Real.log ((m : ℝ) + 16))) :=
      mul_le_mul_of_nonneg_left hll_plus4 (by linarith)
    have h2 : Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) * Real.log (12 * (m : ℝ)) ≤
        (Real.log (m : ℝ) * (5 * Real.log (Real.log ((m : ℝ) + 16)))) * (2 * Real.log (m : ℝ)) :=
      mul_le_mul h1 hlog12m (Real.log_nonneg (by linarith)) (by positivity)
    linarith [show (Real.log (m : ℝ) * (5 * Real.log (Real.log ((m : ℝ) + 16)))) * (2 * Real.log (m : ℝ)) =
      10 * (Real.log (m : ℝ)) ^ 2 * Real.log (Real.log ((m : ℝ) + 16)) by ring]
  have hlog2m : ((Nat.log 2 m : ℕ) : ℝ) ≤ 2 * Real.log (m : ℝ) := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at hlog
    have h2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have hbase : (1 : ℝ) ≤ (Real.log (m : ℝ)) ^ 2 * Real.log (Real.log ((m : ℝ) + 16)) := by
    have h1 : (16 : ℝ) ≤ (Real.log (m : ℝ)) ^ 2 := by nlinarith
    nlinarith
  have hlin : Real.log (m : ℝ) ≤ (Real.log (m : ℝ)) ^ 2 * Real.log (Real.log ((m : ℝ) + 16)) := by
    have h1 : Real.log (m : ℝ) ≤ (Real.log (m : ℝ)) ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- For `m ≥ 4096` and `Q_strip` with `c_band * m / log m ≤ Q_strip.card` and `∀ q ∈ Q_strip, m / 2 < q`:
    `log (∏ q ∈ Q_strip, q) ≥ (c_band / 2) * m`. -/
private lemma log_prod_Qstrip_ge {m : ℕ} {c_band : ℝ} {Q_strip : Finset ℕ}
    (hm4096 : 4096 ≤ m) (hc_pos : 0 < c_band)
    (hQ_gt : ∀ q ∈ Q_strip, m / 2 < q)
    (hQ_card : c_band * (m : ℝ) / Real.log (m : ℝ) ≤ (Q_strip.card : ℝ)) :
    (c_band / 2) * (m : ℝ) ≤ Real.log ((∏ q ∈ Q_strip, q : ℕ) : ℝ) := by
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  rw [Nat.cast_prod, Real.log_prod (fun q hq => by have := hQ_gt q hq; exact Nat.cast_ne_zero.mpr (by omega))]
  have hterm : ∀ q ∈ Q_strip, (1 / 2 : ℝ) * Real.log (m : ℝ) ≤ Real.log (q : ℝ) := by
    intro q hq
    have hq_ge : Real.sqrt (m : ℝ) ≤ (q : ℝ) := by
      have hq1 : (m : ℝ) / 2 ≤ (q : ℝ) := by
        have : m / 2 + 1 ≤ q := hQ_gt q hq
        have hcast : ((m / 2 : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast this
        have hdiv : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : m ≤ 2 * (m / 2) + 1)
        linarith
      have hsq : Real.sqrt (m : ℝ) ≤ (m : ℝ) / 2 := by
        have h2 : (2 : ℝ) ≤ Real.sqrt (m : ℝ) := by
          calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
            _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by linarith)
        nlinarith [Real.sq_sqrt hm_pos.le]
      linarith
    have hlog := Real.log_le_log (Real.sqrt_pos.mpr hm_pos) hq_ge
    rw [Real.log_sqrt hm_pos.le] at hlog
    linarith
  have hsum : (Q_strip.card : ℝ) * ((1 / 2 : ℝ) * Real.log (m : ℝ)) ≤ ∑ q ∈ Q_strip, Real.log (q : ℝ) := by
    calc (Q_strip.card : ℝ) * ((1 / 2 : ℝ) * Real.log (m : ℝ))
        = ∑ _ ∈ Q_strip, ((1 / 2 : ℝ) * Real.log (m : ℝ)) := by simp
      _ ≤ ∑ q ∈ Q_strip, Real.log (q : ℝ) := Finset.sum_le_sum hterm
  have hmul : (c_band * (m : ℝ) / Real.log (m : ℝ)) * ((1 / 2 : ℝ) * Real.log (m : ℝ)) ≤
      (Q_strip.card : ℝ) * ((1 / 2 : ℝ) * Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_right hQ_card (by positivity)
  have hsimp : (c_band * (m : ℝ) / Real.log (m : ℝ)) * ((1 / 2 : ℝ) * Real.log (m : ℝ)) =
      (c_band / 2) * (m : ℝ) := by
    field_simp [hlogm_pos.ne']
  linarith

/-- Master asymptotic threshold `m_pf` given `(c_band, m_band)` from `exists_prime_band`:
    for all `m ≥ m_pf`:
    1. `2 * R_cover m ≤ c_band * m / Real.log m` (hence `2 * R_cover m ≤ Q_tag.card`),
    2. `12 * Real.log m + 4 ≤ (c_band / 4) * m` (hence `K_m / m ≥ 2 ^ (⌊(c_band / 8) * m⌋)` and `m ≤ K_m`),
    3. `m / 2 ≥ m_band` and `m ≥ 16384`. -/
private lemma exists_primefield_threshold {c_band : ℝ} {m_band : ℕ}
    (hc_pos : 0 < c_band) :
    ∃ m_pf : ℕ, max (max (2 * m_band + 4) 16384) (Nat.ceil (64 / c_band) + 16) ≤ m_pf ∧
      ∀ m : ℕ, m_pf ≤ m →
        (2 * R_cover m : ℝ) ≤ c_band * (m : ℝ) / Real.log (m : ℝ) ∧
        12 * Real.log (m : ℝ) + 4 ≤ (c_band / 4) * (m : ℝ) := by
  -- Use u = m^(1/8) = sqrt(sqrt(sqrt m)), so log m ≤ 8 * u and u^4 = sqrt m.
  set K : ℕ := Nat.ceil (max (5000000000 / c_band) (1000 / c_band)) + 64
  set m_pf : ℕ := max (max (max (2 * m_band + 4) 16384) (Nat.ceil (64 / c_band) + 16)) (K ^ 2)
  refine ⟨m_pf, le_max_left _ _, ?_⟩
  intro m hm
  have hm16 : 16384 ≤ m := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hm
  have hmK2 : K ^ 2 ≤ m := le_trans (le_max_right _ _) hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 4096 ≤ m)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  set s : ℝ := Real.sqrt (m : ℝ)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hm_pos
  have hs_geK : (K : ℝ) ≤ s := by
    have hK2 : (K : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hmK2
    calc (K : ℝ) = Real.sqrt ((K : ℝ) ^ 2) := (Real.sqrt_sq (Nat.cast_nonneg K)).symm
      _ ≤ s := Real.sqrt_le_sqrt hK2
  have hs_ge64 : (64 : ℝ) ≤ s := by
    have : (64 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 64 ≤ K)
    linarith
  have hs_sq : s * s = (m : ℝ) := Real.mul_self_sqrt hm_pos.le
  set u : ℝ := Real.sqrt (Real.sqrt s)
  have hu_pos : 0 < u := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hs_pos)
  have hu4 : u ^ 4 = s := by
    have h1 : u ^ 2 = Real.sqrt s := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = (Real.sqrt s) ^ 2 := by rw [h1]
      _ = s := Real.sq_sqrt hs_pos.le
  have hu8 : u ^ 8 = (m : ℝ) := by
    calc u ^ 8 = u ^ 4 * u ^ 4 := by ring
      _ = s * s := by rw [hu4]
      _ = (m : ℝ) := hs_sq
  have hu_ge1 : (1 : ℝ) ≤ u := by
    have h1 : (1 : ℝ) ≤ Real.sqrt s := by
      calc (1 : ℝ) = Real.sqrt (1 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt s := Real.sqrt_le_sqrt (by linarith)
    calc (1 : ℝ) = Real.sqrt (1 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ u := Real.sqrt_le_sqrt (by linarith)
  have hlogm_u : Real.log (m : ℝ) ≤ 8 * u := by
    have h1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu_pos
    have h2 : Real.log (m : ℝ) = 8 * Real.log u := by rw [← hu8, Real.log_pow]; ring
    linarith
  have hlog12m_u : Real.log (12 * (m : ℝ)) ≤ 11 * u := by
    rw [Real.log_mul (by norm_num) hm_pos.ne']
    have h12 : Real.log (12 : ℝ) < 3 := by
      have h := Real.log_lt_log (by norm_num) (show (12 : ℝ) < 2 ^ 4 by norm_num)
      rw [Real.log_pow] at h; push_cast at h; linarith [Real.log_two_lt_d9]
    linarith
  have hll_u : Real.log (Real.log ((m : ℝ) + 16)) + 4 ≤ 15 * u := by
    have hm16 : (m : ℝ) + 16 ≤ 2 * (m : ℝ) := by linarith
    have hlog_m16 : Real.log ((m : ℝ) + 16) ≤ 8 * u + 1 := by
      have h1 := Real.log_le_log (by positivity) hm16
      rw [Real.log_mul (by norm_num) hm_pos.ne'] at h1
      linarith [Real.log_two_lt_d9]
    have hlog16_pos : 0 < Real.log ((m : ℝ) + 16) := Real.log_pos (by linarith)
    have h2 : Real.log (Real.log ((m : ℝ) + 16)) ≤ Real.log ((m : ℝ) + 16) - 1 :=
      Real.log_le_sub_one_of_pos hlog16_pos
    linarith
  constructor
  · -- (2 * R_cover m) ≤ c_band * m / log m
    rw [le_div_iff₀ hlogm_pos]
    have hR_le : (R_cover m : ℝ) ≤
        193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) * Real.log (12 * (m : ℝ)) + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlogm_pos.le) (by linarith [one_lt_log_log_add16_all m])) (Real.log_nonneg (by linarith)))).le
    have hlogm_nn : 0 ≤ Real.log (m : ℝ) := hlogm_pos.le
    have hll_nn : 0 ≤ Real.log (Real.log ((m : ℝ) + 16)) + 4 := by
      have := one_lt_log_log_add16_all m; linarith
    have h12_nn : 0 ≤ Real.log (12 * (m : ℝ)) := Real.log_nonneg (by linarith)
    have h1 : Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) ≤ (8 * u) * (15 * u) :=
      mul_le_mul hlogm_u hll_u hll_nn (by positivity)
    have h2 : Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) * Real.log (12 * (m : ℝ)) ≤
        (8 * u) * (15 * u) * (11 * u) :=
      mul_le_mul h1 hlog12m_u h12_nn (by positivity)
    have hu3_le : u ^ 3 ≤ u ^ 4 := by
      have : u ^ 3 * 1 ≤ u ^ 3 * u := mul_le_mul_of_nonneg_left hu_ge1 (by positivity)
      linarith [show u ^ 3 * u = u ^ 4 by ring]
    have hR_u : (2 * R_cover m : ℝ) ≤ 520000000 * u ^ 3 := by
      have h1_u3 : (1 : ℝ) ≤ u ^ 3 := one_le_pow₀ hu_ge1
      nlinarith [show (8 * u) * (15 * u) * (11 * u) = 1320 * u ^ 3 by ring]
    have hprod_le : (2 * R_cover m : ℝ) * Real.log (m : ℝ) ≤ 5000000000 * s := by
      have hmul := mul_le_mul hR_u hlogm_u hlogm_nn (by positivity)
      linarith [show 520000000 * u ^ 3 * (8 * u) = 4160000000 * u ^ 4 by ring, hu4]
    have h5e9 : 5000000000 / c_band ≤ s := by
      have hle1 : 5000000000 / c_band ≤ max (5000000000 / c_band) (1000 / c_band) := le_max_left _ _
      have hle2 : max (5000000000 / c_band) (1000 / c_band) ≤ (K : ℝ) := by
        have hceil := Nat.le_ceil (max (5000000000 / c_band) (1000 / c_band))
        have hK : (Nat.ceil (max (5000000000 / c_band) (1000 / c_band)) : ℝ) ≤ (K : ℝ) := by
          dsimp only [K]; exact_mod_cast Nat.le_add_right (Nat.ceil (max (5000000000 / c_band) (1000 / c_band))) 64
        linarith
      linarith
    have hcs : (5000000000 : ℝ) ≤ c_band * s := by linarith [(div_le_iff₀ hc_pos).mp h5e9]
    have hcm : 5000000000 * s ≤ c_band * (m : ℝ) := by
      have := mul_le_mul_of_nonneg_right hcs hs_pos.le
      linarith [show c_band * s * s = c_band * (m : ℝ) by rw [mul_assoc, hs_sq]]
    linarith
  · -- 12 * log m + 4 ≤ (c_band / 4) * m
    have h1000 : 1000 / c_band ≤ s := by
      have hle1 : 1000 / c_band ≤ max (5000000000 / c_band) (1000 / c_band) := le_max_right _ _
      have hle2 : max (5000000000 / c_band) (1000 / c_band) ≤ (K : ℝ) := by
        have hceil := Nat.le_ceil (max (5000000000 / c_band) (1000 / c_band))
        have hK : (Nat.ceil (max (5000000000 / c_band) (1000 / c_band)) : ℝ) ≤ (K : ℝ) := by
          dsimp only [K]; exact_mod_cast Nat.le_add_right (Nat.ceil (max (5000000000 / c_band) (1000 / c_band))) 64
        linarith
      linarith
    have hcs : (1000 : ℝ) ≤ c_band * s := by linarith [(div_le_iff₀ hc_pos).mp h1000]
    have hlogm_s : Real.log (m : ℝ) ≤ 2 * s := by
      have h1 := Real.log_le_sub_one_of_pos hs_pos
      have h2 : Real.log (m : ℝ) = 2 * Real.log s := by rw [← hs_sq, ← pow_two, Real.log_pow]; ring
      linarith
    have hcm : 1000 * s ≤ c_band * (m : ℝ) := by
      have := mul_le_mul_of_nonneg_right hcs hs_pos.le
      linarith [show c_band * s * s = c_band * (m : ℝ) by rw [mul_assoc, hs_sq]]
    nlinarith

/-- Helper: from `log M_strip ≥ (c_band / 2) * m` and `12 * log m + 4 ≤ (c_band / 4) * m`,
    we get `m ≤ M_strip / m ^ 5` and `2 ^ (Nat.floor ((c_band / 8) * m)) ≤ (M_strip / m ^ 5) / m`. -/
private lemma K_strip_exponential_lower {m M_strip : ℕ} {c_band : ℝ}
    (hm4096 : 4096 ≤ m) (hc_pos : 0 < c_band) (hM_pos : 0 < M_strip)
    (hlogM : (c_band / 2) * (m : ℝ) ≤ Real.log (M_strip : ℝ))
    (hthresh : 12 * Real.log (m : ℝ) + 4 ≤ (c_band / 4) * (m : ℝ)) :
    m ≤ M_strip / m ^ 5 ∧
    2 ^ (Nat.floor ((c_band / 8) * (m : ℝ))) ≤ (M_strip / m ^ 5) / m := by
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  set e : ℕ := Nat.floor ((c_band / 8) * (m : ℝ))
  have he_le : (e : ℝ) ≤ (c_band / 8) * (m : ℝ) := Nat.floor_le (by positivity)
  -- Show 2 * m^6 * 2^e ≤ M_strip
  have hlog_lhs : Real.log (2 * (m : ℝ) ^ 6 * (2 : ℝ) ^ e) ≤ Real.log (M_strip : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, Real.log_pow]; push_cast
    have hlog2 : Real.log (2 : ℝ) < 1 := by linarith [Real.log_two_lt_d9]
    have h2e : (e : ℝ) * Real.log 2 ≤ (c_band / 8) * (m : ℝ) := by
      calc (e : ℝ) * Real.log 2 ≤ ((c_band / 8) * (m : ℝ)) * 1 :=
            mul_le_mul he_le hlog2.le (Real.log_nonneg (by norm_num)) (by positivity)
        _ = (c_band / 8) * (m : ℝ) := mul_one _
    have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
    linarith
  have hreal_le : 2 * (m : ℝ) ^ 6 * (2 : ℝ) ^ e ≤ (M_strip : ℝ) :=
    (Real.log_le_log_iff (by positivity) (Nat.cast_pos.mpr hM_pos)).mp hlog_lhs
  have hnat_le : 2 * m ^ 6 * 2 ^ e ≤ M_strip := by exact_mod_cast hreal_le
  have hm6_le : m * m ^ 5 ≤ M_strip := by
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num)
    calc m * m ^ 5 = m ^ 6 := by ring
      _ = m ^ 6 * 1 := by ring
      _ ≤ (2 * m ^ 6) * 2 ^ e := Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (by norm_num)) h1
      _ ≤ M_strip := hnat_le
  constructor
  · exact (Nat.le_div_iff_mul_le (by positivity)).mpr hm6_le
  · rw [Nat.div_div_eq_div_mul]
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by
      calc 2 ^ e * (m ^ 5 * m) = m ^ 6 * 2 ^ e := by ring
        _ ≤ (2 * m ^ 6) * 2 ^ e := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by norm_num))
        _ ≤ M_strip := hnat_le)

/-- Helper: `2 * m ^ 10 ≤ (m / 2) ^ 11` for `m ≥ 16384`. -/
private lemma two_mul_pow10_le_half_pow11 {m : ℕ} (hm : 16384 ≤ m) :
    2 * m ^ 10 ≤ (m / 2) ^ 11 := by
  have h49 : (49 / 100 : ℝ) * (m : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by
    have h1 : m ≤ 2 * (m / 2) + 1 := by omega
    have h2 : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    have h3 : (16384 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hpow : ((49 / 100 : ℝ) * (m : ℝ)) ^ 11 ≤ ((m / 2 : ℕ) : ℝ) ^ 11 :=
    pow_le_pow_left₀ (by positivity) h49 11
  have hcoef : (2 : ℝ) ≤ (49 / 100 : ℝ) ^ 11 * (16384 : ℝ) := by norm_num
  have hm16 : (16384 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hreal : 2 * (m : ℝ) ^ 10 ≤ ((m / 2 : ℕ) : ℝ) ^ 11 := by
    have h1 : 2 * (m : ℝ) ^ 10 ≤ ((49 / 100 : ℝ) ^ 11 * (m : ℝ)) * (m : ℝ) ^ 10 := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : (49 / 100 : ℝ) ^ 11 * 16384 ≤ (49 / 100 : ℝ) ^ 11 * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hm16 (by positivity)
      linarith
    have h2 : ((49 / 100 : ℝ) ^ 11 * (m : ℝ)) * (m : ℝ) ^ 10 = ((49 / 100 : ℝ) * (m : ℝ)) ^ 11 := by ring
    linarith
  exact_mod_cast hreal

/-- Helper: `16 * Nat.log 2 m + 18 ≤ m / 4` for `m ≥ 16384`. -/
private lemma sixteen_log2_add18_le_div4 {m : ℕ} (hm16 : 16384 ≤ m) :
    16 * Nat.log 2 m + 18 ≤ m / 4 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm16r : (16384 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm16
  have h2pow : 2 ^ (Nat.log 2 m) ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hlog2m : ((Nat.log 2 m : ℕ) : ℝ) ≤ 2 * Real.log (m : ℝ) := by
    have h1 : (2 : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by exact_mod_cast h2pow
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  set t : ℝ := Real.sqrt (Real.sqrt (m : ℝ))
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hm_pos)
  have ht4 : t ^ 4 = (m : ℝ) := by
    have h1 : t ^ 2 = Real.sqrt (m : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (m : ℝ)) ^ 2 := by rw [h1]
      _ = (m : ℝ) := Real.sq_sqrt hm_pos.le
  have ht_ge11 : (11 : ℝ) ≤ t := by
    have hsq1 : (121 : ℝ) ≤ Real.sqrt (m : ℝ) := by
      calc (121 : ℝ) = Real.sqrt (121 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by linarith)
    calc (11 : ℝ) = Real.sqrt (11 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ t := Real.sqrt_le_sqrt (by linarith)
  have hlogm_t : Real.log (m : ℝ) ≤ 4 * t := by
    have h1 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht_pos
    have h2 : Real.log (m : ℝ) = 4 * Real.log t := by rw [← ht4, Real.log_pow]; ring
    linarith
  have h1331 : 1331 * t ≤ (m : ℝ) := by
    have h1 : (121 : ℝ) ≤ t ^ 2 := by nlinarith only [ht_ge11]
    have h2 : (1331 : ℝ) ≤ t ^ 3 := by nlinarith only [ht_ge11, h1]
    have h3 : 1331 * t ≤ t ^ 3 * t := mul_le_mul_of_nonneg_right h2 ht_pos.le
    linarith only [h3, ht4, show t ^ 3 * t = t ^ 4 by ring]
  have hdiv4 : (m : ℝ) / 4 - 1 ≤ ((m / 4 : ℕ) : ℝ) := by
    have : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast (by omega : m ≤ 4 * (m / 4) + 3)
    linarith
  have hreal : (16 * (Nat.log 2 m : ℝ) + 18) ≤ ((m / 4 : ℕ) : ℝ) := by
    linarith only [hlog2m, hlogm_t, h1331, hdiv4, ht_ge11]
  exact_mod_cast hreal

/-- Branch B (11-prime strip): for `M_strip / m^5 ≤ x < m^5 * M_strip`, represent `x` in
    `≤ 2 * R_cover m + (16 * Nat.log 2 m + 18)` distinct positive divisors of `M_core m`. -/
private lemma branchB_eleven_prime_rep {m m_dil : ℕ} {Q_strip Q_tag : Finset ℕ}
    (hm16 : 16384 ≤ m) (hmdil_lo : m1_pigeonhole ≤ m_dil) (hmdil_hi : m_dil ≤ m)
    (hdisj_band : Disjoint Q_strip Q_tag)
    (hband : ∀ q ∈ Q_strip ∪ Q_tag, q.Prime ∧ m / 2 < q ∧ 14 * m_dil / 25 < q ∧ q ≤ m_dil)
    (hQstrip_ge12 : 12 ≤ Q_strip.card)
    (hQstrip_le : Q_strip.card ≤ (primePool m).card / 2) (hpool_ge8 : 8 ≤ (primePool m).card)
    (hQtag_ge : 2 * R_cover m ≤ Q_tag.card)
    {x : ℕ} (hx_lo : (∏ q ∈ Q_strip, q) / m ^ 5 ≤ x) (hx_hi : x < m ^ 5 * (∏ q ∈ Q_strip, q)) :
    ∃ S : Finset ℕ,
      (∀ d ∈ S, 0 < d ∧ d ∣ M_core m) ∧
      S.sum id = x ∧
      S.card ≤ 2 * R_cover m + (16 * Nat.log 2 m + 18) := by
  have hm4096 : 4096 ≤ m := by omega
  set L : List ℕ := Q_strip.toList
  have hL_nd : L.Nodup := Finset.nodup_toList Q_strip
  have hL_len : 12 ≤ L.length := by rw [Finset.length_toList]; exact hQstrip_ge12
  set Q'' : Finset ℕ := (L.drop 11).toFinset
  have hQ''_sub : Q'' ⊆ Q_strip := by
    intro q hq
    exact Finset.mem_toList.mp (List.mem_of_mem_drop (List.mem_toFinset.mp hq))
  have hQ''_card : Q''.card = Q_strip.card - 11 := by
    rw [List.toFinset_card_of_nodup hL_nd.drop, List.length_drop, Finset.length_toList]
  have hQ''_ne : Q''.Nonempty := Finset.card_pos.mp (by omega)
  set Q_rem : Finset ℕ := Q_strip \ Q''
  have hQrem_card : Q_rem.card = 11 := by
    rw [Finset.card_sdiff_of_subset hQ''_sub]; omega
  set M_strip : ℕ := ∏ q ∈ Q_strip, q
  set M'' : ℕ := ∏ q ∈ Q'', q
  set M_rem : ℕ := ∏ q ∈ Q_rem, q
  have hM_split : M_strip = M'' * M_rem := by
    dsimp [M_strip, M'', M_rem, Q_rem]
    rw [← Finset.prod_sdiff hQ''_sub, mul_comm]
  have hM''_pos : 0 < M'' := Finset.prod_pos fun q hq => (hband q (Finset.mem_union_left _ (hQ''_sub hq))).1.pos
  have : NeZero M'' := ⟨hM''_pos.ne'⟩
  -- Bounds on M_rem: (m / 2)^11 ≤ M_rem ≤ m^11
  have hMrem_lo : (m / 2) ^ 11 ≤ M_rem := by
    calc (m / 2) ^ 11 = ∏ _ ∈ Q_rem, (m / 2) := by rw [Finset.prod_const, hQrem_card]
      _ ≤ ∏ q ∈ Q_rem, q := Finset.prod_le_prod fun q hq => by
          have hb := hband q (Finset.mem_union_left _ (Finset.mem_sdiff.mp hq).1)
          exact le_of_lt hb.2.1
  have hMrem_hi : M_rem ≤ m ^ 11 := by
    calc ∏ q ∈ Q_rem, q ≤ ∏ _ ∈ Q_rem, m := Finset.prod_le_prod fun q hq => by
          have hb := hband q (Finset.mem_union_left _ (Finset.mem_sdiff.mp hq).1)
          exact le_trans hb.2.2.2 hmdil_hi
      _ = m ^ 11 := by rw [Finset.prod_const, hQrem_card]
  have hQ''_le : Q''.card ≤ (primePool m).card / 2 := le_trans (Finset.card_le_card hQ''_sub) hQstrip_le
  rcases mod_Mprime_covering hm4096 hmdil_lo hmdil_hi hdisj_band hband hQ''_sub hQ''_ne hQ''_le
    hpool_ge8 hQtag_ge (x : ZMod M'') with ⟨S₁, hS1_card, hS1_prop, hS1_mod, hS1_sum_lt⟩
  -- Show S₁.sum id < m^5 * M'' ≤ M_strip / m^5 ≤ x
  have hS1_le_x : S₁.sum id ≤ x := by
    have hpow := two_mul_pow10_le_half_pow11 hm16
    have h1 : m ^ 5 * M'' * m ^ 5 ≤ M_strip := by
      calc m ^ 5 * M'' * m ^ 5 = M'' * m ^ 10 := by ring
        _ ≤ M'' * (2 * m ^ 10) := Nat.mul_le_mul_left M'' (by nlinarith)
        _ ≤ M'' * (m / 2) ^ 11 := Nat.mul_le_mul_left M'' hpow
        _ ≤ M'' * M_rem := Nat.mul_le_mul_left M'' hMrem_lo
        _ = M_strip := hM_split.symm
    have h2 : m ^ 5 * M'' ≤ M_strip / m ^ 5 := (Nat.le_div_iff_mul_le (by positivity)).mpr h1
    have hlt' : S₁.sum id < m ^ 5 * M'' := hS1_sum_lt
    exact le_trans (le_of_lt hlt') (le_trans h2 hx_lo)
  have hdvd_diff : M'' ∣ x - S₁.sum id := by
    have hmod : S₁.sum id % M'' = x % M'' := (ZMod.natCast_eq_natCast_iff' (S₁.sum id) x M'').mp hS1_mod
    have h1 := Nat.div_add_mod x M''
    have h2 := Nat.div_add_mod (S₁.sum id) M''
    refine ⟨x / M'' - S₁.sum id / M'', ?_⟩
    rw [Nat.mul_sub]; omega
  set q'' : ℕ := (x - S₁.sum id) / M''
  have hq''_eq : S₁.sum id + M'' * q'' = x := by
    have hmul : M'' * q'' = x - S₁.sum id := Nat.mul_div_cancel' hdvd_diff
    omega
  have hq''_lt : q'' < m ^ 16 := by
    have hmul_lt : M'' * q'' < M'' * m ^ 16 := by
      calc M'' * q'' ≤ x := by omega
        _ < m ^ 5 * M_strip := hx_hi
        _ = M'' * (m ^ 5 * M_rem) := by rw [hM_split]; ring
        _ ≤ M'' * (m ^ 5 * m ^ 11) := Nat.mul_le_mul_left M'' (Nat.mul_le_mul_left _ hMrem_hi)
        _ = M'' * m ^ 16 := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul_lt
  have hm16_lt_pow : m ^ 16 < 2 ^ (16 * Nat.log 2 m + 18) := by
    have hm_lt : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have h1 : m ^ 16 < (2 ^ (Nat.log 2 m + 1)) ^ 16 := Nat.pow_lt_pow_left hm_lt (by norm_num : 16 ≠ 0)
    have h2 : (2 ^ (Nat.log 2 m + 1)) ^ 16 = 2 ^ (16 * Nat.log 2 m + 16) := by rw [← pow_mul]; congr 1; ring
    have h3 : 2 ^ (16 * Nat.log 2 m + 16) ≤ 2 ^ (16 * Nat.log 2 m + 18) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (lt_of_lt_of_eq h1 h2) h3
  have hB_le_div4 : 16 * Nat.log 2 m + 18 ≤ m / 4 := sixteen_log2_add18_le_div4 hm16
  rcases binary_rep_pow2 (16 * Nat.log 2 m + 18) q'' (lt_trans hq''_lt hm16_lt_pow) with ⟨S₂_raw, hS2_card, hS2_prop, hS2_sum⟩
  let S₂ : Finset ℕ := S₂_raw.image (M'' * ·)
  have hinj : Function.Injective (M'' * · : ℕ → ℕ) := fun a b h => Nat.eq_of_mul_eq_mul_left hM''_pos h
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rcases Finset.mem_image.mp hd2 with ⟨a, _, rfl⟩
    exact (hS1_prop (M'' * a) hd1).2.2.1 (dvd_mul_right M'' a)
  have hM''_dvd_prim : M'' ∣ primorial m := by
    unfold primorial
    refine Finset.prod_dvd_prod_of_subset Q'' ((Finset.range (m + 1)).filter Nat.Prime) id ?_
    intro q hq
    have hb := hband q (Finset.mem_union_left _ (hQ''_sub hq))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb.1⟩
  refine ⟨S₁ ∪ S₂, ?_, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_union.mp hd with hd1 | hd2
    · exact ⟨(hS1_prop d hd1).1, (hS1_prop d hd1).2.1⟩
    · rcases Finset.mem_image.mp hd2 with ⟨a, ha, rfl⟩
      rcases hS2_prop a ha with ⟨ha_pos, ha_dvd, _⟩
      refine ⟨Nat.mul_pos hM''_pos ha_pos, ?_⟩
      have h1 : M'' * a ∣ primorial m * 2 ^ (m / 4) :=
        Nat.mul_dvd_mul hM''_dvd_prim (dvd_trans ha_dvd (Nat.pow_dvd_pow 2 hB_le_div4))
      rw [mul_comm (primorial m)] at h1
      unfold M_core
      exact dvd_trans h1 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_refl _) _) _)
  · rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => hinj h)]
    simp only [id_eq] at hS2_sum ⊢; rw [← Finset.mul_sum, hS2_sum]; exact hq''_eq
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective S₂_raw hinj, hS1_card]
    omega

/-! ## Part 3: Stage 2 Tail Recursion (`m → m / 2`) -/

/-- `M_strip` and `M_core (m / 2)` are coprime since every `q ∈ Q_strip` satisfies `q > m / 2`. -/
private lemma coprime_Mstrip_Mcore_half {m : ℕ} {Q_strip : Finset ℕ}
    (hQ : ∀ q ∈ Q_strip, q.Prime ∧ m / 2 < q) :
    Nat.Coprime (∏ q ∈ Q_strip, q) (M_core (m / 2)) := by
  refine Nat.coprime_of_dvd fun p hp hpd1 hpd2 => ?_
  rcases prime_dvd_finset_prod_pf hp hpd1 with ⟨q, hq_mem, hpq⟩
  have hq_info := hQ q hq_mem
  have hp_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_info.1).mp hpq
  have hp_gt : m / 2 < p := hp_eq ▸ hq_info.2
  -- On the other hand, every prime dividing M_core (m / 2) is ≤ m / 2
  unfold M_core at hpd2
  have hp_le : p ≤ m / 2 := by
    rcases hp.dvd_mul.mp hpd2 with h1 | h4
    · rcases hp.dvd_mul.mp h1 with h2 | h3
      · rcases hp.dvd_mul.mp h2 with h2p | hprim
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2p)
          have hne : m / 2 ≥ 2 := by
            by_contra hlt; push Not at hlt
            -- Wait: if m / 2 < 2, then 2^(m/2 / 4) = 1, so p ∣ 1 contradiction!
            have hdiv0 : m / 2 / 4 = 0 := by omega
            rw [hdiv0, pow_zero] at h2p
            exact hp.not_dvd_one h2p
          omega
        · exact prime_dvd_primorial_le hp hprim
      · exact le_trans (prime_dvd_primorial_le hp (hp.dvd_of_dvd_pow h3)) (Nat.div_le_self _ 3)
    · exact le_trans (prime_dvd_primorial_le hp (hp.dvd_of_dvd_pow h4)) (Nat.sqrt_le_self _)
  omega

/-- **Stage 2 (Tail Recursion `m → m / 2`):**
    There exists an absolute constant `C_s2 > 0` such that for every `m ≥ 20` and `x < M_core m`,
    `x` is a sum of at most `C_s2 * (Real.log m)^3 * Real.log (Real.log (m + 16))` strictly distinct
    positive divisors of `M_core m`. -/
theorem stage2_tail_recursion_primefield :
    ∃ C_s2 : ℝ, 0 < C_s2 ∧ ∀ (m x : ℕ), 20 ≤ m → x < M_core m →
      ∃ S : Finset ℕ,
        (∀ d ∈ S, 0 < d ∧ d ∣ M_core m) ∧
        S.sum id = x ∧
        (S.card : ℝ) ≤ C_s2 * (Real.log (m : ℝ)) ^ 3 * Real.log (Real.log ((m : ℝ) + 16)) := by
  rcases exists_prime_band with ⟨c_band, m_band, hc_pos, hm_band_ge, hband_all⟩
  rcases exists_primefield_threshold (c_band := c_band) (m_band := m_band) hc_pos with ⟨m_pf, hmpf_ge, hthresh_all⟩
  set C_dig : ℝ := 6000000
  set K_extra : ℝ := 512 / c_band + 2
  set M_base : ℕ := M_core (2 * m_pf) + 1
  set C_s2 : ℝ := max (10 * (M_base : ℝ)) (2 * (C_dig + K_extra * C_dig))
  have hCs2_pos : 0 < C_s2 := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨C_s2, hCs2_pos, ?_⟩
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro x hm20 hx
    have hlogm_ge1 : (1 : ℝ) ≤ Real.log (m : ℝ) := by
      have hm_r : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm20
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (m : ℝ) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hll_gt1 : 1 < Real.log (Real.log ((m : ℝ) + 16)) := one_lt_log_log_add16_all m
    -- Base case: 20 ≤ m ≤ 2 * m_pf
    by_cases hm_small : m ≤ 2 * m_pf
    · rcases M_core_practical hm20 x hx with ⟨S, hprop, hsum⟩
      refine ⟨S, hprop, hsum, ?_⟩
      have hsub : S ⊆ Finset.range M_base := by
        intro d hd
        rw [Finset.mem_range]
        have hd_le : d ≤ M_core m := Nat.le_of_dvd (M_core_pos m) (hprop d hd).2
        have hM_le : M_core m ≤ M_core (2 * m_pf) := Nat.le_of_dvd (M_core_pos _) (M_core_mono_dvd hm_small)
        omega
      have hcard_le : (S.card : ℝ) ≤ (M_base : ℝ) := by exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
      have h1_le : (1 : ℝ) ≤ (Real.log (m : ℝ)) ^ 3 * Real.log (Real.log ((m : ℝ) + 16)) := by
        have hpow : (1 : ℝ) ≤ (Real.log (m : ℝ)) ^ 3 := one_le_pow₀ hlogm_ge1
        nlinarith only [hpow, hll_gt1]
      have hCs2_ge : 10 * (M_base : ℝ) ≤ C_s2 := le_max_left _ _
      have hM_nn : (0 : ℝ) ≤ (M_base : ℝ) := Nat.cast_nonneg M_base
      nlinarith only [hcard_le, h1_le, hCs2_ge, hM_nn]
    -- Inductive case: m > 2 * m_pf (so both m ≥ m_pf and m / 2 ≥ m_pf!)
    push Not at hm_small
    have hm_ge_mpf : m_pf ≤ m := le_trans (Nat.le_mul_of_pos_left m_pf (by norm_num)) (le_of_lt hm_small)
    have hm2_ge_mpf : m_pf ≤ m / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith [hm_small])
    have h2mb_le : 2 * m_band + 4 ≤ m_pf := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmpf_ge
    have h16_le : 16384 ≤ m_pf := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmpf_ge
    have h64_le : Nat.ceil (64 / c_band) + 16 ≤ m_pf := le_trans (le_max_right _ _) hmpf_ge
    have hm_ge_mband : m_band ≤ m := le_trans (le_trans (Nat.le_mul_of_pos_left m_band (by norm_num)) (le_trans (Nat.le_add_right _ 4) h2mb_le)) hm_ge_mpf
    have hm2_ge_mband : m_band ≤ m / 2 := le_trans (le_trans (Nat.le_mul_of_pos_left m_band (by norm_num)) (le_trans (Nat.le_add_right _ 4) h2mb_le)) hm2_ge_mpf
    have hm16 : 16384 ≤ m := le_trans h16_le hm_ge_mpf
    have hm2_4096 : 4096 ≤ m / 2 := le_trans (le_trans (by norm_num) h16_le) hm2_ge_mpf
    rcases hband_all m hm_ge_mband with
      ⟨m_dil, Q_strip, Q_tag, hmdil_lo, hmdil_hi, hdisj_band, hband, hQstrip_card, hQtag_card, hQstrip_ge12, hQstrip_le, hpool_ge8⟩
    rcases hthresh_all m hm_ge_mpf with ⟨h2R_le, hthresh_m⟩
    have hQtag_ge : 2 * R_cover m ≤ Q_tag.card := by
      have : (2 * R_cover m : ℝ) ≤ (Q_tag.card : ℝ) := le_trans h2R_le hQtag_card
      exact_mod_cast this
    set M_strip : ℕ := ∏ q ∈ Q_strip, q
    have hMstrip_pos : 0 < M_strip := Finset.prod_pos fun q hq => (hband q (Finset.mem_union_left _ hq)).1.pos
    have hdig_le_s2 : (2 * R_cover m + (16 * Nat.log 2 m + 18) : ℝ) ≤
        C_s2 * (Real.log (m : ℝ)) ^ 3 * Real.log (Real.log ((m : ℝ) + 16)) := by
      have h1 := R_cover_le_const (by omega : 4096 ≤ m)
      have h2 : C_dig ≤ C_s2 := by
        have hposK : 0 < K_extra := by dsimp [K_extra]; positivity
        have hle : C_dig ≤ 2 * (C_dig + K_extra * C_dig) := by dsimp [C_dig]; nlinarith only [hposK]
        exact le_trans hle (le_max_right _ _)
      have hpow : (Real.log (m : ℝ)) ^ 2 ≤ (Real.log (m : ℝ)) ^ 3 := by
        have := mul_le_mul_of_nonneg_left hlogm_ge1 (sq_nonneg (Real.log (m : ℝ)))
        linarith
      have h3 : C_dig * (Real.log (m : ℝ)) ^ 2 * Real.log (Real.log ((m : ℝ) + 16)) ≤
          C_s2 * (Real.log (m : ℝ)) ^ 3 * Real.log (Real.log ((m : ℝ) + 16)) := by
        have hmul : C_dig * (Real.log (m : ℝ)) ^ 2 ≤ C_s2 * (Real.log (m : ℝ)) ^ 3 :=
          mul_le_mul h2 hpow (sq_nonneg _) hCs2_pos.le
        exact mul_le_mul_of_nonneg_right hmul (by linarith)
      exact le_trans h1 h3
    -- Branch A: x < M_strip / m ^ 5
    by_cases hxA : x < M_strip / m ^ 5
    · rcases exact_digit_rep_primefield (by omega : 4096 ≤ m) hmdil_lo hmdil_hi hdisj_band hband
        hQstrip_le hpool_ge8 hQtag_ge hxA with ⟨S, hprop, hsum, hcard⟩
      refine ⟨S, hprop, hsum, ?_⟩
      have hcard_le : (S.card : ℝ) ≤ (2 * R_cover m + (16 * Nat.log 2 m + 18) : ℝ) := by
        exact_mod_cast le_trans hcard (by omega)
      exact le_trans hcard_le hdig_le_s2
    push Not at hxA
    -- Branch B: M_strip / m ^ 5 ≤ x < m ^ 5 * M_strip
    by_cases hxB : x < m ^ 5 * M_strip
    · rcases branchB_eleven_prime_rep hm16 hmdil_lo hmdil_hi hdisj_band hband hQstrip_ge12 hQstrip_le
        hpool_ge8 hQtag_ge hxA hxB with ⟨S, hprop, hsum, hcard⟩
      refine ⟨S, hprop, hsum, ?_⟩
      have hcard_le : (S.card : ℝ) ≤ (2 * R_cover m + (16 * Nat.log 2 m + 18) : ℝ) := by exact_mod_cast hcard
      exact le_trans hcard_le hdig_le_s2
    -- Branch C: m ^ 5 * M_strip ≤ x < M_core m
    push Not at hxB
    have hQstrip_ne : Q_strip.Nonempty := Finset.card_pos.mp (by omega)
    have : NeZero M_strip := ⟨hMstrip_pos.ne'⟩
    rcases mod_Mprime_covering (by omega : 4096 ≤ m) hmdil_lo hmdil_hi hdisj_band hband
      (Finset.Subset.refl Q_strip) hQstrip_ne hQstrip_le hpool_ge8 hQtag_ge (x : ZMod M_strip) with
      ⟨S₁, hS1_card, hS1_prop, hS1_mod, hS1_sum_lt⟩
    have hS1_le_x : S₁.sum id ≤ x := le_trans (le_of_lt hS1_sum_lt) hxB
    have hdvd_diff : M_strip ∣ x - S₁.sum id := by
      have hmod : S₁.sum id % M_strip = x % M_strip :=
        (ZMod.natCast_eq_natCast_iff' (S₁.sum id) x M_strip).mp hS1_mod
      have h1 := Nat.div_add_mod x M_strip
      have h2 := Nat.div_add_mod (S₁.sum id) M_strip
      refine ⟨x / M_strip - S₁.sum id / M_strip, ?_⟩
      rw [Nat.mul_sub]; omega
    set y : ℕ := (x - S₁.sum id) / M_strip
    have hy_eq : S₁.sum id + M_strip * y = x := by
      have hmul : M_strip * y = x - S₁.sum id := Nat.mul_div_cancel' hdvd_diff
      omega
    -- Split M_core m = M_strip * (M_core (m / 2) * U_extra)
    have hMstrip_dvd_core : M_strip ∣ M_core m := by
      have hprim : M_strip ∣ primorial m := by
        unfold primorial
        refine Finset.prod_dvd_prod_of_subset Q_strip ((Finset.range (m + 1)).filter Nat.Prime) id ?_
        intro q hq
        have hb := hband q (Finset.mem_union_left _ hq)
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb.1⟩
      unfold M_core
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hprim _) _) _
    have hMhalf_dvd_core : M_core (m / 2) ∣ M_core m := M_core_mono_dvd (Nat.div_le_self m 2)
    have hcop : Nat.Coprime M_strip (M_core (m / 2)) :=
      coprime_Mstrip_Mcore_half (fun q hq => let hb := hband q (Finset.mem_union_left _ hq); ⟨hb.1, hb.2.1⟩)
    have hprod_dvd : M_strip * M_core (m / 2) ∣ M_core m :=
      hcop.mul_dvd_of_dvd_of_dvd hMstrip_dvd_core hMhalf_dvd_core
    set U_extra : ℕ := M_core m / (M_strip * M_core (m / 2))
    have hMcore_split : M_core m = M_strip * (M_core (m / 2) * U_extra) := by
      rw [← mul_assoc]; exact (Nat.mul_div_cancel' hprod_dvd).symm
    have hU_pos : 1 ≤ U_extra := by
      by_contra h0; push Not at h0
      have hU0 : U_extra = 0 := Nat.lt_one_iff.mp h0
      rw [hU0, mul_zero, mul_zero] at hMcore_split
      exact (M_core_pos m).ne' hMcore_split
    have hU_le : U_extra ≤ 2 ^ (6 * m) := by
      have h1 : U_extra ≤ M_core m := Nat.div_le_self _ _
      exact le_trans h1 (M_core_le_two_pow (by omega : 4096 ≤ m))
    have hU_primes : ∀ p : ℕ, p.Prime → p ∣ U_extra → p ≤ m := by
      intro p hp hpd
      have hpd_core : p ∣ M_core m := dvd_trans hpd ⟨M_strip * M_core (m / 2), by linarith [hMcore_split]⟩
      have hpd_fac : p ∣ m.factorial := dvd_trans hpd_core (M_core_dvd_factorial (by omega : 4096 ≤ m))
      exact (Nat.Prime.dvd_factorial hp).mp hpd_fac
    -- Get the band for m / 2 so we can run greedy_factorize on U_extra with K_half = M_strip_half / (m/2)^5
    rcases hband_all (m / 2) hm2_ge_mband with
      ⟨m_dil2, Q_strip2, Q_tag2, hmdil2_lo, hmdil2_hi, hdisj_band2, hband2, hQstrip2_card, hQtag2_card, _, hQstrip2_le, hpool2_ge8⟩
    rcases hthresh_all (m / 2) hm2_ge_mpf with ⟨h2R2_le, hthresh_m2⟩
    have hQtag2_ge : 2 * R_cover (m / 2) ≤ Q_tag2.card := by
      have : (2 * R_cover (m / 2) : ℝ) ≤ (Q_tag2.card : ℝ) := le_trans h2R2_le hQtag2_card
      exact_mod_cast this
    set M_strip2 : ℕ := ∏ q ∈ Q_strip2, q
    have hMstrip2_pos : 0 < M_strip2 := Finset.prod_pos fun q hq => (hband2 q (Finset.mem_union_left _ hq)).1.pos
    set K_half : ℕ := M_strip2 / (m / 2) ^ 5
    have hlogM2 := log_prod_Qstrip_ge hm2_4096 hc_pos
      (fun q hq => (hband2 q (Finset.mem_union_left _ hq)).2.1) hQstrip2_card
    have hKhalf_exp := K_strip_exponential_lower hm2_4096 hc_pos hMstrip2_pos hlogM2 hthresh_m2
    -- Note m ≤ K_half and 2^(e2 - 2) ≤ K_half / m where e2 = ⌊(c_band / 8) * (m / 2)⌋
    set e2 : ℕ := Nat.floor ((c_band / 8) * ((m / 2 : ℕ) : ℝ))
    have he2_ge : 4 ≤ e2 := by
      have hm2_ge64 : 64 / c_band ≤ ((m / 2 : ℕ) : ℝ) := by
        have h2 : Nat.ceil (64 / c_band) ≤ m / 2 := le_trans (le_trans (Nat.le_add_right _ 16) h64_le) hm2_ge_mpf
        exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr h2)
      have h4 : (4 : ℝ) ≤ (c_band / 8) * ((m / 2 : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_left hm2_ge64 (by positivity : 0 ≤ c_band / 8)
        have hsimp : (c_band / 8) * (64 / c_band) = 8 := by field_simp [hc_pos.ne']; ring
        linarith
      exact Nat.le_floor h4
    have hm_le_Khalf : m ≤ K_half := by
      have h2e : 4 ≤ 2 ^ e2 := le_trans (by norm_num : 4 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) he2_ge)
      have h1 : 4 * (m / 2) ≤ K_half := by
        have := (Nat.le_div_iff_mul_le (by omega : 0 < m / 2)).mp hKhalf_exp.2
        calc 4 * (m / 2) ≤ 2 ^ e2 * (m / 2) := Nat.mul_le_mul_right _ h2e
          _ ≤ K_half := this
      omega
    rcases greedy_factorize m K_half (by omega) hm_le_Khalf U_extra hU_pos hU_primes with
      ⟨Ds, hDs_prod, hDs_mem, hDs_len⟩
    -- Bound Ds.length ≤ K_extra = 256 / c_band + 2
    have hDs_len_le : (Ds.length : ℝ) ≤ K_extra := by
      have hKhalf_div_m : 2 ^ (e2 - 2) ≤ K_half / m := by
        have h1 : 2 ^ e2 * (m / 2) ≤ K_half := (Nat.le_div_iff_mul_le (by omega : 0 < m / 2)).mp hKhalf_exp.2
        have h2 : m ≤ 4 * (m / 2) := by omega
        have h3 : 2 ^ (e2 - 2) * m ≤ 2 ^ e2 * (m / 2) := by
          calc 2 ^ (e2 - 2) * m ≤ 2 ^ (e2 - 2) * (4 * (m / 2)) := Nat.mul_le_mul_left _ h2
            _ = (2 ^ (e2 - 2) * 2 ^ 2) * (m / 2) := by ring
            _ = 2 ^ e2 * (m / 2) := by rw [← pow_add, show e2 - 2 + 2 = e2 by omega]
        exact (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr (le_trans h3 h1)
      have hpow_le : (2 ^ (e2 - 2)) ^ (Ds.length - 1) ≤ 2 ^ (6 * m) :=
        le_trans (Nat.pow_le_pow_left hKhalf_div_m _) (le_trans hDs_len hU_le)
      rw [← pow_mul] at hpow_le
      have hexp_le : (e2 - 2) * (Ds.length - 1) ≤ 6 * m :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
      have he2_lb : (c_band / 64) * (m : ℝ) ≤ ((e2 - 2 : ℕ) : ℝ) := by
        have hfl : (c_band / 8) * ((m / 2 : ℕ) : ℝ) - 1 ≤ (e2 : ℝ) := by linarith only [Nat.lt_floor_add_one ((c_band / 8) * ((m / 2 : ℕ) : ℝ))]
        have hm2_ge64 : 64 / c_band ≤ ((m / 2 : ℕ) : ℝ) := by
          have h2 : Nat.ceil (64 / c_band) ≤ m / 2 := le_trans (le_trans (Nat.le_add_right _ 16) h64_le) hm2_ge_mpf
          exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr h2)
        have hge8 : (8 : ℝ) ≤ (c_band / 8) * ((m / 2 : ℕ) : ℝ) := by
          have := mul_le_mul_of_nonneg_left hm2_ge64 (by positivity : 0 ≤ c_band / 8)
          have hsimp : (c_band / 8) * (64 / c_band) = 8 := by field_simp [hc_pos.ne']; ring
          linarith only [this, hsimp]
        have hhalf_ge : (c_band / 16) * ((m / 2 : ℕ) : ℝ) ≤ (e2 : ℝ) - 2 := by linarith only [hfl, hge8]
        have hm_div : (m : ℝ) / 2 - 1 ≤ ((m / 2 : ℕ) : ℝ) := by
          have : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : m ≤ 2 * (m / 2) + 1)
          linarith only [this]
        have hm2_ge_m4 : (m : ℝ) / 4 ≤ ((m / 2 : ℕ) : ℝ) := by
          have hm16r : (16384 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm16
          linarith only [hm_div, hm16r]
        have hstep := mul_le_mul_of_nonneg_left hm2_ge_m4 (by positivity : 0 ≤ c_band / 16)
        have he2_cast : ((e2 - 2 : ℕ) : ℝ) = (e2 : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ e2)]; norm_num
        linarith only [hhalf_ge, hstep, he2_cast]
      have hexp_r : ((e2 - 2 : ℕ) : ℝ) * ((Ds.length - 1 : ℕ) : ℝ) ≤ 6 * (m : ℝ) := by exact_mod_cast hexp_le
      have hmul_lb : ((c_band / 64) * (m : ℝ)) * ((Ds.length - 1 : ℕ) : ℝ) ≤ 6 * (m : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right he2_lb (Nat.cast_nonneg _)) hexp_r
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdm1 : ((Ds.length - 1 : ℕ) : ℝ) ≤ 384 / c_band := by
        rw [le_div_iff₀ hc_pos]
        have : (((Ds.length - 1 : ℕ) : ℝ) * c_band) * (m : ℝ) ≤ 384 * (m : ℝ) := by linarith only [hmul_lb]
        exact le_of_mul_le_mul_right this hm_pos
      have hlen_cast : (Ds.length : ℝ) ≤ ((Ds.length - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (by omega : Ds.length ≤ (Ds.length - 1) + 1)
      dsimp [K_extra]
      have : (384 : ℝ) / c_band ≤ 512 / c_band := div_le_div_of_nonneg_right (by norm_num) hc_pos.le
      linarith only [hdm1, hlen_cast, this]
    -- Invoke mixed_radix_stage1 on M_core (m / 2) and Ds for y < M_core (m / 2) * U_extra
    set L : ℝ := Real.log (m : ℝ)
    set L2 : ℝ := Real.log ((m / 2 : ℕ) : ℝ)
    set LL : ℝ := Real.log (Real.log ((m : ℝ) + 16))
    set LL2 : ℝ := Real.log (Real.log (((m / 2 : ℕ) : ℝ) + 16))
    have hdigit2 : ∀ r < K_half, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M_core (m / 2)) ∧ S.sum id = r ∧
        (S.card : ℝ) ≤ C_dig * L2 ^ 2 * LL2 := by
      intro r hr
      rcases exact_digit_rep_primefield hm2_4096 hmdil2_lo hmdil2_hi hdisj_band2 hband2
        hQstrip2_le hpool2_ge8 hQtag2_ge hr with ⟨S, hprop, hsum, hcard⟩
      refine ⟨S, hprop, hsum, ?_⟩
      have h1 : (S.card : ℝ) ≤ (2 * R_cover (m / 2) + (16 * Nat.log 2 (m / 2) + 18) : ℝ) := by
        exact_mod_cast le_trans hcard (by omega)
      exact le_trans h1 (R_cover_le_const hm2_4096)
    have htail2 : ∀ z < M_core (m / 2), ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M_core (m / 2)) ∧ S.sum id = z ∧
        (S.card : ℝ) ≤ C_s2 * L2 ^ 3 * LL2 :=
      fun z hz => ih (m / 2) (Nat.div_lt_self (lt_of_lt_of_le (by norm_num) hm16) (by norm_num)) z (le_trans (by norm_num) hm2_4096) hz
    have hy_lt : y < M_core (m / 2) * Ds.prod := by
      rw [hDs_prod]
      have hmul_lt : M_strip * y < M_strip * (M_core (m / 2) * U_extra) := by rw [← hMcore_split]; omega
      exact Nat.lt_of_mul_lt_mul_left hmul_lt
    rcases mixed_radix_stage1 (M_core (m / 2)) K_half (C_dig * L2 ^ 2 * LL2) (C_s2 * L2 ^ 3 * LL2)
        hdigit2 htail2 Ds hDs_mem y hy_lt with ⟨S23_raw, hS23_prop, hS23_sum, hS23_card⟩
    let S23 : Finset ℕ := S23_raw.image (M_strip * ·)
    have hinj : Function.Injective (M_strip * · : ℕ → ℕ) := fun a b h => Nat.eq_of_mul_eq_mul_left hMstrip_pos h
    have hdisj : Disjoint S₁ S23 := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      rcases Finset.mem_image.mp hd2 with ⟨a, _, rfl⟩
      exact (hS1_prop (M_strip * a) hd1).2.2.1 (dvd_mul_right M_strip a)
    refine ⟨S₁ ∪ S23, ?_, ?_, ?_⟩
    · intro d hd
      rcases Finset.mem_union.mp hd with hd1 | hd2
      · exact ⟨(hS1_prop d hd1).1, (hS1_prop d hd1).2.1⟩
      · rcases Finset.mem_image.mp hd2 with ⟨a, ha, rfl⟩
        rcases hS23_prop a ha with ⟨ha_pos, ha_dvd⟩
        refine ⟨Nat.mul_pos hMstrip_pos ha_pos, ?_⟩
        rw [hMcore_split, ← hDs_prod]
        exact Nat.mul_dvd_mul_left M_strip ha_dvd
    · rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [id_eq] at hS23_sum ⊢; rw [← Finset.mul_sum, hS23_sum]; exact hy_eq
    · -- Cardinality bound: (S₁ ∪ S23).card ≤ C_s2 * L^3 * LL
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective S23_raw hinj, Nat.cast_add]
      have hL2_drop : L2 ≤ L - 1 / 2 := by
        have h1 : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
          have : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
          have : 2 * ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
          linarith
        have h2 := Real.log_le_log (Nat.cast_pos.mpr (by omega)) h1
        rw [Real.log_div (Nat.cast_ne_zero.mpr (by omega)) (by norm_num)] at h2
        dsimp [L, L2]; linarith [Real.log_two_gt_d9]
      have hL2_nn : 0 ≤ L2 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m / 2))
      have hL2_le_L : L2 ≤ L := by linarith
      have hL2_sq : L2 ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hL2_nn hL2_le_L 2
      have hL2_cube : L2 ^ 3 ≤ L ^ 3 - (1 / 2 : ℝ) * L ^ 2 := by
        have h1 : L2 ^ 3 = L2 * L2 ^ 2 := by ring
        have h2 : L2 * L2 ^ 2 ≤ (L - 1 / 2) * L ^ 2 := mul_le_mul hL2_drop hL2_sq (by positivity) (by linarith)
        linarith
      have hLL2_le : LL2 ≤ LL := Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < m / 2 + 16)))
        (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : m / 2 + 16 ≤ m + 16)))
      have hLL2_nn : 0 ≤ LL2 := by linarith [one_lt_log_log_add16_all (m / 2)]
      have hS1_le : (S₁.card : ℝ) ≤ C_dig * L ^ 2 * LL := by
        have h1 : (S₁.card : ℝ) ≤ (2 * R_cover m + (16 * Nat.log 2 m + 18) : ℝ) := by
          rw [hS1_card]; push_cast; linarith only [show (0 : ℝ) ≤ 16 * (Nat.log 2 m : ℝ) + 18 by positivity]
        exact le_trans h1 (R_cover_le_const (by omega : 4096 ≤ m))
      have hD_term : (Ds.length : ℝ) * (C_dig * L2 ^ 2 * LL2) ≤ K_extra * C_dig * L ^ 2 * LL := by
        have h1 : L2 ^ 2 * LL2 ≤ L ^ 2 * LL := mul_le_mul hL2_sq hLL2_le hLL2_nn (sq_nonneg L)
        have h2 : C_dig * L2 ^ 2 * LL2 ≤ C_dig * L ^ 2 * LL := by
          have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ C_dig); linarith
        calc (Ds.length : ℝ) * (C_dig * L2 ^ 2 * LL2)
            ≤ K_extra * (C_dig * L ^ 2 * LL) := mul_le_mul hDs_len_le h2 (by positivity) (by dsimp [K_extra]; positivity)
          _ = K_extra * C_dig * L ^ 2 * LL := by ring
      have hS3_term : C_s2 * L2 ^ 3 * LL2 ≤ C_s2 * (L ^ 3 - (1 / 2 : ℝ) * L ^ 2) * LL := by
        have h1 : L2 ^ 3 * LL2 ≤ (L ^ 3 - (1 / 2 : ℝ) * L ^ 2) * LL :=
          mul_le_mul hL2_cube hLL2_le hLL2_nn (by nlinarith only [hlogm_ge1])
        calc C_s2 * L2 ^ 3 * LL2 = C_s2 * (L2 ^ 3 * LL2) := by ring
          _ ≤ C_s2 * ((L ^ 3 - (1 / 2 : ℝ) * L ^ 2) * LL) := mul_le_mul_of_nonneg_left h1 hCs2_pos.le
          _ = C_s2 * (L ^ 3 - (1 / 2 : ℝ) * L ^ 2) * LL := by ring
      have hCs2_ge : 2 * (C_dig + K_extra * C_dig) ≤ C_s2 := le_max_right _ _
      have hcoef : (C_dig + K_extra * C_dig) * (L ^ 2 * LL) ≤ (1 / 2 : ℝ) * C_s2 * (L ^ 2 * LL) :=
        mul_le_mul_of_nonneg_right (by linarith only [hCs2_ge]) (by positivity)
      linarith only [hS1_le, hS23_card, hD_term, hS3_term, hcoef]

/-! ## Part 4: Headline Theorem `Erdos18.erdos18_alpha3_loglog1` -/

/-- **Main Theorem (Erdős Problem #18 — `h(n!) = O((log n)^3 log log(n + 16))`)**:
    There exists an absolute constant `C : ℝ` such that for every `n ≥ 2` and every integer
    `1 ≤ t ≤ n!`, `t` can be written as a sum of at most
    `C * (Real.log n) ^ 3 * Real.log (Real.log ((n : ℝ) + 16))` strictly distinct positive
    divisors of `n!`. -/
theorem erdos18_alpha3_loglog1 :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → ∀ t : ℕ, 1 ≤ t → t ≤ Nat.factorial n →
      ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧
        (S.card : ℝ) ≤ C * (Real.log n) ^ 3 * Real.log (Real.log ((n : ℝ) + 16)) := by
  rcases erdos18_alpha3_loglog2 with ⟨C_old, hC_old⟩
  rcases exists_prime_band with ⟨c_band, m_band, hc_pos, _, hband_all⟩
  rcases exists_primefield_threshold (c_band := c_band) (m_band := m_band) hc_pos with ⟨m_pf, hmpf_ge, hthresh_all⟩
  rcases stage2_tail_recursion_primefield with ⟨C_s2, hCs2_pos, hstage2⟩
  set C_dig : ℝ := 6000000
  set C_s1 : ℝ := 32 / c_band + 2
  set C_small : ℝ := max 0 C_old * Real.log (Real.log ((m_pf : ℝ) + 16))
  set C_big : ℝ := C_s1 * C_dig + C_s2 + 10
  set C : ℝ := max C_small C_big
  refine ⟨C, ?_⟩
  intro n hn t ht1 htfac
  have hll_gt1 : 1 < Real.log (Real.log ((n : ℝ) + 16)) := one_lt_log_log_add16_all n
  -- Case 1: t = n!
  by_cases hteq : t = n.factorial
  · subst hteq
    refine ⟨{n.factorial}, ?_, by simp, ?_⟩
    · intro d hd; rw [Finset.mem_singleton] at hd; subst hd
      exact ⟨dvd_refl _, Nat.factorial_pos n⟩
    · simp only [Finset.card_singleton, Nat.cast_one]
      have hlog_ge : (0.69 : ℝ) ≤ Real.log (n : ℝ) := by
        have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith [Real.log_le_log (by norm_num) h2, Real.log_two_gt_d9]
      have hpow3_ge : (0.3 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
        have : (0.69 : ℝ) ^ 3 ≤ (Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) hlog_ge 3
        linarith [show (0.3 : ℝ) ≤ (0.69 : ℝ) ^ 3 by norm_num]
      have hC_ge : 10 ≤ C := by
        have hpos1 : 0 < C_s1 := by dsimp [C_s1]; positivity
        have hle : (10 : ℝ) ≤ C_big := by dsimp [C_big, C_dig]; nlinarith only [hpos1, hCs2_pos]
        exact le_trans hle (le_max_right _ _)
      have hprod_ge : (0.3 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 * Real.log (Real.log ((n : ℝ) + 16)) := by
        nlinarith only [hpow3_ge, hll_gt1]
      nlinarith only [hC_ge, hprod_ge]
  have ht_lt : t < n.factorial := lt_of_le_of_ne htfac hteq
  -- Case 2: 2 ≤ n < m_pf (delegate to erdos18_alpha3_loglog2)
  by_cases hn_small : n < m_pf
  · rcases hC_old n hn t ht1 htfac with ⟨S, hprop, hsum, hcard⟩
    refine ⟨S, hprop, hsum, le_trans hcard ?_⟩
    have hll_le : Real.log (Real.log ((n : ℝ) + 16)) ≤ Real.log (Real.log ((m_pf : ℝ) + 16)) :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 16)))
        (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n + 16 ≤ m_pf + 16)))
    have hC_old_le : C_old ≤ max 0 C_old := le_max_right 0 C_old
    have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have h1 : C_old * (Real.log (n : ℝ)) ^ 3 * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 ≤
        max 0 C_old * (Real.log (n : ℝ)) ^ 3 * (Real.log (Real.log ((n : ℝ) + 16)) * Real.log (Real.log ((m_pf : ℝ) + 16))) := by
      have ha : C_old * (Real.log (n : ℝ)) ^ 3 ≤ max 0 C_old * (Real.log (n : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_right hC_old_le (pow_nonneg hlogn_nn 3)
      have hb : (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 ≤
          Real.log (Real.log ((n : ℝ) + 16)) * Real.log (Real.log ((m_pf : ℝ) + 16)) := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hll_le (by linarith)
      exact mul_le_mul ha hb (by positivity) (by positivity)
    have h2 : max 0 C_old * (Real.log (n : ℝ)) ^ 3 *
        (Real.log (Real.log ((n : ℝ) + 16)) * Real.log (Real.log ((m_pf : ℝ) + 16))) =
        C_small * (Real.log (n : ℝ)) ^ 3 * Real.log (Real.log ((n : ℝ) + 16)) := by
      dsimp [C_small]; ring
    have h3 : C_small * (Real.log (n : ℝ)) ^ 3 * Real.log (Real.log ((n : ℝ) + 16)) ≤
        C * (Real.log (n : ℝ)) ^ 3 * Real.log (Real.log ((n : ℝ) + 16)) := by
      have := mul_le_mul_of_nonneg_right (le_max_left C_small C_big) (by positivity : 0 ≤ (Real.log (n : ℝ)) ^ 3 * Real.log (Real.log ((n : ℝ) + 16)))
      linarith
    linarith
  -- Case 3: n ≥ m_pf (Stage 1 mixed-radix factorization + Stage 2 tail recursion)
  push Not at hn_small
  have h2mb_le : 2 * m_band + 4 ≤ m_pf := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmpf_ge
  have h16_le : 16384 ≤ m_pf := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmpf_ge
  have h64_le : Nat.ceil (64 / c_band) + 16 ≤ m_pf := le_trans (le_max_right _ _) hmpf_ge
  have hn4096 : 4096 ≤ n := le_trans (le_trans (by norm_num) h16_le) hn_small
  have hn_ge_mband : m_band ≤ n := le_trans (le_trans (Nat.le_mul_of_pos_left m_band (by norm_num)) (le_trans (Nat.le_add_right _ 4) h2mb_le)) hn_small
  rcases hband_all n hn_ge_mband with
    ⟨m_dil, Q_strip, Q_tag, hmdil_lo, hmdil_hi, hdisj_band, hband, hQstrip_card, hQtag_card, _, hQstrip_le, hpool_ge8⟩
  rcases hthresh_all n hn_small with ⟨h2R_le, hthresh_n⟩
  have hQtag_ge : 2 * R_cover n ≤ Q_tag.card := by
    have : (2 * R_cover n : ℝ) ≤ (Q_tag.card : ℝ) := le_trans h2R_le hQtag_card
    exact_mod_cast this
  set M_strip : ℕ := ∏ q ∈ Q_strip, q
  have hMstrip_pos : 0 < M_strip := Finset.prod_pos fun q hq => (hband q (Finset.mem_union_left _ hq)).1.pos
  set K_n : ℕ := M_strip / n ^ 5
  have hlogM := log_prod_Qstrip_ge hn4096 hc_pos
    (fun q hq => (hband q (Finset.mem_union_left _ hq)).2.1) hQstrip_card
  have hKn_exp := K_strip_exponential_lower hn4096 hc_pos hMstrip_pos hlogM hthresh_n
  set M := M_core n
  have hM_dvd : M ∣ n.factorial := M_core_dvd_factorial hn4096
  have hM_pos : 0 < M := M_core_pos n
  set U := n.factorial / M
  have hMU : M * U = n.factorial := Nat.mul_div_cancel' hM_dvd
  have hU_pos : 1 ≤ U := by
    by_contra h0; push Not at h0
    have hU0 : U = 0 := Nat.lt_one_iff.mp h0
    rw [hU0, mul_zero] at hMU
    exact Nat.factorial_ne_zero n hMU.symm
  have hU_primes : ∀ p : ℕ, p.Prime → p ∣ U → p ≤ n := by
    intro p hp hpd
    have hpd_fac : p ∣ n.factorial := dvd_trans hpd (by rw [← hMU]; exact dvd_mul_left U M)
    exact (Nat.Prime.dvd_factorial hp).mp hpd_fac
  rcases greedy_factorize n K_n (by omega) hKn_exp.1 U hU_pos hU_primes with
    ⟨Ds, hDs_prod, hDs_mem, hDs_len⟩
  -- Bound Ds.length ≤ C_s1 * Real.log n
  have hDs_len_le : (Ds.length : ℝ) ≤ C_s1 * Real.log (n : ℝ) := by
    set e : ℕ := Nat.floor ((c_band / 8) * (n : ℝ))
    have hpow_le : (2 ^ e) ^ (Ds.length - 1) ≤ n ^ n := by
      have h1 : (2 ^ e) ^ (Ds.length - 1) ≤ (K_n / n) ^ (Ds.length - 1) := Nat.pow_le_pow_left hKn_exp.2 _
      have h2 : U ≤ n.factorial := by rw [← hMU]; exact Nat.le_mul_of_pos_left U hM_pos
      exact le_trans h1 (le_trans hDs_len (le_trans h2 (Nat.factorial_le_pow n)))
    have hreal : (((2 : ℝ) ^ e) ^ (Ds.length - 1)) ≤ (n : ℝ) ^ n := by exact_mod_cast hpow_le
    have hlog := Real.log_le_log (by positivity) hreal
    rw [Real.log_pow, Real.log_pow, Real.log_pow] at hlog
    have he_lb : (c_band / 16) * (n : ℝ) ≤ (e : ℝ) := by
      have hfl : (c_band / 8) * (n : ℝ) - 1 ≤ (e : ℝ) := by linarith [Nat.lt_floor_add_one ((c_band / 8) * (n : ℝ))]
      have hn_ge64 : 64 / c_band ≤ (n : ℝ) := by
        have h2 : Nat.ceil (64 / c_band) ≤ n := le_trans (le_trans (Nat.le_add_right _ 16) h64_le) hn_small
        exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr h2)
      have hge8 : (8 : ℝ) ≤ (c_band / 8) * (n : ℝ) := by
        have := mul_le_mul_of_nonneg_left hn_ge64 (by positivity : 0 ≤ c_band / 8)
        have hsimp : (c_band / 8) * (64 / c_band) = 8 := by field_simp [hc_pos.ne']; ring
        linarith
      linarith
    have hlog2 : (0.5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hmul : ((Ds.length - 1 : ℕ) : ℝ) * ((c_band / 32) * (n : ℝ)) ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have h1 : (c_band / 32) * (n : ℝ) ≤ (e : ℝ) * Real.log 2 := by
        have := mul_le_mul he_lb hlog2 (by norm_num) (by positivity)
        linarith
      exact le_trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) hlog
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hdm1 : ((Ds.length - 1 : ℕ) : ℝ) ≤ (32 / c_band) * Real.log (n : ℝ) := by
      have h1 : (((Ds.length - 1 : ℕ) : ℝ) * (c_band / 32)) * (n : ℝ) ≤ Real.log (n : ℝ) * (n : ℝ) := by linarith
      have h2 : ((Ds.length - 1 : ℕ) : ℝ) * (c_band / 32) ≤ Real.log (n : ℝ) := le_of_mul_le_mul_right h1 hn_pos
      have h3 : ((Ds.length - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) / (c_band / 32) := (le_div_iff₀ (by positivity)).mpr h2
      have h4 : Real.log (n : ℝ) / (c_band / 32) = (32 / c_band) * Real.log (n : ℝ) := by field_simp [hc_pos.ne']
      linarith
    have hlogn_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have hn4 : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4096
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hlen_cast : (Ds.length : ℝ) ≤ ((Ds.length - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : Ds.length ≤ (Ds.length - 1) + 1)
    dsimp [C_s1]; nlinarith only [hdm1, hlen_cast, hlogn_ge1]
  set L : ℝ := Real.log (n : ℝ)
  set LL : ℝ := Real.log (Real.log ((n : ℝ) + 16))
  have hdigit : ∀ r < K_n, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = r ∧
      (S.card : ℝ) ≤ C_dig * L ^ 2 * LL := by
    intro r hr
    rcases exact_digit_rep_primefield hn4096 hmdil_lo hmdil_hi hdisj_band hband
      hQstrip_le hpool_ge8 hQtag_ge hr with ⟨S, hprop, hsum, hcard⟩
    refine ⟨S, hprop, hsum, ?_⟩
    have h1 : (S.card : ℝ) ≤ (2 * R_cover n + (16 * Nat.log 2 n + 18) : ℝ) := by
      exact_mod_cast le_trans hcard (Nat.add_le_add_left (by omega : 6 * Nat.log 2 n + 8 ≤ 16 * Nat.log 2 n + 18) _)
    exact le_trans h1 (R_cover_le_const hn4096)
  have htail : ∀ x < M, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = x ∧
      (S.card : ℝ) ≤ C_s2 * L ^ 3 * LL :=
    fun x hx => hstage2 n x (by omega) hx
  have ht_lt_prod : t < M * Ds.prod := by rw [hDs_prod, hMU]; exact ht_lt
  rcases mixed_radix_stage1 M K_n (C_dig * L ^ 2 * LL) (C_s2 * L ^ 3 * LL)
      hdigit htail Ds hDs_mem t ht_lt_prod with ⟨S, hprop, hsum, hcard⟩
  refine ⟨S, ?_, hsum, ?_⟩
  · intro d hd
    rcases hprop d hd with ⟨hpos, hdvd⟩
    rw [hDs_prod, hMU] at hdvd
    exact ⟨hdvd, hpos⟩
  · have h1 : (Ds.length : ℝ) * (C_dig * L ^ 2 * LL) ≤ (C_s1 * L) * (C_dig * L ^ 2 * LL) :=
      mul_le_mul_of_nonneg_right hDs_len_le (by positivity)
    have h2 : (C_s1 * L) * (C_dig * L ^ 2 * LL) + C_s2 * L ^ 3 * LL = (C_s1 * C_dig + C_s2) * (L ^ 3 * LL) := by ring
    have hC_ge : C_s1 * C_dig + C_s2 ≤ C := le_trans (by dsimp [C_big]; linarith) (le_max_right _ _)
    have h3 : (C_s1 * C_dig + C_s2) * (L ^ 3 * LL) ≤ C * (L ^ 3 * LL) :=
      mul_le_mul_of_nonneg_right hC_ge (by positivity)
    linarith

end Erdos18
