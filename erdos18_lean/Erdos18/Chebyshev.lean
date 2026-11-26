import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdos18/Chebyshev.lean (Layer 3 — Erdős 1932 Elementary Prime Inputs 1–4)

Formalizes all four elementary prime-number inputs required by the `h(n!) = O((log n)^5)` proof:
1. `oddPrimorial_lt_two_pow`: `Q_m = ∏_{3 ≤ p ≤ m/2} p < 2^m` for all `m ≥ 1`.
2. `prime_counting_lower` & `prefix_entropy_rate_lower`: Chebyshev lower bound on `π(x)` and `π_odd(m/2)`.
3. `bertrand_quantitative`: Erdős (1932) quantitative Bertrand lower bound `π_odd(2x) - π_odd(x) ≥ cB * x / log x`.
4. `uTop_dvd_choose`: `∏_{b < p ≤ a} p ∣ Nat.choose a b` whenever `b ≤ a < 2 * b`.
-/

namespace Erdos18

open Finset Nat Real

/-- Product of all odd primes `≤ m`. -/
def oddPrimorial (m : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (m + 1)).filter (fun p => p.Prime ∧ 3 ≤ p), p

/-- Number of odd primes `≤ m` (`π_odd(m)`). -/
def oddPrimeCounting (m : ℕ) : ℕ :=
  ((Finset.range (m + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)).card

lemma oddPrimorial_pos (m : ℕ) : 0 < oddPrimorial m := by
  unfold oddPrimorial
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.1.pos

lemma oddPrimorial_dvd_primorial (m : ℕ) : oddPrimorial m ∣ primorial m := by
  unfold oddPrimorial primorial
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

lemma two_mul_oddPrimorial_eq_primorial {m : ℕ} (hm : 2 ≤ m) :
    2 * oddPrimorial m = primorial m := by
  unfold oddPrimorial primorial
  have h2 : 2 ∈ (Finset.range (m + 1)).filter Nat.Prime := by
    simp [Nat.prime_two, Nat.lt_succ_of_le hm]
  rw [← Finset.mul_prod_erase _ _ h2]
  congr 1
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
  constructor
  · rintro ⟨hp_lt, hp_prime, hp3⟩
    exact ⟨by omega, hp_lt, hp_prime⟩
  · rintro ⟨hp_ne2, hp_lt, hp_prime⟩
    have := hp_prime.two_le
    exact ⟨hp_lt, hp_prime, by omega⟩

/-- Input 1: `Q_m = oddPrimorial (m / 2) < 2^m` for all `m ≥ 1`. -/
theorem oddPrimorial_lt_two_pow {m : ℕ} (hm : 1 ≤ m) :
    oddPrimorial (m / 2) < 2 ^ m := by
  by_cases h4 : m < 4
  · have h1 : oddPrimorial (m / 2) = 1 := by
      unfold oddPrimorial
      apply Finset.prod_eq_one
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      omega
    rw [h1]
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    omega
  · push Not at h4
    have hm2 : 2 ≤ m / 2 := by omega
    have h2 : 2 * oddPrimorial (m / 2) = primorial (m / 2) :=
      two_mul_oddPrimorial_eq_primorial hm2
    have hpos : 0 < oddPrimorial (m / 2) := oddPrimorial_pos (m / 2)
    have hle : primorial (m / 2) ≤ 4 ^ (m / 2) := primorial_le_four_pow (m / 2)
    have hpow : 4 ^ (m / 2) ≤ 2 ^ m := by
      calc 4 ^ (m / 2) = (2 ^ 2) ^ (m / 2) := by norm_num
        _ = 2 ^ (2 * (m / 2)) := by rw [← pow_mul]
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    omega

lemma oddPrimeCounting_eq_primeCounting_sub_one {m : ℕ} (hm : 2 ≤ m) :
    oddPrimeCounting m + 1 = Nat.primeCounting m := by
  unfold oddPrimeCounting Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  have h2 : 2 ∈ (Finset.range (m + 1)).filter Nat.Prime := by
    simp [Nat.prime_two, Nat.lt_succ_of_le hm]
  rw [← Finset.card_erase_add_one h2]
  congr 1
  apply Finset.card_bij (fun p _ => p)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.1, hp.2.1⟩
  · intro _ _ _ _ h; exact h
  · intro p hp
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hp
    have h2le := hp.2.2.two_le
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hp.2.1, hp.2.2, by omega⟩

/-- Input 2: Chebyshev prime-counting lower bound `π(x) ≥ c0 * x / log x` for all `x ≥ 2`. -/
theorem prime_counting_lower :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ x : ℕ, 2 ≤ x → c0 * (x : ℝ) / Real.log (x : ℝ) ≤ (Nat.primeCounting x : ℝ) := by
  refine ⟨Real.log 2 / 4, by positivity, ?_⟩
  intro x hx
  by_cases hx4 : 4 ≤ x
  · have hpi := Chebyshev.pi_ge_of_four_le hx4
    have hlog_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hmul : Real.log 2 / 4 * (x : ℝ) ≤ (x : ℝ) * Real.log 2 := by
      have : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
    exact le_trans (div_le_div_of_nonneg_right hmul hlog_pos.le) hpi
  · interval_cases x
    · have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
      have hpi2 : Nat.primeCounting 2 = 1 := by decide
      rw [hpi2]; push_cast; field_simp [hlog2]; norm_num
    · have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog3 : Real.log (2 : ℝ) ≤ Real.log (3 : ℝ) := Real.log_le_log (by norm_num) (by norm_num)
      have hpi3 : Nat.primeCounting 3 = 2 := by decide
      rw [hpi3]; push_cast
      rw [div_le_iff₀ (lt_of_lt_of_le hlog2 hlog3)]
      nlinarith

/-- Prefix entropy rate lower bound for `Z_m`: `1 + (1/2) * π_odd(m / 2) ≥ c1 * m / log (m + 2)` for all `m ≥ 1`. -/
theorem prefix_entropy_rate_lower :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ m : ℕ, 1 ≤ m →
      c1 * (m : ℝ) / Real.log ((m : ℝ) + 2) ≤ 1 + (oddPrimeCounting (m / 2) : ℝ) / 2 := by
  rcases prime_counting_lower with ⟨c0, hc0, hpi⟩
  refine ⟨min (c0 / 8) (Real.log 3 / 10), by positivity, ?_⟩
  intro m hm
  have hlog_pos : 0 < Real.log ((m : ℝ) + 2) := Real.log_pos (by linarith [show (1 : ℝ) ≤ m from by exact_mod_cast hm])
  by_cases hm8 : m < 8
  · have hlog3 : Real.log 3 ≤ Real.log ((m : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith [show (1 : ℝ) ≤ m from by exact_mod_cast hm])
    have hc1 : min (c0 / 8) (Real.log 3 / 10) ≤ Real.log 3 / 10 := min_le_right _ _
    have hm_le : (m : ℝ) ≤ 7 := by exact_mod_cast (by omega : m ≤ 7)
    have hnonneg : (0 : ℝ) ≤ (oddPrimeCounting (m / 2) : ℝ) / 2 := by positivity
    have hrhs : (1 : ℝ) ≤ 1 + (oddPrimeCounting (m / 2) : ℝ) / 2 := by linarith
    refine le_trans ?_ hrhs
    rw [div_le_iff₀ hlog_pos]
    have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
    nlinarith
  · push Not at hm8
    have hm2 : 2 ≤ m / 2 := by omega
    have hodd := oddPrimeCounting_eq_primeCounting_sub_one hm2
    have hpi_m := hpi (m / 2) hm2
    have hm_div : (m : ℝ) / 4 ≤ ((m / 2 : ℕ) : ℝ) := by
      have : m ≤ 2 * (m / 2) + 1 := by omega
      have h8 : (8 : ℝ) ≤ m := by exact_mod_cast hm8
      have hcast : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
      linarith
    have hlog_le : Real.log ((m / 2 : ℕ) : ℝ) ≤ Real.log ((m : ℝ) + 2) := by
      apply Real.log_le_log
      · exact_mod_cast (by omega : 0 < m / 2)
      · have : m / 2 ≤ m + 2 := by omega
        exact_mod_cast this
    have hlog_m2_pos : 0 < Real.log ((m / 2 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < m / 2))
    have hc1 : min (c0 / 8) (Real.log 3 / 10) ≤ c0 / 8 := min_le_left _ _
    have hstep1 : min (c0 / 8) (Real.log 3 / 10) * (m : ℝ) / Real.log ((m : ℝ) + 2) ≤
        (c0 * ((m / 2 : ℕ) : ℝ) / Real.log ((m / 2 : ℕ) : ℝ)) / 2 := by
      rw [div_div, div_le_div_iff₀ hlog_pos (by positivity)]
      have h1 : min (c0 / 8) (Real.log 3 / 10) * (m : ℝ) * 2 ≤ c0 * ((m / 2 : ℕ) : ℝ) := by
        have : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      have h2 := mul_le_mul h1 hlog_le hlog_m2_pos.le (by positivity)
      linarith
    have hstep2 : (c0 * ((m / 2 : ℕ) : ℝ) / Real.log ((m / 2 : ℕ) : ℝ)) / 2 ≤
        (Nat.primeCounting (m / 2) : ℝ) / 2 := by linarith
    have hstep3 : (Nat.primeCounting (m / 2) : ℝ) / 2 ≤ 1 + (oddPrimeCounting (m / 2) : ℝ) / 2 := by
      have hcast : (oddPrimeCounting (m / 2) : ℝ) + 1 = (Nat.primeCounting (m / 2) : ℝ) := by exact_mod_cast hodd
      linarith
    linarith

/-- Helper: for `n ≥ 3`, `centralBinom n ≤ (2n)^sqrt(2n) * 4^(2n/3) * (2n)^(π(2n) - π(n))`. -/
lemma centralBinom_le_mul_prod_bertrand (n : ℕ) (hn : 3 ≤ n) :
    Nat.centralBinom n ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
        (2 * n) ^ (Nat.primeCounting (2 * n) - Nat.primeCounting n) := by
  have n_pos : 0 < n := by omega
  have n2_pos : 1 ≤ 2 * n := by omega
  let S_lo := (Finset.range (2 * n / 3 + 1)).filter Nat.Prime
  let S_hi := (Finset.Ioc n (2 * n)).filter Nat.Prime
  have hprod_split : Nat.centralBinom n =
      (∏ p ∈ S_lo, p ^ (Nat.centralBinom n).factorization p) *
      (∏ p ∈ S_hi, p ^ (Nat.centralBinom n).factorization p) := by
    have hdisj : Disjoint S_lo S_hi := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [S_lo, S_hi, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp1 hp2
      omega
    rw [← Finset.prod_union hdisj]
    refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
    apply Finset.prod_subset
    · intro p hp
      simp only [Finset.mem_union, S_lo, S_hi, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp ⊢
      rcases hp with ⟨h1, _⟩ | ⟨⟨_, h1⟩, _⟩ <;> omega
    · intro p hp hp_not
      rw [Finset.mem_range, Nat.lt_succ_iff] at hp
      by_cases hp_prime : p.Prime
      · simp only [Finset.mem_union, S_lo, S_hi, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp_not
        have hgt : 2 * n / 3 < p := by
          by_contra hle; exact hp_not (Or.inl ⟨by omega, hp_prime⟩)
        have hle : p ≤ n := by
          by_contra hgt_n; exact hp_not (Or.inr ⟨⟨by omega, hp⟩, hp_prime⟩)
        have h3 : 2 * n < 3 * p := by omega
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul (by omega) hle h3, pow_zero]
      · rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hp_prime, pow_zero]
  rw [hprod_split]
  apply Nat.mul_le_mul
  · rw [← Finset.prod_filter_mul_prod_filter_not S_lo (· ≤ Nat.sqrt (2 * n))]
    apply Nat.mul_le_mul
    · refine (Finset.prod_le_prod fun p _ =>
        Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)).trans ?_
      rw [Finset.prod_const]
      refine Nat.pow_le_pow_right n2_pos ?_
      have hsub : S_lo.filter (· ≤ Nat.sqrt (2 * n)) ⊆ Finset.Icc 1 (Nat.sqrt (2 * n)) := by
        intro p hp
        simp only [Finset.mem_filter, S_lo, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.2.one_lt.le, hp.2⟩
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod (g := id) fun p hp => ?_).trans ?_
      · simp only [Finset.mem_filter, S_lo] at hp
        have hle1 : (Nat.centralBinom n).factorization p ≤ 1 :=
          Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 hp.2)
        exact (Nat.pow_le_pow_right hp.1.2.one_lt.le hle1).trans (by simp)
      · unfold primorial
        apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        intro p hp _
        exact (Finset.mem_filter.mp hp).2.one_lt.le
  · have hcard : S_hi.card = Nat.primeCounting (2 * n) - Nat.primeCounting n := by
      unfold Nat.primeCounting Nat.primeCounting'
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      have hsub : (Finset.range (n + 1)).filter Nat.Prime ⊆ (Finset.range (2 * n + 1)).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨by omega, hp.2⟩
      rw [← Finset.card_sdiff_of_subset hsub]
      congr 1
      ext p
      simp only [S_hi, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩
        exact ⟨⟨by omega, hp⟩, fun h => by omega⟩
      · rintro ⟨⟨h1, hp⟩, h2⟩
        have hgt : n < p := by by_contra hle; exact h2 ⟨by omega, hp⟩
        exact ⟨⟨hgt, by omega⟩, hp⟩
    calc ∏ p ∈ S_hi, p ^ (Nat.centralBinom n).factorization p
        ≤ ∏ _p ∈ S_hi, (2 * n) := by
          apply Finset.prod_le_prod
          intro p hp
          simp only [S_hi, Finset.mem_filter, Finset.mem_Ioc] at hp
          have hle1 : (Nat.centralBinom n).factorization p ≤ 1 := by
            apply Nat.factorization_choose_le_one
            nlinarith
          exact (Nat.pow_le_pow_right hp.2.one_lt.le hle1).trans (by simpa using hp.1.2)
      _ = (2 * n) ^ S_hi.card := by rw [Finset.prod_const]
      _ = (2 * n) ^ (Nat.primeCounting (2 * n) - Nat.primeCounting n) := by rw [hcard]

/-- Input 3: Erdős (1932) quantitative Bertrand lower bound:
    `∃ cB > 0, ∃ x0, ∀ x ≥ x0, cB * x / log x ≤ π_odd(2x) - π_odd(x)`. -/
theorem bertrand_quantitative :
    ∃ cB : ℝ, 0 < cB ∧ ∃ x0 : ℕ, ∀ x : ℕ, x0 ≤ x →
      cB * (x : ℝ) / Real.log (x : ℝ) ≤ (oddPrimeCounting (2 * x) - oddPrimeCounting x : ℝ) := by
  refine ⟨Real.log 2 / 6, by positivity, 20000000, ?_⟩
  intro n hn
  have hodd_eq : (oddPrimeCounting (2 * n) - oddPrimeCounting n : ℝ) =
      ((Nat.primeCounting (2 * n) - Nat.primeCounting n : ℕ) : ℝ) := by
    have h1 := oddPrimeCounting_eq_primeCounting_sub_one (by omega : 2 ≤ 2 * n)
    have h2 := oddPrimeCounting_eq_primeCounting_sub_one (by omega : 2 ≤ n)
    have hmono : Nat.primeCounting n ≤ Nat.primeCounting (2 * n) :=
      Nat.monotone_primeCounting (by omega)
    rw [Nat.cast_sub hmono]
    have h1r : (oddPrimeCounting (2 * n) : ℝ) + 1 = (Nat.primeCounting (2 * n) : ℝ) := by exact_mod_cast h1
    have h2r : (oddPrimeCounting n : ℝ) + 1 = (Nat.primeCounting n : ℝ) := by exact_mod_cast h2
    linarith
  rw [hodd_eq]
  set D : ℕ := Nat.primeCounting (2 * n) - Nat.primeCounting n
  have h4_lt : 4 ^ n < n * Nat.centralBinom n :=
    Nat.four_pow_lt_mul_centralBinom n (by omega)
  have hcb_le := centralBinom_le_mul_prod_bertrand n (by omega)
  have hcomb : 4 ^ n < n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ D) :=
    lt_of_lt_of_le h4_lt (Nat.mul_le_mul_left n hcb_le)
  have hcomb_r : (4 : ℝ) ^ n < (n : ℝ) * ((2 * (n : ℝ)) ^ Nat.sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3) * (2 * (n : ℝ)) ^ D) := by
    exact_mod_cast hcomb
  have h4n_pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hlog_ineq : Real.log ((4 : ℝ) ^ n) <
      Real.log ((n : ℝ) * ((2 * (n : ℝ)) ^ Nat.sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3) * (2 * (n : ℝ)) ^ D)) :=
    Real.log_lt_log h4n_pos hcomb_r
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  rw [Real.log_pow, Real.log_mul hn_pos.ne' (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at hlog_ineq
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have h2n3_le : ((2 * n / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) / 3 := by
    have : 3 * (2 * n / 3) ≤ 2 * n := Nat.mul_div_le (2 * n) 3
    have hcast : (3 : ℝ) * ((2 * n / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast this
    linarith
  have hsqrt_le : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity)]
    have : Nat.sqrt (2 * n) * Nat.sqrt (2 * n) ≤ 2 * n := Nat.sqrt_le (2 * n)
    have hcast : (Nat.sqrt (2 * n) : ℝ) * (Nat.sqrt (2 * n) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast this
    nlinarith
  set r : ℝ := Real.sqrt (Real.sqrt (2 * (n : ℝ)))
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h2n_pos)
  have hr2 : r ^ 2 = Real.sqrt (2 * (n : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hr4 : r ^ 4 = 2 * (n : ℝ) := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (2 * (n : ℝ))) ^ 2 := by rw [hr2]
      _ = 2 * (n : ℝ) := Real.sq_sqrt h2n_pos.le
  have hr_ge72 : (72 : ℝ) ≤ r := by
    by_contra hlt
    push Not at hlt
    have h1 : r ^ 2 < 72 ^ 2 := by nlinarith
    have h2 : r ^ 4 < 72 ^ 4 := by nlinarith
    have h3 : (40000000 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (by omega : 40000000 ≤ 2 * n)
    linarith
  have hlog2n_le : Real.log (2 * (n : ℝ)) ≤ 4 * r := by
    have h1 : Real.log (2 * (n : ℝ)) = 4 * Real.log r := by
      rw [← hr4, Real.log_pow]; ring
    have h2 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr_pos
    linarith
  have hlogn_le : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log hn_pos (by linarith)
  have hlog2n_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by linarith [show (1 : ℝ) ≤ n from by exact_mod_cast (by omega : 1 ≤ n)])
  have herr_bound : Real.log (n : ℝ) + (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) ≤ 8 * r ^ 3 := by
    have h1 : (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) ≤ r ^ 2 * (4 * r) := by
      rw [hr2]
      exact mul_le_mul hsqrt_le hlog2n_le hlog2n_nonneg (Real.sqrt_nonneg _)
    have h2 : 4 * r ≤ 4 * r ^ 3 := by nlinarith
    nlinarith
  have hlog2_gt : (69 / 100 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have herr_small : 8 * r ^ 3 ≤ (n : ℝ) * Real.log 2 / 3 := by
    have : 0 < r ^ 3 := by positivity
    nlinarith
  have hD_mul : (n : ℝ) * Real.log 2 / 3 ≤ (D : ℝ) * Real.log (2 * (n : ℝ)) := by
    have hlog4_pos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    have h2n3_mul : ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 ≤ (2 * (n : ℝ) / 3) * Real.log 4 :=
      mul_le_mul_of_nonneg_right h2n3_le hlog4_pos.le
    rw [hlog4] at hlog_ineq h2n3_mul
    linarith
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog2_le_logn : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n))
  have hlog2n_le_2logn : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) hn_pos.ne']
    linarith
  rw [div_le_iff₀ hlogn_pos]
  have hD_nonneg : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  nlinarith

/-- Input 4: Elementary binomial divisibility for Stage 2:
    `∏_{b < p ≤ a} p ∣ Nat.choose a b` whenever `b ≤ a < 2 * b`. -/
theorem uTop_dvd_choose {a b : ℕ} (hba : b ≤ a) (h2b : a < 2 * b) :
    (∏ p ∈ (Finset.Ioc b a).filter Nat.Prime, p) ∣ Nat.choose a b := by
  apply Finset.prod_primes_dvd
  · intro p hp; exact (Finset.mem_filter.mp hp).2.prime
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    rcases hp with ⟨⟨hb_lt, ha_le⟩, hp_prime⟩
    have hfact : Nat.choose a b * b.factorial * (a - b).factorial = a.factorial :=
      Nat.choose_mul_factorial_mul_factorial hba
    have hp_dvd_a : p ∣ a.factorial := hp_prime.dvd_factorial.mpr ha_le
    have hp_ndvd_b : ¬ (p ∣ b.factorial) := by
      rw [hp_prime.dvd_factorial]; omega
    have hp_ndvd_ab : ¬ (p ∣ (a - b).factorial) := by
      rw [hp_prime.dvd_factorial]; omega
    rw [← hfact] at hp_dvd_a
    rcases hp_prime.dvd_mul.mp hp_dvd_a with h1 | h2
    · rcases hp_prime.dvd_mul.mp h1 with h3 | h4
      · exact h3
      · exact absurd h4 hp_ndvd_b
    · exact absurd h2 hp_ndvd_ab

end Erdos18

#print axioms Erdos18.oddPrimorial_lt_two_pow
#print axioms Erdos18.prime_counting_lower
#print axioms Erdos18.prefix_entropy_rate_lower
#print axioms Erdos18.bertrand_quantitative
#print axioms Erdos18.uTop_dvd_choose
