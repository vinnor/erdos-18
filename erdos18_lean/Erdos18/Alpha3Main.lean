import Erdos18.Alpha3Covering
import Erdos18.MainTheorem

/-!
# Erdos18/Alpha3Main.lean — Unconditional `h(n!) = O((log n)^3 (log log n)^2)` and `O((log n)^4)`

Formalizes Lemma 4*, Stage 2*, and the main theorems of `work/prover4.md` (cleared by `Breaker-3`):
1. `Erdos18.erdos18_alpha3_loglog2`:
     `∃ C : ℝ, ∀ n ≥ 2, ∀ t, 1 ≤ t → t ≤ n! → ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n! ∧ 0 < d) ∧ S.sum id = t ∧ (S.card : ℝ) ≤ C * (Real.log n)^3 * (Real.log (Real.log (n + 16)))^2`.
2. `Erdos18.erdos18_alpha4`:
     Immediate corollary `h(n!) = O((log n)^4)`.
-/

namespace Erdos18

open Finset Nat Real

/-! ## Part 1: Elementary Log-Log Comparison Helpers -/

/-- For all `B : ℕ`, `1 < Real.log (Real.log (B + 16))`. -/
lemma one_lt_log_log_add16_all (B : ℕ) :
    1 < Real.log (Real.log ((B : ℝ) + 16)) := by
  have h16 : (16 : ℝ) ≤ (B : ℝ) + 16 := by linarith [show (0 : ℝ) ≤ (B : ℝ) by positivity]
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; ring
  have hexp_lt : Real.exp 1 < Real.log ((B : ℝ) + 16) := by
    have h1 := Real.exp_one_lt_d9
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log (16 : ℝ) ≤ Real.log ((B : ℝ) + 16) := Real.log_le_log (by norm_num) h16
    linarith
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) hexp_lt

/-- For all `k ≥ 2`, `Real.log (Real.log (k + 16)) ≤ Real.log (k + 2)`. -/
lemma log_log_add16_le_log_add2 {k : ℕ} (hk : 2 ≤ k) :
    Real.log (Real.log ((k : ℝ) + 16)) ≤ Real.log ((k : ℝ) + 2) := by
  have hlog_pos : 0 < Real.log ((k : ℝ) + 16) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k + 16))
  apply Real.log_le_log hlog_pos
  by_cases hk4 : 4 ≤ k
  · have hdiv_pos : (0 : ℝ) < ((k : ℝ) + 16) / 4 := by positivity
    have hmul : (k : ℝ) + 16 = 4 * (((k : ℝ) + 16) / 4) := by ring
    rw [hmul, Real.log_mul (by norm_num) hdiv_pos.ne']
    have h1 : Real.log (((k : ℝ) + 16) / 4) ≤ ((k : ℝ) + 16) / 4 - 1 :=
      Real.log_le_sub_one_of_pos hdiv_pos
    have hlog4 : Real.log (4 : ℝ) < 1.4 := by
      have h2 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      linarith [Real.log_two_lt_d9]
    have hk4r : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
    linarith
  · have h19 : (k : ℝ) + 16 ≤ 19 := by exact_mod_cast (by omega : k + 16 ≤ 19)
    have h4 : (4 : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ k + 2)
    have he3 : (19 : ℝ) < Real.exp 3 := by
      have hpow : Real.exp 3 = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [hpow]
      have hlt : (2.71 : ℝ) ^ 3 < (Real.exp 1) ^ 3 :=
        pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by norm_num)
      linarith [show (19 : ℝ) < (2.71 : ℝ) ^ 3 by norm_num]
    have hlog19 : Real.log ((k : ℝ) + 16) < 3 := by
      calc Real.log ((k : ℝ) + 16) ≤ Real.log (19 : ℝ) := Real.log_le_log (by positivity) h19
        _ < Real.log (Real.exp 3) := Real.log_lt_log (by norm_num) he3
        _ = 3 := Real.log_exp 3
    linarith

/-- The α = 3 covering count `R_alpha3` is always bounded above by the α = 5 covering count `R_alpha5`. -/
lemma ceil_alpha3_le_ceil_alpha5 {C_cov : ℝ} (hC : 0 < C_cov) {k : ℕ} (hk : 2 ≤ k) :
    Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) ≤
      Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) := by
  apply Nat.ceil_mono
  have hll_nn : 0 ≤ Real.log (Real.log ((k : ℝ) + 16)) := (one_lt_log_log_add16_all k).le.trans' (by norm_num)
  have hsq : (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 ≤ (Real.log ((k : ℝ) + 2)) ^ 2 :=
    pow_le_pow_left₀ hll_nn (log_log_add16_le_log_add2 hk) 2
  have hcoef_nn : 0 ≤ C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 := by positivity
  calc C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2
      ≤ C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log ((k : ℝ) + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hcoef_nn
    _ = C_cov * (Real.log ((k : ℝ) + 2)) ^ 4 := by ring

/-! ## Part 2: Lemma 4* (Zero-Loss 2-adic Carry Recursion) -/

/-- **Lemma 4* (Carry Recursion for α = 3)**:
    Every `r < 2^B` (with `2 * B ≤ E`) is a sum of at most
    `C4 * (log (B + 2))^2 * (log (log (B + 16)))^2` distinct positive divisors of
    `2^E * oddPrimorial (E / 4)`. -/
theorem lemma4_carry_recursion_alpha3 :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ (B E r : ℕ), 2 * B ≤ E → r < 2 ^ B →
      ∃ S : Finset ℕ,
        (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ E * oddPrimorial (E / 4)) ∧
        S.sum id = r ∧
        (S.card : ℝ) ≤ C4 * (Real.log ((B : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 := by
  rcases mod_two_pow_covering_alpha3 with ⟨C_cov, hC_cov, hcov⟩
  rcases exists_bertrand_exceeds_R C_cov hC_cov with ⟨k0, hk0, hbert⟩
  rcases exists_B0_carry C_cov hC_cov k0 hk0 with ⟨B0, hB0, hcarry⟩
  set C4 : ℝ := max (5 * (B0 : ℝ)) (4 * (2 * C_cov + 2))
  have hC4_pos : 0 < C4 := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨C4, hC4_pos, ?_⟩
  intro B
  induction B using Nat.strong_induction_on with
  | ind B ih =>
    intro E r h2BE hr
    by_cases hr0 : r = 0
    · subst hr0
      refine ⟨∅, by simp, by simp, ?_⟩
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    by_cases hB_small : B ≤ B0
    · rcases binary_rep hr with ⟨S, hcard, hprop, hsum⟩
      refine ⟨S, ?_, hsum, ?_⟩
      · intro d hd
        rcases hprop d hd with ⟨hpos, hdvd, _⟩
        refine ⟨hpos, dvd_trans hdvd (dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega)) _)⟩
      · have hlog2_ge : (0.69 : ℝ) ≤ Real.log ((B : ℝ) + 2) := by
          have h2 : (2 : ℝ) ≤ (B : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ B by positivity]
          linarith [Real.log_le_log (by norm_num) h2, Real.log_two_gt_d9]
        have hpow_ge : (0.4 : ℝ) ≤ (Real.log ((B : ℝ) + 2)) ^ 2 := by
          have : (0.69 : ℝ) ^ 2 ≤ (Real.log ((B : ℝ) + 2)) ^ 2 := pow_le_pow_left₀ (by norm_num) hlog2_ge 2
          linarith [show (0.4 : ℝ) ≤ (0.69 : ℝ) ^ 2 by norm_num]
        have hll_sq : (1 : ℝ) ≤ (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 := by
          have h1 := one_lt_log_log_add16_all B
          nlinarith
        have hcard_le : (S.card : ℝ) ≤ (B0 : ℝ) := by exact_mod_cast le_trans hcard hB_small
        have hC4_ge : 5 * (B0 : ℝ) ≤ C4 := le_max_left _ _
        have hF_ge : (0.4 : ℝ) ≤ (Real.log ((B : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 := by
          nlinarith
        nlinarith
    push Not at hB_small
    by_cases hr_small : r < 2 ^ (B - 1)
    · have hB_lt : B - 1 < B := by omega
      rcases ih (B - 1) hB_lt E r (by omega) hr_small with ⟨S, hprop, hsum, hcard⟩
      refine ⟨S, hprop, hsum, le_trans hcard ?_⟩
      have hlog_le : Real.log (((B - 1 : ℕ) : ℝ) + 2) ≤ Real.log ((B : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : B - 1 + 2 ≤ B + 2))
      have hlog_sq : (Real.log (((B - 1 : ℕ) : ℝ) + 2)) ^ 2 ≤ (Real.log ((B : ℝ) + 2)) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B - 1 + 2))) hlog_le 2
      have hll_le : Real.log (Real.log (((B - 1 : ℕ) : ℝ) + 16)) ≤ Real.log (Real.log ((B : ℝ) + 16)) :=
        Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < B - 1 + 16)))
          (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : B - 1 + 16 ≤ B + 16)))
      have hll_sq : (Real.log (Real.log (((B - 1 : ℕ) : ℝ) + 16))) ^ 2 ≤
          (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 :=
        pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all (B - 1)]) hll_le 2
      have hmul := mul_le_mul hlog_sq hll_sq (by positivity) (by positivity)
      calc C4 * (Real.log (((B - 1 : ℕ) : ℝ) + 2)) ^ 2 * (Real.log (Real.log (((B - 1 : ℕ) : ℝ) + 16))) ^ 2
          = C4 * ((Real.log (((B - 1 : ℕ) : ℝ) + 2)) ^ 2 * (Real.log (Real.log (((B - 1 : ℕ) : ℝ) + 16))) ^ 2) := by ring
        _ ≤ C4 * ((Real.log ((B : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((B : ℝ) + 16))) ^ 2) :=
            mul_le_mul_of_nonneg_left hmul hC4_pos.le
        _ = C4 * (Real.log ((B : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 := by ring
    push Not at hr_small
    rcases hcarry B hB_small with ⟨hk_ge_k0, hb_lt_B, hpow43, hcarry_bound⟩
    set b := Nat.sqrt B + 1
    set k := B - b
    have hk_ge2 : 2 ≤ k := by omega
    have hQ_ge3 : 3 ≤ k / 2 := by omega
    have hR_le : Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) ≤
        Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) := ceil_alpha3_le_ceil_alpha5 hC_cov hk_ge2
    have hbert_k : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) ≤
        oddPrimeCounting (k / 2) - oddPrimeCounting ((k + 1) / 4) :=
      le_trans (Nat.mul_le_mul_left 2 hR_le) (hbert k hk_ge_k0)
    rcases hcov k (k / 2) hk_ge2 hQ_ge3 hbert_k r with ⟨S1, hS1_card, hS1_prop, hS1_mod⟩
    have hS1_sum_le : S1.sum id ≤ 2 ^ (B - 1) := by
      have h1 : S1.sum id ≤ S1.card * ((k / 2) * 2 ^ k) := by
        calc S1.sum id ≤ ∑ _ ∈ S1, ((k / 2) * 2 ^ k) :=
              Finset.sum_le_sum fun d hd => le_of_lt (hS1_prop d hd).2.2.2
          _ = S1.card * ((k / 2) * 2 ^ k) := by simp
      have h2 : S1.card * ((k / 2) * 2 ^ k) ≤ 2 ^ (b - 1) * 2 ^ k := by
        calc S1.card * ((k / 2) * 2 ^ k)
            = (S1.card * (k / 2)) * 2 ^ k := by ring
          _ ≤ (2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (k / 2)) * 2 ^ k :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_trans hS1_card (Nat.mul_le_mul_left 2 hR_le)))
          _ ≤ 2 ^ (b - 1) * 2 ^ k := Nat.mul_le_mul_right _ hcarry_bound
      have h3 : 2 ^ (b - 1) * 2 ^ k = 2 ^ (B - 1) := by rw [← pow_add]; congr 1; omega
      omega
    have hS1_le_r : S1.sum id ≤ r := le_trans hS1_sum_le hr_small
    have hdvd_diff : 2 ^ k ∣ (r - S1.sum id) := by
      have h1 := Nat.div_add_mod r (2 ^ k)
      have h2 := Nat.div_add_mod (S1.sum id) (2 ^ k)
      refine ⟨r / 2 ^ k - S1.sum id / 2 ^ k, ?_⟩
      rw [Nat.mul_sub]; omega
    set r' := (r - S1.sum id) / 2 ^ k
    have hr'_eq : S1.sum id + 2 ^ k * r' = r := by
      have hmul : 2 ^ k * r' = r - S1.sum id := Nat.mul_div_cancel' hdvd_diff
      omega
    have hr'_lt : r' < 2 ^ b := by
      have h2B : 2 ^ B = 2 ^ k * 2 ^ b := by rw [← pow_add]; congr 1; omega
      have hmul_lt : 2 ^ k * r' < 2 ^ k * 2 ^ b := by omega
      exact Nat.lt_of_mul_lt_mul_left hmul_lt
    have h2b_le : 2 * b ≤ E - k := by omega
    rcases ih b hb_lt_B (E - k) r' h2b_le hr'_lt with ⟨S2, hS2_prop, hS2_sum, hS2_card⟩
    let S2' := S2.image (2 ^ k * ·)
    have hdisj : Disjoint S1 S2' := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      rw [Finset.mem_image] at hd2
      rcases hd2 with ⟨a, _, rfl⟩
      exact (hS1_prop (2 ^ k * a) hd1).2.2.1 (dvd_mul_right (2 ^ k) a)
    refine ⟨S1 ∪ S2', ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_union] at hd
      rcases hd with hd1 | hd2
      · rcases hS1_prop d hd1 with ⟨hpos, hdvd, _, _⟩
        refine ⟨hpos, dvd_trans hdvd ?_⟩
        exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) (oddPrimorial_dvd_oddPrimorial (by omega))
      · rw [Finset.mem_image] at hd2
        rcases hd2 with ⟨a, ha, rfl⟩
        rcases hS2_prop a ha with ⟨hpos, hdvd⟩
        refine ⟨Nat.mul_pos (by positivity) hpos, ?_⟩
        have hmul_dvd : 2 ^ k * a ∣ 2 ^ k * (2 ^ (E - k) * oddPrimorial ((E - k) / 4)) :=
          Nat.mul_dvd_mul_left (2 ^ k) hdvd
        have hrew : 2 ^ k * (2 ^ (E - k) * oddPrimorial ((E - k) / 4)) =
            2 ^ E * oddPrimorial ((E - k) / 4) := by
          rw [← mul_assoc, ← pow_add, show k + (E - k) = E by omega]
        rw [hrew] at hmul_dvd
        exact dvd_trans hmul_dvd (Nat.mul_dvd_mul_left (2 ^ E) (oddPrimorial_dvd_oddPrimorial (by omega)))
    · rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ c _ h => Nat.eq_of_mul_eq_mul_left (by positivity) h)]
      simp only [id_eq]; rw [← Finset.mul_sum]
      have hsum2 : S2.sum (fun a => a) = r' := hS2_sum
      rw [hsum2]; exact hr'_eq
    · have hcard_eq : (S1 ∪ S2').card = S1.card + S2.card := by
        rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective S2 (fun a c h => Nat.eq_of_mul_eq_mul_left (by positivity) h)]
      rw [hcard_eq, Nat.cast_add]
      set FB : ℝ := (Real.log ((B : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((B : ℝ) + 16))) ^ 2
      have hlogb_le : Real.log ((b : ℝ) + 2) ≤ (3 / 4 : ℝ) * Real.log ((B : ℝ) + 2) := by
        have hcast : (((b : ℝ) + 2) ^ 4) ≤ (((B : ℝ) + 2) ^ 3) := by exact_mod_cast hpow43
        have hlog_ineq : Real.log (((b : ℝ) + 2) ^ 4) ≤ Real.log (((B : ℝ) + 2) ^ 3) :=
          Real.log_le_log (by positivity) hcast
        rw [Real.log_pow, Real.log_pow] at hlog_ineq
        push_cast at hlog_ineq
        linarith
      have hlogb_sq : (Real.log ((b : ℝ) + 2)) ^ 2 ≤ (9 / 16 : ℝ) * (Real.log ((B : ℝ) + 2)) ^ 2 := by
        have h1 : (Real.log ((b : ℝ) + 2)) ^ 2 ≤ ((3 / 4 : ℝ) * Real.log ((B : ℝ) + 2)) ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b + 2))) hlogb_le 2
        linarith [show ((3 / 4 : ℝ) * Real.log ((B : ℝ) + 2)) ^ 2 = (9 / 16 : ℝ) * (Real.log ((B : ℝ) + 2)) ^ 2 by ring]
      have hllb_sq : (Real.log (Real.log ((b : ℝ) + 16))) ^ 2 ≤ (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 := by
        have h1 : Real.log (Real.log ((b : ℝ) + 16)) ≤ Real.log (Real.log ((B : ℝ) + 16)) :=
          Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < b + 16)))
            (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : b + 16 ≤ B + 16)))
        exact pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all b]) h1 2
      have hS2_le : (S2.card : ℝ) ≤ (9 / 16 : ℝ) * C4 * FB := by
        have hmul := mul_le_mul hlogb_sq hllb_sq (by positivity) (by positivity)
        have h1 : (Real.log ((b : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((b : ℝ) + 16))) ^ 2 ≤ (9 / 16 : ℝ) * FB := by
          dsimp [FB]; linarith
        calc (S2.card : ℝ)
            ≤ C4 * (Real.log ((b : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((b : ℝ) + 16))) ^ 2 := hS2_card
          _ = C4 * ((Real.log ((b : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((b : ℝ) + 16))) ^ 2) := by ring
          _ ≤ C4 * ((9 / 16 : ℝ) * FB) := mul_le_mul_of_nonneg_left h1 hC4_pos.le
          _ = (9 / 16 : ℝ) * C4 * FB := by ring
      have hFB_ge1 : (1 : ℝ) ≤ FB := by
        have hlogB_ge1 : (1 : ℝ) ≤ Real.log ((B : ℝ) + 2) := by
          have h4 : (4 : ℝ) ≤ (B : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ B + 2)
          have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
          linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
        have hll_gt1 := one_lt_log_log_add16_all B
        have h1 : (1 : ℝ) ≤ (Real.log ((B : ℝ) + 2)) ^ 2 := one_le_pow₀ hlogB_ge1
        have h2 : (1 : ℝ) ≤ (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 := one_le_pow₀ hll_gt1.le
        dsimp [FB]; nlinarith
      have hS1_le : (S1.card : ℝ) ≤ (2 * C_cov + 2) * FB := by
        have hc1 : (S1.card : ℝ) ≤
            2 * (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) : ℝ) := by
          exact_mod_cast hS1_card
        have hceil : (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) : ℝ) ≤
            C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 + 1 :=
          (Nat.ceil_lt_add_one (by positivity)).le
        have hlogk_sq : (Real.log ((k : ℝ) + 2)) ^ 2 ≤ (Real.log ((B : ℝ) + 2)) ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k + 2)))
            (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 2 ≤ B + 2))) 2
        have hllk_sq : (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 ≤ (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 :=
          pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all k])
            (Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < k + 16)))
              (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 16 ≤ B + 16)))) 2
        have hFk_le : (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 ≤ FB :=
          mul_le_mul hlogk_sq hllk_sq (by positivity) (by positivity)
        have hC_Fk : C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 ≤ C_cov * FB := by
          calc C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2
              = C_cov * ((Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) := by ring
            _ ≤ C_cov * FB := mul_le_mul_of_nonneg_left hFk_le hC_cov.le
        linarith
      have hC4_ge : 4 * (2 * C_cov + 2) ≤ C4 := le_max_right _ _
      have hFB_nn : 0 ≤ FB := by positivity
      have hcomb : (2 * C_cov + 2) * FB + (9 / 16 : ℝ) * C4 * FB ≤ C4 * FB := by nlinarith
      calc (S1.card : ℝ) + (S2.card : ℝ)
          ≤ (2 * C_cov + 2) * FB + (9 / 16 : ℝ) * C4 * FB := by linarith
        _ ≤ C4 * FB := hcomb
        _ = C4 * (Real.log ((B : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((B : ℝ) + 16))) ^ 2 := by dsimp [FB]; ring

/-! ## Part 3: Stage 2* (Self-Similar Tail Recursion) -/

set_option maxHeartbeats 600000 in
/-- **Stage 2* (Tail Recursion for α = 3)**:
    Every `x < 2^E * oddPrimorial (E / 4)` (for `E ≥ 1`) is a sum of at most
    `C5 * (log (E + 2))^3 * (log (log (E + 16)))^2` distinct positive divisors of
    `2^E * oddPrimorial (E / 4)`. -/
theorem stage2_tail_recursion_alpha3 :
    ∃ C5 : ℝ, 0 < C5 ∧ ∀ (E x : ℕ), 1 ≤ E → x < 2 ^ E * oddPrimorial (E / 4) →
      ∃ S : Finset ℕ,
        (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ E * oddPrimorial (E / 4)) ∧
        S.sum id = x ∧
        (S.card : ℝ) ≤ C5 * (Real.log ((E : ℝ) + 2)) ^ 3 * (Real.log (Real.log ((E : ℝ) + 16))) ^ 2 := by
  rcases mod_two_pow_covering_alpha3 with ⟨C_cov, hC_cov, hcov⟩
  rcases exists_bertrand_exceeds_R C_cov hC_cov with ⟨k0, hk0, hbert⟩
  rcases lemma4_carry_recursion_alpha3 with ⟨C4, hC4, hlem4⟩
  rcases exists_E0_stage2 C_cov hC_cov k0 hk0 with ⟨E0, hE0, hstage2⟩
  set M_base : ℕ := 2 ^ E0 * oddPrimorial (E0 / 4) + 1
  set C5 : ℝ := max (10 * (M_base : ℝ)) (2 * (2 * C_cov + 2 + C4))
  have hC5_pos : 0 < C5 := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨C5, hC5_pos, ?_⟩
  intro E
  induction E using Nat.strong_induction_on with
  | ind E ih =>
    intro x hE1 hx
    by_cases hE_small : E ≤ E0
    · rcases practical_M_tail E hE1 x hx with ⟨S, hprop, hsum⟩
      refine ⟨S, hprop, hsum, ?_⟩
      have hsub : S ⊆ Finset.range M_base := by
        intro d hd
        rw [Finset.mem_range]
        have hd_le : d ≤ 2 ^ E * oddPrimorial (E / 4) :=
          Nat.le_of_dvd (Nat.mul_pos (by positivity) (oddPrimorial_pos _)) (hprop d hd).2
        have hM_le : 2 ^ E * oddPrimorial (E / 4) ≤ 2 ^ E0 * oddPrimorial (E0 / 4) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hE_small)
            (Nat.le_of_dvd (oddPrimorial_pos _) (oddPrimorial_dvd_oddPrimorial (by omega)))
        omega
      have hcard_le : (S.card : ℝ) ≤ (M_base : ℝ) := by
        exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
      have hlog_ge : (0.69 : ℝ) ≤ Real.log ((E : ℝ) + 2) := by
        have h2 : (2 : ℝ) ≤ (E : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ E by positivity]
        linarith [Real.log_le_log (by norm_num) h2, Real.log_two_gt_d9]
      have hpow3_ge : (0.3 : ℝ) ≤ (Real.log ((E : ℝ) + 2)) ^ 3 := by
        have : (0.69 : ℝ) ^ 3 ≤ (Real.log ((E : ℝ) + 2)) ^ 3 := pow_le_pow_left₀ (by norm_num) hlog_ge 3
        linarith [show (0.3 : ℝ) ≤ (0.69 : ℝ) ^ 3 by norm_num]
      have hll_sq : (1 : ℝ) ≤ (Real.log (Real.log ((E : ℝ) + 16))) ^ 2 := by
        have := one_lt_log_log_add16_all E; nlinarith
      have hC5_ge : 10 * (M_base : ℝ) ≤ C5 := le_max_left _ _
      have hprod_ge : (0.3 : ℝ) ≤ (Real.log ((E : ℝ) + 2)) ^ 3 * (Real.log (Real.log ((E : ℝ) + 16))) ^ 2 := by
        nlinarith
      nlinarith
    push Not at hE_small
    by_cases hx_small : x < 2 ^ (E / 2)
    · rcases hlem4 (E / 2) E x (by omega) hx_small with ⟨S, hprop, hsum, hcard⟩
      refine ⟨S, hprop, hsum, ?_⟩
      have hlog_le : Real.log ((E / 2 : ℕ) + 2 : ℝ) ≤ Real.log ((E : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E / 2 + 2 ≤ E + 2))
      have hlog2 : (Real.log ((E / 2 : ℕ) + 2 : ℝ)) ^ 2 ≤ (Real.log ((E : ℝ) + 2)) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E / 2 + 2))) hlog_le 2
      have hll_sq : (Real.log (Real.log (((E / 2 : ℕ) : ℝ) + 16))) ^ 2 ≤
          (Real.log (Real.log ((E : ℝ) + 16))) ^ 2 :=
        pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all (E / 2)])
          (Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < E / 2 + 16)))
            (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E / 2 + 16 ≤ E + 16)))) 2
      have hlog_ge1 : (1 : ℝ) ≤ Real.log ((E : ℝ) + 2) := by
        have h4 : (4 : ℝ) ≤ (E : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ E + 2)
        have hlog4' : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
        linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
      have hpow23 : (Real.log ((E : ℝ) + 2)) ^ 2 ≤ (Real.log ((E : ℝ) + 2)) ^ 3 := by
        have : (Real.log ((E : ℝ) + 2)) ^ 2 * 1 ≤ (Real.log ((E : ℝ) + 2)) ^ 2 * Real.log ((E : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
        linarith
      have hC4_le : C4 ≤ C5 := le_trans (by linarith) (le_max_right _ _)
      have hmul := mul_le_mul (le_trans hlog2 hpow23) hll_sq (by positivity) (by positivity)
      calc (S.card : ℝ)
          ≤ C4 * (Real.log ((E / 2 : ℕ) + 2 : ℝ)) ^ 2 * (Real.log (Real.log (((E / 2 : ℕ) : ℝ) + 16))) ^ 2 := hcard
        _ = C4 * ((Real.log ((E / 2 : ℕ) + 2 : ℝ)) ^ 2 * (Real.log (Real.log (((E / 2 : ℕ) : ℝ) + 16))) ^ 2) := by ring
        _ ≤ C4 * ((Real.log ((E : ℝ) + 2)) ^ 3 * (Real.log (Real.log ((E : ℝ) + 16))) ^ 2) :=
            mul_le_mul_of_nonneg_left hmul hC4.le
        _ ≤ C5 * ((Real.log ((E : ℝ) + 2)) ^ 3 * (Real.log (Real.log ((E : ℝ) + 16))) ^ 2) :=
            mul_le_mul_of_nonneg_right hC4_le (by positivity)
        _ = C5 * (Real.log ((E : ℝ) + 2)) ^ 3 * (Real.log (Real.log ((E : ℝ) + 16))) ^ 2 := by ring
    push Not at hx_small
    rcases hstage2 E hE_small with ⟨hk_ge_k0, hcarry2, hlog_drop⟩
    set k := 45 * E / 100
    set E_next := E - k
    set U_top := ∏ p ∈ (Finset.Ioc (E_next / 4) (E / 4)).filter Nat.Prime, p
    have hU_pos : 0 < U_top := Finset.prod_pos fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp; omega
    have hodd_split : oddPrimorial (E / 4) = oddPrimorial (E_next / 4) * U_top :=
      oddPrimorial_eq_mul_uTop (by omega) (by omega)
    have hU_lt : U_top < 2 ^ (E_next / 2) := by
      have hdvd : U_top ∣ Nat.choose (E / 4) (E_next / 4) := uTop_dvd_choose (by omega) (by omega)
      have hch_pos : 0 < Nat.choose (E / 4) (E_next / 4) := Nat.choose_pos (by omega)
      have hU_le_ch : U_top ≤ Nat.choose (E / 4) (E_next / 4) := Nat.le_of_dvd hch_pos hdvd
      have hch_le : Nat.choose (E / 4) (E_next / 4) ≤ 2 ^ (E / 4) := by
        have hsum := Nat.sum_range_choose (E / 4)
        rw [← hsum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      have hpow_lt : 2 ^ (E / 4) < 2 ^ (E_next / 2) := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have hR_le : Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) ≤
        Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) := ceil_alpha3_le_ceil_alpha5 hC_cov (by omega)
    have hbert_stage2 : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) ≤
        oddPrimeCounting (E / 4) - oddPrimeCounting ((k + 1) / 4) := by
      have hb := hbert k hk_ge_k0
      have hmono := oddPrimeCounting_mono (show k / 2 ≤ E / 4 by omega)
      have hmul := Nat.mul_le_mul_left 2 hR_le
      omega
    rcases hcov k (E / 4) (by omega) (by omega) hbert_stage2 x with ⟨S1, hS1_card, hS1_prop, hS1_mod⟩
    have hS1_sum_le : S1.sum id ≤ 2 ^ (E / 2) := by
      have h1 : S1.sum id ≤ S1.card * ((E / 4) * 2 ^ k) := by
        calc S1.sum id ≤ ∑ _ ∈ S1, ((E / 4) * 2 ^ k) :=
              Finset.sum_le_sum fun d hd => le_of_lt (hS1_prop d hd).2.2.2
          _ = S1.card * ((E / 4) * 2 ^ k) := by simp
      have h2 : S1.card * ((E / 4) * 2 ^ k) ≤ 2 ^ (E / 2) := by
        calc S1.card * ((E / 4) * 2 ^ k)
            = S1.card * (E / 4) * 2 ^ k := by ring
          _ ≤ 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (E / 4) * 2 ^ k :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_trans hS1_card (Nat.mul_le_mul_left 2 hR_le)))
          _ ≤ 2 ^ (E / 2) := hcarry2
      omega
    have hS1_le_x : S1.sum id ≤ x := le_trans hS1_sum_le hx_small
    have hdvd_diff : 2 ^ k ∣ (x - S1.sum id) := by
      have h1 := Nat.div_add_mod x (2 ^ k)
      have h2 := Nat.div_add_mod (S1.sum id) (2 ^ k)
      refine ⟨x / 2 ^ k - S1.sum id / 2 ^ k, ?_⟩
      rw [Nat.mul_sub]; omega
    set y := (x - S1.sum id) / 2 ^ k
    have hy_eq : S1.sum id + 2 ^ k * y = x := by
      have hmul : 2 ^ k * y = x - S1.sum id := Nat.mul_div_cancel' hdvd_diff
      omega
    have hy_lt : y < (2 ^ E_next * oddPrimorial (E_next / 4)) * U_top := by
      have hM_eq : 2 ^ E * oddPrimorial (E / 4) = 2 ^ k * ((2 ^ E_next * oddPrimorial (E_next / 4)) * U_top) := by
        rw [hodd_split]
        have h2E : 2 ^ E = 2 ^ k * 2 ^ E_next := by rw [← pow_add]; congr 1; omega
        rw [h2E]; ring
      have hmul_lt : 2 ^ k * y < 2 ^ k * ((2 ^ E_next * oddPrimorial (E_next / 4)) * U_top) := by omega
      exact Nat.lt_of_mul_lt_mul_left hmul_lt
    set r1 := y % U_top
    set q1 := y / U_top
    have hr1_lt : r1 < 2 ^ (E_next / 2) := lt_trans (Nat.mod_lt y hU_pos) hU_lt
    have hq1_lt : q1 < 2 ^ E_next * oddPrimorial (E_next / 4) := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    rcases hlem4 (E_next / 2) E_next r1 (by omega) hr1_lt with ⟨S2_raw, hS2_prop, hS2_sum, hS2_card⟩
    rcases ih E_next (by omega) q1 (by omega) hq1_lt with ⟨S3_raw, hS3_prop, hS3_sum, hS3_card⟩
    let S2 := S2_raw.image (2 ^ k * ·)
    let S3 := S3_raw.image (2 ^ k * U_top * ·)
    have hdisj12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2; rw [Finset.mem_image] at hd2; rcases hd2 with ⟨a, _, rfl⟩
      exact (hS1_prop (2 ^ k * a) hd1).2.2.1 (dvd_mul_right (2 ^ k) a)
    have hdisj13 : Disjoint S1 S3 := by
      rw [Finset.disjoint_left]
      intro d hd1 hd3; rw [Finset.mem_image] at hd3; rcases hd3 with ⟨b, _, rfl⟩
      exact (hS1_prop (2 ^ k * U_top * b) hd1).2.2.1 (by rw [mul_assoc]; exact dvd_mul_right (2 ^ k) (U_top * b))
    have hdisj23 : Disjoint S2 S3 := by
      rw [Finset.disjoint_left]
      intro d hd2 hd3; rw [Finset.mem_image] at hd2 hd3
      rcases hd2 with ⟨a, ha, rfl⟩; rcases hd3 with ⟨b, hb, hab⟩
      have hb_pos : 0 < b := (hS3_prop b hb).1
      have ha_eq : a = U_top * b := by
        have h1 : 2 ^ k * (U_top * b) = 2 ^ k * a := by linarith
        exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm
      have ha_le : a ≤ r1 := by rw [← hS2_sum]; exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) ha
      have hU_le : U_top ≤ U_top * b := Nat.le_mul_of_pos_right U_top hb_pos
      have hr1_lt_U : r1 < U_top := Nat.mod_lt y hU_pos
      omega
    have hdisj12_3 : Disjoint (S1 ∪ S2) S3 := Finset.disjoint_union_left.mpr ⟨hdisj13, hdisj23⟩
    refine ⟨(S1 ∪ S2) ∪ S3, ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_union, Finset.mem_union] at hd
      rcases hd with (hd1 | hd2) | hd3
      · rcases hS1_prop d hd1 with ⟨hpos, hdvd, _, _⟩
        exact ⟨hpos, dvd_trans hdvd (Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by omega)) _)⟩
      · rw [Finset.mem_image] at hd2; rcases hd2 with ⟨a, ha, rfl⟩
        rcases hS2_prop a ha with ⟨hpos, hdvd⟩
        refine ⟨Nat.mul_pos (by positivity) hpos, ?_⟩
        have hmul := Nat.mul_dvd_mul_left (2 ^ k) hdvd
        have hrew : 2 ^ k * (2 ^ E_next * oddPrimorial (E_next / 4)) = 2 ^ E * oddPrimorial (E_next / 4) := by
          rw [← mul_assoc, ← pow_add, show k + E_next = E by omega]
        rw [hrew] at hmul
        exact dvd_trans hmul (Nat.mul_dvd_mul_left (2 ^ E) (oddPrimorial_dvd_oddPrimorial (by omega)))
      · rw [Finset.mem_image] at hd3; rcases hd3 with ⟨b, hb, rfl⟩
        rcases hS3_prop b hb with ⟨hpos, hdvd⟩
        refine ⟨Nat.mul_pos (Nat.mul_pos (by positivity) hU_pos) hpos, ?_⟩
        have hmul := Nat.mul_dvd_mul_left (2 ^ k * U_top) hdvd
        have hrew : 2 ^ k * U_top * (2 ^ E_next * oddPrimorial (E_next / 4)) = 2 ^ E * oddPrimorial (E / 4) := by
          rw [hodd_split]
          have h2E : 2 ^ E = 2 ^ k * 2 ^ E_next := by rw [← pow_add]; congr 1; omega
          rw [h2E]; ring
        rwa [hrew] at hmul
    · rw [Finset.sum_union hdisj12_3, Finset.sum_union hdisj12]
      have hS2_sum' : S2.sum id = 2 ^ k * r1 := by
        rw [Finset.sum_image (fun a _ c _ h => Nat.eq_of_mul_eq_mul_left (by positivity) h)]
        simp only [id_eq]; rw [← Finset.mul_sum]; exact congrArg (2 ^ k * ·) hS2_sum
      have hS3_sum' : S3.sum id = 2 ^ k * U_top * q1 := by
        rw [Finset.sum_image (fun a _ c _ h => Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by positivity) hU_pos) h)]
        simp only [id_eq]; rw [← Finset.mul_sum]; exact congrArg (2 ^ k * U_top * ·) hS3_sum
      rw [hS2_sum', hS3_sum']
      have hy_div : U_top * q1 + r1 = y := Nat.div_add_mod y U_top
      have hmul_y : 2 ^ k * r1 + 2 ^ k * U_top * q1 = 2 ^ k * y := by
        calc 2 ^ k * r1 + 2 ^ k * U_top * q1 = 2 ^ k * (U_top * q1 + r1) := by ring
          _ = 2 ^ k * y := by rw [hy_div]
      linarith [hy_eq, hmul_y]
    · have hcard_eq : ((S1 ∪ S2) ∪ S3).card = S1.card + S2_raw.card + S3_raw.card := by
        rw [Finset.card_union_of_disjoint hdisj12_3, Finset.card_union_of_disjoint hdisj12,
            Finset.card_image_of_injective S2_raw (fun a c h => Nat.eq_of_mul_eq_mul_left (by positivity) h),
            Finset.card_image_of_injective S3_raw (fun a c h => Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by positivity) hU_pos) h)]
      rw [hcard_eq, Nat.cast_add, Nat.cast_add]
      set L := Real.log ((E : ℝ) + 2)
      set Ln := Real.log ((E_next : ℝ) + 2)
      set LL := Real.log (Real.log ((E : ℝ) + 16))
      set LLn := Real.log (Real.log ((E_next : ℝ) + 16))
      have hL_ge1 : (1 : ℝ) ≤ L := by
        have h4 : (4 : ℝ) ≤ (E : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ E + 2)
        have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
        linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
      have hLL_gt1 : 1 < LL := one_lt_log_log_add16_all E
      have hLn_nn : 0 ≤ Ln := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E_next + 2))
      have hLn_le_L : Ln ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E_next + 2 ≤ E + 2))
      have hLn3 : Ln ^ 3 ≤ L ^ 3 - (1 / 2 : ℝ) * L ^ 2 := by
        have hLn2 : Ln ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hLn_nn hLn_le_L 2
        have h1 : Ln ^ 3 = Ln * Ln ^ 2 := by ring
        have h2 : Ln * Ln ^ 2 ≤ (L - 1 / 2) * L ^ 2 :=
          mul_le_mul hlog_drop hLn2 (by positivity) (by linarith)
        linarith
      have hLLn_sq : LLn ^ 2 ≤ LL ^ 2 :=
        pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all E_next])
          (Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < E_next + 16)))
            (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E_next + 16 ≤ E + 16)))) 2
      have hS1_le : (S1.card : ℝ) ≤ (2 * C_cov + 2) * L ^ 2 * LL ^ 2 := by
        have hc1 : (S1.card : ℝ) ≤
            2 * (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) : ℝ) := by
          exact_mod_cast hS1_card
        have hceil : (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) : ℝ) ≤
            C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 + 1 :=
          (Nat.ceil_lt_add_one (by positivity)).le
        have hlogk2 : (Real.log ((k : ℝ) + 2)) ^ 2 ≤ L ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k + 2)))
            (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 2 ≤ E + 2))) 2
        have hllk2 : (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 ≤ LL ^ 2 :=
          pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all k])
            (Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < k + 16)))
              (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 16 ≤ E + 16)))) 2
        have hprod_le : (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 ≤ L ^ 2 * LL ^ 2 :=
          mul_le_mul hlogk2 hllk2 (by positivity) (by positivity)
        have h1_le : (1 : ℝ) ≤ L ^ 2 * LL ^ 2 := by
          have h1 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL_ge1
          have h2 : (1 : ℝ) ≤ LL ^ 2 := one_le_pow₀ hLL_gt1.le
          nlinarith
        have hC_prod : C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 ≤
            C_cov * (L ^ 2 * LL ^ 2) := by
          calc C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2
              = C_cov * ((Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2) := by ring
            _ ≤ C_cov * (L ^ 2 * LL ^ 2) := mul_le_mul_of_nonneg_left hprod_le hC_cov.le
        nlinarith
      have hS2_le : (S2_raw.card : ℝ) ≤ C4 * L ^ 2 * LL ^ 2 := by
        have hlog2 : (Real.log ((E_next / 2 : ℕ) + 2 : ℝ)) ^ 2 ≤ L ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E_next / 2 + 2)))
            (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E_next / 2 + 2 ≤ E + 2))) 2
        have hll2 : (Real.log (Real.log (((E_next / 2 : ℕ) : ℝ) + 16))) ^ 2 ≤ LL ^ 2 :=
          pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all (E_next / 2)])
            (Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < E_next / 2 + 16)))
              (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E_next / 2 + 16 ≤ E + 16)))) 2
        have hmul := mul_le_mul hlog2 hll2 (by positivity) (by positivity)
        calc (S2_raw.card : ℝ)
            ≤ C4 * (Real.log ((E_next / 2 : ℕ) + 2 : ℝ)) ^ 2 *
                (Real.log (Real.log (((E_next / 2 : ℕ) : ℝ) + 16))) ^ 2 := hS2_card
          _ = C4 * ((Real.log ((E_next / 2 : ℕ) + 2 : ℝ)) ^ 2 *
                (Real.log (Real.log (((E_next / 2 : ℕ) : ℝ) + 16))) ^ 2) := by ring
          _ ≤ C4 * (L ^ 2 * LL ^ 2) := mul_le_mul_of_nonneg_left hmul hC4.le
          _ = C4 * L ^ 2 * LL ^ 2 := by ring
      have hS3_le : (S3_raw.card : ℝ) ≤ C5 * (L ^ 3 - (1 / 2 : ℝ) * L ^ 2) * LL ^ 2 := by
        have h1 : Ln ^ 3 * LLn ^ 2 ≤ (L ^ 3 - (1 / 2 : ℝ) * L ^ 2) * LL ^ 2 :=
          mul_le_mul hLn3 hLLn_sq (by positivity) (by nlinarith)
        calc (S3_raw.card : ℝ)
            ≤ C5 * Ln ^ 3 * LLn ^ 2 := hS3_card
          _ = C5 * (Ln ^ 3 * LLn ^ 2) := by ring
          _ ≤ C5 * ((L ^ 3 - (1 / 2 : ℝ) * L ^ 2) * LL ^ 2) := mul_le_mul_of_nonneg_left h1 hC5_pos.le
          _ = C5 * (L ^ 3 - (1 / 2 : ℝ) * L ^ 2) * LL ^ 2 := by ring
      have hC5_ge : 2 * (2 * C_cov + 2 + C4) ≤ C5 := le_max_right _ _
      have hL2LL2_nn : 0 ≤ L ^ 2 * LL ^ 2 := by positivity
      have hcoef_le : (2 * C_cov + 2 + C4) * (L ^ 2 * LL ^ 2) ≤ (1 / 2 : ℝ) * C5 * (L ^ 2 * LL ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hL2LL2_nn
      linarith

/-! ## Part 4: Main Theorems `erdos18_alpha3_loglog2` and `erdos18_alpha4` -/

/-- **Main Theorem (Erdős Problem #18 — `h(n!) = O((log n)^3 (log log n)^2)`)**:
    There exists an absolute constant `C : ℝ` such that for every `n ≥ 2` and every integer
    `1 ≤ t ≤ n!`, `t` can be written as a sum of at most
    `C * (Real.log n)^3 * (Real.log (Real.log (n + 16)))^2` distinct positive divisors of `n!`. -/
theorem erdos18_alpha3_loglog2 :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → ∀ t : ℕ, 1 ≤ t → t ≤ n.factorial →
      ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n.factorial ∧ 0 < d) ∧
        S.sum id = t ∧
        (S.card : ℝ) ≤ C * (Real.log n) ^ 3 * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 := by
  rcases lemma4_carry_recursion_alpha3 with ⟨C4, hC4, hlem4⟩
  rcases stage2_tail_recursion_alpha3 with ⟨C5, hC5, hstage2⟩
  set C_small : ℝ := 10 * ((Nat.factorial 64 : ℕ) : ℝ)
  set C_big : ℝ := 25 * C4 * 9 + C5 * 27 + 10
  set C : ℝ := max C_small C_big
  refine ⟨C, ?_⟩
  intro n hn t ht1 htfac
  have hll_n_gt1 : 1 < Real.log (Real.log ((n : ℝ) + 16)) := one_lt_log_log_add16_all n
  have hll_n_sq : (1 : ℝ) ≤ (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 := by nlinarith
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
      have hC_ge : 10 ≤ C := le_trans (by linarith) (le_max_right _ _)
      have hprod_ge : (0.3 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 := by
        nlinarith
      nlinarith
  have ht_lt : t < n.factorial := lt_of_le_of_ne htfac hteq
  -- Case 2: n < 64
  by_cases hn_small : n < 64
  · rcases practical_factorial n (by omega) t ht_lt with ⟨S, hprop, hsum⟩
    refine ⟨S, fun d hd => ⟨(hprop d hd).2, (hprop d hd).1⟩, hsum, ?_⟩
    have hsub' : S ⊆ Finset.Icc 1 (Nat.factorial 64) := by
      intro d hd; rw [Finset.mem_Icc]
      have hd_le : d ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) (hprop d hd).2
      have hfac_le : n.factorial ≤ Nat.factorial 64 := Nat.factorial_le (by omega)
      exact ⟨(hprop d hd).1, le_trans hd_le hfac_le⟩
    have hcard_le' : (S.card : ℝ) ≤ (Nat.factorial 64 : ℝ) := by
      exact_mod_cast le_trans (Finset.card_le_card hsub') (by simp)
    have hlog_ge : (0.69 : ℝ) ≤ Real.log (n : ℝ) := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [Real.log_le_log (by norm_num) h2, Real.log_two_gt_d9]
    have hpow3_ge : (0.3 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
      have : (0.69 : ℝ) ^ 3 ≤ (Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) hlog_ge 3
      linarith [show (0.3 : ℝ) ≤ (0.69 : ℝ) ^ 3 by norm_num]
    have hC_ge : 10 * (Nat.factorial 64 : ℝ) ≤ C := le_max_left _ _
    have hprod_ge : (0.3 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 := by
      nlinarith
    nlinarith
  -- Case 3: n ≥ 64
  push Not at hn_small
  set E := n.factorial.factorization 2
  have hE_bounds := factorial_two_val_bounds n
  have hE_lo : n / 2 ≤ E := hE_bounds.1
  have hE_hi : E ≤ n := hE_bounds.2
  set M := 2 ^ E * oddPrimorial (E / 4)
  have hM_dvd : M ∣ n.factorial := M_tail_dvd_factorial n
  have hM_pos : 0 < M := Nat.mul_pos (by positivity) (oddPrimorial_pos _)
  set U := n.factorial / M
  have hMU : M * U = n.factorial := Nat.mul_div_cancel' hM_dvd
  have hU_pos : 1 ≤ U := by
    by_contra h0; push Not at h0
    have hU0 : U = 0 := Nat.lt_one_iff.mp h0
    rw [hU0, mul_zero] at hMU
    exact Nat.factorial_ne_zero n hMU.symm
  set K := 2 ^ (E / 2)
  have hn_le_2E4 : n ≤ 2 ^ (E / 4) :=
    le_trans (nat_le_two_pow_div_eight hn_small) (Nat.pow_le_pow_right (by omega) (by omega))
  have hn_le_K : n ≤ K := le_trans hn_le_2E4 (Nat.pow_le_pow_right (by omega) (by omega))
  have hU_primes : ∀ p : ℕ, p.Prime → p ∣ U → p ≤ n := by
    intro p hp hpd
    have hpd_fac : p ∣ n.factorial := dvd_trans hpd (by rw [← hMU]; exact dvd_mul_left U M)
    exact (Nat.Prime.dvd_factorial hp).mp hpd_fac
  rcases greedy_factorize n K (by omega) hn_le_K U hU_pos hU_primes with ⟨Ds, hDs_prod, hDs_mem, hDs_len⟩
  have hlogn_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 4 ≤ n)
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
  have hDs_len_le : (Ds.length : ℝ) ≤ 25 * Real.log (n : ℝ) := by
    have hKn_ge : 2 ^ (n / 8) ≤ K / n := by
      have h1 : 2 ^ (n / 8) * n ≤ 2 ^ (E / 4) * 2 ^ (E / 4) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega)) hn_le_2E4
      have h2 : 2 ^ (E / 4) * 2 ^ (E / 4) ≤ K := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (le_trans h1 h2)
    have hpow_le_fac : (2 ^ (n / 8)) ^ (Ds.length - 1) ≤ n ^ n := by
      have h1 : (2 ^ (n / 8)) ^ (Ds.length - 1) ≤ (K / n) ^ (Ds.length - 1) := Nat.pow_le_pow_left hKn_ge _
      have h2 : U ≤ n.factorial := by rw [← hMU]; exact Nat.le_mul_of_pos_left U hM_pos
      have h3 : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
      exact le_trans h1 (le_trans hDs_len (le_trans h2 h3))
    have hreal : (((2 : ℝ) ^ (n / 8)) ^ (Ds.length - 1)) ≤ (n : ℝ) ^ n := by exact_mod_cast hpow_le_fac
    have hlog_ineq : Real.log (((2 : ℝ) ^ (n / 8)) ^ (Ds.length - 1)) ≤ Real.log ((n : ℝ) ^ n) :=
      Real.log_le_log (by positivity) hreal
    rw [Real.log_pow, Real.log_pow, Real.log_pow] at hlog_ineq
    have hn8_ge : (n : ℝ) / 16 ≤ ((n / 8 : ℕ) : ℝ) := by
      have : n ≤ 8 * (n / 8) + 7 := by omega
      have hcast : (n : ℝ) ≤ 8 * ((n / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast this
      have hn64 : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_small
      linarith
    have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hstep : ((Ds.length - 1 : ℕ) : ℝ) * ((n : ℝ) / 16 * 0.69) ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have h1 : (n : ℝ) / 16 * 0.69 ≤ ((n / 8 : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul hn8_ge hlog2 (by norm_num) (by positivity)
      have h2 : ((Ds.length - 1 : ℕ) : ℝ) * ((n : ℝ) / 16 * 0.69) ≤
          ((Ds.length - 1 : ℕ) : ℝ) * (((n / 8 : ℕ) : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlm1 : ((Ds.length - 1 : ℕ) : ℝ) ≤ 24 * Real.log (n : ℝ) := by nlinarith
    have hlen_cast : (Ds.length : ℝ) ≤ ((Ds.length - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : Ds.length ≤ (Ds.length - 1) + 1)
    linarith
  have hlogE_le : Real.log ((E : ℝ) + 2) ≤ 3 * Real.log (n : ℝ) := by
    have hE2_le : (E : ℝ) + 2 ≤ (n : ℝ) ^ 3 := by
      have h1 : E + 2 ≤ n ^ 3 := by
        have h2 : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
        have h3 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 * n ≤ n ^ 2 := by nlinarith
        omega
      exact_mod_cast h1
    have h1 := Real.log_le_log (by positivity) hE2_le
    rw [Real.log_pow] at h1; push_cast at h1; exact h1
  have hlogE_nn : 0 ≤ Real.log ((E : ℝ) + 2) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E + 2))
  have hllE_sq : (Real.log (Real.log ((E : ℝ) + 16))) ^ 2 ≤ (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 :=
    pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all E])
      (Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < E + 16)))
        (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E + 16 ≤ n + 16)))) 2
  have hllE2_sq : (Real.log (Real.log (((E / 2 : ℕ) : ℝ) + 16))) ^ 2 ≤ (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 :=
    pow_le_pow_left₀ (by linarith [one_lt_log_log_add16_all (E / 2)])
      (Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < E / 2 + 16)))
        (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E / 2 + 16 ≤ n + 16)))) 2
  set LLn := Real.log (Real.log ((n : ℝ) + 16))
  have hdigit : ∀ r < K, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = r ∧
      (S.card : ℝ) ≤ C4 * (3 * Real.log (n : ℝ)) ^ 2 * LLn ^ 2 := by
    intro r hr
    rcases hlem4 (E / 2) E r (by omega) hr with ⟨S, hprop, hsum, hcard⟩
    refine ⟨S, hprop, hsum, le_trans hcard ?_⟩
    have hlog2 : (Real.log (((E / 2 : ℕ) : ℝ) + 2)) ^ 2 ≤ (3 * Real.log (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E / 2 + 2)))
        (le_trans (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E / 2 + 2 ≤ E + 2))) hlogE_le) 2
    have hmul := mul_le_mul hlog2 hllE2_sq (by positivity) (by positivity)
    calc C4 * (Real.log (((E / 2 : ℕ) : ℝ) + 2)) ^ 2 * (Real.log (Real.log (((E / 2 : ℕ) : ℝ) + 16))) ^ 2
        = C4 * ((Real.log (((E / 2 : ℕ) : ℝ) + 2)) ^ 2 * (Real.log (Real.log (((E / 2 : ℕ) : ℝ) + 16))) ^ 2) := by ring
      _ ≤ C4 * ((3 * Real.log (n : ℝ)) ^ 2 * LLn ^ 2) := mul_le_mul_of_nonneg_left hmul hC4.le
      _ = C4 * (3 * Real.log (n : ℝ)) ^ 2 * LLn ^ 2 := by ring
  have htail : ∀ x < M, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = x ∧
      (S.card : ℝ) ≤ C5 * (3 * Real.log (n : ℝ)) ^ 3 * LLn ^ 2 := by
    intro x hx
    rcases hstage2 E x (by omega) hx with ⟨S, hprop, hsum, hcard⟩
    refine ⟨S, hprop, hsum, le_trans hcard ?_⟩
    have hlog3 : (Real.log ((E : ℝ) + 2)) ^ 3 ≤ (3 * Real.log (n : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hlogE_nn hlogE_le 3
    have hmul := mul_le_mul hlog3 hllE_sq (by positivity) (by positivity)
    calc C5 * (Real.log ((E : ℝ) + 2)) ^ 3 * (Real.log (Real.log ((E : ℝ) + 16))) ^ 2
        = C5 * ((Real.log ((E : ℝ) + 2)) ^ 3 * (Real.log (Real.log ((E : ℝ) + 16))) ^ 2) := by ring
      _ ≤ C5 * ((3 * Real.log (n : ℝ)) ^ 3 * LLn ^ 2) := mul_le_mul_of_nonneg_left hmul hC5.le
      _ = C5 * (3 * Real.log (n : ℝ)) ^ 3 * LLn ^ 2 := by ring
  have ht_lt_prod : t < M * Ds.prod := by rw [hDs_prod, hMU]; exact ht_lt
  rcases mixed_radix_stage1 M K
      (C4 * (3 * Real.log (n : ℝ)) ^ 2 * LLn ^ 2)
      (C5 * (3 * Real.log (n : ℝ)) ^ 3 * LLn ^ 2)
      hdigit htail Ds hDs_mem t ht_lt_prod with ⟨S, hprop, hsum, hcard⟩
  refine ⟨S, ?_, hsum, ?_⟩
  · intro d hd
    rcases hprop d hd with ⟨hpos, hdvd⟩
    rw [hDs_prod, hMU] at hdvd
    exact ⟨hdvd, hpos⟩
  · have hstep1 : (Ds.length : ℝ) * (C4 * (3 * Real.log (n : ℝ)) ^ 2 * LLn ^ 2) ≤
        25 * Real.log (n : ℝ) * (C4 * (3 * Real.log (n : ℝ)) ^ 2 * LLn ^ 2) :=
      mul_le_mul_of_nonneg_right hDs_len_le (by positivity)
    have hpow_eq : 25 * Real.log (n : ℝ) * (C4 * (3 * Real.log (n : ℝ)) ^ 2 * LLn ^ 2) +
        C5 * (3 * Real.log (n : ℝ)) ^ 3 * LLn ^ 2 =
        (25 * C4 * 9 + C5 * 27) * (Real.log (n : ℝ)) ^ 3 * LLn ^ 2 := by ring
    have hC_ge : 25 * C4 * 9 + C5 * 27 ≤ C := le_trans (by linarith) (le_max_right _ _)
    have hstep2 : (25 * C4 * 9 + C5 * 27) * ((Real.log (n : ℝ)) ^ 3 * LLn ^ 2) ≤
        C * ((Real.log (n : ℝ)) ^ 3 * LLn ^ 2) :=
      mul_le_mul_of_nonneg_right hC_ge (by positivity)
    linarith

/-- **Corollary (Erdős Problem #18 — `h(n!) = O((log n)^4)`)**:
    Immediate corollary of `erdos18_alpha3_loglog2` since `(log (log (n + 16)))^2 ≤ 20 * log n` for `n ≥ 2`. -/
theorem erdos18_alpha4 :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → ∀ t : ℕ, 1 ≤ t → t ≤ n.factorial →
      ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n.factorial ∧ 0 < d) ∧
        S.sum id = t ∧ (S.card : ℝ) ≤ C * (Real.log n) ^ 4 := by
  rcases erdos18_alpha3_loglog2 with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C := by
    rcases hC 2 (le_refl 2) 1 (le_refl 1) (by decide) with ⟨S, _, _, hcard⟩
    have hpos : 0 < (Real.log (2 : ℝ)) ^ 3 * (Real.log (Real.log ((2 : ℝ) + 16))) ^ 2 := by
      have h1 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have h2 : 1 < Real.log (Real.log ((2 : ℝ) + 16)) := one_lt_log_log_add16_all 2
      positivity
    by_contra hneg; push Not at hneg
    have : C * (Real.log (2 : ℝ)) ^ 3 * (Real.log (Real.log ((2 : ℝ) + 16))) ^ 2 < 0 := by nlinarith
    have hnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    push_cast at hcard
    linarith
  refine ⟨20 * C, ?_⟩
  intro n hn t ht1 htfac
  rcases hC n hn t ht1 htfac with ⟨S, hprop, hsum, hcard⟩
  refine ⟨S, hprop, hsum, le_trans hcard ?_⟩
  -- Prove (log (log (n + 16)))^2 ≤ 20 * log n for n ≥ 2
  set x : ℝ := Real.log ((n : ℝ) + 16)
  have hx_pos : 0 < x := Real.log_pos (by exact_mod_cast (by omega : 1 < n + 16))
  have hlogx_le : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx_pos)
    rw [Real.log_sqrt hx_pos.le] at h1
    linarith
  have hll_sq_le : (Real.log x) ^ 2 ≤ 4 * x := by
    have hnn : 0 ≤ Real.log x := by linarith [one_lt_log_log_add16_all n]
    have h1 : (Real.log x) ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ hnn hlogx_le 2
    have h2 : (2 * Real.sqrt x) ^ 2 = 4 * x := by
      rw [mul_pow, Real.sq_sqrt hx_pos.le]; norm_num
    linarith
  have hx_le : x ≤ 5 * Real.log (n : ℝ) := by
    have hpow : (n : ℝ) + 16 ≤ (n : ℝ) ^ 5 := by
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h1 : (n : ℝ) ^ 4 ≥ 16 := by
        have : (2 : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hn2 4
        linarith [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num]
      nlinarith
    have h1 := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h1
  have hll_20 : (Real.log x) ^ 2 ≤ 20 * Real.log (n : ℝ) := by linarith
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  calc C * (Real.log (n : ℝ)) ^ 3 * (Real.log x) ^ 2
      ≤ C * (Real.log (n : ℝ)) ^ 3 * (20 * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hll_20 (by positivity)
    _ = 20 * C * (Real.log (n : ℝ)) ^ 4 := by ring

end Erdos18

#print axioms Erdos18.lemma4_carry_recursion_alpha3
#print axioms Erdos18.stage2_tail_recursion_alpha3
#print axioms Erdos18.erdos18_alpha3_loglog2
#print axioms Erdos18.erdos18_alpha4
