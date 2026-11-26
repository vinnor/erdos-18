import Erdos18.Covering

/-!
# Erdos18/MainTheorem.lean (Layer 4 — Lemma 4, Stages 1–2, and `erdos18_alpha5`)

Proves the unconditional upper bound `h(n!) = O((log n)^5)`:
```lean
theorem erdos18_alpha5 :
  ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → ∀ t : ℕ, 1 ≤ t → t ≤ n.factorial →
    ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n.factorial ∧ 0 < d) ∧
      S.sum id = t ∧ (S.card : ℝ) ≤ C * (Real.log n) ^ 5
```
-/

namespace Erdos18

open Finset Nat Real

/-! ## Part 1: Elementary Binary Representation & Practical-Number Base Cases -/

/-- Binary expansion of `r < 2^B` as a `Finset ℕ` of at most `B` distinct powers of `2`. -/
lemma binary_rep {B r : ℕ} (hr : r < 2 ^ B) :
    ∃ S : Finset ℕ, S.card ≤ B ∧ (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ B ∧ d < 2 ^ B) ∧ S.sum id = r := by
  induction B generalizing r with
  | zero =>
    have hr0 : r = 0 := by omega
    subst hr0
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ B ih =>
    have hq_lt : r / 2 < 2 ^ B := by
      have : 2 ^ (B + 1) = 2 * 2 ^ B := by rw [pow_succ, mul_comm]
      omega
    rcases ih hq_lt with ⟨S', hcard', hprop', hsum'⟩
    let S2 := S'.image (2 * ·)
    have hcard2 : S2.card = S'.card :=
      Finset.card_image_of_injective S' (fun a b h => by omega)
    have hsum2 : S2.sum id = 2 * (r / 2) := by
      rw [Finset.sum_image (fun a _ b _ h => by omega)]
      simp only [id_eq]
      rw [← Finset.mul_sum]
      exact congrArg (2 * ·) hsum'
    have h1_notMem : 1 ∉ S2 := by
      intro hmem
      rw [Finset.mem_image] at hmem
      rcases hmem with ⟨a, ha, ha1⟩
      omega
    have hprop2 : ∀ d ∈ S2, 0 < d ∧ d ∣ 2 ^ (B + 1) ∧ d < 2 ^ (B + 1) := by
      intro d hd
      rw [Finset.mem_image] at hd
      rcases hd with ⟨a, ha, rfl⟩
      rcases hprop' a ha with ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_, ?_⟩
      · rw [pow_succ, mul_comm (2 ^ B) 2]; exact Nat.mul_dvd_mul_left 2 h2
      · rw [pow_succ, mul_comm]; omega
    by_cases hodd : r % 2 = 0
    · refine ⟨S2, by omega, hprop2, by omega⟩
    · refine ⟨insert 1 S2, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem h1_notMem]; omega
      · intro d hd
        rw [Finset.mem_insert] at hd
        rcases hd with rfl | hd2
        · refine ⟨by omega, one_dvd _, ?_⟩
          have : 1 ≤ 2 ^ B := Nat.one_le_two_pow
          rw [pow_succ]; omega
        · exact hprop2 d hd2
      · rw [Finset.sum_insert h1_notMem, id_eq, hsum2]; omega

/-- Stewart-Sierpiński practical-number step: if `M` can represent every `x < M`, and `p ≤ M`,
    then `M * p` can represent every `x < M * p`. -/
lemma practical_mul_step {M p : ℕ} (hp : 1 ≤ p) (hpM : p ≤ M)
    (hM : ∀ x < M, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = x) :
    ∀ x < M * p, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M * p) ∧ S.sum id = x := by
  intro x hx
  have hr_lt : x % p < M := lt_of_lt_of_le (Nat.mod_lt x (by omega)) hpM
  have hq_lt : x / p < M := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  rcases hM (x % p) hr_lt with ⟨Sr, hSr_prop, hSr_sum⟩
  rcases hM (x / p) hq_lt with ⟨Sq, hSq_prop, hSq_sum⟩
  let Sq' := Sq.image (p * ·)
  have hdisj : Disjoint Sr Sq' := by
    rw [Finset.disjoint_left]
    intro d hdr hdq
    rw [Finset.mem_image] at hdq
    rcases hdq with ⟨a, ha, rfl⟩
    have ha_pos : 0 < a := (hSq_prop a ha).1
    have hd_le : p * a ≤ x % p := by
      rw [← hSr_sum]
      exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hdr
    have hmod_lt : x % p < p := Nat.mod_lt x (by omega)
    have hp_le : p ≤ p * a := Nat.le_mul_of_pos_right p ha_pos
    omega
  refine ⟨Sr ∪ Sq', ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hdr | hdq
    · rcases hSr_prop d hdr with ⟨h1, h2⟩
      exact ⟨h1, dvd_mul_of_dvd_left h2 p⟩
    · rw [Finset.mem_image] at hdq
      rcases hdq with ⟨a, ha, rfl⟩
      rcases hSq_prop a ha with ⟨h1, h2⟩
      exact ⟨Nat.mul_pos (by omega) h1, by rw [mul_comm p a]; exact Nat.mul_dvd_mul_right h2 p⟩
  · rw [Finset.sum_union hdisj, hSr_sum,
        Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]
    simp only [id_eq]
    rw [← Finset.mul_sum]
    have hsum_q : Sq.sum (fun a => a) = x / p := hSq_sum
    rw [hsum_q]
    have hdiv := Nat.div_add_mod x p
    omega

/-- Every `M(E) = 2^E * oddPrimorial (E / 4)` is practical for `E ≥ 1`. -/
lemma practical_M_tail (E : ℕ) (hE : 1 ≤ E) :
    ∀ x < 2 ^ E * oddPrimorial (E / 4),
      ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ E * oddPrimorial (E / 4)) ∧ S.sum id = x := by
  have hbase : ∀ x < 2 ^ E, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ E) ∧ S.sum id = x := fun x hx => by
    rcases binary_rep hx with ⟨S, _, hprop, hsum⟩
    exact ⟨S, fun d hd => ⟨(hprop d hd).1, (hprop d hd).2.1⟩, hsum⟩
  have hind : ∀ (P : Finset ℕ), (∀ p ∈ P, 1 ≤ p ∧ p ≤ 2 ^ E) →
      ∀ x < 2 ^ E * ∏ p ∈ P, p,
        ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ E * ∏ p ∈ P, p) ∧ S.sum id = x := by
    intro P
    induction P using Finset.induction_on with
    | empty => intro _; simpa using hbase
    | @insert p s hp ih =>
      intro hP
      have hp_b := hP p (Finset.mem_insert_self p s)
      have hs_b : ∀ q ∈ s, 1 ≤ q ∧ q ≤ 2 ^ E := fun q hq => hP q (Finset.mem_insert_of_mem hq)
      have hprod_pos : 1 ≤ ∏ q ∈ s, q := Finset.one_le_prod fun q hq => (hs_b q hq).1
      have hp_le_M : p ≤ 2 ^ E * ∏ q ∈ s, q := le_trans hp_b.2 (Nat.le_mul_of_pos_right _ hprod_pos)
      have hrew : 2 ^ E * ∏ q ∈ insert p s, q = (2 ^ E * ∏ q ∈ s, q) * p := by
        rw [Finset.prod_insert hp]; ring
      rw [hrew]
      exact practical_mul_step hp_b.1 hp_le_M (ih hs_b)
  unfold oddPrimorial
  apply hind
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  have hE_lt : E < 2 ^ E := Nat.lt_two_pow_self
  omega

/-- Every factorial `n!` is practical for `n ≥ 1`. -/
lemma practical_factorial (n : ℕ) (hn : 1 ≤ n) :
    ∀ x < n.factorial, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ n.factorial) ∧ S.sum id = x := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      intro x hx
      have hx0 : x = 0 := by simp at hx; omega
      subst hx0; exact ⟨∅, by simp, by simp⟩
    | succ k =>
      cases k with
      | zero =>
        intro x hx
        have hx_lt : x < 2 := by simpa using hx
        interval_cases x
        · exact ⟨∅, by simp, by simp⟩
        · exact ⟨{1}, by simp, by simp⟩
      | succ k' =>
        cases k' with
        | zero =>
          intro x hx
          have hx_lt : x < 6 := by simpa [Nat.factorial] using hx
          interval_cases x
          · exact ⟨∅, by simp, by simp⟩
          · exact ⟨{1}, by simp, by simp⟩
          · exact ⟨{2}, by decide, by decide⟩
          · exact ⟨{3}, by decide, by decide⟩
          · exact ⟨{1, 3}, by decide, by decide⟩
          · exact ⟨{2, 3}, by decide, by decide⟩
        | succ k'' =>
          have hle' : k'' + 4 ≤ (k'' + 3).factorial := by
            have hfac2 : 2 ≤ (k'' + 2).factorial :=
              le_trans (by norm_num : 2 ≤ Nat.factorial 2) (Nat.factorial_le (by omega))
            have hmul : (k'' + 3) * 2 ≤ (k'' + 3) * (k'' + 2).factorial := Nat.mul_le_mul_left _ hfac2
            have hrew : (k'' + 3) * (k'' + 2).factorial = (k'' + 3).factorial := rfl
            omega
          intro x hx
          have hrew_fac : (k'' + 4).factorial = (k'' + 3).factorial * (k'' + 4) := by
            rw [Nat.factorial_succ, mul_comm]
          rw [hrew_fac] at hx ⊢
          exact practical_mul_step (by omega) hle' (ih (by omega)) x hx

/-! ## Part 2: Elementary Asymptotic Threshold Helpers (Zero Limits, Pure Algebra) -/

/-- Helper: `m^7 ≤ 2^m` for all `m ≥ 128` (elementary induction). -/
lemma pow_seven_le_two_pow {m : ℕ} (hm : 128 ≤ m) : m ^ 7 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hstep : (m + 1) ^ 7 ≤ 2 * m ^ 7 := by
      have h1 : (m + 1) ^ 7 = m ^ 7 + 7 * m ^ 6 + 21 * m ^ 5 + 35 * m ^ 4 + 35 * m ^ 3 + 21 * m ^ 2 + 7 * m + 1 := by ring
      rw [h1]
      have hm1 : 1 ≤ m := by omega
      have hm2 : m ≤ m ^ 2 := Nat.le_self_pow (by omega) m
      have hm3 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by omega)
      have hm4 : m ^ 3 ≤ m ^ 4 := Nat.pow_le_pow_right hm1 (by omega)
      have hm5 : m ^ 4 ≤ m ^ 5 := Nat.pow_le_pow_right hm1 (by omega)
      have hm6 : m ^ 5 ≤ m ^ 6 := Nat.pow_le_pow_right hm1 (by omega)
      have h7 : 127 * m ^ 6 ≤ m ^ 7 := by
        calc 127 * m ^ 6 ≤ m * m ^ 6 := Nat.mul_le_mul_right (m ^ 6) (by omega)
          _ = m ^ 7 := by ring
      omega
    calc (m + 1) ^ 7 ≤ 2 * m ^ 7 := hstep
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by rw [pow_succ, mul_comm]

/-- Helper: for `x ≥ 1`, `Real.log x ≤ 8 * √(√(√x))`. -/
lemma log_le_eight_eighth_root {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt x)) := by
  set u := Real.sqrt (Real.sqrt (Real.sqrt x))
  have hu_pos : 0 < u := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith)))
  have hu8 : u ^ 8 = x := by
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt x) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    calc u ^ 8 = ((u ^ 2) ^ 2) ^ 2 := by ring
      _ = x := by rw [h1, h2, h3]
  have hlog : Real.log x = 8 * Real.log u := by rw [← hu8, Real.log_pow]; ring
  have hle : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu_pos
  linarith

/-- Threshold 1: For any `C_cov > 0`, there exists `k0 ≥ 16` such that for all `k ≥ k0`,
    `2 * Nat.ceil (C_cov * (log (k + 2))^4) ≤ oddPrimeCounting (k / 2) - oddPrimeCounting ((k + 1) / 4)`. -/
lemma exists_bertrand_exceeds_R (C_cov : ℝ) (hC : 0 < C_cov) :
    ∃ k0 : ℕ, 16 ≤ k0 ∧ ∀ k : ℕ, k0 ≤ k →
      2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) ≤
        oddPrimeCounting (k / 2) - oddPrimeCounting ((k + 1) / 4) := by
  rcases bertrand_quantitative with ⟨cB, hcB, x0, hbert⟩
  set M : ℕ := Nat.ceil ((24 * C_cov + 32) * (8 : ℝ) ^ 5 / cB) + 10
  refine ⟨max (4 * x0 + 16) (M ^ 8), by omega, ?_⟩
  intro k hk
  have hx_ge : x0 ≤ k / 4 := by omega
  have hk_ge : M ^ 8 ≤ k := le_trans (le_max_right _ _) hk
  have hb := hbert (k / 4) hx_ge
  have hmono_hi : oddPrimeCounting (2 * (k / 4)) ≤ oddPrimeCounting (k / 2) := by
    unfold oddPrimeCounting
    apply Finset.card_le_card
    intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
  have hstep_lo : oddPrimeCounting ((k + 1) / 4) ≤ oddPrimeCounting (k / 4) + 1 := by
    unfold oddPrimeCounting
    have hsub : (Finset.range ((k + 1) / 4 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) ⊆
        insert ((k + 1) / 4) ((Finset.range (k / 4 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert] at hp ⊢
      by_cases h : p = (k + 1) / 4
      · exact Or.inl h
      · exact Or.inr ⟨by omega, hp.2⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hreal_bound : (2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) + 1 ≤
      cB * ((k / 4 : ℕ) : ℝ) / Real.log ((k / 4 : ℕ) : ℝ) := by
    set u := Real.sqrt (Real.sqrt (Real.sqrt ((k : ℝ) + 2)))
    have hk2_ge1 : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith [show (16 : ℝ) ≤ k by exact_mod_cast (by omega : 16 ≤ k)]
    have hu_pos : 0 < u := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith)))
    have hu8 : u ^ 8 = (k : ℝ) + 2 := by
      have h1 : u ^ 2 = Real.sqrt (Real.sqrt ((k : ℝ) + 2)) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have h2 : (Real.sqrt (Real.sqrt ((k : ℝ) + 2))) ^ 2 = Real.sqrt ((k : ℝ) + 2) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have h3 : (Real.sqrt ((k : ℝ) + 2)) ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by linarith)
      calc u ^ 8 = ((u ^ 2) ^ 2) ^ 2 := by ring
        _ = (k : ℝ) + 2 := by rw [h1, h2, h3]
    have hu_geM : (M : ℝ) ≤ u := by
      by_contra hlt; push Not at hlt
      have h3 : u ^ 8 < (M : ℝ) ^ 8 := pow_lt_pow_left₀ hlt hu_pos.le (by norm_num)
      have h4 : ((M : ℝ) ^ 8) ≤ (k : ℝ) := by exact_mod_cast hk_ge
      linarith
    have hlog_le : Real.log ((k : ℝ) + 2) ≤ 8 * u := log_le_eight_eighth_root hk2_ge1
    have hlog_pos : 0 < Real.log ((k : ℝ) + 2) := Real.log_pos (by linarith)
    have hlog_k4_pos : 0 < Real.log ((k / 4 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < k / 4))
    have hlog_k4_le : Real.log ((k / 4 : ℕ) : ℝ) ≤ Real.log ((k : ℝ) + 2) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < k / 4)) (by exact_mod_cast (by omega : k / 4 ≤ k + 2))
    have hceil_le : (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) ≤
        C_cov * (Real.log ((k : ℝ) + 2)) ^ 4 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hlog_ge1 : (1 : ℝ) ≤ Real.log ((k : ℝ) + 2) := by
      have h4 : (4 : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ k + 2)
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
    have hlhs_le : ((2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) + 1) * Real.log ((k / 4 : ℕ) : ℝ) ≤
        (2 * C_cov + 3) * (8 * u) ^ 5 := by
      have h1 : (2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) + 1 ≤
          (2 * C_cov + 3) * (Real.log ((k : ℝ) + 2)) ^ 4 := by
        have hpow1 : (1 : ℝ) ≤ (Real.log ((k : ℝ) + 2)) ^ 4 := one_le_pow₀ hlog_ge1
        linarith [show 3 * (1 : ℝ) ≤ 3 * (Real.log ((k : ℝ) + 2)) ^ 4 by linarith]
      have h2 : ((2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) + 1) * Real.log ((k / 4 : ℕ) : ℝ) ≤
          (2 * C_cov + 3) * (Real.log ((k : ℝ) + 2)) ^ 5 := by
        have hm := mul_le_mul h1 hlog_k4_le hlog_k4_pos.le (by positivity)
        linarith
      have h3 : (Real.log ((k : ℝ) + 2)) ^ 5 ≤ (8 * u) ^ 5 :=
        pow_le_pow_left₀ hlog_pos.le hlog_le 5
      exact le_trans h2 (mul_le_mul_of_nonneg_left h3 (by positivity))
    have hk4_ge : ((k : ℝ) + 2) / 8 ≤ ((k / 4 : ℕ) : ℝ) := by
      have : k ≤ 4 * (k / 4) + 3 := by omega
      have h16 : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 16 ≤ k)
      have hcast : (k : ℝ) ≤ 4 * ((k / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast this
      linarith
    have hM_ge : (24 * C_cov + 32) * (8 : ℝ) ^ 5 / cB ≤ (M : ℝ) := by
      have hle : (Nat.ceil ((24 * C_cov + 32) * (8 : ℝ) ^ 5 / cB) : ℝ) ≤ (M : ℝ) := by
        simp only [M]; push_cast; linarith
      exact le_trans (Nat.le_ceil _) hle
    have hu_ge1 : (1 : ℝ) ≤ u := le_trans (by exact_mod_cast (by omega : 1 ≤ M)) hu_geM
    have hu3_ge : (24 * C_cov + 32) * (8 : ℝ) ^ 5 / cB ≤ u ^ 3 := by
      have h1 : u ≤ u ^ 3 := by
        have : u ^ 1 ≤ u ^ 3 := pow_le_pow_right₀ hu_ge1 (by omega)
        simpa using this
      linarith
    have hmul_cB : (24 * C_cov + 32) * (8 : ℝ) ^ 5 ≤ cB * u ^ 3 := by
      have h := (div_le_iff₀ hcB).mp hu3_ge
      linarith
    have hu5_pos : 0 < u ^ 5 := by positivity
    have hfinal : (2 * C_cov + 3) * (8 * u) ^ 5 ≤ cB * ((k / 4 : ℕ) : ℝ) := by
      have h8u : (8 * u) ^ 5 = (8 : ℝ) ^ 5 * u ^ 5 := by ring
      rw [h8u]
      have h1 : (2 * C_cov + 3) * (8 : ℝ) ^ 5 * u ^ 5 * 8 ≤ cB * u ^ 8 := by
        have hcoef : (2 * C_cov + 3) * 8 ≤ 24 * C_cov + 32 := by linarith
        have hstep1 : (2 * C_cov + 3) * 8 * ((8 : ℝ) ^ 5 * u ^ 5) ≤ (24 * C_cov + 32) * ((8 : ℝ) ^ 5 * u ^ 5) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        have hstep2 : (24 * C_cov + 32) * (8 : ℝ) ^ 5 * u ^ 5 ≤ cB * u ^ 3 * u ^ 5 :=
          mul_le_mul_of_nonneg_right hmul_cB hu5_pos.le
        have hpow8 : cB * u ^ 3 * u ^ 5 = cB * u ^ 8 := by ring
        linarith
      have h2 : cB * (u ^ 8 / 8) ≤ cB * ((k / 4 : ℕ) : ℝ) := by
        rw [hu8]
        exact mul_le_mul_of_nonneg_left hk4_ge hcB.le
      linarith
    rw [le_div_iff₀ hlog_k4_pos]
    exact le_trans hlhs_le hfinal
  have hreal_nat : (2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) + 1 ≤
      (oddPrimeCounting (2 * (k / 4)) : ℝ) - (oddPrimeCounting (k / 4) : ℝ) :=
    le_trans hreal_bound hb
  have hnat : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) + 1 ≤
      oddPrimeCounting (2 * (k / 4)) - oddPrimeCounting (k / 4) := by
    have hle : oddPrimeCounting (k / 4) ≤ oddPrimeCounting (2 * (k / 4)) := by
      unfold oddPrimeCounting; apply Finset.card_le_card
      intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
    have hcast : ((2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) + 1 : ℕ) : ℝ) ≤
        ((oddPrimeCounting (2 * (k / 4)) - oddPrimeCounting (k / 4) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]; push_cast; linarith
    exact_mod_cast hcast
  omega

/-- Helper: `oddPrimorial a ∣ oddPrimorial b` whenever `a ≤ b`. -/
lemma oddPrimorial_dvd_oddPrimorial {a b : ℕ} (hab : a ≤ b) :
    oddPrimorial a ∣ oddPrimorial b := by
  unfold oddPrimorial
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- Helper: `oddPrimeCounting` is monotone. -/
lemma oddPrimeCounting_mono {a b : ℕ} (hab : a ≤ b) :
    oddPrimeCounting a ≤ oddPrimeCounting b := by
  unfold oddPrimeCounting
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-! ## Part 3: Lemma 4 — Carry Recursion for `r < 2^B` with `2 * B ≤ E` -/

/-- Threshold 2 for Lemma 4 carry recursion. -/
lemma exists_B0_carry (C_cov : ℝ) (hC : 0 < C_cov) (k0 : ℕ) (hk0 : 16 ≤ k0) :
    ∃ B0 : ℕ, 256 ≤ B0 ∧ ∀ B : ℕ, B0 < B →
      let b := Nat.sqrt B + 1
      let k := B - b
      k0 ≤ k ∧
      b < B ∧
      (b + 2) ^ 4 ≤ (B + 2) ^ 3 ∧
      2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (k / 2) ≤ 2 ^ (b - 1) := by
  set M0 : ℕ := max 256 (Nat.ceil (2 * C_cov + 2) + 2)
  set B0 : ℕ := max (2 * k0 + 256) (M0 ^ 2 * 4)
  refine ⟨B0, by omega, ?_⟩
  intro B hB
  dsimp only
  set b := Nat.sqrt B + 1
  set k := B - b
  have hB_ge : B0 < B := hB
  have hsqrt_ge : 2 * M0 ≤ Nat.sqrt B := by
    have h1 : (2 * M0) ^ 2 ≤ B := by
      have : (2 * M0) ^ 2 = M0 ^ 2 * 4 := by ring
      have : M0 ^ 2 * 4 ≤ B0 := le_max_right _ _
      omega
    exact Nat.le_sqrt.mpr (by simpa [sq] using h1)
  have hb_lt_B : 2 * b ≤ B := by
    have hsq : Nat.sqrt B * Nat.sqrt B ≤ B := Nat.sqrt_le B
    have h4 : 4 ≤ Nat.sqrt B := by omega
    have hb_eq : b = Nat.sqrt B + 1 := rfl
    nlinarith
  have hk_ge_k0 : k0 ≤ k := by
    have : 2 * k0 + 256 ≤ B0 := le_max_left _ _
    omega
  have hpow43 : (b + 2) ^ 4 ≤ (B + 2) ^ 3 := by
    have hsq : Nat.sqrt B * Nat.sqrt B ≤ B := Nat.sqrt_le B
    have hs16 : 16 ≤ Nat.sqrt B := by omega
    have hb2_le : b + 2 ≤ 2 * Nat.sqrt B := by omega
    have h1 : (b + 2) ^ 4 ≤ (2 * Nat.sqrt B) ^ 4 := Nat.pow_le_pow_left hb2_le 4
    have h2 : (2 * Nat.sqrt B) ^ 4 = 16 * (Nat.sqrt B) ^ 4 := by ring
    have h3 : 16 * (Nat.sqrt B) ^ 4 ≤ (Nat.sqrt B) ^ 6 := by
      have : 16 ≤ (Nat.sqrt B) ^ 2 := by nlinarith
      calc 16 * (Nat.sqrt B) ^ 4 ≤ (Nat.sqrt B) ^ 2 * (Nat.sqrt B) ^ 4 := Nat.mul_le_mul_right _ this
        _ = (Nat.sqrt B) ^ 6 := by ring
    have h4 : (Nat.sqrt B) ^ 6 ≤ B ^ 3 := by
      have : (Nat.sqrt B) ^ 6 = (Nat.sqrt B * Nat.sqrt B) ^ 3 := by ring
      rw [this]
      exact Nat.pow_le_pow_left hsq 3
    have h5 : B ^ 3 ≤ (B + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hcarry : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (k / 2) ≤ 2 ^ (b - 1) := by
    set m := Nat.sqrt B
    have hbm : b - 1 = m := by omega
    rw [hbm]
    have hlog_le : Real.log ((k : ℝ) + 2) ≤ (k : ℝ) + 2 := by
      have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      linarith [Real.log_le_sub_one_of_pos hpos]
    have hlog_nonneg : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k + 2))
    have hlog_ge1 : (1 : ℝ) ≤ Real.log ((k : ℝ) + 2) := by
      have h4 : (4 : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ k + 2)
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
    have hceil_le : (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) ≤
        C_cov * (Real.log ((k : ℝ) + 2)) ^ 4 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h2R_le : (2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) ≤
        (2 * C_cov + 2) * ((B : ℝ) + 2) ^ 4 := by
      have hpow1 : (1 : ℝ) ≤ (Real.log ((k : ℝ) + 2)) ^ 4 := one_le_pow₀ hlog_ge1
      have hpow2 : (Real.log ((k : ℝ) + 2)) ^ 4 ≤ ((B : ℝ) + 2) ^ 4 := by
        apply pow_le_pow_left₀ hlog_nonneg
        have hkB : (k : ℝ) + 2 ≤ (B : ℝ) + 2 := by exact_mod_cast (by omega : k + 2 ≤ B + 2)
        linarith
      nlinarith
    have h2R_nat : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) ≤ M0 * (B + 2) ^ 4 := by
      have hM0_ge : 2 * C_cov + 2 ≤ (M0 : ℝ) := by
        have h1 : (Nat.ceil (2 * C_cov + 2) : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast (by omega : _ ≤ M0)
        exact le_trans (Nat.le_ceil _) h1
      have hcast : ((2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℕ) : ℝ) ≤
          ((M0 * (B + 2) ^ 4 : ℕ) : ℝ) := by
        push_cast
        have hpos : (0 : ℝ) ≤ ((B : ℝ) + 2) ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hM0_ge hpos]
      exact_mod_cast hcast
    have hB_lt : B < (m + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt B
      simpa [sq] using this
    have hm_ge : 256 ≤ m := by omega
    have hB2_le : B + 2 ≤ 2 * m ^ 2 := by nlinarith
    have hprod_le : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (k / 2) ≤
        M0 * (2 * m ^ 2) ^ 5 := by
      have hk2_le : k / 2 ≤ B + 2 := by omega
      calc 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (k / 2)
          ≤ (M0 * (B + 2) ^ 4) * (B + 2) := Nat.mul_le_mul h2R_nat hk2_le
        _ = M0 * (B + 2) ^ 5 := by ring
        _ ≤ M0 * (2 * m ^ 2) ^ 5 := Nat.mul_le_mul_left M0 (Nat.pow_le_pow_left hB2_le 5)
    have hm2_ge : 128 ≤ m / 2 := by omega
    have hpow14 : (m / 2) ^ 14 ≤ 2 ^ m := by
      have h7 := pow_seven_le_two_pow hm2_ge
      have h14 : (m / 2) ^ 14 ≤ (2 ^ (m / 2)) ^ 2 := by
        calc (m / 2) ^ 14 = ((m / 2) ^ 7) ^ 2 := by ring
          _ ≤ (2 ^ (m / 2)) ^ 2 := Nat.pow_le_pow_left h7 2
      have h2m : (2 ^ (m / 2)) ^ 2 ≤ 2 ^ m := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      exact le_trans h14 h2m
    have hM0_le : M0 * (2 * m ^ 2) ^ 5 ≤ (m / 2) ^ 14 := by
      have hm_le : m ≤ 3 * (m / 2) := by omega
      have hM0_le_m2 : M0 ≤ m / 2 := by omega
      have h32 : 32 * 3 ^ 10 ≤ (m / 2) ^ 3 := by
        have : (128 : ℕ) ^ 3 ≤ (m / 2) ^ 3 := Nat.pow_le_pow_left hm2_ge 3
        have : 32 * 3 ^ 10 ≤ 128 ^ 3 := by norm_num
        omega
      calc M0 * (2 * m ^ 2) ^ 5
          = M0 * (32 * m ^ 10) := by ring
        _ ≤ (m / 2) * (32 * (3 * (m / 2)) ^ 10) :=
            Nat.mul_le_mul hM0_le_m2 (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hm_le 10))
        _ = (32 * 3 ^ 10) * (m / 2) ^ 11 := by ring
        _ ≤ (m / 2) ^ 3 * (m / 2) ^ 11 := Nat.mul_le_mul_right _ h32
        _ = (m / 2) ^ 14 := by ring
    exact le_trans hprod_le (le_trans hM0_le hpow14)
  exact ⟨hk_ge_k0, by omega, hpow43, hcarry⟩

/-- **Lemma 4 (Carry Recursion)**:
    There exists a universal constant `C4 > 0` such that for all `B, E, r : ℕ` with `2 * B ≤ E`
    and `r < 2 ^ B`, `r` is a sum of at most `C4 * (log (B + 2))^4` distinct positive divisors of
    `2 ^ E * oddPrimorial (E / 4)`. -/
theorem lemma4_carry_recursion :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ (B E r : ℕ), 2 * B ≤ E → r < 2 ^ B →
      ∃ S : Finset ℕ,
        (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ E * oddPrimorial (E / 4)) ∧
        S.sum id = r ∧
        (S.card : ℝ) ≤ C4 * (Real.log ((B : ℝ) + 2)) ^ 4 := by
  rcases mod_two_pow_covering with ⟨C_cov, hC_cov, hcov⟩
  rcases exists_bertrand_exceeds_R C_cov hC_cov with ⟨k0, hk0, hbert⟩
  rcases exists_B0_carry C_cov hC_cov k0 hk0 with ⟨B0, hB0, hcarry⟩
  set C4 : ℝ := max (5 * (B0 : ℝ)) (4 * C_cov + 4)
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
        have hpow_ge : (0.2 : ℝ) ≤ (Real.log ((B : ℝ) + 2)) ^ 4 := by
          have : (0.69 : ℝ) ^ 4 ≤ (Real.log ((B : ℝ) + 2)) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog2_ge 4
          linarith [show (0.2 : ℝ) ≤ (0.69 : ℝ) ^ 4 by norm_num]
        have hcard_le : (S.card : ℝ) ≤ (B0 : ℝ) := by exact_mod_cast le_trans hcard hB_small
        have hC4_ge : 5 * (B0 : ℝ) ≤ C4 := le_max_left _ _
        nlinarith
    push Not at hB_small
    by_cases hr_small : r < 2 ^ (B - 1)
    · have hB_lt : B - 1 < B := by omega
      rcases ih (B - 1) hB_lt E r (by omega) hr_small with ⟨S, hprop, hsum, hcard⟩
      refine ⟨S, hprop, hsum, le_trans hcard ?_⟩
      apply mul_le_mul_of_nonneg_left _ hC4_pos.le
      apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B - 1 + 2)))
      exact Real.log_le_log (by positivity) (by exact_mod_cast (by omega : B - 1 + 2 ≤ B + 2))
    push Not at hr_small
    rcases hcarry B hB_small with ⟨hk_ge_k0, hb_lt_B, hpow43, hcarry_bound⟩
    set b := Nat.sqrt B + 1
    set k := B - b
    have hk_ge2 : 2 ≤ k := by omega
    have hQ_ge3 : 3 ≤ k / 2 := by omega
    have hbert_k := hbert k hk_ge_k0
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
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hS1_card)
          _ ≤ 2 ^ (b - 1) * 2 ^ k := Nat.mul_le_mul_right _ hcarry_bound
      have h3 : 2 ^ (b - 1) * 2 ^ k = 2 ^ (B - 1) := by
        rw [← pow_add]
        congr 1; omega
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
      simp only [id_eq]
      rw [← Finset.mul_sum]
      have hsum2 : S2.sum (fun a => a) = r' := hS2_sum
      rw [hsum2]
      exact hr'_eq
    · have hcard_eq : (S1 ∪ S2').card = S1.card + S2.card := by
        rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective S2 (fun a c h => Nat.eq_of_mul_eq_mul_left (by positivity) h)]
      rw [hcard_eq, Nat.cast_add]
      have hlogb_le : Real.log ((b : ℝ) + 2) ≤ (3 / 4 : ℝ) * Real.log ((B : ℝ) + 2) := by
        have hcast : (((b : ℝ) + 2) ^ 4) ≤ (((B : ℝ) + 2) ^ 3) := by exact_mod_cast hpow43
        have hlog_ineq : Real.log (((b : ℝ) + 2) ^ 4) ≤ Real.log (((B : ℝ) + 2) ^ 3) :=
          Real.log_le_log (by positivity) hcast
        rw [Real.log_pow, Real.log_pow] at hlog_ineq
        push_cast at hlog_ineq
        linarith
      have hlogb_nonneg : 0 ≤ Real.log ((b : ℝ) + 2) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b + 2))
      have hlogb4 : (Real.log ((b : ℝ) + 2)) ^ 4 ≤ (1 / 2 : ℝ) * (Real.log ((B : ℝ) + 2)) ^ 4 := by
        have h1 : (Real.log ((b : ℝ) + 2)) ^ 4 ≤ ((3 / 4 : ℝ) * Real.log ((B : ℝ) + 2)) ^ 4 :=
          pow_le_pow_left₀ hlogb_nonneg hlogb_le 4
        have h2 : ((3 / 4 : ℝ) * Real.log ((B : ℝ) + 2)) ^ 4 = (81 / 256 : ℝ) * (Real.log ((B : ℝ) + 2)) ^ 4 := by ring
        have hpow_nonneg : 0 ≤ (Real.log ((B : ℝ) + 2)) ^ 4 := by positivity
        nlinarith
      have hlogB_ge1 : (1 : ℝ) ≤ Real.log ((B : ℝ) + 2) := by
        have h4 : (4 : ℝ) ≤ (B : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ B + 2)
        have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
        linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
      have hS1_le : (S1.card : ℝ) ≤ (1 / 2 : ℝ) * C4 * (Real.log ((B : ℝ) + 2)) ^ 4 := by
        have hc1 : (S1.card : ℝ) ≤ 2 * (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) := by
          exact_mod_cast hS1_card
        have hceil : (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) ≤
            C_cov * (Real.log ((k : ℝ) + 2)) ^ 4 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
        have hlogk_le : Real.log ((k : ℝ) + 2) ≤ Real.log ((B : ℝ) + 2) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 2 ≤ B + 2))
        have hlogk4 : (Real.log ((k : ℝ) + 2)) ^ 4 ≤ (Real.log ((B : ℝ) + 2)) ^ 4 :=
          pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k + 2))) hlogk_le 4
        have hpow1 : (1 : ℝ) ≤ (Real.log ((B : ℝ) + 2)) ^ 4 := one_le_pow₀ hlogB_ge1
        have hC4_ge : 4 * C_cov + 4 ≤ C4 := le_max_right _ _
        nlinarith
      nlinarith

/-! ## Part 4: Stage 2 — Tail Recursion on `M(E) = 2^E * oddPrimorial (E / 4)` -/

/-- Factoring `oddPrimorial a` into `oddPrimorial b * ∏_{b < p ≤ a} p` when `2 ≤ b ≤ a`. -/
lemma oddPrimorial_eq_mul_uTop {a b : ℕ} (hb2 : 2 ≤ b) (hba : b ≤ a) :
    oddPrimorial a = oddPrimorial b * ∏ p ∈ (Finset.Ioc b a).filter Nat.Prime, p := by
  unfold oddPrimorial
  have hdisj : Disjoint ((Finset.range (b + 1)).filter (fun p => p.Prime ∧ 3 ≤ p))
      ((Finset.Ioc b a).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp1 hp2
    omega
  rw [← Finset.prod_union hdisj]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
  constructor
  · intro ⟨hpa, hp, hp3⟩
    by_cases hpb : p ≤ b
    · exact Or.inl ⟨by omega, hp, hp3⟩
    · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
  · rintro (⟨hpb, hp, hp3⟩ | ⟨⟨hbp, hpa⟩, hp⟩)
    · exact ⟨by omega, hp, hp3⟩
    · exact ⟨by omega, hp, by omega⟩

/-- Threshold 3 for Stage 2 tail recursion. -/
lemma exists_E0_stage2 (C_cov : ℝ) (hC : 0 < C_cov) (k0 : ℕ) (hk0 : 16 ≤ k0) :
    ∃ E0 : ℕ, 256 ≤ E0 ∧ ∀ E : ℕ, E0 < E →
      let k := 45 * E / 100
      let E_next := E - k
      k0 ≤ k ∧
      2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (E / 4) * 2 ^ k ≤ 2 ^ (E / 2) ∧
      Real.log ((E_next : ℝ) + 2) ≤ Real.log ((E : ℝ) + 2) - 1 / 2 := by
  set M1 : ℕ := max 128 (Nat.ceil (2 * C_cov + 2) + 2)
  set E0 : ℕ := max (3 * k0 + 256) (25 * max M1 (M1 * 26 ^ 5))
  refine ⟨E0, by omega, ?_⟩
  intro E hE
  dsimp only
  set k := 45 * E / 100
  set E_next := E - k
  have hk_ge_k0 : k0 ≤ k := by
    have : 3 * k0 + 256 ≤ E0 := le_max_left _ _
    omega
  have hcarry2 : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (E / 4) * 2 ^ k ≤ 2 ^ (E / 2) := by
    set m := E / 25
    have hm_ge_M1 : M1 ≤ m := by
      have : 25 * max M1 (M1 * 26 ^ 5) ≤ E0 := le_max_right _ _
      have : M1 ≤ max M1 (M1 * 26 ^ 5) := le_max_left _ _
      omega
    have hm_ge_big : M1 * 26 ^ 5 ≤ m := by
      have : 25 * max M1 (M1 * 26 ^ 5) ≤ E0 := le_max_right _ _
      have : M1 * 26 ^ 5 ≤ max M1 (M1 * 26 ^ 5) := le_max_right _ _
      omega
    have hm_ge128 : 128 ≤ m := le_trans (le_max_left _ _) hm_ge_M1
    have hlog_le : Real.log ((k : ℝ) + 2) ≤ (k : ℝ) + 2 := by
      have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      linarith [Real.log_le_sub_one_of_pos hpos]
    have hlog_nonneg : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k + 2))
    have hlog_ge1 : (1 : ℝ) ≤ Real.log ((k : ℝ) + 2) := by
      have h4 : (4 : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ k + 2)
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
    have hceil_le : (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) ≤
        C_cov * (Real.log ((k : ℝ) + 2)) ^ 4 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h2R_le : (2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) ≤
        (2 * C_cov + 2) * ((E : ℝ) + 2) ^ 4 := by
      have hpow1 : (1 : ℝ) ≤ (Real.log ((k : ℝ) + 2)) ^ 4 := one_le_pow₀ hlog_ge1
      have hpow2 : (Real.log ((k : ℝ) + 2)) ^ 4 ≤ ((E : ℝ) + 2) ^ 4 := by
        apply pow_le_pow_left₀ hlog_nonneg
        have hkE : (k : ℝ) + 2 ≤ (E : ℝ) + 2 := by exact_mod_cast (by omega : k + 2 ≤ E + 2)
        linarith
      nlinarith
    have h2R_nat : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) ≤ M1 * (E + 2) ^ 4 := by
      have hM1_ge : 2 * C_cov + 2 ≤ (M1 : ℝ) := by
        have h1 : (Nat.ceil (2 * C_cov + 2) : ℝ) ≤ (M1 : ℝ) := by exact_mod_cast (by omega : _ ≤ M1)
        exact le_trans (Nat.le_ceil _) h1
      have hcast : ((2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℕ) : ℝ) ≤
          ((M1 * (E + 2) ^ 4 : ℕ) : ℝ) := by
        push_cast
        have hpos : (0 : ℝ) ≤ ((E : ℝ) + 2) ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hM1_ge hpos]
      exact_mod_cast hcast
    have hE2_le : E + 2 ≤ 26 * m := by omega
    have hprod_le : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (E / 4) ≤ 2 ^ m := by
      have h1 : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (E / 4) ≤ M1 * (26 * m) ^ 5 := by
        calc 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (E / 4)
            ≤ (M1 * (E + 2) ^ 4) * (E + 2) := Nat.mul_le_mul h2R_nat (by omega)
          _ = M1 * (E + 2) ^ 5 := by ring
          _ ≤ M1 * (26 * m) ^ 5 := Nat.mul_le_mul_left M1 (Nat.pow_le_pow_left hE2_le 5)
      have h2 : M1 * (26 * m) ^ 5 ≤ m ^ 7 := by
        have hm1 : 1 ≤ m := by omega
        calc M1 * (26 * m) ^ 5 = (M1 * 26 ^ 5) * m ^ 5 := by ring
          _ ≤ m * m ^ 5 := Nat.mul_le_mul_right _ hm_ge_big
          _ = m ^ 6 := by ring
          _ ≤ m ^ 7 := Nat.pow_le_pow_right hm1 (by omega)
      exact le_trans h1 (le_trans h2 (pow_seven_le_two_pow hm_ge128))
    have hmk_le : m + k ≤ E / 2 := by omega
    calc 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) * (E / 4) * 2 ^ k
        ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_right _ hprod_le
      _ = 2 ^ (m + k) := (pow_add 2 m k).symm
      _ ≤ 2 ^ (E / 2) := Nat.pow_le_pow_right (by omega) hmk_le
  have hlog_drop : Real.log ((E_next : ℝ) + 2) ≤ Real.log ((E : ℝ) + 2) - 1 / 2 := by
    have hratio : (E_next : ℝ) + 2 ≤ (56 / 100 : ℝ) * ((E : ℝ) + 2) := by
      have hnat : 100 * (E_next + 2) ≤ 56 * (E + 2) := by omega
      have hcast : (100 : ℝ) * ((E_next : ℝ) + 2) ≤ 56 * ((E : ℝ) + 2) := by exact_mod_cast hnat
      linarith
    have hlog_56 : Real.log (56 / 100 : ℝ) ≤ -(1 / 2 : ℝ) := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have hexp1 : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
      have hsq : ((56 / 100 : ℝ) * Real.exp (1 / 2)) ^ 2 ≤ 1 := by
        have hmul : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
          rw [sq, ← Real.exp_add]; norm_num
        calc ((56 / 100 : ℝ) * Real.exp (1 / 2)) ^ 2
            = (56 / 100 : ℝ) ^ 2 * (Real.exp (1 / 2)) ^ 2 := by ring
          _ = (56 / 100 : ℝ) ^ 2 * Real.exp 1 := by rw [hmul]
          _ ≤ (56 / 100 : ℝ) ^ 2 * 2.72 := by nlinarith
          _ ≤ 1 := by norm_num
      have hprod_le1 : (56 / 100 : ℝ) * Real.exp (1 / 2) ≤ 1 := by
        by_contra hlt; push Not at hlt
        nlinarith [Real.exp_pos (1 / 2)]
      have hexp_neg : Real.exp (-(1 / 2 : ℝ)) = (Real.exp (1 / 2))⁻¹ := Real.exp_neg (1 / 2)
      rw [hexp_neg]
      exact (le_inv_comm₀ (by norm_num) (Real.exp_pos (1 / 2))).mpr (by
        rw [inv_eq_one_div, le_div_iff₀ (by norm_num)]
        linarith)
    have h1 : Real.log ((E_next : ℝ) + 2) ≤ Real.log ((56 / 100 : ℝ) * ((E : ℝ) + 2)) :=
      Real.log_le_log (by positivity) hratio
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    linarith
  exact ⟨hk_ge_k0, hcarry2, hlog_drop⟩

/-- **Stage 2 (Tail Recursion)**:
    There exists a universal constant `C5 > 0` such that for all `E ≥ 1` and
    `x < 2 ^ E * oddPrimorial (E / 4)`, `x` is a sum of at most `C5 * (log (E + 2))^5`
    distinct positive divisors of `2 ^ E * oddPrimorial (E / 4)`. -/
theorem stage2_tail_recursion :
    ∃ C5 : ℝ, 0 < C5 ∧ ∀ (E x : ℕ), 1 ≤ E → x < 2 ^ E * oddPrimorial (E / 4) →
      ∃ S : Finset ℕ,
        (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ E * oddPrimorial (E / 4)) ∧
        S.sum id = x ∧
        (S.card : ℝ) ≤ C5 * (Real.log ((E : ℝ) + 2)) ^ 5 := by
  rcases mod_two_pow_covering with ⟨C_cov, hC_cov, hcov⟩
  rcases exists_bertrand_exceeds_R C_cov hC_cov with ⟨k0, hk0, hbert⟩
  rcases lemma4_carry_recursion with ⟨C4, hC4, hlem4⟩
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
        have h1 : S.card ≤ M_base := le_trans (Finset.card_le_card hsub) (by simp)
        exact_mod_cast h1
      have hlog_ge : (0.69 : ℝ) ≤ Real.log ((E : ℝ) + 2) := by
        have h2 : (2 : ℝ) ≤ (E : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ E by positivity]
        linarith [Real.log_le_log (by norm_num) h2, Real.log_two_gt_d9]
      have hpow5_ge : (0.1 : ℝ) ≤ (Real.log ((E : ℝ) + 2)) ^ 5 := by
        have : (0.69 : ℝ) ^ 5 ≤ (Real.log ((E : ℝ) + 2)) ^ 5 := pow_le_pow_left₀ (by norm_num) hlog_ge 5
        linarith [show (0.1 : ℝ) ≤ (0.69 : ℝ) ^ 5 by norm_num]
      have hC5_ge : 10 * (M_base : ℝ) ≤ C5 := le_max_left _ _
      nlinarith
    push Not at hE_small
    by_cases hx_small : x < 2 ^ (E / 2)
    · rcases hlem4 (E / 2) E x (by omega) hx_small with ⟨S, hprop, hsum, hcard⟩
      refine ⟨S, hprop, hsum, ?_⟩
      have hlog_le : Real.log ((E / 2 : ℕ) + 2 : ℝ) ≤ Real.log ((E : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E / 2 + 2 ≤ E + 2))
      have hlog4 : (Real.log ((E / 2 : ℕ) + 2 : ℝ)) ^ 4 ≤ (Real.log ((E : ℝ) + 2)) ^ 4 :=
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E / 2 + 2))) hlog_le 4
      have hlog_ge1 : (1 : ℝ) ≤ Real.log ((E : ℝ) + 2) := by
        have h4 : (4 : ℝ) ≤ (E : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ E + 2)
        have hlog4' : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
        linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
      have hpow45 : (Real.log ((E : ℝ) + 2)) ^ 4 ≤ (Real.log ((E : ℝ) + 2)) ^ 5 := by
        have : (Real.log ((E : ℝ) + 2)) ^ 4 * 1 ≤ (Real.log ((E : ℝ) + 2)) ^ 4 * Real.log ((E : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
        linarith
      have hC4_le : C4 ≤ C5 := le_trans (by linarith) (le_max_right _ _)
      calc (S.card : ℝ)
          ≤ C4 * (Real.log ((E / 2 : ℕ) + 2 : ℝ)) ^ 4 := hcard
        _ ≤ C4 * (Real.log ((E : ℝ) + 2)) ^ 4 := mul_le_mul_of_nonneg_left hlog4 hC4.le
        _ ≤ C4 * (Real.log ((E : ℝ) + 2)) ^ 5 := mul_le_mul_of_nonneg_left hpow45 hC4.le
        _ ≤ C5 * (Real.log ((E : ℝ) + 2)) ^ 5 := mul_le_mul_of_nonneg_right hC4_le (by positivity)
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
      have hpow_lt : 2 ^ (E / 4) < 2 ^ (E_next / 2) :=
        Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have hbert_stage2 : 2 * Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) ≤
        oddPrimeCounting (E / 4) - oddPrimeCounting ((k + 1) / 4) := by
      have hb := hbert k hk_ge_k0
      have hmono := oddPrimeCounting_mono (show k / 2 ≤ E / 4 by omega)
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
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hS1_card)
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
      intro d hd1 hd2
      rw [Finset.mem_image] at hd2
      rcases hd2 with ⟨a, _, rfl⟩
      exact (hS1_prop (2 ^ k * a) hd1).2.2.1 (dvd_mul_right (2 ^ k) a)
    have hdisj13 : Disjoint S1 S3 := by
      rw [Finset.disjoint_left]
      intro d hd1 hd3
      rw [Finset.mem_image] at hd3
      rcases hd3 with ⟨b, _, rfl⟩
      exact (hS1_prop (2 ^ k * U_top * b) hd1).2.2.1 (by rw [mul_assoc]; exact dvd_mul_right (2 ^ k) (U_top * b))
    have hdisj23 : Disjoint S2 S3 := by
      rw [Finset.disjoint_left]
      intro d hd2 hd3
      rw [Finset.mem_image] at hd2 hd3
      rcases hd2 with ⟨a, ha, rfl⟩
      rcases hd3 with ⟨b, hb, hab⟩
      have hb_pos : 0 < b := (hS3_prop b hb).1
      have ha_eq : a = U_top * b := by
        have h1 : 2 ^ k * (U_top * b) = 2 ^ k * a := by linarith
        exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm
      have ha_le : a ≤ r1 := by
        rw [← hS2_sum]
        exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) ha
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
      · rw [Finset.mem_image] at hd2
        rcases hd2 with ⟨a, ha, rfl⟩
        rcases hS2_prop a ha with ⟨hpos, hdvd⟩
        refine ⟨Nat.mul_pos (by positivity) hpos, ?_⟩
        have hmul := Nat.mul_dvd_mul_left (2 ^ k) hdvd
        have hrew : 2 ^ k * (2 ^ E_next * oddPrimorial (E_next / 4)) =
            2 ^ E * oddPrimorial (E_next / 4) := by
          rw [← mul_assoc, ← pow_add, show k + E_next = E by omega]
        rw [hrew] at hmul
        exact dvd_trans hmul (Nat.mul_dvd_mul_left (2 ^ E) (oddPrimorial_dvd_oddPrimorial (by omega)))
      · rw [Finset.mem_image] at hd3
        rcases hd3 with ⟨b, hb, rfl⟩
        rcases hS3_prop b hb with ⟨hpos, hdvd⟩
        refine ⟨Nat.mul_pos (Nat.mul_pos (by positivity) hU_pos) hpos, ?_⟩
        have hmul := Nat.mul_dvd_mul_left (2 ^ k * U_top) hdvd
        have hrew : 2 ^ k * U_top * (2 ^ E_next * oddPrimorial (E_next / 4)) =
            2 ^ E * oddPrimorial (E / 4) := by
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
      have hL_ge1 : (1 : ℝ) ≤ L := by
        have h4 : (4 : ℝ) ≤ (E : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ E + 2)
        have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
        linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
      have hLn_nonneg : 0 ≤ Ln := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E_next + 2))
      have hLn_le_L : Ln ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E_next + 2 ≤ E + 2))
      have hLn5 : Ln ^ 5 ≤ L ^ 5 - (1 / 2 : ℝ) * L ^ 4 := by
        have hLn4 : Ln ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hLn_nonneg hLn_le_L 4
        have h1 : Ln ^ 5 = Ln * Ln ^ 4 := by ring
        have h2 : Ln * Ln ^ 4 ≤ (L - 1 / 2) * L ^ 4 :=
          mul_le_mul hlog_drop hLn4 (by positivity) (by linarith)
        linarith
      have hS1_le : (S1.card : ℝ) ≤ (2 * C_cov + 2) * L ^ 4 := by
        have hc1 : (S1.card : ℝ) ≤ 2 * (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) := by
          exact_mod_cast hS1_card
        have hceil : (Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4) : ℝ) ≤
            C_cov * (Real.log ((k : ℝ) + 2)) ^ 4 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
        have hlogk_le : Real.log ((k : ℝ) + 2) ≤ L :=
          Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 2 ≤ E + 2))
        have hlogk4 : (Real.log ((k : ℝ) + 2)) ^ 4 ≤ L ^ 4 :=
          pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k + 2))) hlogk_le 4
        have hpow1 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL_ge1
        nlinarith
      have hS2_le : (S2_raw.card : ℝ) ≤ C4 * L ^ 4 := by
        have hlog_le : Real.log ((E_next / 2 : ℕ) + 2 : ℝ) ≤ L :=
          Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E_next / 2 + 2 ≤ E + 2))
        have hlog4 : (Real.log ((E_next / 2 : ℕ) + 2 : ℝ)) ^ 4 ≤ L ^ 4 :=
          pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E_next / 2 + 2))) hlog_le 4
        exact le_trans hS2_card (mul_le_mul_of_nonneg_left hlog4 hC4.le)
      have hC5_ge : 2 * (2 * C_cov + 2 + C4) ≤ C5 := le_max_right _ _
      have hS3_le : (S3_raw.card : ℝ) ≤ C5 * (L ^ 5 - (1 / 2 : ℝ) * L ^ 4) :=
        le_trans hS3_card (mul_le_mul_of_nonneg_left hLn5 hC5_pos.le)
      have hcoef_le : (2 * C_cov + 2 + C4) * L ^ 4 ≤ (1 / 2 : ℝ) * C5 * L ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith

/-! ## Part 5: Stage 1 Mixed-Radix Factorization & Main Theorem `erdos18_alpha5` -/

/-- Elementary identity: `(2 * m)! = 2 ^ m * m! * ∏_{i < m} (2 * i + 1)`. -/
lemma double_factorial_split (m : ℕ) :
    (2 * m).factorial = 2 ^ m * m.factorial * ∏ i ∈ Finset.range m, (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ, mul_assoc]
    rw [h1, ih, Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
    ring

/-- Product of odd numbers is odd. -/
lemma not_two_dvd_odd_prod (m : ℕ) : ¬(2 ∣ ∏ i ∈ Finset.range m, (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ]
    intro hdvd
    rcases Nat.prime_two.dvd_mul.mp hdvd with h1 | h2
    · exact ih h1
    · omega

/-- Elementary 2-adic valuation bounds for `n!`: `n / 2 ≤ n.factorial.factorization 2 ≤ n`. -/
lemma factorial_two_val_bounds (n : ℕ) :
    n / 2 ≤ n.factorial.factorization 2 ∧ n.factorial.factorization 2 ≤ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp
    have hval_even : ∀ m, (2 * m).factorial.factorization 2 = m + m.factorial.factorization 2 := by
      intro m
      rw [double_factorial_split m]
      have hne1 : 2 ^ m * m.factorial ≠ 0 := Nat.mul_ne_zero (by positivity) (Nat.factorial_ne_zero m)
      have hne2 : (∏ i ∈ Finset.range m, (2 * i + 1)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by omega
      rw [Nat.factorization_mul hne1 hne2, Nat.factorization_mul (by positivity) (Nat.factorial_ne_zero m)]
      simp only [Finsupp.coe_add, Pi.add_apply]
      have hv_odd : (∏ i ∈ Finset.range m, (2 * i + 1)).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (not_two_dvd_odd_prod m)
      rw [hv_odd, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    by_cases heven : n % 2 = 0
    · set m := n / 2
      have hnm : n = 2 * m := by omega
      rw [hnm, hval_even m]
      rcases ih m (by omega) with ⟨hlo, hhi⟩
      omega
    · set m := n / 2
      have hnm : n = 2 * m + 1 := by omega
      rw [hnm, Nat.factorial_succ]
      rw [Nat.factorization_mul (by omega) (Nat.factorial_ne_zero (2 * m))]
      simp only [Finsupp.coe_add, Pi.add_apply]
      have hv_odd : (2 * m + 1).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by omega)
      rw [hv_odd, zero_add, hval_even m]
      rcases ih m (by omega) with ⟨hlo, hhi⟩
      omega

/-- Divisibility: `2 ^ E * oddPrimorial (E / 4) ∣ n!` where `E = n.factorial.factorization 2`. -/
lemma M_tail_dvd_factorial (n : ℕ) :
    2 ^ (n.factorial.factorization 2) * oddPrimorial (n.factorial.factorization 2 / 4) ∣ n.factorial := by
  set E := n.factorial.factorization 2
  have hE_le : E ≤ n := (factorial_two_val_bounds n).2
  have h2_dvd : 2 ^ E ∣ n.factorial := Nat.ordProj_dvd n.factorial 2
  have hodd_dvd : oddPrimorial (E / 4) ∣ n.factorial := by
    have hind : ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≤ n) → (∏ p ∈ P, p) ∣ n.factorial := by
      intro P
      induction P using Finset.induction_on with
      | empty => intro _; simp
      | @insert p s hp ih =>
        intro hP
        rw [Finset.prod_insert hp]
        have hp_b := hP p (Finset.mem_insert_self p s)
        have hs_b : ∀ q ∈ s, q.Prime ∧ q ≤ n := fun q hq => hP q (Finset.mem_insert_of_mem hq)
        have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
          apply Nat.Coprime.prod_right
          intro q hq
          exact (Nat.coprime_primes hp_b.1 (hs_b q hq).1).mpr (fun h => hp (h ▸ hq))
        exact hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_factorial hp_b.1.pos hp_b.2) (ih hs_b)
    unfold oddPrimorial
    apply hind
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.2.1, by omega⟩
  have hcop2 : Nat.Coprime (2 ^ E) (oddPrimorial (E / 4)) := by
    apply Nat.Coprime.pow_left
    unfold oddPrimorial
    apply Nat.Coprime.prod_right
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact (Nat.coprime_primes Nat.prime_two hp.2.1).mpr (by omega)
  exact hcop2.mul_dvd_of_dvd_of_dvd h2_dvd hodd_dvd

/-- Greedy factorization of `U ≥ 1` (all prime factors `≤ n`) into factors `D_i ∈ [1, K]`
    such that `(K / n) ^ (Ds.length - 1) ≤ U`. -/
lemma greedy_factorize (n K : ℕ) (hn : 1 ≤ n) (hK : n ≤ K) :
    ∀ U : ℕ, 1 ≤ U → (∀ p : ℕ, p.Prime → p ∣ U → p ≤ n) →
      ∃ Ds : List ℕ, Ds.prod = U ∧ (∀ D ∈ Ds, 1 ≤ D ∧ D ≤ K) ∧
        (K / n) ^ (Ds.length - 1) ≤ U := by
  intro U
  induction U using Nat.strong_induction_on with
  | ind U ih =>
    intro hU1 hprimes
    by_cases hUK : U ≤ K
    · exact ⟨[U], by simp, by simp [hU1, hUK], by simp [hU1]⟩
    push Not at hUK
    have hex : ∃ D ∈ U.divisors, D ≤ K := ⟨1, Nat.mem_divisors.mpr ⟨one_dvd U, by omega⟩, by omega⟩
    let S := U.divisors.filter (· ≤ K)
    have hS_ne : S.Nonempty := by
      rcases hex with ⟨D, hD, hDK⟩
      exact ⟨D, Finset.mem_filter.mpr ⟨hD, hDK⟩⟩
    let D := S.max' hS_ne
    have hD_mem : D ∈ S := Finset.max'_mem S hS_ne
    have hD_dvd : D ∣ U := (Nat.mem_divisors.mp (Finset.mem_filter.mp hD_mem).1).1
    have hD_le_K : D ≤ K := (Finset.mem_filter.mp hD_mem).2
    have hD_pos : 1 ≤ D := Nat.pos_of_dvd_of_pos hD_dvd (by omega)
    set U' := U / D
    have hDU' : D * U' = U := Nat.mul_div_cancel' hD_dvd
    have hU'_gt1 : 1 < U' := by
      by_contra hle; push Not at hle
      have : U' ≤ 1 := hle
      have : D * U' ≤ D * 1 := Nat.mul_le_mul_left D this
      omega
    let p := U'.minFac
    have hp_prime : p.Prime := Nat.minFac_prime (by omega)
    have hp_dvd_U' : p ∣ U' := Nat.minFac_dvd U'
    have hp_dvd_U : p ∣ U := dvd_trans hp_dvd_U' (by rw [← hDU']; exact dvd_mul_left U' D)
    have hp_le_n : p ≤ n := hprimes p hp_prime hp_dvd_U
    have hDp_dvd : D * p ∣ U := by
      rw [← hDU']
      exact Nat.mul_dvd_mul_left D hp_dvd_U'
    have hDp_gt_K : K < D * p := by
      by_contra hle; push Not at hle
      have hDp_mem : D * p ∈ S :=
        Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hDp_dvd, by omega⟩, hle⟩
      have hle_max : D * p ≤ D := Finset.le_max' S (D * p) hDp_mem
      have hp_ge2 : 2 ≤ p := hp_prime.two_le
      nlinarith
    have hD_ge_Kn : K / n ≤ D := by
      have h1 : K < D * n := lt_of_lt_of_le hDp_gt_K (Nat.mul_le_mul_left D hp_le_n)
      exact Nat.div_le_of_le_mul (by rw [mul_comm]; omega)
    have hD_gt1 : 1 < D := by
      by_contra hle; push Not at hle
      have hD1 : D = 1 := by omega
      rw [hD1, one_mul] at hDp_gt_K
      omega
    have hU'_lt : U' < U := by
      have h1 : 2 * U' ≤ D * U' := Nat.mul_le_mul_right U' hD_gt1
      omega
    have hprimes' : ∀ q : ℕ, q.Prime → q ∣ U' → q ≤ n := fun q hq hqd =>
      hprimes q hq (dvd_trans hqd (by rw [← hDU']; exact dvd_mul_left U' D))
    rcases ih U' hU'_lt (by omega) hprimes' with ⟨Ds', hprod', hmem', hlen'⟩
    refine ⟨D :: Ds', ?_, ?_, ?_⟩
    · simp only [List.prod_cons, hprod', hDU']
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact ⟨hD_pos, hD_le_K⟩
      · exact hmem' x hx'
    · simp only [List.length_cons]
      have hDs'_pos : 1 ≤ Ds'.length := by
        cases Ds' with
        | nil => simp at hprod'; omega
        | cons _ _ => simp
      have hsub : Ds'.length + 1 - 1 = (Ds'.length - 1) + 1 := by omega
      rw [hsub, pow_succ, mul_comm, ← hDU']
      exact Nat.mul_le_mul hD_ge_Kn hlen'

/-- Stage 1 mixed-radix induction over `Ds : List ℕ`. -/
lemma mixed_radix_stage1 (M K : ℕ) (C_digit C_tail : ℝ)
    (hdigit : ∀ r < K, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = r ∧ (S.card : ℝ) ≤ C_digit)
    (htail : ∀ x < M, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = x ∧ (S.card : ℝ) ≤ C_tail) :
    ∀ (Ds : List ℕ), (∀ D ∈ Ds, 1 ≤ D ∧ D ≤ K) →
      ∀ x < M * Ds.prod,
        ∃ S : Finset ℕ,
          (∀ d ∈ S, 0 < d ∧ d ∣ M * Ds.prod) ∧
          S.sum id = x ∧
          (S.card : ℝ) ≤ (Ds.length : ℝ) * C_digit + C_tail := by
  intro Ds
  induction Ds with
  | nil =>
    intro _ x hx
    simp only [List.prod_nil, mul_one, List.length_nil, Nat.cast_zero, zero_mul, zero_add] at hx ⊢
    exact htail x hx
  | cons D Ds' ih =>
    intro hDs x hx
    have hD_b := hDs D (List.mem_cons_self ..)
    have hDs'_b : ∀ D' ∈ Ds', 1 ≤ D' ∧ D' ≤ K := fun D' h => hDs D' (List.mem_cons_of_mem D h)
    have hr_lt : x % D < K := lt_of_lt_of_le (Nat.mod_lt x (by omega)) hD_b.2
    have hq_lt : x / D < M * Ds'.prod := by
      simp only [List.prod_cons] at hx
      exact Nat.div_lt_of_lt_mul (by linarith)
    rcases hdigit (x % D) hr_lt with ⟨Sr, hSr_prop, hSr_sum, hSr_card⟩
    rcases ih hDs'_b (x / D) hq_lt with ⟨Sq, hSq_prop, hSq_sum, hSq_card⟩
    let Sq' := Sq.image (D * ·)
    have hdisj : Disjoint Sr Sq' := by
      rw [Finset.disjoint_left]
      intro d hdr hdq
      rw [Finset.mem_image] at hdq
      rcases hdq with ⟨a, ha, rfl⟩
      have ha_pos : 0 < a := (hSq_prop a ha).1
      have hd_le : D * a ≤ x % D := by
        rw [← hSr_sum]
        exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hdr
      have hD_le : D ≤ D * a := Nat.le_mul_of_pos_right D ha_pos
      have hmod_lt : x % D < D := Nat.mod_lt x (by omega)
      omega
    refine ⟨Sr ∪ Sq', ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_union] at hd
      rcases hd with hdr | hdq
      · rcases hSr_prop d hdr with ⟨h1, h2⟩
        exact ⟨h1, dvd_mul_of_dvd_left h2 _⟩
      · rw [Finset.mem_image] at hdq
        rcases hdq with ⟨a, ha, rfl⟩
        rcases hSq_prop a ha with ⟨h1, h2⟩
        refine ⟨Nat.mul_pos (by omega) h1, ?_⟩
        simp only [List.prod_cons]
        have hrew : M * (D * Ds'.prod) = D * (M * Ds'.prod) := by ring
        rw [hrew]
        exact Nat.mul_dvd_mul_left D h2
    · rw [Finset.sum_union hdisj, hSr_sum,
          Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]
      simp only [id_eq]; rw [← Finset.mul_sum]
      have hsum_q : Sq.sum (fun a => a) = x / D := hSq_sum
      rw [hsum_q]
      have hdiv := Nat.div_add_mod x D
      omega
    · have hcard_eq : (Sr ∪ Sq').card = Sr.card + Sq.card := by
        rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective Sq (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h)]
      rw [hcard_eq, Nat.cast_add, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- Helper: `n ≤ 2 ^ (n / 8)` for all `n ≥ 64`. -/
lemma nat_le_two_pow_div_eight {n : ℕ} (hn : 64 ≤ n) : n ≤ 2 ^ (n / 8) := by
  have hm : 8 ≤ n / 8 := by omega
  have hpow : ∀ m, 8 ≤ m → 8 * m + 7 ≤ 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [pow_succ, mul_comm]
      omega
  have h1 := hpow (n / 8) hm
  omega

/-- **Main Theorem (Erdős Problem #18, Target A — `h(n!) = O((log n)^5)`)**:
    There exists an absolute constant `C : ℝ` such that for every `n ≥ 2` and every integer
    `1 ≤ t ≤ n!`, `t` can be written as a sum of at most `C * (Real.log n)^5` distinct
    positive divisors of `n!`. -/
theorem erdos18_alpha5 :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → ∀ t : ℕ, 1 ≤ t → t ≤ n.factorial →
      ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n.factorial ∧ 0 < d) ∧
        S.sum id = t ∧ (S.card : ℝ) ≤ C * (Real.log n) ^ 5 := by
  rcases lemma4_carry_recursion with ⟨C4, hC4, hlem4⟩
  rcases stage2_tail_recursion with ⟨C5, hC5, hstage2⟩
  set C_small : ℝ := 10 * ((Nat.factorial 64 : ℕ) : ℝ)
  set C_big : ℝ := 25 * C4 * 81 + C5 * 243 + 10
  set C : ℝ := max C_small C_big
  refine ⟨C, ?_⟩
  intro n hn t ht1 htfac
  -- Case 1: t = n! (single divisor {n!})
  by_cases hteq : t = n.factorial
  · subst hteq
    refine ⟨{n.factorial}, ?_, by simp, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst hd
      exact ⟨dvd_refl _, Nat.factorial_pos n⟩
    · simp only [Finset.card_singleton, Nat.cast_one]
      have hlog_ge : (0.69 : ℝ) ≤ Real.log (n : ℝ) := by
        have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith [Real.log_le_log (by norm_num) h2, Real.log_two_gt_d9]
      have hpow5_ge : (0.1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
        have : (0.69 : ℝ) ^ 5 ≤ (Real.log (n : ℝ)) ^ 5 := pow_le_pow_left₀ (by norm_num) hlog_ge 5
        linarith [show (0.1 : ℝ) ≤ (0.69 : ℝ) ^ 5 by norm_num]
      have hC_ge : 10 ≤ C := le_trans (by linarith) (le_max_right _ _)
      nlinarith
  have ht_lt : t < n.factorial := lt_of_le_of_ne htfac hteq
  -- Case 2: n < 64 (practical_factorial)
  by_cases hn_small : n < 64
  · rcases practical_factorial n (by omega) t ht_lt with ⟨S, hprop, hsum⟩
    refine ⟨S, fun d hd => ⟨(hprop d hd).2, (hprop d hd).1⟩, hsum, ?_⟩
    have hsub' : S ⊆ Finset.Icc 1 (Nat.factorial 64) := by
      intro d hd
      rw [Finset.mem_Icc]
      have hd_le : d ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) (hprop d hd).2
      have hfac_le : n.factorial ≤ Nat.factorial 64 := Nat.factorial_le (by omega)
      exact ⟨(hprop d hd).1, le_trans hd_le hfac_le⟩
    have hcard_le' : (S.card : ℝ) ≤ (Nat.factorial 64 : ℝ) := by
      have : S.card ≤ Nat.factorial 64 := le_trans (Finset.card_le_card hsub') (by simp)
      exact_mod_cast this
    have hlog_ge : (0.69 : ℝ) ≤ Real.log (n : ℝ) := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [Real.log_le_log (by norm_num) h2, Real.log_two_gt_d9]
    have hpow5_ge : (0.1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
      have : (0.69 : ℝ) ^ 5 ≤ (Real.log (n : ℝ)) ^ 5 := pow_le_pow_left₀ (by norm_num) hlog_ge 5
      linarith [show (0.1 : ℝ) ≤ (0.69 : ℝ) ^ 5 by norm_num]
    have hC_ge : 10 * (Nat.factorial 64 : ℝ) ≤ C := le_max_left _ _
    nlinarith
  -- Case 3: n ≥ 64 (Stage 1 mixed-radix + Stage 2 tail recursion)
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
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
  have hDs_len_le : (Ds.length : ℝ) ≤ 25 * Real.log (n : ℝ) := by
    have hKn_ge : 2 ^ (n / 8) ≤ K / n := by
      have h1 : 2 ^ (n / 8) * n ≤ 2 ^ (E / 4) * 2 ^ (E / 4) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega)) hn_le_2E4
      have h2 : 2 ^ (E / 4) * 2 ^ (E / 4) ≤ K := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (le_trans h1 h2)
    have hpow_le_fac : (2 ^ (n / 8)) ^ (Ds.length - 1) ≤ n ^ n := by
      have h1 : (2 ^ (n / 8)) ^ (Ds.length - 1) ≤ (K / n) ^ (Ds.length - 1) :=
        Nat.pow_le_pow_left hKn_ge _
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
    have hlm1 : ((Ds.length - 1 : ℕ) : ℝ) ≤ 24 * Real.log (n : ℝ) := by
      nlinarith
    have hlen_cast : (Ds.length : ℝ) ≤ ((Ds.length - 1 : ℕ) : ℝ) + 1 := by
      have : Ds.length ≤ (Ds.length - 1) + 1 := by omega
      exact_mod_cast this
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
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  have hlogE_nonneg : 0 ≤ Real.log ((E : ℝ) + 2) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E + 2))
  have hdigit : ∀ r < K, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = r ∧
      (S.card : ℝ) ≤ C4 * (3 * Real.log (n : ℝ)) ^ 4 := by
    intro r hr
    rcases hlem4 (E / 2) E r (by omega) hr with ⟨S, hprop, hsum, hcard⟩
    refine ⟨S, hprop, hsum, le_trans hcard ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC4.le
    apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E / 2 + 2)))
    exact le_trans (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : E / 2 + 2 ≤ E + 2))) hlogE_le
  have htail : ∀ x < M, ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d ∧ d ∣ M) ∧ S.sum id = x ∧
      (S.card : ℝ) ≤ C5 * (3 * Real.log (n : ℝ)) ^ 5 := by
    intro x hx
    rcases hstage2 E x (by omega) hx with ⟨S, hprop, hsum, hcard⟩
    refine ⟨S, hprop, hsum, le_trans hcard ?_⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogE_nonneg hlogE_le 5) hC5.le
  have ht_lt_prod : t < M * Ds.prod := by rw [hDs_prod, hMU]; exact ht_lt
  rcases mixed_radix_stage1 M K (C4 * (3 * Real.log (n : ℝ)) ^ 4) (C5 * (3 * Real.log (n : ℝ)) ^ 5)
      hdigit htail Ds hDs_mem t ht_lt_prod with ⟨S, hprop, hsum, hcard⟩
  refine ⟨S, ?_, hsum, ?_⟩
  · intro d hd
    rcases hprop d hd with ⟨hpos, hdvd⟩
    rw [hDs_prod, hMU] at hdvd
    exact ⟨hdvd, hpos⟩
  · have hstep1 : (Ds.length : ℝ) * (C4 * (3 * Real.log (n : ℝ)) ^ 4) ≤
        25 * Real.log (n : ℝ) * (C4 * (3 * Real.log (n : ℝ)) ^ 4) :=
      mul_le_mul_of_nonneg_right hDs_len_le (by positivity)
    have hpow_eq : 25 * Real.log (n : ℝ) * (C4 * (3 * Real.log (n : ℝ)) ^ 4) +
        C5 * (3 * Real.log (n : ℝ)) ^ 5 = (25 * C4 * 81 + C5 * 243) * (Real.log (n : ℝ)) ^ 5 := by ring
    have hC_ge : 25 * C4 * 81 + C5 * 243 ≤ C := le_trans (by linarith) (le_max_right _ _)
    have hlog5_nonneg : 0 ≤ (Real.log (n : ℝ)) ^ 5 := by positivity
    have hstep2 : (25 * C4 * 81 + C5 * 243) * (Real.log (n : ℝ)) ^ 5 ≤ C * (Real.log (n : ℝ)) ^ 5 :=
      mul_le_mul_of_nonneg_right hC_ge hlog5_nonneg
    linarith

#print axioms erdos18_alpha5

end Erdos18
