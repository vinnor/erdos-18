import Erdos18.Entropy
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units

/-!
# Erdos18/Covering.lean (Layer 2b — Lemma 3: Parametric Mod-2^k Covering)

Formalizes Lemma 3:
- `Z_pmf`: `1/2 * δ_0 + 1/2 * Unif(Div(oddPrimorial (m/2)))` on `Fin (2^m)` with exact entropy
  `Hnat (Z_pmf m hm) = (1 + oddPrimeCounting (m/2) / 2) * log 2`.
- `shiftPMF` & `Y_pmf`: 2-sided dyadic shift mixture `Y = 2^s Z_{2^t}` with `Y < 2^k` strictly.
- `Hnat_conv_Y_sub_ge` & `Hnat_conv_mulMod_sub_ge`: untagged and prime-tagged entropy contraction.
- `mod_two_pow_covering`: parametric mod-`2^k` covering with `≤ 2 * R(k) = O((log k)^4)`
  strictly distinct positive divisors of `2^k * oddPrimorial Q_max`, each with `¬(2^k ∣ d)`
  and `< Q_max * 2^k`.
-/

namespace Erdos18

open Finset Nat Real

/-! ## Part 1: Divisor Distribution `Z_pmf` and Its Exact Entropy -/

lemma oddPrimorial_odd (m : ℕ) : Odd (oddPrimorial m) := by
  unfold oddPrimorial
  refine Finset.prod_induction (p := Odd) _ (fun _ _ ha hb => ha.mul hb) odd_one ?_
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact hp.2.1.odd_of_ne_two (by omega)

lemma card_divisors_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).divisors.card = 2 ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.card_insert_of_notMem hp, pow_succ]
    have hp_prime : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs_prime : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq_prime := hs_prime q hq
      have hne : p ≠ q := fun h => hp (h ▸ hq)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr hne
    rw [Nat.Coprime.card_divisors_mul hcop, ih hs_prime]
    have hdiv_p : p.divisors.card = 2 := by
      rw [Nat.Prime.divisors hp_prime, Finset.card_pair hp_prime.ne_one.symm]
    rw [hdiv_p]; ring

lemma card_divisors_oddPrimorial (m : ℕ) :
    (oddPrimorial m).divisors.card = 2 ^ oddPrimeCounting m := by
  unfold oddPrimorial oddPrimeCounting
  exact card_divisors_prod_primes _ fun p hp => (Finset.mem_filter.mp hp).2.1

/-- `Z_pmf m hm`: `1/2 * δ_0 + 1/2 * Unif(Div(oddPrimorial (m/2)))` on `Fin (2^m)` for `m ≥ 1`. -/
noncomputable def Z_pmf (m : ℕ) (hm : 1 ≤ m) : PMF_Fin (2 ^ m) where
  p x :=
    if x.val = 0 then (1 : ℝ) / 2
    else if x.val ∈ (oddPrimorial (m / 2)).divisors then 1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ))
    else 0
  nonneg x := by split_ifs <;> positivity
  sum_one := by
    have hQ_pos : 0 < oddPrimorial (m / 2) := oddPrimorial_pos (m / 2)
    have hQ_lt : oddPrimorial (m / 2) < 2 ^ m := oddPrimorial_lt_two_pow hm
    have hcard_pos : (0 : ℝ) < ((oddPrimorial (m / 2)).divisors.card : ℝ) := by
      rw [card_divisors_oddPrimorial]; positivity
    have h0_mem : (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)) ∈ Finset.univ := Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ h0_mem]
    have hp0 : (if (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)).val = 0 then (1 : ℝ) / 2
        else if (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)).val ∈ (oddPrimorial (m / 2)).divisors
          then 1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ)) else 0) = 1 / 2 := by simp
    rw [hp0]
    have hrest : ∑ x ∈ Finset.univ.erase (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)),
        (if x.val = 0 then (1 : ℝ) / 2
         else if x.val ∈ (oddPrimorial (m / 2)).divisors
           then 1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ)) else 0) = 1 / 2 := by
      have hfilt : ((Finset.univ.erase (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m))).filter
          (fun x => x.val ∈ (oddPrimorial (m / 2)).divisors)).card =
          (oddPrimorial (m / 2)).divisors.card := by
        apply Finset.card_bij (fun x _ => x.val)
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro x _ y _ h; exact Fin.ext h
        · intro d hd
          have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
          have hd_le : d ≤ oddPrimorial (m / 2) := Nat.le_of_dvd hQ_pos (Nat.dvd_of_mem_divisors hd)
          refine ⟨⟨d, lt_of_le_of_lt hd_le hQ_lt⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨Fin.ne_of_val_ne (by dsimp; omega), hd⟩
      have hsimp : ∑ x ∈ Finset.univ.erase (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)),
          (if x.val = 0 then (1 : ℝ) / 2
           else if x.val ∈ (oddPrimorial (m / 2)).divisors
             then 1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ)) else 0) =
          ∑ x ∈ (Finset.univ.erase (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m))).filter
            (fun x => x.val ∈ (oddPrimorial (m / 2)).divisors),
            1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ)) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx
        have hx0 : x.val ≠ 0 := fun h => (Finset.mem_erase.mp hx).1 (Fin.ext h)
        simp [hx0]
      rw [hsimp, Finset.sum_const, nsmul_eq_mul, hfilt]
      field_simp [hcard_pos.ne']
    linarith

/-- Exact Shannon entropy of `Z_pmf m hm` (valid for ALL `m ≥ 1`, including `m = 1, 2, 4`!). -/
theorem Hnat_Z_pmf (m : ℕ) (hm : 1 ≤ m) :
    Hnat (Z_pmf m hm) = (1 + (oddPrimeCounting (m / 2) : ℝ) / 2) * Real.log 2 := by
  have hQ_pos : 0 < oddPrimorial (m / 2) := oddPrimorial_pos (m / 2)
  have hQ_lt : oddPrimorial (m / 2) < 2 ^ m := oddPrimorial_lt_two_pow hm
  have hcard_eq : (oddPrimorial (m / 2)).divisors.card = 2 ^ oddPrimeCounting (m / 2) :=
    card_divisors_oddPrimorial (m / 2)
  have hcard_pos : (0 : ℝ) < ((oddPrimorial (m / 2)).divisors.card : ℝ) := by
    rw [hcard_eq]; positivity
  unfold Hnat Z_pmf
  dsimp only
  have h0_mem : (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)) ∈ Finset.univ := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ h0_mem]
  have ht0 : Real.negMulLog (if (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)).val = 0 then (1 : ℝ) / 2
      else if (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)).val ∈ (oddPrimorial (m / 2)).divisors
        then 1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ)) else 0) = (1 / 2) * Real.log 2 := by
    simp [Real.negMulLog, one_div, Real.log_inv]
  rw [ht0]
  have hfilt : ((Finset.univ.erase (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m))).filter
      (fun x => x.val ∈ (oddPrimorial (m / 2)).divisors)).card =
      (oddPrimorial (m / 2)).divisors.card := by
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x _ y _ h; exact Fin.ext h
    · intro d hd
      have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
      have hd_le : d ≤ oddPrimorial (m / 2) := Nat.le_of_dvd hQ_pos (Nat.dvd_of_mem_divisors hd)
      refine ⟨⟨d, lt_of_le_of_lt hd_le hQ_lt⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨Fin.ne_of_val_ne (by dsimp; omega), hd⟩
  have hrest : ∑ x ∈ Finset.univ.erase (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)),
      Real.negMulLog (if x.val = 0 then (1 : ℝ) / 2
       else if x.val ∈ (oddPrimorial (m / 2)).divisors
         then 1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ)) else 0) =
      (1 / 2) * (Real.log 2 + (oddPrimeCounting (m / 2) : ℝ) * Real.log 2) := by
    have hsimp : ∑ x ∈ Finset.univ.erase (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)),
        Real.negMulLog (if x.val = 0 then (1 : ℝ) / 2
         else if x.val ∈ (oddPrimorial (m / 2)).divisors
           then 1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ)) else 0) =
        ∑ x ∈ (Finset.univ.erase (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m))).filter
          (fun x => x.val ∈ (oddPrimorial (m / 2)).divisors),
          Real.negMulLog (1 / (2 * ((oddPrimorial (m / 2)).divisors.card : ℝ))) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : x.val ≠ 0 := fun h => (Finset.mem_erase.mp hx).1 (Fin.ext h)
      by_cases hmem : x.val ∈ (oddPrimorial (m / 2)).divisors
      · simp [hx0, hmem]
      · simp [hx0, hmem]
    rw [hsimp, Finset.sum_const, nsmul_eq_mul, hfilt, Real.negMulLog, one_div, Real.log_inv,
        Real.log_mul (by norm_num) hcard_pos.ne', hcard_eq, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hpow_ne : ((2 : ℝ) ^ oddPrimeCounting (m / 2)) ≠ 0 := by positivity
    field_simp [hpow_ne]
  rw [hrest]; ring

/-! ## Part 2: Dyadic Shift Pushforward `shiftPMF` & Conditional Bit-Shift Identity -/

/-- Pushforward of `Z_pmf (2^t)` to `Fin (2^k)` via `z ↦ 2^s * z` (for `s + 2^t ≤ k`). -/
noncomputable def shiftPMF (k t s : ℕ) (hst : s + 2 ^ t ≤ k) : PMF_Fin (2 ^ k) where
  p x :=
    if h : 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t) then
      (Z_pmf (2 ^ t) (Nat.one_le_two_pow)).p ⟨x.val / 2 ^ s, h.2⟩
    else 0
  nonneg x := by
    split_ifs with h
    · exact (Z_pmf (2 ^ t) Nat.one_le_two_pow).nonneg _
    · exact le_rfl
  sum_one := by
    rw [← (Z_pmf (2 ^ t) Nat.one_le_two_pow).sum_one]
    have hfilt : (∑ x : Fin (2 ^ k),
        if h : 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t) then
          (Z_pmf (2 ^ t) Nat.one_le_two_pow).p ⟨x.val / 2 ^ s, h.2⟩
        else 0) =
        ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t)),
          if h : 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t) then
            (Z_pmf (2 ^ t) Nat.one_le_two_pow).p ⟨x.val / 2 ^ s, h.2⟩
          else 0 := by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro x _; split_ifs <;> rfl
    rw [hfilt]
    apply Finset.sum_bij (fun x hx => ⟨x.val / 2 ^ s, (Finset.mem_filter.mp hx).2.2⟩)
    · intro _ _; exact Finset.mem_univ _
    · intro x hx y hy heq
      have hx_d := (Finset.mem_filter.mp hx).2.1
      have hy_d := (Finset.mem_filter.mp hy).2.1
      have hdiv : x.val / 2 ^ s = y.val / 2 ^ s := congrArg Fin.val heq
      apply Fin.ext
      rw [← Nat.mul_div_cancel' hx_d, ← Nat.mul_div_cancel' hy_d, hdiv]
    · intro z _
      have hlt : 2 ^ s * z.val < 2 ^ k := by
        calc 2 ^ s * z.val < 2 ^ s * 2 ^ (2 ^ t) := Nat.mul_lt_mul_of_pos_left z.isLt (Nat.two_pow_pos s)
          _ = 2 ^ (s + 2 ^ t) := (pow_add 2 s (2 ^ t)).symm
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hst
      refine ⟨⟨2 ^ s * z.val, hlt⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Nat.dvd_mul_right _ _, ?_⟩
        rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)]
        exact z.isLt
      · apply Fin.ext; dsimp only; exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)
    · intro x hx
      have h := (Finset.mem_filter.mp hx).2
      simp [h]

/-- Key bit-shift identity: for `s ≤ j` and `j - s < 2^t`,
    `condBitEnt (shiftPMF k t s hst) j = condBitEnt (Z_pmf (2^t)) (j - s)`. -/
lemma condBitEnt_shiftPMF (k t s j : ℕ) (hst : s + 2 ^ t ≤ k) (hsj : s ≤ j) (hjs : j - s < 2 ^ t) :
    condBitEnt (shiftPMF k t s hst) j = condBitEnt (Z_pmf (2 ^ t) Nat.one_le_two_pow) (j - s) := by
  let Z := Z_pmf (2 ^ t) Nat.one_le_two_pow
  let S := shiftPMF k t s hst
  -- For any a : Fin (2^j), if ¬(2^s ∣ a.val) then W_pref S j a = 0
  have hW_zero : ∀ a : Fin (2 ^ j), ¬ (2 ^ s ∣ a.val) → W_pref S j a = 0 := by
    intro a hnd
    unfold W_pref
    apply Finset.sum_eq_zero
    intro x hx
    have hpref : x.val % 2 ^ j = a.val := congrArg Fin.val (Finset.mem_filter.mp hx).2
    dsimp [S, shiftPMF]
    split_ifs with h
    · exfalso; apply hnd
      have hdvd : 2 ^ s ∣ 2 ^ j := Nat.pow_dvd_pow 2 hsj
      rw [← hpref]
      exact (Nat.dvd_mod_iff hdvd).mpr h.1
    · rfl
  -- For any a' : Fin (2^(j - s)), let a = ⟨2^s * a'.val, ...⟩ : Fin (2^j)
  have hpow_j : 2 ^ s * 2 ^ (j - s) = 2 ^ j := by rw [← pow_add, Nat.add_sub_of_le hsj]
  have hW_eq : ∀ a' : Fin (2 ^ (j - s)),
      W_pref S j ⟨2 ^ s * a'.val, by rw [← hpow_j]; exact Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)⟩ =
      W_pref Z (j - s) a' := by
    intro a'
    let a : Fin (2 ^ j) := ⟨2 ^ s * a'.val, by rw [← hpow_j]; exact Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)⟩
    unfold W_pref
    -- Restrict LHS to x with 2^s ∣ x.val ∧ x.val / 2^s < 2^(2^t)
    have hfilt : ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a), S.p x =
        ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t)), S.p x := by
      symm
      apply Finset.sum_subset
      · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
      · intro x hx hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hnot
        dsimp [S, shiftPMF]
        split_ifs with h
        · exfalso; exact hnot ⟨hx, h⟩
        · rfl
    rw [hfilt]
    apply Finset.sum_bij (fun x hx => ⟨x.val / 2 ^ s, (Finset.mem_filter.mp hx).2.2.2⟩)
    · intro x hx
      have h := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, prefMod]
      have hpref : x.val % 2 ^ j = 2 ^ s * a'.val := congrArg Fin.val h.1
      rw [← hpow_j, ← Nat.mul_div_cancel' h.2.1, Nat.mul_mod_mul_left] at hpref
      exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos s) hpref
    · intro x hx y hy heq
      have hxd := (Finset.mem_filter.mp hx).2.2.1
      have hyd := (Finset.mem_filter.mp hy).2.2.1
      have hdiv : x.val / 2 ^ s = y.val / 2 ^ s := congrArg Fin.val heq
      apply Fin.ext; rw [← Nat.mul_div_cancel' hxd, ← Nat.mul_div_cancel' hyd, hdiv]
    · intro z hz
      have hlt : 2 ^ s * z.val < 2 ^ k := by
        calc 2 ^ s * z.val < 2 ^ s * 2 ^ (2 ^ t) := Nat.mul_lt_mul_of_pos_left z.isLt (Nat.two_pow_pos s)
          _ = 2 ^ (s + 2 ^ t) := (pow_add 2 s (2 ^ t)).symm
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hst
      have hz_pref : z.val % 2 ^ (j - s) = a'.val := congrArg Fin.val (Finset.mem_filter.mp hz).2
      refine ⟨⟨2 ^ s * z.val, hlt⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, Nat.dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)]; exact z.isLt⟩
        apply Fin.ext; dsimp [prefMod, a]; rw [← hpow_j, Nat.mul_mod_mul_left, hz_pref]
      · apply Fin.ext; dsimp only; exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)
    · intro x hx
      have h := (Finset.mem_filter.mp hx).2.2
      dsimp [S, shiftPMF, Z]; simp [h]
  have hW1_eq : ∀ a' : Fin (2 ^ (j - s)),
      W_bit1 S j ⟨2 ^ s * a'.val, by rw [← hpow_j]; exact Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)⟩ =
      W_bit1 Z (j - s) a' := by
    intro a'
    let a : Fin (2 ^ j) := ⟨2 ^ s * a'.val, by rw [← hpow_j]; exact Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)⟩
    unfold W_bit1
    have hfilt : ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = true), S.p x =
        ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => (prefMod k j x = a ∧ bitAt k j x = true) ∧ 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t)), S.p x := by
      symm
      apply Finset.sum_subset
      · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
      · intro x hx hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hnot
        dsimp [S, shiftPMF]
        split_ifs with h
        · exfalso; exact hnot ⟨hx, h⟩
        · rfl
    rw [hfilt]
    apply Finset.sum_bij (fun x hx => ⟨x.val / 2 ^ s, (Finset.mem_filter.mp hx).2.2.2⟩)
    · intro x hx
      have h := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · apply Fin.ext; dsimp [prefMod]
        have hpref : x.val % 2 ^ j = 2 ^ s * a'.val := congrArg Fin.val h.1.1
        rw [← hpow_j, ← Nat.mul_div_cancel' h.2.1, Nat.mul_mod_mul_left] at hpref
        exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos s) hpref
      · have hbit := h.1.2
        simp only [bitAt] at hbit ⊢
        rw [← hpow_j] at hbit
        rw [Nat.div_div_eq_div_mul]
        exact hbit
    · intro x hx y hy heq
      have hxd := (Finset.mem_filter.mp hx).2.2.1
      have hyd := (Finset.mem_filter.mp hy).2.2.1
      have hdiv : x.val / 2 ^ s = y.val / 2 ^ s := congrArg Fin.val heq
      apply Fin.ext; rw [← Nat.mul_div_cancel' hxd, ← Nat.mul_div_cancel' hyd, hdiv]
    · intro z hz
      have hlt : 2 ^ s * z.val < 2 ^ k := by
        calc 2 ^ s * z.val < 2 ^ s * 2 ^ (2 ^ t) := Nat.mul_lt_mul_of_pos_left z.isLt (Nat.two_pow_pos s)
          _ = 2 ^ (s + 2 ^ t) := (pow_add 2 s (2 ^ t)).symm
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hst
      have hz_mem := (Finset.mem_filter.mp hz).2
      have hz_pref : z.val % 2 ^ (j - s) = a'.val := congrArg Fin.val hz_mem.1
      refine ⟨⟨2 ^ s * z.val, hlt⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨?_, ?_⟩, Nat.dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)]; exact z.isLt⟩
        · apply Fin.ext; dsimp [prefMod, a]; rw [← hpow_j, Nat.mul_mod_mul_left, hz_pref]
        · have hbit := hz_mem.2
          simp only [bitAt] at hbit ⊢
          rw [← hpow_j, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos s)]
          exact hbit
      · apply Fin.ext; dsimp only; exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)
    · intro x hx
      have h := (Finset.mem_filter.mp hx).2.2
      dsimp [S, shiftPMF, Z]; simp [h]
  -- Now sum over a : Fin (2^j), restricting to 2^s ∣ a.val
  unfold condBitEnt
  have hfilt_a : (∑ a : Fin (2 ^ j), W_pref S j a * Real.binEntropy (q_bit S j a)) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (2 ^ j) => 2 ^ s ∣ a.val),
        W_pref S j a * Real.binEntropy (q_bit S j a) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    rw [hW_zero a hnot, zero_mul]
  rw [hfilt_a]
  apply Finset.sum_bij (fun a ha => ⟨a.val / 2 ^ s, by
      have ha_lt : a.val < 2 ^ s * 2 ^ (j - s) := by rw [hpow_j]; exact a.isLt
      exact Nat.div_lt_of_lt_mul ha_lt⟩)
  · intro _ _; exact Finset.mem_univ _
  · intro a ha b hb heq
    have had := (Finset.mem_filter.mp ha).2
    have hbd := (Finset.mem_filter.mp hb).2
    have hdiv : a.val / 2 ^ s = b.val / 2 ^ s := congrArg Fin.val heq
    apply Fin.ext; rw [← Nat.mul_div_cancel' had, ← Nat.mul_div_cancel' hbd, hdiv]
  · intro a' _
    refine ⟨⟨2 ^ s * a'.val, by rw [← hpow_j]; exact Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)⟩, ?_, ?_⟩
    · simp [Nat.dvd_mul_right]
    · apply Fin.ext; dsimp only; exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)
  · intro a ha
    have had := (Finset.mem_filter.mp ha).2
    let a' : Fin (2 ^ (j - s)) := ⟨a.val / 2 ^ s, by
      have ha_lt : a.val < 2 ^ s * 2 ^ (j - s) := by rw [hpow_j]; exact a.isLt
      exact Nat.div_lt_of_lt_mul ha_lt⟩
    have ha_eq : a = ⟨2 ^ s * a'.val, by rw [← hpow_j]; exact Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)⟩ := by
      apply Fin.ext; dsimp [a']; exact (Nat.mul_div_cancel' had).symm
    rw [ha_eq]
    dsimp [q_bit]
    rw [hW_eq a', hW1_eq a']
    have hdiv : (⟨2 ^ s * a'.val / 2 ^ s, by
        have ha_lt : 2 ^ s * a'.val < 2 ^ s * 2 ^ (j - s) := Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)
        exact Nat.div_lt_of_lt_mul ha_lt⟩ : Fin (2 ^ (j - s))) = a' :=
      Fin.ext (Nat.mul_div_cancel_left _ (Nat.two_pow_pos s))
    rw [hdiv]

end Erdos18

#print axioms Erdos18.Hnat_Z_pmf
#print axioms Erdos18.condBitEnt_shiftPMF

/-! ## Part 3: 2-Sided Dyadic Shift Mixture `Y_pmf`, Automorphism Invariance & Lemma 3 -/

namespace Erdos18

open Finset Nat Real

/-- Membership in the 2-sided dyadic shift set `S_t` for modulus `2^k`. -/
def inStCov (k t s : ℕ) : Prop :=
  s ≤ k - 2 ^ t ∧ (s < 2 ^ (t + 1) ∨ k < s + 3 * 2 ^ t)

instance (k t s : ℕ) : Decidable (inStCov k t s) :=
  inferInstanceAs (Decidable (s ≤ k - 2 ^ t ∧ (s < 2 ^ (t + 1) ∨ k < s + 3 * 2 ^ t)))

/-- The finite shift set `S_t` as a `Finset ℕ`. -/
def shiftSet (k t : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun s => inStCov k t s)

lemma mem_shiftSet (k t s : ℕ) : s ∈ shiftSet k t ↔ s ≤ k ∧ inStCov k t s := by
  unfold shiftSet
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

lemma shiftSet_nonempty {k t : ℕ} (ht : 2 ^ t ≤ k) : (shiftSet k t).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_shiftSet]
  exact ⟨by omega, by omega, Or.inl (Nat.two_pow_pos (t + 1))⟩

lemma shiftSet_card_le (k t : ℕ) : (shiftSet k t).card ≤ 4 * 2 ^ t := by
  have hsub : shiftSet k t ⊆ Finset.range (2 ^ (t + 1)) ∪ Finset.Icc (k - 3 * 2 ^ t + 1) (k - 2 ^ t) := by
    intro s hs
    rw [mem_shiftSet] at hs
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
    rcases hs with ⟨_, hle, hlt | hgt⟩
    · exact Or.inl hlt
    · by_cases hs0 : s = 0
      · subst hs0; exact Or.inl (Nat.two_pow_pos (t + 1))
      · exact Or.inr ⟨by omega, hle⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.range (2 ^ (t + 1))) (Finset.Icc (k - 3 * 2 ^ t + 1) (k - 2 ^ t))
  rw [Finset.card_range, Nat.card_Icc] at h2
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ, mul_comm]
  omega

lemma shiftSet_coverage (k j : ℕ) (hk : 2 ≤ k) (hj : j < k) :
    let m_j := min (j + 1) (k - j)
    let t_star := Nat.log2 m_j
    2 ^ t_star ≤ k ∧
    t_star ≤ Nat.log2 ((k + 1) / 2) ∧
    ∀ s : ℕ, j + 1 - 2 ^ t_star ≤ s → s ≤ j → s ∈ shiftSet k t_star := by
  intro m_j t_star
  have hm_pos : 0 < m_j := by dsimp [m_j]; omega
  have hm_le_half : m_j ≤ (k + 1) / 2 := by dsimp [m_j]; omega
  have hpow_le : 2 ^ t_star ≤ m_j := (Nat.le_log2 (Nat.ne_of_gt hm_pos)).mp (le_refl _)
  have hlt_pow : m_j < 2 ^ (t_star + 1) := (Nat.log2_lt (Nat.ne_of_gt hm_pos)).mp (Nat.lt_succ_self _)
  have hpow_le_k : 2 ^ t_star ≤ k := by
    have : m_j ≤ k := by dsimp [m_j]; omega
    omega
  have ht_le_L : t_star ≤ Nat.log2 ((k + 1) / 2) := by
    rw [Nat.le_log2 (by omega)]
    exact le_trans hpow_le hm_le_half
  refine ⟨hpow_le_k, ht_le_L, ?_⟩
  intro s hs_lo hs_hi
  rw [mem_shiftSet]
  have hkj : m_j ≤ k - j := min_le_right _ _
  refine ⟨by omega, by omega, ?_⟩
  by_cases hcase : j + 1 ≤ k - j
  · left; have hmj_eq : m_j = j + 1 := min_eq_left hcase; omega
  · right
    have hmj_eq : m_j = k - j := min_eq_right (by omega)
    have hpow2 : 2 ^ (t_star + 1) = 2 * 2 ^ t_star := by rw [pow_succ, mul_comm]
    omega

/-- Number of dyadic scales `L(k) = Nat.log2 ((k + 1) / 2) + 1`. -/
def numScales (k : ℕ) : ℕ := Nat.log2 ((k + 1) / 2) + 1

lemma two_pow_le_k_of_lt_numScales {k t : ℕ} (hk : 2 ≤ k) (ht : t < numScales k) :
    2 ^ t ≤ k := by
  have hle : t ≤ Nat.log2 ((k + 1) / 2) := by unfold numScales at ht; omega
  have hpow : 2 ^ t ≤ (k + 1) / 2 := (Nat.le_log2 (by omega)).mp hle
  omega

/-- Index type for the 2-sided dyadic shift mixture: pairs `(t, s)` with `t < L(k)` and `s ∈ S_t`. -/
abbrev ShiftIdx (k : ℕ) := Σ t : Fin (numScales k), { s : ℕ // s ∈ shiftSet k t.val }

/-- Weight of `(t, s)` in the 2-sided dyadic shift mixture: `1 / (L(k) * |S_t|)`. -/
noncomputable def shiftWeight (k : ℕ) (idx : ShiftIdx k) : ℝ :=
  1 / ((numScales k : ℝ) * ((shiftSet k idx.1.val).card : ℝ))

lemma shiftWeight_nonneg (k : ℕ) (idx : ShiftIdx k) : 0 ≤ shiftWeight k idx := by
  unfold shiftWeight; positivity

lemma shiftWeight_sum_one {k : ℕ} (hk : 2 ≤ k) :
    ∑ idx : ShiftIdx k, shiftWeight k idx = 1 := by
  rw [Fintype.sum_sigma]
  have hinner : ∀ t : Fin (numScales k),
      (∑ s : { s : ℕ // s ∈ shiftSet k t.val }, shiftWeight k ⟨t, s⟩) = 1 / (numScales k : ℝ) := by
    intro t
    have hne : (shiftSet k t.val).Nonempty := shiftSet_nonempty (two_pow_le_k_of_lt_numScales hk t.isLt)
    have hcard_pos : (0 : ℝ) < ((shiftSet k t.val).card : ℝ) := Nat.cast_pos.mpr hne.card_pos
    have hconst : ∀ s : { s : ℕ // s ∈ shiftSet k t.val },
        shiftWeight k ⟨t, s⟩ = 1 / ((numScales k : ℝ) * ((shiftSet k t.val).card : ℝ)) := fun _ => rfl
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    field_simp [hcard_pos.ne']
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hL_pos : (0 : ℝ) < (numScales k : ℝ) := by unfold numScales; positivity
  field_simp [hL_pos.ne']

/-- Component PMF at index `idx = ⟨t, s⟩`. -/
noncomputable def shiftPMF_at {k : ℕ} (hk : 2 ≤ k) (idx : ShiftIdx k) : PMF_Fin (2 ^ k) :=
  shiftPMF k idx.1.val idx.2.val (by
    have hmem := (mem_shiftSet k idx.1.val idx.2.val).mp idx.2.property
    have hpow := two_pow_le_k_of_lt_numScales hk idx.1.isLt
    have hle := hmem.2.1
    omega)

/-- The 2-sided dyadic shift distribution `Y_pmf k hk` on `Fin (2^k)`. -/
noncomputable def Y_pmf (k : ℕ) (hk : 2 ≤ k) : PMF_Fin (2 ^ k) :=
  mixPMF (shiftWeight k) (shiftWeight_nonneg k) (shiftWeight_sum_one hk) (shiftPMF_at hk)

/-- Untagged entropy contraction for `Y_pmf k hk` (Step 3 of Lemma 3). -/
theorem Hnat_conv_Y_sub_ge (k : ℕ) (hk : 2 ≤ k) (c1 : ℝ) (hc1 : 0 < c1)
    (hpref : ∀ m : ℕ, 1 ≤ m → c1 * (m : ℝ) / Real.log ((m : ℝ) + 2) ≤ 1 + (oddPrimeCounting (m / 2) : ℝ) / 2)
    (X : PMF_Fin (2 ^ k)) :
    let g := (c1 * Real.log 2) / Real.log ((k : ℝ) + 2)
    Hnat (convPMF (Nat.two_pow_pos k) X (Y_pmf k hk)) - Hnat X ≥
      (2 * g ^ 2 / (4 * (numScales k : ℝ))) * ((k : ℝ) * Real.log 2 - Hnat X) := by
  intro g
  have hN := Nat.two_pow_pos k
  have hmix : ∑ idx : ShiftIdx k, shiftWeight k idx * Hnat (convPMF hN X (shiftPMF_at hk idx)) ≤
      Hnat (convPMF hN X (Y_pmf k hk)) := by
    unfold Y_pmf
    rw [convPMF_mixPMF_right]
    exact Hnat_mixPMF_ge _ _ _ _
  have hsub_mix : Hnat (convPMF hN X (Y_pmf k hk)) - Hnat X ≥
      ∑ idx : ShiftIdx k, shiftWeight k idx * (Hnat (convPMF hN X (shiftPMF_at hk idx)) - Hnat X) := by
    have h1 : ∑ idx : ShiftIdx k, shiftWeight k idx * (Hnat (convPMF hN X (shiftPMF_at hk idx)) - Hnat X) =
        (∑ idx : ShiftIdx k, shiftWeight k idx * Hnat (convPMF hN X (shiftPMF_at hk idx))) - Hnat X := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, shiftWeight_sum_one hk, one_mul]
    linarith
  have hstep2 : ∑ idx : ShiftIdx k, shiftWeight k idx * (Hnat (convPMF hN X (shiftPMF_at hk idx)) - Hnat X) ≥
      2 * ∑ j : Fin k, (Real.log 2 - condBitEnt X j.val) *
        (∑ idx : ShiftIdx k, shiftWeight k idx * (condBitEnt (shiftPMF_at hk idx) j.val) ^ 2) := by
    have h1 : ∑ idx : ShiftIdx k, shiftWeight k idx * (Hnat (convPMF hN X (shiftPMF_at hk idx)) - Hnat X) ≥
        ∑ idx : ShiftIdx k, shiftWeight k idx *
          (2 * ∑ j : Fin k, (condBitEnt (shiftPMF_at hk idx) j.val) ^ 2 * (Real.log 2 - condBitEnt X j.val)) := by
      apply Finset.sum_le_sum
      intro idx _
      exact mul_le_mul_of_nonneg_left (Hnat_conv_sub_ge_bitwise X (shiftPMF_at hk idx)) (shiftWeight_nonneg k idx)
    refine le_trans ?_ h1
    apply le_of_eq
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro idx _; ring
  have hinner_lb : ∀ j : Fin k,
      g ^ 2 / (4 * (numScales k : ℝ)) ≤
        ∑ idx : ShiftIdx k, shiftWeight k idx * (condBitEnt (shiftPMF_at hk idx) j.val) ^ 2 := by
    intro j
    rcases shiftSet_coverage k j.val hk j.isLt with ⟨hpow_k, ht_le, hcov⟩
    set m_j := min (j.val + 1) (k - j.val)
    set t_star := Nat.log2 m_j
    have ht_lt : t_star < numScales k := by unfold numScales; omega
    let t_fin : Fin (numScales k) := ⟨t_star, ht_lt⟩
    rw [Fintype.sum_sigma]
    have hdrop_t : (∑ s : { s : ℕ // s ∈ shiftSet k t_fin.val },
        shiftWeight k ⟨t_fin, s⟩ * (condBitEnt (shiftPMF_at hk ⟨t_fin, s⟩) j.val) ^ 2) ≤
      ∑ t : Fin (numScales k), ∑ s : { s : ℕ // s ∈ shiftSet k t.val },
        shiftWeight k ⟨t, s⟩ * (condBitEnt (shiftPMF_at hk ⟨t, s⟩) j.val) ^ 2 := by
      exact Finset.single_le_sum (f := fun t : Fin (numScales k) =>
        ∑ s : { s : ℕ // s ∈ shiftSet k t.val },
          shiftWeight k ⟨t, s⟩ * (condBitEnt (shiftPMF_at hk ⟨t, s⟩) j.val) ^ 2)
        (fun t _ => Finset.sum_nonneg fun s _ =>
          mul_nonneg (shiftWeight_nonneg k ⟨t, s⟩) (sq_nonneg _)) (Finset.mem_univ t_fin)
    have hL_pos : (0 : ℝ) < (numScales k : ℝ) := by unfold numScales; positivity
    have hcard_le : ((shiftSet k t_star).card : ℝ) ≤ 4 * ((2 ^ t_star : ℕ) : ℝ) := by
      exact_mod_cast shiftSet_card_le k t_star
    have hcard_pos : (0 : ℝ) < ((shiftSet k t_star).card : ℝ) :=
      Nat.cast_pos.mpr (shiftSet_nonempty hpow_k).card_pos
    have hw_lb : ∀ s : { s : ℕ // s ∈ shiftSet k t_star },
        1 / (4 * (numScales k : ℝ) * ((2 ^ t_star : ℕ) : ℝ)) ≤ shiftWeight k ⟨t_fin, s⟩ := fun s => by
      unfold shiftWeight
      dsimp [t_fin]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2t_le_j1 : 2 ^ t_star ≤ j.val + 1 := by
      have hm_pos : 0 < m_j := by dsimp [m_j]; omega
      have hle : 2 ^ t_star ≤ m_j := (Nat.le_log2 (Nat.ne_of_gt hm_pos)).mp (le_refl _)
      have : m_j ≤ j.val + 1 := min_le_left _ _
      omega
    have hsum_i : ∑ i : Fin (2 ^ t_star),
        (1 / (4 * (numScales k : ℝ) * ((2 ^ t_star : ℕ) : ℝ))) *
          (condBitEnt (Z_pmf (2 ^ t_star) Nat.one_le_two_pow) i.val) ^ 2 ≤ ∑ s : { s : ℕ // s ∈ shiftSet k t_fin.val }, shiftWeight k ⟨t_fin, s⟩ * (condBitEnt (shiftPMF_at hk ⟨t_fin, s⟩) j.val) ^ 2 := by
      let f : Fin (2 ^ t_star) → { s : ℕ // s ∈ shiftSet k t_star } :=
        fun i => ⟨j.val - i.val, hcov (j.val - i.val) (by omega) (by omega)⟩
      have hf_inj : Function.Injective f := by
        intro i1 i2 heq
        have hval : j.val - i1.val = j.val - i2.val := congrArg Subtype.val heq
        apply Fin.ext; omega
      have h1 : ∑ i : Fin (2 ^ t_star),
          (1 / (4 * (numScales k : ℝ) * ((2 ^ t_star : ℕ) : ℝ))) *
            (condBitEnt (Z_pmf (2 ^ t_star) Nat.one_le_two_pow) i.val) ^ 2 ≤
          ∑ i : Fin (2 ^ t_star),
            shiftWeight k ⟨t_fin, f i⟩ * (condBitEnt (shiftPMF_at hk ⟨t_fin, f i⟩) j.val) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hbit_eq : condBitEnt (shiftPMF_at hk ⟨t_fin, f i⟩) j.val =
            condBitEnt (Z_pmf (2 ^ t_star) Nat.one_le_two_pow) i.val := by
          unfold shiftPMF_at
          have hsub_eq : j.val - (f i).val = i.val := by dsimp [f]; omega
          rw [condBitEnt_shiftPMF k t_star (f i).val j.val _ (by dsimp [f]; omega) (by omega), hsub_eq]
        rw [hbit_eq]
        exact mul_le_mul_of_nonneg_right (hw_lb (f i)) (sq_nonneg _)
      refine le_trans h1 ?_
      let G : { s : ℕ // s ∈ shiftSet k t_fin.val } → ℝ := fun s =>
        shiftWeight k ⟨t_fin, s⟩ * (condBitEnt (shiftPMF_at hk ⟨t_fin, s⟩) j.val) ^ 2
      change ∑ i : Fin (2 ^ t_star), G (f i) ≤ ∑ s : { s : ℕ // s ∈ shiftSet k t_fin.val }, G s
      rw [← Finset.sum_image (f := G) (g := f) (fun _ _ _ _ h => hf_inj h)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro s _ _; exact mul_nonneg (shiftWeight_nonneg k ⟨t_fin, s⟩) (sq_nonneg _)
    have hcs : g ^ 2 * ((2 ^ t_star : ℕ) : ℝ) ≤
        ∑ i : Fin (2 ^ t_star), (condBitEnt (Z_pmf (2 ^ t_star) Nat.one_le_two_pow) i.val) ^ 2 := by
      have hsq := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin (2 ^ t_star))))
        (f := fun _ => (1 : ℝ))
        (g := fun i => condBitEnt (Z_pmf (2 ^ t_star) Nat.one_le_two_pow) i.val)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsq
      rw [← Hnat_eq_sum_condBitEnt (Z_pmf (2 ^ t_star) Nat.one_le_two_pow)] at hsq
      have hH_lb : g * ((2 ^ t_star : ℕ) : ℝ) ≤ Hnat (Z_pmf (2 ^ t_star) Nat.one_le_two_pow) := by
        rw [Hnat_Z_pmf]
        have hpr := hpref (2 ^ t_star) Nat.one_le_two_pow
        have hlog_le : Real.log (((2 ^ t_star : ℕ) : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (by omega : 2 ^ t_star + 2 ≤ k + 2))
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hlog_t_pos : 0 < Real.log (((2 ^ t_star : ℕ) : ℝ) + 2) :=
          Real.log_pos (by linarith [show (1 : ℝ) ≤ ((2 ^ t_star : ℕ) : ℝ) by exact_mod_cast Nat.one_le_two_pow])
        have hg_le : c1 * ((2 ^ t_star : ℕ) : ℝ) / Real.log ((k : ℝ) + 2) ≤
            c1 * ((2 ^ t_star : ℕ) : ℝ) / Real.log (((2 ^ t_star : ℕ) : ℝ) + 2) :=
          div_le_div_of_nonneg_left (by positivity) hlog_t_pos hlog_le
        have hmul := mul_le_mul_of_nonneg_right (le_trans hg_le hpr) hlog2_pos.le
        refine le_trans ?_ hmul
        dsimp [g]; ring_nf; exact le_rfl
      have hg_nonneg : 0 ≤ g * ((2 ^ t_star : ℕ) : ℝ) := by
        have : 0 < Real.log ((k : ℝ) + 2) := Real.log_pos (by linarith [show (2 : ℝ) ≤ k by exact_mod_cast hk])
        have : 0 < Real.log 2 := Real.log_pos (by norm_num)
        dsimp [g]; positivity
      have hsq2 : (g * ((2 ^ t_star : ℕ) : ℝ)) ^ 2 ≤ (Hnat (Z_pmf (2 ^ t_star) Nat.one_le_two_pow)) ^ 2 :=
        sq_le_sq' (by linarith) hH_lb
      have h2t_pos : (0 : ℝ) < ((2 ^ t_star : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.two_pow_pos t_star)
      have hcomb : g ^ 2 * ((2 ^ t_star : ℕ) : ℝ) ^ 2 ≤
          ((2 ^ t_star : ℕ) : ℝ) * ∑ i : Fin (2 ^ t_star), (condBitEnt (Z_pmf (2 ^ t_star) Nat.one_le_two_pow) i.val) ^ 2 := by
        nlinarith
      nlinarith
    have hfinal_i : g ^ 2 / (4 * (numScales k : ℝ)) ≤
        ∑ i : Fin (2 ^ t_star),
          (1 / (4 * (numScales k : ℝ) * ((2 ^ t_star : ℕ) : ℝ))) *
            (condBitEnt (Z_pmf (2 ^ t_star) Nat.one_le_two_pow) i.val) ^ 2 := by
      rw [← Finset.mul_sum]
      have hmul := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 1 / (4 * (numScales k : ℝ) * ((2 ^ t_star : ℕ) : ℝ)))
      refine le_trans ?_ hmul
      have h2t_ne : ((2 ^ t_star : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.two_pow_pos t_star)).ne'
      field_simp [hL_pos.ne', h2t_ne]
      exact le_rfl
    exact le_trans hfinal_i (le_trans hsum_i hdrop_t)
  have hdef_sum : (k : ℝ) * Real.log 2 - Hnat X = ∑ j : Fin k, (Real.log 2 - condBitEnt X j.val) := by
    rw [Hnat_eq_sum_condBitEnt X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hstep3 : 2 * ∑ j : Fin k, (Real.log 2 - condBitEnt X j.val) * (g ^ 2 / (4 * (numScales k : ℝ))) ≤
      2 * ∑ j : Fin k, (Real.log 2 - condBitEnt X j.val) *
        (∑ idx : ShiftIdx k, shiftWeight k idx * (condBitEnt (shiftPMF_at hk idx) j.val) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum; intro j _
    have hdef_nn : 0 ≤ Real.log 2 - condBitEnt X j.val := by
      have hle : condBitEnt X j.val ≤ ∑ a : Fin (2 ^ j.val), W_pref X j.val a * Real.log 2 := by
        unfold condBitEnt
        apply Finset.sum_le_sum; intro a _
        exact mul_le_mul_of_nonneg_left (Real.binEntropy_le_log_two (p := q_bit X j.val a)) (W_pref_nonneg X j.val a)
      rw [← Finset.sum_mul, W_pref_sum_one X j.val, one_mul] at hle
      linarith
    exact mul_le_mul_of_nonneg_left (hinner_lb j) hdef_nn
  have hsimp : 2 * ∑ j : Fin k, (Real.log 2 - condBitEnt X j.val) * (g ^ 2 / (4 * (numScales k : ℝ))) =
      (2 * g ^ 2 / (4 * (numScales k : ℝ))) * ((k : ℝ) * Real.log 2 - Hnat X) := by
    rw [hdef_sum, ← Finset.sum_mul]; ring
  linarith

/-- Modular inverse of odd `q` modulo `2^k`. -/
noncomputable def oddInvMod (k q : ℕ) (hq : Odd q) : ℕ :=
  letI : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
  let hcop : Nat.Coprime q (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hq)
  ((ZMod.unitOfCoprime q hcop)⁻¹ : (ZMod (2 ^ k))ˣ).val.val

lemma mul_oddInvMod_mod (k q : ℕ) (hq : Odd q) :
    (q * oddInvMod k q hq) % 2 ^ k = 1 % 2 ^ k := by
  have : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
  have hcop : Nat.Coprime q (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hq)
  let u : (ZMod (2 ^ k))ˣ := ZMod.unitOfCoprime q hcop
  have hu : (u : ZMod (2 ^ k)) * ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) = 1 := by
    exact_mod_cast u.mul_inv
  have hcast : ((q * oddInvMod k q hq : ℕ) : ZMod (2 ^ k)) = 1 := by
    rw [Nat.cast_mul]
    have hq_eq : (q : ZMod (2 ^ k)) = (u : ZMod (2 ^ k)) := (ZMod.coe_unitOfCoprime q hcop).symm
    have hinv_eq : (oddInvMod k q hq : ZMod (2 ^ k)) = ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) :=
      ZMod.natCast_zmod_val _
    rw [hq_eq, hinv_eq, hu]
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast, show (1 : ZMod (2 ^ k)) = ((1 : ℕ) : ZMod (2 ^ k)) from Nat.cast_one.symm, ZMod.val_natCast] at hval
  exact hval

/-- Group automorphism `x ↦ (q * x) % 2^k` on `Fin (2^k)` for odd `q`. -/
noncomputable def mulModEquiv (k q : ℕ) (hq : Odd q) : Fin (2 ^ k) ≃ Fin (2 ^ k) where
  toFun x := ⟨(q * x.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  invFun y := ⟨(oddInvMod k q hq * y.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  left_inv x := by
    apply Fin.ext; dsimp only
    rw [Nat.mul_mod_mod, ← mul_assoc, mul_comm (oddInvMod k q hq) q, Nat.mul_mod, mul_oddInvMod_mod,
        ← Nat.mul_mod, one_mul, Nat.mod_eq_of_lt x.isLt]
  right_inv y := by
    apply Fin.ext; dsimp only
    rw [Nat.mul_mod_mod, ← mul_assoc, Nat.mul_mod, mul_oddInvMod_mod,
        ← Nat.mul_mod, one_mul, Nat.mod_eq_of_lt y.isLt]

lemma mulModEquiv_apply (k q : ℕ) (hq : Odd q) (x : Fin (2 ^ k)) :
    (mulModEquiv k q hq x).val = (q * x.val) % 2 ^ k := rfl

lemma convPMF_pushforward_mulMod (k q : ℕ) (hq : Odd q) (X Y : PMF_Fin (2 ^ k)) :
    convPMF (Nat.two_pow_pos k) (pushforwardEquiv (mulModEquiv k q hq) X)
      (pushforwardEquiv (mulModEquiv k q hq) Y) =
    pushforwardEquiv (mulModEquiv k q hq) (convPMF (Nat.two_pow_pos k) X Y) := by
  let e := mulModEquiv k q hq
  let hN := Nat.two_pow_pos k
  have hsub : ∀ u a : Fin (2 ^ k), e.symm (subModFin hN u a) = subModFin hN (e.symm u) (e.symm a) := by
    intro u a
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    have hadd_e : ∀ x y : Fin (2 ^ k),
        ((e x).val + (e y).val) % 2 ^ k = (e ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩).val := by
      intro x y
      rw [mulModEquiv_apply, mulModEquiv_apply, mulModEquiv_apply]
      dsimp only
      rw [← Nat.add_mod, ← Nat.mul_add, Nat.mul_mod_mod]
    have h1 := hadd_e (e.symm a) (subModFin hN (e.symm u) (e.symm a))
    rw [Equiv.apply_symm_apply] at h1
    have hsum_eq : (⟨((e.symm a).val + (subModFin hN (e.symm u) (e.symm a)).val) % 2 ^ k, Nat.mod_lt _ hN⟩ : Fin (2 ^ k)) = e.symm u := by
      apply Fin.ext; exact add_subModFin_mod hN (e.symm u) (e.symm a)
    rw [hsum_eq, Equiv.apply_symm_apply] at h1
    have h2 := add_subModFin_mod hN u a
    have ha := a.isLt; have hu := u.isLt
    have hlt1 := (e (subModFin hN (e.symm u) (e.symm a))).isLt
    have hlt2 := (subModFin hN u a).isLt
    by_cases hc1 : a.val + (e (subModFin hN (e.symm u) (e.symm a))).val < 2 ^ k <;>
    by_cases hc2 : a.val + (subModFin hN u a).val < 2 ^ k
    · rw [Nat.mod_eq_of_lt hc1] at h1; rw [Nat.mod_eq_of_lt hc2] at h2; omega
    · rw [Nat.mod_eq_of_lt hc1] at h1
      have : (a.val + (subModFin hN u a).val) % 2 ^ k = a.val + (subModFin hN u a).val - 2 ^ k := by
        calc (a.val + (subModFin hN u a).val) % 2 ^ k = ((a.val + (subModFin hN u a).val - 2 ^ k) + 2 ^ k) % 2 ^ k := by congr 1; omega
          _ = (a.val + (subModFin hN u a).val - 2 ^ k) % 2 ^ k := Nat.add_mod_right _ _
          _ = a.val + (subModFin hN u a).val - 2 ^ k := Nat.mod_eq_of_lt (by omega)
      omega
    · rw [Nat.mod_eq_of_lt hc2] at h2
      have : (a.val + (e (subModFin hN (e.symm u) (e.symm a))).val) % 2 ^ k =
          a.val + (e (subModFin hN (e.symm u) (e.symm a))).val - 2 ^ k := by
        calc (a.val + (e (subModFin hN (e.symm u) (e.symm a))).val) % 2 ^ k =
              ((a.val + (e (subModFin hN (e.symm u) (e.symm a))).val - 2 ^ k) + 2 ^ k) % 2 ^ k := by congr 1; omega
          _ = (a.val + (e (subModFin hN (e.symm u) (e.symm a))).val - 2 ^ k) % 2 ^ k := Nat.add_mod_right _ _
          _ = a.val + (e (subModFin hN (e.symm u) (e.symm a))).val - 2 ^ k := Nat.mod_eq_of_lt (by omega)
      omega
    · have h3 : (a.val + (e (subModFin hN (e.symm u) (e.symm a))).val) % 2 ^ k =
          a.val + (e (subModFin hN (e.symm u) (e.symm a))).val - 2 ^ k := by
        calc (a.val + (e (subModFin hN (e.symm u) (e.symm a))).val) % 2 ^ k =
              ((a.val + (e (subModFin hN (e.symm u) (e.symm a))).val - 2 ^ k) + 2 ^ k) % 2 ^ k := by congr 1; omega
          _ = (a.val + (e (subModFin hN (e.symm u) (e.symm a))).val - 2 ^ k) % 2 ^ k := Nat.add_mod_right _ _
          _ = a.val + (e (subModFin hN (e.symm u) (e.symm a))).val - 2 ^ k := Nat.mod_eq_of_lt (by omega)
      have h4 : (a.val + (subModFin hN u a).val) % 2 ^ k = a.val + (subModFin hN u a).val - 2 ^ k := by
        calc (a.val + (subModFin hN u a).val) % 2 ^ k = ((a.val + (subModFin hN u a).val - 2 ^ k) + 2 ^ k) % 2 ^ k := by congr 1; omega
          _ = (a.val + (subModFin hN u a).val - 2 ^ k) % 2 ^ k := Nat.add_mod_right _ _
          _ = a.val + (subModFin hN u a).val - 2 ^ k := Nat.mod_eq_of_lt (by omega)
      omega
  ext u
  dsimp [convPMF, pushforwardEquiv]
  rw [← Equiv.sum_comp e.symm (fun b => X.p b * Y.p (subModFin hN (e.symm u) b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [hsub u a]

/-- Prime-tagged entropy contraction via group automorphism (Step 4 of Lemma 3). -/
theorem Hnat_conv_mulMod_sub_ge (k q : ℕ) (hk : 2 ≤ k) (hq : Odd q) (c1 : ℝ) (hc1 : 0 < c1)
    (hpref : ∀ m : ℕ, 1 ≤ m → c1 * (m : ℝ) / Real.log ((m : ℝ) + 2) ≤ 1 + (oddPrimeCounting (m / 2) : ℝ) / 2)
    (X : PMF_Fin (2 ^ k)) :
    let g := (c1 * Real.log 2) / Real.log ((k : ℝ) + 2)
    Hnat (convPMF (Nat.two_pow_pos k) X (pushforwardEquiv (mulModEquiv k q hq) (Y_pmf k hk))) - Hnat X ≥
      (2 * g ^ 2 / (4 * (numScales k : ℝ))) * ((k : ℝ) * Real.log 2 - Hnat X) := by
  let e := mulModEquiv k q hq
  let X' := pushforwardEquiv e.symm X
  have hX_eq : pushforwardEquiv e X' = X := by
    ext u; dsimp [pushforwardEquiv, X']; simp
  have hconv : convPMF (Nat.two_pow_pos k) X (pushforwardEquiv e (Y_pmf k hk)) =
      pushforwardEquiv e (convPMF (Nat.two_pow_pos k) X' (Y_pmf k hk)) := by
    conv_lhs => rw [← hX_eq]
    exact convPMF_pushforward_mulMod k q hq X' (Y_pmf k hk)
  rw [hconv, Hnat_pushforwardEquiv, ← Hnat_pushforwardEquiv e.symm X]
  exact Hnat_conv_Y_sub_ge k hk c1 hc1 hpref X'

end Erdos18

#print axioms Erdos18.Hnat_conv_Y_sub_ge
#print axioms Erdos18.Hnat_conv_mulMod_sub_ge

/-! ## Part 4: Iterated Contraction, Support Extraction & Parametric Mod-2^k Covering (Lemma 3) -/

namespace Erdos18

open Finset Nat Real

/-- Point mass `δ_0` on `Fin (2^k)`. -/
noncomputable def deltaZeroPMF (k : ℕ) : PMF_Fin (2 ^ k) where
  p x := if x.val = 0 then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_one := by
    rw [Fintype.sum_eq_single (⟨0, Nat.two_pow_pos k⟩ : Fin (2 ^ k))]
    · simp
    · intro x hx
      have hx0 : x.val ≠ 0 := fun h => hx (Fin.ext h)
      simp [hx0]

lemma Hnat_deltaZero (k : ℕ) : Hnat (deltaZeroPMF k) = 0 := by
  unfold Hnat deltaZeroPMF
  dsimp only
  rw [Fintype.sum_eq_single (⟨0, Nat.two_pow_pos k⟩ : Fin (2 ^ k))]
  · simp
  · intro x hx
    have hx0 : x.val ≠ 0 := fun h => hx (Fin.ext h)
    simp [hx0]

/-- Support of `convPMF`: every element in `suppFin (convPMF X Y)` is a sum mod `N` of elements in `suppFin X` and `suppFin Y`. -/
lemma mem_supp_convPMF {N : ℕ} (hN : 0 < N) (X Y : PMF_Fin N) {u : Fin N}
    (hu : u ∈ suppFin (convPMF hN X Y)) :
    ∃ a b : Fin N, a ∈ suppFin X ∧ b ∈ suppFin Y ∧ (a.val + b.val) % N = u.val := by
  unfold suppFin at hu; rw [Finset.mem_filter] at hu; have hu' : 0 < (convPMF hN X Y).p u := hu.2; dsimp only [convPMF] at hu'
  by_contra hnone
  push Not at hnone
  have hzero : ∀ a : Fin N, X.p a * Y.p (subModFin hN u a) = 0 := by
    intro a
    by_cases hXa : 0 < X.p a
    · have hYb : ¬ (0 < Y.p (subModFin hN u a)) := by
        intro hpos
        exact hnone a (subModFin hN u a) (by simp [suppFin, hXa]) (by simp [suppFin, hpos])
          (add_subModFin_mod hN u a)
      have hYb0 : Y.p (subModFin hN u a) = 0 := le_antisymm (not_lt.mp hYb) (Y.nonneg _)
      rw [hYb0, mul_zero]
    · have hXa0 : X.p a = 0 := le_antisymm (not_lt.mp hXa) (X.nonneg _)
      rw [hXa0, zero_mul]
  have hsum0 : ∑ a : Fin N, X.p a * Y.p (subModFin hN u a) = 0 :=
    Finset.sum_eq_zero fun a _ => hzero a
  linarith

/-- Every `y ∈ suppFin (Y_pmf k hk)` is either `0` or a positive divisor `d = 2^s * z` with
    `s < k`, `z ∣ oddPrimorial ((k+1)/4)`, `Odd z`, and `d < 2^k`. -/
lemma mem_supp_Y_pmf {k : ℕ} (hk : 2 ≤ k) {y : Fin (2 ^ k)} (hy : y ∈ suppFin (Y_pmf k hk)) :
    y.val = 0 ∨
    (0 < y.val ∧ y.val < 2 ^ k ∧ ¬ (2 ^ k ∣ y.val) ∧
      ∃ s z : ℕ, s < k ∧ z ∣ oddPrimorial ((k + 1) / 4) ∧ Odd z ∧ y.val = 2 ^ s * z) := by
  by_cases hy0 : y.val = 0
  · exact Or.inl hy0
  · right
    unfold suppFin at hy; rw [Finset.mem_filter] at hy; have hy' : 0 < (Y_pmf k hk).p y := hy.2; dsimp only [Y_pmf, mixPMF] at hy'
    -- Some component idx = ⟨t, s⟩ has positive probability at y
    have hex : ∃ idx : ShiftIdx k, 0 < (shiftPMF_at hk idx).p y := by
      by_contra hno
      push Not at hno
      have hzero : ∑ idx : ShiftIdx k, shiftWeight k idx * (shiftPMF_at hk idx).p y = 0 := by
        apply Finset.sum_eq_zero; intro idx _
        have h0 : (shiftPMF_at hk idx).p y = 0 := le_antisymm (hno idx) ((shiftPMF_at hk idx).nonneg y)
        rw [h0, mul_zero]
      linarith
    rcases hex with ⟨⟨t, ⟨s, hs⟩⟩, hpos⟩
    dsimp [shiftPMF_at, shiftPMF] at hpos
    split_ifs at hpos with hdiv
    · rcases hdiv with ⟨h2s_dvd, hlt_z⟩
      set z := y.val / 2 ^ s
      have hy_eq : y.val = 2 ^ s * z := (Nat.mul_div_cancel' h2s_dvd).symm
      have hz_ne0 : z ≠ 0 := by intro hz0; rw [hz0, mul_zero] at hy_eq; exact hy0 hy_eq
      dsimp [Z_pmf] at hpos
      rw [if_neg hz_ne0] at hpos
      split_ifs at hpos with hmem_div
      · have hz_dvd_t : z ∣ oddPrimorial (2 ^ t.val / 2) := Nat.dvd_of_mem_divisors hmem_div
        have h2t_le : 2 ^ t.val ≤ (k + 1) / 2 := by
          have hle : t.val ≤ Nat.log2 ((k + 1) / 2) := by
            have := t.isLt; unfold numScales at this; omega
          exact (Nat.le_log2 (by omega)).mp hle
        have hhalf : 2 ^ t.val / 2 ≤ (k + 1) / 4 := by omega
        have hz_dvd : z ∣ oddPrimorial ((k + 1) / 4) := by
          refine dvd_trans hz_dvd_t ?_
          unfold oddPrimorial
          apply Finset.prod_dvd_prod_of_subset
          intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨by omega, hp.2⟩
        have hz_odd : Odd z := (oddPrimorial_odd ((k + 1) / 4)).of_dvd_nat hz_dvd
        have hs_lt : s < k := by
          have hmem := (mem_shiftSet k t.val s).mp hs
          have hpow := Nat.one_le_two_pow (n := t.val)
          have hle := hmem.2.1
          omega
        have hndvd_2k : ¬ (2 ^ k ∣ y.val) := by
          intro h2k
          have hle := Nat.le_of_dvd (by omega) h2k
          omega
        exact ⟨by omega, y.isLt, hndvd_2k, s, z, hs_lt, hz_dvd, hz_odd, hy_eq⟩
      · linarith
    · linarith

/-- Iterated convolution of `r` prime-tagged copies of `Y_pmf k hk` starting from `δ_0`. -/
noncomputable def iterConv {k : ℕ} (hk : 2 ≤ k) (tags : List ℕ) (htags : ∀ q ∈ tags, Odd q) :
    PMF_Fin (2 ^ k) :=
  match tags with
  | [] => deltaZeroPMF k
  | q :: qs =>
    convPMF (Nat.two_pow_pos k)
      (iterConv hk qs (fun q' hq' => htags q' (List.mem_cons_of_mem q hq')))
      (pushforwardEquiv (mulModEquiv k q (htags q (List.mem_cons_self ..))) (Y_pmf k hk))

/-- Entropy deficit contraction across `iterConv`. -/
lemma iterConv_deficit_le {k : ℕ} (hk : 2 ≤ k) (c1 : ℝ) (hc1 : 0 < c1)
    (hpref : ∀ m : ℕ, 1 ≤ m → c1 * (m : ℝ) / Real.log ((m : ℝ) + 2) ≤ 1 + (oddPrimeCounting (m / 2) : ℝ) / 2)
    (tags : List ℕ) (htags : ∀ q ∈ tags, Odd q) :
    let g := (c1 * Real.log 2) / Real.log ((k : ℝ) + 2)
    let α := 2 * g ^ 2 / (4 * (numScales k : ℝ))
    (k : ℝ) * Real.log 2 - Hnat (iterConv hk tags htags) ≤
      Real.exp (-α * (tags.length : ℝ)) * ((k : ℝ) * Real.log 2) := by
  intro g α
  induction tags with
  | nil =>
    simp [iterConv, Hnat_deltaZero]
  | cons q qs ih =>
    have hq_odd : Odd q := htags q (List.mem_cons_self ..)
    have hqs_odd : ∀ q' ∈ qs, Odd q' := fun q' hq' => htags q' (List.mem_cons_of_mem q hq')
    let X := iterConv hk qs hqs_odd
    have hgain := Hnat_conv_mulMod_sub_ge k q hk hq_odd c1 hc1 hpref X
    have hstep : (k : ℝ) * Real.log 2 - Hnat (iterConv hk (q :: qs) htags) ≤
        (1 - α) * ((k : ℝ) * Real.log 2 - Hnat X) := by
      dsimp only [iterConv]
      dsimp only [α, g] at hgain ⊢
      linarith
    have hdef_nn : 0 ≤ (k : ℝ) * Real.log 2 - Hnat X := by
      have hH_le : Hnat X ≤ (k : ℝ) * Real.log 2 := by
        calc Hnat X ≤ Real.log ((suppFin X).card : ℝ) := Hnat_le_log_supp X
          _ ≤ Real.log ((2 ^ k : ℕ) : ℝ) := by
            apply Real.log_le_log
            · have hne : (suppFin X).Nonempty := by
                by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
                have h0 : ∀ x, X.p x = 0 := fun x => by
                  have hx : x ∉ suppFin X := by rw [h]; simp
                  simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
                  exact le_antisymm hx (X.nonneg x)
                have : ∑ x : Fin (2 ^ k), X.p x = 0 := Finset.sum_eq_zero fun x _ => h0 x
                linarith [X.sum_one]
              exact Nat.cast_pos.mpr hne.card_pos
            · exact_mod_cast (Finset.card_le_univ (suppFin X)).trans (by simp)
          _ = (k : ℝ) * Real.log 2 := by rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      linarith
    have h1_sub_le : 1 - α ≤ Real.exp (-α) := by
      have := Real.add_one_le_exp (-α)
      linarith
    have hih := ih hqs_odd
    have hexp_pos : 0 ≤ Real.exp (-α) := (Real.exp_pos _).le
    calc (k : ℝ) * Real.log 2 - Hnat (iterConv hk (q :: qs) htags)
        ≤ (1 - α) * ((k : ℝ) * Real.log 2 - Hnat X) := hstep
      _ ≤ Real.exp (-α) * ((k : ℝ) * Real.log 2 - Hnat X) :=
          mul_le_mul_of_nonneg_right h1_sub_le hdef_nn
      _ ≤ Real.exp (-α) * (Real.exp (-α * (qs.length : ℝ)) * ((k : ℝ) * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hih hexp_pos
      _ = Real.exp (-α * (((q :: qs).length : ℕ) : ℝ)) * ((k : ℝ) * Real.log 2) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Support extraction for `iterConv`: every `u ∈ suppFin (iterConv hk tags htags)` is congruent mod `2^k`
    to the sum of a `Finset ℕ` of at most `tags.length` strictly distinct positive divisors of
    `2^k * oddPrimorial Q_max`, each tagged by a distinct prime from `tags`. -/
lemma iterConv_supp_representable {k Q_max : ℕ} (hk : 2 ≤ k)
    (tags : List ℕ) (hnodup : tags.Nodup)
    (hprimes : ∀ q ∈ tags, q.Prime ∧ (k + 1) / 4 < q ∧ q ≤ Q_max)
    (htags : ∀ q ∈ tags, Odd q) :
    ∀ u ∈ suppFin (iterConv hk tags htags),
      ∃ S : Finset ℕ,
        S.card ≤ tags.length ∧
        (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ k * oddPrimorial Q_max ∧ ¬ (2 ^ k ∣ d) ∧ d < Q_max * 2 ^ k ∧
          ∃ q ∈ tags, q ∣ d ∧ ∀ q' : ℕ, q'.Prime → 3 ≤ q' → (k + 1) / 4 < q' → q' ∣ d → q' = q) ∧
        S.sum id % 2 ^ k = u.val := by
  induction tags with
  | nil =>
    intro u hu
    unfold suppFin at hu; rw [Finset.mem_filter] at hu
    have hu' : 0 < (deltaZeroPMF k).p u := hu.2
    dsimp only [deltaZeroPMF] at hu'
    have hu0 : u.val = 0 := by by_contra h; rw [if_neg h] at hu'; linarith
    refine ⟨∅, by simp, by simp, ?_⟩
    simp [hu0]
  | cons q qs ih =>
    intro u hu
    rw [List.nodup_cons] at hnodup
    have hq_info := hprimes q (List.mem_cons_self ..)
    have hqs_primes : ∀ q' ∈ qs, q'.Prime ∧ (k + 1) / 4 < q' ∧ q' ≤ Q_max :=
      fun q' hq' => hprimes q' (List.mem_cons_of_mem q hq')
    have hqs_odd : ∀ q' ∈ qs, Odd q' := fun q' hq' => htags q' (List.mem_cons_of_mem q hq')
    rcases mem_supp_convPMF (Nat.two_pow_pos k) _ _ hu with ⟨a, b, ha, hb, hab⟩
    rcases ih hnodup.2 hqs_primes hqs_odd a ha with ⟨S_a, hSa_card, hSa_prop, hSa_sum⟩
    -- Analyze b ∈ suppFin (pushforwardEquiv (mulModEquiv k q _) (Y_pmf k hk))
    let e := mulModEquiv k q (htags q (List.mem_cons_self ..))
    have hb' : e.symm b ∈ suppFin (Y_pmf k hk) := by
      unfold suppFin at hb ⊢; rw [Finset.mem_filter] at hb ⊢
      exact ⟨Finset.mem_univ _, hb.2⟩
    rcases mem_supp_Y_pmf hk hb' with hby0 | ⟨hby_pos, hby_lt, _, s, z, hs_lt, hz_dvd, hz_odd, hby_eq⟩
    · -- b = 0, so S_a already works!
      have hb0 : b.val = 0 := by
        have hbe : b = e (e.symm b) := (Equiv.apply_symm_apply e b).symm
        rw [hbe, mulModEquiv_apply, hby0, mul_zero, Nat.zero_mod]
      refine ⟨S_a, le_trans hSa_card (by simp), ?_, ?_⟩
      · intro d hd
        rcases hSa_prop d hd with ⟨h1, h2, h3, h4, q', hq'm, hq'd, hq'u⟩
        exact ⟨h1, h2, h3, h4, q', List.mem_cons_of_mem q hq'm, hq'd, hq'u⟩
      · rw [← hab, hb0, add_zero, Nat.mod_eq_of_lt a.isLt] at *
        exact hSa_sum
    · -- Nonzero divisor d_new = q * (e.symm b).val = q * 2^s * z
      let d_new := q * (e.symm b).val
      have hd_pos : 0 < d_new := Nat.mul_pos hq_info.1.pos hby_pos
      have hd_lt : d_new < Q_max * 2 ^ k := by
        calc d_new = q * (e.symm b).val := rfl
          _ ≤ Q_max * (e.symm b).val := Nat.mul_le_mul_right _ hq_info.2.2
          _ < Q_max * 2 ^ k := Nat.mul_lt_mul_of_pos_left hby_lt (by omega)
      have hd_dvd : d_new ∣ 2 ^ k * oddPrimorial Q_max := by
        -- d_new = 2^s * (q * z), with 2^s ∣ 2^k, q ∣ oddPrimorial Q_max, z ∣ oddPrimorial ((k+1)/4), coprime(q, z)
        have hq_ge3 : 3 ≤ q := by
          have := hq_info.1.two_le
          have hq_odd := htags q (List.mem_cons_self ..)
          have hne2 : q ≠ 2 := by intro h; subst h; exact (Nat.not_odd_iff_even.mpr even_two) hq_odd
          omega
        have hq_dvd_Q : q ∣ oddPrimorial Q_max := by
          unfold oddPrimorial
          exact Finset.dvd_prod_of_mem _ (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hq_info.1, hq_ge3⟩)
        have hz_dvd_Q : z ∣ oddPrimorial Q_max := by
          refine dvd_trans hz_dvd ?_
          unfold oddPrimorial
          apply Finset.prod_dvd_prod_of_subset
          intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨by omega, hp.2⟩
        have hq_ndvd_z : ¬ (q ∣ z) := by
          intro hqz
          have hq_dvd_P : q ∣ primorial ((k + 1) / 4) :=
            dvd_trans (dvd_trans hqz hz_dvd) (oddPrimorial_dvd_primorial _)
          have hq_le : q ≤ (k + 1) / 4 := (hq_info.1.dvd_primorial_iff).mp hq_dvd_P
          omega
        have hcop_qz : Nat.Coprime q z := (hq_info.1.coprime_iff_not_dvd).mpr hq_ndvd_z
        have hqz_dvd : q * z ∣ oddPrimorial Q_max := hcop_qz.mul_dvd_of_dvd_of_dvd hq_dvd_Q hz_dvd_Q
        have h2s_dvd : 2 ^ s ∣ 2 ^ k := Nat.pow_dvd_pow 2 hs_lt.le
        have hrew : d_new = 2 ^ s * (q * z) := by dsimp [d_new]; rw [hby_eq]; ring
        rw [hrew]
        exact Nat.mul_dvd_mul h2s_dvd hqz_dvd
      have hd_ndvd_2k : ¬ (2 ^ k ∣ d_new) := by
        intro h2k
        have hrew : d_new = 2 ^ s * (q * z) := by dsimp [d_new]; rw [hby_eq]; ring
        rw [hrew] at h2k
        have h2k_eq : 2 ^ k = 2 ^ s * 2 ^ (k - s) := by rw [← pow_add, Nat.add_sub_of_le hs_lt.le]
        rw [h2k_eq] at h2k
        have h2ks_dvd : 2 ^ (k - s) ∣ q * z := (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos s)).mp h2k
        have h2_dvd : 2 ∣ q * z := dvd_trans (dvd_pow_self 2 (by omega)) h2ks_dvd
        have hqz_odd : Odd (q * z) := (htags q (List.mem_cons_self ..)).mul hz_odd
        exact (Nat.not_even_iff_odd.mpr hqz_odd) (even_iff_two_dvd.mpr h2_dvd)
      have hd_uniq : ∀ q' : ℕ, q'.Prime → 3 ≤ q' → (k + 1) / 4 < q' → q' ∣ d_new → q' = q := by
        intro q' hq'_p hq'_ge3 hq'_gt hq'_dvd
        have hrew : d_new = q * (2 ^ s * z) := by dsimp [d_new]; rw [hby_eq]
        rw [hrew] at hq'_dvd
        rcases hq'_p.dvd_mul.mp hq'_dvd with h1 | h2
        · exact (Nat.prime_dvd_prime_iff_eq hq'_p hq_info.1).mp h1
        · rcases hq'_p.dvd_mul.mp h2 with h2a | h2b
          · have hq'_eq2 : q' = 2 := (Nat.prime_dvd_prime_iff_eq hq'_p Nat.prime_two).mp (hq'_p.dvd_of_dvd_pow h2a)
            omega
          · have hq'_P : q' ∣ primorial ((k + 1) / 4) :=
              dvd_trans (dvd_trans h2b hz_dvd) (oddPrimorial_dvd_primorial _)
            have hq'_le : q' ≤ (k + 1) / 4 := (hq'_p.dvd_primorial_iff).mp hq'_P
            omega
      have hd_notMem : d_new ∉ S_a := by
        intro hmem
        rcases hSa_prop d_new hmem with ⟨_, _, _, _, q', hq'm, _, hq'u⟩
        have hq_ge3 : 3 ≤ q := by
          have := hq_info.1.two_le
          have hq_odd := htags q (List.mem_cons_self ..)
          have hne2 : q ≠ 2 := by intro h; subst h; exact (Nat.not_odd_iff_even.mpr even_two) hq_odd
          omega
        have hqq' : q = q' := hq'u q hq_info.1 hq_ge3 hq_info.2.1 (Nat.dvd_mul_right q _)
        subst hqq'
        exact hnodup.1 hq'm
      refine ⟨insert d_new S_a, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hd_notMem]; simp only [List.length_cons]; omega
      · intro d hd
        rw [Finset.mem_insert] at hd
        rcases hd with rfl | hd_old
        · exact ⟨hd_pos, hd_dvd, hd_ndvd_2k, hd_lt, q, List.mem_cons_self .., Nat.dvd_mul_right q _, hd_uniq⟩
        · rcases hSa_prop d hd_old with ⟨h1, h2, h3, h4, q', hq'm, hq'd, hq'u⟩
          exact ⟨h1, h2, h3, h4, q', List.mem_cons_of_mem q hq'm, hq'd, hq'u⟩
      · rw [Finset.sum_insert hd_notMem, id_eq]
        have hb_val : b.val = d_new % 2 ^ k := by
          have hbe : b = e (e.symm b) := (Equiv.apply_symm_apply e b).symm
          rw [hbe, mulModEquiv_apply]
        rw [Nat.add_mod, ← hb_val, hSa_sum, add_comm, hab]


/-- Pigeonhole sumset covering on `Fin N`: if `N < A.card + B.card`, then `A + B = Fin N`. -/
lemma pigeonhole_finset_cover {N : ℕ} (hN : 0 < N) (A B : Finset (Fin N))
    (hgt : N < A.card + B.card) (x : Fin N) :
    ∃ a ∈ A, ∃ b ∈ B, (a.val + b.val) % N = x.val := by
  let f : Fin N → Fin N := fun b => subModFin hN x b
  have hf_inj : Function.Injective f := by
    intro b1 b2 heq
    have := congrArg f heq
    simpa [f, subModFin_involutive] using this
  let B' := B.image f
  have hB'_card : B'.card = B.card := Finset.card_image_of_injective B hf_inj
  have hnot_disj : ¬ Disjoint A B' := by
    intro hdisj
    have hcard : (A ∪ B').card = A.card + B'.card := Finset.card_union_of_disjoint hdisj
    have hle : (A ∪ B').card ≤ N := by
      simpa using Finset.card_le_univ (A ∪ B')
    omega
  rw [Finset.not_disjoint_iff] at hnot_disj
  rcases hnot_disj with ⟨a, haA, haB'⟩
  rw [Finset.mem_image] at haB'
  rcases haB' with ⟨b, hbB, hfb⟩
  refine ⟨a, haA, b, hbB, ?_⟩
  rw [← hfb, add_comm]
  exact add_subModFin_mod hN x b

/-- Lemma 3 (Parametric Mod-2^k Covering with `O((log k)^4)` Strictly Distinct Divisors). -/
theorem mod_two_pow_covering :
    ∃ C_cov : ℝ, 0 < C_cov ∧
      ∀ (k Q_max : ℕ), 2 ≤ k → 3 ≤ Q_max →
        let R := Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 4)
        2 * R ≤ oddPrimeCounting Q_max - oddPrimeCounting ((k + 1) / 4) →
        ∀ a : ℕ, ∃ S : Finset ℕ,
          S.card ≤ 2 * R ∧
          (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ k * oddPrimorial Q_max ∧ ¬ (2 ^ k ∣ d) ∧ d < Q_max * 2 ^ k) ∧
          S.sum id % 2 ^ k = a % 2 ^ k := by
  rcases prefix_entropy_rate_lower with ⟨c1, hc1, hpref⟩
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Choose C_cov = 24 / (c1 * log 2)^2 so that α * R ≥ log (2 * k) for all k ≥ 2
  refine ⟨24 / (c1 * Real.log 2) ^ 2, by positivity, ?_⟩
  intro k Q_max hk hQmax R hprimes_cnt a
  have hlogk_pos : 0 < Real.log ((k : ℝ) + 2) :=
    Real.log_pos (by linarith [show (2 : ℝ) ≤ k by exact_mod_cast hk])
  have hlogk_ge1 : (1 : ℝ) ≤ Real.log ((k : ℝ) + 2) := by
    have h4 : (4 : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ k + 2)
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    have hgt := Real.log_two_gt_d9
    linarith [Real.log_le_log (by norm_num) h4]
  -- Extract 2 * R distinct odd primes in ((k+1)/4, Q_max]
  let P_pool : Finset ℕ :=
    (Finset.range (Q_max + 1)).filter (fun p => p.Prime ∧ 3 ≤ p ∧ (k + 1) / 4 < p)
  have hpool_card : 2 * R ≤ P_pool.card := by
    have hsub : (Finset.range ((k + 1) / 4 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) ⊆
        (Finset.range (Q_max + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) := by
      by_cases hle : (k + 1) / 4 ≤ Q_max
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
      · -- If (k+1)/4 > Q_max then oddPrimeCounting Q_max ≤ oddPrimeCounting ((k+1)/4), so 2*R = 0, impossible!
        exfalso
        have hmono : oddPrimeCounting Q_max ≤ oddPrimeCounting ((k + 1) / 4) := by
          unfold oddPrimeCounting
          apply Finset.card_le_card
          intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
        have hR_pos : 0 < R := by
          dsimp [R]; exact Nat.ceil_pos.mpr (by positivity)
        omega
    have hsdiff : P_pool =
        ((Finset.range (Q_max + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)) \
        ((Finset.range ((k + 1) / 4 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)) := by
      ext p
      simp only [P_pool, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, fun h => by omega⟩
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        have hgt : (k + 1) / 4 < p := by by_contra hle; exact h4 ⟨by omega, h2, h3⟩
        exact ⟨h1, h2, h3, hgt⟩
    rw [hsdiff, Finset.card_sdiff_of_subset hsub]
    exact hprimes_cnt
  -- Convert P_pool to a list of length ≥ 2 * R with Nodup, take first R and next R
  let L_all : List ℕ := P_pool.toList
  have hL_nodup : L_all.Nodup := Finset.nodup_toList P_pool
  have hL_len : 2 * R ≤ L_all.length := by simpa [L_all] using hpool_card
  let tags1 : List ℕ := L_all.take R
  let tags2 : List ℕ := (L_all.drop R).take R
  have hlen1 : tags1.length = R := by simp [tags1, Nat.min_eq_left (by omega : R ≤ L_all.length)]
  have hlen2 : tags2.length = R := by
    simp [tags2, List.length_take, List.length_drop]; omega
  have hnodup1 : tags1.Nodup := hL_nodup.take
  have hnodup2 : tags2.Nodup := hL_nodup.drop.take
  have hdisj_tags : ∀ q ∈ tags1, q ∉ tags2 := by
    intro q hq1 hq2
    have hsplit : L_all = tags1 ++ L_all.drop R := (List.take_append_drop R L_all).symm
    have hnd := hL_nodup
    rw [hsplit, List.nodup_append] at hnd
    exact hnd.2.2 q hq1 q (List.mem_of_mem_take hq2) rfl
  have hmem_pool : ∀ q ∈ L_all, q.Prime ∧ 3 ≤ q ∧ (k + 1) / 4 < q ∧ q ≤ Q_max := by
    intro q hq
    have hm : q ∈ P_pool := Finset.mem_toList.mp hq
    simp only [P_pool, Finset.mem_filter, Finset.mem_range] at hm
    exact ⟨hm.2.1, hm.2.2.1, hm.2.2.2, by omega⟩
  have hprimes1 : ∀ q ∈ tags1, q.Prime ∧ (k + 1) / 4 < q ∧ q ≤ Q_max := fun q hq => by
    rcases hmem_pool q (List.mem_of_mem_take hq) with ⟨h1, _, h3, h4⟩; exact ⟨h1, h3, h4⟩
  have hprimes2 : ∀ q ∈ tags2, q.Prime ∧ (k + 1) / 4 < q ∧ q ≤ Q_max := fun q hq => by
    rcases hmem_pool q (List.mem_of_mem_drop (List.mem_of_mem_take hq)) with ⟨h1, _, h3, h4⟩; exact ⟨h1, h3, h4⟩
  have hodd1 : ∀ q ∈ tags1, Odd q := fun q hq => by
    rcases hmem_pool q (List.mem_of_mem_take hq) with ⟨h1, h2, _, _⟩
    exact h1.odd_of_ne_two (by omega)
  have hodd2 : ∀ q ∈ tags2, Odd q := fun q hq => by
    rcases hmem_pool q (List.mem_of_mem_drop (List.mem_of_mem_take hq)) with ⟨h1, h2, _, _⟩
    exact h1.odd_of_ne_two (by omega)
  -- Show α * R ≥ log (2 * k), so both suppFin (iterConv tags1) and suppFin (iterConv tags2) have card > 2^(k-1)
  set g : ℝ := (c1 * Real.log 2) / Real.log ((k : ℝ) + 2)
  set α : ℝ := 2 * g ^ 2 / (4 * (numScales k : ℝ))
  have hL_bound : (numScales k : ℝ) ≤ 3 * Real.log ((k : ℝ) + 2) := by
    unfold numScales
    have hpow_le : (2 : ℝ) ^ Nat.log2 ((k + 1) / 2) ≤ (k : ℝ) + 2 := by
      have h1 : 2 ^ Nat.log2 ((k + 1) / 2) ≤ (k + 1) / 2 := (Nat.le_log2 (by omega)).mp (le_refl _)
      have h2 : (k + 1) / 2 ≤ k + 2 := by omega
      exact_mod_cast le_trans h1 h2
    have hlog_nat : (Nat.log2 ((k + 1) / 2) : ℝ) * Real.log 2 ≤ Real.log ((k : ℝ) + 2) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpow_le
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hnat_le : (Nat.log2 ((k + 1) / 2) : ℝ) ≤ 2 * Real.log ((k : ℝ) + 2) := by nlinarith
    push_cast
    linarith
  have hlog2k_le : Real.log (2 * (k : ℝ)) ≤ 2 * Real.log ((k : ℝ) + 2) := by
    have h1 : 2 * (k : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith [show (2 : ℝ) ≤ k by exact_mod_cast hk]
    calc Real.log (2 * (k : ℝ)) ≤ Real.log (((k : ℝ) + 2) ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 * Real.log ((k : ℝ) + 2) := by rw [Real.log_pow]; ring
  have hαR_ge : Real.log (2 * (k : ℝ)) ≤ α * (R : ℝ) := by
    have hR_ge : 24 / (c1 * Real.log 2) ^ 2 * (Real.log ((k : ℝ) + 2)) ^ 4 ≤ (R : ℝ) :=
      Nat.le_ceil _
    have hL_pos : (0 : ℝ) < (numScales k : ℝ) := by unfold numScales; positivity
    have hα_lb : (c1 * Real.log 2) ^ 2 / (6 * (Real.log ((k : ℝ) + 2)) ^ 3) ≤ α := by
      dsimp [α, g]
      rw [div_pow, mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hfac_pos : 0 < (c1 * Real.log 2) ^ 2 * (Real.log ((k : ℝ) + 2)) ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left (show 4 * (numScales k : ℝ) ≤ 12 * Real.log ((k : ℝ) + 2) by linarith) hfac_pos.le
      linarith
    have hprod_lb : 4 * Real.log ((k : ℝ) + 2) ≤ α * (R : ℝ) := by
      have h1 := mul_le_mul hα_lb hR_ge (by positivity) (by positivity)
      refine le_trans ?_ h1
      have hc12_ne : (c1 * Real.log 2) ^ 2 ≠ 0 := by positivity
      field_simp [hc12_ne, hlogk_pos.ne']
      linarith
    linarith
  -- Deduce card > 2^(k-1) for any tags of length R
  have hcard_gt : ∀ (tags : List ℕ) (htags : ∀ q ∈ tags, Odd q), tags.length = R →
      2 ^ (k - 1) < (suppFin (iterConv hk tags htags)).card := by
    intro tags htags hlen
    have hdef := iterConv_deficit_le hk c1 hc1 hpref tags htags
    rw [hlen] at hdef
    have hexp_le : Real.exp (-α * (R : ℝ)) ≤ 1 / (2 * (k : ℝ)) := by
      have h1 : -α * (R : ℝ) ≤ -Real.log (2 * (k : ℝ)) := by linarith
      calc Real.exp (-α * (R : ℝ)) ≤ Real.exp (-Real.log (2 * (k : ℝ))) := Real.exp_le_exp.mpr h1
        _ = (Real.exp (Real.log (2 * (k : ℝ))))⁻¹ := Real.exp_neg _
        _ = 1 / (2 * (k : ℝ)) := by rw [Real.exp_log (by positivity), one_div]
    have hdef_lt : (k : ℝ) * Real.log 2 - Hnat (iterConv hk tags htags) < Real.log 2 := by
      have h1 : Real.exp (-α * (R : ℝ)) * ((k : ℝ) * Real.log 2) ≤ (1 / (2 * (k : ℝ))) * ((k : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_right hexp_le (by positivity)
      have h2 : (1 / (2 * (k : ℝ))) * ((k : ℝ) * Real.log 2) = Real.log 2 / 2 := by
        have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
        field_simp [hk_ne]
      linarith
    have hH_gt : Real.log ((2 ^ (k - 1) : ℕ) : ℝ) < Hnat (iterConv hk tags htags) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      linarith
    have hlog_lt : Real.log ((2 ^ (k - 1) : ℕ) : ℝ) < Real.log ((suppFin (iterConv hk tags htags)).card : ℝ) :=
      lt_of_lt_of_le hH_gt (Hnat_le_log_supp _)
    have hcard_pos : (0 : ℝ) < ((suppFin (iterConv hk tags htags)).card : ℝ) := by
      by_contra hle; push Not at hle
      have h0 : (suppFin (iterConv hk tags htags)).card = 0 := by
        have : ((suppFin (iterConv hk tags htags)).card : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg _)
        exact_mod_cast this
      rw [h0, Nat.cast_zero, Real.log_zero] at hlog_lt
      have : 0 ≤ Real.log ((2 ^ (k - 1) : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_two_pow)
      linarith
    have hreal_lt : ((2 ^ (k - 1) : ℕ) : ℝ) < ((suppFin (iterConv hk tags htags)).card : ℝ) := by
      by_contra hle; push Not at hle
      exact (not_lt_of_ge (Real.log_le_log hcard_pos hle)) hlog_lt
    exact_mod_cast hreal_lt
  have hcard1 := hcard_gt tags1 hodd1 hlen1
  have hcard2 := hcard_gt tags2 hodd2 hlen2
  have hsum_gt : 2 ^ k < (suppFin (iterConv hk tags1 hodd1)).card + (suppFin (iterConv hk tags2 hodd2)).card := by
    have hpow : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_two]
    omega
  -- Pigeonhole covering for target a % 2^k
  let target : Fin (2 ^ k) := ⟨a % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  rcases pigeonhole_finset_cover (Nat.two_pow_pos k) _ _ hsum_gt target with ⟨x, hx, y, hy, hxy⟩
  rcases iterConv_supp_representable hk tags1 hnodup1 hprimes1 hodd1 x hx with ⟨S1, hS1_card, hS1_prop, hS1_sum⟩
  rcases iterConv_supp_representable hk tags2 hnodup2 hprimes2 hodd2 y hy with ⟨S2, hS2_card, hS2_prop, hS2_sum⟩
  have hdisj_S : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rcases hS1_prop d hd1 with ⟨_, _, _, _, q1, hq1m, hq1d, hq1u⟩
    rcases hS2_prop d hd2 with ⟨_, _, _, _, q2, hq2m, hq2d, _⟩
    rcases hmem_pool q2 (List.mem_of_mem_drop (List.mem_of_mem_take hq2m)) with ⟨hq2p, hq2_3, hq2_gt, _⟩
    have heq : q2 = q1 := hq1u q2 hq2p hq2_3 hq2_gt hq2d
    subst heq
    exact hdisj_tags q2 hq1m hq2m
  refine ⟨S1 ∪ S2, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj_S]; omega
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hd1 | hd2
    · rcases hS1_prop d hd1 with ⟨h1, h2, h3, h4, _⟩; exact ⟨h1, h2, h3, h4⟩
    · rcases hS2_prop d hd2 with ⟨h1, h2, h3, h4, _⟩; exact ⟨h1, h2, h3, h4⟩
  · rw [Finset.sum_union hdisj_S, Nat.add_mod, hS1_sum, hS2_sum, hxy]

end Erdos18

#print axioms Erdos18.mod_two_pow_covering
