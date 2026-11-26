import Erdos18.Chebyshev
import Erdos18.Entropy
import Erdos18.Covering
import Erdos18.Alpha3Entropy

/-!
# Erdos18/Alpha3Covering.lean — Composed Parametric Mod-2^k Covering (`O((log k)^2 (log log k)^2)`)

Formalizes Lemma 3A* and Lemma 3B* of `work/prover4.md` (cleared by `Breaker-3`):
- Full-pool candidate divisor sets `cand0, candA, candB, candC` and max-cardinality `D_kt k t`.
- `divPMF`: `1/2 δ_0 + 1/2 Unif(D_kt k t)` with exact entropy `log 2 + (1/2) log |D_kt k t|`.
- `SigmaStar k = ∑ t < numScales k, psiNat (g_kt k t) ≤ C_sig * log (k + 2) * (log (log (k + 16)))^2`.
- Non-uniform scale weights `w_t = psiNat (g_kt k t) / SigmaStar k` + 2-sided dyadic shift mixture `Y_star`.
- `mod_two_pow_covering_alpha3`: every residue mod `2^k` is a sum of at most
  `2 * R` strictly distinct positive divisors of `2^k * oddPrimorial Q_max`, where
  `R = ⌈C_cov * (log (k + 2))^2 * (log (log (k + 16)))^2⌉`.
-/

namespace Erdos18

open Finset Nat Real

/-! ## Part 1: Candidate Divisor Sets `D_kt` and Divisibility/Cardinality Bounds -/

/-- The finset of odd primes `≤ y`. -/
def oddPrimesLe (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)

lemma oddPrimesLe_card (y : ℕ) : (oddPrimesLe y).card = oddPrimeCounting y := rfl

/-- Candidate 0: `{1}`. -/
def cand0 : Finset ℕ := {1}

/-- Candidate A: odd primes in `[3, min (2^m - 1) x]`. -/
def candA (x m : ℕ) : Finset ℕ :=
  oddPrimesLe (min (2 ^ m - 1) x)

/-- Candidate B: products of `s = Nat.log x (2^m - 1)` distinct odd primes `≤ x`. -/
def candB (x m : ℕ) : Finset ℕ :=
  let s := Nat.log x (2 ^ m - 1)
  if 3 ≤ x ∧ 1 ≤ s ∧ s ≤ oddPrimeCounting x then
    ((oddPrimesLe x).powersetCard s).image (fun A => ∏ p ∈ A, p)
  else ∅

/-- Candidate C: all divisors of `oddPrimorial (m / 2)`. -/
def candC (m : ℕ) : Finset ℕ :=
  (oddPrimorial (m / 2)).divisors

/-- Helper: pick the larger of two finsets by cardinality. -/
def maxCardFinset (A B : Finset ℕ) : Finset ℕ :=
  if A.card ≤ B.card then B else A

lemma card_le_maxCardFinset_left (A B : Finset ℕ) : A.card ≤ (maxCardFinset A B).card := by
  unfold maxCardFinset; split_ifs with h <;> omega

lemma card_le_maxCardFinset_right (A B : Finset ℕ) : B.card ≤ (maxCardFinset A B).card := by
  unfold maxCardFinset; split_ifs with h <;> omega

lemma mem_maxCardFinset {A B : Finset ℕ} {d : ℕ} (hd : d ∈ maxCardFinset A B) :
    d ∈ A ∨ d ∈ B := by
  unfold maxCardFinset at hd
  split_ifs at hd with h
  · exact Or.inr hd
  · exact Or.inl hd

/-- Chosen max-cardinality divisor set `D_kt k t` for scale `m = 2^t` and pool `x = (k+1)/4`. -/
def D_kt (k t : ℕ) : Finset ℕ :=
  let x := (k + 1) / 4
  let m := 2 ^ t
  maxCardFinset (maxCardFinset cand0 (candA x m)) (maxCardFinset (candB x m) (candC m))

lemma card_cand0_le_D_kt (k t : ℕ) : 1 ≤ (D_kt k t).card := by
  have h0 : cand0.card = 1 := by simp [cand0]
  have h1 := card_le_maxCardFinset_left cand0 (candA ((k + 1) / 4) (2 ^ t))
  have h2 := card_le_maxCardFinset_left (maxCardFinset cand0 (candA ((k + 1) / 4) (2 ^ t)))
    (maxCardFinset (candB ((k + 1) / 4) (2 ^ t)) (candC (2 ^ t)))
  exact h0 ▸ le_trans h1 h2

lemma D_kt_nonempty (k t : ℕ) : (D_kt k t).Nonempty :=
  Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (card_cand0_le_D_kt k t))

lemma card_candA_le_D_kt (k t : ℕ) : (candA ((k + 1) / 4) (2 ^ t)).card ≤ (D_kt k t).card :=
  le_trans (card_le_maxCardFinset_right _ _) (card_le_maxCardFinset_left _ _)

lemma card_candB_le_D_kt (k t : ℕ) : (candB ((k + 1) / 4) (2 ^ t)).card ≤ (D_kt k t).card :=
  le_trans (card_le_maxCardFinset_left _ _) (card_le_maxCardFinset_right _ _)

lemma card_candC_le_D_kt (k t : ℕ) : (candC (2 ^ t)).card ≤ (D_kt k t).card :=
  le_trans (card_le_maxCardFinset_right _ _) (card_le_maxCardFinset_right _ _)

/-- If a prime divides a finite product of natural numbers, it divides one of the factors. -/
lemma prime_dvd_finset_prod {p : ℕ} (hp : p.Prime) {S : Finset ℕ} (h : p ∣ ∏ q ∈ S, q) :
    ∃ q ∈ S, p ∣ q := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty] at h
    exact absurd (Nat.le_of_dvd Nat.one_pos h) (not_le.mpr hp.one_lt)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · rcases ih h2 with ⟨q, hqs, hqp⟩
      exact ⟨q, Finset.mem_insert_of_mem hqs, hqp⟩

/-- Injectivity of `A ↦ ∏ p ∈ A, p` on finsets of primes. -/
lemma prod_primes_inj {A B : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime)
    (heq : ∏ p ∈ A, p = ∏ p ∈ B, p) : A = B := by
  ext p
  constructor
  · intro hp
    have hp_prime := hA p hp
    have hdvd : p ∣ ∏ q ∈ B, q := heq ▸ Finset.dvd_prod_of_mem id hp
    rcases prime_dvd_finset_prod hp_prime hdvd with ⟨q, hqB, hpq⟩
    have hq_prime := hB q hqB
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hpq
    exact this ▸ hqB
  · intro hp
    have hp_prime := hB p hp
    have hdvd : p ∣ ∏ q ∈ A, q := heq.symm ▸ Finset.dvd_prod_of_mem id hp
    rcases prime_dvd_finset_prod hp_prime hdvd with ⟨q, hqA, hpq⟩
    have hq_prime := hA q hqA
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hpq
    exact this ▸ hqA

lemma card_candB {x m : ℕ} (hx : 3 ≤ x)
    (hs1 : 1 ≤ Nat.log x (2 ^ m - 1))
    (hs2 : Nat.log x (2 ^ m - 1) ≤ oddPrimeCounting x) :
    (candB x m).card = Nat.choose (oddPrimeCounting x) (Nat.log x (2 ^ m - 1)) := by
  unfold candB
  rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hx, hs1, hs2⟩ h)]
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_powersetCard, oddPrimesLe_card]
  · intro A hA B hB heq
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hA hB
    exact prod_primes_inj
      (fun p hp => (Finset.mem_filter.mp (hA.1 hp)).2.1)
      (fun p hp => (Finset.mem_filter.mp (hB.1 hp)).2.1)
      heq

/-- Elementary binomial lower bound: `N^s ≤ s^s * Nat.choose N s` for `s ≤ N` via `Nat.descFactorial`. -/
lemma pow_le_pow_mul_choose' {N s : ℕ} (hs : s ≤ N) :
    N ^ s ≤ s ^ s * Nat.choose N s := by
  have hfact_pos : 0 < s.factorial := Nat.factorial_pos s
  suffices h : N ^ s * s.factorial ≤ s ^ s * Nat.descFactorial N s by
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    have h1 : N ^ s * s.factorial ≤ (s ^ s * Nat.choose N s) * s.factorial := by
      calc N ^ s * s.factorial ≤ s ^ s * (s.factorial * Nat.choose N s) := h
        _ = (s ^ s * Nat.choose N s) * s.factorial := by ring
    exact Nat.le_of_mul_le_mul_right h1 hfact_pos
  have hdesc_N : Nat.descFactorial N s = ∏ i ∈ Finset.range s, (N - i) :=
    Nat.descFactorial_eq_prod_range N s
  have hdesc_s : s.factorial = ∏ i ∈ Finset.range s, (s - i) := by
    rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range]
  rw [hdesc_N, hdesc_s]
  have h1 : N ^ s * ∏ i ∈ Finset.range s, (s - i) = ∏ i ∈ Finset.range s, (N * (s - i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have h2 : s ^ s * ∏ i ∈ Finset.range s, (N - i) = ∏ i ∈ Finset.range s, (s * (N - i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [h1, h2]
  apply Finset.prod_le_prod
  intro i hi
  rw [Finset.mem_range] at hi
  zify [le_of_lt hi, le_trans (le_of_lt hi) hs]
  nlinarith

lemma half_two_pow_le_quarter {k t : ℕ} (hk : 2 ≤ k) (ht : t < numScales k) :
    2 ^ t / 2 ≤ (k + 1) / 4 := by
  have hle : t ≤ Nat.log2 ((k + 1) / 2) := by unfold numScales at ht; omega
  have hpow : 2 ^ t ≤ (k + 1) / 2 := (Nat.le_log2 (by omega)).mp hle
  omega

/-- Every `d ∈ D_kt k t` (for `k ≥ 2`, `t < numScales k`) is positive, odd, divides `oddPrimorial ((k+1)/4)`,
    and is strictly less than `2 ^ (2 ^ t)`. -/
lemma D_kt_props {k t : ℕ} (hk : 2 ≤ k) (ht : t < numScales k) {d : ℕ} (hd : d ∈ D_kt k t) :
    0 < d ∧ Odd d ∧ d ∣ oddPrimorial ((k + 1) / 4) ∧ d < 2 ^ (2 ^ t) := by
  set x := (k + 1) / 4
  set m := 2 ^ t
  have hm1 : 1 ≤ m := Nat.one_le_two_pow
  rcases mem_maxCardFinset hd with h0A | hBC
  · rcases mem_maxCardFinset h0A with h0 | hA
    · rw [cand0, Finset.mem_singleton] at h0; subst h0
      refine ⟨Nat.one_pos, odd_one, one_dvd _, ?_⟩
      have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm1
      omega
    · unfold candA oddPrimesLe at hA
      rw [Finset.mem_filter, Finset.mem_range] at hA
      rcases hA with ⟨hlt, hp, hp3⟩
      refine ⟨hp.pos, hp.odd_of_ne_two (by omega), ?_, ?_⟩
      · unfold oddPrimorial
        apply Finset.dvd_prod_of_mem id
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp, hp3⟩
      · dsimp [m]; omega
  · rcases mem_maxCardFinset hBC with hB | hC
    · unfold candB at hB
      dsimp only at hB
      split_ifs at hB with hcond
      · rw [Finset.mem_image] at hB
        rcases hB with ⟨A, hA, rfl⟩
        rw [Finset.mem_powersetCard] at hA
        have hpos : 0 < ∏ p ∈ A, p :=
          Finset.prod_pos fun p hp => (Finset.mem_filter.mp (hA.1 hp)).2.1.pos
        have hodd : Odd (∏ p ∈ A, p) := by
          have hnot2 : ¬ (2 ∣ ∏ p ∈ A, p) := by
            intro h2
            rcases prime_dvd_finset_prod Nat.prime_two h2 with ⟨p, hpA, h2p⟩
            have hp := Finset.mem_filter.mp (hA.1 hpA)
            have : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.2.1).mp h2p
            omega
          exact Nat.odd_iff.mpr (by omega)
        have hdvd : (∏ p ∈ A, p) ∣ oddPrimorial x := by
          unfold oddPrimorial
          exact Finset.prod_dvd_prod_of_subset _ _ id hA.1
        have hlt : ∏ p ∈ A, p < 2 ^ m := by
          have hle1 : ∏ p ∈ A, p ≤ ∏ _p ∈ A, x := by
            apply Finset.prod_le_prod
            intro p hp
            have hpm := Finset.mem_filter.mp (hA.1 hp)
            rw [Finset.mem_range] at hpm
            omega
          rw [Finset.prod_const, hA.2] at hle1
          have h2m_ne : 2 ^ m - 1 ≠ 0 := by
            have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm1
            omega
          have hlog_le : x ^ Nat.log x (2 ^ m - 1) ≤ 2 ^ m - 1 :=
            Nat.pow_log_le_self x h2m_ne
          have h2m_pos : 0 < 2 ^ m := Nat.two_pow_pos m
          change ∏ p ∈ A, p ≤ x ^ Nat.log x (2 ^ m - 1) at hle1
          omega
        exact ⟨hpos, hodd, hdvd, hlt⟩
      · simp at hB
    · unfold candC at hC
      rw [Nat.mem_divisors] at hC
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hC.1 (oddPrimorial_pos _)
      have hodd : Odd d := by
        have hnot2 : ¬ (2 ∣ d) := fun h2 => by
          have h2P : 2 ∣ oddPrimorial (m / 2) := dvd_trans h2 hC.1
          have hP_odd := oddPrimorial_odd (m / 2)
          rw [Nat.odd_iff] at hP_odd
          omega
        exact Nat.odd_iff.mpr (by omega)
      have hhalf : m / 2 ≤ x := half_two_pow_le_quarter hk ht
      have hdvd : d ∣ oddPrimorial x := by
        refine dvd_trans hC.1 ?_
        unfold oddPrimorial
        apply Finset.prod_dvd_prod_of_subset
        intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨by omega, hp.2⟩
      have hlt : d < 2 ^ m :=
        lt_of_le_of_lt (Nat.le_of_dvd (oddPrimorial_pos _) hC.1) (oddPrimorial_lt_two_pow hm1)
      exact ⟨hpos, hodd, hdvd, hlt⟩

/-- Cardinality upper bound: `|(D_kt k t)| ≤ 2 ^ (2 ^ t - 1)` (all elements are odd in `[1, 2^m - 1]`). -/
lemma card_D_kt_le {k t : ℕ} (hk : 2 ≤ k) (ht : t < numScales k) :
    (D_kt k t).card ≤ 2 ^ (2 ^ t - 1) := by
  set m := 2 ^ t
  have hm1 : 1 ≤ m := Nat.one_le_two_pow
  have hsub : D_kt k t ⊆ (Finset.range (2 ^ (m - 1))).image (fun j => 2 * j + 1) := by
    intro d hd
    rcases D_kt_props hk ht hd with ⟨_, hodd, _, hlt⟩
    rcases hodd with ⟨j, rfl⟩
    rw [Finset.mem_image]
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_range]
    have hpow : 2 * 2 ^ (m - 1) = 2 ^ m := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hm1]
    change j < 2 ^ (m - 1)
    change 2 * j + 1 < 2 ^ m at hlt
    omega
  exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (by simp))

/-! ## Part 2: Generic Divisor-Set PMF `divPMF` and Bitwise Shift `shiftPMF_gen` -/

/-- `1/2 δ_0 + 1/2 Unif(D)` on `Fin (2^m)` for a nonempty `D ⊆ [1, 2^m - 1]`. -/
noncomputable def divPMF (m : ℕ) (D : Finset ℕ) (hne : D.Nonempty)
    (hD : ∀ d ∈ D, 0 < d ∧ d < 2 ^ m) : PMF_Fin (2 ^ m) where
  p x :=
    if x.val = 0 then (1 : ℝ) / 2
    else if x.val ∈ D then 1 / (2 * (D.card : ℝ))
    else 0
  nonneg x := by
    split_ifs <;> positivity
  sum_one := by
    have h0_lt : 0 < 2 ^ m := Nat.two_pow_pos m
    let zeroFin : Fin (2 ^ m) := ⟨0, h0_lt⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ zeroFin)]
    have hz : (if zeroFin.val = 0 then (1 : ℝ) / 2
        else if zeroFin.val ∈ D then 1 / (2 * (D.card : ℝ)) else 0) = 1 / 2 := by
      simp [zeroFin]
    rw [hz]
    have hrest : (∑ x ∈ Finset.univ.erase zeroFin,
        if x.val = 0 then (1 : ℝ) / 2
        else if x.val ∈ D then 1 / (2 * (D.card : ℝ)) else 0) = 1 / 2 := by
      have hsimp : ∀ x ∈ Finset.univ.erase zeroFin,
          (if x.val = 0 then (1 : ℝ) / 2
           else if x.val ∈ D then 1 / (2 * (D.card : ℝ)) else 0) =
          (if x.val ∈ D then 1 / (2 * (D.card : ℝ)) else 0) := by
        intro x hx
        have hxne : x.val ≠ 0 := by
          intro h0; exact (Finset.mem_erase.mp hx).1 (Fin.ext h0)
        simp [hxne]
      rw [Finset.sum_congr rfl hsimp, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hfilt : ((Finset.univ.erase zeroFin).filter (fun x : Fin (2 ^ m) => x.val ∈ D)).card = D.card := by
        apply Finset.card_bij (fun x _ => x.val)
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro x _ y _ h; exact Fin.ext h
        · intro d hd
          rcases hD d hd with ⟨hdpos, hdlt⟩
          refine ⟨⟨d, hdlt⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff, zeroFin]
          exact ⟨by omega, hd⟩
      rw [hfilt]
      have hcard_pos : (0 : ℝ) < (D.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
      field_simp [hcard_pos.ne']
    linarith

/-- Exact Shannon entropy of `divPMF`: `Hnat = log 2 + (1/2) log |D|`. -/
theorem Hnat_divPMF (m : ℕ) (D : Finset ℕ) (hne : D.Nonempty)
    (hD : ∀ d ∈ D, 0 < d ∧ d < 2 ^ m) :
    Hnat (divPMF m D hne hD) = Real.log 2 + Real.log (D.card : ℝ) / 2 := by
  have h0_lt : 0 < 2 ^ m := Nat.two_pow_pos m
  let zeroFin : Fin (2 ^ m) := ⟨0, h0_lt⟩
  unfold Hnat
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ zeroFin)]
  have hz : Real.negMulLog ((divPMF m D hne hD).p zeroFin) = Real.log 2 / 2 := by
    simp only [divPMF, zeroFin, ↓reduceIte, Real.negMulLog, one_div, Real.log_inv]
    ring
  rw [hz]
  have hrest : (∑ x ∈ Finset.univ.erase zeroFin, Real.negMulLog ((divPMF m D hne hD).p x)) =
      (Real.log 2 + Real.log (D.card : ℝ)) / 2 := by
    have hsimp : ∑ x ∈ Finset.univ.erase zeroFin, Real.negMulLog ((divPMF m D hne hD).p x) =
        ∑ x ∈ (Finset.univ.erase zeroFin).filter (fun x : Fin (2 ^ m) => x.val ∈ D),
          Real.negMulLog (1 / (2 * (D.card : ℝ))) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      have hxne : x.val ≠ 0 := fun h0 => (Finset.mem_erase.mp hx).1 (Fin.ext h0)
      dsimp only [divPMF]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hxne)]
      split_ifs <;> simp [Real.negMulLog]
    have hfilt : ((Finset.univ.erase zeroFin).filter (fun x : Fin (2 ^ m) => x.val ∈ D)).card = D.card := by
      apply Finset.card_bij (fun x _ => x.val)
      · intro x hx; exact (Finset.mem_filter.mp hx).2
      · intro x _ y _ h; exact Fin.ext h
      · intro d hd
        rcases hD d hd with ⟨hdpos, hdlt⟩
        refine ⟨⟨d, hdlt⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff, zeroFin]
        exact ⟨by omega, hd⟩
    have hcard_pos : (0 : ℝ) < (D.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
    rw [hsimp, Finset.sum_const, nsmul_eq_mul, hfilt, Real.negMulLog, one_div, Real.log_inv,
        Real.log_mul (by norm_num) hcard_pos.ne']
    field_simp [hcard_pos.ne']
  rw [hrest]; ring

/-- Generic shift pushforward of any `Z : PMF_Fin (2 ^ (2 ^ t))` to `Fin (2^k)` via `z ↦ 2^s * z`. -/
noncomputable def shiftPMF_gen (k t s : ℕ) (hst : s + 2 ^ t ≤ k)
    (Z : PMF_Fin (2 ^ (2 ^ t))) : PMF_Fin (2 ^ k) where
  p x :=
    if h : 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t) then
      Z.p ⟨x.val / 2 ^ s, h.2⟩
    else 0
  nonneg x := by
    split_ifs with h
    · exact Z.nonneg _
    · exact le_rfl
  sum_one := by
    rw [← Z.sum_one]
    have hfilt : (∑ x : Fin (2 ^ k),
        if h : 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t) then
          Z.p ⟨x.val / 2 ^ s, h.2⟩
        else 0) =
        ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t)),
          if h : 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t) then
            Z.p ⟨x.val / 2 ^ s, h.2⟩
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

/-- Generic bit-shift identity: for `s ≤ j`, `condBitEnt (shiftPMF_gen k t s hst Z) j = condBitEnt Z (j - s)`. -/
lemma condBitEnt_shiftPMF_gen (k t s j : ℕ) (hst : s + 2 ^ t ≤ k) (hsj : s ≤ j)
    (Z : PMF_Fin (2 ^ (2 ^ t))) :
    condBitEnt (shiftPMF_gen k t s hst Z) j = condBitEnt Z (j - s) := by
  let S := shiftPMF_gen k t s hst Z
  have hW_zero : ∀ a : Fin (2 ^ j), ¬ (2 ^ s ∣ a.val) → W_pref S j a = 0 := by
    intro a hnd
    unfold W_pref
    apply Finset.sum_eq_zero
    intro x hx
    have hpref : x.val % 2 ^ j = a.val := congrArg Fin.val (Finset.mem_filter.mp hx).2
    dsimp [S, shiftPMF_gen]
    split_ifs with h
    · exfalso; apply hnd
      have hdvd : 2 ^ s ∣ 2 ^ j := Nat.pow_dvd_pow 2 hsj
      rw [← hpref]
      exact (Nat.dvd_mod_iff hdvd).mpr h.1
    · rfl
  have hpow_j : 2 ^ s * 2 ^ (j - s) = 2 ^ j := by rw [← pow_add, Nat.add_sub_of_le hsj]
  have hW_eq : ∀ a' : Fin (2 ^ (j - s)),
      W_pref S j ⟨2 ^ s * a'.val, by rw [← hpow_j]; exact Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)⟩ =
      W_pref Z (j - s) a' := by
    intro a'
    let a : Fin (2 ^ j) := ⟨2 ^ s * a'.val, by rw [← hpow_j]; exact Nat.mul_lt_mul_of_pos_left a'.isLt (Nat.two_pow_pos s)⟩
    unfold W_pref
    have hfilt : ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a), S.p x =
        ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ 2 ^ s ∣ x.val ∧ x.val / 2 ^ s < 2 ^ (2 ^ t)), S.p x := by
      symm
      apply Finset.sum_subset
      · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
      · intro x hx hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hnot
        dsimp [S, shiftPMF_gen]
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
      dsimp [S, shiftPMF_gen]; simp [h]
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
        dsimp [S, shiftPMF_gen]
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
      dsimp [S, shiftPMF_gen]; simp [h]
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
  apply Finset.sum_bij (fun a _ => ⟨a.val / 2 ^ s, by
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
    · simp
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

/-! ## Part 3: Scale Entropy Density `g_kt`, `SigmaStar`, and 4-Regime Upper Bound (Lemma 3A*) -/

/-- Entropy density per bit (in nats) of `Z_{k,t}`: `(log 2 + (1/2) log |D_kt k t|) / 2^t`. -/
noncomputable def g_kt (k t : ℕ) : ℝ :=
  (Real.log 2 + Real.log ((D_kt k t).card : ℝ) / 2) / ((2 ^ t : ℕ) : ℝ)

lemma g_kt_lower_trivial (k t : ℕ) :
    Real.log 2 / ((2 ^ t : ℕ) : ℝ) ≤ g_kt k t := by
  unfold g_kt
  have h1 : (1 : ℝ) ≤ ((D_kt k t).card : ℝ) := by exact_mod_cast card_cand0_le_D_kt k t
  have hlog_nn : 0 ≤ Real.log ((D_kt k t).card : ℝ) := Real.log_nonneg h1
  have hpow_pos : (0 : ℝ) < ((2 ^ t : ℕ) : ℝ) := by positivity
  exact div_le_div_of_nonneg_right (by linarith) hpow_pos.le

lemma g_kt_pos (k t : ℕ) : 0 < g_kt k t := by
  have h1 : 0 < Real.log 2 / ((2 ^ t : ℕ) : ℝ) := div_pos (Real.log_pos (by norm_num)) (by positivity)
  exact lt_of_lt_of_le h1 (g_kt_lower_trivial k t)

lemma g_kt_le_log_two {k t : ℕ} (hk : 2 ≤ k) (ht : t < numScales k) :
    g_kt k t ≤ Real.log 2 := by
  unfold g_kt
  set m := 2 ^ t
  have hm1 : 1 ≤ m := Nat.one_le_two_pow
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hcard_le : ((D_kt k t).card : ℝ) ≤ (2 : ℝ) ^ (m - 1) := by
    exact_mod_cast card_D_kt_le hk ht
  have hcard_pos : (0 : ℝ) < ((D_kt k t).card : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one (card_cand0_le_D_kt k t))
  have hlog_le : Real.log ((D_kt k t).card : ℝ) ≤ ((m - 1 : ℕ) : ℝ) * Real.log 2 := by
    calc Real.log ((D_kt k t).card : ℝ) ≤ Real.log ((2 : ℝ) ^ (m - 1)) :=
          Real.log_le_log hcard_pos hcard_le
      _ = ((m - 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (m - 1)
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast this
    linarith
  rw [hm_sub] at hlog_le
  rw [div_le_iff₀ hm_pos]
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

lemma g_kt_le_one {k t : ℕ} (hk : 2 ≤ k) (ht : t < numScales k) :
    g_kt k t ≤ 1 := by
  have h1 := g_kt_le_log_two hk ht
  have h2 := Real.log_two_lt_d9
  linarith

/-- The log-harmonic scale sum `SigmaStar k = ∑ t < numScales k, psiNat (g_kt k t)`. -/
noncomputable def SigmaStar (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (numScales k), psiNat (g_kt k t)

lemma SigmaStar_ge_two {k : ℕ} (hk : 2 ≤ k) : (2 : ℝ) ≤ SigmaStar k := by
  have h0_mem : 0 ∈ Finset.range (numScales k) := by
    rw [Finset.mem_range]; unfold numScales; omega
  have hterm : psiNat (g_kt k 0) ≤ SigmaStar k := by
    unfold SigmaStar
    apply Finset.single_le_sum (f := fun t => psiNat (g_kt k t)) (fun t ht => ?_) h0_mem
    rw [Finset.mem_range] at ht
    exact (psiNat_pos (g_kt_pos k t) (g_kt_le_one hk ht)).le
  have hge : psiNat (Real.log 2) ≤ psiNat (g_kt k 0) :=
    psiNat_anti (g_kt_pos k 0) (g_kt_le_log_two hk (by unfold numScales; omega))
      (by linarith [Real.log_two_lt_d9])
  have hpsi_ge2 : (2 : ℝ) ≤ psiNat (Real.log 2) := by
    unfold psiNat
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [le_div_iff₀ hlog2_pos]
    -- Need 2 * log 2 ≤ log (4 / log 2) ↔ log 4 ≤ log (4 / log 2) ↔ 4 ≤ 4 / log 2 ↔ log 2 ≤ 1
    have hlog4 : 2 * Real.log 2 = Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    rw [hlog4]
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hlog2_pos]
    linarith [Real.log_two_lt_d9]
  linarith

lemma SigmaStar_pos {k : ℕ} (hk : 2 ≤ k) : 0 < SigmaStar k :=
  lt_of_lt_of_le (by norm_num) (SigmaStar_ge_two hk)

/-- Elementary harmonic sum bound: `∑ u ∈ Finset.Icc 1 U, 1 / (u : ℝ) ≤ 1 + Real.log U` for `U ≥ 1`. -/
lemma harmonic_sum_le_one_add_log {U : ℕ} (hU : 1 ≤ U) :
    ∑ u ∈ Finset.Icc 1 U, (1 : ℝ) / (u : ℝ) ≤ 1 + Real.log (U : ℝ) := by
  induction U, hU using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      have h1 : Real.log ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤ (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hm_pos hm1_pos)
      rw [Real.log_div hm_pos.ne' hm1_pos.ne'] at h1
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have hsub : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(1 / ((m + 1 : ℕ) : ℝ)) := by
        rw [hcast]; field_simp [show (m : ℝ) + 1 ≠ 0 by linarith]; ring
      linarith
    linarith

/-- Helper: `1 < Real.log (Real.log (k + 16))` for all `k ≥ 2`. -/
lemma one_lt_log_log_add16 {k : ℕ} (hk : 2 ≤ k) :
    1 < Real.log (Real.log ((k : ℝ) + 16)) := by
  have h16 : (16 : ℝ) < (k : ℝ) + 16 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; ring
  have hexp_lt : Real.exp 1 < Real.log ((k : ℝ) + 16) := by
    have h1 := Real.exp_one_lt_d9
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log (16 : ℝ) < Real.log ((k : ℝ) + 16) := Real.log_lt_log (by norm_num) h16
    linarith
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) hexp_lt

/-- Helper: `oddPrimeCounting y ≥ c0 * y / log y` for all `y ≥ 3`, with `0 < c0 ≤ 1/4`. -/
lemma oddPrimeCounting_lower :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ 1 / 4 ∧
      ∀ y : ℕ, 3 ≤ y → c0 * (y : ℝ) / Real.log (y : ℝ) ≤ (oddPrimeCounting y : ℝ) := by
  rcases prime_counting_lower with ⟨c0_raw, hc0_raw, hpi⟩
  refine ⟨min (c0_raw / 2) (1 / 4), by positivity, min_le_right _ _, ?_⟩
  intro y hy
  have hpi_y := hpi y (by omega)
  have hpi3 : 2 ≤ Nat.primeCounting y := by
    have h1 : Nat.primeCounting 3 = 2 := by decide
    exact h1 ▸ Nat.monotone_primeCounting hy
  have hodd := oddPrimeCounting_eq_primeCounting_sub_one (by omega : 2 ≤ y)
  have hhalf : (Nat.primeCounting y : ℝ) / 2 ≤ (oddPrimeCounting y : ℝ) := by
    have hcast : (oddPrimeCounting y : ℝ) + 1 = (Nat.primeCounting y : ℝ) := by exact_mod_cast hodd
    have h2 : (2 : ℝ) ≤ (Nat.primeCounting y : ℝ) := by exact_mod_cast hpi3
    linarith
  have hlog_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hc0_le : min (c0_raw / 2) (1 / 4) ≤ c0_raw / 2 := min_le_left _ _
  have h1 : min (c0_raw / 2) (1 / 4) * (y : ℝ) / Real.log (y : ℝ) ≤
      (c0_raw * (y : ℝ) / Real.log (y : ℝ)) / 2 := by
    rw [div_div, div_le_div_iff₀ hlog_pos (by positivity)]
    have hy_nn : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    have hyl_nn : 0 ≤ (y : ℝ) * Real.log (y : ℝ) := mul_nonneg hy_nn hlog_pos.le
    nlinarith
  linarith

/-- Helper: `m ≤ 2 ^ (m / 8)` for `m ≥ 64` (copied locally to avoid circular import with `MainTheorem`). -/
private lemma nat_le_two_pow_div_eight_aux {m : ℕ} (hm : 64 ≤ m) : m ≤ 2 ^ (m / 8) := by
  have hm8 : 8 ≤ m / 8 := by omega
  have hpow : ∀ r, 8 ≤ r → 8 * r + 7 ≤ 2 ^ r := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ r hr ih => rw [pow_succ, mul_comm]; omega
  have h1 := hpow (m / 8) hm8
  omega

private lemma sum_union_le_of_nonneg {A B : Finset ℕ} {f : ℕ → ℝ}
    (hA : ∀ x ∈ A, 0 ≤ f x) (_hB : ∀ x ∈ B, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have hnn : 0 ≤ ∑ x ∈ A ∩ B, f x :=
    Finset.sum_nonneg fun x hx => hA x (Finset.mem_inter.mp hx).1
  linarith

set_option maxHeartbeats 2000000 in
/-- **Lemma 3A* Part 2**: `SigmaStar k ≤ C_sig * log (k + 2) * (log (log (k + 16)))^2` for all `k ≥ 2`. -/
theorem SigmaStar_le :
    ∃ C_sig : ℝ, 0 < C_sig ∧ ∀ k : ℕ, 2 ≤ k →
      SigmaStar k ≤ C_sig * Real.log ((k : ℝ) + 2) * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 := by
  rcases oddPrimeCounting_lower with ⟨c0, hc0_pos, hc0_le, hodd_pi⟩
  rcases prefix_entropy_rate_lower with ⟨c1_raw, hc1_raw, hpref⟩
  set c1 : ℝ := min c1_raw (1 / 2)
  have hc1_pos : 0 < c1 := by positivity
  have hc1_le : c1 ≤ 1 / 2 := min_le_right _ _
  set M0 : ℕ := max 64 (8 * (Nat.ceil (Real.log (1 / c0) / Real.log 2) + 1))
  have hM0_64 : 64 ≤ M0 := le_max_left _ _
  have hM0_pos : (0 : ℝ) < (M0 : ℝ) := by exact_mod_cast (by omega : 0 < M0)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  -- Explicit regime constants
  set K0 : ℝ := ((M0 : ℝ) + 1) * psiNat (Real.log 2 / (M0 : ℝ))
  set K1 : ℝ := 6 * psiNat (Real.log 2 / 8)
  set K2 : ℝ := 200
  set N3 : ℕ := Nat.ceil (Real.log (4 / c0) / Real.log 2) + 2
  set K3 : ℝ := (N3 : ℝ) * (1 / (c1 * Real.log 2)) * (Real.log (4 / (c1 * Real.log 2)) + 2)
  have hK0_nn : 0 ≤ K0 := by
    have h1 : 0 < Real.log 2 / (M0 : ℝ) := div_pos hlog2_pos hM0_pos
    have h2 : Real.log 2 / (M0 : ℝ) ≤ 1 := by
      rw [div_le_one hM0_pos]; have : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast (by omega : 1 ≤ M0)
      linarith
    exact mul_nonneg (by positivity) (psiNat_pos h1 h2).le
  have hK1_nn : 0 ≤ K1 := by
    have h1 : 0 < Real.log 2 / 8 := by positivity
    have h2 : Real.log 2 / 8 ≤ 1 := by linarith
    exact mul_nonneg (by norm_num) (psiNat_pos h1 h2).le
  have hK3_nn : 0 ≤ K3 := by
    have h4c1 : 1 ≤ 4 / (c1 * Real.log 2) := by
      rw [one_le_div (by positivity)]; nlinarith
    have hlog_nn : 0 ≤ Real.log (4 / (c1 * Real.log 2)) := Real.log_nonneg h4c1
    positivity
  refine ⟨K0 + K1 + K2 + K3 + 1, by positivity, ?_⟩
  intro k hk
  set x : ℕ := (k + 1) / 4
  set Φ : ℝ := Real.log ((k : ℝ) + 2) * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2
  have hlogk_ge1 : 1 < Real.log ((k : ℝ) + 2) := by
    have h4 : (4 : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ k + 2)
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    have := Real.log_two_gt_d9
    linarith [Real.log_le_log (by norm_num) h4]
  have hll_gt1 : 1 < Real.log (Real.log ((k : ℝ) + 16)) := one_lt_log_log_add16 hk
  have hΦ_gt1 : 1 < Φ := by dsimp [Φ]; nlinarith
  -- Partition Finset.range (numScales k) into 4 regimes (cover suffices since psiNat > 0)
  let S := Finset.range (numScales k)
  let R0 := S.filter (fun t => 2 ^ t < M0)
  let R1 := S.filter (fun t => M0 ≤ 2 ^ t ∧ ((2 ^ t : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log (x : ℝ))
  let R2 := S.filter (fun t => M0 ≤ 2 ^ t ∧ 2 * Real.log (x : ℝ) < ((2 ^ t : ℕ) : ℝ) * Real.log 2 ∧
      ((2 ^ t : ℕ) : ℝ) ≤ (c0 / 2) * (x : ℝ))
  let R3 := S.filter (fun t => M0 ≤ 2 ^ t ∧ (c0 / 2) * (x : ℝ) < ((2 ^ t : ℕ) : ℝ))
  have hcover : S ⊆ R0 ∪ (R1 ∪ (R2 ∪ R3)) := by
    intro t ht
    simp only [Finset.mem_union, R0, R1, R2, R3, Finset.mem_filter]
    by_cases h0 : 2 ^ t < M0
    · exact Or.inl ⟨ht, h0⟩
    · push Not at h0
      by_cases h1 : ((2 ^ t : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log (x : ℝ)
      · exact Or.inr (Or.inl ⟨ht, h0, h1⟩)
      · push Not at h1
        by_cases h2 : ((2 ^ t : ℕ) : ℝ) ≤ (c0 / 2) * (x : ℝ)
        · exact Or.inr (Or.inr (Or.inl ⟨ht, h0, h1, h2⟩))
        · push Not at h2
          exact Or.inr (Or.inr (Or.inr ⟨ht, h0, h2⟩))
  have hpsi_nn : ∀ t ∈ S, 0 ≤ psiNat (g_kt k t) := fun t ht =>
    (psiNat_pos (g_kt_pos k t) (g_kt_le_one hk (Finset.mem_range.mp ht))).le
  have hsplit : SigmaStar k ≤
      (∑ t ∈ R0, psiNat (g_kt k t)) + (∑ t ∈ R1, psiNat (g_kt k t)) +
      (∑ t ∈ R2, psiNat (g_kt k t)) + (∑ t ∈ R3, psiNat (g_kt k t)) := by
    unfold SigmaStar
    have hsub_sum : ∑ t ∈ S, psiNat (g_kt k t) ≤ ∑ t ∈ R0 ∪ (R1 ∪ (R2 ∪ R3)), psiNat (g_kt k t) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hcover
      intro t ht _
      have htS : t ∈ S := by
        simp only [Finset.mem_union, R0, R1, R2, R3, Finset.mem_filter] at ht
        rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      exact hpsi_nn t htS
    have hnn_all : ∀ t ∈ R0 ∪ (R1 ∪ (R2 ∪ R3)), 0 ≤ psiNat (g_kt k t) := by
      intro t ht
      have htS : t ∈ S := by
        simp only [Finset.mem_union, R0, R1, R2, R3, Finset.mem_filter] at ht
        rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      exact hpsi_nn t htS
    have hu1 : ∑ t ∈ R0 ∪ (R1 ∪ (R2 ∪ R3)), psiNat (g_kt k t) ≤
        (∑ t ∈ R0, psiNat (g_kt k t)) + ∑ t ∈ R1 ∪ (R2 ∪ R3), psiNat (g_kt k t) :=
      sum_union_le_of_nonneg (fun t ht => hnn_all t (Finset.mem_union_left _ ht))
        (fun t ht => hnn_all t (Finset.mem_union_right _ ht))
    have hu2 : ∑ t ∈ R1 ∪ (R2 ∪ R3), psiNat (g_kt k t) ≤
        (∑ t ∈ R1, psiNat (g_kt k t)) + ∑ t ∈ R2 ∪ R3, psiNat (g_kt k t) :=
      sum_union_le_of_nonneg (fun t ht => hnn_all t (Finset.mem_union_right _ (Finset.mem_union_left _ ht)))
        (fun t ht => hnn_all t (Finset.mem_union_right _ (Finset.mem_union_right _ ht)))
    have hu3 : ∑ t ∈ R2 ∪ R3, psiNat (g_kt k t) ≤
        (∑ t ∈ R2, psiNat (g_kt k t)) + ∑ t ∈ R3, psiNat (g_kt k t) :=
      sum_union_le_of_nonneg
        (fun t ht => hnn_all t (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ ht))))
        (fun t ht => hnn_all t (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ ht))))
    linarith
  -- Helper for Regimes 1-3: if t ∈ S and M0 ≤ 2^t then 32 ≤ x and x ≤ k
  have hx_ge32 : ∀ t ∈ S, M0 ≤ 2 ^ t → 32 ≤ x := by
    intro t ht hm
    have ht_lt : t < numScales k := Finset.mem_range.mp ht
    have hhalf := half_two_pow_le_quarter hk ht_lt
    omega
  -- Regime 0 bound: ≤ K0 * Φ
  have hR0 : ∑ t ∈ R0, psiNat (g_kt k t) ≤ K0 * Φ := by
    have hterm : ∀ t ∈ R0, psiNat (g_kt k t) ≤ psiNat (Real.log 2 / (M0 : ℝ)) := by
      intro t ht
      rw [Finset.mem_filter] at ht
      have ht_lt : t < numScales k := Finset.mem_range.mp ht.1
      have hm_le : ((2 ^ t : ℕ) : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast ht.2.le
      have hge : Real.log 2 / (M0 : ℝ) ≤ g_kt k t :=
        le_trans (div_le_div_of_nonneg_left hlog2_pos.le (by positivity) hm_le) (g_kt_lower_trivial k t)
      exact psiNat_anti (div_pos hlog2_pos hM0_pos) hge (g_kt_le_one hk ht_lt)
    have hcard : R0.card ≤ M0 + 1 := by
      have hsub : R0 ⊆ Finset.range (M0 + 1) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [Finset.mem_range]
        have : t < 2 ^ t := Nat.lt_two_pow_self
        omega
      exact le_trans (Finset.card_le_card hsub) (by simp)
    calc ∑ t ∈ R0, psiNat (g_kt k t)
        ≤ ∑ _t ∈ R0, psiNat (Real.log 2 / (M0 : ℝ)) := Finset.sum_le_sum hterm
      _ = (R0.card : ℝ) * psiNat (Real.log 2 / (M0 : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((M0 : ℝ) + 1) * psiNat (Real.log 2 / (M0 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcard
          · exact (psiNat_pos (div_pos hlog2_pos hM0_pos) (by
              rw [div_le_one hM0_pos]; have : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast (by omega : 1 ≤ M0)
              linarith)).le
      _ = K0 := rfl
      _ ≤ K0 * Φ := by nlinarith
  -- Regime 1 bound: ≤ K1 * Φ
  have hR1 : ∑ t ∈ R1, psiNat (g_kt k t) ≤ K1 * Φ := by
    have hterm : ∀ t ∈ R1, psiNat (g_kt k t) ≤ psiNat (Real.log 2 / 8) := by
      intro t ht
      rw [Finset.mem_filter] at ht
      have ht_lt : t < numScales k := Finset.mem_range.mp ht.1
      set m := 2 ^ t
      have hm_ge_M0 : M0 ≤ m := ht.2.1
      have hm_64 : 64 ≤ m := le_trans hM0_64 hm_ge_M0
      have hx32 : 32 ≤ x := hx_ge32 t ht.1 hm_ge_M0
      set y := min (2 ^ m - 1) x
      have h2m_half_le_x : 2 ^ (m / 2) ≤ x := by
        have hlog_le : Real.log ((2 ^ (m / 2) : ℕ) : ℝ) ≤ Real.log (x : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
          have hdiv : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
            have : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
            have hcast : (2 : ℝ) * ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
            linarith
          nlinarith [ht.2.2]
        have hpos1 : (0 : ℝ) < ((2 ^ (m / 2) : ℕ) : ℝ) := by positivity
        have hpos2 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
        have hle_r : ((2 ^ (m / 2) : ℕ) : ℝ) ≤ (x : ℝ) := (Real.log_le_log_iff hpos1 hpos2).mp hlog_le
        exact_mod_cast hle_r
      have h2m_half_lt : 2 ^ (m / 2) ≤ 2 ^ m - 1 := by
        have h1 : 2 ^ (m / 2) * 2 ≤ 2 ^ m := by
          rw [← pow_succ]
          exact Nat.pow_le_pow_right (by omega) (by omega)
        have h2 : 1 ≤ 2 ^ (m / 2) := Nat.one_le_two_pow
        omega
      have hy_ge : 2 ^ (m / 2) ≤ y := le_min h2m_half_lt h2m_half_le_x
      have hy_ge3 : 3 ≤ y := by
        have : 2 ^ 2 ≤ 2 ^ (m / 2) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hy_lt : y < 2 ^ m := by
        have : y ≤ 2 ^ m - 1 := min_le_left _ _
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        omega
      have hcard_ge : c0 * (y : ℝ) / Real.log (y : ℝ) ≤ ((D_kt k t).card : ℝ) := by
        have h1 : (candA x m).card ≤ (D_kt k t).card := card_candA_le_D_kt k t
        have h2 : (candA x m).card = oddPrimeCounting y := by rfl
        have h3 : c0 * (y : ℝ) / Real.log (y : ℝ) ≤ (oddPrimeCounting y : ℝ) := hodd_pi y hy_ge3
        have h4 : (oddPrimeCounting y : ℝ) ≤ ((D_kt k t).card : ℝ) := by exact_mod_cast (h2 ▸ h1)
        linarith
      have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
      have hlogy_lt_m : Real.log (y : ℝ) ≤ (m : ℝ) := by
        have h1 : Real.log (y : ℝ) ≤ Real.log ((2 ^ m : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hy_lt.le)
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
        have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      have hcard_ge2 : c0 * ((2 ^ (m / 2) : ℕ) : ℝ) / (m : ℝ) ≤ ((D_kt k t).card : ℝ) := by
        have h1 : c0 * ((2 ^ (m / 2) : ℕ) : ℝ) / (m : ℝ) ≤ c0 * (y : ℝ) / Real.log (y : ℝ) := by
          apply div_le_div₀ (by positivity)
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hy_ge) hc0_pos.le
          · exact hlogy_pos
          · exact hlogy_lt_m
        linarith
      have hm_even : m / 2 * 2 = m := by
        have ht1 : 1 ≤ t := by
          by_contra ht0; push Not at ht0
          have : t = 0 := by omega
          subst this; simp [m] at hm_64
        have h2 : 2 ∣ 2 ^ t := dvd_pow_self 2 (by omega)
        exact Nat.div_mul_cancel h2
      have hlog_card : (m : ℝ) * Real.log 2 / 4 ≤ Real.log ((D_kt k t).card : ℝ) := by
        have h1 : Real.log (c0 * ((2 ^ (m / 2) : ℕ) : ℝ) / (m : ℝ)) ≤ Real.log ((D_kt k t).card : ℝ) :=
          Real.log_le_log (by positivity) hcard_ge2
        rw [Real.log_div (by positivity) (by positivity),
            Real.log_mul hc0_pos.ne' (by positivity),
            Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
        have hm2_eq : ((m / 2 : ℕ) : ℝ) = (m : ℝ) / 2 := by
          have hcast : ((m / 2 : ℕ) : ℝ) * 2 = (m : ℝ) := by exact_mod_cast hm_even
          linarith
        rw [hm2_eq] at h1
        -- Bound Real.log m ≤ (m / 8) * Real.log 2
        have hlogm_le : Real.log (m : ℝ) ≤ (m : ℝ) / 8 * Real.log 2 := by
          have hpow := nat_le_two_pow_div_eight_aux hm_64
          have hle : Real.log (m : ℝ) ≤ Real.log ((2 ^ (m / 8) : ℕ) : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hpow)
          have hpow_log : Real.log ((2 ^ (m / 8) : ℕ) : ℝ) = ((m / 8 : ℕ) : ℝ) * Real.log 2 := by
            rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
          rw [hpow_log] at hle
          have hdiv8 : ((m / 8 : ℕ) : ℝ) ≤ (m : ℝ) / 8 := by
            have : 8 * (m / 8) ≤ m := Nat.mul_div_le m 8
            have hcast : (8 : ℝ) * ((m / 8 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
            linarith
          nlinarith
        -- Bound -Real.log c0 = Real.log (1 / c0) ≤ (m / 8) * Real.log 2
        have hlogc0_le : -Real.log c0 ≤ (m : ℝ) / 8 * Real.log 2 := by
          have hM0_c0 : 8 * (Nat.ceil (Real.log (1 / c0) / Real.log 2) + 1) ≤ m :=
            le_trans (le_max_right _ _) hm_ge_M0
          have hceil : Real.log (1 / c0) / Real.log 2 ≤ (Nat.ceil (Real.log (1 / c0) / Real.log 2) : ℝ) :=
            Nat.le_ceil _
          have hcast : (8 : ℝ) * ((Nat.ceil (Real.log (1 / c0) / Real.log 2) : ℝ) + 1) ≤ (m : ℝ) := by
            exact_mod_cast hM0_c0
          have hinv : Real.log (1 / c0) = -Real.log c0 := by rw [one_div, Real.log_inv]
          rw [div_le_iff₀ hlog2_pos] at hceil
          nlinarith
        linarith
      have hg_ge : Real.log 2 / 8 ≤ g_kt k t := by
        unfold g_kt
        have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
        rw [div_le_div_iff₀ (by norm_num) hm_pos]
        nlinarith
      exact psiNat_anti (by positivity) hg_ge (g_kt_le_one hk ht_lt)
    have hcard_R1 : (R1.card : ℝ) ≤ 6 * Φ := by
      by_cases hne : R1.Nonempty
      · have hle_all : ∀ t ∈ R1, (t : ℝ) < 5 * Real.log (Real.log ((k : ℝ) + 16)) := by
          intro t ht
          rw [Finset.mem_filter] at ht
          have hx32 : 32 ≤ x := hx_ge32 t ht.1 ht.2.1
          have hx_le : (x : ℝ) ≤ (k : ℝ) + 16 := by exact_mod_cast (by omega : x ≤ k + 16)
          have hlogx_le : Real.log (x : ℝ) ≤ Real.log ((k : ℝ) + 16) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < x)) hx_le
          have h2t_le : ((2 ^ t : ℕ) : ℝ) ≤ 4 * Real.log ((k : ℝ) + 16) := by
            have := Real.log_two_gt_d9
            nlinarith [ht.2.2]
          have hlog_2t : (t : ℝ) * Real.log 2 ≤ Real.log (4 * Real.log ((k : ℝ) + 16)) := by
            have h1 := Real.log_le_log (by positivity) h2t_le
            rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
          have hlog4 : Real.log (4 * Real.log ((k : ℝ) + 16)) =
              2 * Real.log 2 + Real.log (Real.log ((k : ℝ) + 16)) := by
            have hlogk16_pos : 0 < Real.log ((k : ℝ) + 16) :=
              Real.log_pos (by exact_mod_cast (by omega : 1 < k + 16))
            rw [Real.log_mul (by norm_num) hlogk16_pos.ne',
                show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            ring
          have := Real.log_two_gt_d9
          nlinarith
        let N1 : ℕ := Nat.ceil (5 * Real.log (Real.log ((k : ℝ) + 16)))
        have hsub : R1 ⊆ Finset.range N1 := by
          intro t ht
          rw [Finset.mem_range]
          have hlt := hle_all t ht
          have hceil : 5 * Real.log (Real.log ((k : ℝ) + 16)) ≤ (N1 : ℝ) := Nat.le_ceil _
          exact_mod_cast lt_of_lt_of_le hlt hceil
        have hcard_le : (R1.card : ℝ) ≤ (N1 : ℝ) := by
          exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
        have hN1_lt : (N1 : ℝ) < 5 * Real.log (Real.log ((k : ℝ) + 16)) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have : (R1.card : ℝ) ≤ 6 * Real.log (Real.log ((k : ℝ) + 16)) := by linarith
        have : Real.log (Real.log ((k : ℝ) + 16)) ≤ Φ := by dsimp [Φ]; nlinarith
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp only [Finset.card_empty, Nat.cast_zero]; positivity
    calc ∑ t ∈ R1, psiNat (g_kt k t)
        ≤ ∑ _t ∈ R1, psiNat (Real.log 2 / 8) := Finset.sum_le_sum hterm
      _ = (R1.card : ℝ) * psiNat (Real.log 2 / 8) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (6 * Φ) * psiNat (Real.log 2 / 8) := by
          apply mul_le_mul_of_nonneg_right hcard_R1
          exact (psiNat_pos (by positivity) (by linarith)).le
      _ = K1 * Φ := by dsimp [K1]; ring
  -- Regime 2 bound: ≤ K2 * Φ
  have hR2 : ∑ t ∈ R2, psiNat (g_kt k t) ≤ K2 * Φ := by
    by_cases hne : R2.Nonempty
    · rcases hne with ⟨t_ex, ht_ex⟩
      rw [Finset.mem_filter] at ht_ex
      have hx32 : 32 ≤ x := hx_ge32 t_ex ht_ex.1 ht_ex.2.1
      have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
      have hlogx_ge3 : (3 : ℝ) < Real.log (x : ℝ) := by
        have h32 : (32 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx32
        have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
          rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; ring
        have := Real.log_two_gt_d9
        linarith [Real.log_le_log (by norm_num) h32]
      have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith
      -- Define t2 = Nat.log2 (Nat.floor ((c0 / 2) * x))
      set M_hi : ℕ := Nat.floor ((c0 / 2) * (x : ℝ))
      have hM_hi_ge64 : 64 ≤ M_hi := by
        have h1 : (64 : ℝ) ≤ ((2 ^ t_ex : ℕ) : ℝ) := by exact_mod_cast le_trans hM0_64 ht_ex.2.1
        have h2 : (64 : ℝ) ≤ (c0 / 2) * (x : ℝ) := le_trans h1 ht_ex.2.2.2
        exact Nat.le_floor h2
      set t2 : ℕ := Nat.log2 M_hi
      have h2t2_le : ((2 ^ t2 : ℕ) : ℝ) ≤ (c0 / 2) * (x : ℝ) := by
        have h1 : 2 ^ t2 ≤ M_hi := (Nat.le_log2 (by omega)).mp le_rfl
        exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
      have ht_le_t2 : ∀ t ∈ R2, t ≤ t2 := by
        intro t ht
        rw [Finset.mem_filter] at ht
        have hle_M : 2 ^ t ≤ M_hi := Nat.le_floor ht.2.2.2
        exact (Nat.le_log2 (by omega)).mpr hle_M
      have ht2_lt_2logx : (t2 : ℝ) ≤ 2 * Real.log (x : ℝ) := by
        have h2t2_lt_x : ((2 ^ t2 : ℕ) : ℝ) ≤ (x : ℝ) := by nlinarith
        have hlog := Real.log_le_log (by positivity) h2t2_lt_x
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
        have := Real.log_two_gt_d9
        nlinarith
      -- Pointwise bound on psiNat (g_kt k t) for t ∈ R2 in terms of u = t2 - t + 1
      have hpt : ∀ t ∈ R2,
          psiNat (g_kt k t) ≤
            (10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ))) * (1 / ((t2 - t + 1 : ℕ) : ℝ)) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        have ht_lt : t < numScales k := Finset.mem_range.mp ht.1
        set m := 2 ^ t
        have hm_64 : 64 ≤ m := le_trans hM0_64 ht.2.1
        have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
        set s := Nat.log x (2 ^ m - 1)
        have h2m_ne : 2 ^ m - 1 ≠ 0 := by
          have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (Nat.one_le_two_pow)
          omega
        -- Bound s from below and above
        have hs_upper : (s : ℝ) < (m : ℝ) * Real.log 2 / Real.log (x : ℝ) := by
          have hpow : x ^ s < 2 ^ m := by
            have h1 : x ^ s ≤ 2 ^ m - 1 := Nat.pow_log_le_self x h2m_ne
            have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
            omega
          have hlog : Real.log ((x ^ s : ℕ) : ℝ) < Real.log ((2 ^ m : ℕ) : ℝ) :=
            Real.log_lt_log (by positivity) (by exact_mod_cast hpow)
          rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Real.log_pow] at hlog
          rwa [lt_div_iff₀ hlogx_pos]
        have hs_lower1 : (m : ℝ) * Real.log 2 / Real.log (x : ℝ) ≤ (s : ℝ) + 1 := by
          have hpow : 2 ^ m ≤ x ^ (s + 1) := by
            have h1 : 2 ^ m - 1 < x ^ (s + 1) := Nat.lt_pow_succ_log_self (by omega) (2 ^ m - 1)
            omega
          have hlog : Real.log ((2 ^ m : ℕ) : ℝ) ≤ Real.log ((x ^ (s + 1) : ℕ) : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hpow)
          rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Real.log_pow] at hlog
          push_cast at hlog
          rwa [div_le_iff₀ hlogx_pos]
        have hs_ge2 : 2 ≤ s := by
          have h2 : (2 : ℝ) < (m : ℝ) * Real.log 2 / Real.log (x : ℝ) := by
            rw [lt_div_iff₀ hlogx_pos]; linarith [ht.2.2.1]
          have : (1 : ℝ) < (s : ℝ) := by linarith
          exact_mod_cast (by linarith : (1 : ℝ) < (s : ℝ))
        have hs_ge_half : (m : ℝ) * Real.log 2 / (2 * Real.log (x : ℝ)) ≤ (s : ℝ) := by
          have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge2
          have : ((s : ℝ) + 1) / 2 ≤ (s : ℝ) := by linarith
          linarith [show (m : ℝ) * Real.log 2 / (2 * Real.log (x : ℝ)) =
            ((m : ℝ) * Real.log 2 / Real.log (x : ℝ)) / 2 by ring]
        -- Check Candidate B validity: s ≤ oddPrimeCounting x
        have hN_ge : c0 * (x : ℝ) / Real.log (x : ℝ) ≤ (oddPrimeCounting x : ℝ) := hodd_pi x (by omega)
        have hN_div_s : c0 * (x : ℝ) / (m : ℝ) ≤ (oddPrimeCounting x : ℝ) / (s : ℝ) := by
          have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
          rw [div_le_div_iff₀ hm_pos hs_pos]
          have hs_lt_m : (s : ℝ) * Real.log (x : ℝ) ≤ (m : ℝ) := by
            have h1 : (s : ℝ) * Real.log (x : ℝ) < (m : ℝ) * Real.log 2 := (lt_div_iff₀ hlogx_pos).mp hs_upper
            nlinarith
          have h2 : c0 * (x : ℝ) ≤ (oddPrimeCounting x : ℝ) * Real.log (x : ℝ) := (div_le_iff₀ hlogx_pos).mp hN_ge
          nlinarith
        have h2_le_cxm : (2 : ℝ) ≤ c0 * (x : ℝ) / (m : ℝ) := by
          rw [le_div_iff₀ hm_pos]; linarith [ht.2.2.2]
        have hs_le_N : s ≤ oddPrimeCounting x := by
          have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
          have h1 : (2 : ℝ) ≤ (oddPrimeCounting x : ℝ) / (s : ℝ) := le_trans h2_le_cxm hN_div_s
          rw [le_div_iff₀ hs_pos] at h1
          exact_mod_cast (by linarith : (s : ℝ) ≤ (oddPrimeCounting x : ℝ))
        -- Apply Candidate B cardinality & pow_le_pow_mul_choose'
        have hcard_B : ((oddPrimeCounting x : ℝ) / (s : ℝ)) ^ s ≤ ((D_kt k t).card : ℝ) := by
          have h1 := card_candB (x := x) (m := m) (by omega) (by omega) hs_le_N
          have h2 := card_candB_le_D_kt k t
          have h3 : (oddPrimeCounting x) ^ s ≤ s ^ s * Nat.choose (oddPrimeCounting x) s :=
            pow_le_pow_mul_choose' hs_le_N
          have h3r : ((oddPrimeCounting x : ℝ)) ^ s ≤ ((s : ℝ)) ^ s * ((Nat.choose (oddPrimeCounting x) s : ℕ) : ℝ) := by
            exact_mod_cast h3
          have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
          have hdiv : ((oddPrimeCounting x : ℝ) / (s : ℝ)) ^ s ≤ ((Nat.choose (oddPrimeCounting x) s : ℕ) : ℝ) := by
            rw [div_pow, div_le_iff₀ (pow_pos hs_pos s)]
            linarith
          have h4 : ((Nat.choose (oddPrimeCounting x) s : ℕ) : ℝ) ≤ ((D_kt k t).card : ℝ) := by
            exact_mod_cast (h1 ▸ h2)
          linarith
        have hcard_ge_pow : (c0 * (x : ℝ) / (m : ℝ)) ^ s ≤ ((D_kt k t).card : ℝ) :=
          le_trans (pow_le_pow_left₀ (by positivity) hN_div_s s) hcard_B
        -- Bound c0 * x / m ≥ 2^(t2 - t + 1)
        set u := t2 - t + 1
        have ht_le : t ≤ t2 := ht_le_t2 t (Finset.mem_filter.mpr ht)
        have hcxm_ge_2u : ((2 ^ u : ℕ) : ℝ) ≤ c0 * (x : ℝ) / (m : ℝ) := by
          rw [le_div_iff₀ hm_pos]
          have hpow : 2 ^ u * m = 2 * 2 ^ t2 := by
            dsimp [u, m]; rw [← pow_add, show t2 - t + 1 + t = t2 + 1 by omega, pow_succ, mul_comm]
          have hcast : ((2 ^ u : ℕ) : ℝ) * (m : ℝ) = 2 * ((2 ^ t2 : ℕ) : ℝ) := by exact_mod_cast hpow
          linarith
        have hlog_card_ge : (s : ℝ) * ((u : ℝ) * Real.log 2) ≤ Real.log ((D_kt k t).card : ℝ) := by
          have h1 : Real.log ((c0 * (x : ℝ) / (m : ℝ)) ^ s) ≤ Real.log ((D_kt k t).card : ℝ) :=
            Real.log_le_log (by positivity) hcard_ge_pow
          rw [Real.log_pow] at h1
          have h2 : (u : ℝ) * Real.log 2 ≤ Real.log (c0 * (x : ℝ) / (m : ℝ)) := by
            have h3 := Real.log_le_log (by positivity) hcxm_ge_2u
            rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h3
          have hs_nn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
          nlinarith
        have hg_ge : (u : ℝ) / (10 * Real.log (x : ℝ)) ≤ g_kt k t := by
          unfold g_kt
          have hlog_div : (u : ℝ) / (10 * Real.log (x : ℝ)) ≤ Real.log ((D_kt k t).card : ℝ) / (2 * (m : ℝ)) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hlog2_sq : (4 / 10 : ℝ) ≤ (Real.log 2) ^ 2 := by
              have := Real.log_two_gt_d9; nlinarith
            have hstep1 : (m : ℝ) * (Real.log 2) ^ 2 * (u : ℝ) / (2 * Real.log (x : ℝ)) ≤
                Real.log ((D_kt k t).card : ℝ) := by
              have hu_nn : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
              have hmul := mul_le_mul_of_nonneg_right hs_ge_half (mul_nonneg hu_nn hlog2_pos.le)
              calc (m : ℝ) * (Real.log 2) ^ 2 * (u : ℝ) / (2 * Real.log (x : ℝ))
                  = (m : ℝ) * Real.log 2 / (2 * Real.log (x : ℝ)) * ((u : ℝ) * Real.log 2) := by ring
                _ ≤ (s : ℝ) * ((u : ℝ) * Real.log 2) := hmul
                _ ≤ Real.log ((D_kt k t).card : ℝ) := hlog_card_ge
            have hstep2 : (m : ℝ) * (Real.log 2) ^ 2 * (u : ℝ) ≤
                2 * Real.log (x : ℝ) * Real.log ((D_kt k t).card : ℝ) := by
              have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (x : ℝ))).mp hstep1
              linarith
            have hmu_nn : (0 : ℝ) ≤ (m : ℝ) * (u : ℝ) := mul_nonneg hm_pos.le (Nat.cast_nonneg u)
            nlinarith
          have hlog_le_g : Real.log ((D_kt k t).card : ℝ) / (2 * (m : ℝ)) ≤
              (Real.log 2 + Real.log ((D_kt k t).card : ℝ) / 2) / (m : ℝ) := by
            have hrew : Real.log ((D_kt k t).card : ℝ) / (2 * (m : ℝ)) =
                (Real.log ((D_kt k t).card : ℝ) / 2) / (m : ℝ) := by ring
            rw [hrew]
            exact div_le_div_of_nonneg_right (by linarith) hm_pos.le
          linarith
        have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
        have hv_pos : 0 < (u : ℝ) / (10 * Real.log (x : ℝ)) := div_pos hu_pos (by positivity)
        have hpsi_le := psiNat_anti hv_pos hg_ge (g_kt_le_one hk ht_lt)
        -- Simplify psiNat (u / (10 * log x))
        have hpsi_simp : psiNat ((u : ℝ) / (10 * Real.log (x : ℝ))) ≤
            (10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ))) * (1 / (u : ℝ)) := by
          unfold psiNat
          have hdiv_eq : 4 / ((u : ℝ) / (10 * Real.log (x : ℝ))) = 40 * Real.log (x : ℝ) / (u : ℝ) := by
            field_simp [hu_pos.ne', hlogx_pos.ne']; ring
          rw [hdiv_eq]
          have hlog_le : Real.log (40 * Real.log (x : ℝ) / (u : ℝ)) ≤ Real.log (40 * Real.log (x : ℝ)) := by
            apply Real.log_le_log (by positivity)
            exact div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ u))
          have hmul_eq : Real.log (40 * Real.log (x : ℝ) / (u : ℝ)) / ((u : ℝ) / (10 * Real.log (x : ℝ))) =
              (10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ) / (u : ℝ))) * (1 / (u : ℝ)) := by
            field_simp [hu_pos.ne', hlogx_pos.ne']
          rw [hmul_eq]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog_le (by positivity)) (by positivity)
        exact le_trans hpsi_le hpsi_simp
      -- Sum over R2 by injecting t ↦ t2 - t + 1 into Icc 1 (t2 + 1)
      have hsum_R2 : ∑ t ∈ R2, psiNat (g_kt k t) ≤
          (10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ))) *
            (∑ u ∈ Finset.Icc 1 (t2 + 1), (1 : ℝ) / (u : ℝ)) := by
        calc ∑ t ∈ R2, psiNat (g_kt k t)
            ≤ ∑ t ∈ R2, (10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ))) *
                (1 / ((t2 - t + 1 : ℕ) : ℝ)) := Finset.sum_le_sum hpt
          _ = (10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ))) *
                (∑ t ∈ R2, (1 : ℝ) / ((t2 - t + 1 : ℕ) : ℝ)) := by rw [← Finset.mul_sum]
          _ ≤ (10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ))) *
                (∑ u ∈ Finset.Icc 1 (t2 + 1), (1 : ℝ) / (u : ℝ)) := by
              have hcoef_nn : 0 ≤ 10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ)) := by
                have : 1 ≤ 40 * Real.log (x : ℝ) := by linarith
                exact mul_nonneg (by positivity) (Real.log_nonneg this)
              apply mul_le_mul_of_nonneg_left _ hcoef_nn
              have hinj : ∑ t ∈ R2, (1 : ℝ) / ((t2 - t + 1 : ℕ) : ℝ) =
                  ∑ u ∈ R2.image (fun t => t2 - t + 1), (1 : ℝ) / (u : ℝ) := by
                symm
                apply Finset.sum_image
                intro a ha b hb hab
                have ha_le := ht_le_t2 a ha
                have hb_le := ht_le_t2 b hb
                dsimp only at hab
                omega
              rw [hinj]
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro u hu
                rw [Finset.mem_image] at hu
                rcases hu with ⟨t, ht, rfl⟩
                rw [Finset.mem_Icc]; omega
              · intro u _ _; positivity
      -- Bound each factor by log (k+2) and log (log (k+16))
      have hharm : ∑ u ∈ Finset.Icc 1 (t2 + 1), (1 : ℝ) / (u : ℝ) ≤ 1 + Real.log ((t2 + 1 : ℕ) : ℝ) :=
        harmonic_sum_le_one_add_log (by omega)
      have hlogx_le_k : Real.log (x : ℝ) ≤ Real.log ((k : ℝ) + 2) :=
        Real.log_le_log hx_pos (by exact_mod_cast (by omega : x ≤ k + 2))
      have hlogx_le_16 : Real.log (x : ℝ) ≤ Real.log ((k : ℝ) + 16) :=
        Real.log_le_log hx_pos (by exact_mod_cast (by omega : x ≤ k + 16))
      have hll_x : Real.log (Real.log (x : ℝ)) ≤ Real.log (Real.log ((k : ℝ) + 16)) :=
        Real.log_le_log hlogx_pos hlogx_le_16
      have hlog40 : Real.log (40 * Real.log (x : ℝ)) ≤ 5 * Real.log (Real.log ((k : ℝ) + 16)) := by
        rw [Real.log_mul (by norm_num) hlogx_pos.ne']
        have h40_lt : Real.log (40 : ℝ) < 4 := by
          have h64 : (40 : ℝ) < 2 ^ 6 := by norm_num
          have h1 : Real.log (40 : ℝ) < Real.log ((2 : ℝ) ^ 6) := Real.log_lt_log (by norm_num) h64
          rw [Real.log_pow] at h1
          -- 6 * log 2 ≈ 4.158, better: 40 < e^4 since e > 2.718 ⇒ e^4 > 54!
          have he := Real.exp_one_gt_d9
          have h40_e4 : (40 : ℝ) < Real.exp 4 := by
            have hpow : Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
            rw [hpow]
            have hlt : (2.718 : ℝ) ^ 4 < (Real.exp 1) ^ 4 :=
              pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
            linarith [show (40 : ℝ) < (2.718 : ℝ) ^ 4 by norm_num]
          have h2 := Real.log_lt_log (by norm_num) h40_e4
          rwa [Real.log_exp] at h2
        linarith
      have hharm_le : 1 + Real.log ((t2 + 1 : ℕ) : ℝ) ≤ 4 * Real.log (Real.log ((k : ℝ) + 16)) := by
        have ht2_1 : ((t2 + 1 : ℕ) : ℝ) ≤ 3 * Real.log ((k : ℝ) + 16) := by
          push_cast; linarith
        have hlog_t2 : Real.log ((t2 + 1 : ℕ) : ℝ) ≤ Real.log 3 + Real.log (Real.log ((k : ℝ) + 16)) := by
          have h1 := Real.log_le_log (by positivity) ht2_1
          have hlog16_pos : 0 < Real.log ((k : ℝ) + 16) :=
            Real.log_pos (by exact_mod_cast (by omega : 1 < k + 16))
          rwa [Real.log_mul (by norm_num) hlog16_pos.ne'] at h1
        have hlog3 : Real.log (3 : ℝ) < 2 := by
          have he := Real.exp_one_gt_d9
          have h3_e2 : (3 : ℝ) < Real.exp 2 := by
            have : Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
            rw [this]; nlinarith
          have h2 := Real.log_lt_log (by norm_num) h3_e2
          rwa [Real.log_exp] at h2
        linarith
      have hcoef1_nn : 0 ≤ 10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ)) := by
        have : 1 ≤ 40 * Real.log (x : ℝ) := by linarith
        exact mul_nonneg (by positivity) (Real.log_nonneg this)
      calc ∑ t ∈ R2, psiNat (g_kt k t)
          ≤ (10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ))) *
              (1 + Real.log ((t2 + 1 : ℕ) : ℝ)) :=
            le_trans hsum_R2 (mul_le_mul_of_nonneg_left hharm hcoef1_nn)
        _ ≤ (10 * Real.log ((k : ℝ) + 2) * (5 * Real.log (Real.log ((k : ℝ) + 16)))) *
              (4 * Real.log (Real.log ((k : ℝ) + 16))) := by
            have h1 : 10 * Real.log (x : ℝ) * Real.log (40 * Real.log (x : ℝ)) ≤
                10 * Real.log ((k : ℝ) + 2) * (5 * Real.log (Real.log ((k : ℝ) + 16))) := by
              have hlog40_nn : 0 ≤ Real.log (40 * Real.log (x : ℝ)) := Real.log_nonneg (by linarith)
              exact mul_le_mul (by linarith) hlog40 hlog40_nn (by positivity)
            exact mul_le_mul h1 hharm_le (by positivity) (by positivity)
        _ = K2 * Φ := by dsimp [K2, Φ]; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.sum_empty]; positivity
  -- Regime 3 bound: ≤ K3 * Φ
  have hR3 : ∑ t ∈ R3, psiNat (g_kt k t) ≤ K3 * Φ := by
    by_cases hne : R3.Nonempty
    · -- Bound R3.card ≤ N3
      let t_min := R3.min' hne
      have ht_min_mem : t_min ∈ R3 := Finset.min'_mem R3 hne
      have ht_min_prop := (Finset.mem_filter.mp ht_min_mem).2
      have hx32 : 32 ≤ x := hx_ge32 t_min (Finset.mem_filter.mp ht_min_mem).1 ht_min_prop.1
      have hcard_R3 : R3.card ≤ N3 := by
        have hsub : R3 ⊆ Finset.Ico t_min (t_min + N3) := by
          intro t ht
          rw [Finset.mem_Ico]
          have hge_min : t_min ≤ t := Finset.min'_le R3 t ht
          have ht_prop := Finset.mem_filter.mp ht
          have ht_lt : t < numScales k := Finset.mem_range.mp ht_prop.1
          have h2t_le_2x : 2 ^ t ≤ 2 * x := by
            have hhalf := half_two_pow_le_quarter hk ht_lt
            have hm_64 : 64 ≤ 2 ^ t := le_trans hM0_64 ht_prop.2.1
            have ht1 : 1 ≤ t := by
              by_contra h0; push Not at h0
              have : t = 0 := by omega
              subst this; simp at hm_64
            have h2dvd : 2 ∣ 2 ^ t := dvd_pow_self 2 (by omega)
            have : 2 ^ t / 2 * 2 = 2 ^ t := Nat.div_mul_cancel h2dvd
            omega
          have hpow_lt : ((2 ^ (t - t_min) : ℕ) : ℝ) < 4 / c0 := by
            have hmul : ((2 ^ (t - t_min) : ℕ) : ℝ) * ((2 ^ t_min : ℕ) : ℝ) = ((2 ^ t : ℕ) : ℝ) := by
              have : 2 ^ (t - t_min) * 2 ^ t_min = 2 ^ t := by rw [← pow_add, Nat.sub_add_cancel hge_min]
              exact_mod_cast this
            have h1 : (c0 / 2) * (x : ℝ) < ((2 ^ t_min : ℕ) : ℝ) := ht_min_prop.2
            have h2 : ((2 ^ t : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast h2t_le_2x
            have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
            have hpow_pos : (0 : ℝ) < ((2 ^ (t - t_min) : ℕ) : ℝ) := by positivity
            rw [lt_div_iff₀ hc0_pos]
            nlinarith
          have hlog_diff : ((t - t_min : ℕ) : ℝ) * Real.log 2 < Real.log (4 / c0) := by
            have h1 := Real.log_lt_log (by positivity) hpow_lt
            rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
          have hdiff_lt : ((t - t_min : ℕ) : ℝ) < (N3 : ℝ) := by
            have h1 : ((t - t_min : ℕ) : ℝ) < Real.log (4 / c0) / Real.log 2 :=
              (lt_div_iff₀ hlog2_pos).mpr hlog_diff
            have h2 : Real.log (4 / c0) / Real.log 2 ≤ (Nat.ceil (Real.log (4 / c0) / Real.log 2) : ℝ) :=
              Nat.le_ceil _
            dsimp [N3]; push_cast; linarith
          have hdiff_nat : t - t_min < N3 := by exact_mod_cast hdiff_lt
          omega
        exact le_trans (Finset.card_le_card hsub) (by rw [Nat.card_Ico]; omega)
      -- Pointwise bound via Candidate C
      have hterm : ∀ t ∈ R3, psiNat (g_kt k t) ≤
          (1 / (c1 * Real.log 2)) * (Real.log (4 / (c1 * Real.log 2)) + 2) * Φ := by
        intro t ht
        rw [Finset.mem_filter] at ht
        have ht_lt : t < numScales k := Finset.mem_range.mp ht.1
        set m := 2 ^ t
        have hm1 : 1 ≤ m := Nat.one_le_two_pow
        have hm_le_k : m ≤ k := two_pow_le_k_of_lt_numScales hk ht_lt
        have hg_ge : c1 * Real.log 2 / Real.log ((k : ℝ) + 2) ≤ g_kt k t := by
          have hC_card : (candC m).card = 2 ^ oddPrimeCounting (m / 2) :=
            card_divisors_oddPrimorial (m / 2)
          have hD_ge : ((2 ^ oddPrimeCounting (m / 2) : ℕ) : ℝ) ≤ ((D_kt k t).card : ℝ) := by
            exact_mod_cast (hC_card ▸ card_candC_le_D_kt k t)
          have hlog_ge : (oddPrimeCounting (m / 2) : ℝ) * Real.log 2 ≤ Real.log ((D_kt k t).card : ℝ) := by
            have h1 := Real.log_le_log (by positivity) hD_ge
            rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
          have hpr := hpref m hm1
          have hc1_le_raw : c1 ≤ c1_raw := min_le_left _ _
          have hlogm_le : Real.log ((m : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) :=
            Real.log_le_log (by positivity) (by exact_mod_cast (by omega : m + 2 ≤ k + 2))
          have hlogm_pos : 0 < Real.log ((m : ℝ) + 2) :=
            Real.log_pos (by exact_mod_cast (by omega : 1 < m + 2))
          have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
          have hstep1 : c1 * (m : ℝ) / Real.log ((k : ℝ) + 2) ≤ 1 + (oddPrimeCounting (m / 2) : ℝ) / 2 := by
            calc c1 * (m : ℝ) / Real.log ((k : ℝ) + 2)
                ≤ c1_raw * (m : ℝ) / Real.log ((m : ℝ) + 2) :=
                  div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hc1_le_raw hm_pos.le)
                    hlogm_pos hlogm_le
              _ ≤ 1 + (oddPrimeCounting (m / 2) : ℝ) / 2 := hpr
          unfold g_kt
          rw [div_le_div_iff₀ (by linarith) hm_pos]
          have hmul := mul_le_mul_of_nonneg_right hstep1 hlog2_pos.le
          have hmul2 : c1 * (m : ℝ) * Real.log 2 ≤ (1 + (oddPrimeCounting (m / 2) : ℝ) / 2) * Real.log 2 * Real.log ((k : ℝ) + 2) := by
            have := (div_le_iff₀ (by linarith : 0 < Real.log ((k : ℝ) + 2))).mp hstep1
            nlinarith
          nlinarith
        have hv_pos : 0 < c1 * Real.log 2 / Real.log ((k : ℝ) + 2) := div_pos (by positivity) (by linarith)
        have hpsi_le := psiNat_anti hv_pos hg_ge (g_kt_le_one hk ht_lt)
        have hpsi_simp : psiNat (c1 * Real.log 2 / Real.log ((k : ℝ) + 2)) ≤
            (1 / (c1 * Real.log 2)) * (Real.log (4 / (c1 * Real.log 2)) + 2) * Φ := by
          unfold psiNat
          have hlogk_pos : 0 < Real.log ((k : ℝ) + 2) := by linarith
          have hdiv_eq : 4 / (c1 * Real.log 2 / Real.log ((k : ℝ) + 2)) =
              (4 / (c1 * Real.log 2)) * Real.log ((k : ℝ) + 2) := by
            field_simp [hc1_pos.ne', hlog2_pos.ne', hlogk_pos.ne']
          rw [hdiv_eq, Real.log_mul (by positivity) hlogk_pos.ne']
          have hll_le : Real.log (Real.log ((k : ℝ) + 2)) ≤ Real.log (Real.log ((k : ℝ) + 16)) :=
            Real.log_le_log hlogk_pos (Real.log_le_log (by positivity) (by linarith))
          have hlog_bound : Real.log (4 / (c1 * Real.log 2)) + Real.log (Real.log ((k : ℝ) + 2)) ≤
              (Real.log (4 / (c1 * Real.log 2)) + 2) * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 := by
            have h4c1 : 1 ≤ 4 / (c1 * Real.log 2) := by rw [one_le_div (by positivity)]; nlinarith
            have hlog_nn : 0 ≤ Real.log (4 / (c1 * Real.log 2)) := Real.log_nonneg h4c1
            have hll_sq : 1 ≤ (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 := by nlinarith
            have hll_le_sq : Real.log (Real.log ((k : ℝ) + 16)) ≤ (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 := by nlinarith
            nlinarith
          have hrew : (Real.log (4 / (c1 * Real.log 2)) + Real.log (Real.log ((k : ℝ) + 2))) /
              (c1 * Real.log 2 / Real.log ((k : ℝ) + 2)) =
              (1 / (c1 * Real.log 2)) * Real.log ((k : ℝ) + 2) *
                (Real.log (4 / (c1 * Real.log 2)) + Real.log (Real.log ((k : ℝ) + 2))) := by
            field_simp [hc1_pos.ne', hlog2_pos.ne', hlogk_pos.ne']
          rw [hrew]
          dsimp [Φ]
          have h1 : 0 ≤ (1 / (c1 * Real.log 2)) * Real.log ((k : ℝ) + 2) := by positivity
          nlinarith
        exact le_trans hpsi_le hpsi_simp
      calc ∑ t ∈ R3, psiNat (g_kt k t)
          ≤ ∑ _t ∈ R3, (1 / (c1 * Real.log 2)) * (Real.log (4 / (c1 * Real.log 2)) + 2) * Φ :=
            Finset.sum_le_sum hterm
        _ = (R3.card : ℝ) * ((1 / (c1 * Real.log 2)) * (Real.log (4 / (c1 * Real.log 2)) + 2) * Φ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N3 : ℝ) * ((1 / (c1 * Real.log 2)) * (Real.log (4 / (c1 * Real.log 2)) + 2) * Φ) := by
            have h4c1 : 1 ≤ 4 / (c1 * Real.log 2) := by rw [one_le_div (by positivity)]; nlinarith
            have hlog_nn : 0 ≤ Real.log (4 / (c1 * Real.log 2)) := Real.log_nonneg h4c1
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_R3) (by positivity)
        _ = K3 * Φ := by dsimp [K3]; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.sum_empty]; positivity
  -- Combine all 4 regimes
  have hcomb : SigmaStar k ≤ (K0 + K1 + K2 + K3) * Φ := by linarith
  have hΦ_pos : 0 < Φ := by linarith
  have hmul : (K0 + K1 + K2 + K3) * Φ ≤ (K0 + K1 + K2 + K3 + 1) * Φ := by nlinarith
  calc SigmaStar k ≤ (K0 + K1 + K2 + K3 + 1) * Φ := le_trans hcomb hmul
    _ = (K0 + K1 + K2 + K3 + 1) * Real.log ((k : ℝ) + 2) * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 := by
        dsimp [Φ]; ring

/-! ## Part 4: Non-Uniform Dyadic Shift Mixture `Y_star` & Covering Theorem (Lemma 3B*) -/

/-- The scale-`t` base distribution `Z_star k t` on `Fin (2 ^ (2 ^ t))`. -/
noncomputable def Z_star (k t : ℕ) (hk : 2 ≤ k) (ht : t < numScales k) : PMF_Fin (2 ^ (2 ^ t)) :=
  divPMF (2 ^ t) (D_kt k t) (D_kt_nonempty k t)
    (fun _d hd => let h := D_kt_props hk ht hd; ⟨h.1, h.2.2.2⟩)

/-- Non-uniform weight for `(t, s) : ShiftIdx k`: `psiNat (g_kt k t) / (SigmaStar k * |shiftSet k t|)`. -/
noncomputable def shiftWeightStar (k : ℕ) (idx : ShiftIdx k) : ℝ :=
  psiNat (g_kt k idx.1.val) / (SigmaStar k * ((shiftSet k idx.1.val).card : ℝ))

lemma shiftWeightStar_nonneg {k : ℕ} (hk : 2 ≤ k) (idx : ShiftIdx k) :
    0 ≤ shiftWeightStar k idx := by
  unfold shiftWeightStar
  have h1 := (psiNat_pos (g_kt_pos k idx.1.val) (g_kt_le_one hk idx.1.isLt)).le
  have h2 := (SigmaStar_pos hk).le
  positivity

lemma shiftWeightStar_sum_one {k : ℕ} (hk : 2 ≤ k) :
    ∑ idx : ShiftIdx k, shiftWeightStar k idx = 1 := by
  rw [Fintype.sum_sigma]
  have hinner : ∀ t : Fin (numScales k),
      (∑ s : { s : ℕ // s ∈ shiftSet k t.val }, shiftWeightStar k ⟨t, s⟩) =
        psiNat (g_kt k t.val) / SigmaStar k := by
    intro t
    have hne : (shiftSet k t.val).Nonempty := shiftSet_nonempty (two_pow_le_k_of_lt_numScales hk t.isLt)
    have hcard_pos : (0 : ℝ) < ((shiftSet k t.val).card : ℝ) := Nat.cast_pos.mpr hne.card_pos
    have hconst : ∀ s : { s : ℕ // s ∈ shiftSet k t.val },
        shiftWeightStar k ⟨t, s⟩ = psiNat (g_kt k t.val) / (SigmaStar k * ((shiftSet k t.val).card : ℝ)) :=
      fun _ => rfl
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    field_simp [hcard_pos.ne', (SigmaStar_pos hk).ne']
  simp_rw [hinner]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun t => psiNat (g_kt k t))]
  exact div_self (SigmaStar_pos hk).ne'

/-- Component PMF at `idx = ⟨t, s⟩` using `Z_star k t`. -/
noncomputable def shiftPMFStar_at {k : ℕ} (hk : 2 ≤ k) (idx : ShiftIdx k) : PMF_Fin (2 ^ k) :=
  shiftPMF_gen k idx.1.val idx.2.val
    (by
      have hmem := (mem_shiftSet k idx.1.val idx.2.val).mp idx.2.property
      have hpow := two_pow_le_k_of_lt_numScales hk idx.1.isLt
      have hle := hmem.2.1
      omega)
    (Z_star k idx.1.val hk idx.1.isLt)

/-- Non-uniform 2-sided dyadic shift mixture `Y_star k hk` on `Fin (2^k)`. -/
noncomputable def Y_star (k : ℕ) (hk : 2 ≤ k) : PMF_Fin (2 ^ k) :=
  mixPMF (shiftWeightStar k) (shiftWeightStar_nonneg hk) (shiftWeightStar_sum_one hk) (shiftPMFStar_at hk)

set_option maxHeartbeats 600000 in
/-- Untagged entropy contraction for `Y_star` with exact rate `1 / (4 * SigmaStar k)`. -/
theorem Hnat_conv_Y_star_sub_ge (k : ℕ) (hk : 2 ≤ k) (X : PMF_Fin (2 ^ k)) :
    Hnat (convPMF (Nat.two_pow_pos k) X (Y_star k hk)) - Hnat X ≥
      (1 / (4 * SigmaStar k)) * ((k : ℝ) * Real.log 2 - Hnat X) := by
  have hN := Nat.two_pow_pos k
  have hmix : ∑ idx : ShiftIdx k, shiftWeightStar k idx * Hnat (convPMF hN X (shiftPMFStar_at hk idx)) ≤
      Hnat (convPMF hN X (Y_star k hk)) := by
    unfold Y_star
    rw [convPMF_mixPMF_right]
    exact Hnat_mixPMF_ge _ _ _ _
  have hsub_mix : Hnat (convPMF hN X (Y_star k hk)) - Hnat X ≥
      ∑ idx : ShiftIdx k, shiftWeightStar k idx * (Hnat (convPMF hN X (shiftPMFStar_at hk idx)) - Hnat X) := by
    have h1 : ∑ idx : ShiftIdx k, shiftWeightStar k idx * (Hnat (convPMF hN X (shiftPMFStar_at hk idx)) - Hnat X) =
        (∑ idx : ShiftIdx k, shiftWeightStar k idx * Hnat (convPMF hN X (shiftPMFStar_at hk idx))) - Hnat X := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, shiftWeightStar_sum_one hk, one_mul]
    linarith
  have hstep2 : ∑ idx : ShiftIdx k, shiftWeightStar k idx * (Hnat (convPMF hN X (shiftPMFStar_at hk idx)) - Hnat X) ≥
      ∑ j : Fin k, (Real.log 2 - condBitEnt X j.val) *
        (∑ idx : ShiftIdx k, shiftWeightStar k idx * f4nat (condBitEnt (shiftPMFStar_at hk idx) j.val)) := by
    have h1 : ∑ idx : ShiftIdx k, shiftWeightStar k idx * (Hnat (convPMF hN X (shiftPMFStar_at hk idx)) - Hnat X) ≥
        ∑ idx : ShiftIdx k, shiftWeightStar k idx *
          (∑ j : Fin k, f4nat (condBitEnt (shiftPMFStar_at hk idx) j.val) * (Real.log 2 - condBitEnt X j.val)) := by
      apply Finset.sum_le_sum; intro idx _
      exact mul_le_mul_of_nonneg_left (Hnat_conv_sub_ge_bitwise_f4nat X (shiftPMFStar_at hk idx))
        (shiftWeightStar_nonneg hk idx)
    refine le_trans ?_ h1
    apply le_of_eq
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro idx _; ring
  -- Lower bound the inner sum for each bit j : Fin k by 1 / (4 * SigmaStar k)
  have hinner_ge : ∀ j : Fin k,
      1 / (4 * SigmaStar k) ≤
        ∑ idx : ShiftIdx k, shiftWeightStar k idx * f4nat (condBitEnt (shiftPMFStar_at hk idx) j.val) := by
    intro j
    have hcov := shiftSet_coverage k j.val hk j.isLt
    dsimp only at hcov
    set m_j := min (j.val + 1) (k - j.val)
    set t_star := Nat.log2 m_j
    have ht_lt : t_star < numScales k := by unfold numScales; omega
    let tFin : Fin (numScales k) := ⟨t_star, ht_lt⟩
    -- Drop all t ≠ tFin
    have hdrop_t : ∑ s : { s : ℕ // s ∈ shiftSet k tFin.val },
        shiftWeightStar k ⟨tFin, s⟩ * f4nat (condBitEnt (shiftPMFStar_at hk ⟨tFin, s⟩) j.val) ≤
        ∑ idx : ShiftIdx k, shiftWeightStar k idx * f4nat (condBitEnt (shiftPMFStar_at hk idx) j.val) := by
      rw [Fintype.sum_sigma]
      exact Finset.single_le_sum (f := fun t : Fin (numScales k) =>
        ∑ s : { s : ℕ // s ∈ shiftSet k t.val },
          shiftWeightStar k ⟨t, s⟩ * f4nat (condBitEnt (shiftPMFStar_at hk ⟨t, s⟩) j.val))
        (fun t _ => Finset.sum_nonneg fun s _ => by
          have hcb := condBitEnt_bounds (shiftPMFStar_at hk ⟨t, s⟩) j.val
          exact mul_nonneg (shiftWeightStar_nonneg hk ⟨t, s⟩)
            (f4nat_nonneg hcb.1 (le_trans hcb.2 (by linarith [Real.log_two_lt_d9]))))
        (Finset.mem_univ tFin)
    -- Restrict s to the 2^t_star shifts covering j: s = j - i for i ∈ Fin (2^t_star)
    have hpow_le_j1 : 2 ^ t_star ≤ j.val + 1 := by
      have hm_pos : 0 < m_j := by dsimp [m_j]; omega
      have h1 : 2 ^ t_star ≤ m_j := (Nat.le_log2 (Nat.ne_of_gt hm_pos)).mp le_rfl
      exact le_trans h1 (min_le_left _ _)
    have hshift_sum : (∑ i : Fin (2 ^ t_star),
        psiNat (g_kt k t_star) / (SigmaStar k * ((shiftSet k t_star).card : ℝ)) *
          f4nat (condBitEnt (Z_star k t_star hk ht_lt) i.val)) ≤
        ∑ s : { s : ℕ // s ∈ shiftSet k t_star },
          shiftWeightStar k ⟨tFin, s⟩ * f4nat (condBitEnt (shiftPMFStar_at hk ⟨tFin, s⟩) j.val) := by
      let emb : Fin (2 ^ t_star) ↪ { s : ℕ // s ∈ shiftSet k t_star } :=
        { toFun := fun i => ⟨j.val - i.val, hcov.2.2 (j.val - i.val) (by omega) (by omega)⟩
          inj' := fun i₁ i₂ h => by
            have hv : j.val - i₁.val = j.val - i₂.val := congrArg Subtype.val h
            apply Fin.ext; omega }
      calc ∑ i : Fin (2 ^ t_star),
              psiNat (g_kt k t_star) / (SigmaStar k * ((shiftSet k t_star).card : ℝ)) *
                f4nat (condBitEnt (Z_star k t_star hk ht_lt) i.val)
          = ∑ i : Fin (2 ^ t_star),
              shiftWeightStar k ⟨tFin, emb i⟩ * f4nat (condBitEnt (shiftPMFStar_at hk ⟨tFin, emb i⟩) j.val) := by
            apply Finset.sum_congr rfl; intro i _
            have hcb_eq : condBitEnt (shiftPMFStar_at hk ⟨tFin, emb i⟩) j.val =
                condBitEnt (Z_star k t_star hk ht_lt) i.val := by
              change condBitEnt (shiftPMF_gen k t_star (j.val - i.val) _ (Z_star k t_star hk ht_lt)) j.val =
                condBitEnt (Z_star k t_star hk ht_lt) i.val
              rw [condBitEnt_shiftPMF_gen k t_star (j.val - i.val) j.val _ (by omega)]
              have : j.val - (j.val - i.val) = i.val := by omega
              rw [this]
            rw [hcb_eq]; rfl
        _ = ∑ s ∈ Finset.univ.map emb,
              shiftWeightStar k ⟨tFin, s⟩ * f4nat (condBitEnt (shiftPMFStar_at hk ⟨tFin, s⟩) j.val) := by
            rw [Finset.sum_map]
        _ ≤ ∑ s : { s : ℕ // s ∈ shiftSet k t_star },
              shiftWeightStar k ⟨tFin, s⟩ * f4nat (condBitEnt (shiftPMFStar_at hk ⟨tFin, s⟩) j.val) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro s _ _
            have hcb := condBitEnt_bounds (shiftPMFStar_at hk ⟨tFin, s⟩) j.val
            exact mul_nonneg (shiftWeightStar_nonneg hk ⟨tFin, s⟩)
              (f4nat_nonneg hcb.1 (le_trans hcb.2 (by linarith [Real.log_two_lt_d9])))
    -- Apply Jensen on convex f4nat to average of condBitEnt (Z_star k t_star) over Fin (2^t_star)
    have hcard_St_pos : (0 : ℝ) < ((shiftSet k t_star).card : ℝ) :=
      Nat.cast_pos.mpr (shiftSet_nonempty hcov.1).card_pos
    have hcard_St_le : ((shiftSet k t_star).card : ℝ) ≤ 4 * ((2 ^ t_star : ℕ) : ℝ) := by
      exact_mod_cast shiftSet_card_le k t_star
    have h2t_pos : (0 : ℝ) < ((2 ^ t_star : ℕ) : ℝ) := by positivity
    have hjens : f4nat (g_kt k t_star) ≤
        ∑ i : Fin (2 ^ t_star), (1 / ((2 ^ t_star : ℕ) : ℝ)) * f4nat (condBitEnt (Z_star k t_star hk ht_lt) i.val) := by
      have h := convexOn_f4nat.map_sum_le
        (t := (Finset.univ : Finset (Fin (2 ^ t_star))))
        (w := fun _ => (1 : ℝ) / ((2 ^ t_star : ℕ) : ℝ))
        (p := fun i => condBitEnt (Z_star k t_star hk ht_lt) i.val)
        (fun _ _ => by positivity)
        (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp [h2t_pos.ne'])
        (fun i _ => let hc := condBitEnt_bounds (Z_star k t_star hk ht_lt) i.val
          ⟨hc.1, le_trans hc.2 (by linarith [Real.log_two_lt_d9])⟩)
      simp only [smul_eq_mul] at h
      have havg : ∑ i : Fin (2 ^ t_star), (1 / ((2 ^ t_star : ℕ) : ℝ)) * condBitEnt (Z_star k t_star hk ht_lt) i.val =
          g_kt k t_star := by
        rw [← Finset.mul_sum, ← Hnat_eq_sum_condBitEnt, Z_star, Hnat_divPMF]
        unfold g_kt; ring
      rwa [havg] at h
    have hcancel : psiNat (g_kt k t_star) * f4nat (g_kt k t_star) = 1 :=
      psiNat_mul_f4nat (g_kt_pos k t_star) (g_kt_le_one hk ht_lt)
    have hpsi_pos : 0 < psiNat (g_kt k t_star) := psiNat_pos (g_kt_pos k t_star) (g_kt_le_one hk ht_lt)
    have hsig_pos : 0 < SigmaStar k := SigmaStar_pos hk
    have hfinal : 1 / (4 * SigmaStar k) ≤
        ∑ i : Fin (2 ^ t_star),
          psiNat (g_kt k t_star) / (SigmaStar k * ((shiftSet k t_star).card : ℝ)) *
            f4nat (condBitEnt (Z_star k t_star hk ht_lt) i.val) := by
      have hrew : (∑ i : Fin (2 ^ t_star),
            psiNat (g_kt k t_star) / (SigmaStar k * ((shiftSet k t_star).card : ℝ)) *
              f4nat (condBitEnt (Z_star k t_star hk ht_lt) i.val)) =
          (psiNat (g_kt k t_star) * ((2 ^ t_star : ℕ) : ℝ) / (SigmaStar k * ((shiftSet k t_star).card : ℝ))) *
            (∑ i : Fin (2 ^ t_star), (1 / ((2 ^ t_star : ℕ) : ℝ)) *
              f4nat (condBitEnt (Z_star k t_star hk ht_lt) i.val)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        field_simp [h2t_pos.ne', hsig_pos.ne', hcard_St_pos.ne']
      rw [hrew]
      calc 1 / (4 * SigmaStar k)
          = (psiNat (g_kt k t_star) / (4 * SigmaStar k)) * f4nat (g_kt k t_star) := by
            rw [div_mul_eq_mul_div, hcancel]
        _ ≤ (psiNat (g_kt k t_star) * ((2 ^ t_star : ℕ) : ℝ) / (SigmaStar k * ((shiftSet k t_star).card : ℝ))) *
              f4nat (g_kt k t_star) := by
            apply mul_le_mul_of_nonneg_right _ (f4nat_nonneg (g_kt_pos k t_star).le (g_kt_le_one hk ht_lt))
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hps_nn : 0 ≤ psiNat (g_kt k t_star) * SigmaStar k := mul_nonneg hpsi_pos.le hsig_pos.le
            nlinarith
        _ ≤ (psiNat (g_kt k t_star) * ((2 ^ t_star : ℕ) : ℝ) / (SigmaStar k * ((shiftSet k t_star).card : ℝ))) *
              (∑ i : Fin (2 ^ t_star), (1 / ((2 ^ t_star : ℕ) : ℝ)) *
                f4nat (condBitEnt (Z_star k t_star hk ht_lt) i.val)) :=
            mul_le_mul_of_nonneg_left hjens (by positivity)
    exact le_trans hfinal (le_trans hshift_sum hdrop_t)
  -- Sum over j : Fin k
  have hsum_j : (1 / (4 * SigmaStar k)) * ((k : ℝ) * Real.log 2 - Hnat X) ≤
      ∑ j : Fin k, (Real.log 2 - condBitEnt X j.val) *
        (∑ idx : ShiftIdx k, shiftWeightStar k idx * f4nat (condBitEnt (shiftPMFStar_at hk idx) j.val)) := by
    have hdef_sum : (k : ℝ) * Real.log 2 - Hnat X = ∑ j : Fin k, (Real.log 2 - condBitEnt X j.val) := by
      rw [Hnat_eq_sum_condBitEnt, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    rw [hdef_sum, Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    have hdef_nn : 0 ≤ Real.log 2 - condBitEnt X j.val := by linarith [(condBitEnt_bounds X j.val).2]
    have h1 := mul_le_mul_of_nonneg_left (hinner_ge j) hdef_nn
    linarith
  linarith

/-- Tagged entropy contraction for `q * Y_star` (odd `q`). -/
theorem Hnat_conv_mulMod_star_sub_ge (k q : ℕ) (hk : 2 ≤ k) (hq : Odd q) (X : PMF_Fin (2 ^ k)) :
    Hnat (convPMF (Nat.two_pow_pos k) X (pushforwardEquiv (mulModEquiv k q hq) (Y_star k hk))) - Hnat X ≥
      (1 / (4 * SigmaStar k)) * ((k : ℝ) * Real.log 2 - Hnat X) := by
  let e := mulModEquiv k q hq
  let X' := pushforwardEquiv e.symm X
  have hX'_eq : pushforwardEquiv e X' = X := by
    ext x; dsimp [X', pushforwardEquiv]; simp
  have hconv_eq : convPMF (Nat.two_pow_pos k) X (pushforwardEquiv e (Y_star k hk)) =
      pushforwardEquiv e (convPMF (Nat.two_pow_pos k) X' (Y_star k hk)) := by
    rw [← convPMF_pushforward_mulMod k q hq X' (Y_star k hk), hX'_eq]
  rw [hconv_eq, Hnat_pushforwardEquiv e]
  have hHX : Hnat X' = Hnat X := Hnat_pushforwardEquiv e.symm X
  rw [← hHX]
  exact Hnat_conv_Y_star_sub_ge k hk X'

/-- Support characterization of `Y_star k hk`: every nonzero `y` has `y = 2^s * z` with `s < k`,
    `z ∣ oddPrimorial ((k+1)/4)`, `Odd z`. -/
lemma mem_supp_Y_star {k : ℕ} (hk : 2 ≤ k) {y : Fin (2 ^ k)} (hy : y ∈ suppFin (Y_star k hk)) :
    y.val = 0 ∨ (0 < y.val ∧ y.val < 2 ^ k ∧ ¬ (2 ^ k ∣ y.val) ∧
      ∃ s z : ℕ, s < k ∧ z ∣ oddPrimorial ((k + 1) / 4) ∧ Odd z ∧ y.val = 2 ^ s * z) := by
  by_cases hy0 : y.val = 0
  · exact Or.inl hy0
  · right
    unfold suppFin at hy; rw [Finset.mem_filter] at hy
    have hpos : 0 < (Y_star k hk).p y := hy.2
    unfold Y_star mixPMF at hpos
    have hex : ∃ idx : ShiftIdx k, 0 < shiftWeightStar k idx * (shiftPMFStar_at hk idx).p y := by
      by_contra hall; push Not at hall
      have hle : ∑ idx : ShiftIdx k, shiftWeightStar k idx * (shiftPMFStar_at hk idx).p y ≤ 0 :=
        Finset.sum_nonpos fun idx _ => hall idx
      linarith
    rcases hex with ⟨⟨t, ⟨s, hs⟩⟩, hterm⟩
    have hsp_pos : 0 < (shiftPMFStar_at hk ⟨t, ⟨s, hs⟩⟩).p y := by
      by_contra hle; push Not at hle
      have h0 : (shiftPMFStar_at hk ⟨t, ⟨s, hs⟩⟩).p y = 0 :=
        le_antisymm hle ((shiftPMFStar_at hk ⟨t, ⟨s, hs⟩⟩).nonneg y)
      rw [h0, mul_zero] at hterm; linarith
    dsimp only [shiftPMFStar_at, shiftPMF_gen] at hsp_pos
    split_ifs at hsp_pos with hdiv
    · rcases hdiv with ⟨hdvd_s, hlt_2t⟩
      set z := y.val / 2 ^ s
      have hy_eq : y.val = 2 ^ s * z := (Nat.mul_div_cancel' hdvd_s).symm
      have hz_ne0 : z ≠ 0 := by intro hz0; apply hy0; rw [hy_eq, hz0, mul_zero]
      dsimp only [Z_star, divPMF] at hsp_pos
      rw [ite_eq_right_iff.mpr (fun h => absurd h hz_ne0)] at hsp_pos
      split_ifs at hsp_pos with hz_mem
      · rcases D_kt_props hk t.isLt hz_mem with ⟨_, hz_odd, hz_dvd, _⟩
        have hs_lt : s < k := by
          have hmem := (mem_shiftSet k t.val s).mp hs
          have hpow := Nat.one_le_two_pow (n := t.val)
          have h2t_le := two_pow_le_k_of_lt_numScales hk t.isLt
          have := hmem.2.1
          omega
        have hndvd_2k : ¬ (2 ^ k ∣ y.val) := by
          intro h2k; have hle := Nat.le_of_dvd (by omega) h2k; omega
        exact ⟨by omega, y.isLt, hndvd_2k, s, z, hs_lt, hz_dvd, hz_odd, hy_eq⟩
      · linarith
    · linarith

/-- Iterated convolution of `tags.length` prime-tagged copies of `Y_star k hk`. -/
noncomputable def iterConvStar {k : ℕ} (hk : 2 ≤ k) (tags : List ℕ) (htags : ∀ q ∈ tags, Odd q) :
    PMF_Fin (2 ^ k) :=
  match tags with
  | [] => deltaZeroPMF k
  | q :: qs =>
    convPMF (Nat.two_pow_pos k)
      (iterConvStar hk qs (fun q' hq' => htags q' (List.mem_cons_of_mem q hq')))
      (pushforwardEquiv (mulModEquiv k q (htags q (List.mem_cons_self ..))) (Y_star k hk))

/-- Entropy deficit contraction across `iterConvStar`. -/
lemma iterConvStar_deficit_le {k : ℕ} (hk : 2 ≤ k)
    (tags : List ℕ) (htags : ∀ q ∈ tags, Odd q) :
    let α := 1 / (4 * SigmaStar k)
    (k : ℝ) * Real.log 2 - Hnat (iterConvStar hk tags htags) ≤
      Real.exp (-α * (tags.length : ℝ)) * ((k : ℝ) * Real.log 2) := by
  intro α
  induction tags with
  | nil => simp [iterConvStar, Hnat_deltaZero]
  | cons q qs ih =>
    have hq_odd : Odd q := htags q (List.mem_cons_self ..)
    have hqs_odd : ∀ q' ∈ qs, Odd q' := fun q' hq' => htags q' (List.mem_cons_of_mem q hq')
    let X := iterConvStar hk qs hqs_odd
    have hgain := Hnat_conv_mulMod_star_sub_ge k q hk hq_odd X
    have hstep : (k : ℝ) * Real.log 2 - Hnat (iterConvStar hk (q :: qs) htags) ≤
        (1 - α) * ((k : ℝ) * Real.log 2 - Hnat X) := by
      dsimp only [iterConvStar]; dsimp only [α] at hgain ⊢; linarith
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
    have h1_sub_le : 1 - α ≤ Real.exp (-α) := by linarith [Real.add_one_le_exp (-α)]
    have hih := ih hqs_odd
    calc (k : ℝ) * Real.log 2 - Hnat (iterConvStar hk (q :: qs) htags)
        ≤ (1 - α) * ((k : ℝ) * Real.log 2 - Hnat X) := hstep
      _ ≤ Real.exp (-α) * ((k : ℝ) * Real.log 2 - Hnat X) :=
          mul_le_mul_of_nonneg_right h1_sub_le hdef_nn
      _ ≤ Real.exp (-α) * (Real.exp (-α * (qs.length : ℝ)) * ((k : ℝ) * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hih (Real.exp_pos _).le
      _ = Real.exp (-α * (((q :: qs).length : ℕ) : ℝ)) * ((k : ℝ) * Real.log 2) := by
          rw [← mul_assoc, ← Real.exp_add]; congr 2
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- Support extraction for `iterConvStar`. -/
lemma iterConvStar_supp_representable {k Q_max : ℕ} (hk : 2 ≤ k)
    (tags : List ℕ) (hnodup : tags.Nodup)
    (hprimes : ∀ q ∈ tags, q.Prime ∧ (k + 1) / 4 < q ∧ q ≤ Q_max)
    (htags : ∀ q ∈ tags, Odd q) :
    ∀ u ∈ suppFin (iterConvStar hk tags htags),
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
    have hu0 : u.val = 0 := by
      by_contra h; rw [ite_eq_right_iff.mpr (fun h0 => absurd h0 h)] at hu'; linarith
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
    let e := mulModEquiv k q (htags q (List.mem_cons_self ..))
    have hb' : e.symm b ∈ suppFin (Y_star k hk) := by
      unfold suppFin at hb ⊢; rw [Finset.mem_filter] at hb ⊢
      exact ⟨Finset.mem_univ _, hb.2⟩
    rcases mem_supp_Y_star hk hb' with hby0 | ⟨hby_pos, hby_lt, _, s, z, hs_lt, hz_dvd, hz_odd, hby_eq⟩
    · have hb0 : b.val = 0 := by
        have hbe : b = e (e.symm b) := (Equiv.apply_symm_apply e b).symm
        rw [hbe, mulModEquiv_apply, hby0, mul_zero, Nat.zero_mod]
      refine ⟨S_a, le_trans hSa_card (by simp), ?_, ?_⟩
      · intro d hd
        rcases hSa_prop d hd with ⟨h1, h2, h3, h4, q', hq'm, hq'd, hq'u⟩
        exact ⟨h1, h2, h3, h4, q', List.mem_cons_of_mem q hq'm, hq'd, hq'u⟩
      · rw [← hab, hb0, add_zero, Nat.mod_eq_of_lt a.isLt] at *
        exact hSa_sum
    · let d_new := q * (e.symm b).val
      have hd_pos : 0 < d_new := Nat.mul_pos hq_info.1.pos hby_pos
      have hd_lt : d_new < Q_max * 2 ^ k := by
        calc d_new = q * (e.symm b).val := rfl
          _ ≤ Q_max * (e.symm b).val := Nat.mul_le_mul_right _ hq_info.2.2
          _ < Q_max * 2 ^ k := Nat.mul_lt_mul_of_pos_left hby_lt (by omega)
      have hd_dvd : d_new ∣ 2 ^ k * oddPrimorial Q_max := by
        have hq_ge3 : 3 ≤ q := by
          have := hq_info.1.two_le; have hq_odd := htags q (List.mem_cons_self ..)
          rw [Nat.odd_iff] at hq_odd; omega
        have hq_mem_Q : q ∈ (Finset.range (Q_max + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) := by
          simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hq_info.1, hq_ge3⟩
        have hsub_erase : (Finset.range ((k + 1) / 4 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) ⊆
            ((Finset.range (Q_max + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)).erase q := by
          intro p hp; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase] at hp ⊢
          exact ⟨by omega, by omega, hp.2.1, hp.2.2⟩
        have hqz_dvd : q * z ∣ oddPrimorial Q_max := by
          unfold oddPrimorial
          rw [← Finset.mul_prod_erase _ _ hq_mem_Q]
          exact Nat.mul_dvd_mul_left q (dvd_trans hz_dvd (Finset.prod_dvd_prod_of_subset _ _ id hsub_erase))
        have hd_eq : d_new = 2 ^ s * (q * z) := by dsimp [d_new]; rw [hby_eq]; ring
        rw [hd_eq]
        exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hs_lt.le) hqz_dvd
      have hd_ndvd_2k : ¬ (2 ^ k ∣ d_new) := by
        intro h2k
        have hcop : Nat.Coprime (2 ^ k) (q * z) := by
          apply Nat.Coprime.pow_left
          have hq_odd := htags q (List.mem_cons_self ..)
          have hqz_odd : Odd (q * z) := hq_odd.mul hz_odd
          rw [Nat.coprime_two_left]; exact hqz_odd
        have hd_eq : d_new = 2 ^ s * (q * z) := by dsimp [d_new]; rw [hby_eq]; ring
        rw [hd_eq] at h2k
        have h2k_s : 2 ^ k ∣ 2 ^ s := hcop.dvd_of_dvd_mul_right h2k
        have hle := Nat.le_of_dvd (Nat.two_pow_pos s) h2k_s
        have hlt := Nat.pow_lt_pow_right (by omega : 1 < 2) hs_lt
        omega
      have hd_uniq : ∀ q' : ℕ, q'.Prime → 3 ≤ q' → (k + 1) / 4 < q' → q' ∣ d_new → q' = q := by
        intro q' hq'p hq'3 hq'gt hq'd
        have hd_eq : d_new = q * (2 ^ s * z) := by dsimp [d_new]; rw [hby_eq]
        rw [hd_eq] at hq'd
        rcases hq'p.dvd_mul.mp hq'd with h1 | h2
        · exact (Nat.prime_dvd_prime_iff_eq hq'p hq_info.1).mp h1
        · rcases hq'p.dvd_mul.mp h2 with h2a | h2b
          · have h2p := hq'p.dvd_of_dvd_pow h2a
            have : q' = 2 := (Nat.prime_dvd_prime_iff_eq hq'p Nat.prime_two).mp h2p
            omega
          · have hq'P : q' ∣ oddPrimorial ((k + 1) / 4) := dvd_trans h2b hz_dvd
            unfold oddPrimorial at hq'P
            rcases prime_dvd_finset_prod hq'p hq'P with ⟨p, hp_mem, hq'p_dvd⟩
            simp only [Finset.mem_filter, Finset.mem_range] at hp_mem
            have : q' = p := (Nat.prime_dvd_prime_iff_eq hq'p hp_mem.2.1).mp hq'p_dvd
            omega
      have hd_not_mem : d_new ∉ S_a := by
        intro hmem
        rcases hSa_prop d_new hmem with ⟨_, _, _, _, q', hq'm, hq'd, _⟩
        have hq'i := hqs_primes q' hq'm
        have hq'3 : 3 ≤ q' := by
          have := hq'i.1.two_le; have ho := hqs_odd q' hq'm; rw [Nat.odd_iff] at ho; omega
        have heq := hd_uniq q' hq'i.1 hq'3 hq'i.2.1 hq'd
        exact hnodup.1 (heq ▸ hq'm)
      refine ⟨insert d_new S_a, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hd_not_mem, List.length_cons]; omega
      · intro d hd
        rw [Finset.mem_insert] at hd
        rcases hd with rfl | hd_old
        · exact ⟨hd_pos, hd_dvd, hd_ndvd_2k, hd_lt, q, List.mem_cons_self .., dvd_mul_right q _, hd_uniq⟩
        · rcases hSa_prop d hd_old with ⟨h1, h2, h3, h4, q', hq'm, hq'd, hq'u⟩
          exact ⟨h1, h2, h3, h4, q', List.mem_cons_of_mem q hq'm, hq'd, hq'u⟩
      · rw [Finset.sum_insert hd_not_mem, id_eq]
        have hb_val : d_new % 2 ^ k = b.val := by
          have hbe : b = e (e.symm b) := (Equiv.apply_symm_apply e b).symm
          rw [hbe, mulModEquiv_apply]
        calc (d_new + S_a.sum id) % 2 ^ k
            = (d_new % 2 ^ k + S_a.sum id % 2 ^ k) % 2 ^ k := Nat.add_mod _ _ _
          _ = (b.val + a.val) % 2 ^ k := by rw [hb_val, hSa_sum]
          _ = (a.val + b.val) % 2 ^ k := by rw [add_comm]
          _ = u.val := hab

/-- **Lemma 3B* (Composed Parametric Mod-2^k Covering)**:
    Every residue mod `2^k` is a sum of at most `2 * R` strictly distinct positive divisors of
    `2^k * oddPrimorial Q_max`, where `R = ⌈C_cov * (log (k + 2))^2 * (log (log (k + 16)))^2⌉`. -/
theorem mod_two_pow_covering_alpha3 :
    ∃ C_cov : ℝ, 0 < C_cov ∧
      ∀ (k Q_max : ℕ), 2 ≤ k → 3 ≤ Q_max →
        let R := Nat.ceil (C_cov * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2)
        2 * R ≤ oddPrimeCounting Q_max - oddPrimeCounting ((k + 1) / 4) →
        ∀ a : ℕ, ∃ S : Finset ℕ,
          S.card ≤ 2 * R ∧
          (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ k * oddPrimorial Q_max ∧ ¬ (2 ^ k ∣ d) ∧ d < Q_max * 2 ^ k) ∧
          S.sum id % 2 ^ k = a % 2 ^ k := by
  rcases SigmaStar_le with ⟨C_sig, hC_sig, hSigma⟩
  refine ⟨8 * C_sig, by positivity, ?_⟩
  intro k Q_max hk hQmax R hprimes_cnt a
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogk_pos : 0 < Real.log ((k : ℝ) + 2) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k + 2))
  have hlogk_ge1 : (1 : ℝ) ≤ Real.log ((k : ℝ) + 2) := by
    have h4 : (4 : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ k + 2)
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith [Real.log_le_log (by norm_num) h4, Real.log_two_gt_d9]
  have hll_gt1 : 1 < Real.log (Real.log ((k : ℝ) + 16)) := one_lt_log_log_add16 hk
  -- Extract 2 * R distinct odd primes in ((k+1)/4, Q_max]
  let P_pool : Finset ℕ :=
    (Finset.range (Q_max + 1)).filter (fun p => p.Prime ∧ 3 ≤ p ∧ (k + 1) / 4 < p)
  have hpool_card : 2 * R ≤ P_pool.card := by
    have hsub : (Finset.range ((k + 1) / 4 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) ⊆
        (Finset.range (Q_max + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) := by
      by_cases hle : (k + 1) / 4 ≤ Q_max
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
      · exfalso
        have hmono : oddPrimeCounting Q_max ≤ oddPrimeCounting ((k + 1) / 4) := by
          unfold oddPrimeCounting; apply Finset.card_le_card
          intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
        have hR_pos : 0 < R := Nat.ceil_pos.mpr (by positivity)
        omega
    have hsdiff : P_pool =
        ((Finset.range (Q_max + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)) \
        ((Finset.range ((k + 1) / 4 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)) := by
      ext p; simp only [P_pool, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]; constructor
      · rintro ⟨h1, hp, h3, hgt⟩; exact ⟨⟨h1, hp, h3⟩, fun h => by omega⟩
      · rintro ⟨⟨h1, hp, h3⟩, hnot⟩; refine ⟨h1, hp, h3, ?_⟩; by_contra hle; exact hnot ⟨by omega, hp, h3⟩
    rw [hsdiff, Finset.card_sdiff_of_subset hsub]
    exact hprimes_cnt
  let L_all := P_pool.toList
  have hL_nodup : L_all.Nodup := Finset.nodup_toList P_pool
  have hL_len : 2 * R ≤ L_all.length := by rw [Finset.length_toList]; exact hpool_card
  let tags1 := L_all.take R
  let tags2 := (L_all.drop R).take R
  have htags1_len : tags1.length = R := by simp [tags1, Nat.min_eq_left (by omega : R ≤ L_all.length)]
  have htags2_len : tags2.length = R := by simp [tags2, Nat.min_eq_left (by omega : R ≤ L_all.length - R)]
  have htags1_nodup : tags1.Nodup := hL_nodup.take
  have htags2_nodup : tags2.Nodup := hL_nodup.drop.take
  have htags_disj : ∀ q ∈ tags1, q ∉ tags2 := by
    intro q hq1 hq2
    have hsplit_eq : L_all = L_all.take R ++ L_all.drop R := (List.take_append_drop R L_all).symm
    have hnd := hL_nodup
    rw [hsplit_eq, List.nodup_append] at hnd
    exact hnd.2.2 q hq1 q (List.mem_of_mem_take hq2) rfl
  have hmem_pool : ∀ q ∈ L_all, q.Prime ∧ 3 ≤ q ∧ (k + 1) / 4 < q ∧ q ≤ Q_max := by
    intro q hq
    rw [Finset.mem_toList] at hq
    simp only [P_pool, Finset.mem_filter, Finset.mem_range] at hq
    exact ⟨hq.2.1, hq.2.2.1, hq.2.2.2, by omega⟩
  have htags1_primes : ∀ q ∈ tags1, q.Prime ∧ (k + 1) / 4 < q ∧ q ≤ Q_max := fun q hq =>
    let h := hmem_pool q (List.mem_of_mem_take hq); ⟨h.1, h.2.2.1, h.2.2.2⟩
  have htags2_primes : ∀ q ∈ tags2, q.Prime ∧ (k + 1) / 4 < q ∧ q ≤ Q_max := fun q hq =>
    let h := hmem_pool q (List.mem_of_mem_drop (List.mem_of_mem_take hq)); ⟨h.1, h.2.2.1, h.2.2.2⟩
  have htags1_odd : ∀ q ∈ tags1, Odd q := fun q hq =>
    let h := hmem_pool q (List.mem_of_mem_take hq); h.1.odd_of_ne_two (by omega)
  have htags2_odd : ∀ q ∈ tags2, Odd q := fun q hq =>
    let h := hmem_pool q (List.mem_of_mem_drop (List.mem_of_mem_take hq)); h.1.odd_of_ne_two (by omega)
  -- Show α * R ≥ log (2 * k)
  set α := 1 / (4 * SigmaStar k)
  have hαR_ge : Real.log (2 * (k : ℝ)) ≤ α * (R : ℝ) := by
    have hlog2k_le : Real.log (2 * (k : ℝ)) ≤ 2 * Real.log ((k : ℝ) + 2) := by
      have h1 : 2 * (k : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        nlinarith
      have h2 := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow] at h2
    have hR_ge : 8 * C_sig * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 ≤ (R : ℝ) :=
      Nat.le_ceil _
    have hSig_le := hSigma k hk
    have hSig_pos := SigmaStar_pos hk
    dsimp [α]
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    calc Real.log (2 * (k : ℝ)) * (4 * SigmaStar k)
        ≤ (2 * Real.log ((k : ℝ) + 2)) *
            (4 * (C_sig * Real.log ((k : ℝ) + 2) * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2)) :=
          mul_le_mul hlog2k_le (by linarith) (by positivity) (by positivity)
      _ = 8 * C_sig * (Real.log ((k : ℝ) + 2)) ^ 2 * (Real.log (Real.log ((k : ℝ) + 16))) ^ 2 := by ring
      _ ≤ (R : ℝ) := hR_ge
  -- Both iterConvStar distributions have support > 2^(k-1)
  have hsupp_gt : ∀ (tags : List ℕ) (htags : ∀ q ∈ tags, Odd q), tags.length = R →
      2 ^ (k - 1) < (suppFin (iterConvStar hk tags htags)).card := by
    intro tags htags hlen
    have hdef := iterConvStar_deficit_le hk tags htags
    rw [hlen] at hdef
    have hexp_le : Real.exp (-α * (R : ℝ)) ≤ 1 / (2 * (k : ℝ)) := by
      have h1 : -α * (R : ℝ) ≤ -Real.log (2 * (k : ℝ)) := by linarith
      calc Real.exp (-α * (R : ℝ)) ≤ Real.exp (-Real.log (2 * (k : ℝ))) := Real.exp_le_exp.mpr h1
        _ = (Real.exp (Real.log (2 * (k : ℝ))))⁻¹ := Real.exp_neg _
        _ = 1 / (2 * (k : ℝ)) := by rw [Real.exp_log (by positivity), one_div]
    have hdef_lt : (k : ℝ) * Real.log 2 - Hnat (iterConvStar hk tags htags) < Real.log 2 := by
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have h1 : Real.exp (-α * (R : ℝ)) * ((k : ℝ) * Real.log 2) ≤ Real.log 2 / 2 := by
        calc Real.exp (-α * (R : ℝ)) * ((k : ℝ) * Real.log 2)
            ≤ (1 / (2 * (k : ℝ))) * ((k : ℝ) * Real.log 2) :=
              mul_le_mul_of_nonneg_right hexp_le (by positivity)
          _ = Real.log 2 / 2 := by field_simp [hk_pos.ne']
      linarith
    have hH_le_log := Hnat_le_log_supp (iterConvStar hk tags htags)
    have hlog_gt : ((k - 1 : ℕ) : ℝ) * Real.log 2 < Real.log ((suppFin (iterConvStar hk tags htags)).card : ℝ) := by
      have hk_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : k - 1 + 1 = k := by omega
        have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast this
        linarith
      rw [hk_cast]; linarith
    have hpow_lt : ((2 ^ (k - 1) : ℕ) : ℝ) < ((suppFin (iterConvStar hk tags htags)).card : ℝ) := by
      by_contra hle; push Not at hle
      have hcard_pos : (0 : ℝ) < ((suppFin (iterConvStar hk tags htags)).card : ℝ) := by
        by_contra h0; push Not at h0
        have hcard0 : (suppFin (iterConvStar hk tags htags)).card = 0 := by
          have : (suppFin (iterConvStar hk tags htags)).card ≤ 0 := by exact_mod_cast h0
          omega
        rw [Finset.card_eq_zero] at hcard0
        have hsum0 : ∑ x : Fin (2 ^ k), (iterConvStar hk tags htags).p x = 0 := by
          apply Finset.sum_eq_zero; intro x _
          have hx : x ∉ suppFin (iterConvStar hk tags htags) := by rw [hcard0]; simp
          simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
          exact le_antisymm hx ((iterConvStar hk tags htags).nonneg x)
        linarith [(iterConvStar hk tags htags).sum_one]
      have hlog_le : Real.log ((suppFin (iterConvStar hk tags htags)).card : ℝ) ≤ Real.log ((2 ^ (k - 1) : ℕ) : ℝ) :=
        Real.log_le_log hcard_pos hle
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog_le
      linarith
    exact_mod_cast hpow_lt
  have hA_gt := hsupp_gt tags1 htags1_odd htags1_len
  have hB_gt := hsupp_gt tags2 htags2_odd htags2_len
  have hsum_gt : 2 ^ k < (suppFin (iterConvStar hk tags1 htags1_odd)).card +
      (suppFin (iterConvStar hk tags2 htags2_odd)).card := by
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ, mul_comm]
    omega
  let target : Fin (2 ^ k) := ⟨a % 2 ^ k, Nat.mod_lt a (Nat.two_pow_pos k)⟩
  rcases pigeonhole_finset_cover (Nat.two_pow_pos k)
    (suppFin (iterConvStar hk tags1 htags1_odd)) (suppFin (iterConvStar hk tags2 htags2_odd))
    hsum_gt target with ⟨u, hu, v, hv, huv⟩
  rcases iterConvStar_supp_representable hk tags1 htags1_nodup htags1_primes htags1_odd u hu with
    ⟨S1, hS1_card, hS1_prop, hS1_sum⟩
  rcases iterConvStar_supp_representable hk tags2 htags2_nodup htags2_primes htags2_odd v hv with
    ⟨S2, hS2_card, hS2_prop, hS2_sum⟩
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rcases hS1_prop d hd1 with ⟨_, _, _, _, q1, hq1m, hq1d, hq1u⟩
    rcases hS2_prop d hd2 with ⟨_, _, _, _, q2, hq2m, hq2d, _⟩
    have hq2i := htags2_primes q2 hq2m
    have hq2_3 : 3 ≤ q2 := by
      have := hq2i.1.two_le; have ho := htags2_odd q2 hq2m; rw [Nat.odd_iff] at ho; omega
    have heq := hq1u q2 hq2i.1 hq2_3 hq2i.2.1 hq2d
    exact htags_disj q1 hq1m (heq ▸ hq2m)
  refine ⟨S1 ∪ S2, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj]
    rw [htags1_len] at hS1_card; rw [htags2_len] at hS2_card; omega
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hd1 | hd2
    · rcases hS1_prop d hd1 with ⟨h1, h2, h3, h4, _⟩; exact ⟨h1, h2, h3, h4⟩
    · rcases hS2_prop d hd2 with ⟨h1, h2, h3, h4, _⟩; exact ⟨h1, h2, h3, h4⟩
  · rw [Finset.sum_union hdisj]
    calc (S1.sum id + S2.sum id) % 2 ^ k
        = (S1.sum id % 2 ^ k + S2.sum id % 2 ^ k) % 2 ^ k := Nat.add_mod _ _ _
      _ = (u.val + v.val) % 2 ^ k := by rw [hS1_sum, hS2_sum]
      _ = target.val := huv
      _ = a % 2 ^ k := rfl

end Erdos18

#print axioms Erdos18.SigmaStar_le
#print axioms Erdos18.mod_two_pow_covering_alpha3
