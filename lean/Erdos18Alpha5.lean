/-
  Erdos18Alpha5.lean
  Formal Lean 4 verification of the core combinatorial, structural, distinctness,
  divisibility, binomial-bound, and sumset-covering lemmas for the
  h(n!) = O((log n)^5) proof (Erdős Problem #18, Target A).

  Zero external dependencies (pure Lean 4.36.0 core).
  Strict anti-hallucination discipline:
    - zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms.
    - `#print axioms` audited at the bottom of this file for every main theorem.
-/

namespace Erdos18Alpha5

/-! ## Part 1: 2-Sided Dyadic Shift Architecture (Lemma 3) -/

/-- Membership in the 2-sided dyadic shift set S_t for modulus 2^k. -/
def inSt (k t s : Nat) : Prop :=
  s ≤ k - 2 ^ t ∧ (s < 2 ^ (t + 1) ∨ k < s + 3 * 2 ^ t)

instance (k t s : Nat) : Decidable (inSt k t s) :=
  inferInstanceAs (Decidable (s ≤ k - 2 ^ t ∧ (s < 2 ^ (t + 1) ∨ k < s + 3 * 2 ^ t)))

/-- Lemma 3.1a: Every shifted divisor 2^s * z with s ∈ S_t and z < 2^(2^t) is strictly < 2^k. -/
theorem dyadic_shift_size_bound (k t s z : Nat)
    (hSt : inSt k t s) (ht : 2 ^ t ≤ k) (hz : z < 2 ^ (2 ^ t)) :
    2 ^ s * z < 2 ^ k := by
  have hs : s + 2 ^ t ≤ k := Nat.add_le_of_le_sub ht hSt.1
  have h1 : 2 ^ s * z < 2 ^ s * 2 ^ (2 ^ t) :=
    Nat.mul_lt_mul_of_pos_left hz (Nat.two_pow_pos s)
  have h2 : 2 ^ s * 2 ^ (2 ^ t) = 2 ^ (s + 2 ^ t) := (Nat.pow_add 2 s (2 ^ t)).symm
  have h3 : 2 ^ (s + 2 ^ t) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hs
  omega

/-- Helper: 2 ^ Nat.log2 m ≤ m for m ≥ 1. -/
theorem two_pow_log2_le {m : Nat} (hm : 0 < m) : 2 ^ Nat.log2 m ≤ m := by
  exact (Nat.le_log2 (Nat.ne_of_gt hm)).mp (Nat.le_refl _)

/-- Helper: m < 2 ^ (Nat.log2 m + 1) for m ≥ 1. -/
theorem lt_two_pow_log2_succ {m : Nat} (hm : 0 < m) : m < 2 ^ (Nat.log2 m + 1) := by
  exact (Nat.log2_lt (Nat.ne_of_gt hm)).mp (Nat.lt_succ_self _)

/-- Lemma 3.3 (Exhaustive Coverage):
    For every k ≥ 2 and every bit position j < k, setting m_j = min(j+1, k-j)
    and t* = Nat.log2 m_j, we have:
      (1) 2^(t*) ≤ k,
      (2) t* ≤ Nat.log2 ((k + 1) / 2),
      (3) every shift s ∈ [j + 1 - 2^(t*), j] lies in S_{t*}. -/
theorem dyadic_shift_coverage (k j : Nat) (_hk : 2 ≤ k) (hj : j < k) :
    let m_j := min (j + 1) (k - j)
    let t_star := Nat.log2 m_j
    2 ^ t_star ≤ k ∧
    t_star ≤ Nat.log2 ((k + 1) / 2) ∧
    ∀ s : Nat, j + 1 - 2 ^ t_star ≤ s → s ≤ j → inSt k t_star s := by
  intro m_j t_star
  have hm_pos : 0 < m_j := by dsimp [m_j]; omega
  have hm_le_half : m_j ≤ (k + 1) / 2 := by dsimp [m_j]; omega
  have hpow_le : 2 ^ t_star ≤ m_j := two_pow_log2_le hm_pos
  have hlt_pow : m_j < 2 ^ (t_star + 1) := lt_two_pow_log2_succ hm_pos
  have hpow_le_k : 2 ^ t_star ≤ k := by
    have : m_j ≤ k := by dsimp [m_j]; omega
    omega
  have ht_le_L : t_star ≤ Nat.log2 ((k + 1) / 2) := by
    have hhalf_pos : (k + 1) / 2 ≠ 0 := by omega
    rw [Nat.le_log2 hhalf_pos]
    exact Nat.le_trans hpow_le hm_le_half
  refine ⟨hpow_le_k, ht_le_L, ?_⟩
  intro s hs_lo hs_hi
  have hs_le_sub : s ≤ k - 2 ^ t_star := by
    have hkj : m_j ≤ k - j := Nat.min_le_right _ _
    omega
  refine ⟨hs_le_sub, ?_⟩
  by_cases hcase : j + 1 ≤ k - j
  · left
    have hmj_eq : m_j = j + 1 := Nat.min_eq_left hcase
    omega
  · right
    have hmj_eq : m_j = k - j := Nat.min_eq_right (by omega)
    have hpow2 : 2 ^ (t_star + 1) = 2 * 2 ^ t_star := by
      rw [Nat.pow_succ, Nat.mul_comm]
    omega

/-- Helper: counting elements in [0, n) satisfying a boolean predicate. -/
def countUpTo (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countUpTo P n + if P n then 1 else 0

theorem countUpTo_le_self (P : Nat → Bool) (n : Nat) : countUpTo P n ≤ n := by
  induction n with
  | zero => simp [countUpTo]
  | succ n ih =>
    simp only [countUpTo]
    split <;> omega

theorem countUpTo_or_le (P Q : Nat → Bool) (n : Nat) :
    countUpTo (fun s => P s || Q s) n ≤ countUpTo P n + countUpTo Q n := by
  induction n with
  | zero => simp [countUpTo]
  | succ n ih =>
    simp only [countUpTo]
    by_cases hP : P n = true <;> by_cases hQ : Q n = true <;> simp [hP, hQ] <;> omega

theorem countUpTo_lt_bound (b n : Nat) :
    countUpTo (fun s => decide (s < b)) n ≤ b := by
  induction n with
  | zero => simp [countUpTo]
  | succ n ih =>
    simp only [countUpTo]
    by_cases h : n < b
    · have hle := countUpTo_le_self (fun s => decide (s < b)) n
      simp [h]
      omega
    · simp [h]
      exact ih

theorem countUpTo_interval_bound (a b n : Nat) :
    countUpTo (fun s => decide (a ≤ s ∧ s ≤ b)) n ≤ b + 1 - a := by
  suffices ∀ m, countUpTo (fun s => decide (a ≤ s ∧ s ≤ b)) m ≤ (min m (b + 1)) - a by
    have h := this n
    omega
  intro m
  induction m with
  | zero => simp [countUpTo]
  | succ m ih =>
    simp only [countUpTo]
    split
    · rename_i hdec
      have h : a ≤ m ∧ m ≤ b := of_decide_eq_true hdec
      omega
    · omega

/-- Lemma 3.1b: The shift set S_t has cardinality at most 4 * 2^t. -/
theorem dyadic_shift_card_bound (k t : Nat) :
    countUpTo (fun s => decide (s < 2 ^ (t + 1)) || decide (k - 3 * 2 ^ t + 1 ≤ s ∧ s ≤ k - 2 ^ t)) (k + 1)
      ≤ 4 * 2 ^ t := by
  have h1 := countUpTo_or_le
    (fun s => decide (s < 2 ^ (t + 1)))
    (fun s => decide (k - 3 * 2 ^ t + 1 ≤ s ∧ s ≤ k - 2 ^ t))
    (k + 1)
  have h2 := countUpTo_lt_bound (2 ^ (t + 1)) (k + 1)
  have h3 := countUpTo_interval_bound (k - 3 * 2 ^ t + 1) (k - 2 ^ t) (k + 1)
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
  omega


/-- Bridge: exact cardinality bound directly on `decide (inSt k t s)`. -/
theorem dyadic_shift_card_inSt (k t : Nat) :
    countUpTo (fun s => decide (inSt k t s)) (k + 1) ≤ 4 * 2 ^ t := by
  have hmono : ∀ P Q : Nat → Bool, (∀ s, P s = true → Q s = true) →
      ∀ n, countUpTo P n ≤ countUpTo Q n := by
    intro P Q himp n
    induction n with
    | zero => simp [countUpTo]
    | succ n ih =>
      simp only [countUpTo]
      by_cases hP : P n = true
      · have hQ := himp n hP
        simp [hP, hQ]; omega
      · simp [hP]; omega
  refine Nat.le_trans (hmono _ _ ?_ (k + 1)) (dyadic_shift_card_bound k t)
  intro s hs
  have hIn : inSt k t s := of_decide_eq_true hs
  rcases hIn with ⟨hle, hlt | hgt⟩
  · simp [hlt]
  · by_cases hs0 : s = 0
    · subst hs0
      have hpos : 0 < 2 ^ (t + 1) := Nat.two_pow_pos (t + 1)
      simp [hpos]
    · have : k - 3 * 2 ^ t + 1 ≤ s ∧ s ≤ k - 2 ^ t := by omega
      simp [this]

/-! ## Part 2: 2-adic Carry Recursion & Valuation Distinctness (Lemma 4) -/

/-- Lemma 4 invariant: E ≥ 2B with k = B - b and b ≤ B/2 implies E - k ≥ 2b. -/
theorem carry_invariant_preserved (E B b : Nat)
    (hE : 2 * B ≤ E) (hb_le : 2 * b ≤ B) :
    2 * b ≤ E - (B - b) := by
  omega

/-- Lemma 4 distinctness across carry depths:
    any divisor d1 not divisible by 2^k is strictly distinct from 2^k * d2. -/
theorem carry_v2_disjointness (k d1 d2 : Nat) (h1 : ¬ (2 ^ k ∣ d1)) :
    d1 ≠ 2 ^ k * d2 := by
  intro heq
  apply h1
  rw [heq]
  exact Nat.dvd_mul_right (2 ^ k) d2

/-! ## Part 3: Stage 2 Binomial Upper Bound & 3-Group Distinctness -/

/-- Elementary binomial coefficient defined directly via Pascal's recurrence. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_self (n : Nat) : binom n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hgt : ∀ m k, m < k → binom m k = 0 := by
      intro m
      induction m with
      | zero =>
        intro k hk
        cases k with
        | zero => omega
        | succ k' => rfl
      | succ m ihm =>
        intro k hk
        cases k with
        | zero => omega
        | succ k' =>
          simp only [binom]
          rw [ihm k' (by omega), ihm (k' + 1) (by omega)]
    simp only [binom, ih, hgt n (n + 1) (by omega)]

def sumBinom (a : Nat) : Nat → Nat
  | 0 => binom a 0
  | j + 1 => sumBinom a j + binom a (j + 1)

theorem binom_le_sumBinom (a b j : Nat) (h : b ≤ j) :
    binom a b ≤ sumBinom a j := by
  induction j with
  | zero =>
    have hb : b = 0 := Nat.le_zero.mp h
    subst hb
    simp [sumBinom]
  | succ j ih =>
    simp only [sumBinom]
    by_cases hbj : b ≤ j
    · exact Nat.le_trans (ih hbj) (Nat.le_add_right _ _)
    · have hb : b = j + 1 := by omega
      subst hb
      exact Nat.le_add_left _ _

theorem sumBinom_eq_two_pow (a : Nat) : sumBinom a a = 2 ^ a := by
  induction a with
  | zero => simp [sumBinom, binom]
  | succ a ih =>
    have hstep : ∀ j ≤ a, sumBinom (a + 1) j + binom a j = 2 * sumBinom a j := by
      intro j hj
      induction j with
      | zero =>
        simp [sumBinom, binom]
      | succ j ihj =>
        have ih' := ihj (Nat.le_of_succ_le hj)
        simp only [sumBinom, binom]
        omega
    have hlast := hstep a (Nat.le_refl a)
    simp only [sumBinom, binom_self] at hlast ⊢
    rw [Nat.pow_succ, Nat.mul_comm]
    omega

/-- Elementary binomial upper bound: C(a, b) < 2^a for all a ≥ 1 and b ≤ a. -/
theorem binom_lt_two_pow (a b : Nat) (ha : 1 ≤ a) (hb : b ≤ a) :
    binom a b < 2 ^ a := by
  rw [← sumBinom_eq_two_pow a]
  cases a with
  | zero => omega
  | succ m =>
    by_cases hba : b = m + 1
    · subst hba
      simp only [sumBinom]
      have h0 := binom_le_sumBinom (m + 1) 0 m (Nat.zero_le m)
      simp only [binom] at h0
      omega
    · simp only [sumBinom, binom_self]
      have hle := binom_le_sumBinom (m + 1) b m (by omega)
      omega

/-- Stage 2 arithmetic conditions for E ≥ 84 with k = 45*E/100, E_next = E - k:
    (1) E / 4 < 2 * (E_next / 4) (guarantees a - b < b so every prime in (b, a] divides C(a, b)),
    (2) E / 4 < E_next / 2 (guarantees 2^(E/4) < 2^(E_next/2)). -/
theorem stage2_exponents_ineq (E : Nat) (hE : 84 ≤ E) :
    let k := (45 * E) / 100
    let E_next := E - k
    E / 4 < 2 * (E_next / 4) ∧ E / 4 < E_next / 2 := by
  intro k E_next
  dsimp [E_next, k]
  omega

/-- Stage 2 3-group pairwise distinctness and divisibility in M(E) = 2^k * U_top * M_next. -/
theorem stage2_three_group_distinctness_and_divisibility
    (k U_top M_next d1 a b : Nat)
    (h1_div : d1 ∣ 2 ^ k * U_top * M_next) (h1_v2 : ¬ (2 ^ k ∣ d1))
    (_ha_pos : 1 ≤ a) (ha_lt : a < U_top) (ha_div : a ∣ M_next)
    (hb_pos : 1 ≤ b) (hb_div : b ∣ M_next) :
    let M := 2 ^ k * U_top * M_next
    let d2 := 2 ^ k * a
    let d3 := 2 ^ k * U_top * b
    (d1 ∣ M ∧ d2 ∣ M ∧ d3 ∣ M) ∧ (d1 ≠ d2 ∧ d1 ≠ d3 ∧ d2 ≠ d3) := by
  intro M d2 d3
  have hd2_div : d2 ∣ M := by
    dsimp [d2, M]
    rcases ha_div with ⟨c, hc⟩
    refine ⟨U_top * c, ?_⟩
    rw [hc]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hd3_div : d3 ∣ M := by
    dsimp [d3, M]
    exact Nat.mul_dvd_mul_left (2 ^ k * U_top) hb_div
  have h12 : d1 ≠ d2 := carry_v2_disjointness k d1 a h1_v2
  have h13 : d1 ≠ d3 := by
    dsimp [d3]
    rw [Nat.mul_assoc]
    exact carry_v2_disjointness k d1 (U_top * b) h1_v2
  have h23 : d2 ≠ d3 := by
    dsimp [d2, d3]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hlt : 2 ^ k * a < 2 ^ k * U_top := Nat.mul_lt_mul_of_pos_left ha_lt hpos
    have hle : 2 ^ k * U_top ≤ 2 ^ k * U_top * b := Nat.le_mul_of_pos_right _ (by omega)
    omega
  exact ⟨⟨h1_div, hd2_div, hd3_div⟩, ⟨h12, h13, h23⟩⟩

/-! ## Part 4: Stage 1 Mixed-Radix Disjoint Intervals -/

/-- Stage 1 distinctness: divisors in [P_i, P_{i+1}) and [P_j, ∞) for i < j are disjoint. -/
theorem stage1_mixed_radix_disjoint (P_i D_next P_j a b : Nat)
    (hP_i : 0 < P_i) (hstep : P_i * D_next ≤ P_j) (ha_lt : a < D_next) (hb_pos : 1 ≤ b) :
    a * P_i ≠ b * P_j := by
  have h1 : a * P_i < D_next * P_i := Nat.mul_lt_mul_of_pos_right ha_lt hP_i
  have h2 : D_next * P_i = P_i * D_next := Nat.mul_comm D_next P_i
  have h3 : P_j ≤ b * P_j := Nat.le_mul_of_pos_left P_j (by omega)
  omega

/-! ## Part 5: Lemma 3 Prime-Tag Distinctness & Pigeonhole Sumset Covering -/

/-- Lemma 3 prime-tag distinctness: if q1 divides d1 and does not divide d2, then d1 ≠ d2. -/
theorem prime_tag_distinctness (q1 d1 d2 : Nat) (h1 : q1 ∣ d1) (h2 : ¬ (q1 ∣ d2)) :
    d1 ≠ d2 := by
  intro heq
  rw [heq] at h1
  exact h2 h1

/-- Count of `Fin N` elements satisfying a boolean predicate. -/
def finCount {N : Nat} (P : Fin N → Bool) : Nat :=
  countUpTo (fun i => if h : i < N then P ⟨i, h⟩ else false) N

theorem finCount_add_disjoint {N : Nat} (P Q : Fin N → Bool)
    (hdisj : ∀ a : Fin N, ¬ (P a = true ∧ Q a = true)) :
    finCount P + finCount Q ≤ N := by
  have hstep : ∀ m ≤ N,
      countUpTo (fun i => if h : i < N then P ⟨i, h⟩ else false) m +
      countUpTo (fun i => if h : i < N then Q ⟨i, h⟩ else false) m ≤ m := by
    intro m hm
    induction m with
    | zero => simp [countUpTo]
    | succ m ih =>
      have hm_lt : m < N := by omega
      have ih' := ih (Nat.le_of_succ_le hm)
      have hnd := hdisj ⟨m, hm_lt⟩
      simp only [countUpTo, hm_lt, ↓reduceDIte]
      by_cases hP : P ⟨m, hm_lt⟩ = true <;> by_cases hQ : Q ⟨m, hm_lt⟩ = true
      · exact absurd ⟨hP, hQ⟩ hnd
      · simp [hP, hQ]; omega
      · simp [hP, hQ]; omega
      · simp [hP, hQ]; omega
  exact hstep N (Nat.le_refl N)

theorem exists_overlap_of_sum_gt {N : Nat} (P Q : Fin N → Bool)
    (hgt : N < finCount P + finCount Q) :
    ∃ a : Fin N, P a = true ∧ Q a = true := by
  apply Classical.byContradiction
  intro hno
  have hdisj : ∀ a : Fin N, ¬ (P a = true ∧ Q a = true) := by
    intro a ha
    exact hno ⟨a, ha⟩
  have hle := finCount_add_disjoint P Q hdisj
  omega

/-- Involution a ↦ (x + N - a) % N on Fin N. -/
def subMod (N : Nat) (hN : 0 < N) (x a : Fin N) : Fin N :=
  ⟨(x.val + (N - a.val)) % N, Nat.mod_lt _ hN⟩

theorem subMod_involutive (N : Nat) (hN : 0 < N) (x a : Fin N) :
    subMod N hN x (subMod N hN x a) = a := by
  apply Fin.ext
  dsimp [subMod]
  have hx := x.isLt
  have ha := a.isLt
  by_cases h : a.val ≤ x.val
  · have h1 : (x.val + (N - a.val)) % N = x.val - a.val := by
      have : x.val + (N - a.val) = (x.val - a.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : x.val + (N - (x.val - a.val)) = a.val + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · have h1 : (x.val + (N - a.val)) % N = x.val + N - a.val := by
      have : x.val + (N - a.val) = x.val + N - a.val := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : x.val + (N - (x.val + N - a.val)) = a.val := by omega
    rw [this, Nat.mod_eq_of_lt ha]

theorem add_subMod_eq (N : Nat) (hN : 0 < N) (x a : Fin N) :
    (a.val + (subMod N hN x a).val) % N = x.val := by
  dsimp [subMod]
  have hx := x.isLt
  have ha := a.isLt
  by_cases h : a.val ≤ x.val
  · have h1 : (x.val + (N - a.val)) % N = x.val - a.val := by
      have : x.val + (N - a.val) = (x.val - a.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : a.val + (x.val - a.val) = x.val := by omega
    rw [this, Nat.mod_eq_of_lt hx]
  · have h1 : (x.val + (N - a.val)) % N = x.val + N - a.val := by
      have : x.val + (N - a.val) = x.val + N - a.val := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : a.val + (x.val + N - a.val) = x.val + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

theorem countUpTo_eq_list_countP (P : Nat → Bool) (n : Nat) :
    countUpTo P n = (List.range n).countP P := by
  induction n with
  | zero => simp [countUpTo]
  | succ n ih =>
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    simp only [countUpTo, ih]

theorem nodup_map_of_injective {α β : Type} {f : α → β} {l : List α}
    (hinj : ∀ x y, f x = f y → x = y) (hl : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨b, hb, hfb⟩
    have : b = a := hinj b a hfb
    subst this
    exact hl.1 hb

theorem map_val_finRange_eq_range (N : Nat) :
    (List.finRange N).map Fin.val = List.range N := by
  apply List.ext_getElem <;> simp

/-- finCount is invariant under any involution f on Fin N. -/
theorem finCount_involution {N : Nat} (f : Fin N → Fin N)
    (hinv : ∀ a, f (f a) = a) (P : Fin N → Bool) :
    finCount (fun a => P (f a)) = finCount P := by
  have h1 : ∀ Q : Fin N → Bool, finCount Q = (List.finRange N).countP Q := by
    intro Q
    dsimp [finCount]
    rw [countUpTo_eq_list_countP, ← map_val_finRange_eq_range N, List.countP_map]
    apply List.countP_congr
    intro a _
    simp [a.isLt]
  rw [h1, h1]
  have hperm : List.Perm ((List.finRange N).map f) (List.finRange N) := by
    rw [List.perm_ext_iff_of_nodup]
    · intro a
      constructor
      · intro _; exact List.mem_finRange a
      · intro _
        rw [List.mem_map]
        exact ⟨f a, List.mem_finRange (f a), hinv a⟩
    · apply nodup_map_of_injective
      · intro a b hab
        have := congrArg f hab
        rwa [hinv, hinv] at this
      · exact List.nodup_finRange N
    · exact List.nodup_finRange N
  have hcomp : (fun a => P (f a)) = P ∘ f := rfl
  rw [hcomp, ← List.countP_map]
  exact hperm.countP_eq P

/-- Lemma 3.5 (Pigeonhole Sumset Covering on Z/NZ):
    If A, B ⊆ Fin N satisfy |A| + |B| > N, then A + B = Z/NZ. -/
theorem pigeonhole_sumset_cover_zmod (N : Nat) (hN : 0 < N)
    (A B : Fin N → Bool) (hgt : N < finCount A + finCount B) :
    ∀ x : Fin N, ∃ a b : Fin N, A a = true ∧ B b = true ∧ (a.val + b.val) % N = x.val := by
  intro x
  let Q : Fin N → Bool := fun a => B (subMod N hN x a)
  have hQ : finCount Q = finCount B :=
    finCount_involution (subMod N hN x) (subMod_involutive N hN x) B
  have hgt' : N < finCount A + finCount Q := by omega
  rcases exists_overlap_of_sum_gt A Q hgt' with ⟨a, hAa, hQa⟩
  exact ⟨a, subMod N hN x a, hAa, hQa, add_subMod_eq N hN x a⟩

end Erdos18Alpha5

#print axioms Erdos18Alpha5.dyadic_shift_size_bound
#print axioms Erdos18Alpha5.dyadic_shift_coverage
#print axioms Erdos18Alpha5.dyadic_shift_card_bound
#print axioms Erdos18Alpha5.dyadic_shift_card_inSt
#print axioms Erdos18Alpha5.carry_invariant_preserved
#print axioms Erdos18Alpha5.carry_v2_disjointness
#print axioms Erdos18Alpha5.binom_lt_two_pow
#print axioms Erdos18Alpha5.stage2_exponents_ineq
#print axioms Erdos18Alpha5.stage2_three_group_distinctness_and_divisibility
#print axioms Erdos18Alpha5.stage1_mixed_radix_disjoint
#print axioms Erdos18Alpha5.prime_tag_distinctness
#print axioms Erdos18Alpha5.pigeonhole_sumset_cover_zmod
