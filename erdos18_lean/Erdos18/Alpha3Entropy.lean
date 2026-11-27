import Erdos18.Entropy
import Mathlib.Analysis.Convex.Deriv

/-!
# Erdos18/Alpha3Entropy.lean — Sharp Convex Bitwise Entropy Gain (`f4nat`)

Formalizes the sharp convex entropy-variance and bitwise gain lemmas in natural-log units (nats),
matching `Erdos18.Entropy`:
- `f4nat u = if u ≤ 0 then 0 else u / Real.log (4 / u)` on `[0, 1]`.
- `psiNat u = Real.log (4 / u) / u = (f4nat u)⁻¹` on `(0, 1]`.
- `convexOn_f4nat : ConvexOn ℝ (Set.Icc 0 1) f4nat`.
- `binEntropy_f4nat_le : f4nat (Real.binEntropy q) ≤ 4 * q * (1 - q)` for `q ∈ [0, 1]`.
- `Hnat_conv_sub_ge_bitwise_f4nat`:
    `Hnat (conv X Z) - Hnat X ≥ ∑ j : Fin k, f4nat (condBitEnt Z j) * (Real.log 2 - condBitEnt X j)`.
-/

namespace Erdos18

open Finset Real

/-- Sharp convex gain function in nats: `f4nat(u) = u / log(4 / u)` for `u > 0`, `0` for `u ≤ 0`. -/
noncomputable def f4nat (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else u / Real.log (4 / u)

/-- Reciprocal weight function `psiNat(u) = log(4 / u) / u = 1 / f4nat(u)` for `u ∈ (0, 1]`. -/
noncomputable def psiNat (u : ℝ) : ℝ :=
  Real.log (4 / u) / u

lemma f4nat_zero : f4nat 0 = 0 := by
  unfold f4nat; simp

lemma f4nat_of_pos {u : ℝ} (hu : 0 < u) : f4nat u = u / Real.log (4 / u) := by
  unfold f4nat; exact ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hu))

lemma log_four_div_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) : 0 < Real.log (4 / u) := by
  apply Real.log_pos
  rw [one_lt_div hu0]
  linarith

lemma log_four_div_ge_log_four {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    Real.log 4 ≤ Real.log (4 / u) := by
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ hu0]
  linarith

lemma f4nat_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) : 0 < f4nat u := by
  rw [f4nat_of_pos hu0]
  exact div_pos hu0 (log_four_div_pos hu0 hu1)

lemma f4nat_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ f4nat u := by
  rcases eq_or_lt_of_le hu0 with rfl | hpos
  · rw [f4nat_zero]
  · exact (f4nat_pos hpos hu1).le

lemma psiNat_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) : 0 < psiNat u := by
  unfold psiNat
  exact div_pos (log_four_div_pos hu0 hu1) hu0

lemma psiNat_mul_f4nat {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    psiNat u * f4nat u = 1 := by
  unfold psiNat
  rw [f4nat_of_pos hu0]
  have hlog : Real.log (4 / u) ≠ 0 := (log_four_div_pos hu0 hu1).ne'
  field_simp [hu0.ne', hlog]

lemma f4nat_mono {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1) :
    f4nat u ≤ f4nat v := by
  rcases eq_or_lt_of_le hu0 with rfl | hu_pos
  · rw [f4nat_zero]; exact f4nat_nonneg (le_trans hu0 huv) hv1
  · have hv_pos : 0 < v := lt_of_lt_of_le hu_pos huv
    rw [f4nat_of_pos hu_pos, f4nat_of_pos hv_pos]
    have hlog_v : 0 < Real.log (4 / v) := log_four_div_pos hv_pos hv1
    have hlog_le : Real.log (4 / v) ≤ Real.log (4 / u) := by
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_left (by norm_num) hu_pos huv
    exact div_le_div₀ (by linarith) huv hlog_v hlog_le

lemma psiNat_anti {u v : ℝ} (hu0 : 0 < u) (huv : u ≤ v) (hv1 : v ≤ 1) :
    psiNat v ≤ psiNat u := by
  have hv_pos : 0 < v := lt_of_lt_of_le hu0 huv
  have hf_u := f4nat_pos hu0 (le_trans huv hv1)
  have hfm : f4nat u ≤ f4nat v := f4nat_mono hu0.le huv hv1
  have h1 : psiNat u = (f4nat u)⁻¹ :=
    eq_inv_of_mul_eq_one_left (psiNat_mul_f4nat hu0 (le_trans huv hv1))
  have h2 : psiNat v = (f4nat v)⁻¹ :=
    eq_inv_of_mul_eq_one_left (psiNat_mul_f4nat hv_pos hv1)
  rw [h1, h2]
  exact inv_anti₀ hf_u hfm

/-- Auxiliary smooth version of `f4nat` on `(0, 2)` for second-derivative convexity. -/
private noncomputable def f4smooth (u : ℝ) : ℝ := u / Real.log (4 / u)

private lemma hasDerivAt_log_four_div {u : ℝ} (hu0 : 0 < u) :
    HasDerivAt (fun t => Real.log (4 / t)) (-1 / u) u := by
  have h1 : HasDerivAt (fun t : ℝ => (4 : ℝ) / t) (-4 / u ^ 2) u := by
    have hinv := (hasDerivAt_inv hu0.ne').const_mul (4 : ℝ)
    convert hinv using 1
    · ext t; simp [div_eq_mul_inv]
    · ring
  have hdiv_ne : (4 : ℝ) / u ≠ 0 := by positivity
  have h2 := h1.log hdiv_ne
  convert h2 using 1
  field_simp [hu0.ne']

private lemma hasDerivAt_f4smooth {u : ℝ} (hu0 : 0 < u) (hu2 : u < 2) :
    HasDerivAt f4smooth ((Real.log (4 / u) + 1) / (Real.log (4 / u)) ^ 2) u := by
  have hL_pos : 0 < Real.log (4 / u) := by
    apply Real.log_pos; rw [one_lt_div hu0]; linarith
  have h1 : HasDerivAt (fun t : ℝ => t) 1 u := hasDerivAt_id u
  have h2 : HasDerivAt (fun t => Real.log (4 / t)) (-1 / u) u := hasDerivAt_log_four_div hu0
  have hq := h1.div h2 hL_pos.ne'
  convert hq using 1
  · ext t; rfl
  · field_simp [hu0.ne', hL_pos.ne']
    ring

private lemma hasDerivAt_f4smooth_deriv {u : ℝ} (hu0 : 0 < u) (hu2 : u < 2) :
    HasDerivAt (fun t => (Real.log (4 / t) + 1) / (Real.log (4 / t)) ^ 2)
      ((Real.log (4 / u) + 2) / (u * (Real.log (4 / u)) ^ 3)) u := by
  have hL_pos : 0 < Real.log (4 / u) := by
    apply Real.log_pos; rw [one_lt_div hu0]; linarith
  have hL := hasDerivAt_log_four_div hu0
  have hnum : HasDerivAt (fun t => Real.log (4 / t) + 1) (-1 / u) u := by
    simpa using hL.add_const (1 : ℝ)
  have hden : HasDerivAt (fun t => (Real.log (4 / t)) ^ 2) (2 * Real.log (4 / u) * (-1 / u)) u := by
    have hp := hL.pow 2
    convert hp using 1
    · ring
  have hden_ne : (Real.log (4 / u)) ^ 2 ≠ 0 := pow_ne_zero 2 hL_pos.ne'
  have hq := hnum.div hden hden_ne
  convert hq using 1
  field_simp [hu0.ne', hL_pos.ne']
  ring

private lemma convexOn_f4smooth_Ioo : ConvexOn ℝ (Set.Ioo (0 : ℝ) 2) f4smooth := by
  apply convexOn_of_deriv2_nonneg (convex_Ioo 0 2)
  · intro u hu
    exact (hasDerivAt_f4smooth hu.1 hu.2).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    exact (hasDerivAt_f4smooth hu.1 hu.2).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    have hderiv_eq : ∀ᶠ t in nhds u,
        deriv f4smooth t = (Real.log (4 / t) + 1) / (Real.log (4 / t)) ^ 2 := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
      exact (hasDerivAt_f4smooth ht.1 ht.2).deriv
    have h2 : HasDerivAt (deriv f4smooth)
        ((Real.log (4 / u) + 2) / (u * (Real.log (4 / u)) ^ 3)) u :=
      (hasDerivAt_f4smooth_deriv hu.1 hu.2).congr_of_eventuallyEq hderiv_eq
    exact h2.differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    have hderiv_eq : ∀ᶠ t in nhds u,
        deriv f4smooth t = (Real.log (4 / t) + 1) / (Real.log (4 / t)) ^ 2 := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
      exact (hasDerivAt_f4smooth ht.1 ht.2).deriv
    have h2 : deriv (deriv f4smooth) u =
        (Real.log (4 / u) + 2) / (u * (Real.log (4 / u)) ^ 3) :=
      ((hasDerivAt_f4smooth_deriv hu.1 hu.2).congr_of_eventuallyEq hderiv_eq).deriv
    change 0 ≤ deriv (deriv f4smooth) u
    rw [h2]
    have hL_pos : 0 < Real.log (4 / u) := by
      apply Real.log_pos; rw [one_lt_div hu.1]; linarith [hu.2]
    have hu_pos : 0 < u := hu.1
    positivity

/-- `f4nat` is convex on `[0, 1]`. -/
theorem convexOn_f4nat : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f4nat := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
  · simp only [f4nat_zero, mul_zero, zero_add]
    rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp only [zero_mul, f4nat_zero, le_refl]
    · rcases eq_or_lt_of_le hy.1 with rfl | hy_pos
      · simp only [mul_zero, f4nat_zero, le_refl]
      · have hby_pos : 0 < b * y := mul_pos hb_pos hy_pos
        have hb1 : b ≤ 1 := by linarith
        have hby_le : b * y ≤ y := mul_le_of_le_one_left hy_pos.le hb1
        rw [f4nat_of_pos hby_pos, f4nat_of_pos hy_pos]
        have hLy : 0 < Real.log (4 / y) := log_four_div_pos hy_pos hy.2
        have hL_le : Real.log (4 / y) ≤ Real.log (4 / (b * y)) := by
          apply Real.log_le_log (by positivity)
          exact div_le_div_of_nonneg_left (by norm_num) hby_pos hby_le
        calc b * y / Real.log (4 / (b * y))
            ≤ b * y / Real.log (4 / y) := div_le_div_of_nonneg_left hby_pos.le hLy hL_le
          _ = b * (y / Real.log (4 / y)) := by ring
  · rcases eq_or_lt_of_le hy.1 with rfl | hy_pos
    · simp only [f4nat_zero, mul_zero, add_zero]
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · simp only [zero_mul, f4nat_zero, le_refl]
      · have hax_pos : 0 < a * x := mul_pos ha_pos hx_pos
        have ha1 : a ≤ 1 := by linarith
        have hax_le : a * x ≤ x := mul_le_of_le_one_left hx_pos.le ha1
        rw [f4nat_of_pos hax_pos, f4nat_of_pos hx_pos]
        have hLx : 0 < Real.log (4 / x) := log_four_div_pos hx_pos hx.2
        have hL_le : Real.log (4 / x) ≤ Real.log (4 / (a * x)) := by
          apply Real.log_le_log (by positivity)
          exact div_le_div_of_nonneg_left (by norm_num) hax_pos hax_le
        calc a * x / Real.log (4 / (a * x))
            ≤ a * x / Real.log (4 / x) := div_le_div_of_nonneg_left hax_pos.le hLx hL_le
          _ = a * (x / Real.log (4 / x)) := by ring
    · have hx_mem : x ∈ Set.Ioo (0 : ℝ) 2 := ⟨hx_pos, by linarith [hx.2]⟩
      have hy_mem : y ∈ Set.Ioo (0 : ℝ) 2 := ⟨hy_pos, by linarith [hy.2]⟩
      have hconv_pos : 0 < a * x + b * y := by
        rcases eq_or_lt_of_le ha with rfl | ha_pos
        · have hb1 : b = 1 := by linarith
          subst hb1; linarith
        · nlinarith
      rw [f4nat_of_pos hconv_pos, f4nat_of_pos hx_pos, f4nat_of_pos hy_pos]
      simpa [f4smooth, smul_eq_mul] using convexOn_f4smooth_Ioo.2 hx_mem hy_mem ha hb hab

/-- Lemma 1'(2) in nats: `f4nat (Real.binEntropy q) ≤ 4 * q * (1 - q)` for all `q ∈ [0, 1]`. -/
theorem binEntropy_f4nat_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    f4nat (Real.binEntropy q) ≤ 4 * q * (1 - q) := by
  suffices hhalf : ∀ r : ℝ, 0 ≤ r → r ≤ 1 / 2 → f4nat (Real.binEntropy r) ≤ 4 * r * (1 - r) by
    by_cases h : q ≤ 1 / 2
    · exact hhalf q hq0 h
    · have h1q0 : 0 ≤ 1 - q := by linarith
      have h1q_half : 1 - q ≤ 1 / 2 := by linarith
      have hsymm : Real.binEntropy (1 - q) = Real.binEntropy q := by
        rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
            Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
        simp [sub_sub_cancel, add_comm]
      have hres := hhalf (1 - q) h1q0 h1q_half
      rw [hsymm] at hres
      linarith
  intro r hr0 hr_half
  rcases eq_or_lt_of_le hr0 with rfl | hr_pos
  · simp [f4nat_zero]
  have hr_lt1 : r < 1 := by linarith
  have h1mr_pos : 0 < 1 - r := by linarith
  set u := Real.binEntropy r
  have hu_pos : 0 < u := by
    dsimp [u]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    unfold Real.negMulLog
    have h1 : 0 < -r * Real.log r := by
      have : Real.log r < 0 := Real.log_neg hr_pos hr_lt1
      nlinarith
    have h2 : 0 < -(1 - r) * Real.log (1 - r) := by
      have : Real.log (1 - r) < 0 := Real.log_neg h1mr_pos (by linarith)
      nlinarith
    linarith
  have hu_sq : u ^ 2 ≤ 2 * r := by
    have hsq := binEntropy_sq_le hr0 (by linarith : r ≤ 1)
    nlinarith
  have hu_le_sqrt : u ≤ Real.sqrt (2 * r) := by
    rw [Real.le_sqrt hu_pos.le (by positivity)]
    linarith
  have hlogr_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt1
  have h1mlogr_pos : 0 < 1 - Real.log r := by linarith
  have hexp_lt8 : Real.exp 1 < 8 := by
    have := Real.exp_one_lt_d9
    linarith
  have h4u_ge : Real.sqrt (Real.exp 1 / r) ≤ 4 / u := by
    have h1 : Real.sqrt (Real.exp 1 / r) ≤ Real.sqrt (8 / r) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hexp_lt8.le hr_pos.le)
    have h2 : Real.sqrt (8 / r) = 4 / Real.sqrt (2 * r) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_div (by positivity)]
      congr 1
      field_simp [hr_pos.ne']
      ring
    have h3 : 4 / Real.sqrt (2 * r) ≤ 4 / u :=
      div_le_div_of_nonneg_left (by norm_num) hu_pos hu_le_sqrt
    linarith
  have hlog4u_ge : (1 - Real.log r) / 2 ≤ Real.log (4 / u) := by
    have h1 : Real.log (Real.sqrt (Real.exp 1 / r)) ≤ Real.log (4 / u) :=
      Real.log_le_log (Real.sqrt_pos.mpr (by positivity)) h4u_ge
    rw [Real.log_sqrt (by positivity), Real.log_div (Real.exp_pos 1).ne' hr_pos.ne',
        Real.log_exp] at h1
    exact h1
  have hu_le : u ≤ r * (1 - Real.log r) := by
    dsimp [u]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    unfold Real.negMulLog
    have hlog1mr : -Real.log (1 - r) ≤ r / (1 - r) := by
      have hinv : Real.log (1 / (1 - r)) ≤ 1 / (1 - r) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [one_div, Real.log_inv] at hinv
      have hsub : (1 - r)⁻¹ - 1 = r / (1 - r) := by
        field_simp [h1mr_pos.ne']
        ring
      linarith
    have hmul : -(1 - r) * Real.log (1 - r) ≤ r := by
      have h1 := mul_le_mul_of_nonneg_left hlog1mr h1mr_pos.le
      have h2 : (1 - r) * (r / (1 - r)) = r := by field_simp [h1mr_pos.ne']
      linarith
    linarith
  rw [f4nat_of_pos hu_pos]
  have hlog4u_pos : 0 < Real.log (4 / u) := by linarith
  have hdiv : u / Real.log (4 / u) ≤ 2 * r := by
    rw [div_le_iff₀ hlog4u_pos]
    calc u ≤ r * (1 - Real.log r) := hu_le
      _ = 2 * r * ((1 - Real.log r) / 2) := by ring
      _ ≤ 2 * r * Real.log (4 / u) := mul_le_mul_of_nonneg_left hlog4u_ge (by positivity)
  nlinarith

/-- Sharp XOR entropy gain inequality using `f4nat` (Lemma 1' + Lemma 1b). -/
theorem binEntropy_xor_gain_f4nat {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    let α := |1 - 2 * p|
    let β := |1 - 2 * q|
    Real.binEntropy ((1 - α * β) / 2) - Real.binEntropy p ≥
      f4nat (Real.binEntropy q) * (Real.log 2 - Real.binEntropy p) := by
  intro α β
  have hα0 : 0 ≤ α := abs_nonneg _
  have hα1 : α ≤ 1 := by dsimp [α]; rw [abs_le]; constructor <;> linarith
  have hβ0 : 0 ≤ β := abs_nonneg _
  have hβ1 : β ≤ 1 := by dsimp [β]; rw [abs_le]; constructor <;> linarith
  have hp_symm : Real.binEntropy ((1 - α) / 2) = Real.binEntropy p := by
    dsimp [α]
    by_cases h : 0 ≤ 1 - 2 * p
    · rw [abs_of_nonneg h]; congr 1; ring
    · rw [abs_of_neg (lt_of_not_ge h)]
      have : (1 - -(1 - 2 * p)) / 2 = 1 - p := by ring
      rw [this, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
          Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      simp [sub_sub_cancel, add_comm]
  have hdef := binEntropy_deficit_mul_le hα0 hα1 hβ0 hβ1
  rw [hp_symm] at hdef
  have h1b2 : 1 - β ^ 2 = 4 * q * (1 - q) := by
    dsimp [β]; rw [sq_abs]; ring
  have hq_f4 := binEntropy_f4nat_le hq0 hq1
  have hdef_nonneg : 0 ≤ Real.log 2 - Real.binEntropy p := by
    have := Real.binEntropy_le_log_two (p := p)
    linarith
  nlinarith

/-- Helper: `Real.binEntropy q ∈ [0, 1]` for all `q ∈ [0, 1]`. -/
lemma binEntropy_mem_Icc {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.binEntropy q ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have h1 : 0 ≤ Real.negMulLog q := Real.negMulLog_nonneg hq0 hq1
    have h2 : 0 ≤ Real.negMulLog (1 - q) := Real.negMulLog_nonneg (by linarith) (by linarith)
    linarith
  · have h1 := Real.binEntropy_le_log_two (p := q)
    have h2 := Real.log_two_lt_d9
    linarith

/-- Helper: `condBitEnt Z j ∈ [0, Real.log 2]`. -/
lemma condBitEnt_bounds {k : ℕ} (Z : PMF_Fin (2 ^ k)) (j : ℕ) :
    0 ≤ condBitEnt Z j ∧ condBitEnt Z j ≤ Real.log 2 := by
  constructor
  · unfold condBitEnt
    apply Finset.sum_nonneg
    intro b _
    have hqb := q_bit_bounds Z j b
    exact mul_nonneg (W_pref_nonneg Z j b) (binEntropy_mem_Icc hqb.1 hqb.2).1
  · have hle : condBitEnt Z j ≤ ∑ b : Fin (2 ^ j), W_pref Z j b * Real.log 2 := by
      unfold condBitEnt
      apply Finset.sum_le_sum; intro b _
      exact mul_le_mul_of_nonneg_left (Real.binEntropy_le_log_two (p := q_bit Z j b)) (W_pref_nonneg Z j b)
    rw [← Finset.sum_mul, W_pref_sum_one Z j, one_mul] at hle
    exact hle

/-- Single-bit conditional entropy gain under convolution using `f4nat` (for `j < k`). -/
lemma condBitEnt_conv_sub_ge_f4nat {k j : ℕ} (hj : j < k) (X Z : PMF_Fin (2 ^ k)) :
    condBitEnt (convPMF (Nat.two_pow_pos k) X Z) j - condBitEnt X j ≥
      f4nat (condBitEnt Z j) * (Real.log 2 - condBitEnt X j) := by
  let U := convPMF (Nat.two_pow_pos k) X Z
  let hNj := Nat.two_pow_pos j
  have hconc_u : ∀ u : Fin (2 ^ j),
      W_pref U j u * Real.binEntropy (q_bit U j u) ≥
      ∑ a : Fin (2 ^ j),
        W_pref X j a * W_pref Z j (subModFin hNj u a) *
          Real.binEntropy ((1 - |1 - 2 * q_bit X j a| * |1 - 2 * q_bit Z j (subModFin hNj u a)|) / 2) := by
    intro u
    by_cases hU0 : W_pref U j u = 0
    · rw [hU0, zero_mul]
      have hsum0 := W_pref_conv_eq hj.le X Z u
      rw [hU0] at hsum0
      have hall0 : ∀ a : Fin (2 ^ j), W_pref X j a * W_pref Z j (subModFin hNj u a) = 0 := fun a =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => mul_nonneg (W_pref_nonneg X j a') (W_pref_nonneg Z j _))).mp
          hsum0.symm a (Finset.mem_univ a)
      simp [hall0]
    · have hUpos : 0 < W_pref U j u := lt_of_le_of_ne (W_pref_nonneg U j u) (Ne.symm hU0)
      let w : Fin (2 ^ j) → ℝ := fun a => W_pref X j a * W_pref Z j (subModFin hNj u a) / W_pref U j u
      let r : Fin (2 ^ j) → ℝ := fun a =>
        xorProb (q_bit X j a) (q_bit Z j (subModFin hNj u a)) (carryBit j a (subModFin hNj u a))
      have hw0 : ∀ a ∈ (Finset.univ : Finset (Fin (2 ^ j))), 0 ≤ w a := fun a _ =>
        div_nonneg (mul_nonneg (W_pref_nonneg X j a) (W_pref_nonneg Z j _)) hUpos.le
      have hw1 : ∑ a : Fin (2 ^ j), w a = 1 := by
        dsimp [w]; rw [← Finset.sum_div, ← W_pref_conv_eq hj.le X Z u, div_self hU0]
      have hr_mem : ∀ a ∈ (Finset.univ : Finset (Fin (2 ^ j))), r a ∈ Set.Icc (0 : ℝ) 1 := fun a _ =>
        xorProb_bounds (q_bit_bounds X j a).1 (q_bit_bounds X j a).2
          (q_bit_bounds Z j _).1 (q_bit_bounds Z j _).2 _
      have hqU_eq : q_bit U j u = ∑ a : Fin (2 ^ j), w a * r a := by
        unfold q_bit; rw [ite_eq_right_iff.mpr (fun h => absurd h hU0), W_bit1_conv_eq hj X Z u, Finset.sum_div]
        apply Finset.sum_congr rfl; intro a _; dsimp [w, r]; ring
      have hconc_bin : ConcaveOn ℝ (Set.Icc 0 1) Real.binEntropy := by
        have h1 : ConcaveOn ℝ (Set.Icc 0 1) Real.negMulLog :=
          Real.strictConcaveOn_negMulLog.concaveOn.subset (fun x hx => hx.1) (convex_Icc 0 1)
        have h2 : ConcaveOn ℝ (Set.Icc 0 1) (fun p => Real.negMulLog (1 - p)) := by
          refine ⟨convex_Icc 0 1, ?_⟩
          intro x hx y hy a b ha hb hab
          have hx' : 1 - x ∈ Set.Ici (0 : ℝ) := by simp [Set.mem_Ici]; linarith [hx.2]
          have hy' : 1 - y ∈ Set.Ici (0 : ℝ) := by simp [Set.mem_Ici]; linarith [hy.2]
          have hlin : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by
            calc 1 - (a * x + b * y) = (a + b) - (a * x + b * y) := by rw [hab]
              _ = a * (1 - x) + b * (1 - y) := by ring
          simpa [smul_eq_mul, hlin] using Real.strictConcaveOn_negMulLog.concaveOn.2 hx' hy' ha hb hab
        have hbe : Real.binEntropy = Real.negMulLog + fun p => Real.negMulLog (1 - p) := by
          ext p; exact Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub p
        rw [hbe]; exact h1.add h2
      have hjens := hconc_bin.le_map_sum hw0 hw1 hr_mem
      simp only [smul_eq_mul] at hjens
      rw [← hqU_eq] at hjens
      have hmul := mul_le_mul_of_nonneg_left hjens hUpos.le
      refine le_trans ?_ hmul
      rw [Finset.mul_sum]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro a _
      dsimp [w, r]
      rw [binEntropy_xorProb_eq]
      field_simp [hU0]
  have hsum_u : condBitEnt U j ≥
      ∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
        W_pref X j a * W_pref Z j b *
          Real.binEntropy ((1 - |1 - 2 * q_bit X j a| * |1 - 2 * q_bit Z j b|) / 2) := by
    have h1 : condBitEnt U j ≥
        ∑ u : Fin (2 ^ j), ∑ a : Fin (2 ^ j),
          W_pref X j a * W_pref Z j (subModFin hNj u a) *
            Real.binEntropy ((1 - |1 - 2 * q_bit X j a| * |1 - 2 * q_bit Z j (subModFin hNj u a)|) / 2) :=
      Finset.sum_le_sum fun u _ => hconc_u u
    refine le_trans ?_ h1
    conv_rhs => rw [Finset.sum_comm]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro a _
    let e : Fin (2 ^ j) ≃ Fin (2 ^ j) :=
      { toFun := fun u => subModFin hNj u a
        invFun := fun b => ⟨(a.val + b.val) % 2 ^ j, Nat.mod_lt _ hNj⟩
        left_inv := fun u => by apply Fin.ext; exact add_subModFin_mod hNj u a
        right_inv := fun b => by
          apply Fin.ext; dsimp [subModFin]
          have ha := a.isLt; have hb := b.isLt
          by_cases h : a.val + b.val < 2 ^ j
          · rw [Nat.mod_eq_of_lt h]
            have : a.val + b.val + (2 ^ j - a.val) = b.val + 2 ^ j := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
          · have h1 : (a.val + b.val) % 2 ^ j = a.val + b.val - 2 ^ j := by
              calc (a.val + b.val) % 2 ^ j = ((a.val + b.val - 2 ^ j) + 2 ^ j) % 2 ^ j := by congr 1; omega
                _ = (a.val + b.val - 2 ^ j) % 2 ^ j := Nat.add_mod_right _ _
                _ = a.val + b.val - 2 ^ j := Nat.mod_eq_of_lt (by omega)
            rw [h1]
            have : a.val + b.val - 2 ^ j + (2 ^ j - a.val) = b.val := by omega
            rw [this, Nat.mod_eq_of_lt hb] }
    exact (Equiv.sum_comp e _).symm
  have hX_double : condBitEnt X j =
      ∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
        W_pref X j a * W_pref Z j b * Real.binEntropy (q_bit X j a) := by
    unfold condBitEnt
    apply Finset.sum_congr rfl
    intro a _
    have hfactor : ∑ b : Fin (2 ^ j), W_pref X j a * W_pref Z j b * Real.binEntropy (q_bit X j a) =
        (∑ b : Fin (2 ^ j), W_pref Z j b) * (W_pref X j a * Real.binEntropy (q_bit X j a)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro b _; ring
    rw [hfactor, W_pref_sum_one Z j, one_mul]
  have hdiff_ge : condBitEnt U j - condBitEnt X j ≥
      (∑ b : Fin (2 ^ j), W_pref Z j b * f4nat (Real.binEntropy (q_bit Z j b))) *
        (Real.log 2 - condBitEnt X j) := by
    have h1 : condBitEnt U j - condBitEnt X j ≥
        ∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
          W_pref X j a * W_pref Z j b *
            (f4nat (Real.binEntropy (q_bit Z j b)) * (Real.log 2 - Real.binEntropy (q_bit X j a))) := by
      have hsub : (∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
          W_pref X j a * W_pref Z j b *
            Real.binEntropy ((1 - |1 - 2 * q_bit X j a| * |1 - 2 * q_bit Z j b|) / 2)) - condBitEnt X j =
          ∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
            W_pref X j a * W_pref Z j b *
              (Real.binEntropy ((1 - |1 - 2 * q_bit X j a| * |1 - 2 * q_bit Z j b|) / 2) - Real.binEntropy (q_bit X j a)) := by
        rw [hX_double, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro a _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro b _; ring
      have hpt : ∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
          W_pref X j a * W_pref Z j b *
            (f4nat (Real.binEntropy (q_bit Z j b)) * (Real.log 2 - Real.binEntropy (q_bit X j a))) ≤
          ∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
            W_pref X j a * W_pref Z j b *
              (Real.binEntropy ((1 - |1 - 2 * q_bit X j a| * |1 - 2 * q_bit Z j b|) / 2) - Real.binEntropy (q_bit X j a)) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        apply mul_le_mul_of_nonneg_left
        · exact binEntropy_xor_gain_f4nat (q_bit_bounds X j a).1 (q_bit_bounds X j a).2
            (q_bit_bounds Z j b).1 (q_bit_bounds Z j b).2
        · exact mul_nonneg (W_pref_nonneg X j a) (W_pref_nonneg Z j b)
      linarith
    have hfac : (∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
        W_pref X j a * W_pref Z j b *
          (f4nat (Real.binEntropy (q_bit Z j b)) * (Real.log 2 - Real.binEntropy (q_bit X j a)))) =
        (∑ b : Fin (2 ^ j), W_pref Z j b * f4nat (Real.binEntropy (q_bit Z j b))) *
          (Real.log 2 - condBitEnt X j) := by
      have hX_def : Real.log 2 - condBitEnt X j =
          ∑ a : Fin (2 ^ j), W_pref X j a * (Real.log 2 - Real.binEntropy (q_bit X j a)) := by
        unfold condBitEnt
        rw [Finset.sum_congr rfl (fun a _ => mul_sub _ _ _), Finset.sum_sub_distrib,
            ← Finset.sum_mul, W_pref_sum_one X j, one_mul]
      rw [hX_def, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro b _; ring
    linarith
  have hjens : f4nat (condBitEnt Z j) ≤
      ∑ b : Fin (2 ^ j), W_pref Z j b * f4nat (Real.binEntropy (q_bit Z j b)) := by
    have h := convexOn_f4nat.map_sum_le
      (t := Finset.univ)
      (w := fun b : Fin (2 ^ j) => W_pref Z j b)
      (p := fun b : Fin (2 ^ j) => Real.binEntropy (q_bit Z j b))
      (fun b _ => W_pref_nonneg Z j b)
      (W_pref_sum_one Z j)
      (fun b _ => binEntropy_mem_Icc (q_bit_bounds Z j b).1 (q_bit_bounds Z j b).2)
    simpa [condBitEnt, smul_eq_mul] using h
  have hdef_nonneg : 0 ≤ Real.log 2 - condBitEnt X j := by
    linarith [(condBitEnt_bounds X j).2]
  nlinarith

/-- Lemma 2' (Sharp Bitwise Chain-Rule Entropy Gain on `Fin (2^k)`):
    `Hnat (conv X Z) - Hnat X ≥ ∑ j : Fin k, f4nat (condBitEnt Z j) * (log 2 - condBitEnt X j)`. -/
theorem Hnat_conv_sub_ge_bitwise_f4nat {k : ℕ} (X Z : PMF_Fin (2 ^ k)) :
    Hnat (convPMF (Nat.two_pow_pos k) X Z) - Hnat X ≥
      ∑ j : Fin k, f4nat (condBitEnt Z j.val) * (Real.log 2 - condBitEnt X j.val) := by
  rw [Hnat_eq_sum_condBitEnt, Hnat_eq_sum_condBitEnt, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact condBitEnt_conv_sub_ge_f4nat j.isLt X Z

end Erdos18

#print axioms Erdos18.convexOn_f4nat
#print axioms Erdos18.binEntropy_f4nat_le
#print axioms Erdos18.Hnat_conv_sub_ge_bitwise_f4nat
