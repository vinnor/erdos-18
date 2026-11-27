import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units

/-!
# Erdos18/PrimeFieldEntropy.lean — Prime-Field Dilation Entropy-Gain Theory (Module 1)

Formalizes Lemmas 1 and 2 of the unconditional `h(n!) = O((log n)^3 log log(n+16))` proof:
- `PMF_ZMod q`: probability mass functions on `ZMod q` (`[NeZero q]`).
- `Hnat_zmod`, `deficit_zmod`, `klDiv_zmod`, `conv_dilate`.
- `pointwise_kl_contraction_le` (Lemma 1): Pointwise KL contraction on `ZMod q` (`3 ≤ q`) with
  absolute constant `c₁ = 1 / 484`:
    `klDiv_zmod p.p (Tr_val q p r) ≥ (1 / 484) * (min (log (1 / r)) (log q) / log q) * deficit_zmod p`.
- `fq_uniform_dilation_entropy_gain` (Lemma 2a): For prime `q ≥ 3` and independent `U, V` on `ZMod q`,
    `(1 / (q - 1)) * ∑ c ≠ 0, (Hnat_zmod (conv_dilate U V c) - Hnat_zmod U) ≥
      (1 / (2420 * log q)) * (Hnat_zmod V - 5 * log q / q) * deficit_zmod U`.
- `fq_general_dilation_entropy_gain` (Lemma 2b): General dilator distribution `W` on `(ZMod q)ˣ`
  with `∀ c ≠ 0, c_dil / (q - 1) ≤ W c`.
-/

namespace Erdos18

open Finset Real

/-! ## Basic Definitions on `ZMod q` -/

/-- A probability mass function on `ZMod q`. -/
@[ext]
structure PMF_ZMod (q : ℕ) [NeZero q] where
  p : ZMod q → ℝ
  nonneg : ∀ x, 0 ≤ p x
  sum_one : ∑ x : ZMod q, p x = 1

lemma PMF_ZMod.le_one {q : ℕ} [NeZero q] (μ : PMF_ZMod q) (x : ZMod q) : μ.p x ≤ 1 := by
  rw [← μ.sum_one]
  exact Finset.single_le_sum (fun y _ => μ.nonneg y) (Finset.mem_univ x)

/-- Shannon entropy in nats on `ZMod q`: `Hnat_zmod μ = ∑ x, -μ(x) * log(μ(x))`. -/
noncomputable def Hnat_zmod {q : ℕ} [NeZero q] (μ : PMF_ZMod q) : ℝ :=
  ∑ x : ZMod q, Real.negMulLog (μ.p x)

/-- Entropy deficit from uniform on `ZMod q`: `Δ_q(μ) = log q - Hnat_zmod μ`. -/
noncomputable def deficit_zmod {q : ℕ} [NeZero q] (μ : PMF_ZMod q) : ℝ :=
  Real.log (q : ℝ) - Hnat_zmod μ

/-- KL divergence in nats on `ZMod q`: `∑ x, p x * log (p x / Q x)` (with `0 * log 0 = 0`). -/
noncomputable def klDiv_zmod {q : ℕ} [NeZero q] (p Q : ZMod q → ℝ) : ℝ :=
  ∑ x : ZMod q, p x * Real.log (p x / Q x)

/-- Law of `U + c * V` on `ZMod q` for independent `U, V`. -/
noncomputable def conv_dilate {q : ℕ} [NeZero q] (U V : PMF_ZMod q) (c : ZMod q) : PMF_ZMod q where
  p x := ∑ y : ZMod q, U.p (x - c * y) * V.p y
  nonneg x := Finset.sum_nonneg fun y _ => mul_nonneg (U.nonneg _) (V.nonneg _)
  sum_one := by
    rw [Finset.sum_comm]
    calc ∑ y : ZMod q, ∑ x : ZMod q, U.p (x - c * y) * V.p y
        = ∑ y : ZMod q, (∑ x : ZMod q, U.p (x - c * y)) * V.p y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ y : ZMod q, 1 * V.p y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have hbij : ∑ x : ZMod q, U.p (x - c * y) = ∑ x : ZMod q, U.p x :=
            Equiv.sum_comp (Equiv.subRight (c * y)) U.p
          rw [hbij, U.sum_one]
      _ = 1 := by simp [V.sum_one]

/-- Smoothed distribution `T_r(p)(x) = r * p(x) + (1 - r) * (1 - p(x)) / (q - 1)`. -/
noncomputable def Tr_val (q : ℕ) [NeZero q] (p : PMF_ZMod q) (r : ℝ) (x : ZMod q) : ℝ :=
  r * p.p x + (1 - r) * (1 - p.p x) / ((q : ℝ) - 1)

lemma Hnat_zmod_nonneg {q : ℕ} [NeZero q] (μ : PMF_ZMod q) : 0 ≤ Hnat_zmod μ := by
  unfold Hnat_zmod
  exact Finset.sum_nonneg fun x _ => Real.negMulLog_nonneg (μ.nonneg x) (μ.le_one x)

lemma deficit_zmod_eq_sum_B {q : ℕ} [NeZero q] (μ : PMF_ZMod q) :
    deficit_zmod μ = (1 / (q : ℝ)) *
      ∑ x : ZMod q, ((q : ℝ) * μ.p x * Real.log ((q : ℝ) * μ.p x) - ((q : ℝ) * μ.p x - 1)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq_ne : (q : ℝ) ≠ 0 := hq_pos.ne'
  have hsum_u : ∑ x : ZMod q, ((q : ℝ) * μ.p x - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, μ.sum_one, Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul, mul_one, sub_self]
  rw [Finset.sum_sub_distrib, hsum_u, sub_zero]
  unfold deficit_zmod Hnat_zmod
  have hterm : ∀ x : ZMod q,
      (q : ℝ) * μ.p x * Real.log ((q : ℝ) * μ.p x) =
        (q : ℝ) * (μ.p x * Real.log (q : ℝ) - Real.negMulLog (μ.p x)) := by
    intro x
    by_cases hx : μ.p x = 0
    · simp [hx, Real.negMulLog_zero]
    · rw [Real.log_mul hq_ne hx, Real.negMulLog]
      ring
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, μ.sum_one, one_mul]
  field_simp [hq_ne]

lemma B_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ u * Real.log u - (u - 1) := by
  rcases eq_or_lt_of_le hu with rfl | hpos
  · simp
  · have hlog : Real.log (1 / u) ≤ 1 / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [one_div, Real.log_inv] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
    have h1 : u * (u⁻¹ - 1) = 1 - u := by field_simp [hpos.ne']
    linarith

lemma deficit_zmod_nonneg {q : ℕ} [NeZero q] (μ : PMF_ZMod q) : 0 ≤ deficit_zmod μ := by
  rw [deficit_zmod_eq_sum_B]
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => B_nonneg ?_)
  exact mul_nonneg hq_pos.le (μ.nonneg x)

lemma Hnat_zmod_le_log {q : ℕ} [NeZero q] (μ : PMF_ZMod q) :
    Hnat_zmod μ ≤ Real.log (q : ℝ) := by
  have h := deficit_zmod_nonneg μ
  unfold deficit_zmod at h
  linarith

/-! ## Lemma 1: Pointwise KL Contraction Lemma -/

private lemma Tr_val_pos {q : ℕ} [NeZero q] (hq : 3 ≤ q) (p : PMF_ZMod q)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) (x : ZMod q) :
    0 < Tr_val q p r x := by
  unfold Tr_val
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have h1r : 0 < 1 - r := by linarith
  have hp0 : 0 ≤ p.p x := p.nonneg x
  have hp1 : p.p x ≤ 1 := p.le_one x
  rcases eq_or_lt_of_le hp0 with hx | hx
  · rw [← hx]; positivity
  · have h2 : 0 ≤ (1 - r) * (1 - p.p x) / ((q : ℝ) - 1) := by
      have : 0 ≤ 1 - p.p x := by linarith
      positivity
    linarith [mul_pos hr0 hx]

/-- Subcase 2a of Lemma 1: for `θ ∈ (0, 1/2]` and `u ∈ [0, 10/θ]`,
`u * log (u / (θ * u + 1 - θ)) - (1 - θ) * (u - 1) ≥ (1 / 484) * (u * log u - (u - 1))`. -/
private lemma lemma1_subcase_2a {θ u : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hu0 : 0 ≤ u) (hu_hi : u ≤ 10 / θ) :
    (1 / 484 : ℝ) * (u * Real.log u - (u - 1)) ≤
      u * Real.log (u / (θ * u + 1 - θ)) - (1 - θ) * (u - 1) := by
  set a : ℝ := 1 - θ
  have ha_ge : (1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have ha_pos : 0 < a := by linarith
  let h : ℝ → ℝ := fun t =>
    t * Real.log (t / (θ * t + a)) - a * (t - 1) - (1 / 484 : ℝ) * (t * Real.log t - (t - 1))
  suffices hgoal : 0 ≤ h u by
    have ha_eq : θ * u + a = θ * u + 1 - θ := by dsimp [a]; ring
    dsimp [h] at hgoal
    rw [ha_eq] at hgoal
    dsimp [a] at hgoal
    linarith
  rcases eq_or_lt_of_le hu0 with rfl | hu_pos
  · simp only [h, zero_mul, zero_sub, mul_neg, mul_one, neg_neg]
    linarith
  let h' : ℝ → ℝ := fun t =>
    Real.log (t / (θ * t + a)) + a / (θ * t + a) - a - (1 / 484 : ℝ) * Real.log t
  have hden_pos : ∀ t : ℝ, 0 < t → 0 < θ * t + a := fun t ht => by positivity
  have hderiv1 : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt h (h' t) t := by
    intro t ht
    have ht_pos : 0 < t := ht
    have hd_pos : 0 < θ * t + a := hden_pos t ht_pos
    have hd_lin : HasDerivAt (fun s : ℝ => θ * s + a) θ t := by
      simpa using ((hasDerivAt_id t).const_mul θ).add_const a
    have hlog_den : HasDerivAt (fun s : ℝ => Real.log (θ * s + a)) (θ / (θ * t + a)) t :=
      hd_lin.log hd_pos.ne'
    have hlog_t : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht_pos.ne'
    have ht_log_t : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t := by
      have := (hasDerivAt_id' t).mul hlog_t
      convert this using 1
      field_simp [ht_pos.ne']
    have ht_log_den : HasDerivAt (fun s : ℝ => s * Real.log (θ * s + a))
        (Real.log (θ * t + a) + t * (θ / (θ * t + a))) t := by
      have := (hasDerivAt_id' t).mul hlog_den
      convert this using 1
      ring
    have heq : ∀ᶠ s in nhds t, h s =
        s * Real.log s - s * Real.log (θ * s + a) - a * (s - 1) -
          (1 / 484 : ℝ) * (s * Real.log s - (s - 1)) := by
      filter_upwards [eventually_gt_nhds ht_pos] with s hs
      have hds : 0 < θ * s + a := hden_pos s hs
      dsimp [h]
      rw [Real.log_div hs.ne' hds.ne']
      ring
    have hd_rhs : HasDerivAt
        (fun s : ℝ => s * Real.log s - s * Real.log (θ * s + a) - a * (s - 1) -
          (1 / 484 : ℝ) * (s * Real.log s - (s - 1)))
        (h' t) t := by
      have hsub1 : HasDerivAt (fun s : ℝ => s - 1) 1 t := (hasDerivAt_id t).sub_const 1
      have h_all := ((ht_log_t.sub ht_log_den).sub (hsub1.const_mul a)).sub
        ((ht_log_t.sub hsub1).const_mul (1 / 484 : ℝ))
      convert h_all using 1
      dsimp [h']
      rw [Real.log_div ht_pos.ne' hd_pos.ne']
      field_simp [hd_pos.ne']
      ring
    exact hd_rhs.congr_of_eventuallyEq heq
  have hderiv2 : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt h' (a ^ 2 / (t * (θ * t + a) ^ 2) - (1 / 484 : ℝ) / t) t := by
    intro t ht
    have ht_pos : 0 < t := ht
    have hd_pos : 0 < θ * t + a := hden_pos t ht_pos
    have hd_lin : HasDerivAt (fun s : ℝ => θ * s + a) θ t := by
      simpa using ((hasDerivAt_id t).const_mul θ).add_const a
    have hlog_den : HasDerivAt (fun s : ℝ => Real.log (θ * s + a)) (θ / (θ * t + a)) t :=
      hd_lin.log hd_pos.ne'
    have hlog_t : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht_pos.ne'
    have h_inv_den : HasDerivAt (fun s : ℝ => a / (θ * s + a)) (-(a * θ) / (θ * t + a) ^ 2) t := by
      have := (hasDerivAt_const t a).div hd_lin hd_pos.ne'
      convert this using 1
      ring
    have heq : ∀ᶠ s in nhds t, h' s =
        Real.log s - Real.log (θ * s + a) + a / (θ * s + a) - a - (1 / 484 : ℝ) * Real.log s := by
      filter_upwards [eventually_gt_nhds ht_pos] with s hs
      have hds : 0 < θ * s + a := hden_pos s hs
      dsimp [h']
      rw [Real.log_div hs.ne' hds.ne']
    have hd_rhs : HasDerivAt
        (fun s : ℝ => Real.log s - Real.log (θ * s + a) + a / (θ * s + a) - a -
          (1 / 484 : ℝ) * Real.log s)
        (a ^ 2 / (t * (θ * t + a) ^ 2) - (1 / 484 : ℝ) / t) t := by
      have h_all := (((hlog_t.sub hlog_den).add h_inv_den).sub_const a).sub
        (hlog_t.const_mul (1 / 484 : ℝ))
      convert h_all using 1
      field_simp [ht_pos.ne', hd_pos.ne']
      ring
    exact hd_rhs.congr_of_eventuallyEq heq
  have h'_mono : MonotoneOn h' (Set.Ioc 0 (10 / θ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (10 / θ))
    · exact fun t ht => (hderiv2 t ht.1).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv2 t (interior_subset ht).1).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht_mem : t ∈ Set.Ioc 0 (10 / θ) := interior_subset ht
      have ht_pos : 0 < t := ht_mem.1
      have hd_pos : 0 < θ * t + a := hden_pos t ht_pos
      rw [(hderiv2 t ht_pos).deriv]
      have hθt : θ * t ≤ 10 := by
        have := mul_le_mul_of_nonneg_left ht_mem.2 hθ0.le
        rwa [mul_div_cancel₀ _ hθ0.ne'] at this
      have hden_le : θ * t + a ≤ 11 := by dsimp [a]; linarith
      have hden_sq : (θ * t + a) ^ 2 ≤ 121 := by nlinarith
      have ha_sq : (1 / 4 : ℝ) ≤ a ^ 2 := by nlinarith
      have hdiv : (1 / 484 : ℝ) / t ≤ a ^ 2 / (t * (θ * t + a) ^ 2) := by
        rw [div_le_div_iff₀ ht_pos (by positivity)]
        have : (1 / 484 : ℝ) * (θ * t + a) ^ 2 ≤ 1 / 4 := by linarith
        nlinarith
      linarith
  have h'_one : h' 1 = 0 := by
    have h1 : θ + a = 1 := by dsimp [a]; ring
    simp [h', h1]
  have h_one : h 1 = 0 := by
    have h1 : θ + a = 1 := by dsimp [a]; ring
    simp [h, h1]
  have h1_le : (1 : ℝ) ≤ 10 / θ := by
    rw [le_div_iff₀ hθ0]; linarith
  by_cases hu1 : u ≤ 1
  · have h_anti : AntitoneOn h (Set.Ioc 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
      · exact fun t ht => (hderiv1 t ht.1).continuousAt.continuousWithinAt
      · exact fun t ht => (hderiv1 t (interior_subset ht).1).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht_mem : t ∈ Set.Ioc 0 1 := interior_subset ht
        rw [(hderiv1 t ht_mem.1).deriv]
        have := h'_mono ⟨ht_mem.1, le_trans ht_mem.2 h1_le⟩ ⟨zero_lt_one, h1_le⟩ ht_mem.2
        linarith [h'_one]
    have := h_anti ⟨hu_pos, hu1⟩ ⟨zero_lt_one, le_rfl⟩ hu1
    linarith [h_one]
  · push Not at hu1
    have h_mono : MonotoneOn h (Set.Icc 1 (10 / θ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 1 (10 / θ))
      · exact fun t ht => (hderiv1 t (lt_of_lt_of_le zero_lt_one ht.1)).continuousAt.continuousWithinAt
      · exact fun t ht =>
          (hderiv1 t (lt_of_lt_of_le zero_lt_one (interior_subset ht).1)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht_mem : t ∈ Set.Icc 1 (10 / θ) := interior_subset ht
        have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_mem.1
        rw [(hderiv1 t ht_pos).deriv]
        have := h'_mono ⟨zero_lt_one, h1_le⟩ ⟨ht_pos, ht_mem.2⟩ ht_mem.1
        linarith [h'_one]
    have := h_mono ⟨le_rfl, h1_le⟩ ⟨hu1.le, hu_hi⟩ hu1.le
    linarith [h_one]

/-- Subcase 2b of Lemma 1: for `θ ∈ (0, 1/2]`, `θ < r ≤ 1/2`, and `10/θ < u ≤ q`,
`g_θ(u) ≥ (1 / 484) * (log (1 / r) / log q) * B(u)`. -/
private lemma lemma1_subcase_2b {q : ℕ} (hq : 3 ≤ q) {r θ u : ℝ}
    (hθ0 : 0 < θ) (hθr : θ < r) (hr1 : r ≤ 1 / 2)
    (hu_lo : 10 / θ < u) (hu_hi : u ≤ (q : ℝ)) :
    (1 / 484 : ℝ) * (Real.log (1 / r) / Real.log (q : ℝ)) * (u * Real.log u - (u - 1)) ≤
      u * Real.log (u / (θ * u + 1 - θ)) - (1 - θ) * (u - 1) := by
  have hθ1 : θ ≤ 1 / 2 := le_trans hθr.le hr1
  have hu_gt20 : (20 : ℝ) < u := by
    have : (20 : ℝ) ≤ 10 / θ := by rw [le_div_iff₀ hθ0]; linarith
    linarith
  have hu_pos : 0 < u := by linarith
  have hq_gt1 : (1 : ℝ) < (q : ℝ) := by
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_gt1
  have hden_pos : 0 < θ * u + 1 - θ := by nlinarith
  have hθu_gt10 : 10 < θ * u := by
    have := mul_lt_mul_of_pos_left hu_lo hθ0
    rwa [mul_div_cancel₀ _ hθ0.ne'] at this
  have hden_lt : θ * u + 1 - θ < (11 / 10 : ℝ) * (θ * u) := by linarith
  have hlog_step : Real.log (1 / θ) - Real.log (11 / 10) ≤ Real.log (u / (θ * u + 1 - θ)) := by
    have h11 : (0 : ℝ) < 11 / 10 := by norm_num
    rw [← Real.log_div (one_div_pos.mpr hθ0).ne' h11.ne']
    apply Real.log_le_log (div_pos (one_div_pos.mpr hθ0) h11)
    rw [div_le_div_iff₀ h11 hden_pos]
    have : (1 / θ) * (θ * u + 1 - θ) ≤ (11 / 10 : ℝ) * u := by
      have hmul := mul_le_mul_of_nonneg_left hden_lt.le (by positivity : (0 : ℝ) ≤ 1 / θ)
      refine hmul.trans_eq ?_
      field_simp [hθ0.ne']
    nlinarith
  have hlog_11_10 : Real.log (11 / 10 : ℝ) ≤ 1 / 10 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 10)
    linarith
  have hlog_2θ : Real.log (2 * θ) ≤ 2 * θ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlog_inv_θ : Real.log (1 / θ) = Real.log 2 - Real.log (2 * θ) := by
    have h1 : (1 : ℝ) / θ = 2 / (2 * θ) := by field_simp [hθ0.ne']
    rw [h1, Real.log_div (by norm_num) (by positivity)]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hmargin : (1 / 484 : ℝ) * Real.log (1 / θ) ≤
      Real.log (1 / θ) - Real.log (11 / 10) - (1 - θ) := by
    linarith
  have hr0 : 0 < r := lt_trans hθ0 hθr
  have hlog_r_le : Real.log (1 / r) ≤ Real.log (1 / θ) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hθ0 hθr.le)
  have hlog_r_pos : 0 < Real.log (1 / r) := by
    apply Real.log_pos
    rw [one_lt_div (lt_trans hθ0 hθr)]
    linarith
  have hB_le : u * Real.log u - (u - 1) ≤ u * Real.log (q : ℝ) := by
    have hlu : Real.log u ≤ Real.log (q : ℝ) := Real.log_le_log hu_pos hu_hi
    have : u * Real.log u ≤ u * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left hlu hu_pos.le
    linarith
  have h_lhs_le :
      (1 / 484 : ℝ) * (Real.log (1 / r) / Real.log (q : ℝ)) * (u * Real.log u - (u - 1)) ≤
        (1 / 484 : ℝ) * u * Real.log (1 / θ) := by
    have h1 : (1 / 484 : ℝ) * (Real.log (1 / r) / Real.log (q : ℝ)) * (u * Real.log u - (u - 1)) ≤
        (1 / 484 : ℝ) * (Real.log (1 / r) / Real.log (q : ℝ)) * (u * Real.log (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hB_le (by positivity)
    have h2 : (1 / 484 : ℝ) * (Real.log (1 / r) / Real.log (q : ℝ)) * (u * Real.log (q : ℝ)) =
        (1 / 484 : ℝ) * u * Real.log (1 / r) := by
      field_simp [hlogq_pos.ne']
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hlog_r_le (by positivity))
  have h_rhs_ge :
      u * (Real.log (1 / θ) - Real.log (11 / 10) - (1 - θ)) ≤
        u * Real.log (u / (θ * u + 1 - θ)) - (1 - θ) * (u - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hlog_step hu_pos.le
    nlinarith
  have h_mid : (1 / 484 : ℝ) * u * Real.log (1 / θ) ≤
      u * (Real.log (1 / θ) - Real.log (11 / 10) - (1 - θ)) := by
    have := mul_le_mul_of_nonneg_left hmargin hu_pos.le
    linarith
  linarith

/-- **Lemma 1 (Pointwise KL Contraction Lemma):**
For `q ≥ 3`, any PMF `p` on `ZMod q`, and `r ∈ (0, 1/2]`,
`klDiv_zmod p.p (Tr_val q p r) ≥ (1 / 484) * (min (log (1 / r)) (log q) / log q) * deficit_zmod p`. -/
theorem pointwise_kl_contraction_le {q : ℕ} [NeZero q] (hq : 3 ≤ q) (p : PMF_ZMod q)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    (1 / 484 : ℝ) * (min (Real.log (1 / r)) (Real.log (q : ℝ)) / Real.log (q : ℝ)) *
        deficit_zmod p ≤
      klDiv_zmod p.p (Tr_val q p r) := by
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq_ne : (q : ℝ) ≠ 0 := hq_pos.ne'
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  set θ : ℝ := ((q : ℝ) * r - 1) / ((q : ℝ) - 1)
  have hTr_eq : ∀ x : ZMod q, (q : ℝ) * Tr_val q p r x = 1 + θ * ((q : ℝ) * p.p x - 1) := by
    intro x
    unfold Tr_val
    dsimp [θ]
    field_simp [hq1_pos.ne']
    ring
  by_cases hcase : r ≤ 1 / (q : ℝ)
  · -- Case 1: 0 < r ≤ 1 / q, so θ ≤ 0 and KL(p || T_r(p)) ≥ deficit_zmod p
    have hθ_nonpos : θ ≤ 0 := by
      dsimp [θ]
      apply div_nonpos_of_nonpos_of_nonneg _ hq1_pos.le
      have := mul_le_mul_of_nonneg_left hcase hq_pos.le
      rw [mul_one_div_cancel hq_ne] at this
      linarith
    have hdiff_ge : 0 ≤ klDiv_zmod p.p (Tr_val q p r) - deficit_zmod p := by
      have hrewrite : klDiv_zmod p.p (Tr_val q p r) - deficit_zmod p =
          ∑ x : ZMod q, -(p.p x * Real.log ((q : ℝ) * Tr_val q p r x)) := by
        unfold klDiv_zmod deficit_zmod Hnat_zmod
        have h1 : Real.log (q : ℝ) = ∑ x : ZMod q, p.p x * Real.log (q : ℝ) := by
          rw [← Finset.sum_mul, p.sum_one, one_mul]
        rw [h1, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : p.p x = 0
        · simp [hx, Real.negMulLog_zero]
        · have hTr_p : 0 < Tr_val q p r x := Tr_val_pos hq p hr0 hr1 x
          rw [Real.log_div hx hTr_p.ne', Real.log_mul hq_ne hTr_p.ne', Real.negMulLog]
          ring
      rw [hrewrite]
      have hterm : ∀ x : ZMod q,
          -(θ * p.p x * ((q : ℝ) * p.p x - 1)) ≤ -(p.p x * Real.log ((q : ℝ) * Tr_val q p r x)) := by
        intro x
        have hTr_p : 0 < (q : ℝ) * Tr_val q p r x := mul_pos hq_pos (Tr_val_pos hq p hr0 hr1 x)
        have hlog := Real.log_le_sub_one_of_pos hTr_p
        have hlog' : Real.log ((q : ℝ) * Tr_val q p r x) ≤ θ * ((q : ℝ) * p.p x - 1) := by
          linarith [hTr_eq x]
        have hmul := mul_le_mul_of_nonneg_left hlog' (p.nonneg x)
        linarith
      refine le_trans ?_ (Finset.sum_le_sum fun x _ => hterm x)
      have hcs : (1 : ℝ) ≤ (q : ℝ) * ∑ x : ZMod q, (p.p x) ^ 2 := by
        have hsq_nn : 0 ≤ ∑ x : ZMod q, ((q : ℝ) * p.p x - 1) ^ 2 :=
          Finset.sum_nonneg fun x _ => sq_nonneg _
        have hexpand : ∑ x : ZMod q, ((q : ℝ) * p.p x - 1) ^ 2 =
            (q : ℝ) * ((q : ℝ) * (∑ x : ZMod q, (p.p x) ^ 2) - 1) := by
          have h1 : ∀ x : ZMod q, ((q : ℝ) * p.p x - 1) ^ 2 =
              (q : ℝ) ^ 2 * (p.p x) ^ 2 - 2 * (q : ℝ) * p.p x + 1 := fun x => by ring
          simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            p.sum_one, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
          ring
        rw [hexpand] at hsq_nn
        nlinarith
      have hsum_eq : ∑ x : ZMod q, -(θ * p.p x * ((q : ℝ) * p.p x - 1)) =
          (-θ) * ((q : ℝ) * (∑ x : ZMod q, (p.p x) ^ 2) - 1) := by
        have h1 : ∀ x : ZMod q, -(θ * p.p x * ((q : ℝ) * p.p x - 1)) =
            (-θ) * ((q : ℝ) * (p.p x) ^ 2 - p.p x) := fun x => by ring
        simp_rw [h1, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, p.sum_one]
      rw [hsum_eq]
      exact mul_nonneg (by linarith) (by linarith)
    have hcoeff : (1 / 484 : ℝ) * (min (Real.log (1 / r)) (Real.log (q : ℝ)) / Real.log (q : ℝ)) ≤ 1 := by
      have hmin : min (Real.log (1 / r)) (Real.log (q : ℝ)) / Real.log (q : ℝ) ≤ 1 := by
        rw [div_le_one hlogq_pos]; exact min_le_right _ _
      linarith
    have hdef := deficit_zmod_nonneg p
    nlinarith
  · -- Case 2: 1 / q < r ≤ 1 / 2
    push Not at hcase
    have hqr_gt1 : 1 < (q : ℝ) * r := by
      have := mul_lt_mul_of_pos_left hcase hq_pos
      rwa [mul_one_div_cancel hq_ne] at this
    have hθ_pos : 0 < θ := div_pos (by linarith) hq1_pos
    have hθ_lt_r : θ < r := by
      dsimp [θ]
      rw [div_lt_iff₀ hq1_pos]
      nlinarith
    have hθ_le_half : θ ≤ 1 / 2 := le_trans hθ_lt_r.le hr1
    have hlog_r_lt : Real.log (1 / r) < Real.log (q : ℝ) := by
      apply Real.log_lt_log (by positivity)
      rw [div_lt_iff₀ hr0]
      linarith
    rw [min_eq_left hlog_r_lt.le]
    have hlog_r_pos : 0 < Real.log (1 / r) := by
      apply Real.log_pos; rw [one_lt_div hr0]; linarith
    have hγ_le1 : Real.log (1 / r) / Real.log (q : ℝ) ≤ 1 := by
      rw [div_le_one hlogq_pos]; exact hlog_r_lt.le
    have hKL_eq : klDiv_zmod p.p (Tr_val q p r) = (1 / (q : ℝ)) *
        ∑ x : ZMod q, ((q : ℝ) * p.p x * Real.log (((q : ℝ) * p.p x) / (θ * ((q : ℝ) * p.p x) + 1 - θ)) -
          (1 - θ) * ((q : ℝ) * p.p x - 1)) := by
      have hsum_u : ∑ x : ZMod q, (1 - θ) * ((q : ℝ) * p.p x - 1) = 0 := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, p.sum_one,
            Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one,
            sub_self, mul_zero]
      rw [Finset.sum_sub_distrib, hsum_u, sub_zero]
      unfold klDiv_zmod
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hden_eq : θ * ((q : ℝ) * p.p x) + 1 - θ = (q : ℝ) * Tr_val q p r x := by
        rw [hTr_eq x]; ring
      rw [hden_eq, mul_div_mul_left _ _ hq_ne]
      field_simp [hq_ne]
    rw [hKL_eq, deficit_zmod_eq_sum_B]
    have hpull : (1 / 484 : ℝ) * (Real.log (1 / r) / Real.log (q : ℝ)) *
        ((1 / (q : ℝ)) * ∑ x : ZMod q, ((q : ℝ) * p.p x * Real.log ((q : ℝ) * p.p x) - ((q : ℝ) * p.p x - 1))) =
        (1 / (q : ℝ)) * ∑ x : ZMod q,
          (1 / 484 : ℝ) * (Real.log (1 / r) / Real.log (q : ℝ)) *
            ((q : ℝ) * p.p x * Real.log ((q : ℝ) * p.p x) - ((q : ℝ) * p.p x - 1)) := by
      rw [← Finset.mul_sum]; ring
    rw [hpull]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
    set u : ℝ := (q : ℝ) * p.p x
    have hu0 : 0 ≤ u := mul_nonneg hq_pos.le (p.nonneg x)
    have hu_hi : u ≤ (q : ℝ) := by
      dsimp [u]
      have := mul_le_mul_of_nonneg_left (p.le_one x) hq_pos.le
      linarith
    by_cases hu_split : u ≤ 10 / θ
    · have h2a := lemma1_subcase_2a hθ_pos hθ_le_half hu0 hu_split
      have hB0 : 0 ≤ u * Real.log u - (u - 1) := B_nonneg hu0
      have hmul : (1 / 484 : ℝ) * (Real.log (1 / r) / Real.log (q : ℝ)) * (u * Real.log u - (u - 1)) ≤
          (1 / 484 : ℝ) * (u * Real.log u - (u - 1)) := by
        nlinarith
      exact hmul.trans h2a
    · push Not at hu_split
      exact lemma1_subcase_2b hq hθ_pos hθ_lt_r hr1 hu_split hu_hi

/-! ## Lemma 2: Universal Prime-Field Dilation Entropy-Gain Theorem -/

/-- Exact pointwise convexity of `t ↦ a * log (a / (r * a + (1 - r) * t))` on `[0, ∞)`
for `a > 0` and `r ∈ (0, 1)`. -/
private lemma convexOn_kl_slice {a r : ℝ} (ha : 0 < a) (hr0 : 0 < r) (hr1 : r < 1) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => a * Real.log (a / (r * a + (1 - r) * t))) := by
  let f : ℝ → ℝ := fun t => a * Real.log (a / (r * a + (1 - r) * t))
  let f' : ℝ → ℝ := fun t => -(a * (1 - r)) / (r * a + (1 - r) * t)
  have hden_pos : ∀ t ∈ Set.Ici (0 : ℝ), 0 < r * a + (1 - r) * t := fun t ht => by
    have : 0 ≤ (1 - r) * t := mul_nonneg (by linarith) ht
    linarith [mul_pos hr0 ha]
  have hd1 : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt f (f' t) t := by
    intro t ht
    have hdp : 0 < r * a + (1 - r) * t := hden_pos t ht
    have hlin : HasDerivAt (fun s : ℝ => r * a + (1 - r) * s) (1 - r) t := by
      simpa using ((hasDerivAt_id t).const_mul (1 - r)).const_add (r * a)
    have hlog : HasDerivAt (fun s : ℝ => Real.log (r * a + (1 - r) * s))
        ((1 - r) / (r * a + (1 - r) * t)) t := hlin.log hdp.ne'
    have heq : ∀ᶠ s in nhds t, f s = a * Real.log a - a * Real.log (r * a + (1 - r) * s) := by
      have hopen : IsOpen {s : ℝ | 0 < r * a + (1 - r) * s} :=
        isOpen_lt continuous_const (by fun_prop)
      filter_upwards [hopen.mem_nhds hdp] with s hs
      dsimp [f]
      rw [Real.log_div ha.ne' hs.ne']
      ring
    have hd_rhs : HasDerivAt (fun s : ℝ => a * Real.log a - a * Real.log (r * a + (1 - r) * s))
        (f' t) t := by
      have := (hasDerivAt_const t (a * Real.log a)).sub (hlog.const_mul a)
      convert this using 1
      dsimp [f']
      ring
    exact hd_rhs.congr_of_eventuallyEq heq
  have hd2 : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt f' (a * (1 - r) ^ 2 / (r * a + (1 - r) * t) ^ 2) t := by
    intro t ht
    have hdp : 0 < r * a + (1 - r) * t := hden_pos t (Set.Ioi_subset_Ici_self ht)
    have hlin : HasDerivAt (fun s : ℝ => r * a + (1 - r) * s) (1 - r) t := by
      simpa using ((hasDerivAt_id t).const_mul (1 - r)).const_add (r * a)
    have hq := (hasDerivAt_const t (-(a * (1 - r)))).div hlin hdp.ne'
    convert hq using 1
    ring
  apply convexOn_of_deriv2_nonneg (convex_Ici (0 : ℝ))
  · exact fun t ht => (hd1 t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hd1 t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hderiv_eq : ∀ᶠ s in nhds t, deriv f s = f' s := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact (hd1 s (Set.Ioi_subset_Ici_self hs)).deriv
    exact ((hd2 t ht).congr_of_eventuallyEq hderiv_eq).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hderiv_eq : ∀ᶠ s in nhds t, deriv f s = f' s := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact (hd1 s (Set.Ioi_subset_Ici_self hs)).deriv
    have h2 : deriv (deriv f) t = a * (1 - r) ^ 2 / (r * a + (1 - r) * t) ^ 2 :=
      ((hd2 t ht).congr_of_eventuallyEq hderiv_eq).deriv
    change 0 ≤ deriv (deriv f) t
    rw [h2]
    have hdp : 0 < r * a + (1 - r) * t := hden_pos t (Set.Ioi_subset_Ici_self ht)
    positivity

/-- Entropy non-decrease under convolution with a dilated variable:
`0 ≤ Hnat_zmod (conv_dilate U V c) - Hnat_zmod U`. -/
theorem Hnat_conv_dilate_sub_nonneg {q : ℕ} [NeZero q] (U V : PMF_ZMod q) (c : ZMod q) :
    0 ≤ Hnat_zmod (conv_dilate U V c) - Hnat_zmod U := by
  have hconc : ConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.negMulLog := Real.concaveOn_negMulLog
  have hsum : ∀ x : ZMod q,
      ∑ y : ZMod q, V.p y * Real.negMulLog (U.p (x - c * y)) ≤
        Real.negMulLog ((conv_dilate U V c).p x) := by
    intro x
    have h := hconc.le_map_sum (t := Finset.univ) (w := V.p) (p := fun y => U.p (x - c * y))
      (fun y _ => V.nonneg y) V.sum_one (fun y _ => U.nonneg _)
    simpa only [smul_eq_mul, conv_dilate, mul_comm (V.p _)] using h
  have htot := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hsum x
  have hlhs : ∑ x : ZMod q, ∑ y : ZMod q, V.p y * Real.negMulLog (U.p (x - c * y)) =
      Hnat_zmod U := by
    rw [Finset.sum_comm]
    calc ∑ y : ZMod q, ∑ x : ZMod q, V.p y * Real.negMulLog (U.p (x - c * y))
        = ∑ y : ZMod q, V.p y * ∑ x : ZMod q, Real.negMulLog (U.p (x - c * y)) := by
          refine Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
      _ = ∑ y : ZMod q, V.p y * Hnat_zmod U := by
          refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          exact Equiv.sum_comp (Equiv.subRight (c * y)) (fun z => Real.negMulLog (U.p z))
      _ = Hnat_zmod U := by rw [← Finset.sum_mul, V.sum_one, one_mul]
  rw [hlhs] at htot
  unfold Hnat_zmod at htot ⊢
  linarith

/-- Exact Jensen-gap identity for `Hnat_zmod (conv_dilate U V c) - Hnat_zmod U`. -/
private lemma Hnat_conv_dilate_sub_eq {q : ℕ} [NeZero q] (U V : PMF_ZMod q) (c : ZMod q) :
    Hnat_zmod (conv_dilate U V c) - Hnat_zmod U =
      ∑ y : ZMod q, V.p y *
        ∑ x' : ZMod q, U.p x' * Real.log (U.p x' / (conv_dilate U V c).p (x' + c * y)) := by
  unfold Hnat_zmod
  have h1 : ∑ x : ZMod q, Real.negMulLog ((conv_dilate U V c).p x) =
      ∑ y : ZMod q, V.p y * ∑ x' : ZMod q, -(U.p x' * Real.log ((conv_dilate U V c).p (x' + c * y))) := by
    calc ∑ x : ZMod q, Real.negMulLog ((conv_dilate U V c).p x)
        = ∑ x : ZMod q, -(∑ y : ZMod q, U.p (x - c * y) * V.p y) *
            Real.log ((conv_dilate U V c).p x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [Real.negMulLog, conv_dilate]
      _ = ∑ x : ZMod q, ∑ y : ZMod q,
            -(U.p (x - c * y) * V.p y * Real.log ((conv_dilate U V c).p x)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_neg_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ y : ZMod q, V.p y * ∑ x : ZMod q,
            -(U.p (x - c * y) * Real.log ((conv_dilate U V c).p x)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ y : ZMod q, V.p y * ∑ x' : ZMod q,
            -(U.p x' * Real.log ((conv_dilate U V c).p (x' + c * y))) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          have hbij := Equiv.sum_comp (Equiv.addRight (c * y))
            (fun x => -(U.p (x - c * y) * Real.log ((conv_dilate U V c).p x)))
          simpa only [Equiv.coe_addRight, add_sub_cancel_right] using hbij.symm
  have h2 : ∑ x' : ZMod q, Real.negMulLog (U.p x') =
      ∑ y : ZMod q, V.p y * ∑ x' : ZMod q, -(U.p x' * Real.log (U.p x')) := by
    rw [← Finset.sum_mul, V.sum_one, one_mul]
    refine Finset.sum_congr rfl fun x' _ => by simp [Real.negMulLog]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  by_cases hy : V.p y = 0
  · simp [hy]
  congr 1
  refine Finset.sum_congr rfl fun x' _ => ?_
  by_cases hx' : U.p x' = 0
  · simp [hx']
  have hpos_conv : 0 < (conv_dilate U V c).p (x' + c * y) := by
    have hterm : U.p (x' + c * y - c * y) * V.p y ≤ (conv_dilate U V c).p (x' + c * y) :=
      Finset.single_le_sum (fun z _ => mul_nonneg (U.nonneg _) (V.nonneg _)) (Finset.mem_univ y)
    rw [add_sub_cancel_right] at hterm
    have hx_pos : 0 < U.p x' := lt_of_le_of_ne (U.nonneg x') (Ne.symm hx')
    have hy_pos : 0 < V.p y := lt_of_le_of_ne (V.nonneg y) (Ne.symm hy)
    exact lt_of_lt_of_le (mul_pos hx_pos hy_pos) hterm
  rw [Real.log_div hx' hpos_conv.ne']
  ring

/-- Every nonzero element of `ZMod q` (`q` prime) is a unit. -/
lemma zmod_isUnit_of_ne_zero {q : ℕ} [Fact q.Prime] {d : ZMod q} (hd : d ≠ 0) :
    IsUnit d := by
  have hqp : q.Prime := Fact.out
  have hval_pos : 0 < d.val := by
    by_contra h0
    have hval0 : d.val = 0 := by omega
    apply hd
    rw [← ZMod.natCast_zmod_val d, hval0, Nat.cast_zero]
  have hval_lt : d.val < q := d.val_lt
  have hcop : Nat.Coprime d.val q :=
    (hqp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hval_pos hval_lt)).symm
  rw [← ZMod.natCast_zmod_val d]
  exact (ZMod.isUnit_iff_coprime d.val q).mpr hcop

/-- Orbit average over `(ZMod q)ˣ` (represented as `c ≠ 0` in `ZMod q`, `q` prime):
for any `d ≠ 0`, `∑_{c ≠ 0} U.p (x' + c * d) = 1 - U.p x'`. -/
private lemma sum_nonzero_orbit {q : ℕ} [Fact q.Prime] (U : PMF_ZMod q) (x' d : ZMod q) (hd : d ≠ 0) :
    ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0), U.p (x' + c * d) = 1 - U.p x' := by
  rcases zmod_isUnit_of_ne_zero hd with ⟨u, rfl⟩
  have htot : ∑ c : ZMod q, U.p (x' + c * (u : ZMod q)) = 1 := by
    let e : ZMod q ≃ ZMod q :=
      { toFun := fun c => x' + c * (u : ZMod q)
        invFun := fun z => (z - x') * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
        left_inv := fun c => by simp [mul_assoc]
        right_inv := fun z => by simp [mul_assoc] }
    have hcomp := Equiv.sum_comp e U.p
    simpa [e, U.sum_one] using hcomp
  have h0 : (0 : ZMod q) ∈ (Finset.univ : Finset (ZMod q)) := Finset.mem_univ 0
  have hsplit : ∑ c : ZMod q, U.p (x' + c * (u : ZMod q)) =
      U.p (x' + 0 * (u : ZMod q)) + ∑ c ∈ Finset.univ.erase 0, U.p (x' + c * (u : ZMod q)) :=
    (Finset.add_sum_erase _ _ h0).symm
  have hfilt : Finset.univ.filter (fun c : ZMod q => c ≠ 0) = Finset.univ.erase (0 : ZMod q) := by
    ext c; simp
  rw [hfilt]
  simp only [zero_mul, add_zero] at hsplit
  linarith

/-- Intermediate Jensen bound in Lemma 2:
`E_{c ≠ 0}[Hnat(U + cV) - Hnat(U)] ≥ ∑_{y : 0 < V.p y < 1} V.p y * KL(U || T_{V.p y}(U))`. -/
private lemma fq_dilation_jensen_ge_kl {q : ℕ} [Fact q.Prime] (hq : 3 ≤ q)
    (U V : PMF_ZMod q) (hmax : ∀ y : ZMod q, V.p y < 1) :
    ∑ y : ZMod q, (if V.p y = 0 then 0 else V.p y * klDiv_zmod U.p (Tr_val q U (V.p y))) ≤
      (1 / ((q : ℝ) - 1)) * ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0),
        (Hnat_zmod (conv_dilate U V c) - Hnat_zmod U) := by
  set nz : Finset (ZMod q) := Finset.univ.filter (fun c : ZMod q => c ≠ 0)
  have hnz_card : (nz.card : ℝ) = (q : ℝ) - 1 := by
    have hfilt : nz = Finset.univ.erase (0 : ZMod q) := by ext c; simp [nz]
    rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have h1 : 1 ≤ q := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  simp_rw [Hnat_conv_dilate_sub_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hy : V.p y = 0
  · simp [hy]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hy)]
  have hy_pos : 0 < V.p y := lt_of_le_of_ne (V.nonneg y) (Ne.symm hy)
  have hy_lt1 : V.p y < 1 := hmax y
  have h1y_pos : 0 < 1 - V.p y := by linarith
  have hpull : (1 / ((q : ℝ) - 1)) * ∑ c ∈ nz,
      V.p y * ∑ x' : ZMod q, U.p x' * Real.log (U.p x' / (conv_dilate U V c).p (x' + c * y)) =
      V.p y * ∑ x' : ZMod q, (1 / ((q : ℝ) - 1)) *
        ∑ c ∈ nz, U.p x' * Real.log (U.p x' / (conv_dilate U V c).p (x' + c * y)) := by
    rw [← Finset.mul_sum, Finset.sum_comm, ← Finset.mul_sum]
    ring
  rw [hpull]
  refine mul_le_mul_of_nonneg_left ?_ hy_pos.le
  unfold klDiv_zmod
  refine Finset.sum_le_sum fun x' _ => ?_
  by_cases hx' : U.p x' = 0
  · simp [hx']
  have hx_pos : 0 < U.p x' := lt_of_le_of_ne (U.nonneg x') (Ne.symm hx')
  let t_fn : ZMod q → ℝ := fun c =>
    (1 / (1 - V.p y)) * ∑ z ∈ Finset.univ.erase y, V.p z * U.p (x' + c * (y - z))
  have ht_nonneg : ∀ c ∈ nz, 0 ≤ t_fn c := fun c _ =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => mul_nonneg (V.nonneg z) (U.nonneg _))
  have hconv_eq : ∀ c : ZMod q,
      (conv_dilate U V c).p (x' + c * y) = V.p y * U.p x' + (1 - V.p y) * t_fn c := by
    intro c
    dsimp [conv_dilate, t_fn]
    rw [← mul_assoc, mul_one_div_cancel h1y_pos.ne', one_mul]
    have hsplit := (Finset.add_sum_erase Finset.univ (fun z => U.p (x' + c * y - c * z) * V.p z)
      (Finset.mem_univ y)).symm
    rw [hsplit]
    have h1 : x' + c * y - c * y = x' := add_sub_cancel_right _ _
    rw [h1, mul_comm (U.p x') (V.p y)]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    have : x' + c * y - c * z = x' + c * (y - z) := by ring
    rw [this, mul_comm]
  have ht_avg : ∑ c ∈ nz, (1 / ((q : ℝ) - 1)) * t_fn c = (1 - U.p x') / ((q : ℝ) - 1) := by
    rw [← Finset.mul_sum]
    dsimp [t_fn]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hinner : ∑ z ∈ Finset.univ.erase y, ∑ c ∈ nz, V.p z * U.p (x' + c * (y - z)) =
        (1 - V.p y) * (1 - U.p x') := by
      have h1 : ∀ z ∈ Finset.univ.erase y,
          ∑ c ∈ nz, V.p z * U.p (x' + c * (y - z)) = V.p z * (1 - U.p x') := by
        intro z hz
        rw [← Finset.mul_sum]
        congr 1
        have hne : y - z ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hz).symm
        exact sum_nonzero_orbit U x' (y - z) hne
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
      have hsum_er : ∑ z ∈ Finset.univ.erase y, V.p z = 1 - V.p y := by
        have := Finset.add_sum_erase Finset.univ V.p (Finset.mem_univ y)
        linarith [V.sum_one]
      rw [hsum_er]
    rw [hinner]
    field_simp [h1y_pos.ne', hq1_pos.ne']
  have hconv_on := convexOn_kl_slice hx_pos hy_pos hy_lt1
  have hw_sum : ∑ _c ∈ nz, (1 / ((q : ℝ) - 1)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hnz_card, mul_one_div_cancel hq1_pos.ne']
  have hjensen := hconv_on.map_sum_le (t := nz) (w := fun _ => 1 / ((q : ℝ) - 1)) (p := t_fn)
    (fun _ _ => by positivity) hw_sum ht_nonneg
  simp only [smul_eq_mul] at hjensen
  rw [ht_avg] at hjensen
  have hTr_match : V.p y * U.p x' + (1 - V.p y) * ((1 - U.p x') / ((q : ℝ) - 1)) =
      Tr_val q U (V.p y) x' := by
    unfold Tr_val; ring
  rw [hTr_match] at hjensen
  refine hjensen.trans_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hconv_eq c]

/-- Helper for the `q⁻²`-tail split in Lemma 2:
for `q ≥ 3` and any subset `S ⊆ ZMod q`,
`(1/2) * (∑_{y ∈ S} negMulLog (V.p y) - 2 * log q / q) ≤ ∑_{y ∈ S} V.p y * min (log (1 / V.p y)) (log q)`. -/
private lemma tail_split_min_log {q : ℕ} [NeZero q] (hq : 3 ≤ q) (V : PMF_ZMod q)
    (S : Finset (ZMod q)) :
    (1 / 2 : ℝ) * ((∑ y ∈ S, Real.negMulLog (V.p y)) - 2 * Real.log (q : ℝ) / (q : ℝ)) ≤
      ∑ y ∈ S, (if V.p y = 0 then 0 else V.p y * min (Real.log (1 / V.p y)) (Real.log (q : ℝ))) := by
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hterm : ∀ y ∈ S,
      (1 / 2 : ℝ) * (Real.negMulLog (V.p y) - 2 * Real.log (q : ℝ) / ((q : ℝ) ^ 2)) ≤
        (if V.p y = 0 then 0 else V.p y * min (Real.log (1 / V.p y)) (Real.log (q : ℝ))) := by
    intro y _
    by_cases hy : V.p y = 0
    · simp only [hy, ite_true, Real.negMulLog_zero, zero_sub]
      have : 0 ≤ 2 * Real.log (q : ℝ) / ((q : ℝ) ^ 2) := by positivity
      linarith
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hy)]
      have hy_pos : 0 < V.p y := lt_of_le_of_ne (V.nonneg y) (Ne.symm hy)
      have hneg_eq : Real.negMulLog (V.p y) = V.p y * Real.log (1 / V.p y) := by
        rw [Real.negMulLog, one_div, Real.log_inv]; ring
      rw [hneg_eq]
      by_cases hbig : (1 : ℝ) / ((q : ℝ) ^ 2) ≤ V.p y
      · have hlog_le : Real.log (1 / V.p y) ≤ 2 * Real.log (q : ℝ) := by
          have h1 : 1 / V.p y ≤ (q : ℝ) ^ 2 := by
            rw [div_le_iff₀ hy_pos]
            have := mul_le_mul_of_nonneg_right hbig (sq_nonneg (q : ℝ))
            rw [div_mul_cancel₀ _ (pow_ne_zero 2 hq_pos.ne')] at this
            linarith
          calc Real.log (1 / V.p y) ≤ Real.log ((q : ℝ) ^ 2) := Real.log_le_log (by positivity) h1
            _ = 2 * Real.log (q : ℝ) := by rw [Real.log_pow]; ring
        have hhalf : (1 / 2 : ℝ) * Real.log (1 / V.p y) ≤ min (Real.log (1 / V.p y)) (Real.log (q : ℝ)) := by
          apply le_min
          · have : 0 ≤ Real.log (1 / V.p y) := by
              apply Real.log_nonneg; rw [one_le_div hy_pos]; exact V.le_one y
            linarith
          · linarith
        have hmul := mul_le_mul_of_nonneg_left hhalf hy_pos.le
        have : 0 ≤ 2 * Real.log (q : ℝ) / ((q : ℝ) ^ 2) := by positivity
        linarith
      · push Not at hbig
        have h_inv_e : (1 : ℝ) / ((q : ℝ) ^ 2) ≤ Real.exp (-1) := by
          have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
          have hq2 : (9 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
          rw [Real.exp_neg, ← one_div]
          exact one_div_le_one_div_of_le (Real.exp_pos 1) (by linarith)
        have hmono : Real.negMulLog (V.p y) ≤ Real.negMulLog (1 / (q : ℝ) ^ 2) := by
          have hd : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.exp (-1)),
              HasDerivAt Real.negMulLog (-(Real.log t + 1)) t := fun t ht => by
            have h1 := ((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht.1.ne')).neg
            convert h1 using 1
            · ext s; simp [Real.negMulLog]
            · field_simp [ht.1.ne']
          have hmon : MonotoneOn Real.negMulLog (Set.Icc 0 (Real.exp (-1))) := by
            apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.exp (-1)))
            · exact Real.continuous_negMulLog.continuousOn
            · exact fun t ht => by
                rw [interior_Icc] at ht
                exact (hd t ht).differentiableAt.differentiableWithinAt
            · intro t ht
              rw [interior_Icc] at ht
              rw [(hd t ht).deriv]
              have hlt : Real.log t < -1 := by
                have := Real.log_lt_log ht.1 ht.2
                rwa [Real.log_exp] at this
              linarith
          exact hmon ⟨hy_pos.le, le_trans hbig.le h_inv_e⟩ ⟨by positivity, h_inv_e⟩ hbig.le
        have hval : Real.negMulLog (1 / (q : ℝ) ^ 2) = 2 * Real.log (q : ℝ) / ((q : ℝ) ^ 2) := by
          rw [Real.negMulLog, one_div, Real.log_inv, Real.log_pow]
          ring
        rw [hneg_eq, hval] at hmono
        have hrhs : 0 ≤ V.p y * min (Real.log (1 / V.p y)) (Real.log (q : ℝ)) := by
          refine mul_nonneg hy_pos.le (le_min ?_ hlogq_pos.le)
          apply Real.log_nonneg; rw [one_le_div hy_pos]; exact V.le_one y
        linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard_le : (S.card : ℝ) ≤ (q : ℝ) := by
    have : S.card ≤ q := by
      calc S.card ≤ (Finset.univ : Finset (ZMod q)).card := Finset.card_le_univ S
        _ = q := ZMod.card q
    exact_mod_cast this
  have htail : (S.card : ℝ) * (2 * Real.log (q : ℝ) / (q : ℝ) ^ 2) ≤ 2 * Real.log (q : ℝ) / (q : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hcard_le (by positivity : (0 : ℝ) ≤ 2 * Real.log (q : ℝ) / (q : ℝ) ^ 2)
    refine hmul.trans_eq ?_
    field_simp [hq_pos.ne']
  linarith

/-- **Lemma 2a (Universal Prime-Field Dilation Entropy-Gain Theorem — Uniform Dilator):**
For every prime `q ≥ 3` and independent `U, V` on `ZMod q`,
`(1 / (q - 1)) * ∑_{c ≠ 0} (Hnat(U + cV) - Hnat(U)) ≥ (1 / (2420 * log q)) * (Hnat(V) - 5 * log q / q) * deficit(U)`. -/
theorem fq_uniform_dilation_entropy_gain {q : ℕ} [Fact q.Prime] (hq : 3 ≤ q)
    (U V : PMF_ZMod q) :
    (1 / (2420 * Real.log (q : ℝ))) * (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) * deficit_zmod U ≤
      (1 / ((q : ℝ) - 1)) * ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0),
        (Hnat_zmod (conv_dilate U V c) - Hnat_zmod U) := by
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hdef_nn : 0 ≤ deficit_zmod U := deficit_zmod_nonneg U
  by_cases hpoint : ∃ y0 : ZMod q, V.p y0 = 1
  · rcases hpoint with ⟨y0, hy0⟩
    have hV_zero : ∀ y : ZMod q, y ≠ y0 → V.p y = 0 := by
      intro y hy
      have hsum := Finset.add_sum_erase Finset.univ V.p (Finset.mem_univ y0)
      rw [V.sum_one, hy0] at hsum
      have hrest : ∑ z ∈ Finset.univ.erase y0, V.p z = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => V.nonneg z)).mp hrest y
        (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)
    have hHV : Hnat_zmod V = 0 := by
      unfold Hnat_zmod
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y = y0
      · subst hy; rw [hy0]; simp [Real.negMulLog]
      · rw [hV_zero y hy, Real.negMulLog_zero]
    rw [hHV]
    have hlhs_nonpos : (1 / (2420 * Real.log (q : ℝ))) * (0 - 5 * Real.log (q : ℝ) / (q : ℝ)) *
        deficit_zmod U ≤ 0 := by
      have h1 : (0 : ℝ) - 5 * Real.log (q : ℝ) / (q : ℝ) ≤ 0 := by
        have : 0 ≤ 5 * Real.log (q : ℝ) / (q : ℝ) := by positivity
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) h1) hdef_nn
    have hrhs_nn : 0 ≤ (1 / ((q : ℝ) - 1)) * ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0),
        (Hnat_zmod (conv_dilate U V c) - Hnat_zmod U) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => Hnat_conv_dilate_sub_nonneg U V c)
    exact hlhs_nonpos.trans hrhs_nn
  · push Not at hpoint
    have hmax_lt1 : ∀ y : ZMod q, V.p y < 1 := fun y => lt_of_le_of_ne (V.le_one y) (hpoint y)
    have hjensen := fq_dilation_jensen_ge_kl hq U V hmax_lt1
    by_cases hhalf : ∀ y : ZMod q, V.p y ≤ 1 / 2
    · have hkl_lb : ∀ y : ZMod q,
          (1 / (484 * Real.log (q : ℝ))) * deficit_zmod U *
            (if V.p y = 0 then 0 else V.p y * min (Real.log (1 / V.p y)) (Real.log (q : ℝ))) ≤
          (if V.p y = 0 then 0 else V.p y * klDiv_zmod U.p (Tr_val q U (V.p y))) := by
        intro y
        by_cases hy : V.p y = 0
        · simp [hy]
        rw [ite_eq_right_iff.mpr (fun h => absurd h hy), ite_eq_right_iff.mpr (fun h => absurd h hy)]
        have hy_pos : 0 < V.p y := lt_of_le_of_ne (V.nonneg y) (Ne.symm hy)
        have hL1 := pointwise_kl_contraction_le hq U hy_pos (hhalf y)
        have hmul := mul_le_mul_of_nonneg_left hL1 hy_pos.le
        refine le_trans ?_ hmul
        ring_nf; exact le_rfl
      have hsum_kl := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hkl_lb y
      rw [← Finset.mul_sum] at hsum_kl
      have htail := tail_split_min_log hq V Finset.univ
      change (1 / 2 : ℝ) * (Hnat_zmod V - 2 * Real.log (q : ℝ) / (q : ℝ)) ≤ _ at htail
      have hstep : (1 / (2420 * Real.log (q : ℝ))) * (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) *
          deficit_zmod U ≤
          (1 / (484 * Real.log (q : ℝ))) * deficit_zmod U *
            ((1 / 2 : ℝ) * (Hnat_zmod V - 2 * Real.log (q : ℝ) / (q : ℝ))) := by
        have hdiff : (1 / 5 : ℝ) * (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) ≤
            (1 / 2 : ℝ) * (Hnat_zmod V - 2 * Real.log (q : ℝ) / (q : ℝ)) := by
          have hH0 : 0 ≤ Hnat_zmod V := Hnat_zmod_nonneg V
          have heq1 : (1 / 5 : ℝ) * (5 * Real.log (q : ℝ) / (q : ℝ)) = Real.log (q : ℝ) / (q : ℝ) := by ring
          have heq2 : (1 / 2 : ℝ) * (2 * Real.log (q : ℝ) / (q : ℝ)) = Real.log (q : ℝ) / (q : ℝ) := by ring
          linarith
        have hmul := mul_le_mul_of_nonneg_left hdiff
          (by positivity : (0 : ℝ) ≤ (1 / (484 * Real.log (q : ℝ))) * deficit_zmod U)
        refine le_trans ?_ hmul
        ring_nf; exact le_rfl
      have hmul2 := mul_le_mul_of_nonneg_left htail
        (by positivity : (0 : ℝ) ≤ (1 / (484 * Real.log (q : ℝ))) * deficit_zmod U)
      exact (hstep.trans (hmul2.trans hsum_kl)).trans hjensen
    · push Not at hhalf
      rcases hhalf with ⟨y0, hy0⟩
      set S : Finset (ZMod q) := Finset.univ.erase y0
      have hS_le : ∀ y ∈ S, V.p y ≤ 1 / 2 := by
        intro y hy
        have hne : y ≠ y0 := Finset.ne_of_mem_erase hy
        have hpair : V.p y + V.p y0 ≤ 1 := by
          rw [← V.sum_one]
          have hsub : ({y, y0} : Finset (ZMod q)) ⊆ Finset.univ := Finset.subset_univ _
          have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => V.nonneg z)
          rwa [Finset.sum_pair hne] at hsum_le
        linarith
      have hkl_nonneg_y0 : 0 ≤ (if V.p y0 = 0 then 0 else V.p y0 * klDiv_zmod U.p (Tr_val q U (V.p y0))) := by
        have hy0_pos : 0 < V.p y0 := by linarith
        rw [ite_eq_right_iff.mpr (fun h => absurd h hy0_pos.ne')]
        refine mul_nonneg hy0_pos.le ?_
        have hQ_pos : ∀ x : ZMod q, 0 < Tr_val q U (V.p y0) x := by
          intro x
          unfold Tr_val
          have h1 : 0 < 1 - V.p y0 := by linarith [hmax_lt1 y0]
          rcases eq_or_lt_of_le (U.nonneg x) with hx | hx
          · rw [← hx]; positivity
          · have h2 : 0 ≤ (1 - V.p y0) * (1 - U.p x) / ((q : ℝ) - 1) := by
              have : 0 ≤ 1 - U.p x := by linarith [U.le_one x]
              positivity
            linarith [mul_pos hy0_pos hx]
        have hQ_sum : ∑ x : ZMod q, Tr_val q U (V.p y0) x = 1 := by
          unfold Tr_val
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, U.sum_one, mul_one]
          simp_rw [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one, U.sum_one]
          field_simp [hq1_pos.ne']
          ring
        have hgibbs : ∑ x : ZMod q, (U.p x - Tr_val q U (V.p y0) x) ≤
            klDiv_zmod U.p (Tr_val q U (V.p y0)) := by
          unfold klDiv_zmod
          refine Finset.sum_le_sum fun x _ => ?_
          by_cases hx : U.p x = 0
          · simp [hx]; exact (hQ_pos x).le
          · have hxp : 0 < U.p x := lt_of_le_of_ne (U.nonneg x) (Ne.symm hx)
            have hlog := Real.log_le_sub_one_of_pos (div_pos (hQ_pos x) hxp)
            rw [Real.log_div (hQ_pos x).ne' hxp.ne'] at hlog
            have hmul := mul_le_mul_of_nonneg_left hlog hxp.le
            have hsimp : U.p x * (Tr_val q U (V.p y0) x / U.p x - 1) =
                Tr_val q U (V.p y0) x - U.p x := by field_simp [hx]
            rw [hsimp] at hmul
            rw [Real.log_div hx (hQ_pos x).ne']
            linarith
        rw [Finset.sum_sub_distrib, U.sum_one, hQ_sum, sub_self] at hgibbs
        exact hgibbs
      have hdrop : ∑ y ∈ S, (if V.p y = 0 then 0 else V.p y * klDiv_zmod U.p (Tr_val q U (V.p y))) ≤
          ∑ y : ZMod q, (if V.p y = 0 then 0 else V.p y * klDiv_zmod U.p (Tr_val q U (V.p y))) := by
        have := Finset.add_sum_erase Finset.univ
          (fun y => if V.p y = 0 then 0 else V.p y * klDiv_zmod U.p (Tr_val q U (V.p y)))
          (Finset.mem_univ y0)
        linarith
      have hkl_lb : ∀ y ∈ S,
          (1 / (484 * Real.log (q : ℝ))) * deficit_zmod U *
            (if V.p y = 0 then 0 else V.p y * min (Real.log (1 / V.p y)) (Real.log (q : ℝ))) ≤
          (if V.p y = 0 then 0 else V.p y * klDiv_zmod U.p (Tr_val q U (V.p y))) := by
        intro y hyS
        by_cases hy : V.p y = 0
        · simp [hy]
        rw [ite_eq_right_iff.mpr (fun h => absurd h hy), ite_eq_right_iff.mpr (fun h => absurd h hy)]
        have hy_pos : 0 < V.p y := lt_of_le_of_ne (V.nonneg y) (Ne.symm hy)
        have hL1 := pointwise_kl_contraction_le hq U hy_pos (hS_le y hyS)
        have hmul := mul_le_mul_of_nonneg_left hL1 hy_pos.le
        refine le_trans ?_ hmul
        ring_nf; exact le_rfl
      have hsum_kl := Finset.sum_le_sum hkl_lb
      rw [← Finset.mul_sum] at hsum_kl
      have htail := tail_split_min_log hq V S
      set S_ne : ℝ := ∑ y ∈ S, Real.negMulLog (V.p y)
      set eps : ℝ := 1 - V.p y0
      have heps_pos : 0 < eps := by dsimp [eps]; linarith [hmax_lt1 y0]
      have heps_eq : eps = ∑ y ∈ S, V.p y := by
        have := Finset.add_sum_erase Finset.univ V.p (Finset.mem_univ y0)
        dsimp [eps, S]; linarith [V.sum_one]
      have hy0_ent : Real.negMulLog (V.p y0) ≤ eps := by
        have hlog := Real.log_le_sub_one_of_pos (div_pos one_pos (by linarith : 0 < V.p y0))
        rw [one_div, Real.log_inv] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ V.p y0)
        have hsimp : V.p y0 * ((V.p y0)⁻¹ - 1) = 1 - V.p y0 := by
          field_simp [(by linarith : V.p y0 ≠ 0)]
        rw [hsimp] at hmul
        rw [Real.negMulLog]; dsimp [eps]; linarith
      have heps_le_Sne : Real.log 2 * eps ≤ S_ne := by
        rw [heps_eq, Finset.mul_sum]
        dsimp [S_ne]
        refine Finset.sum_le_sum fun y hyS => ?_
        by_cases hy : V.p y = 0
        · simp [hy, Real.negMulLog_zero]
        · have hyp : 0 < V.p y := lt_of_le_of_ne (V.nonneg y) (Ne.symm hy)
          have hlog : Real.log 2 ≤ Real.log (1 / V.p y) := by
            apply Real.log_le_log (by norm_num)
            rw [le_div_iff₀ hyp]; linarith [hS_le y hyS]
          have hmul := mul_le_mul_of_nonneg_left hlog hyp.le
          rw [one_div, Real.log_inv] at hmul
          rw [Real.negMulLog]
          linarith
      have hH_split : Hnat_zmod V = Real.negMulLog (V.p y0) + S_ne := by
        unfold Hnat_zmod
        exact (Finset.add_sum_erase Finset.univ (fun y => Real.negMulLog (V.p y))
          (Finset.mem_univ y0)).symm
      have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hH_le : Hnat_zmod V ≤ (5 / 2 : ℝ) * S_ne := by
        have hSne_nn : 0 ≤ S_ne := Finset.sum_nonneg fun y _ => Real.negMulLog_nonneg (V.nonneg y) (V.le_one y)
        nlinarith
      have hstep : (1 / (2420 * Real.log (q : ℝ))) * (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) *
          deficit_zmod U ≤
          (1 / (484 * Real.log (q : ℝ))) * deficit_zmod U *
            ((1 / 2 : ℝ) * (S_ne - 2 * Real.log (q : ℝ) / (q : ℝ))) := by
        have hdiff : (1 / 5 : ℝ) * (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) ≤
            (1 / 2 : ℝ) * (S_ne - 2 * Real.log (q : ℝ) / (q : ℝ)) := by
          have heq1 : (1 / 5 : ℝ) * (5 * Real.log (q : ℝ) / (q : ℝ)) = Real.log (q : ℝ) / (q : ℝ) := by ring
          have heq2 : (1 / 2 : ℝ) * (2 * Real.log (q : ℝ) / (q : ℝ)) = Real.log (q : ℝ) / (q : ℝ) := by ring
          linarith
        have hmul := mul_le_mul_of_nonneg_left hdiff
          (by positivity : (0 : ℝ) ≤ (1 / (484 * Real.log (q : ℝ))) * deficit_zmod U)
        refine le_trans ?_ hmul
        ring_nf; exact le_rfl
      have hmul2 := mul_le_mul_of_nonneg_left htail
        (by positivity : (0 : ℝ) ≤ (1 / (484 * Real.log (q : ℝ))) * deficit_zmod U)
      exact (hstep.trans (hmul2.trans (hsum_kl.trans hdrop))).trans hjensen

/-- **Lemma 2b (General Prime-Field Dilation Entropy-Gain Theorem):**
For any prime `q ≥ 3`, independent `U, V` on `ZMod q`, and any dilator weights `W : ZMod q → ℝ`
satisfying `∀ c ≠ 0, c_dil / (q - 1) ≤ W c` (with `0 ≤ c_dil`),
`∑_{c ≠ 0} W c * (Hnat(U + cV) - Hnat(U)) ≥ (c_dil / (2420 * log q)) * (Hnat(V) - 5 * log q / q) * deficit(U)`. -/
theorem fq_general_dilation_entropy_gain {q : ℕ} [Fact q.Prime] (hq : 3 ≤ q)
    (U V : PMF_ZMod q) (W : ZMod q → ℝ) {c_dil : ℝ} (hc_dil : 0 ≤ c_dil)
    (hW : ∀ c : ZMod q, c ≠ 0 → c_dil / ((q : ℝ) - 1) ≤ W c) :
    (c_dil / (2420 * Real.log (q : ℝ))) * (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) *
        deficit_zmod U ≤
      ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0),
        W c * (Hnat_zmod (conv_dilate U V c) - Hnat_zmod U) := by
  have hunif := fq_uniform_dilation_entropy_gain hq U V
  have hmul := mul_le_mul_of_nonneg_left hunif hc_dil
  have hlhs : c_dil * ((1 / (2420 * Real.log (q : ℝ))) *
        (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) * deficit_zmod U) =
      (c_dil / (2420 * Real.log (q : ℝ))) *
        (Hnat_zmod V - 5 * Real.log (q : ℝ) / (q : ℝ)) * deficit_zmod U := by ring
  rw [hlhs] at hmul
  refine hmul.trans ?_
  have hrhs_eq : c_dil * ((1 / ((q : ℝ) - 1)) * ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0),
      (Hnat_zmod (conv_dilate U V c) - Hnat_zmod U)) =
      ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0),
        (c_dil / ((q : ℝ) - 1)) * (Hnat_zmod (conv_dilate U V c) - Hnat_zmod U) := by
    rw [← mul_assoc, mul_one_div, Finset.mul_sum]
  rw [hrhs_eq]
  refine Finset.sum_le_sum fun c hc => ?_
  have hc_ne : c ≠ 0 := (Finset.mem_filter.mp hc).2
  exact mul_le_mul_of_nonneg_right (hW c hc_ne) (Hnat_conv_dilate_sub_nonneg U V c)

end Erdos18
