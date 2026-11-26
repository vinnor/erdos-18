import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.ZMod.Basic
import Erdos18.Chebyshev

/-!
# Erdos18/Entropy.lean (Layer 2 — Lemmas 1, 2, 3)

Formalizes:
- Lemma 1 (`binEntropy_sq_le`, `binEntropy_xor_gain`): elementary binary entropy & XOR bias inequalities.
- Lemma 2 (`Hnat_conv_sub_ge_bitwise`): bitwise chain-rule entropy gain on `Fin (2^k)`.
- Lemma 3 (`mod_two_pow_covering`): parametric mod-`2^k` covering with `O((log k)^4)` strictly distinct divisors.
-/

namespace Erdos18

open Finset Real

/-! ## Lemma 1: Elementary Binary Entropy & XOR Gain (in nats) -/

/-- Helper: `Real.log x ≤ (x - 1) / Real.sqrt x` for all `x ≥ 1`. -/
lemma log_le_sub_one_div_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - 1) / Real.sqrt x := by
  set t : ℝ := Real.sqrt x
  have ht1 : 1 ≤ t := Real.one_le_sqrt.mpr hx
  have ht_pos : 0 < t := by linarith
  have htsq : t ^ 2 = x := Real.sq_sqrt (by linarith)
  let f : ℝ → ℝ := fun u => u - u⁻¹ - 2 * Real.log u
  have hderiv : ∀ u ∈ Set.Ici (1 : ℝ), HasDerivAt f (1 + u⁻¹ ^ 2 - 2 * u⁻¹) u := by
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
    have h1 : HasDerivAt (fun u : ℝ => u) 1 u := hasDerivAt_id u
    have h2 : HasDerivAt (fun u : ℝ => u⁻¹) (-(u ^ 2)⁻¹) u := hasDerivAt_inv hu_pos.ne'
    have h3 : HasDerivAt (fun u : ℝ => 2 * Real.log u) (2 * u⁻¹) u :=
      (Real.hasDerivAt_log hu_pos.ne').const_mul 2
    have h123 : HasDerivAt f (1 - -(u ^ 2)⁻¹ - 2 * u⁻¹) u := (h1.sub h2).sub h3
    convert h123 using 1
    field_simp [hu_pos.ne']; ring
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
    · exact fun u hu => (hderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hderiv u (interior_subset hu)).deriv]
      have : 1 + u⁻¹ ^ 2 - 2 * u⁻¹ = (1 - u⁻¹) ^ 2 := by ring
      rw [this]
      exact sq_nonneg _
  have hf0 : f 1 ≤ f t := hmono (Set.mem_Ici.mpr le_rfl) ht1 ht1
  have hf1 : f 1 = 0 := by simp [f]
  have hlogx : Real.log x = 2 * Real.log t := by
    rw [← htsq, Real.log_pow]; ring
  rw [hf1] at hf0
  dsimp [f] at hf0
  rw [hlogx, ← htsq]
  have : (t ^ 2 - 1) / t = t - t⁻¹ := by field_simp [ht_pos.ne']
  linarith

/-- Lemma 1a: `2 * (binEntropy q)^2 ≤ 4 * q * (1 - q)` for all `q ∈ [0, 1]`. -/
theorem binEntropy_sq_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    2 * (Real.binEntropy q) ^ 2 ≤ 4 * q * (1 - q) := by
  by_cases h0 : q = 0
  · subst h0; simp [Real.binEntropy]
  by_cases h1 : q = 1
  · subst h1; simp [Real.binEntropy]
  have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm h0)
  have h1qp : 0 < 1 - q := by linarith [lt_of_le_of_ne hq1 h1]
  have hinv_q : 1 ≤ q⁻¹ := one_le_inv₀ hqp |>.mpr hq1
  have hinv_1q : 1 ≤ (1 - q)⁻¹ := one_le_inv₀ h1qp |>.mpr (by linarith)
  have hlog_q : Real.log q⁻¹ ≤ (q⁻¹ - 1) / Real.sqrt q⁻¹ := log_le_sub_one_div_sqrt hinv_q
  have hlog_1q : Real.log (1 - q)⁻¹ ≤ ((1 - q)⁻¹ - 1) / Real.sqrt (1 - q)⁻¹ := log_le_sub_one_div_sqrt hinv_1q
  have hterm1 : q * Real.log q⁻¹ ≤ (1 - q) * Real.sqrt q := by
    have hmul := mul_le_mul_of_nonneg_left hlog_q hqp.le
    refine hmul.trans_eq ?_
    rw [Real.sqrt_inv]
    have hsq : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hqp).ne'
    have hsq2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
    field_simp [hqp.ne', hsq]
  have hterm2 : (1 - q) * Real.log (1 - q)⁻¹ ≤ q * Real.sqrt (1 - q) := by
    have hmul := mul_le_mul_of_nonneg_left hlog_1q h1qp.le
    refine hmul.trans_eq ?_
    rw [Real.sqrt_inv]
    have hsq : Real.sqrt (1 - q) ≠ 0 := (Real.sqrt_pos.mpr h1qp).ne'
    have hsq2 : Real.sqrt (1 - q) * Real.sqrt (1 - q) = 1 - q := Real.mul_self_sqrt h1qp.le
    field_simp [h1qp.ne', hsq]; ring
  have hbin_eq : Real.binEntropy q = q * Real.log q⁻¹ + (1 - q) * Real.log (1 - q)⁻¹ := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog,
        Real.log_inv, Real.log_inv]
    ring
  have hbin_le : Real.binEntropy q ≤ Real.sqrt (q * (1 - q)) * (Real.sqrt (1 - q) + Real.sqrt q) := by
    rw [hbin_eq, Real.sqrt_mul hq0]
    have hsq_q : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
    have hsq_1q : Real.sqrt (1 - q) * Real.sqrt (1 - q) = 1 - q := Real.mul_self_sqrt h1qp.le
    have hid : Real.sqrt q * Real.sqrt (1 - q) * (Real.sqrt (1 - q) + Real.sqrt q) =
        (1 - q) * Real.sqrt q + q * Real.sqrt (1 - q) := by
      calc Real.sqrt q * Real.sqrt (1 - q) * (Real.sqrt (1 - q) + Real.sqrt q)
          = Real.sqrt q * (Real.sqrt (1 - q) * Real.sqrt (1 - q)) +
            (Real.sqrt q * Real.sqrt q) * Real.sqrt (1 - q) := by ring
        _ = (1 - q) * Real.sqrt q + q * Real.sqrt (1 - q) := by rw [hsq_1q, hsq_q]; ring
    linarith
  have hsum_sq : (Real.sqrt (1 - q) + Real.sqrt q) ^ 2 ≤ 2 := by
    have h1s : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt h1qp.le
    have h2s : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
    have hdiff : 0 ≤ (Real.sqrt (1 - q) - Real.sqrt q) ^ 2 := sq_nonneg _
    nlinarith
  have hbin_nonneg : 0 ≤ Real.binEntropy q := Real.binEntropy_nonneg hq0 hq1
  have hsq_le : (Real.binEntropy q) ^ 2 ≤ (Real.sqrt (q * (1 - q)) * (Real.sqrt (1 - q) + Real.sqrt q)) ^ 2 :=
    sq_le_sq' (by linarith [show 0 ≤ Real.sqrt (q * (1 - q)) * (Real.sqrt (1 - q) + Real.sqrt q) by positivity]) hbin_le
  have hsq_rhs : (Real.sqrt (q * (1 - q)) * (Real.sqrt (1 - q) + Real.sqrt q)) ^ 2 =
      q * (1 - q) * (Real.sqrt (1 - q) + Real.sqrt q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq_rhs] at hsq_le
  have hq1q : 0 ≤ q * (1 - q) := by positivity
  nlinarith

/-- Helper: `g(u) = log 2 - binEntropy ((1 - u) / 2)` satisfies `g(α * β) ≤ β^2 * g(α)` for `α, β ∈ [0, 1]`. -/
lemma binEntropy_deficit_mul_le {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Real.log 2 - Real.binEntropy ((1 - α * β) / 2) ≤
      β ^ 2 * (Real.log 2 - Real.binEntropy ((1 - α) / 2)) := by
  let g : ℝ → ℝ := fun u => Real.log 2 - Real.binEntropy ((1 - u) / 2)
  change g (α * β) ≤ β ^ 2 * g α
  have hg0 : g 0 = 0 := by
    simp only [g, sub_zero]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
    have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h12, one_div, Real.log_inv]; ring
  by_cases hαz : α = 0
  · subst hαz; simp [hg0]
  by_cases hβz : β = 0
  · subst hβz; simp [hg0]
  have hαp : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hαz)
  have hβp : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβz)
  -- Helper derivatives for 1 + u and 1 - u
  have hd_add1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => 1 + v) 1 u := fun u =>
    (hasDerivAt_id u).const_add 1
  have hd_sub1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => 1 - v) (-1) u := fun u => by
    simpa using (hasDerivAt_id u).const_sub 1
  -- Step 1: ψ(u) = u / (1 - u^2) - (1/2) * (log(1 + u) - log(1 - u)) ≥ 0 on [0, 1)
  let ψ : ℝ → ℝ := fun u => u / (1 - u ^ 2) - (1 / 2) * (Real.log (1 + u) - Real.log (1 - u))
  have hψ_deriv : ∀ u ∈ Set.Ico (0 : ℝ) 1, HasDerivAt ψ (2 * u ^ 2 / (1 - u ^ 2) ^ 2) u := by
    intro u hu
    have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
    have hu2 : 1 + u ≠ 0 := by linarith [hu.1]
    have hu12 : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
    have hden : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-2 * u) u := by
      have h := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)
      convert h using 1; ring
    have hA : HasDerivAt (fun v : ℝ => v / (1 - v ^ 2))
        ((1 * (1 - u ^ 2) - u * (-2 * u)) / (1 - u ^ 2) ^ 2) u :=
      (hasDerivAt_id u).div hden hu12
    have hB : HasDerivAt (fun v : ℝ => Real.log (1 + v)) ((1 + u)⁻¹ * 1) u :=
      (Real.hasDerivAt_log hu2).comp u (hd_add1 u)
    have hC : HasDerivAt (fun v : ℝ => Real.log (1 - v)) ((1 - u)⁻¹ * (-1)) u :=
      (Real.hasDerivAt_log hu1).comp u (hd_sub1 u)
    have hBC : HasDerivAt (fun v : ℝ => (1 / 2) * (Real.log (1 + v) - Real.log (1 - v)))
        ((1 / 2) * ((1 + u)⁻¹ * 1 - (1 - u)⁻¹ * (-1))) u := (hB.sub hC).const_mul (1 / 2 : ℝ)
    convert hA.sub hBC using 1
    field_simp [hu1, hu2, hu12]; ring
  have hψ_nonneg : ∀ u ∈ Set.Ico (0 : ℝ) 1, 0 ≤ ψ u := by
    have hmono : MonotoneOn ψ (Set.Ico 0 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      · exact fun u hu => (hψ_deriv u hu).continuousAt.continuousWithinAt
      · exact fun u hu => (hψ_deriv u (interior_subset hu)).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [(hψ_deriv u (interior_subset hu)).deriv]
        positivity
    intro u hu
    have h0 : ψ 0 = 0 := by simp [ψ]
    rw [← h0]
    exact hmono (by simp) hu hu.1
  -- Step 2: g'(u) = (1/2) * (log(1 + u) - log(1 - u)) on [0, 1)
  have hg_deriv : ∀ u ∈ Set.Ico (0 : ℝ) 1,
      HasDerivAt g ((1 / 2) * (Real.log (1 + u) - Real.log (1 - u))) u := by
    intro u hu
    have h1 : 0 < (1 - u) / 2 := by linarith [hu.2]
    have h2 : 0 < (1 + u) / 2 := by linarith [hu.1]
    have hg_eq : g = fun v => Real.log 2 - (Real.negMulLog ((1 - v) / 2) + Real.negMulLog ((1 + v) / 2)) := by
      ext v
      simp only [g, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      have : 1 - (1 - v) / 2 = (1 + v) / 2 := by ring
      rw [this]
    rw [hg_eq]
    have hlin1 : HasDerivAt (fun v : ℝ => (1 - v) / 2) (-1 / 2) u := by
      simpa using (hd_sub1 u).div_const 2
    have hlin2 : HasDerivAt (fun v : ℝ => (1 + v) / 2) (1 / 2) u := by
      simpa using (hd_add1 u).div_const 2
    have hd1 := (Real.hasDerivAt_negMulLog h1.ne').comp u hlin1
    have hd2 := (Real.hasDerivAt_negMulLog h2.ne').comp u hlin2
    have hsub := (hasDerivAt_const u (Real.log 2)).sub (hd1.add hd2)
    have hsub' : HasDerivAt (fun v : ℝ => Real.log 2 - (Real.negMulLog ((1 - v) / 2) + Real.negMulLog ((1 + v) / 2)))
        (0 - ((-Real.log ((1 - u) / 2) - 1) * (-1 / 2) + (-Real.log ((1 + u) / 2) - 1) * (1 / 2))) u := hsub
    convert hsub' using 1
    rw [Real.log_div (by linarith [hu.2]) (by norm_num), Real.log_div (by linarith [hu.1]) (by norm_num)]
    ring
  -- Step 3: φ(u) = u * (1/2) * (log(1 + u) - log(1 - u)) - 2 * g(u) ≥ 0 on [0, 1)
  let φ : ℝ → ℝ := fun u => u * ((1 / 2) * (Real.log (1 + u) - Real.log (1 - u))) - 2 * g u
  have hφ_deriv : ∀ u ∈ Set.Ico (0 : ℝ) 1, HasDerivAt φ (ψ u) u := by
    intro u hu
    have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
    have hu2 : 1 + u ≠ 0 := by linarith [hu.1]
    have hu12 : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
    have hB : HasDerivAt (fun v : ℝ => Real.log (1 + v)) ((1 + u)⁻¹ * 1) u :=
      (Real.hasDerivAt_log hu2).comp u (hd_add1 u)
    have hC : HasDerivAt (fun v : ℝ => Real.log (1 - v)) ((1 - u)⁻¹ * (-1)) u :=
      (Real.hasDerivAt_log hu1).comp u (hd_sub1 u)
    have h1 : HasDerivAt (fun v : ℝ => v * ((1 / 2) * (Real.log (1 + v) - Real.log (1 - v))))
        (1 * ((1 / 2) * (Real.log (1 + u) - Real.log (1 - u))) +
          u * ((1 / 2) * ((1 + u)⁻¹ * 1 - (1 - u)⁻¹ * (-1)))) u :=
      (hasDerivAt_id u).mul ((hB.sub hC).const_mul (1 / 2 : ℝ))
    have h2 : HasDerivAt (fun v : ℝ => 2 * g v) (2 * ((1 / 2) * (Real.log (1 + u) - Real.log (1 - u)))) u :=
      (hg_deriv u hu).const_mul 2
    have h12 : HasDerivAt φ
        (1 * ((1 / 2) * (Real.log (1 + u) - Real.log (1 - u))) +
          u * ((1 / 2) * ((1 + u)⁻¹ * 1 - (1 - u)⁻¹ * (-1))) -
          2 * ((1 / 2) * (Real.log (1 + u) - Real.log (1 - u)))) u := h1.sub h2
    convert h12 using 1
    dsimp [ψ]
    field_simp [hu1, hu2, hu12]; ring
  have hφ_nonneg : ∀ u ∈ Set.Ico (0 : ℝ) 1, 0 ≤ φ u := by
    have hmono : MonotoneOn φ (Set.Ico 0 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      · exact fun u hu => (hφ_deriv u hu).continuousAt.continuousWithinAt
      · exact fun u hu => (hφ_deriv u (interior_subset hu)).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [(hφ_deriv u (interior_subset hu)).deriv]
        exact hψ_nonneg u (interior_subset hu)
    intro u hu
    have h0 : φ 0 = 0 := by simp [φ, hg0]
    rw [← h0]
    exact hmono (by simp) hu hu.1
  -- Step 4: h(u) = g(u) / u^2 is monotone on (0, 1]
  let h : ℝ → ℝ := fun u => g u / u ^ 2
  have hh_mono : MonotoneOn h (Set.Ioc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · apply ContinuousOn.div
      · have hg_cont : Continuous g := by
          have hg_eq : g = fun v => Real.log 2 - (Real.negMulLog ((1 - v) / 2) + Real.negMulLog ((1 + v) / 2)) := by
            ext v
            simp only [g, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
            have : 1 - (1 - v) / 2 = (1 + v) / 2 := by ring
            rw [this]
          rw [hg_eq]
          fun_prop
        exact hg_cont.continuousOn
      · exact (continuous_pow 2).continuousOn
      · intro u hu; exact pow_ne_zero 2 hu.1.ne'
    · intro u hu
      rw [interior_Ioc] at hu
      have hd : HasDerivAt h
          (((1 / 2) * (Real.log (1 + u) - Real.log (1 - u)) * u ^ 2 - g u * (2 * u ^ (2 - 1))) / (u ^ 2) ^ 2) u :=
        (hg_deriv u ⟨hu.1.le, hu.2⟩).div (hasDerivAt_pow 2 u) (pow_ne_zero 2 hu.1.ne')
      exact hd.differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ioc] at hu
      have hd : HasDerivAt h
          (((1 / 2) * (Real.log (1 + u) - Real.log (1 - u)) * u ^ 2 - g u * (2 * u ^ (2 - 1))) / (u ^ 2) ^ 2) u :=
        (hg_deriv u ⟨hu.1.le, hu.2⟩).div (hasDerivAt_pow 2 u) (pow_ne_zero 2 hu.1.ne')
      rw [hd.deriv]
      have hnum : (1 / 2) * (Real.log (1 + u) - Real.log (1 - u)) * u ^ 2 - g u * (2 * u ^ (2 - 1)) = u * φ u := by
        dsimp [φ]; ring
      rw [hnum]
      exact div_nonneg (mul_nonneg hu.1.le (hφ_nonneg u ⟨hu.1.le, hu.2⟩)) (sq_nonneg _)
  have hle : h (α * β) ≤ h α := hh_mono ⟨mul_pos hαp hβp, by nlinarith⟩ ⟨hαp, hα1⟩ (by nlinarith)
  dsimp [h] at hle
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hle
  have hα2 : 0 < α ^ 2 := by positivity
  nlinarith

/-- Lemma 1b: XOR entropy gain inequality for independent biased bits. -/
theorem binEntropy_xor_gain {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    let α := |1 - 2 * p|
    let β := |1 - 2 * q|
    Real.binEntropy ((1 - α * β) / 2) - Real.binEntropy p ≥
      2 * (Real.binEntropy q) ^ 2 * (Real.log 2 - Real.binEntropy p) := by
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
  have hq_sq := binEntropy_sq_le hq0 hq1
  have hdef_nonneg : 0 ≤ Real.log 2 - Real.binEntropy p := by
    have := Real.binEntropy_le_log_two (p := p)
    linarith
  nlinarith

end Erdos18

#print axioms Erdos18.binEntropy_sq_le
#print axioms Erdos18.binEntropy_xor_gain

/-! ## Lemma 2: Finite Shannon Entropy & Bitwise Chain-Rule Gain on `Fin (2^k)` -/

namespace Erdos18

open Finset Real

/-- A probability mass function on `Fin N`. -/
@[ext]
structure PMF_Fin (N : ℕ) where
  p : Fin N → ℝ
  nonneg : ∀ x, 0 ≤ p x
  sum_one : ∑ x : Fin N, p x = 1

lemma PMF_Fin.le_one {N : ℕ} (μ : PMF_Fin N) (x : Fin N) : μ.p x ≤ 1 := by
  rw [← μ.sum_one]
  exact Finset.single_le_sum (fun y _ => μ.nonneg y) (Finset.mem_univ x)

/-- Shannon entropy in nats: `Hnat μ = ∑ x, -μ(x) * log(μ(x))`. -/
noncomputable def Hnat {N : ℕ} (μ : PMF_Fin N) : ℝ :=
  ∑ x : Fin N, Real.negMulLog (μ.p x)

/-- Support of a `PMF_Fin N`. -/
noncomputable def suppFin {N : ℕ} (μ : PMF_Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun x => 0 < μ.p x)

/-- `Hnat μ ≤ log |supp μ|` (4-line elementary proof via `log t ≤ t - 1`). -/
theorem Hnat_le_log_supp {N : ℕ} (μ : PMF_Fin N) :
    Hnat μ ≤ Real.log ((suppFin μ).card : ℝ) := by
  have hne : (suppFin μ).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hzero : ∀ x : Fin N, μ.p x = 0 := by
      intro x
      have hx : x ∉ suppFin μ := by rw [h]; simp
      simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
      exact le_antisymm hx (μ.nonneg x)
    have : ∑ x : Fin N, μ.p x = 0 := Finset.sum_eq_zero fun x _ => hzero x
    linarith [μ.sum_one]
  have hcard_pos : (0 : ℝ) < ((suppFin μ).card : ℝ) := Nat.cast_pos.mpr hne.card_pos
  have hsum_supp : ∑ x ∈ suppFin μ, μ.p x = 1 := by
    rw [← μ.sum_one]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
    exact le_antisymm hx (μ.nonneg x)
  have hH_supp : Hnat μ = ∑ x ∈ suppFin μ, Real.negMulLog (μ.p x) := by
    unfold Hnat
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
    rw [le_antisymm hx (μ.nonneg x), Real.negMulLog_zero]
  rw [hH_supp]
  have hdiff : ∑ x ∈ suppFin μ, (Real.negMulLog (μ.p x) - μ.p x * Real.log ((suppFin μ).card : ℝ)) ≤ 0 := by
    calc ∑ x ∈ suppFin μ, (Real.negMulLog (μ.p x) - μ.p x * Real.log ((suppFin μ).card : ℝ))
        = ∑ x ∈ suppFin μ, μ.p x * Real.log (1 / (μ.p x * ((suppFin μ).card : ℝ))) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hpx : 0 < μ.p x := (Finset.mem_filter.mp hx).2
          rw [Real.negMulLog, one_div, Real.log_inv, Real.log_mul hpx.ne' hcard_pos.ne']
          ring
      _ ≤ ∑ x ∈ suppFin μ, μ.p x * (1 / (μ.p x * ((suppFin μ).card : ℝ)) - 1) := by
          apply Finset.sum_le_sum
          intro x hx
          have hpx : 0 < μ.p x := (Finset.mem_filter.mp hx).2
          exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity)) hpx.le
      _ = ∑ x ∈ suppFin μ, (1 / ((suppFin μ).card : ℝ) - μ.p x) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hpx : 0 < μ.p x := (Finset.mem_filter.mp hx).2
          field_simp [hpx.ne', hcard_pos.ne']
      _ = 1 - 1 := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsum_supp]
          field_simp [hcard_pos.ne']
      _ = 0 := sub_self 1
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_supp, one_mul] at hdiff
  linarith

/-- Pushforward of a `PMF_Fin N` along a bijection `e : Fin N ≃ Fin N`. -/
noncomputable def pushforwardEquiv {N : ℕ} (e : Fin N ≃ Fin N) (μ : PMF_Fin N) : PMF_Fin N where
  p x := μ.p (e.symm x)
  nonneg x := μ.nonneg (e.symm x)
  sum_one := by
    rw [Equiv.sum_comp e.symm μ.p]
    exact μ.sum_one

theorem Hnat_pushforwardEquiv {N : ℕ} (e : Fin N ≃ Fin N) (μ : PMF_Fin N) :
    Hnat (pushforwardEquiv e μ) = Hnat μ := by
  unfold Hnat pushforwardEquiv
  exact Equiv.sum_comp e.symm (fun x => Real.negMulLog (μ.p x))

/-- Finite convex mixture of `PMF_Fin N` distributions. -/
noncomputable def mixPMF {N : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : ι, w i = 1)
    (μ : ι → PMF_Fin N) : PMF_Fin N where
  p x := ∑ i : ι, w i * (μ i).p x
  nonneg x := Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) ((μ i).nonneg x)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (μ _).sum_one, mul_one]
    exact hw1

/-- Concavity of Shannon entropy under convex mixtures. -/
theorem Hnat_mixPMF_ge {N : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : ι, w i = 1)
    (μ : ι → PMF_Fin N) :
    ∑ i : ι, w i * Hnat (μ i) ≤ Hnat (mixPMF w hw0 hw1 μ) := by
  unfold Hnat mixPMF
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hconc := Real.strictConcaveOn_negMulLog.concaveOn.le_map_sum
    (t := Finset.univ) (w := w) (p := fun i => (μ i).p x)
    (fun i _ => hw0 i) hw1 (fun i _ => Set.mem_Ici.mpr ((μ i).nonneg x))
  simpa [smul_eq_mul] using hconc

/-- Subtraction modulo `N` on `Fin N` (for `N > 0`). -/
def subModFin {N : ℕ} (hN : 0 < N) (u a : Fin N) : Fin N :=
  ⟨(u.val + (N - a.val)) % N, Nat.mod_lt _ hN⟩

lemma subModFin_involutive {N : ℕ} (hN : 0 < N) (u a : Fin N) :
    subModFin hN u (subModFin hN u a) = a := by
  apply Fin.ext
  dsimp [subModFin]
  have hu := u.isLt; have ha := a.isLt
  by_cases h : a.val ≤ u.val
  · have h1 : (u.val + (N - a.val)) % N = u.val - a.val := by
      have : u.val + (N - a.val) = (u.val - a.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : u.val + (N - (u.val - a.val)) = a.val + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · have h1 : (u.val + (N - a.val)) % N = u.val + N - a.val := by
      have : u.val + (N - a.val) = u.val + N - a.val := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : u.val + (N - (u.val + N - a.val)) = a.val := by omega
    rw [this, Nat.mod_eq_of_lt ha]

lemma add_subModFin_mod {N : ℕ} (hN : 0 < N) (u a : Fin N) :
    (a.val + (subModFin hN u a).val) % N = u.val := by
  dsimp [subModFin]
  have hu := u.isLt; have ha := a.isLt
  by_cases h : a.val ≤ u.val
  · have h1 : (u.val + (N - a.val)) % N = u.val - a.val := by
      have : u.val + (N - a.val) = (u.val - a.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : a.val + (u.val - a.val) = u.val := by omega
    rw [this, Nat.mod_eq_of_lt hu]
  · have h1 : (u.val + (N - a.val)) % N = u.val + N - a.val := by
      have : u.val + (N - a.val) = u.val + N - a.val := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : a.val + (u.val + N - a.val) = u.val + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hu]

/-- Convolution of two `PMF_Fin N` distributions modulo `N`. -/
noncomputable def convPMF {N : ℕ} (hN : 0 < N) (μ ν : PMF_Fin N) : PMF_Fin N where
  p u := ∑ a : Fin N, μ.p a * ν.p (subModFin hN u a)
  nonneg u := Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonneg a) (ν.nonneg _)
  sum_one := by
    rw [Finset.sum_comm]
    have hinner : ∀ a : Fin N, ∑ u : Fin N, μ.p a * ν.p (subModFin hN u a) = μ.p a := by
      intro a
      rw [← Finset.mul_sum]
      -- u ↦ subModFin hN u a is a bijection on Fin N with inverse b ↦ (a + b) % N
      let e : Fin N ≃ Fin N :=
        { toFun := fun u => subModFin hN u a
          invFun := fun b => ⟨(a.val + b.val) % N, Nat.mod_lt _ hN⟩
          left_inv := fun u => by
            apply Fin.ext; exact add_subModFin_mod hN u a
          right_inv := fun b => by
            apply Fin.ext
            dsimp [subModFin]
            have ha := a.isLt; have hb := b.isLt
            by_cases h : a.val + b.val < N
            · rw [Nat.mod_eq_of_lt h]
              have : a.val + b.val + (N - a.val) = b.val + N := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
            · have : (a.val + b.val) % N = a.val + b.val - N := by
                calc (a.val + b.val) % N = ((a.val + b.val - N) + N) % N := by congr 1; omega
                  _ = (a.val + b.val - N) % N := Nat.add_mod_right _ N
                  _ = a.val + b.val - N := Nat.mod_eq_of_lt (by omega)
              rw [this]
              have : a.val + b.val - N + (N - a.val) = b.val := by omega
              rw [this, Nat.mod_eq_of_lt hb] }
      change μ.p a * ∑ u : Fin N, ν.p (e u) = μ.p a
      rw [Equiv.sum_comp e ν.p, ν.sum_one, mul_one]
    simp_rw [hinner]
    exact μ.sum_one

lemma convPMF_mixPMF_right {N : ℕ} (hN : 0 < N) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : ι, w i = 1)
    (X : PMF_Fin N) (Y : ι → PMF_Fin N) :
    convPMF hN X (mixPMF w hw0 hw1 Y) = mixPMF w hw0 hw1 (fun i => convPMF hN X (Y i)) := by
  cases X
  ext u
  dsimp [convPMF, mixPMF]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Prefix projection `Fin (2^k) → Fin (2^j)` (bottom `j` bits). -/
def prefMod (k j : ℕ) (x : Fin (2 ^ k)) : Fin (2 ^ j) :=
  ⟨x.val % 2 ^ j, Nat.mod_lt _ (Nat.two_pow_pos j)⟩

/-- Bit `j` of `x : Fin (2^k)`. -/
def bitAt (k j : ℕ) (x : Fin (2 ^ k)) : Bool :=
  decide ((x.val / 2 ^ j) % 2 = 1)

/-- Marginal probability of prefix `a : Fin (2^j)`. -/
noncomputable def W_pref {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) (a : Fin (2 ^ j)) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a), μ.p x

/-- Joint probability of prefix `a : Fin (2^j)` and bit `j` equal to `1`. -/
noncomputable def W_bit1 {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) (a : Fin (2 ^ j)) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = true), μ.p x

/-- Conditional probability `P(bit j = 1 | pref j = a)`. -/
noncomputable def q_bit {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) (a : Fin (2 ^ j)) : ℝ :=
  if W_pref μ j a = 0 then 0 else W_bit1 μ j a / W_pref μ j a

/-- Conditional entropy of bit `j` given the bottom `j` bits (in nats). -/
noncomputable def condBitEnt {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) : ℝ :=
  ∑ a : Fin (2 ^ j), W_pref μ j a * Real.binEntropy (q_bit μ j a)

lemma W_pref_nonneg {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) (a : Fin (2 ^ j)) :
    0 ≤ W_pref μ j a :=
  Finset.sum_nonneg fun x _ => μ.nonneg x

lemma W_pref_sum_one {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) :
    ∑ a : Fin (2 ^ j), W_pref μ j a = 1 := by
  unfold W_pref
  rw [Finset.sum_fiberwise_of_maps_to (g := prefMod k j) (fun _ _ => Finset.mem_univ _)]
  exact μ.sum_one

lemma W_bit1_le_W_pref {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) (a : Fin (2 ^ j)) :
    W_bit1 μ j a ≤ W_pref μ j a := by
  unfold W_bit1 W_pref
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  · intro x _ _; exact μ.nonneg x

lemma q_bit_bounds {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) (a : Fin (2 ^ j)) :
    0 ≤ q_bit μ j a ∧ q_bit μ j a ≤ 1 := by
  unfold q_bit
  split_ifs with h
  · exact ⟨le_rfl, zero_le_one⟩
  · have hpos : 0 < W_pref μ j a := lt_of_le_of_ne (W_pref_nonneg μ j a) (Ne.symm h)
    have h0 : 0 ≤ W_bit1 μ j a := Finset.sum_nonneg fun x _ => μ.nonneg x
    exact ⟨div_nonneg h0 hpos.le, (div_le_one hpos).mpr (W_bit1_le_W_pref μ j a)⟩

/-- Marginal distribution on the bottom `j` bits (`Fin (2^j)`). -/
noncomputable def projPMF {k : ℕ} (μ : PMF_Fin (2 ^ k)) (j : ℕ) : PMF_Fin (2 ^ j) where
  p := W_pref μ j
  nonneg := W_pref_nonneg μ j
  sum_one := W_pref_sum_one μ j

/-- One-step chain rule: `Hnat μ = Hnat (projPMF μ k) + condBitEnt μ k` for `μ : PMF_Fin (2^(k+1))`. -/
lemma Hnat_succ_eq_proj_add_condBitEnt {k : ℕ} (μ : PMF_Fin (2 ^ (k + 1))) :
    Hnat μ = Hnat (projPMF μ k) + condBitEnt μ k := by
  unfold Hnat projPMF condBitEnt
  rw [← Finset.sum_add_distrib]
  -- Partition Fin (2^(k+1)) by prefMod (k+1) k x : Fin (2^k)
  rw [← Finset.sum_fiberwise_of_maps_to (g := prefMod (k + 1) k) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro a _
  -- Fiber over a consists of exactly two elements: x0 = ⟨a.val, ...⟩ and x1 = ⟨a.val + 2^k, ...⟩
  have ha := a.isLt
  have h2k : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
  let x0 : Fin (2 ^ (k + 1)) := ⟨a.val, by omega⟩
  let x1 : Fin (2 ^ (k + 1)) := ⟨a.val + 2 ^ k, by omega⟩
  have hxne : x0 ≠ x1 := by
    intro h; have := congrArg Fin.val h; dsimp [x0, x1] at this; have := Nat.two_pow_pos k; omega
  have hfib : Finset.univ.filter (fun x : Fin (2 ^ (k + 1)) => prefMod (k + 1) k x = a) = {x0, x1} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
               Fin.ext_iff, prefMod, x0, x1]
    constructor
    · intro hmod
      have hx := x.isLt
      by_cases hlt : x.val < 2 ^ k
      · left; rw [Nat.mod_eq_of_lt hlt] at hmod; exact hmod
      · right
        have hsub : x.val % 2 ^ k = x.val - 2 ^ k := by
          calc x.val % 2 ^ k = ((x.val - 2 ^ k) + 2 ^ k) % 2 ^ k := by congr 1; omega
            _ = (x.val - 2 ^ k) % 2 ^ k := Nat.add_mod_right _ _
            _ = x.val - 2 ^ k := Nat.mod_eq_of_lt (by omega)
        omega
    · rintro (h | h)
      · rw [h, Nat.mod_eq_of_lt ha]
      · rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  have hfib1 : Finset.univ.filter (fun x : Fin (2 ^ (k + 1)) => prefMod (k + 1) k x = a ∧ bitAt (k + 1) k x = true) = {x1} := by
    ext x
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hpref, hbit⟩
      have hxmem : x ∈ ({x0, x1} : Finset (Fin (2 ^ (k + 1)))) := by
        rw [← hfib, Finset.mem_filter]; exact ⟨Finset.mem_univ x, hpref⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
      rcases hxmem with rfl | rfl
      · exfalso
        have hdiv : x0.val / 2 ^ k = 0 := Nat.div_eq_of_lt ha
        simp [bitAt, hdiv] at hbit
      · rfl
    · rintro rfl
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · apply Fin.ext; dsimp [prefMod, x1]; rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
      · dsimp [bitAt, x1]
        have hdiv : (a.val + 2 ^ k) / 2 ^ k = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos k), Nat.div_eq_of_lt ha]
        simp [hdiv]
  have hW : W_pref μ k a = μ.p x0 + μ.p x1 := by
    unfold W_pref; rw [hfib, Finset.sum_pair hxne]
  have hW1 : W_bit1 μ k a = μ.p x1 := by
    unfold W_bit1; rw [hfib1, Finset.sum_singleton]
  rw [hfib, Finset.sum_pair hxne]
  by_cases hW0 : W_pref μ k a = 0
  · have hp0 : μ.p x0 = 0 := by linarith [μ.nonneg x0, μ.nonneg x1]
    have hp1 : μ.p x1 = 0 := by linarith [μ.nonneg x0, μ.nonneg x1]
    simp [hW0, hp0, hp1]
  · have hq : q_bit μ k a = μ.p x1 / W_pref μ k a := by simp [q_bit, hW0, hW1]
    have h1q : 1 - q_bit μ k a = μ.p x0 / W_pref μ k a := by
      rw [hq]; field_simp [hW0]; linarith
    have hx1_eq : μ.p x1 = W_pref μ k a * q_bit μ k a := by rw [hq]; field_simp [hW0]
    have hx0_eq : μ.p x0 = W_pref μ k a * (1 - q_bit μ k a) := by rw [h1q]; field_simp [hW0]
    rw [hx0_eq, hx1_eq, Real.negMulLog_mul, Real.negMulLog_mul,
        Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    ring

/-- Compatibility of `condBitEnt` under prefix projection for `j < m ≤ k`. -/
lemma condBitEnt_projPMF {k m j : ℕ} (hjm : j < m) (hmk : m ≤ k) (μ : PMF_Fin (2 ^ k)) :
    condBitEnt (projPMF μ m) j = condBitEnt μ j := by
  have hW : ∀ a : Fin (2 ^ j), W_pref (projPMF μ m) j a = W_pref μ j a := by
    intro a
    unfold W_pref projPMF
    dsimp only
    simp_rw [W_pref]
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, prefMod]
      constructor
      · rintro ⟨b, hb, hxb⟩
        rw [← hb, ← hxb]
        have hdvd : 2 ^ j ∣ 2 ^ m := Nat.pow_dvd_pow 2 hjm.le
        exact (Nat.mod_mod_of_dvd x.val hdvd).symm
      · intro hx
        refine ⟨prefMod k m x, ?_, rfl⟩
        dsimp [prefMod]
        have hdvd : 2 ^ j ∣ 2 ^ m := Nat.pow_dvd_pow 2 hjm.le
        rw [Nat.mod_mod_of_dvd x.val hdvd, hx]
    · intro b1 _ b2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter] at hx1 hx2
      exact hne (hx1.2.symm.trans hx2.2)
  have hW1 : ∀ a : Fin (2 ^ j), W_bit1 (projPMF μ m) j a = W_bit1 μ j a := by
    intro a
    unfold W_bit1 projPMF
    dsimp only
    simp_rw [W_pref]
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, prefMod, bitAt]
      have hdvd_j : 2 ^ j ∣ 2 ^ m := Nat.pow_dvd_pow 2 hjm.le
      have hdvd_j1 : 2 ^ (j + 1) ∣ 2 ^ m := Nat.pow_dvd_pow 2 hjm
      have hbit_mod : (x.val % 2 ^ m / 2 ^ j) % 2 = (x.val / 2 ^ j) % 2 := by
        have h1 : x.val % 2 ^ m % 2 ^ (j + 1) = x.val % 2 ^ (j + 1) :=
          Nat.mod_mod_of_dvd x.val hdvd_j1
        have h2 : ∀ z : ℕ, (z / 2 ^ j) % 2 = (z % 2 ^ (j + 1)) / 2 ^ j := by
          intro z
          rw [pow_succ, Nat.mod_mul_right_div_self]
        rw [h2, h2, h1]
      constructor
      · rintro ⟨b, ⟨hb1, hb2⟩, hxb⟩
        refine ⟨?_, ?_⟩
        · rw [← hb1, ← hxb, Nat.mod_mod_of_dvd x.val hdvd_j]
        · rw [← hxb] at hb2; simpa [hbit_mod] using hb2
      · rintro ⟨hx1, hx2⟩
        refine ⟨prefMod k m x, ⟨?_, ?_⟩, rfl⟩
        · dsimp [prefMod]; rw [Nat.mod_mod_of_dvd x.val hdvd_j, hx1]
        · dsimp [prefMod]; simpa [hbit_mod] using hx2
    · intro b1 _ b2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter] at hx1 hx2
      exact hne (hx1.2.symm.trans hx2.2)
  unfold condBitEnt q_bit
  apply Finset.sum_congr rfl
  intro a _
  rw [hW a, hW1 a]

/-- Full bitwise chain rule on `Fin (2^k)`: `Hnat μ = ∑ j : Fin k, condBitEnt μ j`. -/
theorem Hnat_eq_sum_condBitEnt {k : ℕ} (μ : PMF_Fin (2 ^ k)) :
    Hnat μ = ∑ j : Fin k, condBitEnt μ j.val := by
  induction k with
  | zero =>
    unfold Hnat
    have hsum : ∑ x : Fin (2 ^ 0), Real.negMulLog (μ.p x) = Real.negMulLog (μ.p ⟨0, by omega⟩) := by
      rw [Fintype.sum_eq_single ⟨0, by omega⟩]
      intro x hx; exfalso; apply hx; apply Fin.ext; omega
    have h0 : μ.p ⟨0, by omega⟩ = 1 := by
      have hs := μ.sum_one
      rw [Fintype.sum_eq_single ⟨0, by omega⟩] at hs
      · exact hs
      · intro x hx; exfalso; apply hx; apply Fin.ext; omega
    rw [hsum, h0, Real.negMulLog_one, Fin.sum_univ_zero]
  | succ k ih =>
    rw [Hnat_succ_eq_proj_add_condBitEnt, ih (projPMF μ k), Fin.sum_univ_castSucc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact condBitEnt_projPMF j.isLt (Nat.le_succ k) μ

end Erdos18

namespace Erdos18

open Finset Real

/-- Carry bit from adding two `j`-bit prefixes `a, b : Fin (2^j)`. -/
def carryBit (j : ℕ) (a b : Fin (2 ^ j)) : Bool :=
  decide (2 ^ j ≤ a.val + b.val)

/-- Probability that `x ⊕ z ⊕ c = 1` for independent Bernoulli(`p`), Bernoulli(`q`). -/
def xorProb (p q : ℝ) (c : Bool) : ℝ :=
  if c then p * q + (1 - p) * (1 - q) else p * (1 - q) + (1 - p) * q

lemma xorProb_bounds {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Bool) :
    0 ≤ xorProb p q c ∧ xorProb p q c ≤ 1 := by
  unfold xorProb
  cases c <;> simp <;> constructor <;> nlinarith

lemma binEntropy_xorProb_eq {p q : ℝ} (c : Bool) :
    Real.binEntropy (xorProb p q c) = Real.binEntropy ((1 - |1 - 2 * p| * |1 - 2 * q|) / 2) := by
  have hsymm : ∀ r : ℝ, Real.binEntropy (1 - r) = Real.binEntropy r := fun r => by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
        Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp [sub_sub_cancel, add_comm]
  have h1 : xorProb p q false = (1 - (1 - 2 * p) * (1 - 2 * q)) / 2 := by
    simp [xorProb]; ring
  have h2 : xorProb p q true = 1 - xorProb p q false := by
    simp [xorProb]; ring
  have hfalse : Real.binEntropy (xorProb p q false) = Real.binEntropy ((1 - |1 - 2 * p| * |1 - 2 * q|) / 2) := by
    rw [h1]
    rcases le_or_gt 0 ((1 - 2 * p) * (1 - 2 * q)) with hpos | hneg
    · rw [← abs_mul, abs_of_nonneg hpos]
    · rw [← abs_mul, abs_of_neg hneg]
      have : (1 - -((1 - 2 * p) * (1 - 2 * q))) / 2 = 1 - (1 - (1 - 2 * p) * (1 - 2 * q)) / 2 := by ring
      rw [this, hsymm]
  cases c
  · exact hfalse
  · rw [h2, hsymm, hfalse]

/-- Helper: bit `j` of `(x + y) % 2^k` (for `j < k`) is determined by `bitAt k j x`, `bitAt k j y`, and `carryBit j (prefMod k j x) (prefMod k j y)`. -/
lemma bitAt_add_mod {k j : ℕ} (hj : j < k) (x y : Fin (2 ^ k)) :
    let u : Fin (2 ^ k) := ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
    bitAt k j u = xor (xor (bitAt k j x) (bitAt k j y)) (carryBit j (prefMod k j x) (prefMod k j y)) := by
  intro u
  have hdvd : 2 ^ (j + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 hj
  have h2j_pos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hmod : u.val % 2 ^ (j + 1) = (x.val + y.val) % 2 ^ (j + 1) :=
    Nat.mod_mod_of_dvd (x.val + y.val) hdvd
  have hdiv_mod : ∀ z : ℕ, (z / 2 ^ j) % 2 = (z % 2 ^ (j + 1)) / 2 ^ j := fun z => by
    rw [pow_succ, Nat.mod_mul_right_div_self]
  have hu_bit : (u.val / 2 ^ j) % 2 = ((x.val + y.val) / 2 ^ j) % 2 := by
    rw [hdiv_mod u.val, hmod, ← hdiv_mod]
  -- Write x = qx * 2^j + rx, y = qy * 2^j + ry
  have hxy_div : (x.val + y.val) / 2 ^ j = x.val / 2 ^ j + y.val / 2 ^ j + (x.val % 2 ^ j + y.val % 2 ^ j) / 2 ^ j := by
    have hx := (Nat.div_add_mod x.val (2 ^ j)).symm
    have hy := (Nat.div_add_mod y.val (2 ^ j)).symm
    calc (x.val + y.val) / 2 ^ j
        = (2 ^ j * (x.val / 2 ^ j + y.val / 2 ^ j) + (x.val % 2 ^ j + y.val % 2 ^ j)) / 2 ^ j := by
          congr 1; linarith
      _ = (x.val / 2 ^ j + y.val / 2 ^ j) + (x.val % 2 ^ j + y.val % 2 ^ j) / 2 ^ j :=
          Nat.mul_add_div h2j_pos _ _
  have hcarry : (x.val % 2 ^ j + y.val % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ x.val % 2 ^ j + y.val % 2 ^ j then 1 else 0 := by
    have hrx : x.val % 2 ^ j < 2 ^ j := Nat.mod_lt _ h2j_pos
    have hry : y.val % 2 ^ j < 2 ^ j := Nat.mod_lt _ h2j_pos
    split_ifs with h
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · exact Nat.div_eq_of_lt (by omega)
  simp only [bitAt, carryBit, prefMod, hu_bit, hxy_div, hcarry]
  split_ifs with hc
  · rcases Nat.mod_two_eq_zero_or_one (x.val / 2 ^ j) with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (y.val / 2 ^ j) with hy | hy <;>
    simp [hc, hx, hy, Nat.add_mod]
  · rcases Nat.mod_two_eq_zero_or_one (x.val / 2 ^ j) with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (y.val / 2 ^ j) with hy | hy <;>
    simp [hc, hx, hy, Nat.add_mod]

/-- Helper: prefix projection of `(x + y) % 2^k` (for `j ≤ k`) equals `(pref x + pref y) % 2^j`. -/
lemma prefMod_add_mod {k j : ℕ} (hj : j ≤ k) (x y : Fin (2 ^ k)) :
    let u : Fin (2 ^ k) := ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
    prefMod k j u = ⟨((prefMod k j x).val + (prefMod k j y).val) % 2 ^ j, Nat.mod_lt _ (Nat.two_pow_pos j)⟩ := by
  intro u
  apply Fin.ext
  dsimp [prefMod, u]
  have hdvd : 2 ^ j ∣ 2 ^ k := Nat.pow_dvd_pow 2 hj
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod]

/-- Convolution formula for `W_pref` and `W_bit1` on `Fin (2^k)` for `j < k`. -/
lemma W_pref_conv_eq {k j : ℕ} (hj : j ≤ k) (X Z : PMF_Fin (2 ^ k)) (u : Fin (2 ^ j)) :
    W_pref (convPMF (Nat.two_pow_pos k) X Z) j u =
      ∑ a : Fin (2 ^ j), W_pref X j a * W_pref Z j (subModFin (Nat.two_pow_pos j) u a) := by
  let hN := Nat.two_pow_pos k
  let hNj := Nat.two_pow_pos j
  -- Rewrite LHS as double sum over (x, y) : Fin (2^k) × Fin (2^k) with prefMod (x + y) = u
  have hlhs : W_pref (convPMF hN X Z) j u =
      ∑ x : Fin (2 ^ k), ∑ y : Fin (2 ^ k),
        if prefMod k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ = u then X.p x * Z.p y else 0 := by
    unfold W_pref convPMF
    dsimp only
    rw [Finset.sum_filter]
    have hite : ∀ w : Fin (2 ^ k),
        (if prefMod k j w = u then ∑ x : Fin (2 ^ k), X.p x * Z.p (subModFin hN w x) else 0) =
        ∑ x : Fin (2 ^ k), if prefMod k j w = u then X.p x * Z.p (subModFin hN w x) else 0 := fun w => by
      split_ifs <;> simp
    simp_rw [hite]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    -- Reindex w : Fin (2^k) via y = subModFin hN w x (inverse w = (x + y) % 2^k)
    let e : Fin (2 ^ k) ≃ Fin (2 ^ k) :=
      { toFun := fun y => ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩
        invFun := fun w => subModFin hN w x
        left_inv := fun y => by
          apply Fin.ext; dsimp [subModFin]
          have hx := x.isLt; have hy := y.isLt
          by_cases h : x.val + y.val < 2 ^ k
          · rw [Nat.mod_eq_of_lt h]
            have : x.val + y.val + (2 ^ k - x.val) = y.val + 2 ^ k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
          · have h1 : (x.val + y.val) % 2 ^ k = x.val + y.val - 2 ^ k := by
              calc (x.val + y.val) % 2 ^ k = ((x.val + y.val - 2 ^ k) + 2 ^ k) % 2 ^ k := by congr 1; omega
                _ = (x.val + y.val - 2 ^ k) % 2 ^ k := Nat.add_mod_right _ _
                _ = x.val + y.val - 2 ^ k := Nat.mod_eq_of_lt (by omega)
            rw [h1]
            have : x.val + y.val - 2 ^ k + (2 ^ k - x.val) = y.val := by omega
            rw [this, Nat.mod_eq_of_lt hy]
        right_inv := fun w => by apply Fin.ext; exact add_subModFin_mod hN w x }
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro y _
    have hsub : subModFin hN (e y) x = y := e.left_inv y
    rw [hsub]; rfl
  rw [hlhs]
  -- Group x by prefMod k j x = a and y by prefMod k j y = b
  rw [← Finset.sum_fiberwise_of_maps_to (g := prefMod k j) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro a _
  have hinner : ∀ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a),
      (∑ y : Fin (2 ^ k),
        if prefMod k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ = u then X.p x * Z.p y else 0) =
      X.p x * W_pref Z j (subModFin hNj u a) := by
    intro x hx
    have hxa : prefMod k j x = a := (Finset.mem_filter.mp hx).2
    rw [← Finset.sum_fiberwise_of_maps_to (g := prefMod k j) (fun _ _ => Finset.mem_univ _)]
    rw [Fintype.sum_eq_single (subModFin hNj u a)]
    · unfold W_pref
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have hyb : prefMod k j y = subModFin hNj u a := (Finset.mem_filter.mp hy).2
      have hcond : prefMod k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ = u := by
        rw [prefMod_add_mod hj, hxa, hyb]
        apply Fin.ext; exact add_subModFin_mod hNj u a
      simp [hcond]
    · intro b hb
      apply Finset.sum_eq_zero
      intro y hy
      have hyb : prefMod k j y = b := (Finset.mem_filter.mp hy).2
      have hne : prefMod k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ ≠ u := by
        rw [prefMod_add_mod hj, hxa, hyb]
        intro heq
        apply hb
        have hval := congrArg Fin.val heq
        dsimp only at hval
        apply Fin.ext
        dsimp [subModFin]
        have ha := a.isLt; have hb_lt := b.isLt
        by_cases h : a.val + b.val < 2 ^ j
        · rw [Nat.mod_eq_of_lt h] at hval
          have : u.val + (2 ^ j - a.val) = b.val + 2 ^ j := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hb_lt]
        · have h1 : (a.val + b.val) % 2 ^ j = a.val + b.val - 2 ^ j := by
            calc (a.val + b.val) % 2 ^ j = ((a.val + b.val - 2 ^ j) + 2 ^ j) % 2 ^ j := by congr 1; omega
              _ = (a.val + b.val - 2 ^ j) % 2 ^ j := Nat.add_mod_right _ _
              _ = a.val + b.val - 2 ^ j := Nat.mod_eq_of_lt (by omega)
          rw [h1] at hval
          have : u.val + (2 ^ j - a.val) = b.val := by omega
          rw [this, Nat.mod_eq_of_lt hb_lt]
      simp [hne]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  rfl

lemma W_bit1_conv_eq {k j : ℕ} (hj : j < k) (X Z : PMF_Fin (2 ^ k)) (u : Fin (2 ^ j)) :
    W_bit1 (convPMF (Nat.two_pow_pos k) X Z) j u =
      ∑ a : Fin (2 ^ j),
        W_pref X j a * W_pref Z j (subModFin (Nat.two_pow_pos j) u a) *
          xorProb (q_bit X j a) (q_bit Z j (subModFin (Nat.two_pow_pos j) u a))
            (carryBit j a (subModFin (Nat.two_pow_pos j) u a)) := by
  let hN := Nat.two_pow_pos k
  let hNj := Nat.two_pow_pos j
  -- Rewrite LHS as double sum over (x, y)
  have hlhs : W_bit1 (convPMF hN X Z) j u =
      ∑ x : Fin (2 ^ k), ∑ y : Fin (2 ^ k),
        if prefMod k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ = u ∧
           bitAt k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ = true
        then X.p x * Z.p y else 0 := by
    unfold W_bit1 convPMF
    dsimp only
    rw [Finset.sum_filter]
    have hite : ∀ w : Fin (2 ^ k),
        (if prefMod k j w = u ∧ bitAt k j w = true then ∑ x : Fin (2 ^ k), X.p x * Z.p (subModFin hN w x) else 0) =
        ∑ x : Fin (2 ^ k), if prefMod k j w = u ∧ bitAt k j w = true then X.p x * Z.p (subModFin hN w x) else 0 := fun w => by
      split_ifs <;> simp
    simp_rw [hite]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    let e : Fin (2 ^ k) ≃ Fin (2 ^ k) :=
      { toFun := fun y => ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩
        invFun := fun w => subModFin hN w x
        left_inv := fun y => by
          apply Fin.ext; dsimp [subModFin]
          have hx := x.isLt; have hy := y.isLt
          by_cases h : x.val + y.val < 2 ^ k
          · rw [Nat.mod_eq_of_lt h]
            have : x.val + y.val + (2 ^ k - x.val) = y.val + 2 ^ k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
          · have h1 : (x.val + y.val) % 2 ^ k = x.val + y.val - 2 ^ k := by
              calc (x.val + y.val) % 2 ^ k = ((x.val + y.val - 2 ^ k) + 2 ^ k) % 2 ^ k := by congr 1; omega
                _ = (x.val + y.val - 2 ^ k) % 2 ^ k := Nat.add_mod_right _ _
                _ = x.val + y.val - 2 ^ k := Nat.mod_eq_of_lt (by omega)
            rw [h1]
            have : x.val + y.val - 2 ^ k + (2 ^ k - x.val) = y.val := by omega
            rw [this, Nat.mod_eq_of_lt hy]
        right_inv := fun w => by apply Fin.ext; exact add_subModFin_mod hN w x }
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro y _
    have hsub : subModFin hN (e y) x = y := e.left_inv y
    rw [hsub]; rfl
  rw [hlhs]
  rw [← Finset.sum_fiberwise_of_maps_to (g := prefMod k j) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro a _
  set b := subModFin hNj u a
  -- For fixed x with prefMod x = a, only y with prefMod y = b can match prefMod (x+y) = u
  have hinner : ∀ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a),
      (∑ y : Fin (2 ^ k),
        if prefMod k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ = u ∧
           bitAt k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ = true
        then X.p x * Z.p y else 0) =
      ∑ y ∈ Finset.univ.filter (fun y : Fin (2 ^ k) => prefMod k j y = b),
        if xor (xor (bitAt k j x) (bitAt k j y)) (carryBit j a b) = true then X.p x * Z.p y else 0 := by
    intro x hx
    have hxa : prefMod k j x = a := (Finset.mem_filter.mp hx).2
    rw [← Finset.sum_fiberwise_of_maps_to (g := prefMod k j) (fun _ _ => Finset.mem_univ _)]
    rw [Fintype.sum_eq_single b]
    · apply Finset.sum_congr rfl
      intro y hy
      have hyb : prefMod k j y = b := (Finset.mem_filter.mp hy).2
      have hpref : prefMod k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ = u := by
        rw [prefMod_add_mod hj.le, hxa, hyb]; apply Fin.ext; exact add_subModFin_mod hNj u a
      have hbit := bitAt_add_mod hj x y
      dsimp only at hbit
      rw [hxa, hyb] at hbit
      simp [hpref, hbit]
    · intro b' hb'
      apply Finset.sum_eq_zero
      intro y hy
      have hyb' : prefMod k j y = b' := (Finset.mem_filter.mp hy).2
      have hne : prefMod k j ⟨(x.val + y.val) % 2 ^ k, Nat.mod_lt _ hN⟩ ≠ u := by
        rw [prefMod_add_mod hj.le, hxa, hyb']
        intro heq; apply hb'
        have hval := congrArg Fin.val heq; dsimp only at hval
        apply Fin.ext; dsimp [b, subModFin]
        have ha := a.isLt; have hb_lt := b'.isLt
        by_cases h : a.val + b'.val < 2 ^ j
        · rw [Nat.mod_eq_of_lt h] at hval
          have : u.val + (2 ^ j - a.val) = b'.val + 2 ^ j := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hb_lt]
        · have h1 : (a.val + b'.val) % 2 ^ j = a.val + b'.val - 2 ^ j := by
            calc (a.val + b'.val) % 2 ^ j = ((a.val + b'.val - 2 ^ j) + 2 ^ j) % 2 ^ j := by congr 1; omega
              _ = (a.val + b'.val - 2 ^ j) % 2 ^ j := Nat.add_mod_right _ _
              _ = a.val + b'.val - 2 ^ j := Nat.mod_eq_of_lt (by omega)
          rw [h1] at hval
          have : u.val + (2 ^ j - a.val) = b'.val := by omega
          rw [this, Nat.mod_eq_of_lt hb_lt]
      simp [hne]
  rw [Finset.sum_congr rfl hinner]
  -- Split by bitAt x ∈ {true, false} and bitAt y ∈ {true, false}
  have hW0_eq : ∀ (μ : PMF_Fin (2 ^ k)) (c : Fin (2 ^ j)),
      (∑ z ∈ Finset.univ.filter (fun z : Fin (2 ^ k) => prefMod k j z = c ∧ bitAt k j z = false), μ.p z) =
      W_pref μ j c - W_bit1 μ j c := by
    intro μ c
    have hsplit : W_pref μ j c =
        W_bit1 μ j c + ∑ z ∈ Finset.univ.filter (fun z : Fin (2 ^ k) => prefMod k j z = c ∧ bitAt k j z = false), μ.p z := by
      unfold W_pref W_bit1
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun z => bitAt k j z = true)]
      congr 1 <;> apply Finset.sum_congr _ (fun _ _ => rfl) <;> ext z <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true]
    linarith
  have hW1_mul : ∀ (μ : PMF_Fin (2 ^ k)) (c : Fin (2 ^ j)),
      W_bit1 μ j c = W_pref μ j c * q_bit μ j c := by
    intro μ c
    unfold q_bit
    split_ifs with h
    · have hle := W_bit1_le_W_pref μ j c
      have hge : 0 ≤ W_bit1 μ j c := Finset.sum_nonneg fun z _ => μ.nonneg z
      linarith
    · field_simp [h]
  have hW0_mul : ∀ (μ : PMF_Fin (2 ^ k)) (c : Fin (2 ^ j)),
      W_pref μ j c - W_bit1 μ j c = W_pref μ j c * (1 - q_bit μ j c) := by
    intro μ c; rw [hW1_mul μ c]; ring
  -- Evaluate the double sum by case-splitting on carryBit j a b
  have hsplit_x : ∀ (f : Fin (2 ^ k) → ℝ),
      (∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a), f x) =
      (∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = true), f x) +
      (∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = false), f x) := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun x => bitAt k j x = true)]
    congr 1 <;> apply Finset.sum_congr _ (fun _ _ => rfl) <;> ext x <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true]
  rw [hsplit_x]
  cases hc : carryBit j a b
  · -- carry = false: (bit x = true ∧ bit y = false) ∨ (bit x = false ∧ bit y = true)
    have ht : ∀ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = true),
        (∑ y ∈ Finset.univ.filter (fun y : Fin (2 ^ k) => prefMod k j y = b),
          if xor (xor (bitAt k j x) (bitAt k j y)) false = true then X.p x * Z.p y else 0) =
        X.p x * (W_pref Z j b - W_bit1 Z j b) := by
      intro x hx
      have hbx : bitAt k j x = true := (Finset.mem_filter.mp hx).2.2
      rw [← hW0_eq Z b, Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbx]
      cases bitAt k j y <;> simp
    have hf : ∀ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = false),
        (∑ y ∈ Finset.univ.filter (fun y : Fin (2 ^ k) => prefMod k j y = b),
          if xor (xor (bitAt k j x) (bitAt k j y)) false = true then X.p x * Z.p y else 0) =
        X.p x * W_bit1 Z j b := by
      intro x hx
      have hbx : bitAt k j x = false := (Finset.mem_filter.mp hx).2.2
      unfold W_bit1
      rw [Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbx]
      cases bitAt k j y <;> simp
    rw [Finset.sum_congr rfl ht, Finset.sum_congr rfl hf, ← Finset.sum_mul, ← Finset.sum_mul,
        hW0_eq X a, show (∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = true), X.p x) = W_bit1 X j a from rfl,
        hW1_mul X a, hW1_mul Z b]
    simp only [xorProb, Bool.false_eq_true, ↓reduceIte]; ring
  · -- carry = true: (bit x = true ∧ bit y = true) ∨ (bit x = false ∧ bit y = false)
    have ht : ∀ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = true),
        (∑ y ∈ Finset.univ.filter (fun y : Fin (2 ^ k) => prefMod k j y = b),
          if xor (xor (bitAt k j x) (bitAt k j y)) true = true then X.p x * Z.p y else 0) =
        X.p x * W_bit1 Z j b := by
      intro x hx
      have hbx : bitAt k j x = true := (Finset.mem_filter.mp hx).2.2
      unfold W_bit1
      rw [Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbx]
      cases bitAt k j y <;> simp
    have hf : ∀ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = false),
        (∑ y ∈ Finset.univ.filter (fun y : Fin (2 ^ k) => prefMod k j y = b),
          if xor (xor (bitAt k j x) (bitAt k j y)) true = true then X.p x * Z.p y else 0) =
        X.p x * (W_pref Z j b - W_bit1 Z j b) := by
      intro x hx
      have hbx : bitAt k j x = false := (Finset.mem_filter.mp hx).2.2
      rw [← hW0_eq Z b, Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbx]
      cases bitAt k j y <;> simp
    rw [Finset.sum_congr rfl ht, Finset.sum_congr rfl hf, ← Finset.sum_mul, ← Finset.sum_mul,
        hW0_eq X a, show (∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ k) => prefMod k j x = a ∧ bitAt k j x = true), X.p x) = W_bit1 X j a from rfl,
        hW1_mul X a, hW1_mul Z b]
    simp only [xorProb, ↓reduceIte]; ring

/-- Single-bit conditional entropy gain under convolution (for `j < k`). -/
lemma condBitEnt_conv_sub_ge {k j : ℕ} (hj : j < k) (X Z : PMF_Fin (2 ^ k)) :
    condBitEnt (convPMF (Nat.two_pow_pos k) X Z) j - condBitEnt X j ≥
      2 * (condBitEnt Z j) ^ 2 * (Real.log 2 - condBitEnt X j) := by
  let U := convPMF (Nat.two_pow_pos k) X Z
  let hNj := Nat.two_pow_pos j
  -- Step 1: Concavity of binEntropy at each prefix u : Fin (2^j)
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
        unfold q_bit; rw [if_neg hU0, W_bit1_conv_eq hj X Z u, Finset.sum_div]
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
  -- Step 2: Sum over u and reindex (u, a) ↔ (a, b) with b = subModFin hNj u a
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
  -- Step 3: Subtract condBitEnt X j and apply Lemma 1b pointwise
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
      2 * (∑ b : Fin (2 ^ j), W_pref Z j b * (Real.binEntropy (q_bit Z j b)) ^ 2) *
          (Real.log 2 - condBitEnt X j) := by
    have h1 : condBitEnt U j - condBitEnt X j ≥
        ∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
          W_pref X j a * W_pref Z j b *
            (2 * (Real.binEntropy (q_bit Z j b)) ^ 2 * (Real.log 2 - Real.binEntropy (q_bit X j a))) := by
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
            (2 * (Real.binEntropy (q_bit Z j b)) ^ 2 * (Real.log 2 - Real.binEntropy (q_bit X j a))) ≤
          ∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
            W_pref X j a * W_pref Z j b *
              (Real.binEntropy ((1 - |1 - 2 * q_bit X j a| * |1 - 2 * q_bit Z j b|) / 2) - Real.binEntropy (q_bit X j a)) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        apply mul_le_mul_of_nonneg_left
        · exact binEntropy_xor_gain (q_bit_bounds X j a).1 (q_bit_bounds X j a).2
            (q_bit_bounds Z j b).1 (q_bit_bounds Z j b).2
        · exact mul_nonneg (W_pref_nonneg X j a) (W_pref_nonneg Z j b)
      linarith
    have hfac : (∑ a : Fin (2 ^ j), ∑ b : Fin (2 ^ j),
        W_pref X j a * W_pref Z j b *
          (2 * (Real.binEntropy (q_bit Z j b)) ^ 2 * (Real.log 2 - Real.binEntropy (q_bit X j a)))) =
        2 * (∑ b : Fin (2 ^ j), W_pref Z j b * (Real.binEntropy (q_bit Z j b)) ^ 2) *
          (Real.log 2 - condBitEnt X j) := by
      have hX_def : Real.log 2 - condBitEnt X j =
          ∑ a : Fin (2 ^ j), W_pref X j a * (Real.log 2 - Real.binEntropy (q_bit X j a)) := by
        unfold condBitEnt
        rw [Finset.sum_congr rfl (fun a _ => mul_sub _ _ _), Finset.sum_sub_distrib,
            ← Finset.sum_mul, W_pref_sum_one X j, one_mul]
      rw [hX_def, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro b _; ring
    linarith
  -- Step 4: Cauchy-Schwarz / Jensen for t ↦ t^2 on Z
  have hcs : (condBitEnt Z j) ^ 2 ≤ ∑ b : Fin (2 ^ j), W_pref Z j b * (Real.binEntropy (q_bit Z j b)) ^ 2 := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun b : Fin (2 ^ j) => Real.sqrt (W_pref Z j b))
      (g := fun b : Fin (2 ^ j) => Real.sqrt (W_pref Z j b) * Real.binEntropy (q_bit Z j b))
    have h1 : (∑ b : Fin (2 ^ j), Real.sqrt (W_pref Z j b) * (Real.sqrt (W_pref Z j b) * Real.binEntropy (q_bit Z j b))) =
        condBitEnt Z j := by
      unfold condBitEnt
      apply Finset.sum_congr rfl; intro b _
      rw [← mul_assoc, Real.mul_self_sqrt (W_pref_nonneg Z j b)]
    have h2 : (∑ b : Fin (2 ^ j), Real.sqrt (W_pref Z j b) ^ 2) = 1 := by
      simp_rw [Real.sq_sqrt (W_pref_nonneg Z j _)]
      exact W_pref_sum_one Z j
    have h3 : (∑ b : Fin (2 ^ j), (Real.sqrt (W_pref Z j b) * Real.binEntropy (q_bit Z j b)) ^ 2) =
        ∑ b : Fin (2 ^ j), W_pref Z j b * (Real.binEntropy (q_bit Z j b)) ^ 2 := by
      apply Finset.sum_congr rfl; intro b _
      rw [mul_pow, Real.sq_sqrt (W_pref_nonneg Z j b)]
    rw [h1, h2, one_mul, h3] at hsq
    exact hsq
  have hdef_nonneg : 0 ≤ Real.log 2 - condBitEnt X j := by
    have hle : condBitEnt X j ≤ ∑ a : Fin (2 ^ j), W_pref X j a * Real.log 2 := by
      unfold condBitEnt
      apply Finset.sum_le_sum; intro a _
      exact mul_le_mul_of_nonneg_left (Real.binEntropy_le_log_two (p := q_bit X j a)) (W_pref_nonneg X j a)
    rw [← Finset.sum_mul, W_pref_sum_one X j, one_mul] at hle
    linarith
  nlinarith

/-- Lemma 2 (Bitwise Chain-Rule Entropy Gain on `Fin (2^k)`):
    `Hnat (conv X Z) - Hnat X ≥ 2 * ∑ j : Fin k, (condBitEnt Z j)^2 * (log 2 - condBitEnt X j)`. -/
theorem Hnat_conv_sub_ge_bitwise {k : ℕ} (X Z : PMF_Fin (2 ^ k)) :
    Hnat (convPMF (Nat.two_pow_pos k) X Z) - Hnat X ≥
      2 * ∑ j : Fin k, (condBitEnt Z j.val) ^ 2 * (Real.log 2 - condBitEnt X j.val) := by
  rw [Hnat_eq_sum_condBitEnt, Hnat_eq_sum_condBitEnt, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := condBitEnt_conv_sub_ge j.isLt X Z
  linarith

end Erdos18

#print axioms Erdos18.Hnat_le_log_supp
#print axioms Erdos18.Hnat_eq_sum_condBitEnt
#print axioms Erdos18.Hnat_conv_sub_ge_bitwise
