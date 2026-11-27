import Erdos18.PrimeFieldDilation
import Erdos18.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Erdos18/PrimeFieldCovering.lean — Carry-Free CRT Chain Rule & Covering (Module 3)

Formalizes:
- Section 1: 2-factor CRT chain rule on `ZMod (q * M₂) ≃+* ZMod q × ZMod M₂`.
- Section 2: Recursive list-CRT coordinate entropy/deficit & `crt_list_dilation_entropy_gain`.
- Section 3: `M_core`, 16-subinterval Bertrand prime band, harmonic sum, Lemma 4 & Lemma 5.
-/

namespace Erdos18

open Finset Nat Real

/-! ## Section 1: 2-Factor CRT Chain Rule on `ZMod (q * M₂)` -/

/-- Additive convolution on `ZMod M`. -/
noncomputable def conv_zmod {M : ℕ} [NeZero M] (U V : PMF_ZMod M) : PMF_ZMod M :=
  conv_dilate U V 1

/-- Point mass at `x₀` on `ZMod M`. -/
noncomputable def pointPMF {M : ℕ} [NeZero M] (x₀ : ZMod M) : PMF_ZMod M where
  p x := if x = x₀ then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_one := by simp

/-- Uniform PMF on a nonempty `Finset (ZMod M)`. -/
noncomputable def unifFinsetPMF {M : ℕ} [NeZero M] (S : Finset (ZMod M)) (hS : S.Nonempty) :
    PMF_ZMod M where
  p x := if x ∈ S then (1 : ℝ) / (S.card : ℝ) else 0
  nonneg x := by split_ifs <;> positivity
  sum_one := by
    have hpos : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
    simp [Finset.sum_ite_mem, hpos]

/-- Pushforward of a `PMF_ZMod M` along a function `f : ZMod M → ZMod N`. -/
noncomputable def mapPMF {M N : ℕ} [NeZero M] [NeZero N] (f : ZMod M → ZMod N)
    (μ : PMF_ZMod M) : PMF_ZMod N where
  p y := ∑ x ∈ Finset.univ.filter (fun x => f x = y), μ.p x
  nonneg y := Finset.sum_nonneg fun x _ => μ.nonneg x
  sum_one := by
    have hpart := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (ZMod M)))
      (t := (Finset.univ : Finset (ZMod N))) (g := f) (fun _ _ => Finset.mem_univ _) μ.p
    simpa [μ.sum_one] using hpart

/-- Pushforward along a bijection preserves `Hnat_zmod`. -/
lemma Hnat_zmod_equiv {M N : ℕ} [NeZero M] [NeZero N] (e : ZMod M ≃ ZMod N) (μ : PMF_ZMod M) :
    Hnat_zmod (mapPMF e μ) = Hnat_zmod μ := by
  unfold Hnat_zmod mapPMF
  have hval : ∀ y : ZMod N, (∑ x ∈ Finset.univ.filter (fun x => e x = y), μ.p x) = μ.p (e.symm y) := by
    intro y
    have hfilt : Finset.univ.filter (fun x => e x = y) = {e.symm y} := by
      ext x; simp [Equiv.eq_symm_apply]
    rw [hfilt, Finset.sum_singleton]
  simp_rw [hval]
  exact Equiv.sum_comp e.symm (fun x => Real.negMulLog (μ.p x))

/-- First marginal of `X : PMF_ZMod (q * M₂)` under `ZMod.chineseRemainder hcop`. -/
noncomputable def fstMarg {q M₂ : ℕ} [NeZero q] [NeZero M₂] [NeZero (q * M₂)]
    (hcop : Nat.Coprime q M₂) (X : PMF_ZMod (q * M₂)) : PMF_ZMod q where
  p a := ∑ b : ZMod M₂, X.p ((ZMod.chineseRemainder hcop).symm (a, b))
  nonneg a := Finset.sum_nonneg fun b _ => X.nonneg _
  sum_one := by
    rw [← Fintype.sum_prod_type']
    have hcomp := Equiv.sum_comp (ZMod.chineseRemainder hcop).symm.toEquiv X.p
    simpa [X.sum_one] using hcomp

/-- Second conditional of `X : PMF_ZMod (q * M₂)` given `fst = a`. -/
noncomputable def sndCond {q M₂ : ℕ} [NeZero q] [NeZero M₂] [NeZero (q * M₂)]
    (hcop : Nat.Coprime q M₂) (X : PMF_ZMod (q * M₂)) (a : ZMod q) : PMF_ZMod M₂ where
  p b :=
    if (fstMarg hcop X).p a = 0 then (pointPMF (0 : ZMod M₂)).p b
    else X.p ((ZMod.chineseRemainder hcop).symm (a, b)) / (fstMarg hcop X).p a
  nonneg b := by
    split_ifs with h
    · exact (pointPMF (0 : ZMod M₂)).nonneg b
    · exact div_nonneg (X.nonneg _) ((fstMarg hcop X).nonneg a)
  sum_one := by
    split_ifs with h
    · exact (pointPMF (0 : ZMod M₂)).sum_one
    · rw [← Finset.sum_div]
      exact div_self h

lemma fstMarg_mul_sndCond {q M₂ : ℕ} [NeZero q] [NeZero M₂] [NeZero (q * M₂)]
    (hcop : Nat.Coprime q M₂) (X : PMF_ZMod (q * M₂)) (a : ZMod q) (b : ZMod M₂) :
    (fstMarg hcop X).p a * (sndCond hcop X a).p b = X.p ((ZMod.chineseRemainder hcop).symm (a, b)) := by
  dsimp [sndCond]
  split_ifs with h
  · rw [h, zero_mul]
    have hsum0 : ∑ b' : ZMod M₂, X.p ((ZMod.chineseRemainder hcop).symm (a, b')) = 0 := h
    symm
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun b' _ => X.nonneg _)).mp hsum0 b (Finset.mem_univ b)
  · exact mul_div_cancel₀ _ h

/-- Exact 2-factor CRT chain rule for Shannon entropy. -/
theorem Hnat_crt_chain_rule {q M₂ : ℕ} [NeZero q] [NeZero M₂] [NeZero (q * M₂)]
    (hcop : Nat.Coprime q M₂) (X : PMF_ZMod (q * M₂)) :
    Hnat_zmod X = Hnat_zmod (fstMarg hcop X) +
      ∑ a : ZMod q, (fstMarg hcop X).p a * Hnat_zmod (sndCond hcop X a) := by
  unfold Hnat_zmod
  have hcomp := Equiv.sum_comp (ZMod.chineseRemainder hcop).symm.toEquiv (fun x => Real.negMulLog (X.p x))
  rw [← hcomp, Fintype.sum_prod_type]; simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (fstMarg hcop X).p a = 0
  · rw [ha, Real.negMulLog_zero, zero_mul, add_zero]
    apply Finset.sum_eq_zero
    intro b _
    have hx0 : X.p ((ZMod.chineseRemainder hcop).symm (a, b)) = 0 := by
      have := fstMarg_mul_sndCond hcop X a b
      rw [ha, zero_mul] at this
      exact this.symm
    rw [hx0, Real.negMulLog_zero]
  · have ha_pos : 0 < (fstMarg hcop X).p a := lt_of_le_of_ne ((fstMarg hcop X).nonneg a) (Ne.symm ha)
    have hsplit : ∀ b : ZMod M₂,
        Real.negMulLog (X.p ((ZMod.chineseRemainder hcop).symm (a, b))) =
          -(fstMarg hcop X).p a * (sndCond hcop X a).p b * Real.log ((fstMarg hcop X).p a) +
          (fstMarg hcop X).p a * Real.negMulLog ((sndCond hcop X a).p b) := by
      intro b
      rw [← fstMarg_mul_sndCond hcop X a b]
      by_cases hb : (sndCond hcop X a).p b = 0
      · simp [hb, Real.negMulLog_zero]
      · rw [Real.negMulLog, Real.negMulLog, Real.log_mul ha hb]
        ring
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hsum1 : ∑ b : ZMod M₂, -(fstMarg hcop X).p a * (sndCond hcop X a).p b *
        Real.log ((fstMarg hcop X).p a) = Real.negMulLog ((fstMarg hcop X).p a) := by
      have h1 : ∀ b : ZMod M₂, -(fstMarg hcop X).p a * (sndCond hcop X a).p b *
          Real.log ((fstMarg hcop X).p a) =
          Real.negMulLog ((fstMarg hcop X).p a) * (sndCond hcop X a).p b := fun b => by
        rw [Real.negMulLog]; ring
      simp_rw [h1, ← Finset.mul_sum, (sndCond hcop X a).sum_one, mul_one]
    rw [hsum1]

/-- Exact 2-factor CRT chain rule for entropy deficit. -/
theorem deficit_crt_chain_rule {q M₂ : ℕ} [NeZero q] [NeZero M₂] [NeZero (q * M₂)]
    (hcop : Nat.Coprime q M₂) (X : PMF_ZMod (q * M₂)) :
    deficit_zmod X = deficit_zmod (fstMarg hcop X) +
      ∑ a : ZMod q, (fstMarg hcop X).p a * deficit_zmod (sndCond hcop X a) := by
  unfold deficit_zmod
  rw [Hnat_crt_chain_rule hcop X]
  have hlog : Real.log ((q * M₂ : ℕ) : ℝ) = Real.log (q : ℝ) + Real.log (M₂ : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne q))
      (Nat.cast_ne_zero.mpr (NeZero.ne M₂))]
  have hsum_log : ∑ a : ZMod q, (fstMarg hcop X).p a * (Real.log (M₂ : ℝ) - Hnat_zmod (sndCond hcop X a)) =
      Real.log (M₂ : ℝ) - ∑ a : ZMod q, (fstMarg hcop X).p a * Hnat_zmod (sndCond hcop X a) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (fstMarg hcop X).sum_one, one_mul]
  rw [hlog, hsum_log]
  ring

/-- Helper: CRT image of `(conv_dilate X Y c)` decomposes as a mixture over `(a, b)` on the second factor. -/
private lemma crt_conv_dilate_fst {q M₂ : ℕ} [NeZero q] [NeZero M₂] [NeZero (q * M₂)]
    (hcop : Nat.Coprime q M₂) (X Y : PMF_ZMod (q * M₂)) (c : ℕ) :
    fstMarg hcop (conv_dilate X Y (c : ZMod (q * M₂))) =
      conv_dilate (fstMarg hcop X) (fstMarg hcop Y) (c : ZMod q) := by
  ext u₁
  dsimp [fstMarg, conv_dilate]
  have hcomp : ∀ u₂ : ZMod M₂,
      ∑ y : ZMod (q * M₂), X.p ((ZMod.chineseRemainder hcop).symm (u₁, u₂) - (c : ZMod (q * M₂)) * y) * Y.p y =
      ∑ b : ZMod q, ∑ y₂ : ZMod M₂,
        X.p ((ZMod.chineseRemainder hcop).symm (u₁ - (c : ZMod q) * b, u₂ - (c : ZMod M₂) * y₂)) *
        Y.p ((ZMod.chineseRemainder hcop).symm (b, y₂)) := by
    intro u₂
    have he := Equiv.sum_comp (ZMod.chineseRemainder hcop).symm.toEquiv
      (fun y => X.p ((ZMod.chineseRemainder hcop).symm (u₁, u₂) - (c : ZMod (q * M₂)) * y) * Y.p y)
    rw [← he, Fintype.sum_prod_type]; simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y₂ _ => ?_
    congr 2
    have hmap : (ZMod.chineseRemainder hcop).symm (u₁, u₂) -
        (c : ZMod (q * M₂)) * (ZMod.chineseRemainder hcop).symm (b, y₂) =
        (ZMod.chineseRemainder hcop).symm (u₁ - (c : ZMod q) * b, u₂ - (c : ZMod M₂) * y₂) := by
      apply (ZMod.chineseRemainder hcop).injective
      simp [map_sub, map_mul, map_natCast]; rfl
    exact hmap
  simp_rw [hcomp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  have hinner : ∀ y₂ : ZMod M₂,
      ∑ u₂ : ZMod M₂,
        X.p ((ZMod.chineseRemainder hcop).symm (u₁ - (c : ZMod q) * b, u₂ - (c : ZMod M₂) * y₂)) *
        Y.p ((ZMod.chineseRemainder hcop).symm (b, y₂)) =
      (∑ x₂ : ZMod M₂, X.p ((ZMod.chineseRemainder hcop).symm (u₁ - (c : ZMod q) * b, x₂))) *
        Y.p ((ZMod.chineseRemainder hcop).symm (b, y₂)) := by
    intro y₂
    rw [← Finset.sum_mul]
    congr 1
    exact Equiv.sum_comp (Equiv.subRight ((c : ZMod M₂) * y₂))
      (fun x₂ => X.p ((ZMod.chineseRemainder hcop).symm (u₁ - (c : ZMod q) * b, x₂)))
  simp_rw [hinner, ← Finset.mul_sum]

/-- **2-Factor Carry-Free CRT Chain-Rule Entropy Gain:**
For any `c : ℕ` and independent `X, Y : PMF_ZMod (q * M₂)` with `Nat.Coprime q M₂`,
`H(X + cY) - H(X) ≥ (H(X₁ + cY₁) - H(X₁)) + ∑ a b, X₁(a) Y₁(b) (H((X₂|a) + c(Y₂|b)) - H(X₂|a))`. -/
theorem Hnat_conv_dilate_crt_ge {q M₂ : ℕ} [NeZero q] [NeZero M₂] [NeZero (q * M₂)]
    (hcop : Nat.Coprime q M₂) (X Y : PMF_ZMod (q * M₂)) (c : ℕ) :
    (Hnat_zmod (conv_dilate (fstMarg hcop X) (fstMarg hcop Y) (c : ZMod q)) -
        Hnat_zmod (fstMarg hcop X)) +
      ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
        (Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) (c : ZMod M₂)) -
          Hnat_zmod (sndCond hcop X a)) ≤
      Hnat_zmod (conv_dilate X Y (c : ZMod (q * M₂))) - Hnat_zmod X := by
  set U := conv_dilate X Y (c : ZMod (q * M₂))
  rw [Hnat_crt_chain_rule hcop U, Hnat_crt_chain_rule hcop X, crt_conv_dilate_fst hcop X Y c]
  -- Cancel the first-marginal terms; it suffices to bound the second-conditional entropy sum!
  suffices hcond :
      ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
        Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) (c : ZMod M₂)) ≤
      ∑ u₁ : ZMod q, (fstMarg hcop U).p u₁ * Hnat_zmod (sndCond hcop U u₁) by
    have hX2 : ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
        Hnat_zmod (sndCond hcop X a) =
        ∑ a : ZMod q, (fstMarg hcop X).p a * Hnat_zmod (sndCond hcop X a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 : ∀ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
          Hnat_zmod (sndCond hcop X a) =
          (fstMarg hcop X).p a * Hnat_zmod (sndCond hcop X a) * (fstMarg hcop Y).p b := fun b => by ring
      simp_rw [h1, ← Finset.mul_sum, (fstMarg hcop Y).sum_one, mul_one]
    have hsub : ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
        (Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) (c : ZMod M₂)) -
          Hnat_zmod (sndCond hcop X a)) =
        (∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
          Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) (c : ZMod M₂))) -
        (∑ a : ZMod q, (fstMarg hcop X).p a * Hnat_zmod (sndCond hcop X a)) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [hX2]
    rw [hsub]; rw [crt_conv_dilate_fst hcop X Y c] at hcond
    linarith
  -- Re-index (a, b) ↦ (u₁ = a + c * b, b)
  have hreindex :
      ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
        Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) (c : ZMod M₂)) =
      ∑ u₁ : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p (u₁ - (c : ZMod q) * b) * (fstMarg hcop Y).p b *
        Hnat_zmod (conv_dilate (sndCond hcop X (u₁ - (c : ZMod q) * b)) (sndCond hcop Y b) (c : ZMod M₂)) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have he := Equiv.sum_comp (Equiv.subRight ((c : ZMod q) * b))
      (fun a => (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
        Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) (c : ZMod M₂)))
    exact he.symm
  rw [hreindex]
  refine Finset.sum_le_sum fun u₁ _ => ?_
  -- Express (fstMarg hcop U).p u₁ * (sndCond hcop U u₁).p u₂ as ∑ b, w(b) * P_b(u₂)
  have hmix : ∀ u₂ : ZMod M₂,
      (fstMarg hcop U).p u₁ * (sndCond hcop U u₁).p u₂ =
        ∑ b : ZMod q, (fstMarg hcop X).p (u₁ - (c : ZMod q) * b) * (fstMarg hcop Y).p b *
          (conv_dilate (sndCond hcop X (u₁ - (c : ZMod q) * b)) (sndCond hcop Y b) (c : ZMod M₂)).p u₂ := by
    intro u₂
    rw [fstMarg_mul_sndCond hcop U u₁ u₂]
    dsimp [U, conv_dilate]
    have he := Equiv.sum_comp (ZMod.chineseRemainder hcop).symm.toEquiv
      (fun y => X.p ((ZMod.chineseRemainder hcop).symm (u₁, u₂) - (c : ZMod (q * M₂)) * y) * Y.p y)
    rw [← he, Fintype.sum_prod_type]; simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y₂ _ => ?_
    have hmap : (ZMod.chineseRemainder hcop).symm (u₁, u₂) -
        (c : ZMod (q * M₂)) * (ZMod.chineseRemainder hcop).symm (b, y₂) =
        (ZMod.chineseRemainder hcop).symm (u₁ - (c : ZMod q) * b, u₂ - (c : ZMod M₂) * y₂) := by
      apply (ZMod.chineseRemainder hcop).injective
      simp [map_sub, map_mul, map_natCast]; rfl
    rw [hmap, ← fstMarg_mul_sndCond hcop X (u₁ - (c : ZMod q) * b) (u₂ - (c : ZMod M₂) * y₂),
        ← fstMarg_mul_sndCond hcop Y b y₂]
    ring
  by_cases hu1 : (fstMarg hcop U).p u₁ = 0
  · rw [hu1, zero_mul]
    have hsum_w : ∑ b : ZMod q, (fstMarg hcop X).p (u₁ - (c : ZMod q) * b) * (fstMarg hcop Y).p b = 0 := by
      have hfst := congrArg (fun μ : PMF_ZMod q => μ.p u₁) (crt_conv_dilate_fst hcop X Y c)
      dsimp [U, conv_dilate] at hu1 hfst ⊢
      linarith
    have hw0 : ∀ b : ZMod q, (fstMarg hcop X).p (u₁ - (c : ZMod q) * b) * (fstMarg hcop Y).p b = 0 :=
      fun b => (Finset.sum_eq_zero_iff_of_nonneg (fun b' _ =>
        mul_nonneg ((fstMarg hcop X).nonneg _) ((fstMarg hcop Y).nonneg _))).mp hsum_w b (Finset.mem_univ b)
    have : ∑ b : ZMod q, (fstMarg hcop X).p (u₁ - (c : ZMod q) * b) * (fstMarg hcop Y).p b *
        Hnat_zmod (conv_dilate (sndCond hcop X (u₁ - (c : ZMod q) * b)) (sndCond hcop Y b) (c : ZMod M₂)) = 0 :=
      Finset.sum_eq_zero fun b _ => by rw [hw0 b, zero_mul]
    linarith
  · have hu1_pos : 0 < (fstMarg hcop U).p u₁ :=
      lt_of_le_of_ne ((fstMarg hcop U).nonneg u₁) (Ne.symm hu1)
    let w : ZMod q → ℝ := fun b =>
      ((fstMarg hcop X).p (u₁ - (c : ZMod q) * b) * (fstMarg hcop Y).p b) / (fstMarg hcop U).p u₁
    have hw_nn : ∀ b ∈ (Finset.univ : Finset (ZMod q)), 0 ≤ w b := fun b _ =>
      div_nonneg (mul_nonneg ((fstMarg hcop X).nonneg _) ((fstMarg hcop Y).nonneg _)) hu1_pos.le
    have hw_sum : ∑ b : ZMod q, w b = 1 := by
      dsimp [w]
      rw [← Finset.sum_div]
      have hnum : ∑ b : ZMod q, (fstMarg hcop X).p (u₁ - (c : ZMod q) * b) * (fstMarg hcop Y).p b =
          (fstMarg hcop U).p u₁ := by
        have hfst := congrArg (fun μ : PMF_ZMod q => μ.p u₁) (crt_conv_dilate_fst hcop X Y c)
        exact hfst.symm
      rw [hnum, div_self hu1]
    have hconc : ∀ u₂ : ZMod M₂,
        ∑ b : ZMod q, w b * Real.negMulLog
          ((conv_dilate (sndCond hcop X (u₁ - (c : ZMod q) * b)) (sndCond hcop Y b) (c : ZMod M₂)).p u₂) ≤
          Real.negMulLog ((sndCond hcop U u₁).p u₂) := by
      intro u₂
      have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := w)
        (p := fun b => (conv_dilate (sndCond hcop X (u₁ - (c : ZMod q) * b)) (sndCond hcop Y b) (c : ZMod M₂)).p u₂)
        hw_nn hw_sum (fun b _ => (conv_dilate _ _ _).nonneg u₂)
      refine h.trans_eq ?_
      congr 1
      simp only [smul_eq_mul, w, div_mul_eq_mul_div, ← Finset.sum_div, ← hmix u₂]
      exact mul_div_cancel_left₀ _ hu1
    have htot := Finset.sum_le_sum fun u₂ (_ : u₂ ∈ Finset.univ) => hconc u₂
    have hmul := mul_le_mul_of_nonneg_left htot hu1_pos.le
    refine le_trans (le_of_eq ?_) hmul
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold Hnat_zmod
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u₂ _ => ?_
    dsimp [w]
    field_simp [hu1]

/-! ## Section 2: Recursive List-CRT Coordinate Entropy/Deficit & Dilation Gain -/

lemma list_prod_neZero {l : List ℕ} (hl : ∀ q ∈ l, q.Prime) : NeZero l.prod := by
  refine ⟨?_⟩
  induction l with
  | nil => simp
  | cons q l' ih =>
    simp only [List.prod_cons]
    exact mul_ne_zero (hl q List.mem_cons_self).ne_zero (ih fun p hp => hl p (List.mem_cons_of_mem q hp))

lemma head_coprime_tail_prod {q : ℕ} {l' : List ℕ}
    (hl : ∀ p ∈ q :: l', p.Prime) (hnd : (q :: l').Nodup) :
    Nat.Coprime q l'.prod := by
  have hq : q.Prime := hl q List.mem_cons_self
  have hnotmem : q ∉ l' := (List.nodup_cons.mp hnd).1
  induction l' with
  | nil => simp
  | cons p ps ih =>
    simp only [List.prod_cons]
    have hp : p.Prime := hl p (List.mem_cons_of_mem q List.mem_cons_self)
    have hne : q ≠ p := fun h => hnotmem (h ▸ List.mem_cons_self)
    refine Nat.Coprime.mul_right ((Nat.coprime_primes hq hp).mpr hne) ?_
    refine ih (fun r hr => ?_) ?_ ?_
    · rcases List.mem_cons.mp hr with rfl | hr'
      · exact hq
      · exact hl r (List.mem_cons_of_mem q (List.mem_cons_of_mem p hr'))
    · rw [List.nodup_cons] at hnd ⊢
      exact ⟨fun h => hnotmem (List.mem_cons_of_mem p h), (List.nodup_cons.mp hnd.2).2⟩
    · exact fun h => hnotmem (List.mem_cons_of_mem p h)

/-- Recursive coordinate deficit `δ_i(X) = log q_i - H(X_i | X_{<i})` along a nodup list of primes `l`. -/
noncomputable def coordDeficit :
    (l : List ℕ) → (hl : ∀ q ∈ l, q.Prime) → (hnd : l.Nodup) →
    @PMF_ZMod l.prod (list_prod_neZero hl) → Fin l.length → ℝ
  | [], _, _, _, i => Fin.elim0 i
  | q :: l', hl, hnd, X, i =>
    letI : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
    letI : NeZero l'.prod := list_prod_neZero (fun p hp => hl p (List.mem_cons_of_mem q hp))
    letI : NeZero (q * l'.prod) := list_prod_neZero hl
    let hcop := head_coprime_tail_prod hl hnd
    Fin.cases
      (deficit_zmod (fstMarg hcop X))
      (fun j => ∑ a : ZMod q, (fstMarg hcop X).p a *
        coordDeficit l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
          (sndCond hcop X a) j)
      i

/-- Recursive coordinate entropy `h_i(Y) = H(Y_i | Y_{<i})` along a nodup list of primes `l`. -/
noncomputable def coordEnt :
    (l : List ℕ) → (hl : ∀ q ∈ l, q.Prime) → (hnd : l.Nodup) →
    @PMF_ZMod l.prod (list_prod_neZero hl) → Fin l.length → ℝ
  | [], _, _, _, i => Fin.elim0 i
  | q :: l', hl, hnd, Y, i =>
    letI : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
    letI : NeZero l'.prod := list_prod_neZero (fun p hp => hl p (List.mem_cons_of_mem q hp))
    letI : NeZero (q * l'.prod) := list_prod_neZero hl
    let hcop := head_coprime_tail_prod hl hnd
    Fin.cases
      (Hnat_zmod (fstMarg hcop Y))
      (fun j => ∑ b : ZMod q, (fstMarg hcop Y).p b *
        coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
          (sndCond hcop Y b) j)
      i

lemma coordDeficit_nonneg (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) (hnd : l.Nodup)
    (X : @PMF_ZMod l.prod (list_prod_neZero hl)) (i : Fin l.length) :
    0 ≤ coordDeficit l hl hnd X i := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons q l' ih =>
    have : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
    have : NeZero l'.prod := list_prod_neZero (fun p hp => hl p (List.mem_cons_of_mem q hp))
    have : NeZero (q * l'.prod) := list_prod_neZero hl
    refine Fin.cases ?_ ?_ i
    · exact deficit_zmod_nonneg _
    · intro j
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg ((fstMarg (head_coprime_tail_prod hl hnd) X).nonneg a) (ih _ _ _ j)

lemma coordEnt_nonneg (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) (hnd : l.Nodup)
    (Y : @PMF_ZMod l.prod (list_prod_neZero hl)) (i : Fin l.length) :
    0 ≤ coordEnt l hl hnd Y i := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons q l' ih =>
    have : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
    have : NeZero l'.prod := list_prod_neZero (fun p hp => hl p (List.mem_cons_of_mem q hp))
    have : NeZero (q * l'.prod) := list_prod_neZero hl
    refine Fin.cases ?_ ?_ i
    · exact Hnat_zmod_nonneg _
    · intro j
      exact Finset.sum_nonneg fun b _ =>
        mul_nonneg ((fstMarg (head_coprime_tail_prod hl hnd) Y).nonneg b) (ih _ _ _ j)

theorem sum_coordDeficit (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) (hnd : l.Nodup)
    (X : @PMF_ZMod l.prod (list_prod_neZero hl)) :
    ∑ i : Fin l.length, coordDeficit l hl hnd X i =
      @deficit_zmod l.prod (list_prod_neZero hl) X := by
  induction l with
  | nil =>
    simp only [List.length_nil, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty] at X ⊢
    unfold deficit_zmod Hnat_zmod
    have h1 := X.sum_one
    simp only [Finset.univ_unique, Finset.sum_singleton] at h1 ⊢
    rw [h1]
    simp [Real.negMulLog]
  | cons q l' ih =>
    have : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
    have : NeZero l'.prod := list_prod_neZero (fun p hp => hl p (List.mem_cons_of_mem q hp))
    have : NeZero (q * l'.prod) := list_prod_neZero hl
    change ∑ i : Fin (l'.length + 1), coordDeficit (q :: l') hl hnd X i = _
    rw [Fin.sum_univ_succ]
    dsimp [coordDeficit]
    rw [Finset.sum_comm]
    have hinner : ∀ a : ZMod q,
        ∑ j : Fin l'.length, (fstMarg (head_coprime_tail_prod hl hnd) X).p a *
          coordDeficit l' (fun p hp => hl p (List.mem_cons_of_mem q hp))
            (List.nodup_cons.mp hnd).2 (sndCond (head_coprime_tail_prod hl hnd) X a) j =
        (fstMarg (head_coprime_tail_prod hl hnd) X).p a *
          deficit_zmod (sndCond (head_coprime_tail_prod hl hnd) X a) := by
      intro a
      rw [← Finset.mul_sum, ih]
    simp_rw [hinner]
    exact (deficit_crt_chain_rule (head_coprime_tail_prod hl hnd) X).symm

theorem sum_coordEnt (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) (hnd : l.Nodup)
    (Y : @PMF_ZMod l.prod (list_prod_neZero hl)) :
    ∑ i : Fin l.length, coordEnt l hl hnd Y i =
      @Hnat_zmod l.prod (list_prod_neZero hl) Y := by
  induction l with
  | nil =>
    simp only [List.length_nil, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty] at Y ⊢
    unfold Hnat_zmod
    have h1 := Y.sum_one
    simp only [Finset.univ_unique, Finset.sum_singleton] at h1 ⊢
    rw [h1]
    simp [Real.negMulLog]
  | cons q l' ih =>
    have : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
    have : NeZero l'.prod := list_prod_neZero (fun p hp => hl p (List.mem_cons_of_mem q hp))
    have : NeZero (q * l'.prod) := list_prod_neZero hl
    change ∑ i : Fin (l'.length + 1), coordEnt (q :: l') hl hnd Y i = _
    rw [Fin.sum_univ_succ]
    dsimp [coordEnt]
    rw [Finset.sum_comm]
    have hinner : ∀ b : ZMod q,
        ∑ j : Fin l'.length, (fstMarg (head_coprime_tail_prod hl hnd) Y).p b *
          coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp))
            (List.nodup_cons.mp hnd).2 (sndCond (head_coprime_tail_prod hl hnd) Y b) j =
        (fstMarg (head_coprime_tail_prod hl hnd) Y).p b *
          Hnat_zmod (sndCond (head_coprime_tail_prod hl hnd) Y b) := by
      intro b
      rw [← Finset.mul_sum, ih]
    simp_rw [hinner]
    exact (Hnat_crt_chain_rule (head_coprime_tail_prod hl hnd) Y).symm

/-- Helper: averaging over `c₁, c₂ ∈ smoothSet m_dil` equals `∑ c ≠ 0, dilatorWeight m_dil q c * f c`. -/
private lemma smooth_avg_eq_sum_dilatorWeight {m_dil q : ℕ} [Fact q.Prime]
    (hq_lo : 14 * m_dil / 25 < q) (f : ZMod q → ℝ) :
    (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
      ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil, f ((c₁ * c₂ : ℕ) : ZMod q) =
      ∑ c ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0), dilatorWeight m_dil q c * f c := by
  rw [← Finset.sum_product']
  have hmaps : ∀ p ∈ (smoothSet m_dil) ×ˢ (smoothSet m_dil),
      ((p.1 : ZMod q) * (p.2 : ZMod q)) ∈ Finset.univ.filter (fun c : ZMod q => c ≠ 0) := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hne1 : (p.1 : ZMod q) ≠ 0 := by
      intro h0
      have hlt : p.1 < q := lt_of_le_of_lt (smoothSet_le h1) hq_lo
      have hpos : 0 < p.1 := smoothSet_pos h1
      have hval := congrArg ZMod.val h0
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hval; omega
    have hne2 : (p.2 : ZMod q) ≠ 0 := by
      intro h0
      have hlt : p.2 < q := lt_of_le_of_lt (smoothSet_le h2) hq_lo
      have hpos : 0 < p.2 := smoothSet_pos h2
      have hval := congrArg ZMod.val h0
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hval; omega
    have hu1 := zmod_isUnit_of_ne_zero hne1
    have hu2 := zmod_isUnit_of_ne_zero hne2
    exact (hu1.mul hu2).ne_zero
  have hfib := (Finset.sum_fiberwise_of_maps_to
    (s := (smoothSet m_dil) ×ˢ (smoothSet m_dil))
    (t := Finset.univ.filter (fun c : ZMod q => c ≠ 0))
    (g := fun p : ℕ × ℕ => (p.1 : ZMod q) * (p.2 : ZMod q))
    hmaps (fun p => f ((p.1 : ZMod q) * (p.2 : ZMod q)))).symm
  simp_rw [Nat.cast_mul]
  rw [hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hconst : ∑ p ∈ ((smoothSet m_dil) ×ˢ (smoothSet m_dil)).filter
      (fun p => (p.1 : ZMod q) * (p.2 : ZMod q) = c), f ((p.1 : ZMod q) * (p.2 : ZMod q)) =
      ((((smoothSet m_dil) ×ˢ (smoothSet m_dil)).filter
        (fun p => (p.1 : ZMod q) * (p.2 : ZMod q) = c)).card : ℝ) * f c := by
    calc ∑ p ∈ ((smoothSet m_dil) ×ˢ (smoothSet m_dil)).filter
          (fun p => (p.1 : ZMod q) * (p.2 : ZMod q) = c), f ((p.1 : ZMod q) * (p.2 : ZMod q))
        = ∑ _p ∈ ((smoothSet m_dil) ×ˢ (smoothSet m_dil)).filter
          (fun p => (p.1 : ZMod q) * (p.2 : ZMod q) = c), f c := by
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [(Finset.mem_filter.mp hp).2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  unfold dilatorWeight
  ring

/-- **List-CRT 2-Factor Smooth Dilation Entropy-Gain Theorem:**
For any nodup list `l` of primes in `(14 * m_dil / 25, m_dil]` with `m_dil ≥ m1_pigeonhole`,
and independent `X, Y : PMF_ZMod l.prod`, the average entropy gain over `(c₁, c₂) ∈ smoothSet m_dil`
satisfies the coordinatewise lower bound with `max 0 (...)`. -/
theorem crt_list_dilation_entropy_gain (m_dil : ℕ) (hm : m1_pigeonhole ≤ m_dil) :
    ∀ (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) (hnd : l.Nodup)
      (_hband : ∀ q ∈ l, 14 * m_dil / 25 < q ∧ q ≤ m_dil)
      (X Y : @PMF_ZMod l.prod (list_prod_neZero hl)),
      ∑ i : Fin l.length,
        max 0 (((1 / 40 : ℝ) / (2420 * Real.log (l.get i : ℝ))) *
          (coordEnt l hl hnd Y i - 5 * Real.log (l.get i : ℝ) / (l.get i : ℝ)) *
          coordDeficit l hl hnd X i) ≤
      (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
        ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
          (@Hnat_zmod l.prod (list_prod_neZero hl)
              (@conv_dilate l.prod (list_prod_neZero hl) X Y ((c₁ * c₂ : ℕ) : ZMod l.prod)) -
            @Hnat_zmod l.prod (list_prod_neZero hl) X) := by
  intro l
  induction l with
  | nil =>
    intro hl hnd _hband X Y
    simp only [List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun c₁ _ => Finset.sum_nonneg fun c₂ _ => ?_)
    exact @Hnat_conv_dilate_sub_nonneg _ (list_prod_neZero hl) X Y _
  | cons q l' ih =>
    intro hl hnd hband X Y
    have hq_prime : q.Prime := hl q List.mem_cons_self
    have : Fact q.Prime := ⟨hq_prime⟩
    have : NeZero q := ⟨hq_prime.ne_zero⟩
    have : NeZero l'.prod := list_prod_neZero (fun p hp => hl p (List.mem_cons_of_mem q hp))
    have : NeZero (q * l'.prod) := list_prod_neZero hl
    have : NeZero (q :: l').prod := list_prod_neZero hl
    have hcop := head_coprime_tail_prod hl hnd
    have hq_band := hband q List.mem_cons_self
    have hstep_crt : ∀ c₁ c₂ : ℕ,
        (Hnat_zmod (conv_dilate (fstMarg hcop X) (fstMarg hcop Y) ((c₁ * c₂ : ℕ) : ZMod q)) -
          Hnat_zmod (fstMarg hcop X)) +
        ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
          (Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) ((c₁ * c₂ : ℕ) : ZMod l'.prod)) -
            Hnat_zmod (sndCond hcop X a)) ≤
        Hnat_zmod (conv_dilate X Y ((c₁ * c₂ : ℕ) : ZMod (q * l'.prod))) - Hnat_zmod X :=
      fun c₁ c₂ => Hnat_conv_dilate_crt_ge hcop X Y (c₁ * c₂)
    have hsum_crt := Finset.sum_le_sum fun c₁ (_ : c₁ ∈ smoothSet m_dil) =>
      Finset.sum_le_sum fun c₂ (_ : c₂ ∈ smoothSet m_dil) => hstep_crt c₁ c₂
    have hmul_crt := mul_le_mul_of_nonneg_left hsum_crt (by positivity : (0 : ℝ) ≤ 1 / ((smoothSet m_dil).card : ℝ) ^ 2)
    simp_rw [Finset.sum_add_distrib, mul_add] at hmul_crt
    -- Bound head term
    have hhead : max 0 (((1 / 40 : ℝ) / (2420 * Real.log (q : ℝ))) *
          (Hnat_zmod (fstMarg hcop Y) - 5 * Real.log (q : ℝ) / (q : ℝ)) *
          deficit_zmod (fstMarg hcop X)) ≤
        (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
          ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
            (Hnat_zmod (conv_dilate (fstMarg hcop X) (fstMarg hcop Y) ((c₁ * c₂ : ℕ) : ZMod q)) -
              Hnat_zmod (fstMarg hcop X)) := by
      rw [smooth_avg_eq_sum_dilatorWeight hq_band.1
        (fun c => Hnat_zmod (conv_dilate (fstMarg hcop X) (fstMarg hcop Y) c) - Hnat_zmod (fstMarg hcop X))]
      apply max_le
      · exact Finset.sum_nonneg fun c _ =>
          mul_nonneg (by unfold dilatorWeight; positivity) (Hnat_conv_dilate_sub_nonneg _ _ c)
      · exact two_factor_smooth_entropy_gain hm hq_band.1 hq_band.2 (fstMarg hcop X) (fstMarg hcop Y)
    -- Bound tail term using IH on each (a, b) and convexity of max 0 (·)
    have htail_ab : ∀ a b : ZMod q,
        ∑ j : Fin l'.length,
          max 0 (((1 / 40 : ℝ) / (2420 * Real.log (l'.get j : ℝ))) *
            (coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
              (sndCond hcop Y b) j - 5 * Real.log (l'.get j : ℝ) / (l'.get j : ℝ)) *
            coordDeficit l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
              (sndCond hcop X a) j) ≤
        (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
          ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
            (Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) ((c₁ * c₂ : ℕ) : ZMod l'.prod)) -
              Hnat_zmod (sndCond hcop X a)) :=
      fun a b => ih (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
        (fun p hp => hband p (List.mem_cons_of_mem q hp)) (sndCond hcop X a) (sndCond hcop Y b)
    have htail :
        ∑ j : Fin l'.length,
          max 0 (((1 / 40 : ℝ) / (2420 * Real.log (l'.get j : ℝ))) *
            ((∑ b : ZMod q, (fstMarg hcop Y).p b *
                coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop Y b) j) - 5 * Real.log (l'.get j : ℝ) / (l'.get j : ℝ)) *
            (∑ a : ZMod q, (fstMarg hcop X).p a *
                coordDeficit l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop X a) j)) ≤
        (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
          ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
            ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
              (Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) ((c₁ * c₂ : ℕ) : ZMod l'.prod)) -
                Hnat_zmod (sndCond hcop X a)) := by
      have hrhs_swap :
          (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
            ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
              ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
                (Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) ((c₁ * c₂ : ℕ) : ZMod l'.prod)) -
                  Hnat_zmod (sndCond hcop X a)) =
          ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
            ((1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
              ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
                (Hnat_zmod (conv_dilate (sndCond hcop X a) (sndCond hcop Y b) ((c₁ * c₂ : ℕ) : ZMod l'.prod)) -
                  Hnat_zmod (sndCond hcop X a))) := by
        rw [Finset.mul_sum]
        conv_lhs =>
          arg 2; ext c₁; rw [Finset.mul_sum]
          arg 2; ext c₂; rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_lhs =>
          arg 2; ext c₂; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs =>
          arg 2; ext c₂; arg 2; ext c₁; rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_lhs =>
          arg 2; ext c₁; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c₂ _ => by ring
      rw [hrhs_swap]
      have hsum_ab := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
        Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) =>
          mul_le_mul_of_nonneg_left (htail_ab a b)
            (mul_nonneg ((fstMarg hcop X).nonneg a) ((fstMarg hcop Y).nonneg b))
      refine le_trans ?_ hsum_ab
      -- Move ∑ j outside ∑ a ∑ b and apply subadditivity of max 0 (·)
      have hlhs_move :
          ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
            ∑ j : Fin l'.length,
              max 0 (((1 / 40 : ℝ) / (2420 * Real.log (l'.get j : ℝ))) *
                (coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop Y b) j - 5 * Real.log (l'.get j : ℝ) / (l'.get j : ℝ)) *
                coordDeficit l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop X a) j) =
          ∑ j : Fin l'.length, ∑ a : ZMod q, ∑ b : ZMod q,
            (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
              max 0 (((1 / 40 : ℝ) / (2420 * Real.log (l'.get j : ℝ))) *
                (coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop Y b) j - 5 * Real.log (l'.get j : ℝ) / (l'.get j : ℝ)) *
                coordDeficit l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop X a) j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => by rw [Finset.sum_comm]
      rw [hlhs_move]
      refine Finset.sum_le_sum fun j _ => ?_
      apply max_le
      · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
          mul_nonneg (mul_nonneg ((fstMarg hcop X).nonneg a) ((fstMarg hcop Y).nonneg b)) (le_max_left _ _)
      · have hbilin :
            ((1 / 40 : ℝ) / (2420 * Real.log (l'.get j : ℝ))) *
              ((∑ b : ZMod q, (fstMarg hcop Y).p b *
                  coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                    (sndCond hcop Y b) j) - 5 * Real.log (l'.get j : ℝ) / (l'.get j : ℝ)) *
              (∑ a : ZMod q, (fstMarg hcop X).p a *
                  coordDeficit l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                    (sndCond hcop X a) j) =
            ∑ a : ZMod q, ∑ b : ZMod q, (fstMarg hcop X).p a * (fstMarg hcop Y).p b *
              (((1 / 40 : ℝ) / (2420 * Real.log (l'.get j : ℝ))) *
                (coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop Y b) j - 5 * Real.log (l'.get j : ℝ) / (l'.get j : ℝ)) *
                coordDeficit l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop X a) j) := by
          have hsub_b :
              (∑ b : ZMod q, (fstMarg hcop Y).p b *
                coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop Y b) j) - 5 * Real.log (l'.get j : ℝ) / (l'.get j : ℝ) =
              ∑ b : ZMod q, (fstMarg hcop Y).p b *
                (coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp)) (List.nodup_cons.mp hnd).2
                  (sndCond hcop Y b) j - 5 * Real.log (l'.get j : ℝ) / (l'.get j : ℝ)) := by
            simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (fstMarg hcop Y).sum_one, one_mul]
          rw [hsub_b, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => by ring
        rw [hbilin]
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        exact mul_le_mul_of_nonneg_left (le_max_right _ _)
          (mul_nonneg ((fstMarg hcop X).nonneg a) ((fstMarg hcop Y).nonneg b))
    change ∑ i : Fin (l'.length + 1),
      max 0 (((1 / 40 : ℝ) / (2420 * Real.log ((q :: l').get i : ℝ))) *
        (coordEnt (q :: l') hl hnd Y i - 5 * Real.log ((q :: l').get i : ℝ) / ((q :: l').get i : ℝ)) *
        coordDeficit (q :: l') hl hnd X i) ≤ _
    rw [Fin.sum_univ_succ]
    dsimp [coordDeficit, coordEnt]
    exact (add_le_add hhead htail).trans hmul_crt


/-! ## Section 3A: `M_core`, 16-Subinterval Bertrand Prime Band, and Harmonic Sum -/

/-- Core smooth-plus-primorial divisor `M_core m ∣ m!` for `m ≥ 4096`. -/
def M_core (m : ℕ) : ℕ :=
  2 ^ (m / 4) * primorial m * (primorial (m / 3)) ^ 2 *
    (primorial (Nat.sqrt m)) ^ (2 * Nat.log 2 m)

lemma M_core_pos (m : ℕ) : 0 < M_core m := by
  unfold M_core
  exact mul_pos (mul_pos (mul_pos (by positivity) (primorial_pos m))
    (pow_pos (primorial_pos _) 2)) (pow_pos (primorial_pos _) _)

private lemma pow_div_dvd_factorial' (p m : ℕ) : p ^ (m / p) ∣ m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.succ_div]
    split_ifs with h
    · rw [_root_.pow_succ, mul_comm (p ^ (m / p)) p]
      exact mul_dvd_mul h ih
    · rw [add_zero]
      exact dvd_mul_of_dvd_right ih (m + 1)

private lemma primorial_factorization_le (n p : ℕ) :
    (primorial n).factorization p ≤ if p ≤ n then 1 else 0 := by
  by_cases hp : p.Prime
  · unfold primorial
    have hgen : ∀ S : Finset ℕ, (∀ r ∈ S, r.Prime) →
        (∏ r ∈ S, r).factorization p = if p ∈ S then 1 else 0 := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; simp
      | insert a s ha ih =>
        intro hS
        have hap : a.Prime := hS a (Finset.mem_insert_self a s)
        have hs_p : ∀ r ∈ s, r.Prime := fun r hr => hS r (Finset.mem_insert_of_mem hr)
        have hprod_ne : (∏ r ∈ s, r) ≠ 0 :=
          (Finset.prod_pos fun r hr => (hs_p r hr).pos).ne'
        rw [Finset.prod_insert ha, Nat.factorization_mul hap.ne_zero hprod_ne,
            Finsupp.add_apply, ih hs_p]
        by_cases hpa : p = a
        · subst hpa
          simp only [Finset.mem_insert_self, ite_true, ha, ite_false, add_zero]
          exact hp.factorization_self
        · have hfa : a.factorization p = 0 :=
            Nat.factorization_eq_zero_of_not_dvd
              (fun hd => hpa ((Nat.prime_dvd_prime_iff_eq hp hap).mp hd))
          rw [hfa, zero_add]
          simp [Finset.mem_insert, hpa]
    rw [hgen _ (fun r hr => (Finset.mem_filter.mp hr).2)]
    split_ifs with hmem hpn
    · exact le_rfl
    · simp only [Finset.mem_filter, Finset.mem_range] at hmem; omega
    · exact Nat.zero_le _
    · exact le_rfl
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

private lemma log2_bound_sqrt {m : ℕ} (hm : 4096 ≤ m) :
    4 * Nat.log 2 m + 6 ≤ Nat.sqrt m := by
  have hk_ge : 12 ≤ Nat.log 2 m := by
    have h1 : 2 ^ 12 ≤ m := by omega
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h1
  have hpow_le : 2 ^ (Nat.log 2 m) ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hsq : ∀ k : ℕ, 12 ≤ k → (4 * k + 6) ^ 2 ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have h1 : (4 * (k + 1) + 6) ^ 2 ≤ 2 * (4 * k + 6) ^ 2 := by nlinarith
      have h2 : 2 * (4 * k + 6) ^ 2 ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      have h3 : 2 * 2 ^ k = 2 ^ (k + 1) := (_root_.pow_succ' 2 k).symm
      omega
  have hle : (4 * Nat.log 2 m + 6) ^ 2 ≤ m := (hsq _ hk_ge).trans hpow_le
  exact Nat.le_sqrt.mpr (by nlinarith)

theorem M_core_dvd_factorial {m : ℕ} (hm : 4096 ≤ m) : M_core m ∣ m.factorial := by
  rw [← Nat.factorization_le_iff_dvd (M_core_pos m).ne' (Nat.factorial_ne_zero m)]
  intro p
  by_cases hp : p.Prime
  · have hdiv_le : m / p ≤ m.factorial.factorization p :=
      (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero m)).mp (pow_div_dvd_factorial' p m)
    have hsqrt := log2_bound_sqrt hm
    unfold M_core
    have h1ne : (2 ^ (m / 4) : ℕ) ≠ 0 := by positivity
    have h2ne : primorial m ≠ 0 := (primorial_pos m).ne'
    have h3ne : (primorial (m / 3)) ^ 2 ≠ 0 := (pow_pos (primorial_pos _) 2).ne'
    have h4ne : (primorial (Nat.sqrt m)) ^ (2 * Nat.log 2 m) ≠ 0 := (pow_pos (primorial_pos _) _).ne'
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero h1ne h2ne) h3ne) h4ne,
        Nat.factorization_mul (mul_ne_zero h1ne h2ne) h3ne,
        Nat.factorization_mul h1ne h2ne,
        Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have hf1 := primorial_factorization_le m p
    have hf2 := primorial_factorization_le (m / 3) p
    have hf3 := primorial_factorization_le (Nat.sqrt m) p
    have h2f : (2 : ℕ).factorization p = if p = 2 then 1 else 0 := by
      split_ifs with h
      · subst h; simp [Nat.Prime.factorization_self Nat.prime_two]
      · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => h ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
    rw [h2f]
    have hf3_mul : 2 * Nat.log 2 m * (primorial (Nat.sqrt m)).factorization p ≤ 2 * Nat.log 2 m := by
      have hle1 : (primorial (Nat.sqrt m)).factorization p ≤ 1 := by split_ifs at hf3 <;> omega
      calc 2 * Nat.log 2 m * (primorial (Nat.sqrt m)).factorization p
          ≤ 2 * Nat.log 2 m * 1 := Nat.mul_le_mul_left _ hle1
        _ = 2 * Nat.log 2 m := mul_one _
    by_cases hp2 : p = 2
    · subst hp2
      have hsq_le : Nat.sqrt m ≤ m / 2 := by
        have h1 : 2 * Nat.sqrt m ≤ Nat.sqrt m * Nat.sqrt m :=
          Nat.mul_le_mul_right _ (by omega : 2 ≤ Nat.sqrt m)
        have h2 : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
        omega
      split_ifs at hf1 hf2 hf3 ⊢ <;> omega
    · simp only [hp2, ite_false, mul_zero, zero_add]
      by_cases hps : p ≤ Nat.sqrt m
      · have hmp : Nat.sqrt m ≤ m / p := by
          rw [Nat.le_div_iff_mul_le hp.pos]
          have h1 : Nat.sqrt m * p ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul_left _ hps
          exact h1.trans (Nat.sqrt_le m)
        split_ifs at hf1 hf2 hf3 ⊢ <;> omega
      · simp only [hps, ite_false] at hf3
        have hf30 : (primorial (Nat.sqrt m)).factorization p = 0 := by omega
        rw [hf30, mul_zero, add_zero]
        by_cases hp3 : p ≤ m / 3
        · have hmp : 3 ≤ m / p := by rw [Nat.le_div_iff_mul_le hp.pos]; omega
          split_ifs at hf1 hf2 ⊢ <;> omega
        · simp only [hp3, ite_false] at hf2
          have hf20 : (primorial (m / 3)).factorization p = 0 := by omega
          rw [hf20, mul_zero, add_zero]
          by_cases hpm : p ≤ m
          · have hmp : 1 ≤ m / p := by rw [Nat.le_div_iff_mul_le hp.pos]; omega
            simp only [hpm, ite_true] at hf1; omega
          · simp only [hpm, ite_false] at hf1; omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; exact Nat.zero_le _

lemma primorial_dvd_primorial {a b : ℕ} (hab : a ≤ b) : primorial a ∣ primorial b := by
  unfold primorial
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

theorem M_core_mono_dvd {a b : ℕ} (hab : a ≤ b) : M_core a ∣ M_core b := by
  unfold M_core
  refine mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ?_ ?_) ?_) ?_
  · exact Nat.pow_dvd_pow 2 (Nat.div_le_div_right hab)
  · exact primorial_dvd_primorial hab
  · exact pow_dvd_pow_of_dvd (primorial_dvd_primorial (Nat.div_le_div_right hab)) 2
  · exact dvd_trans
      (pow_dvd_pow_of_dvd (primorial_dvd_primorial (Nat.sqrt_le_sqrt hab)) _)
      (Nat.pow_dvd_pow _ (Nat.mul_le_mul_left 2 (Nat.log_mono_right hab)))

theorem M_core_le_two_pow {m : ℕ} (hm : 4096 ≤ m) : M_core m ≤ 2 ^ (6 * m) := by
  unfold M_core
  have h1 : 2 ^ (m / 4) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : primorial m ≤ 2 ^ (2 * m) := by
    calc primorial m ≤ 4 ^ m := primorial_le_four_pow m
      _ = (2 ^ 2) ^ m := by norm_num
      _ = 2 ^ (2 * m) := by rw [← pow_mul]
  have h3 : (primorial (m / 3)) ^ 2 ≤ 2 ^ (2 * m) := by
    calc (primorial (m / 3)) ^ 2 ≤ (4 ^ (m / 3)) ^ 2 := Nat.pow_le_pow_left (primorial_le_four_pow _) 2
      _ = 2 ^ (4 * (m / 3)) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (primorial (Nat.sqrt m)) ^ (2 * Nat.log 2 m) ≤ 2 ^ m := by
    have hsq := log2_bound_sqrt hm
    have hmul_le : 4 * Nat.sqrt m * Nat.log 2 m ≤ m := by
      have h1 : 4 * Nat.log 2 m ≤ Nat.sqrt m := by omega
      have h2 : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
      nlinarith
    calc (primorial (Nat.sqrt m)) ^ (2 * Nat.log 2 m)
        ≤ (4 ^ Nat.sqrt m) ^ (2 * Nat.log 2 m) :=
          Nat.pow_le_pow_left (primorial_le_four_pow _) _
      _ = 2 ^ (4 * Nat.sqrt m * Nat.log 2 m) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hmul_le
  calc 2 ^ (m / 4) * primorial m * (primorial (m / 3)) ^ 2 * (primorial (Nat.sqrt m)) ^ (2 * Nat.log 2 m)
      ≤ 2 ^ m * 2 ^ (2 * m) * 2 ^ (2 * m) * 2 ^ m :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4
    _ = 2 ^ (6 * m) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf

/-- Harmonic sum bound: for `N ≥ 8` and `1 ≤ m' ≤ N / 2`,
`∑_{r=1}^{m'} 1 / (r * log(N / r)) ≤ log(log(N + 16)) + 4`. -/
theorem harmonic_choose_sum_le {N m' : ℕ} (hN : 8 ≤ N) (hm' : m' ≤ N / 2) :
    ∑ r ∈ Finset.Icc 1 m', (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) ≤
      Real.log (Real.log ((N : ℝ) + 16)) + 4 := by
  have hNr : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN_ge : (2 : ℝ) < Real.log (N : ℝ) := by
    have h1 : Real.exp 2 < 8 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      have he : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
      have : (Real.exp 1) ^ 2 < 2.72 ^ 2 := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
      linarith [show (2.72 : ℝ) ^ 2 < 8 by norm_num]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ < Real.log 8 := Real.log_lt_log (Real.exp_pos 2) h1
      _ ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hNr
  -- Split Icc 1 m' into {1}, Icc 2 K (where K = min m' (N / 3)), and Ioc K m'
  set K : ℕ := min m' (N / 3)
  have hterm_nn : ∀ r ∈ Finset.Icc 1 m', (0 : ℝ) ≤ 1 / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrm : r ≤ m' := (Finset.mem_Icc.mp hr).2
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hlog_pos : 0 < Real.log ((N : ℝ) / (r : ℝ)) := by
      apply Real.log_pos
      rw [one_lt_div hr_pos]
      have : 2 * r ≤ N := by omega
      have hcast : (2 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
      linarith
    positivity
  -- Bound the middle part Icc 2 K by telescoping -log(log(N/r))
  have hmid : ∑ r ∈ Finset.Icc 2 K, (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) ≤
      Real.log (Real.log (N : ℝ)) := by
    by_cases hK2 : K < 2
    · have hemp : Finset.Icc 2 K = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]
      exact Real.log_nonneg (by linarith)
    · push Not at hK2
      -- Pointwise MVT: for t ∈ [r - 1, r] with 2 ≤ r ≤ N / 3,
      -- d/dt (-log(log(N/t))) = 1 / (t * log(N/t)) ≥ 1 / (r * log(N/r)) since t * log(N/t) is increasing on [1, N/e]
      let F : ℝ → ℝ := fun t => -Real.log (Real.log ((N : ℝ) / t))
      have hstep : ∀ r ∈ Finset.Icc 2 K,
          (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) ≤ F (r : ℝ) - F ((r - 1 : ℕ) : ℝ) := by
        intro r hr
        have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
        have hrK : r ≤ K := (Finset.mem_Icc.mp hr).2
        have hr3 : 3 * r ≤ N := by have : K ≤ N / 3 := min_le_right _ _; omega
        have hcast_sub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
        rw [hcast_sub]
        have hlt : (r : ℝ) - 1 < (r : ℝ) := by linarith
        have hderiv : ∀ t ∈ Set.Icc ((r : ℝ) - 1) (r : ℝ),
            HasDerivAt F (1 / (t * Real.log ((N : ℝ) / t))) t := by
          intro t ht
          have ht1 : (1 : ℝ) ≤ t := by
            have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
            linarith [ht.1]
          have ht_pos : 0 < t := by linarith
          have hNt : (3 : ℝ) ≤ (N : ℝ) / t := by
            rw [le_div_iff₀ ht_pos]
            have : (3 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr3
            linarith [ht.2]
          have hlog_gt1 : (1 : ℝ) < Real.log ((N : ℝ) / t) := by
            have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
            calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
              _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
              _ ≤ Real.log ((N : ℝ) / t) := Real.log_le_log (by norm_num) hNt
          have hd_div : HasDerivAt (fun s : ℝ => (N : ℝ) / s) (-(N : ℝ) / t ^ 2) t := by
            have := (hasDerivAt_const t (N : ℝ)).div (hasDerivAt_id' t) ht_pos.ne'
            convert this using 1; ring
          have hd_log1 : HasDerivAt (fun s : ℝ => Real.log ((N : ℝ) / s)) (-1 / t) t := by
            have := hd_div.log (by positivity : (N : ℝ) / t ≠ 0)
            convert this using 1
            field_simp [ht_pos.ne', hNpos.ne']
          have hd_log2 : HasDerivAt (fun s : ℝ => Real.log (Real.log ((N : ℝ) / s)))
              ((-1 / t) / Real.log ((N : ℝ) / t)) t :=
            hd_log1.log (by linarith)
          convert hd_log2.neg using 1
          field_simp [ht_pos.ne', (by linarith : Real.log ((N : ℝ) / t) ≠ 0)]
        have hcont : ContinuousOn F (Set.Icc ((r : ℝ) - 1) (r : ℝ)) :=
          fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
        have hdiff : DifferentiableOn ℝ F (Set.Ioo ((r : ℝ) - 1) (r : ℝ)) :=
          fun t ht => (hderiv t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
        rcases exists_deriv_eq_slope F hlt hcont hdiff with ⟨c, hc, hslope⟩
        have hc_mem : c ∈ Set.Icc ((r : ℝ) - 1) (r : ℝ) := ⟨hc.1.le, hc.2.le⟩
        rw [(hderiv c hc_mem).deriv] at hslope
        have hFdiff : F (r : ℝ) - F ((r : ℝ) - 1) = 1 / (c * Real.log ((N : ℝ) / c)) := by
          have : (r : ℝ) - ((r : ℝ) - 1) = 1 := by ring
          rw [this, div_one] at hslope
          exact hslope.symm
        rw [hFdiff]
        -- Show c * log(N / c) ≤ r * log(N / r) since g(t) = t * log(N / t) has g'(t) = log(N / t) - 1 > 0 on [r-1, r]
        have hg_mono : MonotoneOn (fun t : ℝ => t * Real.log ((N : ℝ) / t)) (Set.Icc ((r : ℝ) - 1) (r : ℝ)) := by
          have hgd : ∀ t ∈ Set.Icc ((r : ℝ) - 1) (r : ℝ),
              HasDerivAt (fun s : ℝ => s * Real.log ((N : ℝ) / s)) (Real.log ((N : ℝ) / t) - 1) t := by
            intro t ht
            have ht1 : (1 : ℝ) ≤ t := by
              have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
              linarith [ht.1]
            have ht_pos : 0 < t := by linarith
            have hd_div : HasDerivAt (fun s : ℝ => (N : ℝ) / s) (-(N : ℝ) / t ^ 2) t := by
              have := (hasDerivAt_const t (N : ℝ)).div (hasDerivAt_id' t) ht_pos.ne'
              convert this using 1; ring
            have hd_log1 : HasDerivAt (fun s : ℝ => Real.log ((N : ℝ) / s)) (-1 / t) t := by
              have := hd_div.log (by positivity : (N : ℝ) / t ≠ 0)
              convert this using 1; field_simp [ht_pos.ne', hNpos.ne']
            have := (hasDerivAt_id' t).mul hd_log1
            convert this using 1
            field_simp [ht_pos.ne']; ring
          apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
          · exact fun t ht => (hgd t ht).continuousAt.continuousWithinAt
          · exact fun t ht => (hgd t (interior_subset ht)).differentiableAt.differentiableWithinAt
          · intro t ht
            have htm := interior_subset ht
            rw [(hgd t htm).deriv]
            have ht_pos : 0 < t := by
              have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
              linarith [htm.1]
            have hNt : (3 : ℝ) ≤ (N : ℝ) / t := by
              rw [le_div_iff₀ ht_pos]
              have : (3 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr3
              linarith [htm.2]
            have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
            have hlt1 : (1 : ℝ) < Real.log ((N : ℝ) / t) := by
              calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
                _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
                _ ≤ Real.log ((N : ℝ) / t) := Real.log_le_log (by norm_num) hNt
            linarith
        have hcle : c * Real.log ((N : ℝ) / c) ≤ (r : ℝ) * Real.log ((N : ℝ) / (r : ℝ)) :=
          hg_mono hc_mem ⟨hlt.le, le_rfl⟩ hc.2.le
        have hc_pos : 0 < c := by
          have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
          linarith [hc.1]
        have hlogc_pos : 0 < Real.log ((N : ℝ) / c) := by
          apply Real.log_pos; rw [one_lt_div hc_pos]
          have : (3 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr3
          linarith [hc.2]
        exact one_div_le_one_div_of_le (mul_pos hc_pos hlogc_pos) hcle
      have htele : ∀ n : ℕ, 2 ≤ n → ∑ r ∈ Finset.Icc 2 n, (F (r : ℝ) - F ((r - 1 : ℕ) : ℝ)) =
          F (n : ℝ) - F (1 : ℝ) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => simp
        | succ k hk ih =>
          have hsplit : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsplit, Finset.sum_insert (by simp), ih]
          simp only [Nat.add_sub_cancel]
          ring
      have htele := htele K hK2
      have hsum_le := (Finset.sum_le_sum hstep).trans_eq htele
      -- F(K) = -log(log(N/K)) ≤ 0 since N/K ≥ 3 > e, and -F(1) = log(log N)
      have hFK_nonpos : F (K : ℝ) ≤ 0 := by
        dsimp [F]
        have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
        have hNK : (3 : ℝ) ≤ (N : ℝ) / (K : ℝ) := by
          rw [le_div_iff₀ hK_pos]
          have : 3 * K ≤ N := by have : K ≤ N / 3 := min_le_right _ _; omega
          exact_mod_cast this
        have hlog1 : (1 : ℝ) ≤ Real.log ((N : ℝ) / (K : ℝ)) := by
          have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
          calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
            _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) he
            _ ≤ Real.log ((N : ℝ) / (K : ℝ)) := Real.log_le_log (by norm_num) hNK
        linarith [Real.log_nonneg hlog1]
      have hF1 : -F (1 : ℝ) = Real.log (Real.log (N : ℝ)) := by simp [F]
      linarith
  -- Bound the tail part Ioc K m' (each r > N/3, log(N/r) ≥ log 2, at most N/2 terms)
  have htail : ∑ r ∈ Finset.Ioc K m', (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) ≤ 3 := by
    by_cases hKm : m' ≤ K
    · have hemp : Finset.Ioc K m' = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]; norm_num
    · push Not at hKm
      have hK_eq : K = N / 3 := by
        dsimp [K] at hKm ⊢; omega
      have hterm : ∀ r ∈ Finset.Ioc K m',
          (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) ≤ 3 / ((N : ℝ) * Real.log 2) := by
        intro r hr
        have hr_gt : N / 3 < r := by rw [← hK_eq]; exact (Finset.mem_Ioc.mp hr).1
        have hr_le : r ≤ m' := (Finset.mem_Ioc.mp hr).2
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
        have h3r : (N : ℝ) ≤ 3 * (r : ℝ) := by exact_mod_cast (by omega : N ≤ 3 * r)
        have hlog2 : Real.log 2 ≤ Real.log ((N : ℝ) / (r : ℝ)) := by
          apply Real.log_le_log (by norm_num)
          rw [le_div_iff₀ hr_pos]
          have : 2 * r ≤ N := by omega
          exact_mod_cast this
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        rw [div_le_div_iff₀ (mul_pos hr_pos (lt_of_lt_of_le hlog2_pos hlog2)) (mul_pos hNpos hlog2_pos)]
        nlinarith
      have hsum_le := (Finset.sum_le_sum hterm).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul])
      have hcard : ((Finset.Ioc K m').card : ℝ) ≤ (N : ℝ) / 2 := by
        have hc : (Finset.Ioc K m').card ≤ N / 2 := by rw [Nat.card_Ioc]; omega
        have hcast : ((Finset.Ioc K m').card : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hc
        have hdiv : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
          have : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
          have : (2 : ℝ) * ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
          linarith
        exact hcast.trans hdiv
      have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hmul : ((Finset.Ioc K m').card : ℝ) * (3 / ((N : ℝ) * Real.log 2)) ≤
          ((N : ℝ) / 2) * (3 / ((N : ℝ) * Real.log 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      have hsimp : ((N : ℝ) / 2) * (3 / ((N : ℝ) * Real.log 2)) = 3 / (2 * Real.log 2) := by
        field_simp [hNpos.ne', (by linarith : Real.log 2 ≠ 0)]
      have h3 : 3 / (2 * Real.log 2) ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
  -- Combine {1} ∪ Icc 2 K ∪ Ioc K m'
  have h1_le : (1 : ℝ) / ((1 : ℝ) * Real.log ((N : ℝ) / (1 : ℝ))) ≤ 1 := by
    rw [one_mul, div_one, div_le_one (by linarith)]
    linarith
  have hsplit : Finset.Icc 1 m' ⊆ ({1} : Finset ℕ) ∪ (Finset.Icc 2 K ∪ Finset.Ioc K m') := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrm⟩
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum_split : ∑ r ∈ Finset.Icc 1 m', (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) ≤
      (1 : ℝ) / ((1 : ℝ) * Real.log ((N : ℝ) / (1 : ℝ))) +
      (∑ r ∈ Finset.Icc 2 K, (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ)))) +
      (∑ r ∈ Finset.Ioc K m', (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ)))) := by
    have hsub1 : ∀ r ∈ ({1} : Finset ℕ) ∪ (Finset.Icc 2 K ∪ Finset.Ioc K m'),
        (0 : ℝ) ≤ 1 / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) := by
      intro r hr
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc, Finset.mem_Ioc] at hr
      have hr1 : 1 ≤ r := by omega
      have hrm : r ≤ N / 2 := by
        have : K ≤ N / 2 := le_trans (min_le_left _ _) hm'
        omega
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      have hlog_pos : 0 < Real.log ((N : ℝ) / (r : ℝ)) := by
        apply Real.log_pos; rw [one_lt_div hr_pos]
        have : (2 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 * r ≤ N)
        linarith
      positivity
    have hle1 := Finset.sum_le_sum_of_subset_of_nonneg hsplit (fun r hr _ => hsub1 r hr)
    have hdisj1 : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 K ∪ Finset.Ioc K m') := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      simp only [Finset.mem_singleton] at hr1
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc] at hr2
      omega
    have hdisj2 : Disjoint (Finset.Icc 2 K) (Finset.Ioc K m') := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      simp only [Finset.mem_Icc] at hr1
      simp only [Finset.mem_Ioc] at hr2
      omega
    rw [Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_singleton, Nat.cast_one] at hle1
    linarith
  have hloglog_le : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log ((N : ℝ) + 16)) := by
    apply Real.log_le_log (by linarith)
    exact Real.log_le_log hNpos (by linarith)
  linarith


/-! ## Section 3B: Prime Band, Greedy Top-`r` Sets, Lemma 4, and Lemma 5 -/

/-- Prime pool `P(m) = {p prime : 2 ≤ p ≤ m / 8}` for `Z_r`. -/
def primePool (m : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (m / 8)).filter Nat.Prime

/-- 16-subinterval Bertrand band: using only `bertrand_quantitative` and `prime_counting_lower`,
there exist `c_band > 0` and `m_band ≥ max 4096 (2 * m1_pigeonhole)` such that for every `m ≥ m_band`,
there exist `m_dil` and disjoint `Q_strip, Q_tag` of primes in `(m/2, m]` with `14*m_dil/25 < q ≤ m_dil`,
`|Q_strip|, |Q_tag| ≥ c_band * m / log m`, `12 ≤ |Q_strip|`, and `|Q_strip| ≤ |primePool m| / 2`. -/
theorem exists_prime_band :
    ∃ (c_band : ℝ) (m_band : ℕ), 0 < c_band ∧ max 4096 (2 * m1_pigeonhole) ≤ m_band ∧
      ∀ m : ℕ, m_band ≤ m →
        ∃ (m_dil : ℕ) (Q_strip Q_tag : Finset ℕ),
          m1_pigeonhole ≤ m_dil ∧ m_dil ≤ m ∧
          Disjoint Q_strip Q_tag ∧
          (∀ q ∈ Q_strip ∪ Q_tag, q.Prime ∧ m / 2 < q ∧ 14 * m_dil / 25 < q ∧ q ≤ m_dil) ∧
          c_band * (m : ℝ) / Real.log (m : ℝ) ≤ (Q_strip.card : ℝ) ∧
          c_band * (m : ℝ) / Real.log (m : ℝ) ≤ (Q_tag.card : ℝ) ∧
          12 ≤ Q_strip.card ∧
          Q_strip.card ≤ (primePool m).card / 2 ∧
          8 ≤ (primePool m).card := by
  rcases bertrand_quantitative with ⟨cB, hcB, x0, hbert⟩
  rcases prime_counting_lower with ⟨c0, hc0, hpi⟩
  set c_band : ℝ := min (cB / 256) (c0 / 64)
  have hc_pos : 0 < c_band := by positivity
  -- Choose threshold m_band large enough so all linear/log inequalities hold
  -- Note: for m ≥ K, m / log m ≥ sqrt m ≥ ...
  have hexists_M : ∃ M : ℕ, max (max 4096 (2 * m1_pigeonhole)) (max (2 * x0 + 4) 100000) ≤ M ∧
      ∀ m : ℕ, M ≤ m →
        12 ≤ c_band * (m : ℝ) / Real.log (m : ℝ) ∧
        16 ≤ (c0 / 16) * (m : ℝ) / Real.log (m : ℝ) := by
    -- Since log m ≤ sqrt m for m ≥ 16, m / log m ≥ sqrt m
    -- Pick M so sqrt M ≥ max (12 / c_band + 1) (16 / (c0 / 16) + 1)
    set K : ℕ := Nat.ceil (max (12 / c_band) (256 / c0)) + 16
    refine ⟨max (max (max 4096 (2 * m1_pigeonhole)) (max (2 * x0 + 4) 100000)) (K ^ 2),
      le_max_left _ _, ?_⟩
    intro m hm
    have hm_ge : K ^ 2 ≤ m := le_trans (le_max_right _ _) hm
    have hm4096 : 4096 ≤ m := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm))
    have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    -- Real.log m ≤ Real.sqrt m (since log(sqrt m) ≤ sqrt m / 2 ⇒ 2 * log(sqrt m) ≤ sqrt m)
    have hlog_le_sqrt : Real.log (m : ℝ) ≤ Real.sqrt (m : ℝ) := by
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have h1 : Real.log (Real.sqrt (m : ℝ) / 2) ≤ Real.sqrt (m : ℝ) / 2 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (m : ℝ) = 2 * Real.log (Real.sqrt (m : ℝ)) := by
        rw [Real.log_sqrt hm_pos.le]; ring
      have h3 : Real.log (Real.sqrt (m : ℝ)) = Real.log (Real.sqrt (m : ℝ) / 2) + Real.log 2 := by
        rw [Real.log_div (Real.sqrt_pos.mpr hm_pos).ne' (by norm_num)]; ring
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hsqrt_ge : (K : ℝ) ≤ Real.sqrt (m : ℝ) := by
      have h1 : ((K : ℝ) ^ 2) ≤ (m : ℝ) := by exact_mod_cast hm_ge
      calc (K : ℝ) = Real.sqrt ((K : ℝ) ^ 2) := (Real.sqrt_sq (Nat.cast_nonneg K)).symm
        _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt h1
    have hdiv_ge : (K : ℝ) ≤ (m : ℝ) / Real.log (m : ℝ) := by
      rw [le_div_iff₀ hlog_pos]
      have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg m)
      have : (K : ℝ) * Real.log (m : ℝ) ≤ Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) :=
        mul_le_mul hsqrt_ge hlog_le_sqrt hlog_pos.le (Real.sqrt_nonneg _)
      linarith
    have hK1 : 12 / c_band ≤ (K : ℝ) := by
      have : 12 / c_band ≤ max (12 / c_band) (256 / c0) := le_max_left _ _
      have := le_trans this (Nat.le_ceil _)
      push_cast [K]; linarith
    have hK2 : 256 / c0 ≤ (K : ℝ) := by
      have : 256 / c0 ≤ max (12 / c_band) (256 / c0) := le_max_right _ _
      have := le_trans this (Nat.le_ceil _)
      push_cast [K]; linarith
    constructor
    · have h1 := mul_le_mul_of_nonneg_left (hK1.trans hdiv_ge) hc_pos.le
      rw [mul_div_cancel₀ _ hc_pos.ne'] at h1
      linarith [show c_band * ((m : ℝ) / Real.log (m : ℝ)) = c_band * (m : ℝ) / Real.log (m : ℝ) by ring]
    · have h1 := mul_le_mul_of_nonneg_left (hK2.trans hdiv_ge) (by positivity : (0 : ℝ) ≤ c0 / 16)
      have h2 : (c0 / 16) * (256 / c0) = 16 := by field_simp [hc0.ne']; norm_num
      rw [h2] at h1
      linarith [show (c0 / 16) * ((m : ℝ) / Real.log (m : ℝ)) = (c0 / 16) * (m : ℝ) / Real.log (m : ℝ) by ring]
  rcases hexists_M with ⟨m_band, hm_band_lo, hm_band_prop⟩
  refine ⟨c_band, m_band, hc_pos, le_trans (le_max_left _ _) hm_band_lo, ?_⟩
  intro m hm
  have hm4096 : 4096 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hm_band_lo.trans hm)
  have hm_pig : 2 * m1_pigeonhole ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hm_band_lo.trans hm)
  have hm_x0 : 2 * x0 + 4 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hm_band_lo.trans hm)
  have hm_log_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have ⟨h12_cb, h16_c0⟩ := hm_band_prop m hm
  -- Lower bound |primePool m| ≥ (c0 / 16) * m / log m ≥ 16
  have hpool_card : (c0 / 16) * (m : ℝ) / Real.log (m : ℝ) ≤ ((primePool m).card : ℝ) := by
    have h8 : 2 ≤ m / 8 := by omega
    have hpi8 := hpi (m / 8) h8
    have hpool_eq : (primePool m).card = Nat.primeCounting (m / 8) := by
      unfold primePool Nat.primeCounting Nat.primeCounting'
      rw [Nat.count_eq_card_filter_range]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      constructor
      · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨Nat.lt_succ_of_le h2, hp⟩
      · rintro ⟨h1, hp⟩; exact ⟨⟨hp.two_le, Nat.lt_succ_iff.mp h1⟩, hp⟩
    rw [hpool_eq]
    have hm8_ge : (m : ℝ) / 16 ≤ ((m / 8 : ℕ) : ℝ) := by
      have : m ≤ 8 * (m / 8) + 7 := by omega
      have hcast : (m : ℝ) ≤ 8 * ((m / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast this
      have hm_r : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
      linarith
    have hlog8_le : Real.log ((m / 8 : ℕ) : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (Nat.div_pos (le_trans (by norm_num) hm4096) (by norm_num))) (Nat.cast_le.mpr (Nat.div_le_self m 8))
    have hlog8_pos : 0 < Real.log ((m / 8 : ℕ) : ℝ) :=
      Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num) (Nat.div_le_div_right (c := 8) hm4096)))
    have hstep : (c0 / 16) * (m : ℝ) / Real.log (m : ℝ) ≤ c0 * ((m / 8 : ℕ) : ℝ) / Real.log ((m / 8 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ hm_log_pos hlog8_pos]
      have h1 : (c0 / 16) * (m : ℝ) ≤ c0 * ((m / 8 : ℕ) : ℝ) := by rw [div_mul_eq_mul_div, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hm8_ge hc0.le
      exact mul_le_mul h1 hlog8_le hlog8_pos.le (by positivity)
    exact hstep.trans hpi8
  have hpool_ge8 : 8 ≤ (primePool m).card := by
    have : (16 : ℝ) ≤ ((primePool m).card : ℝ) := h16_c0.trans hpool_card
    exact_mod_cast (by linarith : (8 : ℝ) ≤ ((primePool m).card : ℝ))
  -- Lower bound |P_hi| ≥ (cB / 4) * m / log m where P_hi = (Ioc (m / 2) m).filter Nat.Prime
  set P_hi : Finset ℕ := (Finset.Ioc (m / 2) m).filter Nat.Prime
  have hPhi_card : (cB / 4) * (m : ℝ) / Real.log (m : ℝ) ≤ (P_hi.card : ℝ) := by
    have hbert_m := hbert (m / 2) (by omega)
    have hodd_le : oddPrimeCounting (2 * (m / 2)) - oddPrimeCounting (m / 2) ≤ P_hi.card := by
      have hsub : ((Finset.range (2 * (m / 2) + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)) \
          ((Finset.range (m / 2 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)) ⊆ P_hi := by
        intro p hp
        rw [Finset.mem_sdiff] at hp
        simp only [Finset.mem_filter, Finset.mem_range, P_hi, Finset.mem_Ioc] at hp ⊢
        refine ⟨⟨?_, by omega⟩, hp.1.2.1⟩
        by_contra hle; exact hp.2 ⟨by omega, hp.1.2⟩
      have hinc : (Finset.range (m / 2 + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) ⊆
          (Finset.range (2 * (m / 2) + 1)).filter (fun p => p.Prime ∧ 3 ≤ p) := by
        intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
      have hcs := Finset.card_sdiff_add_card_eq_card hinc
      have hle := Finset.card_le_card hsub
      unfold oddPrimeCounting; omega
    have hcast_le : (oddPrimeCounting (2 * (m / 2)) : ℝ) - (oddPrimeCounting (m / 2) : ℝ) ≤ (P_hi.card : ℝ) := by
      have hmono : oddPrimeCounting (m / 2) ≤ oddPrimeCounting (2 * (m / 2)) := by
        unfold oddPrimeCounting
        apply Finset.card_le_card
        intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
      have : ((oddPrimeCounting (2 * (m / 2)) - oddPrimeCounting (m / 2) : ℕ) : ℝ) ≤ (P_hi.card : ℝ) :=
        by exact_mod_cast hodd_le
      rwa [Nat.cast_sub hmono] at this
    have hm2_ge : (m : ℝ) / 4 ≤ ((m / 2 : ℕ) : ℝ) := by
      have : m ≤ 2 * (m / 2) + 1 := by omega
      have hcast : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
      have hm_r : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
      linarith
    have hlog2_le : Real.log ((m / 2 : ℕ) : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (Nat.div_pos (le_trans (by norm_num) hm4096) (by norm_num))) (Nat.cast_le.mpr (Nat.div_le_self m 2))
    have hlog2_pos : 0 < Real.log ((m / 2 : ℕ) : ℝ) :=
      Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num) (Nat.div_le_div_right (c := 2) hm4096)))
    have hstep : (cB / 4) * (m : ℝ) / Real.log (m : ℝ) ≤ cB * ((m / 2 : ℕ) : ℝ) / Real.log ((m / 2 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ hm_log_pos hlog2_pos]
      have h1 : (cB / 4) * (m : ℝ) ≤ cB * ((m / 2 : ℕ) : ℝ) := by rw [div_mul_eq_mul_div, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hm2_ge hcB.le
      exact mul_le_mul h1 hlog2_le hlog2_pos.le (by positivity)
    exact hstep.trans (hbert_m.trans hcast_le)
  -- Partition P_hi into 16 sub-intervals Ioc (a j) (a (j+1))
  let a : ℕ → ℕ := fun j => m / 2 + j * (m - m / 2) / 16
  let B : ℕ → Finset ℕ := fun j => (Finset.Ioc (a j) (a (j + 1))).filter Nat.Prime
  have hcover : ∀ k : ℕ, k ≤ 16 →
      Finset.Ioc (a 0) (a k) ⊆ (Finset.range k).biUnion (fun j => Finset.Ioc (a j) (a (j + 1))) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      intro p hp
      rcases Finset.mem_Ioc.mp hp with ⟨hp0, hpk⟩
      rw [Finset.range_add_one, Finset.biUnion_insert]
      by_cases hle : p ≤ a k
      · exact Finset.mem_union_right _ (ih (by omega) (Finset.mem_Ioc.mpr ⟨hp0, hle⟩))
      · exact Finset.mem_union_left _ (Finset.mem_Ioc.mpr ⟨by omega, hpk⟩)
  have hPhi_sub : P_hi ⊆ (Finset.range 16).biUnion B := by
    intro p hp
    have hp_ioc : p ∈ Finset.Ioc (a 0) (a 16) := by
      have ha0 : a 0 = m / 2 := by simp [a]
      have ha16 : a 16 = m := by dsimp [a]; omega
      rw [ha0, ha16]; exact (Finset.mem_filter.mp hp).1
    rcases Finset.mem_biUnion.mp (hcover 16 le_rfl hp_ioc) with ⟨j, hj, hpj⟩
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hpj, (Finset.mem_filter.mp hp).2⟩⟩
  have hsum_ge : P_hi.card ≤ ∑ j ∈ Finset.range 16, (B j).card :=
    (Finset.card_le_card hPhi_sub).trans Finset.card_biUnion_le
  -- Pigeonhole: exists j < 16 with P_hi.card ≤ 16 * (B j).card
  have hex_j : ∃ j ∈ Finset.range 16, P_hi.card ≤ 16 * (B j).card := by
    by_contra hnone
    push Not at hnone
    have h16 : ∑ j ∈ Finset.range 16, (16 * (B j).card) < ∑ _j ∈ Finset.range 16, P_hi.card :=
      Finset.sum_lt_sum_of_nonempty (by simp) (fun j hj => hnone j hj)
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul] at h16
    omega
  rcases hex_j with ⟨j, hj, hBj_ge⟩
  have hj16 : j < 16 := Finset.mem_range.mp hj
  set m_dil : ℕ := a (j + 1)
  have hmdil_lo : m1_pigeonhole ≤ m_dil := by dsimp [m_dil, a]; omega
  have hmdil_hi : m_dil ≤ m := by
    dsimp [m_dil, a]
    have hmul : (j + 1) * (m - m / 2) ≤ 16 * (m - m / 2) := Nat.mul_le_mul_right _ (by omega)
    have hdiv : (j + 1) * (m - m / 2) / 16 ≤ m - m / 2 := by omega
    omega
  have haj_gt : 14 * m_dil / 25 < a j := by
    dsimp [m_dil, a]
    have hsplit : (j + 1) * (m - m / 2) = j * (m - m / 2) + (m - m / 2) := by ring
    have hdiv_le : (j + 1) * (m - m / 2) / 16 ≤ j * (m - m / 2) / 16 + (m - m / 2) / 16 + 1 := by
      rw [hsplit]; omega
    omega
  have hhalf_le : (B j).card / 2 ≤ (B j).card := Nat.div_le_self _ 2
  rcases Finset.exists_subset_card_eq hhalf_le with ⟨Q_strip₀, hQs0_sub, hQs0_card⟩
  set Q_tag : Finset ℕ := (B j) \ Q_strip₀
  have hQtag_card : (B j).card / 2 ≤ Q_tag.card := by
    have := Finset.card_sdiff_add_card_eq_card hQs0_sub
    dsimp [Q_tag]; omega
  -- Trim Q_strip₀ to size min Q_strip₀.card ((primePool m).card / 2)
  set target_card : ℕ := min Q_strip₀.card ((primePool m).card / 2)
  rcases Finset.exists_subset_card_eq (min_le_left Q_strip₀.card ((primePool m).card / 2)) with
    ⟨Q_strip, hQs_sub, hQs_card⟩
  refine ⟨m_dil, Q_strip, Q_tag, hmdil_lo, hmdil_hi, ?_, ?_, ?_, ?_, ?_, ?_, hpool_ge8⟩
  · -- Disjoint Q_strip Q_tag
    exact Disjoint.mono_left hQs_sub disjoint_sdiff_self_right
  · -- All q ∈ Q_strip ∪ Q_tag satisfy prime & band bounds
    intro q hq
    have hqB : q ∈ B j := by
      rcases Finset.mem_union.mp hq with h1 | h2
      · exact hQs0_sub (hQs_sub h1)
      · exact (Finset.mem_sdiff.mp h2).1
    have hqf := Finset.mem_filter.mp hqB
    have hqioc := Finset.mem_Ioc.mp hqf.1
    refine ⟨hqf.2, ?_, ?_, hqioc.2⟩
    · have : m / 2 ≤ a j := by dsimp [a]; omega
      omega
    · omega
  · -- c_band * m / log m ≤ Q_strip.card
    set X : ℝ := (m : ℝ) / Real.log (m : ℝ)
    have hX_nn : 0 ≤ X := by positivity
    have hBj_real : (cB / 64) * X ≤ ((B j).card : ℝ) := by
      have hcast : (P_hi.card : ℝ) ≤ 16 * ((B j).card : ℝ) := by exact_mod_cast hBj_ge
      have hPhi' : (cB / 4) * X ≤ (P_hi.card : ℝ) := by
        simpa [X, mul_div_assoc] using hPhi_card
      linarith
    have hcb1 : c_band * X ≤ (cB / 256) * X := mul_le_mul_of_nonneg_right (min_le_left _ _) hX_nn
    have hcb2 : c_band * X ≤ (c0 / 64) * X := mul_le_mul_of_nonneg_right (min_le_right _ _) hX_nn
    have h12X : (12 : ℝ) ≤ c_band * X := by simpa [X, mul_div_assoc] using h12_cb
    have hQs0_real : c_band * X ≤ (Q_strip₀.card : ℝ) := by
      rw [hQs0_card]
      have h2 : (B j).card ≤ 2 * ((B j).card / 2) + 1 := by omega
      have hcast : ((B j).card : ℝ) ≤ 2 * (((B j).card / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
      linarith
    have hpool_half : c_band * X ≤ (((primePool m).card / 2 : ℕ) : ℝ) := by
      have h2 : (primePool m).card ≤ 2 * ((primePool m).card / 2) + 1 := by omega
      have hcast : ((primePool m).card : ℝ) ≤ 2 * (((primePool m).card / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
      have hpool' : (c0 / 16) * X ≤ ((primePool m).card : ℝ) := by
        simpa [X, mul_div_assoc] using hpool_card
      linarith
    rw [hQs_card, Nat.cast_min]
    have hgoal : c_band * X ≤ min (Q_strip₀.card : ℝ) (((primePool m).card / 2 : ℕ) : ℝ) :=
      le_min hQs0_real hpool_half
    simpa [X, mul_div_assoc] using hgoal
  · -- c_band * m / log m ≤ Q_tag.card
    set X : ℝ := (m : ℝ) / Real.log (m : ℝ)
    have hX_nn : 0 ≤ X := by positivity
    have hBj_real : (cB / 64) * X ≤ ((B j).card : ℝ) := by
      have hcast : (P_hi.card : ℝ) ≤ 16 * ((B j).card : ℝ) := by exact_mod_cast hBj_ge
      have hPhi' : (cB / 4) * X ≤ (P_hi.card : ℝ) := by
        simpa [X, mul_div_assoc] using hPhi_card
      linarith
    have hcb1 : c_band * X ≤ (cB / 256) * X := mul_le_mul_of_nonneg_right (min_le_left _ _) hX_nn
    have h12X : (12 : ℝ) ≤ c_band * X := by simpa [X, mul_div_assoc] using h12_cb
    have h2 : (B j).card ≤ 2 * ((B j).card / 2) + 1 := by omega
    have hcast : ((B j).card : ℝ) ≤ 2 * (((B j).card / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    have hQt_r : (((B j).card / 2 : ℕ) : ℝ) ≤ (Q_tag.card : ℝ) := by exact_mod_cast hQtag_card
    have hgoal : c_band * X ≤ (Q_tag.card : ℝ) := by linarith
    simpa [X, mul_div_assoc] using hgoal
  · -- 12 ≤ Q_strip.card
    set X : ℝ := (m : ℝ) / Real.log (m : ℝ)
    have hX_nn : 0 ≤ X := by positivity
    have hBj_real : (cB / 64) * X ≤ ((B j).card : ℝ) := by
      have hcast : (P_hi.card : ℝ) ≤ 16 * ((B j).card : ℝ) := by exact_mod_cast hBj_ge
      have hPhi' : (cB / 4) * X ≤ (P_hi.card : ℝ) := by
        simpa [X, mul_div_assoc] using hPhi_card
      linarith
    have hcb1 : c_band * X ≤ (cB / 256) * X := mul_le_mul_of_nonneg_right (min_le_left _ _) hX_nn
    have hcb2 : c_band * X ≤ (c0 / 64) * X := mul_le_mul_of_nonneg_right (min_le_right _ _) hX_nn
    have h12X : (12 : ℝ) ≤ c_band * X := by simpa [X, mul_div_assoc] using h12_cb
    have hQs0_real : (12 : ℝ) ≤ (Q_strip₀.card : ℝ) := by
      rw [hQs0_card]
      have h2 : (B j).card ≤ 2 * ((B j).card / 2) + 1 := by omega
      have hcast : ((B j).card : ℝ) ≤ 2 * (((B j).card / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
      linarith
    have hpool_half : (12 : ℝ) ≤ (((primePool m).card / 2 : ℕ) : ℝ) := by
      have h2 : (primePool m).card ≤ 2 * ((primePool m).card / 2) + 1 := by omega
      have hcast : ((primePool m).card : ℝ) ≤ 2 * (((primePool m).card / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
      have hpool' : (c0 / 16) * X ≤ ((primePool m).card : ℝ) := by
        simpa [X, mul_div_assoc] using hpool_card
      linarith
    have hcb_r : (12 : ℝ) ≤ (Q_strip.card : ℝ) := by
      rw [hQs_card, Nat.cast_min]
      exact le_min hQs0_real hpool_half
    exact_mod_cast hcb_r
  · -- Q_strip.card ≤ (primePool m).card / 2
    rw [hQs_card]; exact min_le_right _ _

/-- Greedy top-`r` subsets of any finite set `U` for any function `δ : α → ℝ`:
for `k = U.card`, there exist `ord : ℕ → ℝ` and `S : ℕ → Finset α` such that
for every `r ∈ Icc 1 k`, `S r ⊆ U`, `(S r).card = r`, `∀ i ∈ S r, ord r ≤ δ i`,
and `∑ r ∈ Icc 1 k, ord r = ∑ i ∈ U, δ i`. -/
private lemma exists_greedy_top_sets {α : Type*} [DecidableEq α] (U : Finset α) (δ : α → ℝ) :
    ∃ (ord : ℕ → ℝ) (S : ℕ → Finset α),
      (∀ r ∈ Finset.Icc 1 U.card, S r ⊆ U ∧ (S r).card = r ∧ ∀ i ∈ S r, ord r ≤ δ i) ∧
      ∑ r ∈ Finset.Icc 1 U.card, ord r = ∑ i ∈ U, δ i := by
  induction hn : U.card generalizing U with
  | zero =>
    have hemp : U = ∅ := Finset.card_eq_zero.mp hn
    subst hemp
    exact ⟨fun _ => 0, fun _ => ∅, by simp, by simp⟩
  | succ k ih =>
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    rcases Finset.exists_min_image U δ hne with ⟨i₀, hi₀, hmin⟩
    have hcard_er : (U.erase i₀).card = k := by
      rw [Finset.card_erase_of_mem hi₀, hn]; omega
    rcases ih (U.erase i₀) hcard_er with ⟨ord', S', hS', hsum'⟩
    let ord : ℕ → ℝ := fun r => if r = k + 1 then δ i₀ else ord' r
    let S : ℕ → Finset α := fun r => if r = k + 1 then U else S' r
    refine ⟨ord, S, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_Icc.mp hr with ⟨hr1, hrk⟩
      by_cases htop : r = k + 1
      · subst htop
        simp only [S, ord, ite_true]
        exact ⟨subset_rfl, hn, fun i hi => hmin i hi⟩
      · simp only [S, ord, htop, ite_false]
        rcases hS' r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) with ⟨hsub, hcard, hle⟩
        exact ⟨hsub.trans (Finset.erase_subset i₀ U), hcard, hle⟩
    · have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have htop : ord (k + 1) = δ i₀ := by simp [ord]
      have hrest : ∑ r ∈ Finset.Icc 1 k, ord r = ∑ r ∈ Finset.Icc 1 k, ord' r := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hne_r : r ≠ k + 1 := by have := (Finset.mem_Icc.mp hr).2; omega
        simp [ord, hne_r]
      rw [htop, hrest, hsum', Finset.add_sum_erase U δ hi₀]

/-- Binomial lower bound: for `1 ≤ r ≤ N`, `((N : ℝ) / (r : ℝ)) ^ r ≤ (Nat.choose N r : ℝ)`. -/
private lemma div_pow_le_choose_real {N r : ℕ} (hr1 : 1 ≤ r) (hrN : r ≤ N) :
    ((N : ℝ) / (r : ℝ)) ^ r ≤ (Nat.choose N r : ℝ) := by
  -- Prove N^r ≤ r^r * choose N r by showing N^r * r! ≤ r^r * ∏_{i < r} (N - i)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  rw [div_pow, div_le_iff₀ (pow_pos hr_pos r)]
  suffices hnat : N ^ r ≤ (Nat.choose N r) * r ^ r by
    exact_mod_cast hnat
  have hdesc : Nat.choose N r * r.factorial = Nat.descFactorial N r := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  suffices hprod : N ^ r * r.factorial ≤ Nat.descFactorial N r * r ^ r by
    rw [← hdesc] at hprod
    have hfac_pos : 0 < r.factorial := Nat.factorial_pos r
    nlinarith
  -- Induction on k ≤ r: N^k * k! ≤ descFactorial N k * r^k? Better: ∏_{i < r} N * (r - i) ≤ ∏_{i < r} (N - i) * r
  have h1 : ∀ k : ℕ, k ≤ r → N ^ k * (∏ i ∈ Finset.range k, (r - i)) ≤
      (∏ i ∈ Finset.range k, (N - i)) * r ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, _root_.pow_succ, _root_.pow_succ]
      have hstep : N * (r - k) ≤ (N - k) * r := by
        have hk1 : k ≤ r := by omega
        have hk2 : k ≤ N := by omega
        zify [hk1, hk2]
        nlinarith
      have ih' := ih (by omega)
      calc N ^ k * N * ((∏ i ∈ Finset.range k, (r - i)) * (r - k))
          = (N ^ k * ∏ i ∈ Finset.range k, (r - i)) * (N * (r - k)) := by ring
        _ ≤ ((∏ i ∈ Finset.range k, (N - i)) * r ^ k) * ((N - k) * r) :=
            Nat.mul_le_mul ih' hstep
        _ = (∏ i ∈ Finset.range k, (N - i)) * (N - k) * (r ^ k * r) := by ring
  have hr_eq : ∏ i ∈ Finset.range r, (r - i) = r.factorial := by
    clear h1 hdesc hr1 hrN hr_pos
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.prod_range_succ', Nat.sub_zero, Nat.factorial_succ, mul_comm (r + 1)]
      congr 1
      have : ∀ i ∈ Finset.range r, r + 1 - (i + 1) = r - i := fun i _ => by omega
      rw [Finset.prod_congr rfl this, ih]
  have hdesc_eq : ∏ i ∈ Finset.range r, (N - i) = Nat.descFactorial N r :=
    (Nat.descFactorial_eq_prod_range N r).symm
  have hfinal := h1 r le_rfl
  rwa [hr_eq, hdesc_eq] at hfinal

/-- If `Y : PMF_ZMod l.prod` is supported on multiples of `l.get i` (mod `l.prod`), then `coordEnt l Y i = 0`. -/
private lemma coordEnt_eq_zero_of_dvd :
    ∀ (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) (hnd : l.Nodup)
      (Y : @PMF_ZMod l.prod (list_prod_neZero hl)) (i : Fin l.length),
      (∀ y : ZMod l.prod, @PMF_ZMod.p l.prod (list_prod_neZero hl) Y y ≠ 0 → l.get i ∣ y.val) →
      coordEnt l hl hnd Y i = 0
  | [], _, _, _, i, _ => Fin.elim0 i
  | q :: l', hl, hnd, Y, i, hdvd => by
    have : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
    have : NeZero l'.prod := list_prod_neZero (fun p hp => hl p (List.mem_cons_of_mem q hp))
    have : NeZero (q * l'.prod) := list_prod_neZero hl
    have : NeZero (q :: l').prod := list_prod_neZero hl
    set hcop := head_coprime_tail_prod hl hnd
    have hcrt_val : ∀ x : ZMod (q * l'.prod),
        ZMod.chineseRemainder hcop x = ((x.val : ZMod q), (x.val : ZMod l'.prod)) := by
      intro x
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      rw [map_natCast]
      rfl
    revert hdvd
    refine Fin.cases ?_ ?_ i
    · intro hdvd
      dsimp [coordEnt]
      have h0 : ∀ a : ZMod q, a ≠ 0 → (fstMarg hcop Y).p a = 0 := by
        intro a ha
        dsimp [fstMarg]
        apply Finset.sum_eq_zero
        intro b _
        by_contra hne
        have hq_dvd : q ∣ ((ZMod.chineseRemainder hcop).symm (a, b)).val := hdvd _ hne
        have hcast0 : (((ZMod.chineseRemainder hcop).symm (a, b)).val : ZMod q) = 0 :=
          (ZMod.natCast_eq_zero_iff _ q).mpr hq_dvd
        have hfst : (((ZMod.chineseRemainder hcop).symm (a, b)).val : ZMod q) = a := by
          have hinv := congrArg Prod.fst ((ZMod.chineseRemainder hcop).apply_symm_apply (a, b))
          rw [hcrt_val] at hinv
          exact hinv
        exact ha (hfst.symm.trans hcast0)
      have hp0 : (fstMarg hcop Y).p 0 = 1 := by
        have hs := (fstMarg hcop Y).sum_one
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))] at hs
        have hrest : ∑ a ∈ Finset.univ.erase (0 : ZMod q), (fstMarg hcop Y).p a = 0 :=
          Finset.sum_eq_zero fun a ha => h0 a (Finset.ne_of_mem_erase ha)
        linarith
      unfold Hnat_zmod
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), hp0]
      have hrest : ∑ a ∈ Finset.univ.erase (0 : ZMod q), Real.negMulLog ((fstMarg hcop Y).p a) = 0 :=
        Finset.sum_eq_zero fun a ha => by rw [h0 a (Finset.ne_of_mem_erase ha), Real.negMulLog_zero]
      rw [hrest, add_zero]; simp [Real.negMulLog]
    · intro j hdvd
      dsimp [coordEnt]
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : (fstMarg hcop Y).p b = 0
      · rw [hb, zero_mul]
      · suffices hzero : coordEnt l' (fun p hp => hl p (List.mem_cons_of_mem q hp))
            (List.nodup_cons.mp hnd).2 (sndCond hcop Y b) j = 0 by
          rw [hzero, mul_zero]
        apply coordEnt_eq_zero_of_dvd l' (fun p hp => hl p (List.mem_cons_of_mem q hp))
          (List.nodup_cons.mp hnd).2 (sndCond hcop Y b) j
        intro y₂ hy₂
        have hy_ne : Y.p ((ZMod.chineseRemainder hcop).symm (b, y₂)) ≠ 0 := by
          intro h0
          have := fstMarg_mul_sndCond hcop Y b y₂
          rw [h0] at this
          exact (mul_ne_zero hb hy₂) this
        have hlj_dvd : l'.get j ∣ ((ZMod.chineseRemainder hcop).symm (b, y₂)).val := hdvd _ hy_ne
        have hsnd : (((ZMod.chineseRemainder hcop).symm (b, y₂)).val : ZMod l'.prod) = y₂ := by
          have hinv := congrArg Prod.snd ((ZMod.chineseRemainder hcop).apply_symm_apply (b, y₂))
          rw [hcrt_val] at hinv
          exact hinv
        have hmod : y₂.val = ((ZMod.chineseRemainder hcop).symm (b, y₂)).val % l'.prod := by
          calc y₂.val = (((ZMod.chineseRemainder hcop).symm (b, y₂)).val : ZMod l'.prod).val :=
                congrArg ZMod.val hsnd.symm
            _ = ((ZMod.chineseRemainder hcop).symm (b, y₂)).val % l'.prod := ZMod.val_natCast _ _
        rw [hmod]
        exact (Nat.dvd_mod_iff (List.dvd_prod (List.get_mem l' j))).mpr hlj_dvd


/-! ## Section 3C: Lemma 4 (Adaptive Dilation Contraction) & Lemma 5 (Mod-`M'` Covering + Exact Digit Rep) -/

/-- Support of a `PMF_ZMod M`. -/
noncomputable def suppZMod {M : ℕ} [NeZero M] (μ : PMF_ZMod M) : Finset (ZMod M) := by
  classical
  exact Finset.univ.filter (fun x => μ.p x ≠ 0)

lemma Hnat_zmod_le_log_supp {M : ℕ} [NeZero M] (μ : PMF_ZMod M) :
    Hnat_zmod μ ≤ Real.log ((suppZMod μ).card : ℝ) := by
  classical
  have hne : (suppZMod μ).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h0 : ∀ x : ZMod M, μ.p x = 0 := by
      intro x
      have hx : x ∉ suppZMod μ := by rw [h]; simp
      simp only [suppZMod, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
      exact hx
    have := μ.sum_one
    simp [h0] at this
  have hcard_pos : (0 : ℝ) < ((suppZMod μ).card : ℝ) := Nat.cast_pos.mpr hne.card_pos
  have hsum_s : ∑ x ∈ suppZMod μ, μ.p x = 1 := by
    rw [← μ.sum_one]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [suppZMod, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
    exact hx
  have hH_s : Hnat_zmod μ = ∑ x ∈ suppZMod μ, Real.negMulLog (μ.p x) := by
    unfold Hnat_zmod
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [suppZMod, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
    rw [hx, Real.negMulLog_zero]
  rw [hH_s]
  have hdiff : ∑ x ∈ suppZMod μ, (Real.negMulLog (μ.p x) - μ.p x * Real.log ((suppZMod μ).card : ℝ)) ≤ 0 := by
    have hterm : ∀ x ∈ suppZMod μ,
        Real.negMulLog (μ.p x) - μ.p x * Real.log ((suppZMod μ).card : ℝ) ≤
          1 / ((suppZMod μ).card : ℝ) - μ.p x := by
      intro x hx
      have hne_x : μ.p x ≠ 0 := (Finset.mem_filter.mp hx).2
      have hpos_x : 0 < μ.p x := lt_of_le_of_ne (μ.nonneg x) (Ne.symm hne_x)
      have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / (μ.p x * ((suppZMod μ).card : ℝ)))
      have hmul := mul_le_mul_of_nonneg_left hlog hpos_x.le
      have hlhs : μ.p x * Real.log (1 / (μ.p x * ((suppZMod μ).card : ℝ))) =
          Real.negMulLog (μ.p x) - μ.p x * Real.log ((suppZMod μ).card : ℝ) := by
        rw [one_div, Real.log_inv, Real.log_mul hne_x hcard_pos.ne', Real.negMulLog]; ring
      have hrhs : μ.p x * (1 / (μ.p x * ((suppZMod μ).card : ℝ)) - 1) =
          1 / ((suppZMod μ).card : ℝ) - μ.p x := by
        field_simp [hne_x, hcard_pos.ne']
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsum_s,
        mul_one_div_cancel hcard_pos.ne', sub_self] at hsum
    rw [Finset.sum_sub_distrib]
    exact hsum
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_s, one_mul] at hdiff
  linarith

lemma Hnat_unifFinsetPMF {M : ℕ} [NeZero M] (T : Finset (ZMod M)) (hT : T.Nonempty) :
    Hnat_zmod (unifFinsetPMF T hT) = Real.log (T.card : ℝ) := by
  have hpos : (0 : ℝ) < (T.card : ℝ) := Nat.cast_pos.mpr hT.card_pos
  unfold Hnat_zmod unifFinsetPMF
  have hsum : ∑ x : ZMod M, Real.negMulLog (if x ∈ T then 1 / (T.card : ℝ) else 0) =
      ∑ x ∈ T, Real.negMulLog (1 / (T.card : ℝ)) := by
    symm
    calc ∑ x ∈ T, Real.negMulLog (1 / (T.card : ℝ))
        = ∑ x ∈ T, Real.negMulLog (if x ∈ T then 1 / (T.card : ℝ) else 0) :=
          Finset.sum_congr rfl fun x hx => by simp [hx]
      _ = ∑ x : ZMod M, Real.negMulLog (if x ∈ T then 1 / (T.card : ℝ) else 0) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro x _ hx; simp [hx, Real.negMulLog_zero]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, Real.negMulLog, one_div, Real.log_inv]
  field_simp [hpos.ne']

/-- Mixture of `c₁ * c₂ * Y₀` over `(c₁, c₂) ∈ smoothSet m_dil ×ˢ smoothSet m_dil`. -/
noncomputable def mixDilate {M : ℕ} [NeZero M] (m_dil : ℕ) (hA : (smoothSet m_dil).Nonempty)
    (Y₀ : PMF_ZMod M) : PMF_ZMod M where
  p z := (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
    ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
      (conv_dilate (pointPMF (0 : ZMod M)) Y₀ ((c₁ * c₂ : ℕ) : ZMod M)).p z
  nonneg z := mul_nonneg (by positivity) (Finset.sum_nonneg fun c₁ _ =>
    Finset.sum_nonneg fun c₂ _ => (conv_dilate _ _ _).nonneg z)
  sum_one := by
    have hA_ne : ((smoothSet m_dil).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.card_pos.ne'
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h1 : ∀ c₁ ∈ smoothSet m_dil,
        ∑ z : ZMod M, ∑ c₂ ∈ smoothSet m_dil,
          (conv_dilate (pointPMF (0 : ZMod M)) Y₀ ((c₁ * c₂ : ℕ) : ZMod M)).p z =
        ((smoothSet m_dil).card : ℝ) := by
      intro c₁ _
      rw [Finset.sum_comm]
      have h2 : ∀ c₂ ∈ smoothSet m_dil,
          ∑ z : ZMod M, (conv_dilate (pointPMF (0 : ZMod M)) Y₀ ((c₁ * c₂ : ℕ) : ZMod M)).p z = 1 :=
        fun c₂ _ => (conv_dilate _ _ _).sum_one
      rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    field_simp [hA_ne]

lemma conv_zmod_mixDilate_p {M : ℕ} [NeZero M] (m_dil : ℕ) (hA : (smoothSet m_dil).Nonempty)
    (X Y₀ : PMF_ZMod M) (x : ZMod M) :
    (conv_zmod X (mixDilate m_dil hA Y₀)).p x =
      (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
        ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
          (conv_dilate X Y₀ ((c₁ * c₂ : ℕ) : ZMod M)).p x := by
  dsimp [conv_zmod, conv_dilate, mixDilate, pointPMF]
  simp_rw [one_mul]
  have h1 : ∀ y : ZMod M,
      X.p (x - y) * ((1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
        ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
          ∑ z : ZMod M, (if y - ((c₁ * c₂ : ℕ) : ZMod M) * z = 0 then (1 : ℝ) else 0) * Y₀.p z) =
      (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
        ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
          ∑ z : ZMod M, if y = ((c₁ * c₂ : ℕ) : ZMod M) * z then X.p (x - y) * Y₀.p z else 0 := by
    intro y
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c₂ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : y = ((c₁ * c₂ : ℕ) : ZMod M) * z
    · simp [h]
    · have h' : y - ((c₁ * c₂ : ℕ) : ZMod M) * z ≠ 0 := sub_ne_zero.mpr h
      simp only [h, h', ite_false, zero_mul, mul_zero]
  simp_rw [h1, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => by simp

lemma Hnat_conv_mixDilate_ge {M : ℕ} [NeZero M] (m_dil : ℕ) (hA : (smoothSet m_dil).Nonempty)
    (X Y₀ : PMF_ZMod M) :
    (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
      ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
        (Hnat_zmod (conv_dilate X Y₀ ((c₁ * c₂ : ℕ) : ZMod M)) - Hnat_zmod X) ≤
      Hnat_zmod (conv_zmod X (mixDilate m_dil hA Y₀)) - Hnat_zmod X := by
  have hA_ne : ((smoothSet m_dil).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.card_pos.ne'
  have havg_X : (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
      ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil, Hnat_zmod X = Hnat_zmod X := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp [hA_ne]
  simp_rw [Finset.sum_sub_distrib, mul_sub]
  rw [havg_X]
  suffices hconc :
      (1 / ((smoothSet m_dil).card : ℝ) ^ 2) *
        ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
          Hnat_zmod (conv_dilate X Y₀ ((c₁ * c₂ : ℕ) : ZMod M)) ≤
        Hnat_zmod (conv_zmod X (mixDilate m_dil hA Y₀)) by linarith
  unfold Hnat_zmod
  rw [Finset.mul_sum]
  conv_lhs =>
    arg 2; ext c₁; rw [Finset.mul_sum]
    arg 2; ext c₂; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c₂; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  have hw_sum : ∑ p ∈ (smoothSet m_dil) ×ˢ (smoothSet m_dil),
      (1 / ((smoothSet m_dil).card : ℝ) ^ 2) = 1 := by
    rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
    field_simp [hA_ne]
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := (smoothSet m_dil) ×ˢ (smoothSet m_dil))
    (w := fun _ => 1 / ((smoothSet m_dil).card : ℝ) ^ 2)
    (p := fun p => (conv_dilate X Y₀ ((p.1 * p.2 : ℕ) : ZMod M)).p x)
    (fun _ _ => by positivity) hw_sum (fun p _ => (conv_dilate _ _ _).nonneg x)
  simp only [smul_eq_mul] at hj
  simp_rw [Finset.sum_product] at hj
  simp_rw [← Finset.mul_sum] at hj
  rw [← conv_zmod_mixDilate_p m_dil hA X Y₀ x] at hj
  refine le_trans (le_of_eq ?_) hj
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm]


/-- Factorization of a product of distinct primes. -/
private lemma prod_primes_factorization {A : Finset ℕ} (hA : ∀ r ∈ A, r.Prime) (p : ℕ) :
    (∏ r ∈ A, r).factorization p = if p ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hap : a.Prime := hA a (Finset.mem_insert_self a s)
    have hs_p : ∀ r ∈ s, r.Prime := fun r hr => hA r (Finset.mem_insert_of_mem hr)
    have hprod_ne : (∏ r ∈ s, r) ≠ 0 := (Finset.prod_pos fun r hr => (hs_p r hr).pos).ne'
    rw [Finset.prod_insert ha, Nat.factorization_mul hap.ne_zero hprod_ne, Finsupp.add_apply, ih hs_p]
    by_cases hpa : p = a
    · subst hpa
      simp only [Finset.mem_insert_self, ite_true, ha, ite_false, add_zero]
      exact hap.factorization_self
    · have hfa : a.factorization p = 0 := by
        by_cases hp : p.Prime
        · exact Nat.factorization_eq_zero_of_not_dvd
            (fun hd => hpa ((Nat.prime_dvd_prime_iff_eq hp hap).mp hd))
        · exact Nat.factorization_eq_zero_of_not_prime a hp
      rw [hfa, zero_add]
      simp [Finset.mem_insert, hpa]

/-- Unique factorization: `A ↦ ∏ p ∈ A, p` is injective on subsets of `primePool m`. -/
private lemma prime_prod_injOn (m r : ℕ) :
    Set.InjOn (fun A : Finset ℕ => ∏ p ∈ A, p) ((primePool m).powersetCard r : Set (Finset ℕ)) := by
  intro A hA B hB hprod
  have hAp : ∀ p ∈ A, p.Prime := fun p hp =>
    (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hA).1 hp)).2
  have hBp : ∀ p ∈ B, p.Prime := fun p hp =>
    (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hB).1 hp)).2
  ext p
  have hf := congrArg (fun n : ℕ => n.factorization p) hprod
  rw [prod_primes_factorization hAp p, prod_primes_factorization hBp p] at hf
  by_cases hpA : p ∈ A <;> by_cases hpB : p ∈ B <;> simp [hpA, hpB] at hf ⊢

/-- Helper: every prime `p ≤ n` has `(primorial n).factorization p = 1`. -/
private lemma primorial_factorization_eq_one {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    (primorial n).factorization p = 1 := by
  unfold primorial
  rw [prod_primes_factorization (fun r hr => (Finset.mem_filter.mp hr).2) p]
  have hmem : p ∈ (Finset.range (n + 1)).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpn), hp⟩
  simp [hmem]

/-- Helper: for `c ∈ smoothSet m_dil` (`m_dil ≤ m`), `c.factorization p` is bounded cleanly. -/
private lemma smoothSet_factorization_le {m m_dil c p : ℕ} (hm_dil : m_dil ≤ m)
    (hc : c ∈ smoothSet m_dil) (hp : p.Prime) :
    c.factorization p ≤ (if p ≤ Nat.sqrt m then Nat.log 2 m else if p ≤ m / 3 then 1 else 0) := by
  by_cases hd : p ∣ c
  · have hp_le_B : p ≤ 7 * m_dil / 25 := smoothSet_prime_dvd_le hc hp hd
    have hp_le_m3 : p ≤ m / 3 := by omega
    have hpow_le : p ^ (c.factorization p) ≤ m := by
      have hdvd : p ^ (c.factorization p) ∣ c := Nat.ordProj_dvd c p
      exact (Nat.le_of_dvd (smoothSet_pos hc) hdvd).trans (by have := smoothSet_le hc; omega)
    by_cases hps : p ≤ Nat.sqrt m
    · simp only [hps, ite_true]
      have h2pow : 2 ^ (c.factorization p) ≤ m :=
        (Nat.pow_le_pow_left hp.two_le _).trans hpow_le
      exact (Nat.le_log_iff_pow_le (by norm_num) (by have := smoothSet_pos hc; have := smoothSet_le hc; omega)).mpr h2pow
    · simp only [hps, ite_false, hp_le_m3, ite_true]
      by_contra hgt
      push Not at hgt
      have h2 : p ^ 2 ≤ m := (Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ c.factorization p)).trans hpow_le
      have hle_sqrt : p ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by rwa [← pow_two])
      exact hps hle_sqrt
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]
    exact Nat.zero_le _

/-- Every Lemma 4 divisor `d = p_tag * c₁ * c₂ * M_comp * ∏ A` divides `M_core m`. -/
private lemma lemma4_term_dvd_M_core {m m_dil p_tag c₁ c₂ : ℕ} {Q_comp A : Finset ℕ}
    (hm : 4096 ≤ m) (hm_dil : m_dil ≤ m)
    (hp_tag : p_tag.Prime ∧ m / 2 < p_tag ∧ p_tag ≤ m)
    (hc₁ : c₁ ∈ smoothSet m_dil) (hc₂ : c₂ ∈ smoothSet m_dil)
    (hQ : ∀ q ∈ Q_comp, q.Prime ∧ m / 2 < q ∧ q ≤ m)
    (hdisj : p_tag ∉ Q_comp)
    (hA : A ⊆ primePool m) :
    p_tag * c₁ * c₂ * (∏ q ∈ Q_comp, q) * (∏ p ∈ A, p) ∣ M_core m := by
  have hAp : ∀ p ∈ A, p.Prime := fun p hp => (Finset.mem_filter.mp (hA hp)).2
  have hne_pt : p_tag ≠ 0 := hp_tag.1.ne_zero
  have hne_c1 : c₁ ≠ 0 := (smoothSet_pos hc₁).ne'
  have hne_c2 : c₂ ≠ 0 := (smoothSet_pos hc₂).ne'
  have hne_Q : (∏ q ∈ Q_comp, q) ≠ 0 := (Finset.prod_pos fun q hq => (hQ q hq).1.pos).ne'
  have hne_A : (∏ p ∈ A, p) ≠ 0 := (Finset.prod_pos fun p hp => (hAp p hp).pos).ne'
  rw [← Nat.factorization_le_iff_dvd
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hne_pt hne_c1) hne_c2) hne_Q) hne_A)
    (M_core_pos m).ne']
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hne_pt hne_c1) hne_c2) hne_Q) hne_A,
        Nat.factorization_mul (mul_ne_zero (mul_ne_zero hne_pt hne_c1) hne_c2) hne_Q,
        Nat.factorization_mul (mul_ne_zero hne_pt hne_c1) hne_c2,
        Nat.factorization_mul hne_pt hne_c1]
    simp only [Finsupp.add_apply]
    unfold M_core
    have h1ne : (2 ^ (m / 4) : ℕ) ≠ 0 := by positivity
    have h2ne : primorial m ≠ 0 := (primorial_pos m).ne'
    have h3ne : (primorial (m / 3)) ^ 2 ≠ 0 := (pow_pos (primorial_pos _) 2).ne'
    have h4ne : (primorial (Nat.sqrt m)) ^ (2 * Nat.log 2 m) ≠ 0 := (pow_pos (primorial_pos _) _).ne'
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero h1ne h2ne) h3ne) h4ne,
        Nat.factorization_mul (mul_ne_zero h1ne h2ne) h3ne,
        Nat.factorization_mul h1ne h2ne,
        Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have hf_pt : p_tag.factorization p = if p = p_tag then 1 else 0 := by
      split_ifs with heq
      · subst heq; exact hp.factorization_self
      · exact Nat.factorization_eq_zero_of_not_dvd
          (fun hd => heq ((Nat.prime_dvd_prime_iff_eq hp hp_tag.1).mp hd))
    have hf_Q : (∏ q ∈ Q_comp, q).factorization p = if p ∈ Q_comp then 1 else 0 :=
      prod_primes_factorization (fun q hq => (hQ q hq).1) p
    have hf_A : (∏ r ∈ A, r).factorization p = if p ∈ A then 1 else 0 :=
      prod_primes_factorization hAp p
    have hf_c1 := smoothSet_factorization_le hm_dil hc₁ hp
    have hf_c2 := smoothSet_factorization_le hm_dil hc₂ hp
    rw [hf_pt, hf_Q, hf_A]
    by_cases hpm : p ≤ m
    · have hpm1 := primorial_factorization_eq_one hp hpm
      by_cases hp_hi : m / 2 < p
      · have hnot_s : ¬ (p ≤ Nat.sqrt m) := by
          have : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
          have : Nat.sqrt m ≤ m / 2 := by
            have h2 : 2 ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
            have : 2 * Nat.sqrt m ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul_right _ h2
            omega
          omega
        have hnot_3 : ¬ (p ≤ m / 3) := by omega
        have hnot_A : p ∉ A := by
          intro hmem
          have : p ≤ m / 8 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hA hmem)).1).2
          omega
        simp only [hnot_s, hnot_3, hnot_A, ite_false] at hf_c1 hf_c2 ⊢
        split_ifs with heq hmemQ
        · subst heq; exact absurd hmemQ hdisj
        · omega
        · omega
        · omega
      · -- p ≤ m / 2: so p ≠ p_tag and p ∉ Q_comp
        have hne_pt' : p ≠ p_tag := by omega
        have hnot_Q : p ∉ Q_comp := fun hmem => by have := (hQ p hmem).2.1; omega
        simp only [hne_pt', hnot_Q, ite_false]
        by_cases hps : p ≤ Nat.sqrt m
        · have hp3 : p ≤ m / 3 := by
            have h2 : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
            have h3 : 3 ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
            have : 3 * Nat.sqrt m ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul_right _ h3
            omega
          have hps1 := primorial_factorization_eq_one hp hps
          have hp31 := primorial_factorization_eq_one hp hp3
          simp only [hps, ite_true] at hf_c1 hf_c2
          rw [hpm1, hp31, hps1, mul_one, mul_one]
          split_ifs <;> omega
        · by_cases hp3 : p ≤ m / 3
          · have hp31 := primorial_factorization_eq_one hp hp3
            simp only [hps, ite_false, hp3, ite_true] at hf_c1 hf_c2
            rw [hpm1, hp31, mul_one]
            split_ifs <;> omega
          · have hnot_A : p ∉ A := by
              intro hmem
              have : p ≤ m / 8 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hA hmem)).1).2
              omega
            simp only [hps, hp3, hnot_A, ite_false] at hf_c1 hf_c2 ⊢
            omega
    · -- p > m: zero on LHS
      have hne_pt' : p ≠ p_tag := by omega
      have hnot_Q : p ∉ Q_comp := fun hmem => by have := (hQ p hmem).2.2; omega
      have hnot_A : p ∉ A := fun hmem => by
        have : p ≤ m / 8 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hA hmem)).1).2; omega
      have hnot_s : ¬ (p ≤ Nat.sqrt m) := by have := Nat.sqrt_le_self m; omega
      have hnot_3 : ¬ (p ≤ m / 3) := by omega
      simp only [hne_pt', hnot_Q, hnot_A, hnot_s, hnot_3, ite_false] at hf_c1 hf_c2 ⊢
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; exact Nat.zero_le _

private lemma margin_bound_4096 {m : ℕ} (hm4096 : 4096 ≤ m) :
    (10 : ℝ) / (96800 * (m : ℝ)) ≤
      1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hlog16_pos : 0 < Real.log ((m : ℝ) + 16) := Real.log_pos (by linarith)
  have hll_pos : 0 < Real.log (Real.log ((m : ℝ) + 16)) + 4 := by
    have : 1 ≤ Real.log ((m : ℝ) + 16) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ((m : ℝ) + 16) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith [Real.log_nonneg this]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set t : ℝ := Real.sqrt (Real.sqrt (m : ℝ))
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hm_pos)
  have ht_ge8 : (8 : ℝ) ≤ t := by
    have hsq1 : (64 : ℝ) ≤ Real.sqrt (m : ℝ) := by
      calc (64 : ℝ) = Real.sqrt (64 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by linarith)
    calc (8 : ℝ) = Real.sqrt (8 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ t := Real.sqrt_le_sqrt (by linarith)
  have ht4 : t ^ 4 = (m : ℝ) := by
    have h1 : t ^ 2 = Real.sqrt (m : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (m : ℝ)) ^ 2 := by rw [h1]
      _ = (m : ℝ) := Real.sq_sqrt hm_pos.le
  have hlog4 : Real.log (4 : ℝ) < 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; linarith [Real.log_two_lt_d9]
  have hlogm_t : Real.log (m : ℝ) ≤ t + 2 := by
    have h1 : Real.log (t / 4) ≤ t / 4 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlogt : Real.log t = Real.log (t / 4) + Real.log 4 := by
      rw [Real.log_div ht_pos.ne' (by norm_num)]; ring
    have h2 : Real.log (m : ℝ) = 4 * Real.log t := by rw [← ht4, Real.log_pow]; ring
    linarith
  have hll_le : Real.log (Real.log ((m : ℝ) + 16)) + 4 ≤ t := by
    have hm16 : (m : ℝ) + 16 ≤ 2 * (m : ℝ) := by linarith
    have hlog_m16 : Real.log ((m : ℝ) + 16) ≤ t + 3 := by
      have h1 := Real.log_le_log (by positivity) hm16
      rw [Real.log_mul (by norm_num) hm_pos.ne'] at h1
      linarith [Real.log_two_lt_d9]
    have hdiv4 : Real.log ((t + 3) / 4) ≤ (t + 3) / 4 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hlog_t3 : Real.log (t + 3) ≤ (t + 3) / 4 + 0.4 := by
      have : Real.log (t + 3) = Real.log ((t + 3) / 4) + Real.log 4 := by
        rw [Real.log_div (by positivity) (by norm_num)]; ring
      linarith
    have hle2 := Real.log_le_log hlog16_pos hlog_m16
    linarith
  have hprod_le : 20 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) ≤ (m : ℝ) := by
    have h1 : 20 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) ≤ 20 * (t + 2) * t :=
      mul_le_mul (by linarith) hll_le hll_pos.le (by positivity)
    have h2 : 20 * (t + 2) * t ≤ t ^ 4 := by
      have hsq : (64 : ℝ) ≤ t ^ 2 := by nlinarith
      have h25 : 20 * (t + 2) * t ≤ 25 * t ^ 2 := by nlinarith
      have h64 : 25 * t ^ 2 ≤ t ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
      linarith [show t ^ 2 * t ^ 2 = t ^ 4 by ring]
    linarith
  nlinarith

/-- **Lemma 4 (Adaptive Top-`r` Dilation Contraction on `ZMod M'`):**
For any `m ≥ m_band` with `(m_dil, Q_strip, Q_tag)` from `exists_prime_band`, any nonempty
`Q' ⊆ Q_strip` (`M' = ∏ q ∈ Q', q`), any `X : PMF_ZMod M'`, and any tag prime `p_tag ∈ Q_tag`,
there exists a PMF `Y : PMF_ZMod M'` supported on residues of positive divisors `d ∣ M_core m`
with `¬ (M' ∣ d)`, `d < m ^ 3 * M'`, `p_tag ∣ d`, and unique prime factor `p_tag` in `Q_tag`,
satisfying `Hnat(X + Y) - Hnat(X) ≥ (1 / (193600 * log m * (log log (m + 16) + 4))) * deficit(X)`. -/
theorem adaptive_dilation_contraction {m m_dil : ℕ} {Q_strip Q_tag Q' : Finset ℕ}
    (hm4096 : 4096 ≤ m) (hmdil_lo : m1_pigeonhole ≤ m_dil) (hmdil_hi : m_dil ≤ m)
    (hdisj_band : Disjoint Q_strip Q_tag)
    (hband : ∀ q ∈ Q_strip ∪ Q_tag, q.Prime ∧ m / 2 < q ∧ 14 * m_dil / 25 < q ∧ q ≤ m_dil)
    (hQ'_sub : Q' ⊆ Q_strip) (hQ'_ne : Q'.Nonempty)
    (hQ'_le : Q'.card ≤ (primePool m).card / 2) (hpool_ge8 : 8 ≤ (primePool m).card)
    {p_tag : ℕ} (hp_tag_mem : p_tag ∈ Q_tag)
    [NeZero (∏ q ∈ Q', q)]
    (X : PMF_ZMod (∏ q ∈ Q', q)) :
    ∃ Y : PMF_ZMod (∏ q ∈ Q', q),
      (∀ y : ZMod (∏ q ∈ Q', q), Y.p y ≠ 0 →
        ∃ d : ℕ, 0 < d ∧ d ∣ M_core m ∧ ¬ ((∏ q ∈ Q', q) ∣ d) ∧
          d < m ^ 3 * (∏ q ∈ Q', q) ∧ p_tag ∣ d ∧ (∀ p ∈ Q_tag, p ∣ d → p = p_tag) ∧
          (d : ZMod (∏ q ∈ Q', q)) = y) ∧
      (1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))) *
          deficit_zmod X ≤
        Hnat_zmod (conv_zmod X Y) - Hnat_zmod X := by
  classical
  set l : List ℕ := Q'.toList
  have hnd : l.Nodup := Finset.nodup_toList Q'
  have hl : ∀ q ∈ l, q.Prime := fun q hq =>
    (hband q (Finset.mem_union_left _ (hQ'_sub (Finset.mem_toList.mp hq)))).1
  have hl_band : ∀ q ∈ l, 14 * m_dil / 25 < q ∧ q ≤ m_dil := fun q hq =>
    let hb := hband q (Finset.mem_union_left _ (hQ'_sub (Finset.mem_toList.mp hq)))
    ⟨hb.2.2.1, hb.2.2.2⟩
  have hprod_eq : l.prod = ∏ q ∈ Q', q := Finset.prod_toList Q'
  have hlen_eq : l.length = Q'.card := Finset.length_toList Q'
  have hlen_pos : 1 ≤ l.length := by rw [hlen_eq]; exact hQ'_ne.card_pos
  -- Transport X along hprod_eq : l.prod = ∏ q ∈ Q', q
  -- Actually generalize via subst hprod_eq? No, Q' is a Finset; use a clean cast!
  -- Even cleaner: prove the statement for l.prod directly, then rewrite by hprod_eq!
  have hmain : ∀ (M' : ℕ) (hM' : l.prod = M') [hM'_nz : NeZero M'] (X₀ : PMF_ZMod M'),
      ∃ Y₀ : PMF_ZMod M',
        (∀ y : ZMod M', Y₀.p y ≠ 0 →
          ∃ d : ℕ, 0 < d ∧ d ∣ M_core m ∧ ¬ (M' ∣ d) ∧
            d < m ^ 3 * M' ∧ p_tag ∣ d ∧ (∀ p ∈ Q_tag, p ∣ d → p = p_tag) ∧
            (d : ZMod M') = y) ∧
        (1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))) *
            deficit_zmod X₀ ≤
          Hnat_zmod (conv_zmod X₀ Y₀) - Hnat_zmod X₀ := by
    intro M' hM' hM'_nz X₀
    subst hM'
    have : NeZero l.prod := list_prod_neZero hl
    have hnz_eq : hM'_nz = list_prod_neZero hl := Subsingleton.elim _ _
    subst hnz_eq
    set δ : Fin l.length → ℝ := coordDeficit l hl hnd X₀
    rcases exists_greedy_top_sets (Finset.univ : Finset (Fin l.length)) δ with ⟨ord, S, hS, hsum_ord⟩
    have hcard_univ : (Finset.univ : Finset (Fin l.length)).card = l.length := Finset.card_fin l.length
    rw [hcard_univ] at hS hsum_ord
    rw [sum_coordDeficit l hl hnd X₀] at hsum_ord
    set N : ℕ := (primePool m).card
    have hN_le_m : N ≤ m := by
      have : (primePool m).card ≤ (Finset.Icc 2 (m / 8)).card := Finset.card_le_card (Finset.filter_subset _ _)
      rw [Nat.card_Icc] at this; omega
    have hlen_le_N2 : l.length ≤ N / 2 := by rw [hlen_eq]; exact hQ'_le
    -- Choose r* ∈ Icc 1 l.length maximizing ord r * (r * log (N / r))
    have hIcc_ne : (Finset.Icc 1 l.length).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hlen_pos⟩⟩
    let score : ℕ → ℝ := fun r => ord r * ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ)))
    rcases Finset.exists_max_image (Finset.Icc 1 l.length) score hIcc_ne with ⟨r_star, hr_mem, hr_max⟩
    have hr1 : 1 ≤ r_star := (Finset.mem_Icc.mp hr_mem).1
    have hr_len : r_star ≤ l.length := (Finset.mem_Icc.mp hr_mem).2
    have hharm := harmonic_choose_sum_le hpool_ge8 hlen_le_N2
    have hloglog_le : Real.log (Real.log ((N : ℝ) + 16)) + 4 ≤ Real.log (Real.log ((m : ℝ) + 16)) + 4 := by
      have h16 : (16 : ℝ) ≤ (N : ℝ) + 16 := by linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
      have hlog16_pos : 0 < Real.log ((N : ℝ) + 16) := Real.log_pos (by linarith)
      have hNm_cast : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hN_le_m
      have hNm_r : (N : ℝ) + 16 ≤ (m : ℝ) + 16 := by linarith
      have hle := Real.log_le_log hlog16_pos (Real.log_le_log (by linarith) hNm_r)
      linarith
    have hscore_lb : deficit_zmod X₀ ≤ score r_star * (Real.log (Real.log ((m : ℝ) + 16)) + 4) := by
      have hsum_le : ∑ r ∈ Finset.Icc 1 l.length, ord r ≤
          score r_star * ∑ r ∈ Finset.Icc 1 l.length, (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun r hr => ?_
        have hr_1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hr_l : r ≤ l.length := (Finset.mem_Icc.mp hr).2
        have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
        have hlog_pos : 0 < Real.log ((N : ℝ) / (r : ℝ)) := by
          apply Real.log_pos; rw [one_lt_div hr_pos]
          have : 2 * r ≤ N := by omega
          have : (2 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
          linarith
        have hden_pos : 0 < (r : ℝ) * Real.log ((N : ℝ) / (r : ℝ)) := mul_pos hr_pos hlog_pos
        have hsc := hr_max r hr
        dsimp [score] at hsc
        rw [mul_one_div, le_div_iff₀ hden_pos]
        exact hsc
      have hscore_nn : 0 ≤ score r_star := by
        rcases hS r_star hr_mem with ⟨_, hcard_S, hord_le⟩
        have hne_S : (S r_star).Nonempty := Finset.card_pos.mp (by omega)
        -- Actually ord r_star could be ≤ δ i, wait: what if ord r_star < 0?
        -- Since δ i ≥ 0 for all i, we can check: if score r_star < 0 then ∑ ord ≤ 0, contradicting deficit ≥ 0?
        -- Even cleaner: 0 ≤ deficit_zmod X₀ = ∑ ord ≤ score r_star * ∑ (1 / ...) and ∑ (1 / ...) > 0!
        by_contra hneg
        push Not at hneg
        have hsum_pos : 0 < ∑ r ∈ Finset.Icc 1 l.length, (1 : ℝ) / ((r : ℝ) * Real.log ((N : ℝ) / (r : ℝ))) := by
          refine Finset.sum_pos (fun r hr => ?_) hIcc_ne
          have hr_1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
          have hr_l : r ≤ l.length := (Finset.mem_Icc.mp hr).2
          have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
          have hlog_pos : 0 < Real.log ((N : ℝ) / (r : ℝ)) := by
            apply Real.log_pos; rw [one_lt_div hr_pos]
            have : (2 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 * r ≤ N)
            linarith
          positivity
        have hdef_nn := deficit_zmod_nonneg X₀
        nlinarith
      rw [hsum_ord] at hsum_le
      exact hsum_le.trans (mul_le_mul_of_nonneg_left (hharm.trans hloglog_le) hscore_nn)
    -- Build S* = S r_star, Q_comp = image of univ \ S* under l.get, M_comp = ∏ Q_comp
    set S_star : Finset (Fin l.length) := S r_star
    rcases hS r_star hr_mem with ⟨_, hS_card, hord_le_S⟩
    set S_comp : Finset (Fin l.length) := Finset.univ \ S_star
    have hl_inj : Function.Injective l.get := List.nodup_iff_injective_get.mp hnd
    set Q_S : Finset ℕ := S_star.image l.get
    set Q_comp : Finset ℕ := S_comp.image l.get
    have hQS_card : Q_S.card = r_star := by
      rw [Finset.card_image_of_injective _ hl_inj, hS_card]
    have hdisj_SQ : Disjoint Q_S Q_comp := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      rcases Finset.mem_image.mp hq1 with ⟨i1, hi1, rfl⟩
      rcases Finset.mem_image.mp hq2 with ⟨i2, hi2, heq⟩
      have := hl_inj heq
      subst this
      exact (Finset.mem_sdiff.mp hi2).2 hi1
    have hM'_split : (∏ q ∈ Q_S, q) * (∏ q ∈ Q_comp, q) = l.prod := by
      rw [← Finset.prod_union hdisj_SQ]
      have hunion : Q_S ∪ Q_comp = Q' := by
        ext q
        simp only [Q_S, Q_comp, S_comp, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff,
          Finset.mem_univ, true_and]
        constructor
        · rintro (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩)
          · exact Finset.mem_toList.mp (List.get_mem l i)
          · exact Finset.mem_toList.mp (List.get_mem l i)
        · intro hq
          rcases List.mem_iff_get.mp (Finset.mem_toList.mpr hq) with ⟨i, rfl⟩
          by_cases hi : i ∈ S_star
          · exact Or.inl ⟨i, hi, rfl⟩
          · exact Or.inr ⟨i, hi, rfl⟩
      rw [hunion, hprod_eq]
    set M_S : ℕ := ∏ q ∈ Q_S, q
    set M_comp : ℕ := ∏ q ∈ Q_comp, q
    have hptag_info := hband p_tag (Finset.mem_union_right _ hp_tag_mem)
    have hQcomp_info : ∀ q ∈ Q_comp, q.Prime ∧ m / 2 < q ∧ q ≤ m := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨i, _, rfl⟩
      have hb := hband (l.get i) (Finset.mem_union_left _ (hQ'_sub (Finset.mem_toList.mp (List.get_mem l i))))
      exact ⟨hb.1, hb.2.1, le_trans hb.2.2.2 hmdil_hi⟩
    have hQS_info : ∀ q ∈ Q_S, q.Prime ∧ m / 2 < q ∧ q ≤ m := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨i, _, rfl⟩
      have hb := hband (l.get i) (Finset.mem_union_left _ (hQ'_sub (Finset.mem_toList.mp (List.get_mem l i))))
      exact ⟨hb.1, hb.2.1, le_trans hb.2.2.2 hmdil_hi⟩
    have hptag_not_Qcomp : p_tag ∉ Q_comp := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨i, _, heq⟩
      have hq_strip : p_tag ∈ Q_strip := heq ▸ hQ'_sub (Finset.mem_toList.mp (List.get_mem l i))
      exact Finset.disjoint_left.mp hdisj_band hq_strip hp_tag_mem
    -- Coprimality of p_tag * M_comp with M_S
    have hcop_S : Nat.Coprime (p_tag * M_comp) M_S := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hqp := (hQS_info q hq).1
      apply Nat.Coprime.mul_left
      · have hne : p_tag ≠ q := by
          intro heq; subst heq
          rcases Finset.mem_image.mp hq with ⟨i, _, hi⟩
          have hq_strip : p_tag ∈ Q_strip := hi ▸ hQ'_sub (Finset.mem_toList.mp (List.get_mem l i))
          exact Finset.disjoint_left.mp hdisj_band hq_strip hp_tag_mem
        exact (Nat.coprime_primes hptag_info.1 hqp).mpr hne
      · apply Nat.Coprime.prod_left
        intro q' hq'
        have hne : q' ≠ q := fun heq => Finset.disjoint_left.mp hdisj_SQ hq (heq ▸ hq')
        exact (Nat.coprime_primes (hQcomp_info q' hq').1 hqp).mpr hne
    -- Build T = image of (primePool m).powersetCard r_star under A ↦ (p_tag * M_comp * ∏ A : ZMod l.prod)
    set Pow : Finset (Finset ℕ) := (primePool m).powersetCard r_star
    let fZ : Finset ℕ → ZMod l.prod := fun A => ((p_tag * M_comp * ∏ p ∈ A, p : ℕ) : ZMod l.prod)
    have hZ_lt_MS : ∀ A ∈ Pow, ∏ p ∈ A, p < M_S := by
      intro A hA
      rcases Finset.mem_powersetCard.mp hA with ⟨hA_sub, hA_card⟩
      have h1 : ∏ p ∈ A, p ≤ (m / 8) ^ r_star := by
        calc ∏ p ∈ A, p ≤ ∏ _p ∈ A, (m / 8) :=
              Finset.prod_le_prod fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hA_sub hp)).1).2
          _ = (m / 8) ^ r_star := by rw [Finset.prod_const, hA_card]
      have h2 : (m / 8) ^ r_star < (m / 2) ^ r_star :=
        Nat.pow_lt_pow_left (by omega : m / 8 < m / 2) (by omega : r_star ≠ 0)
      have h3 : (m / 2) ^ r_star ≤ M_S := by
        calc (m / 2) ^ r_star = ∏ _q ∈ Q_S, (m / 2) := by rw [Finset.prod_const, hQS_card]
          _ ≤ ∏ q ∈ Q_S, q := Finset.prod_le_prod fun q hq => (hQS_info q hq).2.1.le
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
    have hfZ_inj : Set.InjOn fZ (Pow : Set (Finset ℕ)) := by
      intro A hA B hB hEq
      have hmod : (p_tag * M_comp * ∏ p ∈ A, p) ≡ (p_tag * M_comp * ∏ p ∈ B, p) [MOD l.prod] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hEq
      have hmodS : (p_tag * M_comp * ∏ p ∈ A, p) ≡ (p_tag * M_comp * ∏ p ∈ B, p) [MOD M_S] :=
        hmod.of_dvd ⟨M_comp, hM'_split.symm⟩
      have hz_mod : (∏ p ∈ A, p) ≡ (∏ p ∈ B, p) [MOD M_S] :=
        Nat.ModEq.cancel_left_of_coprime hcop_S.symm hmodS
      have hz_eq : ∏ p ∈ A, p = ∏ p ∈ B, p := by
        unfold Nat.ModEq at hz_mod
        rwa [Nat.mod_eq_of_lt (hZ_lt_MS A hA), Nat.mod_eq_of_lt (hZ_lt_MS B hB)] at hz_mod
      exact prime_prod_injOn m r_star hA hB hz_eq
    set T : Finset (ZMod l.prod) := Pow.image fZ
    have hT_card : T.card = Nat.choose N r_star := by
      rw [Finset.card_image_of_injOn hfZ_inj, Finset.card_powersetCard]
    have hT_ne : T.Nonempty := Finset.card_pos.mp (by rw [hT_card]; exact Nat.choose_pos (by omega))
    set Y₀ : PMF_ZMod l.prod := unifFinsetPMF T hT_ne
    have hA_ne : (smoothSet m_dil).Nonempty := by
      have := smoothSet_card_ge hmdil_lo
      have hm_big : 10000 ≤ m_dil := le_trans (by unfold m1_pigeonhole; norm_num) hmdil_lo
      exact Finset.card_pos.mp (by omega)
    set Y : PMF_ZMod l.prod := mixDilate m_dil hA_ne Y₀
    refine ⟨Y, ?_, ?_⟩
    · -- Support properties of Y
      intro y hy
      dsimp [Y, mixDilate] at hy
      have hne_sum : ∑ c₁ ∈ smoothSet m_dil, ∑ c₂ ∈ smoothSet m_dil,
          (conv_dilate (pointPMF (0 : ZMod l.prod)) Y₀ ((c₁ * c₂ : ℕ) : ZMod l.prod)).p y ≠ 0 :=
        right_ne_zero_of_mul hy
      rcases Finset.exists_ne_zero_of_sum_ne_zero hne_sum with ⟨c₁, hc₁, hne2⟩
      rcases Finset.exists_ne_zero_of_sum_ne_zero hne2 with ⟨c₂, hc₂, hne3⟩
      dsimp [conv_dilate, pointPMF] at hne3
      rcases Finset.exists_ne_zero_of_sum_ne_zero hne3 with ⟨z, _, hne4⟩
      have hz_eq : y = ((c₁ * c₂ : ℕ) : ZMod l.prod) * z := by
        by_contra hne_yz
        have hsub : y - ((c₁ * c₂ : ℕ) : ZMod l.prod) * z ≠ 0 := sub_ne_zero.mpr hne_yz
        simp only [hsub, ite_false, zero_mul] at hne4
        exact hne4 rfl
      have hz_mem : z ∈ T := by
        by_contra hnot
        have : Y₀.p z = 0 := by simp [Y₀, unifFinsetPMF, hnot]
        simp [this] at hne4
      rcases Finset.mem_image.mp hz_mem with ⟨A, hA_mem, rfl⟩
      have hA_sub : A ⊆ primePool m := (Finset.mem_powersetCard.mp hA_mem).1
      set d : ℕ := p_tag * c₁ * c₂ * M_comp * ∏ p ∈ A, p
      refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- 0 < d
        exact mul_pos (mul_pos (mul_pos (mul_pos hptag_info.1.pos (smoothSet_pos hc₁)) (smoothSet_pos hc₂))
          (Finset.prod_pos fun q hq => (hQcomp_info q hq).1.pos))
          (Finset.prod_pos fun p hp => (Finset.mem_filter.mp (hA_sub hp)).2.pos)
      · -- d ∣ M_core m
        exact lemma4_term_dvd_M_core hm4096 hmdil_hi
          ⟨hptag_info.1, hptag_info.2.1, le_trans hptag_info.2.2.2 hmdil_hi⟩
          hc₁ hc₂ hQcomp_info hptag_not_Qcomp hA_sub
      · -- ¬ (l.prod ∣ d)
        intro hdvd
        have hne_S : S_star.Nonempty := Finset.card_pos.mp (by rw [hS_card]; omega)
        rcases hne_S with ⟨i₀, hi₀⟩
        set q₀ : ℕ := l.get i₀
        have hq₀_QS : q₀ ∈ Q_S := Finset.mem_image.mpr ⟨i₀, hi₀, rfl⟩
        have hq₀_info := hQS_info q₀ hq₀_QS
        have hq₀_dvd_d : q₀ ∣ d := dvd_trans (List.dvd_prod (List.get_mem l i₀)) hdvd
        have hq₀_prime := hq₀_info.1
        rcases hq₀_prime.dvd_mul.mp hq₀_dvd_d with h1 | hA_dvd
        · rcases hq₀_prime.dvd_mul.mp h1 with h2 | hQ_dvd
          · rcases hq₀_prime.dvd_mul.mp h2 with h3 | hc2_dvd
            · rcases hq₀_prime.dvd_mul.mp h3 with hpt_dvd | hc1_dvd
              · have heq := (Nat.prime_dvd_prime_iff_eq hq₀_prime hptag_info.1).mp hpt_dvd
                have hq_strip : p_tag ∈ Q_strip := heq ▸ hQ'_sub (Finset.mem_toList.mp (List.get_mem l i₀))
                exact Finset.disjoint_left.mp hdisj_band hq_strip hp_tag_mem
              · have := smoothSet_prime_dvd_le hc₁ hq₀_prime hc1_dvd; omega
            · have := smoothSet_prime_dvd_le hc₂ hq₀_prime hc2_dvd; omega
          · have hf := congrArg (fun n : ℕ => n.factorization q₀) (rfl : M_comp = ∏ q ∈ Q_comp, q)
            have hmemQ : q₀ ∈ Q_comp := by
              by_contra hnot
              have h0 : M_comp.factorization q₀ = 0 := by
                rw [prod_primes_factorization (fun q hq => (hQcomp_info q hq).1) q₀]; simp [hnot]
              have hpos : 1 ≤ M_comp.factorization q₀ :=
                (hq₀_prime.pow_dvd_iff_le_factorization
                  (Finset.prod_pos fun q hq => (hQcomp_info q hq).1.pos).ne').mp (by simpa using hQ_dvd)
              omega
            exact Finset.disjoint_left.mp hdisj_SQ hq₀_QS hmemQ
        · have hmemA : q₀ ∈ A := by
            by_contra hnot
            have h0 : (∏ p ∈ A, p).factorization q₀ = 0 := by
              rw [prod_primes_factorization (fun p hp => (Finset.mem_filter.mp (hA_sub hp)).2) q₀]; simp [hnot]
            have hpos : 1 ≤ (∏ p ∈ A, p).factorization q₀ :=
              (hq₀_prime.pow_dvd_iff_le_factorization
                (Finset.prod_pos fun p hp => (Finset.mem_filter.mp (hA_sub hp)).2.pos).ne').mp
                (by simpa using hA_dvd)
            omega
          have : q₀ ≤ m / 8 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hA_sub hmemA)).1).2
          omega
      · -- d < m ^ 3 * l.prod
        have hpt_le : p_tag ≤ m := le_trans hptag_info.2.2.2 hmdil_hi
        have hc12 : c₁ * c₂ < m ^ 2 := by
          have hm_dil2 : 2 ≤ m_dil := le_trans (by unfold m1_pigeonhole; norm_num) hmdil_lo
          have := smoothSet_mul_lt_sq hm_dil2 hc₁ hc₂
          exact lt_of_lt_of_le this (Nat.pow_le_pow_left hmdil_hi 2)
        have hZ_lt := hZ_lt_MS A hA_mem
        have h1 : p_tag * (c₁ * c₂) < m ^ 3 := by
          calc p_tag * (c₁ * c₂) ≤ m * (c₁ * c₂) := Nat.mul_le_mul_right _ hpt_le
            _ < m * m ^ 2 := Nat.mul_lt_mul_of_pos_left hc12 (by omega)
            _ = m ^ 3 := by ring
        have h2 : M_comp * (∏ p ∈ A, p) < l.prod := by
          rw [← hM'_split, mul_comm M_S M_comp]
          exact Nat.mul_lt_mul_of_pos_left hZ_lt (Finset.prod_pos fun q hq => (hQcomp_info q hq).1.pos)
        calc d = (p_tag * (c₁ * c₂)) * (M_comp * ∏ p ∈ A, p) := by dsimp [d]; ring
          _ < m ^ 3 * l.prod := Nat.mul_lt_mul'' h1 h2
      · -- p_tag ∣ d
        exact ⟨c₁ * c₂ * M_comp * ∏ p ∈ A, p, by dsimp [d]; ring⟩
      · -- ∀ p ∈ Q_tag, p ∣ d → p = p_tag
        intro p hp_mem hp_dvd
        have hp_info := hband p (Finset.mem_union_right _ hp_mem)
        have hpp := hp_info.1
        rcases hpp.dvd_mul.mp hp_dvd with h1 | hA_dvd
        · rcases hpp.dvd_mul.mp h1 with h2 | hQ_dvd
          · rcases hpp.dvd_mul.mp h2 with h3 | hc2_dvd
            · rcases hpp.dvd_mul.mp h3 with hpt_dvd | hc1_dvd
              · exact (Nat.prime_dvd_prime_iff_eq hpp hptag_info.1).mp hpt_dvd
              · have := smoothSet_prime_dvd_le hc₁ hpp hc1_dvd; omega
            · have := smoothSet_prime_dvd_le hc₂ hpp hc2_dvd; omega
          · have hmemQ : p ∈ Q_comp := by
              by_contra hnot
              have h0 : M_comp.factorization p = 0 := by
                rw [prod_primes_factorization (fun q hq => (hQcomp_info q hq).1) p]; simp [hnot]
              have hpos : 1 ≤ M_comp.factorization p :=
                (hpp.pow_dvd_iff_le_factorization
                  (Finset.prod_pos fun q hq => (hQcomp_info q hq).1.pos).ne').mp (by simpa using hQ_dvd)
              omega
            rcases Finset.mem_image.mp hmemQ with ⟨i, _, hi⟩
            have hp_strip : p ∈ Q_strip := hi ▸ hQ'_sub (Finset.mem_toList.mp (List.get_mem l i))
            exact absurd hp_mem (Finset.disjoint_left.mp hdisj_band hp_strip)
        · have hmemA : p ∈ A := by
            by_contra hnot
            have h0 : (∏ r ∈ A, r).factorization p = 0 := by
              rw [prod_primes_factorization (fun r hr => (Finset.mem_filter.mp (hA_sub hr)).2) p]; simp [hnot]
            have hpos : 1 ≤ (∏ r ∈ A, r).factorization p :=
              (hpp.pow_dvd_iff_le_factorization
                (Finset.prod_pos fun r hr => (Finset.mem_filter.mp (hA_sub hr)).2.pos).ne').mp
                (by simpa using hA_dvd)
            omega
          have : p ≤ m / 8 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hA_sub hmemA)).1).2
          omega
      · -- (d : ZMod l.prod) = y
        rw [hz_eq]
        dsimp [d, fZ]
        push_cast
        ring
    · -- Entropy gain lower bound
      have hcrt := crt_list_dilation_entropy_gain m_dil hmdil_lo l hl hnd hl_band X₀ Y₀
      have hmix := Hnat_conv_mixDilate_ge m_dil hA_ne X₀ Y₀
      -- Restrict sum over Fin l.length to S_star
      have hsub_sum :
          ∑ i ∈ S_star,
            ((1 / 40 : ℝ) / (2420 * Real.log (l.get i : ℝ))) *
              (coordEnt l hl hnd Y₀ i - 5 * Real.log (l.get i : ℝ) / (l.get i : ℝ)) * δ i ≤
          ∑ i : Fin l.length,
            max 0 (((1 / 40 : ℝ) / (2420 * Real.log (l.get i : ℝ))) *
              (coordEnt l hl hnd Y₀ i - 5 * Real.log (l.get i : ℝ) / (l.get i : ℝ)) * δ i) := by
        calc ∑ i ∈ S_star,
              ((1 / 40 : ℝ) / (2420 * Real.log (l.get i : ℝ))) *
                (coordEnt l hl hnd Y₀ i - 5 * Real.log (l.get i : ℝ) / (l.get i : ℝ)) * δ i
            ≤ ∑ i ∈ S_star,
              max 0 (((1 / 40 : ℝ) / (2420 * Real.log (l.get i : ℝ))) *
                (coordEnt l hl hnd Y₀ i - 5 * Real.log (l.get i : ℝ) / (l.get i : ℝ)) * δ i) :=
              Finset.sum_le_sum fun i _ => le_max_right _ _
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => le_max_left _ _)
      -- On S_star: log(l.get i) ≤ log m, l.get i > m/2, and δ i ≥ ord r_star
      have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr (by omega))
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hterm_S : ∀ i ∈ S_star,
          (1 / (96800 * Real.log (m : ℝ))) * (coordEnt l hl hnd Y₀ i * ord r_star) -
            (10 / (96800 * (m : ℝ))) * δ i ≤
          ((1 / 40 : ℝ) / (2420 * Real.log (l.get i : ℝ))) *
            (coordEnt l hl hnd Y₀ i - 5 * Real.log (l.get i : ℝ) / (l.get i : ℝ)) * δ i := by
        intro i hi
        have hqi_info := hband (l.get i) (Finset.mem_union_left _ (hQ'_sub (Finset.mem_toList.mp (List.get_mem l i))))
        have hqi_le : (l.get i : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (le_trans hqi_info.2.2.2 hmdil_hi)
        have hqi_gt : (m : ℝ) / 2 ≤ (l.get i : ℝ) := by
          have : m / 2 + 1 ≤ l.get i := hqi_info.2.1
          have : m ≤ 2 * (m / 2) + 1 := by omega
          have hcast : (m : ℝ) ≤ 2 * (l.get i : ℝ) := by exact_mod_cast (by omega : m ≤ 2 * l.get i)
          linarith
        have hqi_pos : (0 : ℝ) < (l.get i : ℝ) := by linarith
        have hlogqi_pos : 0 < Real.log (l.get i : ℝ) :=
          Real.log_pos (Nat.one_lt_cast.mpr (by have := hqi_info.2.1; omega))
        have hlogqi_le : Real.log (l.get i : ℝ) ≤ Real.log (m : ℝ) :=
          Real.log_le_log hqi_pos hqi_le
        have hsplit : ((1 / 40 : ℝ) / (2420 * Real.log (l.get i : ℝ))) *
            (coordEnt l hl hnd Y₀ i - 5 * Real.log (l.get i : ℝ) / (l.get i : ℝ)) * δ i =
            (1 / (96800 * Real.log (l.get i : ℝ))) * (coordEnt l hl hnd Y₀ i * δ i) -
            (5 / (96800 * (l.get i : ℝ))) * δ i := by
          field_simp [hlogqi_pos.ne', hqi_pos.ne']
          ring
        rw [hsplit]
        have h1 : (1 / (96800 * Real.log (m : ℝ))) * (coordEnt l hl hnd Y₀ i * ord r_star) ≤
            (1 / (96800 * Real.log (l.get i : ℝ))) * (coordEnt l hl hnd Y₀ i * δ i) := by
          have hord_i : ord r_star ≤ δ i := hord_le_S i hi
          have hce_nn : 0 ≤ coordEnt l hl hnd Y₀ i := coordEnt_nonneg l hl hnd Y₀ i
          have hδ_nn : 0 ≤ δ i := coordDeficit_nonneg l hl hnd X₀ i
          have hinv : 1 / (96800 * Real.log (m : ℝ)) ≤ 1 / (96800 * Real.log (l.get i : ℝ)) :=
            one_div_le_one_div_of_le (by positivity) (by nlinarith)
          have hmul1 : coordEnt l hl hnd Y₀ i * ord r_star ≤ coordEnt l hl hnd Y₀ i * δ i :=
            mul_le_mul_of_nonneg_left hord_i hce_nn
          exact (mul_le_mul_of_nonneg_left hmul1 (by positivity)).trans
            (mul_le_mul_of_nonneg_right hinv (mul_nonneg hce_nn hδ_nn))
        have h2 : (5 / (96800 * (l.get i : ℝ))) * δ i ≤ (10 / (96800 * (m : ℝ))) * δ i := by
          have hδ_nn : 0 ≤ δ i := coordDeficit_nonneg l hl hnd X₀ i
          have hfrac : 5 / (96800 * (l.get i : ℝ)) ≤ 10 / (96800 * (m : ℝ)) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          exact mul_le_mul_of_nonneg_right hfrac hδ_nn
        linarith
      have hsum_S := Finset.sum_le_sum hterm_S
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul] at hsum_S
      -- Compute ∑ i ∈ S_star, coordEnt l hl hnd Y₀ i = Hnat_zmod Y₀ = log (choose N r_star) ≥ r_star * log (N / r_star)
      have hzero_outside : ∀ i ∈ Finset.univ, i ∉ S_star → coordEnt l hl hnd Y₀ i = 0 := by
        intro i _ hi
        apply coordEnt_eq_zero_of_dvd l hl hnd Y₀ i
        intro y hy
        have hyT : y ∈ T := by
          by_contra hnot; simp [Y₀, unifFinsetPMF, hnot] at hy
        rcases Finset.mem_image.mp hyT with ⟨A, _, rfl⟩
        have hli_Qcomp : l.get i ∈ Q_comp :=
          Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
        have hli_dvd_Mc : l.get i ∣ M_comp := Finset.dvd_prod_of_mem _ hli_Qcomp
        have hli_dvd_num : l.get i ∣ p_tag * M_comp * ∏ p ∈ A, p :=
          dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hli_dvd_Mc p_tag) _
        dsimp [fZ]
        rw [ZMod.val_natCast]
        exact (Nat.dvd_mod_iff (List.dvd_prod (List.get_mem l i))).mpr hli_dvd_num
      have hsum_ce : ∑ i ∈ S_star, coordEnt l hl hnd Y₀ i = Real.log (Nat.choose N r_star : ℝ) := by
        calc ∑ i ∈ S_star, coordEnt l hl hnd Y₀ i
            = ∑ i : Fin l.length, coordEnt l hl hnd Y₀ i :=
              Finset.sum_subset (Finset.subset_univ _) hzero_outside
          _ = Hnat_zmod Y₀ := sum_coordEnt l hl hnd Y₀
          _ = Real.log (T.card : ℝ) := Hnat_unifFinsetPMF T hT_ne
          _ = Real.log (Nat.choose N r_star : ℝ) := by rw [hT_card]
      have hchoose_lb : (r_star : ℝ) * Real.log ((N : ℝ) / (r_star : ℝ)) ≤
          Real.log (Nat.choose N r_star : ℝ) := by
        have h1 := div_pow_le_choose_real hr1 (by omega : r_star ≤ N)
        have hr_pos : (0 : ℝ) < (r_star : ℝ) := Nat.cast_pos.mpr (by omega)
        have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
        calc (r_star : ℝ) * Real.log ((N : ℝ) / (r_star : ℝ))
            = Real.log (((N : ℝ) / (r_star : ℝ)) ^ r_star) := (Real.log_pow _ _).symm
          _ ≤ Real.log (Nat.choose N r_star : ℝ) := Real.log_le_log (by positivity) h1
      have hsum_δ_le : ∑ i ∈ S_star, δ i ≤ deficit_zmod X₀ := by
        rw [← sum_coordDeficit l hl hnd X₀]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => coordDeficit_nonneg l hl hnd X₀ i)
      -- Combine: score r_star / (96800 * log m) - 10 / (96800 * m) * deficit ≥ deficit / (193600 * log m * (log log (m+16) + 4))
      have hll_pos : 0 < Real.log (Real.log ((m : ℝ) + 16)) + 4 := by
        have h16 : (16 : ℝ) ≤ (m : ℝ) + 16 := by linarith
        have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; ring
        have : 0 ≤ Real.log (Real.log ((m : ℝ) + 16)) := by
          apply Real.log_nonneg
          have := Real.log_le_log (by norm_num) h16
          linarith [Real.log_two_gt_d9]
        linarith
      have hscore_div : deficit_zmod X₀ / (Real.log (Real.log ((m : ℝ) + 16)) + 4) ≤ score r_star :=
        (div_le_iff₀ hll_pos).mpr hscore_lb
      have hord_nn : 0 ≤ ord r_star := by
        by_contra hneg
        push Not at hneg
        have hr_pos : (0 : ℝ) < (r_star : ℝ) := Nat.cast_pos.mpr (by omega)
        have hlog_pos : 0 < Real.log ((N : ℝ) / (r_star : ℝ)) := by
          apply Real.log_pos; rw [one_lt_div hr_pos]
          have : (2 : ℝ) * (r_star : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 * r_star ≤ N)
          linarith
        have hsc_neg : score r_star < 0 := mul_neg_of_neg_of_pos hneg (mul_pos hr_pos hlog_pos)
        have hdef_nn := deficit_zmod_nonneg X₀
        have : 0 ≤ score r_star := le_trans (div_nonneg hdef_nn hll_pos.le) hscore_div
        linarith
      have hterm1 : (1 / (96800 * Real.log (m : ℝ))) * (deficit_zmod X₀ / (Real.log (Real.log ((m : ℝ) + 16)) + 4)) ≤
          (1 / (96800 * Real.log (m : ℝ))) * ((∑ i ∈ S_star, coordEnt l hl hnd Y₀ i) * ord r_star) := by
        rw [hsum_ce]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hchoose_lb hord_nn
        rw [mul_comm] at hmul
        exact hscore_div.trans hmul
      -- Show 10 / m ≤ 1 / (2 * log m * (log log (m + 16) + 4)) for m ≥ 4096
      have hmargin := margin_bound_4096 hm4096
      have hdef_nn := deficit_zmod_nonneg X₀
      have hterm2 : (10 / (96800 * (m : ℝ))) * (∑ i ∈ S_star, δ i) ≤
          (1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))) * deficit_zmod X₀ := by
        exact (mul_le_mul_of_nonneg_left hsum_δ_le (by positivity)).trans
          (mul_le_mul_of_nonneg_right hmargin hdef_nn)
      have hhalf : (1 / (96800 * Real.log (m : ℝ))) * (deficit_zmod X₀ / (Real.log (Real.log ((m : ℝ) + 16)) + 4)) -
          (1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))) * deficit_zmod X₀ =
          (1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))) * deficit_zmod X₀ := by
        field_simp [hlogm_pos.ne', hll_pos.ne']
        ring
      have hchain := (hsum_S.trans hsub_sum).trans (hcrt.trans hmix)
      linarith
  exact hmain (∏ q ∈ Q', q) hprod_eq X


/-! ## Section 4: Lemma 5 — Iterated Mod-`M'` Covering and Exact Digit Representation -/

/-- Step count for Lemma 5 mod-`M'` covering:
    `R_cover m = ⌈193600 * log m * (log log (m + 16) + 4) * log (12 * m)⌉`. -/
noncomputable def R_cover (m : ℕ) : ℕ :=
  Nat.ceil (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) * Real.log (12 * (m : ℝ)))

/-- Support of a convolution `conv_zmod X Y`. -/
private lemma suppZMod_conv_zmod {M : ℕ} [NeZero M] (X Y : PMF_ZMod M) {z : ZMod M}
    (hz : z ∈ suppZMod (conv_zmod X Y)) :
    ∃ x ∈ suppZMod X, ∃ y ∈ suppZMod Y, x + y = z := by
  rw [suppZMod, Finset.mem_filter] at hz
  have hz2 : ∑ y : ZMod M, X.p (z - 1 * y) * Y.p y ≠ 0 := hz.2
  rcases Finset.exists_ne_zero_of_sum_ne_zero hz2 with ⟨y, _, hne⟩
  rw [one_mul] at hne
  have h1 : X.p (z - y) ≠ 0 := (mul_ne_zero_iff.mp hne).1
  have h2 : Y.p y ≠ 0 := (mul_ne_zero_iff.mp hne).2
  exact ⟨z - y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
    y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, sub_add_cancel z y⟩

/-- Iterating `adaptive_dilation_contraction` along a list `tags` of distinct tag primes in `Q_tag`. -/
private lemma iterated_contraction_list {m m_dil : ℕ} {Q_strip Q_tag Q' : Finset ℕ}
    (hm4096 : 4096 ≤ m) (hmdil_lo : m1_pigeonhole ≤ m_dil) (hmdil_hi : m_dil ≤ m)
    (hdisj_band : Disjoint Q_strip Q_tag)
    (hband : ∀ q ∈ Q_strip ∪ Q_tag, q.Prime ∧ m / 2 < q ∧ 14 * m_dil / 25 < q ∧ q ≤ m_dil)
    (hQ'_sub : Q' ⊆ Q_strip) (hQ'_ne : Q'.Nonempty)
    (hQ'_le : Q'.card ≤ (primePool m).card / 2) (hpool_ge8 : 8 ≤ (primePool m).card)
    [NeZero (∏ q ∈ Q', q)]
    (tags : List ℕ) (htags_nd : tags.Nodup) (htags_sub : ∀ p ∈ tags, p ∈ Q_tag)
    (X₀ : PMF_ZMod (∏ q ∈ Q', q)) :
    ∃ X_end : PMF_ZMod (∏ q ∈ Q', q),
      deficit_zmod X_end ≤
        (1 - 1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))) ^ tags.length *
          deficit_zmod X₀ ∧
      ∀ x ∈ suppZMod X_end, ∃ x₀ ∈ suppZMod X₀, ∃ S : Finset ℕ,
        S.card = tags.length ∧
        (∀ d ∈ S, 0 < d ∧ d ∣ M_core m ∧ ¬ ((∏ q ∈ Q', q) ∣ d) ∧
          d < m ^ 3 * (∏ q ∈ Q', q) ∧ (∃ p ∈ tags, p ∣ d) ∧ (∀ p ∈ Q_tag, p ∣ d → p ∈ tags)) ∧
        x₀ + ((S.sum id : ℕ) : ZMod (∏ q ∈ Q', q)) = x := by
  set η : ℝ := 1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
  have hlogm_ge1 : (1 : ℝ) ≤ Real.log (m : ℝ) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (m : ℝ) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hll_ge4 : (4 : ℝ) ≤ Real.log (Real.log ((m : ℝ) + 16)) + 4 := by
    have h1 : (1 : ℝ) ≤ Real.log ((m : ℝ) + 16) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ((m : ℝ) + 16) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith [Real.log_nonneg h1]
  have hη_le1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one (by positivity)]
    nlinarith
  have h1mη_nn : 0 ≤ 1 - η := by linarith
  induction tags with
  | nil =>
    refine ⟨X₀, by simp, ?_⟩
    intro x hx
    exact ⟨x, hx, ∅, by simp, by simp, by simp⟩
  | cons p rest ih =>
    rw [List.nodup_cons] at htags_nd
    rcases htags_nd with ⟨hp_not_rest, hrest_nd⟩
    have hp_mem : p ∈ Q_tag := htags_sub p List.mem_cons_self
    have hrest_sub : ∀ q ∈ rest, q ∈ Q_tag := fun q hq => htags_sub q (List.mem_cons_of_mem p hq)
    rcases ih hrest_nd hrest_sub with ⟨X_mid, hdef_mid, hsupp_mid⟩
    rcases adaptive_dilation_contraction hm4096 hmdil_lo hmdil_hi hdisj_band hband hQ'_sub hQ'_ne
      hQ'_le hpool_ge8 hp_mem X_mid with ⟨Y, hY_supp, hY_gain⟩
    refine ⟨conv_zmod X_mid Y, ?_, ?_⟩
    · have hstep : deficit_zmod (conv_zmod X_mid Y) ≤ (1 - η) * deficit_zmod X_mid := by
        dsimp [deficit_zmod, η] at hY_gain ⊢
        linarith
      calc deficit_zmod (conv_zmod X_mid Y)
          ≤ (1 - η) * deficit_zmod X_mid := hstep
        _ ≤ (1 - η) * ((1 - η) ^ rest.length * deficit_zmod X₀) :=
            mul_le_mul_of_nonneg_left hdef_mid h1mη_nn
        _ = (1 - η) ^ (p :: rest).length * deficit_zmod X₀ := by
            simp only [List.length_cons]; rw [_root_.pow_succ']; ring
    · intro x hx
      rcases suppZMod_conv_zmod X_mid Y hx with ⟨x_mid, hx_mid, y, hy, rfl⟩
      rcases hsupp_mid x_mid hx_mid with ⟨x₀, hx₀, S_mid, hS_card, hS_prop, hS_sum⟩
      have hy_ne : Y.p y ≠ 0 := (Finset.mem_filter.mp hy).2
      rcases hY_supp y hy_ne with ⟨d, hd_pos, hd_dvd, hd_ndvd, hd_lt, hd_ptag, hd_uniq, hd_eq⟩
      have hd_not_mem : d ∉ S_mid := by
        intro hd_in
        have hp_in_rest : p ∈ rest := (hS_prop d hd_in).2.2.2.2.2 p hp_mem hd_ptag
        exact hp_not_rest hp_in_rest
      refine ⟨x₀, hx₀, insert d S_mid, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hd_not_mem, hS_card, List.length_cons]
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha_mid
        · exact ⟨hd_pos, hd_dvd, hd_ndvd, hd_lt, ⟨p, List.mem_cons_self, hd_ptag⟩,
            fun q hq hqd => by rw [hd_uniq q hq hqd]; exact List.mem_cons_self⟩
        · rcases hS_prop a ha_mid with ⟨h1, h2, h3, h4, ⟨q0, hq0_rest, hq0_dvd⟩, h6⟩
          exact ⟨h1, h2, h3, h4, ⟨q0, List.mem_cons_of_mem p hq0_rest, hq0_dvd⟩,
            fun q hq hqa => List.mem_cons_of_mem p (h6 q hq hqa)⟩
      · rw [Finset.sum_insert hd_not_mem, id_eq, Nat.cast_add, hd_eq]
        rw [← hS_sum]
        ring

/-- If `deficit_zmod X < log 2`, then `M < 2 * (suppZMod X).card`. -/
private lemma deficit_lt_log_two_implies_two_mul_supp_gt {M : ℕ} [NeZero M] (X : PMF_ZMod M)
    (hdef : deficit_zmod X < Real.log 2) :
    M < 2 * (suppZMod X).card := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hsupp_ne : (suppZMod X).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : ∑ x : ZMod M, X.p x = 0 := Finset.sum_eq_zero fun x _ => by
      by_contra hne
      have : x ∈ suppZMod X := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [hemp] at this; exact Finset.notMem_empty _ this
    linarith [X.sum_one]
  have hcard_pos : (0 : ℝ) < ((suppZMod X).card : ℝ) := Nat.cast_pos.mpr hsupp_ne.card_pos
  have hH_le := Hnat_zmod_le_log_supp X
  have hlog_lt : Real.log (M : ℝ) < Real.log (2 * ((suppZMod X).card : ℝ)) := by
    rw [Real.log_mul (by norm_num) hcard_pos.ne']
    dsimp [deficit_zmod] at hdef
    linarith
  have hreal_lt : (M : ℝ) < 2 * ((suppZMod X).card : ℝ) :=
    (Real.log_lt_log_iff hM_pos (by positivity)).mp hlog_lt
  exact_mod_cast hreal_lt

/-- Pigeonhole sumset covering in `ZMod M`: if `M < |A| + |B|`, then `A + B = ZMod M`. -/
private lemma pigeonhole_sum_zmod {M : ℕ} [NeZero M] (A B : Finset (ZMod M))
    (hcard : M < A.card + B.card) (r : ZMod M) :
    ∃ a ∈ A, ∃ b ∈ B, a + b = r := by
  let B' : Finset (ZMod M) := B.image (fun b => r - b)
  have hinj : Function.Injective (fun b : ZMod M => r - b) := fun b₁ b₂ h => by
    have : r - (r - b₁) = r - (r - b₂) := congrArg (r - ·) h
    simpa using this
  have hB'_card : B'.card = B.card := Finset.card_image_of_injective B hinj
  have hnot_disj : ¬ Disjoint A B' := by
    intro hdisj
    have hle : (A ∪ B').card ≤ Fintype.card (ZMod M) := Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj, hB'_card, ZMod.card] at hle
    omega
  rw [Finset.not_disjoint_iff] at hnot_disj
  rcases hnot_disj with ⟨a, haA, haB'⟩
  rcases Finset.mem_image.mp haB' with ⟨b, hbB, hrb⟩
  exact ⟨a, haA, b, hbB, by rw [← hrb]; ring⟩

/-- After `R_cover m` steps, `(1 - η)^R * log M' < log 2` for `M' ≤ 2 ^ (6 * m)`. -/
private lemma one_sub_pow_R_cover_lt_log_two {m M' : ℕ} (hm4096 : 4096 ≤ m)
    (hM'_pos : 0 < M') (hM'_le : M' ≤ 2 ^ (6 * m)) :
    (1 - 1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))) ^ (R_cover m) *
        Real.log (M' : ℝ) < Real.log 2 := by
  set η : ℝ := 1 / (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4))
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogm_ge1 : (1 : ℝ) ≤ Real.log (m : ℝ) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (m : ℝ) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hll_ge4 : (4 : ℝ) ≤ Real.log (Real.log ((m : ℝ) + 16)) + 4 := by
    have h1 : (1 : ℝ) ≤ Real.log ((m : ℝ) + 16) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ((m : ℝ) + 16) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith [Real.log_nonneg h1]
  have hη_pos : 0 < η := by dsimp [η]; positivity
  have hη_le1 : η ≤ 1 := by dsimp [η]; rw [div_le_one (by positivity)]; nlinarith
  have h1mη_nn : 0 ≤ 1 - η := by linarith
  have h1mη_exp : 1 - η ≤ Real.exp (-η) := by linarith [Real.add_one_le_exp (-η)]
  have hpow_exp : (1 - η) ^ (R_cover m) ≤ Real.exp (-(R_cover m : ℝ) * η) := by
    calc (1 - η) ^ (R_cover m) ≤ (Real.exp (-η)) ^ (R_cover m) := pow_le_pow_left₀ h1mη_nn h1mη_exp _
      _ = Real.exp ((R_cover m : ℝ) * (-η)) := (Real.exp_nat_mul (-η) (R_cover m)).symm
      _ = Real.exp (-(R_cover m : ℝ) * η) := by ring_nf
  have hR_ge : 193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) * Real.log (12 * (m : ℝ)) ≤
      (R_cover m : ℝ) := Nat.le_ceil _
  have hRη_ge : Real.log (12 * (m : ℝ)) ≤ (R_cover m : ℝ) * η := by
    have hmul := mul_le_mul_of_nonneg_right hR_ge hη_pos.le
    have hsimp : 193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) *
        Real.log (12 * (m : ℝ)) * η = Real.log (12 * (m : ℝ)) := by
      dsimp [η]; field_simp [(by positivity : (193600 : ℝ) * Real.log (m : ℝ) *
        (Real.log (Real.log ((m : ℝ) + 16)) + 4) ≠ 0)]
    linarith
  have hexp_le : Real.exp (-(R_cover m : ℝ) * η) ≤ 1 / (12 * (m : ℝ)) := by
    calc Real.exp (-(R_cover m : ℝ) * η)
        ≤ Real.exp (-Real.log (12 * (m : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp (Real.log (12 * (m : ℝ))))⁻¹ := Real.exp_neg _
      _ = 1 / (12 * (m : ℝ)) := by rw [Real.exp_log (by positivity), one_div]
  have hlogM_le : Real.log (M' : ℝ) ≤ 6 * (m : ℝ) * Real.log 2 := by
    have hcast : (M' : ℝ) ≤ (2 : ℝ) ^ (6 * m) := by exact_mod_cast hM'_le
    calc Real.log (M' : ℝ) ≤ Real.log ((2 : ℝ) ^ (6 * m)) :=
          Real.log_le_log (Nat.cast_pos.mpr hM'_pos) hcast
      _ = ((6 * m : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (6 * m)
      _ = 6 * (m : ℝ) * Real.log 2 := by push_cast; ring
  have hlogM_nn : 0 ≤ Real.log (M' : ℝ) := Real.log_nonneg (by exact_mod_cast hM'_pos)
  calc (1 - η) ^ (R_cover m) * Real.log (M' : ℝ)
      ≤ (1 / (12 * (m : ℝ))) * (6 * (m : ℝ) * Real.log 2) :=
        mul_le_mul (hpow_exp.trans hexp_le) hlogM_le hlogM_nn (by positivity)
    _ = Real.log 2 / 2 := by field_simp [hm_pos.ne']; ring
    _ < Real.log 2 := by linarith [Real.log_two_gt_d9]

/-- For `m ≥ m1_pigeonhole`, `2 * R_cover m < m ^ 2`. -/
lemma two_mul_R_cover_lt_sq {m : ℕ} (hm : m1_pigeonhole ≤ m) :
    2 * R_cover m < m ^ 2 := by
  have hm_ge : 4 ^ 45 ≤ m := le_trans (by unfold m1_pigeonhole; omega) hm
  have hm4096 : 4096 ≤ m := le_trans (by norm_num : 4096 ≤ 4 ^ 45) hm_ge
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
  set t : ℝ := Real.sqrt (Real.sqrt (m : ℝ))
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hm_pos)
  have ht4 : t ^ 4 = (m : ℝ) := by
    have h1 : t ^ 2 = Real.sqrt (m : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (m : ℝ)) ^ 2 := by rw [h1]
      _ = (m : ℝ) := Real.sq_sqrt hm_pos.le
  have ht_ge : (1000000 : ℝ) ≤ t := by
    have h10 : (1000000 : ℝ) ^ 4 ≤ (m : ℝ) := by
      have h1 : (1000000 : ℕ) ^ 4 ≤ 4 ^ 45 := by norm_num
      have h2 : (1000000 : ℕ) ^ 4 ≤ m := le_trans h1 hm_ge
      exact_mod_cast h2
    have hsq1 : (1000000 : ℝ) ^ 2 ≤ Real.sqrt (m : ℝ) := by
      calc (1000000 : ℝ) ^ 2 = Real.sqrt (((1000000 : ℝ) ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by linarith [show ((1000000 : ℝ) ^ 2) ^ 2 = (1000000 : ℝ) ^ 4 by ring])
    calc (1000000 : ℝ) = Real.sqrt ((1000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ t := Real.sqrt_le_sqrt hsq1
  have hlog4 : Real.log (4 : ℝ) < 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; linarith [Real.log_two_lt_d9]
  have hlogm_le : Real.log (m : ℝ) ≤ t + 2 := by
    have h1 : Real.log (t / 4) ≤ t / 4 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlogt : Real.log t = Real.log (t / 4) + Real.log 4 := by
      rw [Real.log_div ht_pos.ne' (by norm_num)]; ring
    have h2 : Real.log (m : ℝ) = 4 * Real.log t := by rw [← ht4, Real.log_pow]; ring
    linarith
  have hlog12m_le : Real.log (12 * (m : ℝ)) ≤ t + 5 := by
    rw [Real.log_mul (by norm_num) hm_pos.ne']
    have hlog12 : Real.log (12 : ℝ) < 3 := by
      have h1 : (12 : ℝ) < 2 ^ 4 := by norm_num
      have h2 := Real.log_lt_log (by norm_num) h1
      rw [Real.log_pow] at h2; push_cast at h2; linarith [Real.log_two_lt_d9]
    linarith
  have hll_le : Real.log (Real.log ((m : ℝ) + 16)) + 4 ≤ t := by
    have hm16 : (m : ℝ) + 16 ≤ 2 * (m : ℝ) := by linarith
    have hlog_m16 : Real.log ((m : ℝ) + 16) ≤ t + 3 := by
      have h1 := Real.log_le_log (by positivity) hm16
      rw [Real.log_mul (by norm_num) hm_pos.ne'] at h1
      linarith [Real.log_two_lt_d9]
    have hlog16_pos : 0 < Real.log ((m : ℝ) + 16) := Real.log_pos (by linarith)
    have hdiv4 : Real.log ((t + 3) / 4) ≤ (t + 3) / 4 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlog_t3 : Real.log (t + 3) ≤ (t + 3) / 4 + 0.4 := by
      have : Real.log (t + 3) = Real.log ((t + 3) / 4) + Real.log 4 := by
        rw [Real.log_div (by positivity) (by norm_num)]; ring
      linarith
    have hle2 := Real.log_le_log hlog16_pos hlog_m16
    linarith
  have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hlog12_nn : 0 ≤ Real.log (12 * (m : ℝ)) := Real.log_nonneg (by linarith)
  have hll_nn : 0 ≤ Real.log (Real.log ((m : ℝ) + 16)) + 4 := by
    have : (1 : ℝ) ≤ Real.log ((m : ℝ) + 16) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ((m : ℝ) + 16) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith [Real.log_nonneg this]
  have hR_real : (R_cover m : ℝ) < 193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) *
      Real.log (12 * (m : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hprod_le : 2 * (193600 * Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) *
      Real.log (12 * (m : ℝ)) + 1) < (m : ℝ) ^ 2 := by
    have h1 : Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) ≤ (t + 2) * t :=
      mul_le_mul hlogm_le hll_le hll_nn (by positivity)
    have h2 : Real.log (m : ℝ) * (Real.log (Real.log ((m : ℝ) + 16)) + 4) * Real.log (12 * (m : ℝ)) ≤
        (t + 2) * t * (t + 5) := mul_le_mul h1 hlog12m_le hlog12_nn (by positivity)
    have h3 : (t + 2) * t * (t + 5) ≤ 2 * t ^ 3 := by
      have : (t + 2) * (t + 5) ≤ 2 * t ^ 2 := by nlinarith
      nlinarith
    have h4 : (t ^ 4) ^ 2 = (m : ℝ) ^ 2 := by rw [ht4]
    have h5 : (1000000 : ℝ) * t ^ 3 ≤ t ^ 4 := by nlinarith
    have h6 : t ^ 4 ≤ (t ^ 4) ^ 2 := by nlinarith
    nlinarith
  have hcast_lt : (2 * R_cover m : ℝ) < (m : ℝ) ^ 2 := by linarith
  exact_mod_cast hcast_lt

/-- **Lemma 5a (Iterated Mod-`M'` Covering on `ZMod M'`):**
    For any nonempty `Q' ⊆ Q_strip` (`M' = ∏ q ∈ Q', q`) and `2 * R_cover m ≤ Q_tag.card`,
    every residue `r : ZMod M'` is represented as the sum of `2 * R_cover m` strictly distinct
    positive divisors `d ∣ M_core m` with `¬ (M' ∣ d)` and `d < m ^ 3 * M'` (hence `S.sum id < m ^ 5 * M'`). -/
theorem mod_Mprime_covering {m m_dil : ℕ} {Q_strip Q_tag Q' : Finset ℕ}
    (hm4096 : 4096 ≤ m) (hmdil_lo : m1_pigeonhole ≤ m_dil) (hmdil_hi : m_dil ≤ m)
    (hdisj_band : Disjoint Q_strip Q_tag)
    (hband : ∀ q ∈ Q_strip ∪ Q_tag, q.Prime ∧ m / 2 < q ∧ 14 * m_dil / 25 < q ∧ q ≤ m_dil)
    (hQ'_sub : Q' ⊆ Q_strip) (hQ'_ne : Q'.Nonempty)
    (hQ'_le : Q'.card ≤ (primePool m).card / 2) (hpool_ge8 : 8 ≤ (primePool m).card)
    (hQtag_ge : 2 * R_cover m ≤ Q_tag.card)
    [NeZero (∏ q ∈ Q', q)]
    (r_target : ZMod (∏ q ∈ Q', q)) :
    ∃ S : Finset ℕ,
      S.card = 2 * R_cover m ∧
      (∀ d ∈ S, 0 < d ∧ d ∣ M_core m ∧ ¬ ((∏ q ∈ Q', q) ∣ d) ∧ d < m ^ 3 * (∏ q ∈ Q', q)) ∧
      ((S.sum id : ℕ) : ZMod (∏ q ∈ Q', q)) = r_target ∧
      S.sum id < m ^ 5 * (∏ q ∈ Q', q) := by
  revert r_target
  set R : ℕ := R_cover m
  set M' : ℕ := ∏ q ∈ Q', q
  intro r_target
  set L : List ℕ := Q_tag.toList
  have hL_nd : L.Nodup := Finset.nodup_toList Q_tag
  have hL_len : 2 * R ≤ L.length := by rw [Finset.length_toList]; exact hQtag_ge
  set tags₁ : List ℕ := L.take R
  set tags₂ : List ℕ := (L.drop R).take R
  have ht1_len : tags₁.length = R := List.length_take_of_le (by omega)
  have ht2_len : tags₂.length = R := by
    rw [List.length_take_of_le]; rw [List.length_drop]; omega
  have ht1_nd : tags₁.Nodup := hL_nd.take
  have ht2_nd : tags₂.Nodup := hL_nd.drop.take
  have ht1_sub : ∀ p ∈ tags₁, p ∈ Q_tag := fun p hp => Finset.mem_toList.mp (List.mem_of_mem_take hp)
  have ht2_sub : ∀ p ∈ tags₂, p ∈ Q_tag := fun p hp =>
    Finset.mem_toList.mp (List.mem_of_mem_drop (List.mem_of_mem_take hp))
  have ht_disj : List.Disjoint tags₁ tags₂ := by
    have hnd_app : (L.take R ++ L.drop R).Nodup := by rwa [List.take_append_drop]
    intro p hp1 hp2
    exact (List.nodup_append.mp hnd_app).2.2 p hp1 p (List.mem_of_mem_take hp2) rfl
  have hM'_dvd_prim : M' ∣ primorial m := by
    unfold primorial
    refine Finset.prod_dvd_prod_of_subset Q' ((Finset.range (m + 1)).filter Nat.Prime) id ?_
    intro q hq
    have hb := hband q (Finset.mem_union_left _ (hQ'_sub hq))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb.1⟩
  have hM'_dvd_core : M' ∣ M_core m := by
    unfold M_core
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hM'_dvd_prim _) _) _
  have hM'_pos : 0 < M' := NeZero.pos M'
  have hM'_le : M' ≤ 2 ^ (6 * m) := le_trans (Nat.le_of_dvd (M_core_pos m) hM'_dvd_core) (M_core_le_two_pow hm4096)
  have hdef0 : deficit_zmod (pointPMF (0 : ZMod M')) = Real.log (M' : ℝ) := by
    dsimp [deficit_zmod, Hnat_zmod, pointPMF]
    have h0 : ∑ x : ZMod M', Real.negMulLog (if x = 0 then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs <;> simp [Real.negMulLog_one, Real.negMulLog_zero]
    rw [h0, sub_zero]
  rcases iterated_contraction_list hm4096 hmdil_lo hmdil_hi hdisj_band hband hQ'_sub hQ'_ne
    hQ'_le hpool_ge8 tags₁ ht1_nd ht1_sub (pointPMF (0 : ZMod M')) with ⟨X₁, hdef₁, hsupp₁⟩
  rcases iterated_contraction_list hm4096 hmdil_lo hmdil_hi hdisj_band hband hQ'_sub hQ'_ne
    hQ'_le hpool_ge8 tags₂ ht2_nd ht2_sub (pointPMF (0 : ZMod M')) with ⟨X₂, hdef₂, hsupp₂⟩
  rw [ht1_len, hdef0] at hdef₁
  rw [ht2_len, hdef0] at hdef₂
  have hlt_log2 := one_sub_pow_R_cover_lt_log_two hm4096 hM'_pos hM'_le
  have hcard₁ : M' < 2 * (suppZMod X₁).card :=
    deficit_lt_log_two_implies_two_mul_supp_gt X₁ (lt_of_le_of_lt hdef₁ hlt_log2)
  have hcard₂ : M' < 2 * (suppZMod X₂).card :=
    deficit_lt_log_two_implies_two_mul_supp_gt X₂ (lt_of_le_of_lt hdef₂ hlt_log2)
  rcases pigeonhole_sum_zmod (suppZMod X₁) (suppZMod X₂) (by omega) r_target with ⟨x₁, hx₁, x₂, hx₂, hsum_r⟩
  rcases hsupp₁ x₁ hx₁ with ⟨x₀₁, hx₀₁, S₁, hS1_card, hS1_prop, hS1_sum⟩
  rcases hsupp₂ x₂ hx₂ with ⟨x₀₂, hx₀₂, S₂, hS2_card, hS2_prop, hS2_sum⟩
  have hx₀₁_zero : x₀₁ = 0 := by
    have h := (Finset.mem_filter.mp hx₀₁).2
    dsimp [pointPMF] at h
    by_contra hne; simp [hne] at h
  have hx₀₂_zero : x₀₂ = 0 := by
    have h := (Finset.mem_filter.mp hx₀₂).2
    dsimp [pointPMF] at h
    by_contra hne; simp [hne] at h
  subst hx₀₁_zero; subst hx₀₂_zero
  rw [zero_add] at hS1_sum hS2_sum
  have hdisj_S : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rcases (hS1_prop d hd1).2.2.2.2.1 with ⟨p, hp1, hpd⟩
    have hp2 : p ∈ tags₂ := (hS2_prop d hd2).2.2.2.2.2 p (ht1_sub p hp1) hpd
    exact ht_disj hp1 hp2
  refine ⟨S₁ ∪ S₂, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj_S, hS1_card, hS2_card, ht1_len, ht2_len]; omega
  · intro d hd
    rcases Finset.mem_union.mp hd with hd1 | hd2
    · rcases hS1_prop d hd1 with ⟨h1, h2, h3, h4, _, _⟩; exact ⟨h1, h2, h3, h4⟩
    · rcases hS2_prop d hd2 with ⟨h1, h2, h3, h4, _, _⟩; exact ⟨h1, h2, h3, h4⟩
  · rw [Finset.sum_union hdisj_S, Nat.cast_add]
    exact (congrArg₂ (· + ·) hS1_sum hS2_sum).trans hsum_r
  · have hcard_union : (S₁ ∪ S₂).card = 2 * R := by
      rw [Finset.card_union_of_disjoint hdisj_S, hS1_card, hS2_card, ht1_len, ht2_len]; omega
    have hsum_le : (S₁ ∪ S₂).sum id ≤ (S₁ ∪ S₂).card * (m ^ 3 * M') := by
      calc (S₁ ∪ S₂).sum id ≤ ∑ _ ∈ S₁ ∪ S₂, (m ^ 3 * M') := Finset.sum_le_sum fun d hd => by
              rcases Finset.mem_union.mp hd with hd1 | hd2
              · exact le_of_lt (hS1_prop d hd1).2.2.2.1
              · exact le_of_lt (hS2_prop d hd2).2.2.2.1
        _ = (S₁ ∪ S₂).card * (m ^ 3 * M') := by simp
    have h2R_lt : 2 * R < m ^ 2 := two_mul_R_cover_lt_sq (le_trans hmdil_lo hmdil_hi)
    have hmul_lt : 2 * R * (m ^ 3 * M') < m ^ 2 * (m ^ 3 * M') :=
      Nat.mul_lt_mul_of_pos_right h2R_lt (by positivity)
    calc (S₁ ∪ S₂).sum id ≤ 2 * R * (m ^ 3 * M') := by rwa [← hcard_union]
      _ < m ^ 2 * (m ^ 3 * M') := hmul_lt
      _ = m ^ 5 * M' := by ring

/-- Self-contained binary representation for `k < 2 ^ B`. -/
lemma binary_rep_pow2 : ∀ (B k : ℕ), k < 2 ^ B →
    ∃ S : Finset ℕ, S.card ≤ B ∧ (∀ d ∈ S, 0 < d ∧ d ∣ 2 ^ B ∧ d < 2 ^ B) ∧ S.sum id = k
  | 0, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0; exact ⟨∅, by simp, by simp, by simp⟩
  | B + 1, k, hk => by
    have hk2 : k / 2 < 2 ^ B := by rw [pow_succ] at hk; omega
    rcases binary_rep_pow2 B (k / 2) hk2 with ⟨S', hcard', hprop', hsum'⟩
    let S2 : Finset ℕ := S'.image (2 * ·)
    have hinj : Function.Injective (2 * · : ℕ → ℕ) := fun a b h => by dsimp at h; omega
    have hS2_card : S2.card = S'.card := Finset.card_image_of_injective S' hinj
    have hS2_sum : S2.sum id = 2 * (k / 2) := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [id_eq]; rw [← Finset.mul_sum]; exact congrArg (2 * ·) hsum'
    have hS2_prop : ∀ d ∈ S2, 0 < d ∧ d ∣ 2 ^ (B + 1) ∧ d < 2 ^ (B + 1) := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨a, ha, rfl⟩
      rcases hprop' a ha with ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_, ?_⟩
      · rw [_root_.pow_succ']; exact Nat.mul_dvd_mul_left 2 h2
      · rw [_root_.pow_succ']; omega
    by_cases hpar : k % 2 = 0
    · exact ⟨S2, by omega, hS2_prop, by omega⟩
    · have h1_not : (1 : ℕ) ∉ S2 := by
        intro hmem; rcases Finset.mem_image.mp hmem with ⟨a, _, ha⟩; omega
      refine ⟨insert 1 S2, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem h1_not]; omega
      · intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd2
        · exact ⟨by omega, one_dvd _, by have : 1 ≤ 2 ^ B := Nat.one_le_pow B 2 (by omega); rw [pow_succ]; omega⟩
        · exact hS2_prop d hd2
      · rw [Finset.sum_insert h1_not, id_eq, hS2_sum]; omega

/-- Greedy nonempty subset `Q' ⊆ Q_strip` with `T < m * ∏ Q'` and `∏ Q' ≤ T` whenever `m ≤ T < ∏ Q_strip`. -/
private lemma exists_greedy_prime_subset {m : ℕ} (hm1 : 1 ≤ m) (Q_strip : Finset ℕ)
    (hQ : ∀ q ∈ Q_strip, 1 ≤ q ∧ q ≤ m) {T : ℕ}
    (hm_le_T : m ≤ T) (hT_lt : T < ∏ q ∈ Q_strip, q) :
    ∃ Q' : Finset ℕ, Q' ⊆ Q_strip ∧ Q'.Nonempty ∧
      T < m * (∏ q ∈ Q', q) ∧ (∏ q ∈ Q', q) ≤ T := by
  classical
  let cands : Finset (Finset ℕ) := Q_strip.powerset.filter (fun A => (∏ q ∈ A, q) ≤ T)
  have hcands_ne : cands.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp; omega⟩⟩
  rcases Finset.exists_max_image cands Finset.card hcands_ne with ⟨Q', hQ'_mem, hQ'_max⟩
  have hQ'_sub : Q' ⊆ Q_strip := Finset.mem_powerset.mp (Finset.mem_filter.mp hQ'_mem).1
  have hQ'_le : (∏ q ∈ Q', q) ≤ T := (Finset.mem_filter.mp hQ'_mem).2
  have hQ'_ne_full : Q' ≠ Q_strip := by intro heq; subst heq; omega
  have hdiff_ne : (Q_strip \ Q').Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    exact hQ'_ne_full (Finset.Subset.antisymm hQ'_sub hemp)
  rcases hdiff_ne with ⟨q₀, hq₀_diff⟩
  have hq₀_in : q₀ ∈ Q_strip := (Finset.mem_sdiff.mp hq₀_diff).1
  have hq₀_not : q₀ ∉ Q' := (Finset.mem_sdiff.mp hq₀_diff).2
  have hgt_T : T < q₀ * (∏ q ∈ Q', q) := by
    by_contra hle; push Not at hle
    have hmem_ins : insert q₀ Q' ∈ cands := by
      rw [Finset.mem_filter, Finset.mem_powerset, Finset.prod_insert hq₀_not]
      exact ⟨Finset.insert_subset hq₀_in hQ'_sub, hle⟩
    have hcard_le := hQ'_max (insert q₀ Q') hmem_ins
    rw [Finset.card_insert_of_notMem hq₀_not] at hcard_le
    omega
  have hT_lt_m : T < m * (∏ q ∈ Q', q) :=
    lt_of_lt_of_le hgt_T (Nat.mul_le_mul_right _ (hQ q₀ hq₀_in).2)
  have hQ'_ne : Q'.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    subst hemp; simp at hT_lt_m; omega
  exact ⟨Q', hQ'_sub, hQ'_ne, hT_lt_m, hQ'_le⟩

/-- Helper: `m ^ 16 < 2 ^ (m / 4)` for `m ≥ 4096`. -/
lemma pow16_lt_two_pow_div4 {m : ℕ} (hm4096 : 4096 ≤ m) :
    m ^ 16 < 2 ^ (m / 4) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm4 : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4096
  have hlogm : Real.log (m : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hm_pos)
    rw [Real.log_sqrt hm_pos.le] at h1; linarith
  have hsqrt_le : 64 * Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
    have h64 : (64 : ℝ) ≤ Real.sqrt (m : ℝ) := by
      calc (64 : ℝ) = Real.sqrt (64 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by linarith)
    nlinarith [Real.sq_sqrt hm_pos.le]
  have hm4_ge : (m : ℝ) / 4 - 1 ≤ ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 4 * (m / 4) + 3 := by omega
    have hcast : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast this
    linarith
  -- Actually for m ≥ 4096: 16 * log m ≤ 32 * sqrt m ≤ m / 2? No, 32 * sqrt(4096) = 2048 > 1024*0.69.
  -- Use t = sqrt(sqrt m) ≥ 8: log m ≤ t + 2, so 16 * log m ≤ 16 * (t + 2) ≤ 20 * t, while m = t^4 ≥ 512 * t!
  set t : ℝ := Real.sqrt (Real.sqrt (m : ℝ))
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hm_pos)
  have ht_ge8 : (8 : ℝ) ≤ t := by
    have hsq1 : (64 : ℝ) ≤ Real.sqrt (m : ℝ) := by
      calc (64 : ℝ) = Real.sqrt (64 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by linarith)
    calc (8 : ℝ) = Real.sqrt (8 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ t := Real.sqrt_le_sqrt (by linarith)
  have ht4 : t ^ 4 = (m : ℝ) := by
    have h1 : t ^ 2 = Real.sqrt (m : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (m : ℝ)) ^ 2 := by rw [h1]
      _ = (m : ℝ) := Real.sq_sqrt hm_pos.le
  have hlog4 : Real.log (4 : ℝ) < 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; linarith [Real.log_two_lt_d9]
  have hlogm_t : Real.log (m : ℝ) ≤ t + 2 := by
    have h1 : Real.log (t / 4) ≤ t / 4 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlogt : Real.log t = Real.log (t / 4) + Real.log 4 := by
      rw [Real.log_div ht_pos.ne' (by norm_num)]; ring
    have h2 : Real.log (m : ℝ) = 4 * Real.log t := by rw [← ht4, Real.log_pow]; ring
    linarith
  have h512 : 512 * t ≤ (m : ℝ) := by
    have h1 : (64 : ℝ) ≤ t ^ 2 := by nlinarith
    have h2 : (512 : ℝ) ≤ t ^ 3 := by nlinarith
    have h3 : 512 * t ≤ t ^ 3 * t := mul_le_mul_of_nonneg_right h2 ht_pos.le
    linarith [show t ^ 3 * t = t ^ 4 by ring]
  have hlog_lt : Real.log ((m : ℝ) ^ 16) < Real.log ((2 : ℝ) ^ (m / 4)) := by
    rw [Real.log_pow, Real.log_pow]
    have h2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have hreal_lt : (m : ℝ) ^ 16 < (2 : ℝ) ^ (m / 4) :=
    (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog_lt
  exact_mod_cast hreal_lt

/-- **Lemma 5b (Exact Digit Representation in `M_core m`):**
    For any `r < (∏ q ∈ Q_strip, q) / m ^ 5`, `r` is a sum of at most
    `2 * R_cover m + (6 * Nat.log 2 m + 8)` strictly distinct positive divisors of `M_core m`. -/
theorem exact_digit_rep_primefield {m m_dil : ℕ} {Q_strip Q_tag : Finset ℕ}
    (hm4096 : 4096 ≤ m) (hmdil_lo : m1_pigeonhole ≤ m_dil) (hmdil_hi : m_dil ≤ m)
    (hdisj_band : Disjoint Q_strip Q_tag)
    (hband : ∀ q ∈ Q_strip ∪ Q_tag, q.Prime ∧ m / 2 < q ∧ 14 * m_dil / 25 < q ∧ q ≤ m_dil)
    (hQstrip_le : Q_strip.card ≤ (primePool m).card / 2) (hpool_ge8 : 8 ≤ (primePool m).card)
    (hQtag_ge : 2 * R_cover m ≤ Q_tag.card)
    {r : ℕ} (hr_lt : r < (∏ q ∈ Q_strip, q) / m ^ 5) :
    ∃ S : Finset ℕ,
      (∀ d ∈ S, 0 < d ∧ d ∣ M_core m) ∧
      S.sum id = r ∧
      S.card ≤ 2 * R_cover m + (6 * Nat.log 2 m + 8) := by
  have hm_pow_lt : 2 * m ^ 6 < 2 ^ (6 * Nat.log 2 m + 8) := by
    have hm_lt : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have hm6 : m ^ 6 < (2 ^ (Nat.log 2 m + 1)) ^ 6 := Nat.pow_lt_pow_left hm_lt (by norm_num : 6 ≠ 0)
    have hpow_eq : 2 * (2 ^ (Nat.log 2 m + 1)) ^ 6 = 2 ^ (6 * Nat.log 2 m + 7) := by
      rw [← pow_mul, ← _root_.pow_succ']; congr 1; ring
    have hstep : 2 ^ (6 * Nat.log 2 m + 7) ≤ 2 ^ (6 * Nat.log 2 m + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left hm6 (by norm_num)) hpow_eq) hstep
  have hB_le_div4 : 6 * Nat.log 2 m + 8 ≤ m / 4 := by
    have hpow16 := pow16_lt_two_pow_div4 hm4096
    have h2pow : 2 ^ (Nat.log 2 m) ≤ m := Nat.pow_log_le_self 2 (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hm4096))
    have h2_8 : 2 ^ 8 ≤ m := le_trans (by norm_num) hm4096
    have h1 : 2 ^ (6 * Nat.log 2 m + 8) ≤ m ^ 7 := by
      rw [pow_add, mul_comm 6, pow_mul]
      calc (2 ^ Nat.log 2 m) ^ 6 * 2 ^ 8 ≤ m ^ 6 * m := Nat.mul_le_mul (Nat.pow_le_pow_left h2pow 6) h2_8
        _ = m ^ 7 := by ring
    have h2 : m ^ 7 ≤ m ^ 16 := Nat.pow_le_pow_right (le_trans (by norm_num) hm4096) (by norm_num)
    have hlt : 2 ^ (6 * Nat.log 2 m + 8) < 2 ^ (m / 4) := lt_of_le_of_lt (h1.trans h2) hpow16
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt)
  by_cases hr_small : r < 2 * m ^ 6
  · rcases binary_rep_pow2 (6 * Nat.log 2 m + 8) r (lt_trans hr_small hm_pow_lt) with ⟨S, hcard, hprop, hsum⟩
    refine ⟨S, ?_, hsum, by omega⟩
    intro d hd
    rcases hprop d hd with ⟨hpos, hdvd, _⟩
    refine ⟨hpos, dvd_trans hdvd (dvd_trans (Nat.pow_dvd_pow 2 hB_le_div4) ?_)⟩
    unfold M_core
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  · push Not at hr_small
    set T : ℕ := r / (2 * m ^ 5)
    have hm_le_T : m ≤ T := by
      exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith [show m * (2 * m ^ 5) = 2 * m ^ 6 by ring])
    have hT_lt : T < ∏ q ∈ Q_strip, q := by
      have h1 : T ≤ r / m ^ 5 := Nat.div_le_div_left (Nat.le_mul_of_pos_left (m ^ 5) (by norm_num)) (by positivity)
      have h2 : r / m ^ 5 ≤ r := Nat.div_le_self r _
      have h3 : r < (∏ q ∈ Q_strip, q) / m ^ 5 := hr_lt
      have h4 : (∏ q ∈ Q_strip, q) / m ^ 5 ≤ ∏ q ∈ Q_strip, q := Nat.div_le_self _ _
      omega
    have hQ_info : ∀ q ∈ Q_strip, 1 ≤ q ∧ q ≤ m := fun q hq => by
      have hb := hband q (Finset.mem_union_left _ hq)
      exact ⟨hb.1.pos, le_trans hb.2.2.2 hmdil_hi⟩
    rcases exists_greedy_prime_subset (by omega : 1 ≤ m) Q_strip hQ_info hm_le_T hT_lt with ⟨Q', hQ'_sub, hQ'_ne, hT_lt_m, hM'_le_T⟩
    set M' : ℕ := ∏ q ∈ Q', q
    have hM'_pos : 0 < M' := Finset.prod_pos fun q hq => (hband q (Finset.mem_union_left _ (hQ'_sub hq))).1.pos
    have : NeZero M' := ⟨hM'_pos.ne'⟩
    have hQ'_le : Q'.card ≤ (primePool m).card / 2 := le_trans (Finset.card_le_card hQ'_sub) hQstrip_le
    rcases mod_Mprime_covering hm4096 hmdil_lo hmdil_hi hdisj_band hband hQ'_sub hQ'_ne hQ'_le
      hpool_ge8 hQtag_ge (r : ZMod M') with ⟨S₁, hS1_card, hS1_prop, hS1_mod, hS1_sum_lt⟩
    -- S₁.sum id < m^5 * M' ≤ m^5 * T ≤ r / 2 < r
    have hM'_mul_le : 2 * m ^ 5 * M' ≤ r := by
      have h1 : M' * (2 * m ^ 5) ≤ T * (2 * m ^ 5) := Nat.mul_le_mul_right _ hM'_le_T
      have h2 : T * (2 * m ^ 5) ≤ r := Nat.div_mul_le_self r (2 * m ^ 5)
      linarith [mul_comm M' (2 * m ^ 5)]
    have hS1_le_r : S₁.sum id ≤ r := by
      have hlt' : S₁.sum id < m ^ 5 * M' := hS1_sum_lt
      have : m ^ 5 * M' ≤ 2 * m ^ 5 * M' := by rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num)
      omega
    have hdvd_diff : M' ∣ r - S₁.sum id := by
      have hmod : S₁.sum id % M' = r % M' := by
        have := (ZMod.natCast_eq_natCast_iff' (S₁.sum id) r M').mp hS1_mod
        exact this
      have h1 := Nat.div_add_mod r M'
      have h2 := Nat.div_add_mod (S₁.sum id) M'
      refine ⟨r / M' - S₁.sum id / M', ?_⟩
      rw [Nat.mul_sub]; omega
    set k : ℕ := (r - S₁.sum id) / M'
    have hk_eq : S₁.sum id + M' * k = r := by
      have hmul : M' * k = r - S₁.sum id := Nat.mul_div_cancel' hdvd_diff
      omega
    -- k ≤ r / M' < 2 * m ^ 6? Let's check: T < m * M', and r < (T + 1) * (2 * m^5) ≤ 2 * T * (2 * m^5) = 4 * m^5 * T < 4 * m^6 * M'?
    -- Even sharper: T + 1 ≤ m * M', so r < (T + 1) * (2 * m^5) ≤ m * M' * (2 * m^5) = 2 * m^6 * M'!
    have hk_lt : k < 2 * m ^ 6 := by
      have hT1 : T + 1 ≤ m * M' := hT_lt_m
      have hr_ub : r < (T + 1) * (2 * m ^ 5) := by
        have := Nat.lt_div_mul_add (a := r) (b := 2 * m ^ 5) (by positivity)
        dsimp [T]
        linarith
      have hmul_lt : M' * k < M' * (2 * m ^ 6) := by
        calc M' * k ≤ r := by omega
          _ < (T + 1) * (2 * m ^ 5) := hr_ub
          _ ≤ (m * M') * (2 * m ^ 5) := Nat.mul_le_mul_right _ hT1
          _ = M' * (2 * m ^ 6) := by ring
      exact Nat.lt_of_mul_lt_mul_left hmul_lt
    rcases binary_rep_pow2 (6 * Nat.log 2 m + 8) k (lt_trans hk_lt hm_pow_lt) with ⟨S₂_raw, hS2_card, hS2_prop, hS2_sum⟩
    let S₂ : Finset ℕ := S₂_raw.image (M' * ·)
    have hinj : Function.Injective (M' * · : ℕ → ℕ) := fun a b h => Nat.eq_of_mul_eq_mul_left hM'_pos h
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      rcases Finset.mem_image.mp hd2 with ⟨a, _, rfl⟩
      exact (hS1_prop (M' * a) hd1).2.2.1 (dvd_mul_right M' a)
    have hM'_dvd_prim : M' ∣ primorial m := by
      unfold primorial
      refine Finset.prod_dvd_prod_of_subset Q' ((Finset.range (m + 1)).filter Nat.Prime) id ?_
      intro q hq
      have hb := hband q (Finset.mem_union_left _ (hQ'_sub hq))
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb.1⟩
    refine ⟨S₁ ∪ S₂, ?_, ?_, ?_⟩
    · intro d hd
      rcases Finset.mem_union.mp hd with hd1 | hd2
      · exact ⟨(hS1_prop d hd1).1, (hS1_prop d hd1).2.1⟩
      · rcases Finset.mem_image.mp hd2 with ⟨a, ha, rfl⟩
        rcases hS2_prop a ha with ⟨ha_pos, ha_dvd, _⟩
        refine ⟨Nat.mul_pos hM'_pos ha_pos, ?_⟩
        have h1 : M' * a ∣ primorial m * 2 ^ (m / 4) :=
          Nat.mul_dvd_mul hM'_dvd_prim (dvd_trans ha_dvd (Nat.pow_dvd_pow 2 hB_le_div4))
        rw [mul_comm (primorial m)] at h1
        unfold M_core
        exact dvd_trans h1 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_refl _) _) _)
    · rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [id_eq] at hS2_sum ⊢; rw [← Finset.mul_sum, hS2_sum]; exact hk_eq
    · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective S₂_raw hinj, hS1_card]
      omega

end Erdos18
