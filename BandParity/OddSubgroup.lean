module

public import BandParity.Matching

@[expose] public section

/-!
# The odd-subgroup congruence (Theorem B)

Let `N ≥ 3` be odd, `H` a subgroup of `(ℤ/N)ˣ` of odd order `h`, `X = xH` a coset and `e ≥ 2`
even. For a unit `u` write `s(u) = (-1)^⟨u⟩`, `ε(u) = (-1)^{⌊⟨u⟩^e/N⌋}`, and let
`α(S)` count the elements of `S` with odd least residue. Since `-1 ∉ H`, the cosets `X` and `-X`
are disjoint, and each pair `{u, -u}` has one member below `N/2`. The band-parity sum of the pair
of cosets is

  `T = ∑_{0 < n < N/2, n ∈ X ∪ (-X)} σ(n) ε(n)`,  `σ = 1` on `X`, `-1` on `-X`.

This file proves

* `cosetBandSum_eq`: `T = ∑_{u ∈ X} s(u) s(u^e)` (the representative identity);
* `odd_subgroup_congruence`: `T ≡ h - 2 α(X) - 2 α(Y) (mod 4)`, `Y = X^e`.

No primality, cyclicity, character, Bernoulli number or class number enters.
-/

namespace BandParity

open Finset

variable {N : ℕ} [NeZero N]

/-- The parity sign `s(u) = (-1)^⟨u⟩` of a unit modulo `N`. -/
def uSign (u : (ZMod N)ˣ) : ℤ := (-1) ^ (u : ZMod N).val

/-- The band sign `ε(u) = (-1)^{⌊⟨u⟩^e / N⌋}`. -/
def bandSignPow (e : ℕ) (u : (ZMod N)ˣ) : ℤ := (-1) ^ ((u : ZMod N).val ^ e / N)

/-- The coset `xH` as a finite set of units. -/
def coset (H : Subgroup (ZMod N)ˣ) [DecidablePred (· ∈ H)] (x : (ZMod N)ˣ) :
    Finset (ZMod N)ˣ :=
  univ.filter (fun u => x⁻¹ * u ∈ H)

/-- `α(S)`: the number of elements of `S` whose least residue is odd. -/
def oddCount (S : Finset (ZMod N)ˣ) : ℕ :=
  (S.filter (fun u : (ZMod N)ˣ => Odd ((u : ZMod N).val))).card

/-- The band-parity sum `T^{(e)}_{H,x}(N)` of the pair of cosets `xH ∪ (-xH)` over `(0, N/2)`. -/
def cosetBandSum (H : Subgroup (ZMod N)ˣ) [DecidablePred (· ∈ H)] (x : (ZMod N)ˣ) (e : ℕ) :
    ℤ :=
  ∑ u ∈ univ.filter (fun u : (ZMod N)ˣ =>
      2 * (u : ZMod N).val < N ∧ (x⁻¹ * u ∈ H ∨ x⁻¹ * (-u) ∈ H)),
    (if x⁻¹ * u ∈ H then 1 else -1) * bandSignPow e u

omit [NeZero N] in
lemma uSign_eq (u : (ZMod N)ˣ) : uSign u = 1 ∨ uSign u = -1 := neg_one_pow_eq_or ℤ _

section Odd

variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3

omit [NeZero N] hN in
lemma unit_val_ne_zero (u : (ZMod N)ˣ) : (u : ZMod N).val ≠ 0 := by
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
  intro h; exact u.ne_zero ((ZMod.val_eq_zero _).1 h)

lemma uSign_neg (u : (ZMod N)ˣ) : uSign (-u) = -uSign u := by
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
  unfold uSign
  rw [Units.val_neg, ZMod.neg_val]; simp only [u.ne_zero, ↓reduceIte]
  have hv := ZMod.val_lt (u : ZMod N)
  have h : (-1 : ℤ) ^ (N - (u : ZMod N).val) * (-1) ^ (u : ZMod N).val = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hv.le, hN.neg_one_pow]
  rcases neg_one_pow_eq_or ℤ (u : ZMod N).val with h' | h' <;> rw [h'] at h ⊢ <;> linarith

omit hN3 in
/-- **Parity dictionary.** `ε(u) = s(u) s(u^e)` for `e ≥ 1`. -/
lemma bandSignPow_eq {e : ℕ} (he0 : e ≠ 0) (u : (ZMod N)ˣ) :
    bandSignPow e u = uSign u * uSign (u ^ e) := by
  unfold bandSignPow uSign
  set v := (u : ZMod N).val with hv
  have hval : ((u ^ e : (ZMod N)ˣ) : ZMod N).val = v ^ e % N := by
    rw [Units.val_pow_eq_pow_val, show (u : ZMod N) = ((v : ℕ) : ZMod N) by
      rw [hv, ZMod.natCast_zmod_val], ← Nat.cast_pow, ZMod.val_natCast]
  rw [hval]
  have h1 : (-1 : ℤ) ^ (v ^ e) = (-1) ^ v := by
    rcases Nat.even_or_odd v with h | h
    · rw [h.neg_one_pow, (Nat.even_pow.2 ⟨h, he0⟩).neg_one_pow]
    · rw [h.neg_one_pow, (h.pow).neg_one_pow]
  have h2 : (-1 : ℤ) ^ (v ^ e) = (-1) ^ (v ^ e / N) * (-1) ^ (v ^ e % N) := by
    conv_lhs => rw [← Nat.div_add_mod (v ^ e) N]
    rw [pow_add, pow_mul, hN.neg_one_pow]
  have hr : (-1 : ℤ) ^ (v ^ e % N) * (-1) ^ (v ^ e % N) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have E := h1.symm.trans h2
  linear_combination (-((-1 : ℤ) ^ (v ^ e % N))) * E + (-((-1 : ℤ) ^ (v ^ e / N))) * hr

variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hH

omit [NeZero N] hN [DecidablePred (· ∈ H)] in
lemma neg_one_not_mem : (-1 : (ZMod N)ˣ) ∉ H := by
  intro hm
  have : Fact (2 < N) := ⟨by omega⟩
  have hne : (-1 : (ZMod N)ˣ) ≠ 1 := by
    intro h
    exact ZMod.neg_one_ne_one (congrArg Units.val h)
  have hord : orderOf (-1 : (ZMod N)ˣ) = 2 :=
    orderOf_eq_prime (by rw [neg_one_sq]) hne
  have := Subgroup.orderOf_dvd_natCard H hm
  rw [hord] at this
  exact (Nat.not_even_iff_odd.2 hH) (even_iff_two_dvd.2 this)

omit [NeZero N] hN [DecidablePred (· ∈ H)] in
lemma not_both (x u : (ZMod N)ˣ) : ¬ (x⁻¹ * u ∈ H ∧ -(x⁻¹ * u) ∈ H) := by
  rintro ⟨h1, h2⟩
  apply neg_one_not_mem hN3 hH
  have := H.mul_mem (H.inv_mem h1) h2
  rwa [mul_neg, inv_mul_cancel] at this

/-- **Representative identity.** `T = ∑_{u ∈ xH} s(u) s(u^e)` for even `e ≥ 2`. -/
theorem cosetBandSum_eq' (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e = ∑ u ∈ coset H x, uSign u * uSign (u ^ e) := by
  set G : (ZMod N)ˣ → ℤ := fun u => uSign u * uSign (u ^ e) with hG
  have hGneg : ∀ u, G (-u) = -G u := by
    intro u; simp only [hG, uSign_neg hN hN3, he.neg_pow, neg_mul]
  have hNodd : N % 2 = 1 := Nat.odd_iff.1 hN
  -- split the defining sum according to `X` and `-X`
  have hsplit : cosetBandSum H x e =
      ∑ u : (ZMod N)ˣ, (if 2 * (u : ZMod N).val < N ∧ x⁻¹ * u ∈ H then G u else 0) +
      ∑ u : (ZMod N)ˣ, (if 2 * (u : ZMod N).val < N ∧ -(x⁻¹ * u) ∈ H then -G u else 0) := by
    unfold cosetBandSum
    simp only [mul_neg]
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hnb := not_both hN3 hH x u
    rw [bandSignPow_eq hN he0]
    by_cases hl : 2 * (u : ZMod N).val < N
    · by_cases h1 : x⁻¹ * u ∈ H
      · have h2 : -(x⁻¹ * u) ∉ H := fun h2 => hnb ⟨h1, h2⟩
        simp [hl, h1, h2, hG]
      · by_cases h2 : -(x⁻¹ * u) ∈ H
        · simp [hl, h1, h2, hG]
        · simp [hl, h1, h2]
    · simp [hl]
  -- reflect the second sum by `u ↦ -u`
  have hrefl : ∑ u : (ZMod N)ˣ, (if 2 * (u : ZMod N).val < N ∧ -(x⁻¹ * u) ∈ H then -G u else 0) =
      ∑ u : (ZMod N)ˣ, (if ¬ 2 * (u : ZMod N).val < N ∧ x⁻¹ * u ∈ H then G u else 0) := by
    refine Fintype.sum_equiv (Equiv.neg (ZMod N)ˣ) _ _ fun u => ?_
    simp only [Equiv.neg_apply, mul_neg, hGneg]
    have hv := ZMod.val_lt (u : ZMod N)
    have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
    have hnv : (-(u : ZMod N)).val = N - (u : ZMod N).val := by
      rw [ZMod.neg_val]; simp only [u.ne_zero, ↓reduceIte]
    have hu0 := unit_val_ne_zero hN3 u
    by_cases hl : 2 * (u : ZMod N).val < N
    · have h' : N ≤ 2 * (-(u : ZMod N)).val := by rw [hnv]; omega
      simp [hl, h']
    · have h' : ¬ N ≤ 2 * (-(u : ZMod N)).val := by rw [hnv]; omega
      simp [hl, h']
  rw [hsplit, hrefl, ← Finset.sum_add_distrib, coset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hl : 2 * (u : ZMod N).val < N <;> by_cases h1 : x⁻¹ * u ∈ H <;> simp [hl, h1, hG]

omit hN hN3 hH in
lemma card_coset (x : (ZMod N)ˣ) : (coset H x).card = Nat.card H := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_nbij' (fun u => x⁻¹ * u) (fun k => x * k) ?_ ?_ ?_ ?_
  · intro u hu; simpa [coset] using hu
  · intro k hk; simpa [coset] using hk
  · intro u _; simp
  · intro k _; simp

omit [NeZero N] hN hN3 hH in
lemma sum_uSign (S : Finset (ZMod N)ˣ) :
    ∑ u ∈ S, uSign u = (S.card : ℤ) - 2 * oddCount S := by
  unfold oddCount
  have : ∀ u : (ZMod N)ˣ, uSign u = 1 - 2 * (if Odd (u : ZMod N).val then 1 else 0) := by
    intro u
    unfold uSign
    rcases Nat.even_or_odd (u : ZMod N).val with h | h
    · rw [h.neg_one_pow]; split_ifs with hh
      · exact absurd hh (Nat.not_odd_iff_even.2 h)
      · ring
    · rw [h.neg_one_pow]; split_ifs; ring
  rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp

/-- The kernel of the `e`-th power map on `H`. -/
def powKer (H : Subgroup (ZMod N)ˣ) [DecidablePred (· ∈ H)] (e : ℕ) : Finset (ZMod N)ˣ :=
  univ.filter (fun k => k ∈ H ∧ k ^ e = 1)

omit hN hN3 in
lemma odd_card_powKer (e : ℕ) : Odd (powKer H e).card := by
  classical
  let K : Subgroup (ZMod N)ˣ := H ⊓ (powMonoidHom e).ker
  have hK : (powKer H e).card = Nat.card K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext k
    simp [powKer, K, Subgroup.mem_inf, MonoidHom.mem_ker]
  have hdvd : Nat.card K ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_left
  rw [hK]
  exact Odd.of_dvd_nat hH hdvd

omit hN hN3 hH in
/-- Every fibre of `u ↦ u^e` on `xH` has the size of the kernel. -/
lemma card_fibre (x : (ZMod N)ˣ) (e : ℕ) {u₀ : (ZMod N)ˣ} (hu₀ : u₀ ∈ coset H x) :
    ((coset H x).filter (fun u => u ^ e = u₀ ^ e)).card = (powKer H e).card := by
  symm
  have hu' : x⁻¹ * u₀ ∈ H := by simpa [coset] using hu₀
  refine Finset.card_nbij' (fun k => u₀ * k) (fun u => u₀⁻¹ * u) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_coe, powKer, coset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hk ⊢
    refine ⟨by rw [← mul_assoc]; exact H.mul_mem hu' hk.1, by rw [mul_pow, hk.2, mul_one]⟩
  · intro u hu
    simp only [Finset.mem_coe, powKer, coset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hu ⊢
    refine ⟨?_, by rw [mul_pow, inv_pow, hu.2, inv_mul_cancel]⟩
    have := H.mul_mem (H.inv_mem hu') hu.1
    rwa [mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc x, mul_inv_cancel, one_mul] at this
  · intro k _; simp
  · intro u _; simp

omit hN hN3 hH in
/-- Counting through the power map: `#{u ∈ X : P(u^e)} = d · #{y ∈ X^e : P y}`. -/
lemma card_filter_pow (x : (ZMod N)ˣ) (e : ℕ) (P : (ZMod N)ˣ → Prop) [DecidablePred P] :
    ((coset H x).filter (fun u => P (u ^ e))).card =
      (powKer H e).card * (((coset H x).image (· ^ e)).filter P).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := (· ^ e))
    (t := ((coset H x).image (· ^ e)).filter P)
    (fun u hu => by
      simp only [Finset.mem_coe, Finset.mem_filter] at hu ⊢
      exact ⟨Finset.mem_image_of_mem _ hu.1, hu.2⟩)]
  rw [Finset.sum_congr rfl (g := fun _ => (powKer H e).card), Finset.sum_const, smul_eq_mul,
    mul_comm]
  intro y hy
  simp only [mem_filter, mem_image] at hy
  obtain ⟨⟨u₀, hu₀, rfl⟩, hP⟩ := hy
  rw [← card_fibre x e hu₀, Finset.filter_filter]
  congr 1; ext u
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, by rw [h3]; exact hP, h3⟩

/-- **Theorem B (the odd-subgroup congruence).** For odd `N ≥ 3`, a subgroup `H` of `(ℤ/N)ˣ` of
odd order `h`, a coset `X = xH` and even `e ≥ 2`,
`T^{(e)}_{H,x}(N) ≡ h - 2 α(X) - 2 α(X^e) (mod 4)`. -/
theorem odd_subgroup_congruence' (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e ≡
      (Nat.card H : ℤ) - 2 * oddCount (coset H x) - 2 * oddCount ((coset H x).image (· ^ e))
      [ZMOD 4] := by
  rw [cosetBandSum_eq' hN hN3 hH x he he0]
  have hm := sum_sign_mul_modEq (coset H x) uSign (fun u => uSign (u ^ e))
    (fun u _ => uSign_eq u) (fun u _ => uSign_eq _)
  have h1 := sum_uSign (coset H x)
  have h2 : ∑ u ∈ coset H x, uSign (u ^ e) =
      ((coset H x).card : ℤ) - 2 * ((powKer H e).card * oddCount ((coset H x).image (· ^ e))) := by
    have : ∀ u : (ZMod N)ˣ, uSign (u ^ e) =
        1 - 2 * (if Odd ((u ^ e : (ZMod N)ˣ) : ZMod N).val then 1 else 0) := by
      intro u; unfold uSign
      rcases Nat.even_or_odd ((u ^ e : (ZMod N)ˣ) : ZMod N).val with h | h
      · rw [h.neg_one_pow]; split_ifs with hh
        · exact absurd hh (Nat.not_odd_iff_even.2 h)
        · ring
      · rw [h.neg_one_pow]; split_ifs; ring
    have hcf := card_filter_pow (H := H) x e (fun y : (ZMod N)ˣ => Odd (y : ZMod N).val)
    rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole, oddCount]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcf]; push_cast; ring
  rw [h1, h2, card_coset] at hm
  refine hm.trans ?_
  obtain ⟨c, hc⟩ := odd_card_powKer hH e
  rw [hc]
  exact Int.modEq_iff_dvd.2 ⟨c * oddCount ((coset H x).image (· ^ e)), by push_cast; ring⟩

end Odd

end BandParity
