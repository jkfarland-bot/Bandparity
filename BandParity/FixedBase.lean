module

public import BandParity.Basic

@[expose] public section

/-!
# The fixed-base collapse (Proposition 4.1)

For a multiplicative character `χ` modulo a prime `p` with values in any commutative ring and
for `b` prime to `p`, write `T χ = ∑ χ(n) n` (sum over `0 ≤ n < p`) and
`floorSum χ b = ∑ χ(n) ⌊b n / p⌋`. Then

  `p · χ(b) · floorSum χ b = (b · χ(b) - 1) · T χ`     (`fixed_base_collapse`).

Since `T χ = p · B₁,χ`, dividing by `p · χ(b)` gives the survey's
`∑ χ(n) ⌊bn/p⌋ = (b - χ̄(b)) B₁,χ`, which is Proposition 4.1 with `χ` and `χ̄` exchanged.
The proof is the bijective substitution `m = b n`, which is all the proposition says.

Specialization (Remark in §2.2): for an odd character and `b = 2` this is the case
`m = 1, N = p, r = 2` of the Szmidt–Urbanowicz–Zagier formula in its conjugated form,
`∑_{0<n<p/2} χ(n) = (χ̄(2) - 2) B₁,χ` (`half_sum`). The conjugated form is the one used by
Girstmair; nothing here is new.
-/

namespace BandParity

open Finset

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

/-- `T χ = ∑_{n mod p} χ(n) n`, with `n` its least nonnegative residue; `T χ = p · B₁,χ`. -/
def T (χ : MulChar (ZMod p) R) : R := ∑ n : ZMod p, χ n * (n.val : R)

/-- `∑_{n mod p} χ(n) ⌊b n / p⌋`. -/
def floorSum (χ : MulChar (ZMod p) R) (b : ZMod p) : R :=
  ∑ n : ZMod p, χ n * ((b.val * n.val / p : ℕ) : R)

/-- **Proposition 4.1 (fixed-base collapse).** -/
theorem fixed_base_collapse (χ : MulChar (ZMod p) R) {b : ZMod p} (hb : b ≠ 0) :
    (p : R) * χ b * floorSum χ b = ((b.val : R) * χ b - 1) * T χ := by
  -- the substitution `m = b n`
  have hsub : χ b * ∑ n : ZMod p, χ n * ((b * n).val : R) = T χ := by
    rw [Finset.mul_sum]
    unfold T
    refine Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ fun n => ?_
    simp only [Equiv.mulLeft₀_apply, map_mul]; ring
  -- `(b n).val = b.val n.val - p ⌊b.val n.val / p⌋`
  have hval : ∀ n : ZMod p, ((b * n).val : R) =
      (b.val : R) * n.val - p * ((b.val * n.val / p : ℕ) : R) := by
    intro n
    rw [ZMod.val_mul, eq_sub_iff_add_eq]
    have h := congrArg (fun x : ℕ => (x : R)) (Nat.mod_add_div (b.val * n.val) p)
    push_cast at h
    exact h
  have : ∑ n : ZMod p, χ n * ((b * n).val : R) = (b.val : R) * T χ - p * floorSum χ b := by
    unfold T floorSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hval]; ring
  rw [this] at hsub
  linear_combination -hsub

/-- For `n ≠ 0`, `(-n).val = p - n.val`. -/
lemma val_neg_of_ne_zero {n : ZMod p} (hn : n ≠ 0) : (-n).val = p - n.val := by
  have := ZMod.val_lt n
  have h := ZMod.neg_val n
  simpa [hn] using h

/-- **The half-range sum** (the case `m = 1`, `N = p`, `r = 2` of SUZ (6), conjugated form).
For an odd character, `p · χ(2) · ∑_{0 < n < p/2} χ(n) = (1 - 2 χ(2)) · T χ`, i.e.
`∑_{0<n<p/2} χ(n) = (χ̄(2) - 2) B₁,χ`. -/
theorem half_sum (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hodd : χ (-1) = -1) :
    (p : R) * χ 2 * ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), χ n =
      (1 - 2 * χ 2) * T χ := by
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hpodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have h2val : (2 : ZMod p).val = 2 := by
    have : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast,
      Nat.mod_eq_of_lt this]
  have key := fixed_base_collapse χ h20
  rw [h2val] at key
  -- `floorSum χ 2 = ∑_{2n ≥ p} χ n = - ∑_{2n < p} χ n`
  have hfl : floorSum χ 2 = -∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), χ n := by
    unfold floorSum
    rw [h2val]
    have h1 : ∀ n : ZMod p, χ n * ((2 * n.val / p : ℕ) : R) =
        if p ≤ 2 * n.val then χ n else 0 := by
      intro n
      have hn := ZMod.val_lt n
      by_cases h : p ≤ 2 * n.val
      · rw [show 2 * n.val / p = 1 from Nat.div_eq_of_lt_le (by omega) (by omega)]
        simp [h]
      · rw [Nat.div_eq_of_lt (by omega)]; simp [h]
    simp_rw [h1]
    rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun n => ?_
    simp only [Equiv.neg_apply]
    by_cases hn0 : n = 0
    · subst hn0; simp [MulChar.map_zero]
    · rw [val_neg_of_ne_zero hn0]
      have hn := ZMod.val_lt n
      have hχn : χ (-n) = -χ n := by
        rw [neg_eq_neg_one_mul, map_mul, hodd, neg_one_mul]
      by_cases h : p ≤ 2 * n.val
      · have h' : 2 * (p - n.val) < p := by omega
        simp [h, h', hχn]
      · have h' : ¬ 2 * (p - n.val) < p := by omega
        simp [h, h']
  rw [hfl] at key
  linear_combination -key

end BandParity
