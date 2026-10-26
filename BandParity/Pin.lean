module

public import BandParity.Basic

@[expose] public section

/-!
# The pin `χ(2) = i` (Definition 3.3)

For `p ≡ 5 (mod 8)` there is exactly one quartic character modulo `p` with values in `ℤ[i]`
satisfying `χ 2 = i` (`existsUnique_pinned`). Any quartic character is either `χ` or its
conjugate `χ ^ 3` (`quartic_eq_or_eq_pow_three`).
-/

namespace BandParity

variable {p : ℕ} [hp : Fact p.Prime]

lemma isPrimitiveRoot_gi : IsPrimitiveRoot gi 4 := by
  refine IsPrimitiveRoot.mk_of_lt gi (by norm_num) gi_pow_four fun l hl0 hl4 h => ?_
  interval_cases l
  · exact absurd (pow_one gi ▸ h) gi_ne_one
  · rw [gi_sq] at h; exact absurd h neg_one_ne_one
  · rw [pow_succ, gi_sq] at h
    have := congrArg Zsqrtd.re h; simp at this

omit hp in
lemma orderOf_pow_three {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) :
    orderOf (χ ^ 3) = 4 := by
  rw [orderOf_pow' χ (by norm_num), hχ]; rfl

/-- Two quartic characters with the same value at a generator coincide. -/
lemma quartic_ext {χ ψ : MulChar (ZMod p) GaussianInt} {g : (ZMod p)ˣ}
    (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) (h : χ g = ψ g) : χ = ψ := by
  refine MulChar.ext fun u => ?_
  obtain ⟨k, rfl⟩ := hg u
  rw [Units.val_pow_eq_pow_val, map_pow, map_pow, h]

omit hp in
/-- The conjugate character: `χ ^ 3` takes the value `-χ(a)` where `χ(a) = ± i`. -/
lemma pow_three_apply_of_pm_gi (χ : MulChar (ZMod p) GaussianInt) {a : ZMod p}
    (h : χ a = gi ∨ χ a = -gi) : (χ ^ 3) a = -χ a := by
  rw [MulChar.pow_apply' χ (by norm_num), pow_succ]
  have : χ a ^ 2 = -1 := by rcases h with h | h <;> rw [h] <;> simp [gi_sq]
  rw [this]; ring

/-- **Definition 3.3 (the pin).** For `p ≡ 5 (mod 8)` there is a unique quartic character
modulo `p` with `χ 2 = i`. -/
theorem existsUnique_pinned' (hp8 : p % 8 = 5) :
    ∃! χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi := by
  have hdvd : 4 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hdvd isPrimitiveRoot_gi
  have existence : ∃ χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi := by
    rcases quartic_apply_two χ hχ hp8 with h | h
    · exact ⟨χ, hχ, h⟩
    · refine ⟨χ ^ 3, orderOf_pow_three hχ, ?_⟩
      rw [pow_three_apply_of_pm_gi χ (Or.inr h), h, neg_neg]
  obtain ⟨χ, hχ, h2⟩ := existence
  refine ⟨χ, ⟨hχ, h2⟩, fun ψ ⟨hψ, h2'⟩ => ?_⟩
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  obtain ⟨e, he, hge⟩ := two_eq_generator_pow_odd hp8 hg
  refine quartic_ext hg ?_
  rcases quartic_apply_generator χ hχ hg with hc | hc <;>
    rcases quartic_apply_generator ψ hψ hg with hs | hs
  · rw [hc, hs]
  · exfalso
    have e1 : ψ 2 = (-gi) ^ e := by rw [← hge, Units.val_pow_eq_pow_val, map_pow, hs]
    have e2 : χ 2 = gi ^ e := by rw [← hge, Units.val_pow_eq_pow_val, map_pow, hc]
    rw [h2', Odd.neg_pow he, ← e2, h2] at e1
    exact gi_ne_neg_gi e1
  · exfalso
    have e1 : ψ 2 = gi ^ e := by rw [← hge, Units.val_pow_eq_pow_val, map_pow, hs]
    have e2 : χ 2 = (-gi) ^ e := by rw [← hge, Units.val_pow_eq_pow_val, map_pow, hc]
    rw [Odd.neg_pow he, h2] at e2
    rw [h2'] at e1
    rw [← e1] at e2
    exact gi_ne_neg_gi e2
  · rw [hc, hs]

/-- **The two quartic characters.** Every quartic character modulo `p` is `χ` or its
conjugate `χ ^ 3`. -/
theorem quartic_eq_or_eq_pow_three {χ ψ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hψ : orderOf ψ = 4) : ψ = χ ∨ ψ = χ ^ 3 := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  have hc := quartic_apply_generator χ hχ hg
  have h3 := pow_three_apply_of_pm_gi χ hc
  rcases hc with hc | hc <;> rcases quartic_apply_generator ψ hψ hg with hs | hs
  · exact Or.inl (quartic_ext hg (by rw [hc, hs]))
  · exact Or.inr (quartic_ext hg (by rw [h3, hc, hs]))
  · exact Or.inr (quartic_ext hg (by rw [h3, hc, hs, neg_neg]))
  · exact Or.inl (quartic_ext hg (by rw [hc, hs]))

end BandParity
