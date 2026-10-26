module

public import Mathlib

@[expose] public section

/-!
# The matching lemma

Let `X`, `Y` be finite sets of the same size `m`, let `σ` and `τ` take only the values `± 1`,
and let `π : X → Y` be a bijection. Then

  `∑_{x ∈ X} σ(x) τ(π x) ≡ ∑_X σ + ∑_Y τ - m (mod 4)`,

so the residue modulo `4` of a correlation of two families of signs does not depend on how they
are matched (`matching`, `matching_indep`).

The proof is termwise: for `a, b ∈ {± 1}`, `a b - a - b + 1 = (a - 1)(b - 1) ∈ {0, 4}`.
-/

namespace BandParity

open Finset

/-- For signs `a, b ∈ {± 1}`, `a b ≡ a + b - 1 (mod 4)`. -/
lemma sign_mul_modEq {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b ≡ a + b - 1 [ZMOD 4] := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- Termwise form: a sum of products of signs is congruent to the sum of the two marginals
minus the number of terms. -/
lemma sum_sign_mul_modEq {ι : Type*} (X : Finset ι) (σ τ : ι → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ x ∈ X, τ x = 1 ∨ τ x = -1) :
    ∑ x ∈ X, σ x * τ x ≡ ∑ x ∈ X, σ x + ∑ x ∈ X, τ x - X.card [ZMOD 4] := by
  induction X using Finset.cons_induction with
  | empty => simp
  | cons a X ha ih =>
    rw [sum_cons, sum_cons, sum_cons, card_cons]
    have h1 := sign_mul_modEq (hσ a (mem_cons_self a X)) (hτ a (mem_cons_self a X))
    have h2 := ih (fun x hx => hσ x (mem_cons_of_mem hx)) (fun x hx => hτ x (mem_cons_of_mem hx))
    have := Int.ModEq.add h1 h2
    push_cast
    exact this.trans (by ring_nf; rfl)

/-- **The matching lemma.** For a bijection `π` from `X` onto `Y` and sign functions `σ` on `X`
and `τ` on `Y`, `∑_{x ∈ X} σ(x) τ(π x) ≡ ∑_X σ + ∑_Y τ - |X| (mod 4)`. -/
theorem matching' {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π : ι → κ)
    (hπ : Set.BijOn π X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x + ∑ y ∈ Y, τ y - X.card [ZMOD 4] := by
  have hY : ∑ x ∈ X, τ (π x) = ∑ y ∈ Y, τ y :=
    Finset.sum_nbij π (fun x hx => hπ.mapsTo hx) (fun x hx y hy h => hπ.injOn hx hy h)
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hπ.surjOn hy
        exact ⟨x, hx, rfl⟩) (fun _ _ => rfl)
  rw [← hY]
  exact sum_sign_mul_modEq X σ (fun x => τ (π x)) hσ (fun x hx => hτ _ (hπ.mapsTo hx))

/-- **Independence of the matching.** Two bijections from `X` onto `Y` give correlations that
agree modulo `4`. -/
theorem matching_indep' {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π π' : ι → κ)
    (hπ : Set.BijOn π X Y) (hπ' : Set.BijOn π' X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x * τ (π' x) [ZMOD 4] :=
  (matching' X Y π hπ σ τ hσ hτ).trans (matching' X Y π' hπ' σ τ hσ hτ).symm

end BandParity
