# BandParity

Lean 4 / Mathlib formalization accompanying J. S. Farland, *The band-parity sum of a quartic
character: two laws modulo four, formalized in Lean* (preprint, Zenodo, 2026).

For a prime `p ≡ 5 (mod 8)` let `χ` be the quartic character with `χ(2) = i` and put

  `𝒞(p) = ∑_{0 < n < p/2} χ(n) (-1)^⌊n²/p⌋ = f + i e`,  `Q = (p - 1)/4`,  `κ = ∑_{0 < n < p/4} (n/p)`.

This repository proves:

- **Theorem A.** `f ≡ Q (mod 4)` for every `p ≡ 5 (mod 8)`, and `e ≡ κ (mod 4)` for `p > 5`.
- **The matching lemma.** For signs `σ, τ = ± 1` and a bijection `π : X → Y`,
  `∑ σ(x) τ(π x) ≡ ∑ σ + ∑ τ - |X| (mod 4)`, so the residue does not depend on `π`.
- **The lag identity.** `∑_{u ∈ 2H} s(u) s(2u) = κ` exactly, with `s(u) = (-1)^⟨u⟩` and `H` the
  fourth powers.
- **Coset parities and the Coordinate Congruence.** `∑_H s = k + 2t`, `∑_{2H} s = t - 2k` where
  `B_{1,χ} = k + i t`, and `e ≡ κ ≡ Q + k + t (mod 4)`.
- **Theorem B.** For any odd `N ≥ 3`, any subgroup `H ≤ (ℤ/N)ˣ` of odd order `h`, any coset `xH`
  and any even `e ≥ 2`, the band-parity sum of `xH ∪ (-xH)` over `(0, N/2)` is
  `≡ h - 2α(xH) - 2α((xH)^e) (mod 4)`, where `α` counts elements with odd least residue.

`κ = h(-4p)/2` by Dirichlet's formula; that identification is quoted in the paper and not used
here. The files `Basic`, `Pin`, `FixedBase` and `CosetSums` are reused from the formalized survey
[KSurvey](https://github.com/jkfarland-bot/KSurvey)
([doi:10.5281/zenodo.23624363](https://doi.org/10.5281/zenodo.23624363)).

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface a reader should audit. It restates the definitions
  exactly as the development has them and states the seventeen results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `BandParity/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the
  [Palomar starter template](https://github.com/PalomarRegistry/PalomarTemplate).

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

| Paper | Challenge declaration |
|---|---|
| Proposition 2.1(1) | `T_eq`, `odd_k`, `odd_t` |
| the pin `χ(2) = i` | `existsUnique_pinned` |
| Lemma 3.1 (matching) | `matching`, `matching_indep` |
| Lemma 4.1 (parity dictionary) | `neg_one_pow_band` |
| Proposition 4.2 (coset form) | `bandSum_re`, `bandSum_im` |
| Proposition 5.1 (lag identity) | `lag_identity` |
| **Theorem 6.1 (Theorem A)** | `bandSum_re_modEq`, `bandSum_im_modEq` |
| Proposition 6.2 (coset parities) | `coset_parities` |
| Corollary 6.3 (Coordinate Congruence) | `bandSum_im_modEq_coords`, `coordinate_congruence` |
| Lemma 7.1 (representative identity) | `cosetBandSum_eq` |
| **Theorem 7.2 (Theorem B)** | `odd_subgroup_congruence` |

## Files

| File | Contents |
|---|---|
| `Basic.lean` | `gi = i`, quartic characters: values, oddness at `p ≡ 5 (mod 8)`, `χ(2) = ± i` |
| `Pin.lean` | existence and uniqueness of `χ` with `χ(2) = i`; the two quartic characters |
| `FixedBase.lean` | `T χ = ∑ χ(n) n`, the fixed-base collapse and the half-sum identity |
| `CosetSums.lean` | coset sums, `S`, `k`, `t`, `T χ = p (k + i t)`, oddness of `k`, `t` |
| `Defs.lean` | `parSign`, `band`, `bandSum`, `Q`, `kappa` |
| `Matching.lean` | the matching lemma |
| `Laws.lean` | parity dictionary, half-range sums, classes `cls`, coset form of `𝒞(p)` |
| `Main.lean` | lag identity, Theorem A, coset parities, Coordinate Congruence |
| `OddSubgroup.lean` | Theorem B for any odd modulus |
