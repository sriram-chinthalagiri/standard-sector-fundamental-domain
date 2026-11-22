# The standard sector is a fundamental domain for `GL_r(F[t])`

A standalone Lean 4 / Mathlib project containing only the general-rank result: for any field
`F` (in particular `F = 𝔽_q`) and `r ≥ 2`, the standard sector is a fundamental domain for the
action of `GL_r(F[t])` on the Bruhat–Tits building of `GL_r(F((1/t)))`.  The rank-2 case
(the Bruhat–Tits tree of `GL_2`) is the special case `r = 2` and is not included separately.

Main theorem: `GLrBuilding.standard_sector_fundamental_domain` in
`GLrFundamentalDomain/FundamentalDomain.lean`.  It states that

1. the simplices of the sector form a subcomplex;
2. every vertex is `GL_r(F[t])`-equivalent to exactly one vertex of the sector
   (`vertex_fundamental_domain`);
3. every simplex is equivalent to exactly one simplex of the sector (`simplex_fundamental_domain`);
4. every pointed chamber is equivalent to exactly one pointed chamber of the sector
   (`pchamber_fundamental_domain`).

Everything is proved without `sorry`; the main theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Files (in import order)

| File | Contents |
| --- | --- |
| `LaurentField.lean` | `K = F((1/t))`, `O = F[[1/t]]`, `F[t] ⊆ K`, the valuation `v_∞` |
| `Lattice.lean` | lattices in `K^r`, vertices (homothety classes), simplices |
| `Cosets.lean` | vertices as cosets of `K^× GL_r(O)` |
| `FlagRefinement.lean`, `FlagBasis.lean`, `Flags.lean` | flags in `F^r` and lattice chains |
| `Chambers.lean`, `PointedChambers.lean` | chambers and pointed chambers |
| `Sector.lean` | the standard sector and the statements of the two key lemmas |
| `RowValuation.lean`, `ApartmentReduction.lean` | reduction of any `g ∈ GL_r(K)` into the standard apartment |
| `SectorProofs.lean` | proofs of the key lemmas (apartment to sector, orbit uniqueness) |
| `FundamentalDomain.lean` | the fundamental domain theorems |
| `ReductionExample.lean` | small explicit examples illustrating the reduction algorithm (not needed for the main theorem) |

## Building

```
lake exe cache get
lake build
```

## Attribution

The method of proof is due to Gebhard Böckle (University of Heidelberg), and is carried out for
the Bruhat–Tits building of `GL_r` in the PhD thesis of Sriram Chinthalagiri Venkata. This Lean 4 formalization was developed with assistance from [Aristotle by Harmonic](https://aristotle.harmonic.fun). I directed the proof strategy and guided the formalization through iterative prompting.
