## Abstract Simplicial Complexes & Stellar Subdivisions
Formalization for abstract simplicial complexes and stellar subdivisions in Lean 4. Partial progress and additional experiments toward formalizing a proof of Pachner's Theorem on equivalence of combinatorial manifolds.

Part of this work is to be presented at [ITP '26](https://itp-conference-2026.github.io/index.html).

### Contents:
- `Basic/` Foundational definitions and some properties.
	- `AbstractSimplicialComplex`
	- `Dimension`
	- `Disjoint` Disjoint union of faces.
	- `Graph` Graphs as 1-dim. complexes.
- `Constructions/` Various operations on complexes.
	- `Cone`
	- `Join`
	- `JoinProjections` First-coordinate projection for joins.
	- `JoinProperties`
- `Maps/` Definitions and properties of classes of morphisms.
	- `SimplicialCoercion` Utilities for typecasting complexes.
	- `SimplicialIsomorphism`
	- `SimplicialMap`
- `Results/` Complex proofs identities, organized into their own files.
	- `SimplicialJoinStellarEquiv`
	- `StarBoundaryIsJoin`
	- `StellarSubdivAnticommLink`
	- `StellarSubdivLinkOfBarycenter`
	- `StellarSubdivLinkOfStarComplement`
- `Stellar/` Definitions and properties of stellar subdivisions/equivalence.
	- `Stellar` Some properties of stellar subdivisions.
	- `StellarCoercion` Typecasting for stellar subdivisions.
	- `StellarEquivlance`
	- `StellarSubdivision`
- `Subcomplex/` Definitions and properties of some standard subcomplexes.
	- `FaceBoundary`
	- `Intersection`
	- `Link`
	- `Star`
	- `StarComplement`
	- `Union`

Citation:
```
@inproceedings{stellarsubdivisionsinlean,
  title={Formalizing Abstract Simplicial Complexes {\&} Stellar Subdivisions in Lean},
  author={Cunningham, Garett and Zach, Daniel and Friedl, Stefan},
  booktitle={17th International Conference on Interactive Theorem Proving (ITP 2026)},
  year={2026},
  organization={Schloss Dagstuhl--Leibniz-Zentrum f{\"u}r Informatik}
}
```
