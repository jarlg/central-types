# Central types, vector fields on spheres, Euler classes, etc.

This repository contains work in progress on formalizing results from the papers [Central H-spaces and banded types](https://arxiv.org/abs/2301.02636) by Ulrik Buchholtz, Dan Christensen, Jarl G. Taxerås Flaten, and Egbert Rijke (BCFR) and "Vector fields on spheres and Euler classes" by Ulrik Buchholtz, Dan Christensen and David Jaz Myers (BCM) (to be released soon).  The results related to BCM were added on March 18, 2026.

Some results from BCFR, mostly related to H-spaces (e.g., Proposition 2.2, Proposition 2.19, Corollary 2.20 and Theorem 2.27), have been merged into the [Coq-HoTT library](https://github.com/HoTT/Coq-HoTT) under the `Homotopy.HSpace` namespace.
The notable results in this repository are:

- Most of **Proposition 3.6:** The characterization of central types
  (search for "3.6" in [`Central.v`](./Central.v))
- **Example 3.8:** Eilenberg-Mac Lane spaces are central
  (see `central_em` in [`EMSpace.v`](./EMSpace.v))
- **Theorem 4.6:** `BAut1 A` is the unique delooping of a central type `A` (see `unique_delooping_central` in [`Central.v`](./Central.v))
- **Theorem 4.19:** `BAut1 A` is a coherent H-space whenever `A` is central (see `hspace_twisted_baut`  and `iscoherent_hspace_twisted_baut1` in [`BAut1.v`](./BAut1.v))
- Part of **Corollary 4.20:** `BAut1 A` is central whenever `A` is central (see `central_pbaut` in [`Central.v`](./Central.v))

Notable results from the BCM paper are:

- Results on co-H-spaces, in [`CoHSpace.v`](./CoHSpace.v).
- Definitions of the Euler class and Thom class and their relationship,
  in [`ThomEuler.v`](./ThomEuler.v).
- All of the material on reflections, in [`Reflections.v`](./Reflections.v).
- The general tangent bundle construction, in [`TorsorTangent.v`](./TorsorTangent.v),
  e.g. `tau` and `theta` in that file.
- The tangent bundles of spheres, in [`Spheres.v`](./Spheres.v),
  including the existence of sections of for odd spheres.
- The new material required to prove the Hairy Ball Theorem,
  in [`TorsorTangent.v`](./TorsorTangent.v).  Some (known) necessary background
  on the homotopy groups of spheres is not yet available in this library.
- The tangent bundles of real and complex projective spaces, in [`ProjectiveSpaces.v`](./ProjectiveSpaces.v).

A lot of necessary background material was also formalized.

The version 3dffd1af from Apr 29, 2026 has been tested with Rocq 9.2.0, Rocq 9.1.0 and Rocq 9.0.0 against commit 8a3c787a of Coq-HoTT from Apr 29, 2026.

The version from Mar 18, 2026 has been tested with Rocq 9.1.0 against commit 6526cb5a of Coq-HoTT from Feb 18, 2026.
It very likely works with Rocq 9.0.0 as well.
This is the version that introduced material related to the (BCM) paper.

Version 0e542a59 from Nov 1, 2025 has been tested with Rocq 9.0.0 and Rocq 9.1.0 against commit 5c938e4f of Coq-HoTT from Oct 31, 2025.

Version c7785d4e1 from Oct 10, 2025 has been tested with Rocq 9.0.0 against commit 0025f6cc of Coq-HoTT from Oct 2, 2025.

Verion b0a11e45 from Mar 13, 2025 has been tested with Coq 8.20.1 against commit dd2ca5cb of Coq-HoTT from Mar 11, 2025.

Version 24608d02 from Sep 26, 2024 has been tested with Coq 8.19.1 against commit b0082605 of Coq-HoTT from Sep 26, 2024.
Some parts of the file Smallness.v have now been merged into Coq-HoTT in Universes/Smallness.v.

Verion 55e4619e from Jan 21, 2024 has been tested with Coq 8.18.0 against commit ce3af423 of Coq-HoTT from Jan 21, 2024.

Version 0fde1817 from Dec 29, 2023 has been tested with Coq 8.18.0 against commit 6ad532f7 of Coq-HoTT from Dec 29, 2023.
The first two results in the list above were added to this repo before this.

Version 1b44982f from Oct 17, 2023 has been tested with Coq 8.18.0 against commit 687e370c of Coq-HoTT from Oct 17, 2023.
Some things that were formerly in this repository have been merged into Coq-HoTT.

Version 1d6503fe from May 15, 2023 has been tested with Coq 8.16.1 and Coq 8.17.0 against commit 832aef3e of Coq-HoTT from May 2, 2023.

You will need to create a `_CoqProject` file to build this project.
If you have a local build of Coq-HoTT, you can use the below after filling in the path to your local build.

```
-docroot .
-R <path to local Coq-HoTT build> HoTT
-Q . CentralTypes
-arg -noinit
-arg -indices-matter
-arg -native-compiler -arg no

Bands.v
BAut1.v
Central.v
CoHSpace.v
Conn.v
Cover.v
EMSpace.v
JoinLemmas.v
KZ.v
Lemmas.v
misc.v
ProjectiveLemmas.v
ProjectiveSpaces.v
Reflections.v
SelfMaps.v
Smallness.v
Spheres.v
ThomEuler.v
Torsor.v
TorsorTangent.v
```
