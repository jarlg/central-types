# Central types (work in progress)

This repository contains work in progress on formalizing results from the paper [Central H-spaces and banded types](https://arxiv.org/abs/2301.02636) by Ulrik Buchholtz, Dan Christensen, Jarl G. Taxerås Flaten, and Egbert Rijke.

Some results from that paper, mostly related to H-spaces (e.g., Proposition 2.2 and Theorem 2.27), have been merged into the [Coq-HoTT library](https://github.com/HoTT/Coq-HoTT) under the `Homotopy.HSpace` namespace.
The notable results in this repository are:

- Most of **Proposition 3.6:** The characterization of central types
  (search for "3.6" in [`Central.v`](./Central.v))
- **Example 3.8:** Eilenberg-Mac Lane spaces are central
  (see `central_em` in [`EMSpace.v`](./EMSpace.v))
- **Theorem 4.6:** `BAut1 A` is the unique delooping of a central type `A` (see `unique_delooping_central` in [`Central.v`](./Central.v))
- **Theorem 4.19:** `BAut1 A` is a coherent H-space whenever `A` is central (see `hspace_twisted_baut`  and `iscoherent_hspace_twisted_baut1` in [`BAut1.v`](./BAut1.v))
- Part of **Corollary 4.20:** `BAut1 A` is central whenever `A` is central (see `central_pbaut` in [`Central.v`](./Central.v))

Version 0fde1817 from Dec 29, 2023 has been tested with Coq 8.18.0 against commit 6ad532f7 of Coq-HoTT from Dec 29, 2023.
The first two results in the list above were recently added to this repo.

Version 1b44982f from Oct 17, 2023 has been tested with Coq 8.18.0 against commit 687e370c of Coq-HoTT from Oct 17, 2023.
Some things that were formerly in this repository have been merged into Coq-HoTT.

Version 1d6503fe from May 15, 2023 has been tested with Coq 8.16.1 and Coq 8.17.0 against commit 832aef3e of Coq-HoTT from May 2, 2023.

You will need to create a `_CoqProject` file to build this project.
If you have a local build of Coq-HoTT, you can use the below after filling in the path to your local build.

```
-docroot .
-R <path to local Coq-HoTT build> HoTT
-R . Top
-arg -noinit
-arg -indices-matter
-arg -native-compiler -arg no

Bands.v
BAut1.v
Central.v
Conn.v
Cover.v
EMspace.v
Lemmas.v
misc.v
SelfMaps.v
Smallness.v
```
