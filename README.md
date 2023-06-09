# Central types (work in progress)

This repository contains work in progress on formalizing results from the paper [Central H-spaces and banded types](https://arxiv.org/abs/2301.02636) by Ulrik Buchholtz, Dan Christensen, Jarl G. Taxerås Flaten, and Egbert Rijke.

Some results from that paper, mostly related to H-spaces (e.g., Theorem 2.27), have been merged into the [Coq-HoTT library](https://github.com/HoTT/Coq-HoTT) under the `Homotopy.HSpace` namespace.
The notable results in this repository are:

- **Theorem 4.6:** `BAut1 A` is the unique delooping of a central type `A` (see `unique_delooping_central` in [`Central.v`](./Central.v))
- **Theorem 4.19:** `BAut1 A` is a coherent H-space whenever `A` is central (see `hspace_twisted_baut`  and `iscoherent_hspace_twisted_baut1` in [`BAut1.v`](./BAut1.v))
- Part of **Corollary 4.20:** `BAut1 A` is central whenever `A` is central (see `central_pbaut` in [`Central.v`](./Central.v))

This version has been tested with Coq 8.16.1 and Coq 8.17.0 against commit 832aef3e of Coq-HoTT from May 2, 2023.

You will need to create a `_CoqProject` file to build this project.
If you have a local build of Coq-HoTT, you can use the below after filling in the link to your local build.

```
-docroot .
-R <path to local Coq-HoTT build> HoTT
-R . Top
-arg -noinit
-arg -indices-matter
-arg -native-compiler -arg no

BAut1.v
Central.v
Conn.v
Cover.v
Lemmas.v
misc.v
SelfMaps.v
Smallness.v
WildCatLemmas.v
```
