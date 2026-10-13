# Signed Diffie-Hellman Tutorial

## About

This repository contains an EasyCrypt formalization of the Signed
Diffie-Hellman protocol and its IND-security proof, developed in the
context of the [Proof Ladders](https://proof-ladders.github.io/) project.

The formalization builds on the project's
[problem set](https://github.com/proof-ladders/protocol-ladder/blob/main/Notes/main.pdf)
and the definitions and
[pen-and-paper proof](https://github.com/proof-ladders/protocol-ladder/blob/main/Notes/computational/main.pdf)
by Paul Rösler and Doreen Riepel.

The original EasyCrypt code was developed by François Dupressoir (see [Origin](#origin)).
This repository extends that code with assistance from GPT-6.1 Sol
and Claude Opus 5.5.

An [interactive tutorial](https://provsec.org/proofs/signed-dh-ec/index.html)
presents the pen-and-paper proof alongside its EasyCrypt formalization,
including the games, game hops, and security reductions.

> **Work in progress.** Both the EasyCrypt formalization and the
> interactive tutorial are under development. See [Status](#status)
> for the current proof scope and remaining obligations.

## Origin

This repository is a standalone development based on the Signed
Diffie-Hellman EasyCrypt formalization from Proof Ladders.

- Original repository: [proof-ladders/protocol-ladder](https://github.com/proof-ladders/protocol-ladder)
- Original branch: [signeddh-ec](https://github.com/proof-ladders/protocol-ladder/tree/signeddh-ec)
- Original folder: [signedDH/easycrypt](https://github.com/proof-ladders/protocol-ladder/tree/signeddh-ec/signedDH/easycrypt)
- Standalone repository: [DoreenRiepel/signeddh-tutorial](https://github.com/DoreenRiepel/signeddh-tutorial)

## Status

The game-hop proofs and security reductions have been formalized.
Concrete statistical estimates for the collision events, including
the signature-key collision bound, remain to be established. The
current security theorem retains explicit bad-event probabilities
and assumes bounds for some of them.

This work should not yet be regarded as a complete, independently
reviewed formalization of the paper's quantitative security bound.
Please examine the model, assumptions, and remaining probability
estimates before relying on the results. Feedback and independent
review are welcome.

## Compiling the Project

The current formalization has been checked with:

- EasyCrypt r2026.07 (commit `ad94f3f`)
- Alt-Ergo 2.6.3
- Why3 1.8.2
- OCaml 5.4.0

After installing the toolchain, configure EasyCrypt to find the prover:

```sh
easycrypt why3config
```

Then, from the directory containing `easycrypt/`, check the proof:

```sh
easycrypt compile -I easycrypt easycrypt/SignedDH.ec
```

## Updates

This repository is maintained separately from the original Proof
Ladders repository. Changes are not synchronized automatically, but
upstream changes may be incorporated in the future.


