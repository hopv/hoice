`hoice` is a Horn Clause ICE engine.

It infers predicates verifying a set of horn clauses.

[![Build Status](https://travis-ci.org/hopv/hoice.svg?branch=master)](https://travis-ci.org/hopv/hoice)


# Install

If you haven't already, install [Rust](https://www.rust-lang.org) on your system. The recommended way to do this is to use [`rustup`](https://www.rustup.rs/).

`cargo` installation:

```bash
cargo install --git https://github.com/hopv/hoice
```

To build `hoice` manually, clone this repository `cd` in the directory and run

```bash
cargo build --release
```
The binary file will be in `target/release/hoice`.

To get the fastest version, compile `hoice` with

```bash
cargo build --release --features "bench"
```

Note that this disables some features such as verbosity.


## z3

`hoice` relies on the [z3](https://github.com/Z3Prover/z3) SMT-solver. Make sure you have a relatively recent version of the z3 binary in your path.


# Language

[Consult the wiki](https://github.com/hopv/hoice/wiki/Language) for a description of `hoice`'s language.


# Contributing

We welcome any help, please the [contribution guidelines](https://github.com/hopv/hoice/wiki/Contributing) to get started.


# License

`hoice` is released under the [Apache 2 license](./LICENSE.md). Please note in particular that the [`NOTICE.md`](./NOTICE.md) file from this repository must be available if you redistribute `hoice` in a source or binary format.