`hoice` is a Horn Clause ICE engine.

It infers predicates verifying a set of horn clauses.

| linux / macos | windows |     |
|:-------------:|:-------:|:---:|
| [![Build Status](https://travis-ci.org/hopv/hoice.svg?branch=master)](https://travis-ci.org/hopv/hoice) | [![Build status](https://ci.appveyor.com/api/projects/status/db247pe2jp9uo9cs?svg=true)](https://ci.appveyor.com/project/hopv/rsmt2) | [![codecov](https://codecov.io/gh/hopv/hoice/branch/master/graph/badge.svg)](https://codecov.io/gh/hopv/hoice) |

`hoice` supports the `Bool`, `Int` and `Real` sorts.

# Install

If you haven't already, install [Rust](https://www.rust-lang.org) on your system. The recommended way to do this is to use [`rustup`](https://www.rustup.rs/).

Hoice generally uses the latest rust features available. Make sure the rust ecosystem is up to date by running the following command before building hoice.

```bash
rustup update stable
```

Installing hoice with `cargo`:

```bash
cargo install --git https://github.com/hopv/hoice
```

To build hoice manually, clone this repository, `cd` in the directory and run

```bash
cargo build --release
```
The binary file will be in `target/release/hoice`.

To get the fastest version, compile hoice with

```bash
cargo build --release --features "bench"
```

Note that this disables some features such as verbose output, profiling...


## z3

`hoice` relies on the [z3](https://github.com/Z3Prover/z3) SMT-solver. Make sure you have a relatively recent version of the z3 binary in your path.


# Language

[Consult the wiki](https://github.com/hopv/hoice/wiki/Language) for a description of `hoice`'s language.


# Features

- [x] `define-fun`s
- [x] `Bool`
- [x] `Int`
- [x] `Real`
- [x] `Array` (naive)
- [x] `List`
- [x] (mutually recursive) ADTs

Future features:

- [ ] user-specified qualifiers through `define-fun`s


# Checking the result

`hoice` can check its own results. The code performing this feature is completely separated from the code doing the actual inference so that the check is meaningful.

In fact, the code for this is almost implemented as some string substitutions followed by an SMT query for each clause of the problem.

For now, this feature is completely off-line. Put `hoice`'s result in a file, for instance with

```bash
hoice <horn_clause_file> | tee <output_file>
```

and use the `--check` option to verify that the predicates inferred verify all the horn clauses:

```bash
hoice --check <output_file> <horn_clause_file>
```


# Latest version

This repository hosts the latest stable version of hoice. See the [main
developer's fork][main dev fork] for a cutting edge, although unstable,
version.


# Contributing

We welcome any help, please the [contribution guidelines](https://github.com/hopv/hoice/wiki/Contributing) if you are not familiar with the github pull request workflow to get started.


# License

`hoice` is released under the [Apache 2 license](./LICENSE.md). Please note in particular that the [`NOTICE.md`](./NOTICE.md) file from this repository must be available if you redistribute `hoice` in a source or binary format.

[benchs]: https://github.com/hopv/benchmarks/tree/master/clauses (hopv benchmarks)
[main dev fork]: https://github.com/AdrienChampion/hoice (AdrienChampion's fork of hoice on github)
