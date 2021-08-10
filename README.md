<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Autosubst

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/autosubst/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/autosubst/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/978-3-319-22102-1_24.svg
[doi-link]: https://doi.org/10.1007/978-3-319-22102-1_24

Autosubst is a library for the Coq proof assistant which
provides automation for formalizing syntactic theories with
variable binders. Given an inductive definition of syntactic
objects in de Bruijn representation augmented with binding
annotations, Autosubst synthesizes the parallel substitution
operation and automatically proves the basic lemmas about
substitutions.

## Meta

- Author(s):
  - Steven Schäfer (initial)
  - Tobias Tebbi (initial)
- Coq-community maintainer(s):
  - Ralf Jung ([**@RalfJung**](https://github.com/RalfJung))
  - Dan Frumin ([**@co-dan**](https://github.com/co-dan))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.11 or later
- Additional dependencies: none
- Coq namespace: `Autosubst`
- Related publication(s):
  - [Autosubst: Reasoning with de Bruijn Terms and Parallel Substitutions](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf) doi:[10.1007/978-3-319-22102-1_24](https://doi.org/10.1007/978-3-319-22102-1_24)

## Building and installation instructions

The easiest way to install the latest released version of Autosubst
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-autosubst
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/autosubst.git
cd autosubst
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


To build the examples that do not need ssreflect, type
```
make examples-plain
```

The examples that depend on ssreflect are built with
```
make examples-ssr
```

To build the documentation (including all examples), type
```
make doc
```

You can use the file `doc/toc.html` to browse the documentation.

## Bug Reports

Please submit bugs reports on https://github.com/coq-community/autosubst/issues

