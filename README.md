# oak

Oak is a proof checker focused on simplicity, readability, and ease of use.

For downloads and more information, including a tutorial, go to [oakproof.org](https://oakproof.org/).

## Requirements

  * [Ruby programming language](http://ruby-lang.org/) version ≥ 2.0
  * [E theorem prover](https://eprover.org/) version 2.3.  E is included in the prepackaged Oak downloads available at [oakproof.org](https://oakproof.org/).  If you prefer to install E yourself, be sure to add E's PROVER directory to your system's PATH variable so that Oak will detect it.

## Editor support

  * The [Pulsar](https://pulsar-edit.dev/) text editor (formerly Atom) has a package [language-oak](https://web.pulsar-edit.dev/packages/language-oak) which provides syntax highlighting, automatic indentation, and comment toggling for Oak.
  * For syntax highlighting on web pages, there is a [highlight.js language definition](https://github.com/timlabs/highlightjs-oak) for Oak.
  * Similar packages for other editors would be welcome.

## Usage

Oak is a command-line application which takes a proof file as input, and tells you whether or not the proof is correct.  See [oakproof.org](https://oakproof.org) for more information.

```
oak [-v] [-c] [-w] [filename]
  -v  print the version number of Oak
  -c  check for unneeded citations
  -w  wait for validity (does not change proof outcome)
```

## Version history

### v0.6.1 - 2023-08-10
* improved cross-platform portability

### v0.6 - 2023-07-09
* added support for predicates in quantifiers, like `for all odd n`
* gave `iff`, `if`, and `implies` lower precedence
* new examples: `godel_disjunction.oak`, `product.oak`, `bernstein.oak`, `recursion.oak`

### v0.5 - 2022-04-19
* new feature: parameterized tie-ins
* new examples: `list.oak`, `graph.oak`, `konigsberg.oak`, `leibniz.oak`
* moved comprehension axioms into `comprehension.oak`

### v0.4 - 2021-04-17
* new examples: `infinite_primes.oak` and `set.oak`
* merged `peano.oak` into `naturals.oak` and expanded
* `-w` option to wait for validity if unknown
* extra check to ensure `A implies A` always succeeds
* added `not in` condition
* added `for at most one` quantifier
* improved assumption printing
* simplified quantifier variable list syntax
* `exit` now skips rest of proof, not just current file
* proofs with `exit` are now marked incomplete

### v0.3 - 2020-12-22
* add "tie-ins" for variables
* `-c` option to check for unneeded citations
* new examples: `kalam.oak` and `square_root_two.oak`
* print notice when `exit` is called

### v0.2 - 2019-08-08
* performance improvement from internal reworking of scopes/bindings
* variables bound with `define` can no longer be re-bound in the same scope

### v0.1 - 2017-08-31
* initial release

## Acknowledgements

Many thanks to Stephan Schulz, the author of E, for answering questions and adding options to E to better support Oak.