# oak

Oak is a proof checker focused on simplicity, readability, and ease of use.

For downloads and more information, including a tutorial, go to [oakproof.org](http://oakproof.org/).

## Requirements

  * [Ruby programming language](http://ruby-lang.org/) version ≥ 2.0
  * [E theorem prover](http://eprover.org/) version 2.3.  E is included in the prepackaged Oak downloads available at [oakproof.org](http://oakproof.org/).  If you prefer to install E yourself, be sure to add E's PROVER directory to your system's PATH variable so that Oak will detect it.

## Editor support

  * The [Atom](https://atom.io/) text editor has a package `language-oak` which provides syntax highlighting, automatic indentation, and comment toggling for Oak.

## Usage

Oak is a command-line application which takes a proof file as input, and tells you whether or not the proof is correct.  See [oakproof.org](http://oakproof.org) for more information.

```
oak [-v] [-c] [filename]
    -v  print the version number of Oak
    -c  check for unneeded citations
```

## Version history

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