# the-thoralf-plugin
This a type-checker plugin to rule all type checker plugins 
involving type-equality reasoning using smt solvers.


## Setup

You need
 * Stack
 * Z3 (the smt solver) version 4.5 and above.
   - [The github repo has instructions](https://github.com/Z3Prover/z3)
 * To build simply

```bash
$ git clone git@github.com:Divesh-Otwani/the-thoralf-plugin.git
$ cd the-thoralf-plugin
$ stack install
$ echo "Now the example should load or run!"
$ stack ghci thoralf-plugin/test/Main.hs

Loaded GHCi configuration from /home/divesh/.ghc/ghci.conf
[1 of 1] Compiling Main             ( test/Main.hs, interpreted )
Ok, 1 module loaded.
*Main> 

```


## Usage

 * Read our haskell symposium submission! Link forthcoming.
 * See /thoralf-plugin/test/Main.hs for an example
 * See [DOCUMENTATION.md](DOCUMENTATION.md) for how to extend thoralf 
   and make your own plugin with all of thoralf's theories and some new
   ones you write



