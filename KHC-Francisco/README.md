# KU Leuven Haskell Compiler, Extended with Implicit Type Conversions (ITC) #

This repository contains a modified version of the KU Leuven Haskell Compiler that supports ICTs. This is a simple Haskell compiler featuring type inference with translation to System F.
The compiler is constructed at KU Leuven, under the programming languages group of [prof Tom Schrijvers](https://people.cs.kuleuven.be/~tom.schrijvers/).
The original KHC can be found at [prototype implementation](https://github.com/gkaracha/quantcs-impl).

**Tested with GHC 8.4.3**

## Implementation ##

The implementation is split over three directories: `Frontend`, `Backend` and `Utils`. The most important modules are the following:

  * Frontend
    + `HsTypes.hs`: Source language abstract syntax.
    + `HsParser.hs`: A simple parser.
    + `HsRenamer.hs`: The renamer.
    + `HsTypeChecker.hs`: The type inference algorithm with translation to System F.
    + `Conditions.hs`: The implementation of the `nonambig` condition.

  * Backend
    + `FcTypes.hs`: The abstract syntax of System F with datatypes and recursive let bindings.
    + `FcTypeChecker.hs`: A System F type checker.


### Try it in GHCi ###

The easiest way to try out the prototype in examples is by loading it in GHCi. For example:

    :load Main.hs
    runTest "Example/example3.hs"

    
## TODOs ##

This is still an early version, so several improvements are planned for the near future:

* Allowing the annotation to be a polytype;
* The KHC's TODO's.
