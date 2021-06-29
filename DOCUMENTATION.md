# How do I Extend Thoralf?

## Assumptions

For this part of the documentation, I'm assuming a reader knows the following.

1. What type-equality plugins are supposed to implement. 
2. An understanding of how types can be broken down with functions like the following.

```haskell
splitTyConApp_maybe :: HasDebugCallStack => Type -> Maybe (TyCon, [Type]) 
```

## Overview

There are two ways to extend thoralf:

* First, you can *support a theory* (like finite maps) by making a `TheorySeed`.
* Second, you can support more advanced Singleton comparisons, e.g., Singleton string comparisons.

These correspond to the two sections below.


# Adding Theories with a `TheorySeed`


## Simple SMT Example

Let's say we have a simple type-equality problem on
the type indicies of literal naturals:


```haskell
import Data.TypeLits

test :: forall (a :: Nat). (1 + a) :~: (a + 1)
test = Refl
```

We can convert this into a problem for an smt solver.
Say we have the file `example.z3` as follows:

```lisp
(declare-const a Int)
(assert (not (= (+ 1 a) (+ a 1))))
(check-sat)
```
If we run this file, i.e., do

```bash
$ z3 example.z3
```

We will get `unsat`, which means it's impossible to subsitute the variable `a` 
so that `(not (= (+ 1 a) (+ a 1)))` is true. This means the equality 
`(= (+ 1 a) (+ a 1))`
holds for any substitution of `a`. Hence, our type equality 
`1 + a ~ a + 1` holds.

*The thoralf plugin automates this procedure.*

It's easy to see all it really needs to do this are a few functions.
First, a function to convert GHC's internal representation of the type 
`1+a` into the smt string `"(+ 1 a)"`. This, in turn, requires a way to determine 
that the kind of the *type variable* `a` should be converted to the *smt sort* `"Int"`.
This would be another function, that can convert kinds into strings that are valid sort in
smt solvers (according to the lib2 standard).


**A `TheorySeed` is a monadic wrapper around a `TheoryBox`, which contains these functions.**

You add theories to the plugin by adding `TheorySeed`s.


## TheorySeed: The Interface

```haskell
type TheorySeed = TcPluginM TheoryBox
type SExpr = SMT.SExpr

data TheoryBox where
  TheoryBox ::
    { typeConvs :: [TypeConv]
    , kindConvs :: [KindConv]
    , startDecs :: [SExpr]
    } -> TheoryBox

type TypeConv = Type -> Maybe TyStrMaker
type KindConv = Type -> Maybe KdStrMaker

data TyStrMaker where
  TyKit ::
    ( Vec n Type
    , Vec m Kind
    , Vec n String -> Vec m String -> String) -> TyStrMaker

data KdStrMaker where
  KdKit :: (Vec m Kind, Vec m String -> String) -> KdStrMaker
```

## What is a TheorySeed?

It's a monad wrapper around a `TheoryBox`, We need the monadic wrapper because
it allows us to look up things we need like `TyCon`s from the environment.

## What is a TheoryBox?

We just trace the three fields in the single record constructor.

* First, it has a list of `TypeConv`s.
These are homormorphic functions that allow the plugin to convert
`1+2` into the the string `"(+ 1 2)"` that the smt solver can recognize.

They correspond to converting one type constructor 
and giving the plugin a kit to convert the rest of the type.
They have the type `Type -> Maybe TyStrMaker`.

A `TyStrMaker` is a triple of (1) a list of types and (2) a list of  kinds that the plugin should convert and then (3) a function that
can take those converted types and kinds, and build the overall smt string. 
The lists are length indexed vectors to help verify everything runs smoothly.
The interface is pretty simple:


```haskell
data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

data Vec :: Nat -> Kind.Type -> Kind.Type where
  VNil :: Vec Zero a
  (:>) :: a -> Vec n a -> Vec (Succ n) a
infixr 5 :>
```

We can imagine that for `(1 + 2)`, we would have a function in our `TheoryBox` that produces
a `Just <of type TyStrMaker>` on the input type `1+2` where the `<of type TyStrMaker>` is
the triple 

(1) `[<type representation of 1>, <type reprentation of 2>]`
(2) `[]` since there are no kinds to convert
(3) `\[firstString, secondString] -> \[] -> "(+ " ++ firstString ++ " " ++ secondString ++ ")"`

Look at the concrete finite map example for more detail.

* Second, we have a similar collection of kind constructor convertors: a list of `KindConv`s.

In this situation, we won't ever need to convert types to convert a kind. Hence the kit these functions return is
just a tuple of (kinds to convert, a string maker).

For type level naturals, we just need to be able to convert the kind of the type `(1+2)` into the string `"Int"`.
The function that does this would produce a double
(1) `[]` -- an empty list of kinds to convert
(2) `\[] -> "Int"` -- a function that takes an empty list and returns the string for the smt supported sort.


* Finally, it holds a collection of declarations that you might use in your conversion
to valid smt strings. This is in the record field `startDecs`.

For instance, with finite maps, we need to declare the maybe datatype in the smt solver.
The `TheoryBox` for finite maps contains the list of declarations 
`startDecs = [maybeDec]` with something like
`maybeDec = SMT.Atom "(declare-datatypes (T) ((Maybe T ...)))"`.



## The Procedure for adding a theory

0. Decide on an interface using closed type families.

   **Put this module in src/ThoralfPlugin/Theory**

1. Start implementing a `TheorySeed` and follow the examples to look up any `TyCon`s you need to from the environment.

   **Put this module in src/ThoralfPlugin/Box**

2. Having looked up any needed `TyCon`s, implement the `TheoryBox`. Look at the examples for help.

3. Add your `TheorySeed` to the declaration of `currentDefaultSeed` located in the module `ThoralfPlugin.Plugin`.


## Finite Map Example

The easiest explanation is just lots of well-commented code.
That's what we provide.

### The Interface

This module is ThoralfPlugin.Theory.FiniteMap

```haskell
{-

Encode the Kind you want, in our case -- Fm,
with a basic datatype definition and use TypeInType
to implement the needed type families

-}

data Fm :: forall k v. k -> v -> Type where {}


-- The Encoding:
type family Nil :: forall (k :: Type) (v :: Type). Fm k v where {}

type family Alter (m :: Fm k v) (key :: k) (val :: v)
  :: forall (k :: Type) (v :: Type). Fm k v where {}

type family Delete (m :: Fm k (v :: Type)) (key :: k)
  :: forall (k :: Type) (v :: Type). Fm k v where {}

{-

Use closed type families to construct types of kind 'Fm k v'.
You should encode things so that by injecting the right 
type equalities of your type indicies, 
you can get the sematics of that type index that you want.
In other words, your type index should represent
all the information you want even though GHC doesn't 
use it the way you want it to.

-}

------------------------------------------------------------------------

{-

You shouldn't expose the homomorphic constructors
(which are Alter and Delete; Nil has no arguments).

Why? 
Well, (and read the paper for more detail) 
it allows the user to put type variables 
inside them leading to a much harder constraint solving problem: unification.

Instead, create type families like the following ones
that produce constraints.
All of these together allow you to express any property of 
a finite map you want to express.

Notice how ConcreteFm allows you to build any concrete finite map you want.
Often, you need something like this.

-}

-- Interface
type family Has (f :: Fm k v) (key :: k) (val :: v) :: Constraint where
  Has m k v = (Alter m k v ~ m)

type family Omits (f :: Fm (k :: Type) (v :: Type)) (key :: k) :: Constraint where
  Omits m k = (Delete m k ~ m)

type family ConcreteFm (xs :: [(k,v)]) :: Fm k v where
  ConcreteFm xs = Build Nil xs

type family
  AddField (m :: Fm k v) (m' :: Fm k v) (key :: k) (val :: v)
  :: Constraint where
    AddField m m' k v = (Alter m k v) ~ m'

type family
  DelField (m :: Fm k (v :: Type)) (m' :: Fm k v) (key :: k)
  :: Constraint where
    DelField m m' k = (Delete m k) ~ m'
------------------------------------------------------------------------

type family Build (m :: Fm k v) (xs :: [(k, v)]) :: Fm k v where
  Build m '[] = m
  Build m ('(k,v) :< ys) = Build (Alter m k v) ys
```

### Starting The TheorySeed: Getting Type Constructors

All of the following code is in the module
ThoralfPlugin.Box.FiniteMaps

```haskell
fmSeed :: TheorySeed
fmSeed = do
  (Found location fmModule) <- findImportedModule fmModName (Just pkg)
  nilTyCon <- findTyCon fmModule "Nil"
  alterTyCon <- findTyCon fmModule "Alter"
  deleteTyCon <- findTyCon fmModule "Delete"
  fmTyCon <- findTyCon fmModule "Fm"
  return $ mkFmBox nilTyCon alterTyCon deleteTyCon fmTyCon
  where
    fmModName = mkModuleName "ThoralfPlugin.Theory.FiniteMap"
    pkg = fsLit "thoralf-plugin"

{-
We use the library functions mkModuleName, findImportedModule
to implement findTyCon and to get the needed type constructors.

Usually, if things are spelled wrong type checking fails
with an error at the start.

-}

findTyCon :: Module -> String -> TcPluginM TyCon
findTyCon md strNm = do
    name <- lookupOrig md (mkTcOcc strNm)
    tcLookupTyCon name

{-
We make the TheoryBox by calling several other 
functions that take a given type constructor and 
make the appropreate conversion functions.

Of course, we have one data declaration that we 
know we need -- maybe.
-}

mkFmBox :: TyCon -> TyCon -> TyCon -> TyCon -> TheoryBox
mkFmBox nil alter delete fm =
  emptyBox { startDecs = [maybeDef]
           , typeConvs =
             [ nilConvert nil
             , alterConvert alter
             , deleteConvert delete
             ]
           , kindConvs = [fmConvert fm]
           }

-- Data and constant declarations
maybeDef :: SExpr
maybeDef = SMT.Atom "(declare-datatypes (T) \
           \((Maybe nothing (just (fromJust T)))))"
```


### The Type Constructor `Nil`

```haskell
{-

We make one conversion function per type family
and per kind. The type conversion functions are of 
type TypeConv and the kind converstion functions are of 
type KindConv.

We start with Nil.

Once nilConvert has a TyCon, it is of type
TypeConv and can fit in the theory box.
It is the conversion function for Nil.


The function's implementation is simple.
It splits the input type and verifies that it is 
a respresentation of the type Nil.

From trial and error, we know the order of the kind arguments
in the type application of the nil-tycon is the keyKind then valKind 
and this is reflected in the implicit pattern match.

A Nil should turn into the string
"((as const (Array <key kind> (Maybe <value kind>))) nothing)"
and to do this it needs strings for the converted "<key kind>" and
"<val kind>". 

Therefore, the kit it produces has an empty list of types to convert, 
a list of those two kinds to convert, and, a simple function to build
the string for Nil: nilString.

nilString expects a list of types and kinds of the same 
size as those lists provided in the kit.
Hence, it pattern matches on an empty list of string-converted types
and two string converted kinds, in the order they were provided and produces 
the desired string.

-}

nilConvert :: TyCon -> Type -> Maybe TyStrMaker
nilConvert nil ty = do
  (tcon, (keyKind : valKind : xs)) <- splitTyConApp_maybe ty
  case tcon == nil of
    False -> Nothing
    True ->
      let
        kindList =  keyKind :> valKind :> VNil
      in
        Just $ TyKit (VNil, kindList, nilString)


nilString :: Vec Zero String -> Vec Two String -> String
nilString VNil (keyKindStr :> valKindStr :> VNil) =
  let
    maybeVal = " (Maybe " ++ valKindStr ++ ")"
    arrayTp = "(Array " ++ keyKindStr ++ " " ++ maybeVal ++ ")"
    nilStr = "((as const " ++ arrayTp ++ ") nothing)"
  in nilStr
```



### The Type Constructor `Alter`

```haskell
{-

Analogous to the converstion function for Nil is the one for Alter.

Alter-headed expressions convert into 

"(store <converted fm string> <key string> (just <val string>))".

Clearly, the kit to make this has a list of three types to convert and 
zero kinds to convert.

-}

alterConvert :: TyCon -> Type -> Maybe TyStrMaker
alterConvert alter ty = do
  (tcon, (_ : _ : fmTp : keyTp : valTp : xs)) <- splitTyConApp_maybe ty
  case tcon == alter of
    False -> Nothing
    True ->
      let
        tyList = fmTp :> keyTp :> valTp :> VNil
      in
        Just $ TyKit (tyList, VNil, alterString)

-- as before, alterString expects the corresponding lists of
-- converted Types and Kinds and makes the desired expression.

type Three = 'Succ ('Succ ('Succ 'Zero))
alterString :: Vec Three String -> Vec Zero String -> String

-- the pattern match is the the same order as tyList:

alterString (fmStr :> keyStr :> valStr :> VNil) VNil =
  let
    valueStr = "(just " ++ valStr  ++ ")"
    altStr =
      "(store " ++ fmStr ++ " " ++ keyStr ++ " " ++ valueStr ++ ")"
  in
    altStr
```

We omit the conversion function for the type family `Delete` 
since it's similar to the `Alter` case.


### The Kind Constructor `Fm`

```haskell
{-

Finally, we make the function of type KindConv, 
by giving fmConvert the type constructor for 'Fm'.

The only difference with this example 
is the smt string-making kit for kinds, KdStrMaker, 
only deals with other kinds to convert, not types.

Hence, we return tuples of (kinds-to-convert, kind-string-maker).

-}

fmConvert :: TyCon -> Type -> Maybe KdStrMaker
fmConvert fm ty = do
  (tcon, (_ : _ : keyKind : valKind : xs)) <- splitTyConApp_maybe ty
  case tcon == fm of
    False -> Nothing
    True ->
      let
        kindList = keyKind :> valKind :> VNil
      in
        Just $ KdKit (kindList, fmString)

fmString :: Vec Two String -> String
fmString (keyKindStr :> valKindStr :> VNil) =
  mkArrayTp keyKindStr valKindStr

mkArrayTp :: String -> String -> String
mkArrayTp keySort valSort =
  "(Array " ++ keySort ++ " (Maybe " ++ valSort ++ "))"
```

### Finishing Up


All that's left is adding the `TheorySeed` to the list in
ThoralfPlugin/Plugin:


```haskell
currentDefaultSeed :: TheorySeed
currentDefaultSeed =
  sumSeeds [ natSeed
           , fmSeed -- << here it is!  
           , symbolSeed
           ]
```

## Restrictions and rules



1. There are a collection of reserved data types that you can't use.
 * Don't make data types with the same name as Type with constructors
`apply` or `lit`
 * Don't make data types with the same names used in 

  `(declare-datatypes (T) ((Maybe nothing (just (fromJust T)))))`

 * Your theories specify data types for z3 without conflicting each other.


3. The smt expressions you make that are combinations in lisp like syntax should have
   parenthesis around them. So, for finite maps, parsing a type that used the type family 
  `Alter` should turn into  "(store ... )" and not "store ...".


4. All `TheoryBox` functions ignore types for type variables,
   i.e., the `TypeConv`s and `KindConv`s return `nothing`.


## Unsupported Theories

Nothing unsafe will happen, but we make no promises.










# Singleton Comparisons

It's really useful with to be able to make any constraints we want to 
when writing order comparison functions on singletons.
We can do this with pattern matching on `Dict`
and using `unsafeCoerce` as we do below.



```haskell
import GHC.TypeLits

{-
Suppose we had `SNat n`
with some special function to 
extract the literal natVal:

natVal :: SNat n -> Int

We could write the following.
-}

compareSNat :: SNat n -> SNat m -> NatOrder
compareSNat x y = case (compare (natVal x) (natVal y)) of
  EQ -> 
   case unsafeCoerce (Dict :: Dict ()) :: Dict (NatEq n m ~ True) of 
     Dict :: Dict (NatEq n m ~ True) -> NEqual
  LT -> 
   case unsafeCoerce (Dict :: Dict ()) :: Dict (NatLt n m ~ True) of 
     Dict :: Dict (NatLt n m ~ True) -> NLThan
  GT -> 
   case unsafeCoerce (Dict :: Dict ()) :: Dict (NatGt n m ~ True) of 
     Dict :: Dict (NatGt n m ~ True) -> NGThan


data NatOrder :: Nat -> Nat -> Type where
  NEqual :: NatEq n m ~ True => NatOrder n m
  NLThan :: NatLt n m ~ True => NatOrder n m
  NGThan :: NatGt n m ~ True => NatOrder n m

type family NatLt (x :: Nat) (y :: Nat) :: Bool where {}
type family NatGt (x :: Nat) (y :: Nat) :: Bool where {}
type family NatEq (x :: Nat) (y :: Nat) :: Bool where {}

data Dict :: Constraint -> Type where
  Dict :: a => Dict a
```
Now, if we had a TheoryBox for the kind `Bool` (analogous to the kind `Fm k v`) 
with support for the operators `NatLt, NatGt, NatEq` 
(and of course, the boolean literals `True, False`), 
this would be really powerful.
This singleton comparison function could help implement, say,
a verified binary search tree.
