
# Requirements For Using Thoralf

1. Your theories specify data types for z3 without conflicting each other.
   This includes the default theory. The finite map theory will need to
   specify Maybe:
```bash
(declare-datatypes (T) ((Maybe nothing (just (fromJust T)))))
```
   and other theories should not specify things with the same names.

2. Make paranthesized SMT expressions. E.g., "(store (...) (...) (...) )"

3. None of the TheoryBox functions deal with type variables !!!  They also
   satisfy an encoding property.

4. Your encoding with type families doesn't allow for the creation of Tau
   type variables. (Otherwise, fake tau variables which are treated as
   skolems in this plugin will misbehave.


# Design Choices

* We do solver calls in batches. Either all the wanted constraints follow
  or at least one didn't follow.
* Ignore plugin-solver calls where we have no wanted constraints.
* We "default" on types we can't break down with any of our theories.
  Provided these types are represented only with the constructors TyConApp
  and FunTy, we break them down into syntatatic string representations and
  use those. Formally, we are deducing wanteds from givens, where we only
  use a subset of the equational theory of concrete types.
* We use the show of uniques for tyvars to display them.
* If we can't parse it, we don't touch it. Hence, the plugin only deals
  with known theories.



