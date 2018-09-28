# The Thoralf Plugin

\\[ ~ \\]
\\[ ~ \\]
\\[ ~ \\]

# *Divesh Otwani* *
## Haverford College
## dotwani@haverford.edu

$ ~~ $

# Richard A. Eisenberg
## Bryn Mawr College
## rae@cs.brynmawr.edu

\\[ ~ \\]
\\[ ~ \\]
*Presenter

---

# Agenda

1. **What's the problem? Who cares?**
2. Contributions
3. Main Ideas
     1. Formalization
     2. Equivalence of Substitutions
     3. Unification
4. The Paper
5. Conclusion



---

# Motivation

    !haskell
    {-# OPTIONS_GHC -fplugin ThoralfPlugin.Plugin #-}

    data Vec :: Nat -> Type -> Type where
      VNil  :: Vec 0 a
      (:>)  :: a -> Vec n a -> Vec (1+n) a
    infixr 5 :>

    concatVec :: Vec n a -> Vec m a -> Vec (n+m) a
    concatVec VNil       ys  =  ys
    concatVec (x :> xs)  ys  =  x :> (concatVec xs ys)


## Type error:

    !text
    * Could not deduce: (1 + (n1 + m)) ~ (n + m)
      from the context: n ~ (1 + n1)
      Expected type: Vec (n + m) a
        Actual type: Vec (1 + (n1 + m)) a

\\[ ~ \\]

GOAL: Make the *right* type errors dissapear.

---

# Motivation

    !haskell
    {-# OPTIONS_GHC -fplugin ThoralfPlugin.Plugin #-}

    data Vec :: Nat -> Type -> Type where
      VNil  :: Vec 0 a
      (:>)  :: a -> Vec n a -> Vec (1+n) a
    infixr 5 :>

    concatVec :: Vec n a -> Vec m a -> Vec (n+m) a
    concatVec VNil       ys  =  ys
    concatVec (x :> xs)  ys  =  x :> (concatVec xs ys)

    fancyLookup :: In n keys => FancyMap keys Nat Bool -> SNat n -> Bool

 * Support type indicies
     * These can be fancy: type level sets, finite maps
 * Allow us to mimic dependent types
 * Enable us to write sophisticated data types
     * E.g., Generic records


---


# Motivation: Existing Approaches

## Type Families

    !haskell
    type family (n :: Nat) + (m :: Nat) :: Nat where
      Z     + m = Z
      (S n) + m = S (n + m)

Issues: complicated instances, tedious proofs

## Type Checker Plugins Assert Deductions

    !text
    * Could not deduce: (1 + (n1 + m)) ~ (n + m)
      from the context: n ~ (1 + n1)
      Expected type: Vec (n + m) a
        Actual type: Vec (1 + (n1 + m)) a

* Diatchki’s type-nat-solver
* Gundry’s uom-solver


## Problem Statement

1. Formalize the type error
2. Provide an algorithm in a plugin

---




# Agenda

1. <s>What's the problem? Who cares?</s>
2. **Contributions**
3. Main Ideas
     1. Formalization
     2. Equivalence of Substitutions
     3. Unification
4. The Paper
5. Conclusion


---


# Contributions

## 1. The Thoralf Plugin

> [**github.com/Divesh-Otwani/the-thoralf-plugin**](https://github.com/Divesh-Otwani/the-thoralf-plugin)

 * A handful of indices: nats, maps, sets
 * Extensible: Fairly easy to add more indices
 * Generic: You can add indicies
## 2. Formalized the problem from the type error
> Call it the **equational deduction problem**,  EDP

## 3. Generic, SMT-based algorithm for EDP


---



# Agenda

1. <s>What's the problem? Who cares?</s>
2. <s>Contributions</s>
3. Main Ideas
     1. **Formalization**
     2. Equivalence of Substitutions
     3. Unification
4. The Paper
5. Conclusion


---



# Formalization: Nats

## Type error:

    !text
    * Could not deduce: (1 + (n1 + m)) ~ (n + m)
      from the context: n ~ (1 + n1)
      Expected type: Vec (n + m) a
        Actual type: Vec (1 + (n1 + m)) a


## Formalizing the error

* We have a set of given equalities $G$ and a set of wanted equalities $W$.
* What does it mean to assume  $n \\sim (1 + n_1)~$?
    * We have some $n, n_1,m$ such that $n = (1 + n_1)$
    * We have a substitution so each for each given $g \\sim g'$ 
    we know $g = g'$

* When do we deduce the wanted equality?
    * When all substitutions that satisfy the given equalities satisfy the wanted
    equalities

---


# Formalization: Finite Maps

> $\texttt{Fm} ::= \texttt{Nil } \vert \texttt{ Alter } fm ~ k ~ v ~\vert
> \texttt{ Delete } fm ~ k$

# Finite Map Type Error
    !text
    * Could not deduce: m1 ~ (Alter m1 "price" Int)
      from the context: m ~ (Alter m1 field val)
      or                m ~ Alter m "price" Int
      or from           DisEquality "price" field

# Analysis

* The given says we have a $m, m_1, field, val$ such that all givens pairs are
in fact equal
    * We define the equality relation of literal finite maps, $E$,

$$\frac{\texttt{k} \sim \texttt{k'}}{\texttt{Alter (Alter fm k v1) k' v2} \sim \texttt{Alter fm k v2}}$$


---



# Formalization: Finite Maps

> $\texttt{Fm} ::= \texttt{Nil } \vert \texttt{ Alter } fm ~ k ~ v ~\vert
> \texttt{ Delete } fm ~ k$

# Finite Map Type Error
    !text
    * Could not deduce: m1 ~ (Alter m1 "price" Int)
      from the context: m = (Alter m1 field val)
      or                m = Alter m "price" Int
      or from           "price" != field

# Analysis

* The given says we have a $m, m_1, field, val$ such that all givens pairs are
in fact equal
    * We define the equality relation of literal finite maps, $E$,

$$\frac{\texttt{k} \sim \texttt{k'}}{\texttt{Alter (Alter fm k v1) k' v2} \sim \texttt{Alter fm k v2}}$$

* We deduce the wanted if, as per our definition of literal equality, all
  substitutions which "satisfy" the given equalites, also, satisfy the wanted
  equality


---




# Summary: Formalizing EDP

## Formalization:
> $ G \\Rightarrow W $ iff all (closing) substitutions that satisfy $G$ neccesarily satisfy $W$

Note: users define "satisfy" (via the literal equality relation)

## Ok, how can we solve this problem?



---


# Agenda

1. <s>What's the problem? Who cares?</s>
2. <s>Contributions</s>
3. Main Ideas
     1. <s>Formalization</s>
     2. **Equivalence of Substitutions**
     3. Unification
4. The Paper
5. Conclusion


---




# Solving EDP: What are SMT solvers?

## Simple Example

    !text
    (declare-const n Int)
    (declare-const m Int)
    (declare-const n1 Int)

    ; Assert all givens.
    (assert (= n (+ 1 n1)))
    (assert (= n1 (+ 1 n)))
    (check-sat) // unsat


* We should see unsat above

## Example Continued

    !text
    ; Assert at least one wanted is false.
    (assert (= n (+ 1 n1)))
    (assert (not (= n m)))
    (check-sat) 

* We should see sat above



---




# Solving EDP: Nats

 * Why does this work at all?

## Type Error
    !text
    * Could not deduce: (n2 - n1) ~ (m - n)
      from the context: n ~ (1 + n1)
      or from: m ~ (1 + n2)

## SMT Query

    !text
    (declare-const n Int)
    (declare-const m Int)
    (declare-const n1 Int)
    (declare-const n2 Int)

    ; Assert all givens.
    (assert (= n (+ 1 n1)))
    (assert (= m (+ 1 n2)))
    (check-sat) ; check if givens are consistent

    ; Assert at least one wanted is false.
    (assert (not (= (- n2 n1) (- m n))))
    (check-sat) ; we want "unsat"




---


# Solving EDP: Nats: Handwave S.E.
* Why does this work at all?
    * Sufficient: Equivalence of existence of "satisfying" substitutions
* S.E. follows from **Encoding property**: For encoding function $f : \texttt{GHC-TYPE} \rightarrow \texttt{SMT-SORT}$,
    * $ t \sim t' \iff f(t) \cong f(t')$
## Type Error
    !text
      from the context: n ~ (1 + n1)
      or from: m ~ (1 + n2)

## SMT Query

    !text
    (declare-const n Int)
    (declare-const m Int)
    (declare-const n1 Int)
    (declare-const n2 Int)

    ; Assert all givens.
    (assert (= n (+ 1 n1)))
    (assert (= m (+ 1 n2)))
    (check-sat) ; check if givens are consistent


---



# Solving EDP: Finite Maps
    !text
    * Could not deduce: m1 ~ (Alter m1 "price" Int)
      from the context: m ~ (Alter m1 field val)
      or                m ~ Alter m "price" Int
      or from           DisEquality "price" field



## SMT Call
    !text
    (declare-datatypes (T)
      ((Maybe nothing (just (fromJust T)))))

    (declare-const m (Array String (Maybe String)))
    (declare-const m1 (Array String (Maybe String)))
    (declare-const field String)
    (declare-const val String)

    ; Assert Givens
    (assert (not (= "price" field)))
    (assert (= m (store m "price" (just "Int"))))
    (assert (= m (store m1 field (just val))))
    (check-sat)

    ; Assert at least one wanted is false.
    (assert (not (= m1 (store m1 "price" (just "Int")))))
    (check-sat)

---


# Solving EDP: Finite Maps: Argue S.E.

    !text
    * Could not deduce: m1 ~ (Alter m1 "price" Int)
      from the context: m ~ (Alter m1 field val)
      or                m ~ Alter m "price" Int
      or from           DisEquality "price" field

* **Suppose** for $f : \texttt{Fm Int Bool} \rightarrow \texttt{Array Int (Maybe
  Bool)}$, for all $ t,t'$, $ \quad \quad \quad \quad \quad \quad \quad \quad ~~~ t \sim t' \iff f(t) \cong f(t') $
* Claim: Subst. Equiv. of GHC world and SMT world
     * $(\Rightarrow).$ Suppose $\varphi$ satisfies $\texttt{m ~ (Alter m1 field val)}$.
     * WTS: $\exists ~m', m_1', field', val'$ such that 
     $m' \cong \texttt{(store }m' ~field' ~val'\texttt{)}$.



$\varphi(m)  \sim  \varphi(\texttt{Alter } ~~~m_1 ~~~field
~~~val )\texttt{)}$


$f(\varphi(m))  \cong f( \varphi(\texttt{Alter } ~~~m_1 ~~~field
~~~val ))\texttt{)}$

$f(\varphi(m))  \cong f(\texttt{Alter } ~~~\varphi(m_1) ~~~\varphi(field) 
~~~((\varphi(val))\texttt{)}$

$f(\varphi(m))  \cong \texttt{(store } ~~~(f(\varphi(m_1))) ~~~(f(\varphi(field)))
~~~(f(\varphi(val)))\texttt{)}$

* Other direction (and general argument similar)



---

# Solving EDP: Summary

## 1. Assert givens and assert at least one wanted false

## 2. It's sufficient to get substitutive equivalence

From this, proving our algorithm meets our specification of EDP is easy.


## 3. This follows from the encoding property:

For the encoding function $f : \texttt{GHC-TYPE} \rightarrow \texttt{SMT-SORT}$,

$$ t \sim t' \iff f(t) \cong f(t')$$

---


# Agenda

1. <s>What's the problem? Who cares?</s>
2. <s>Contributions</s>
3. Main Ideas
     1. <s>Formalization</s>
     2. <s>Equivalence of Substitutions</s>
     3. **Unification**
4. The Paper
5. Conclusion

---


# Unification

    !haskell
    type Has fm key val = (Alter fm key val ~ fm)

    someFn :: SomeTy (Alter fm "a" 5) -> Int

    otherFn :: Has fm "a" 5 => SomeTy fm -> Int


* First function introducing a pointless unification variable
* Second function is clearer and less computational annoying


---


# Agenda

1. <s>What's the problem? Who cares?</s>
2. <s>Contributions</s>
3. <s>Main Ideas</s>
     1. <s>Formalization</s>
     2. <s>Equivalence of Substitutions</s>
     3. <s>Unification</s>
4. **The Paper**
5. Conclusion

---


# The Paper

## In the paper

* Starting thoughts on type safety
* Gory details of formalizing EDP
* A fancy example
  * Type-level finite maps
  * Extensible records

## *Not* in the paper

* Rigorous theory of type safety
* Connection between the EDP problem and the theory behind GHC’s type safety
* Practical examples
* Proof of correctness of the SMT algorithm


---


# Conclusion


* Has potential
     * With SMT solvers growing, could become very powerful
     * Many fancy types work now
* Lot's of work left
     * Type safety, error messages, proof of correctness
     * Practical examples


---



# Questions about *The Thoralf Plugin*?

> [**github.com/Divesh-Otwani/the-thoralf-plugin**](https://github.com/Divesh-Otwani/the-thoralf-plugin)

\\[ ~ \\]
\\[ ~ \\]

# *Divesh Otwani* *
## Haverford College
## dotwani@haverford.edu

$ ~~ $

# Richard A. Eisenberg
## Bryn Mawr College
## rae@cs.brynmawr.edu

\\[ ~ \\]

*Presenter



