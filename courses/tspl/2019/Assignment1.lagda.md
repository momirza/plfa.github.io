---
title     : "Assignment1: TSPL Assignment 1"
layout    : page
permalink : /TSPL/2019/Assignment1/
---

```
module Assignment1 where
```

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).



## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import plfa.part1.Relations using (_<_; z<s; s<s; zero; suc; even; odd)
```

## Naturals

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.

```agda
seven : ℕ
seven = suc ( suc ( suc ( suc ( suc ( suc ( suc zero))))))
```

#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.

```agda
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩  -- inductive case
    suc (2 + 4)
  ≡⟨⟩  -- inductive case
    suc (suc (1 + 4))
  ≡⟨⟩  -- inductive case
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc (4)))
  ≡⟨⟩
    7
  ∎

```

#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.

```agda
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + 4 + (0 * 4))
  ≡⟨⟩
    12
  ∎
```

#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

```agda
_^_ : ℕ → ℕ → ℕ
n ^ zero    = 1
n ^ (suc m) = n * (n ^ m)

```

Check that `3 ^ 4` is `81`.

```agda
_ : 3 ^ 4 ≡ 81
_ = refl
```


#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

```agda
_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎ 
```

```agda
_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5 
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎
```

#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
```
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
```
For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

```agda
inc_ : Bin → Bin
inc nil    = x1 nil
inc (x0 x) = x1 x
inc (x1 x) = x0 inc (x)
```


Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

```agda
_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

_ : inc nil ≡ x1 nil
_ = refl

_ : inc x0 nil ≡ x1 nil
_ = refl

_ : inc x1 nil ≡ x0 x1 nil
_ = refl

_ : inc x0 x1 nil ≡ x1 x1 nil
_ = refl

_ : inc x1 x1 nil ≡ x0 x0 x1 nil
_ = begin
      inc x1 x1 nil
    ≡⟨⟩
      x0 inc x1 nil
    ≡⟨⟩
      x0 x0 inc nil
    ≡⟨⟩
      x0 x0 x1 nil
    ≡⟨⟩
      x0 x0 x1 nil
    ∎
```

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

```agda
to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n) 


from : Bin → ℕ
from nil = zero
from (x0 x) = 0 + 2 * (from x) 
from (x1 x) = 1 + 2 * (from x)

_ : to 0 ≡ x0 nil
_ = refl

_ : to 1 ≡ x1 nil
_ = refl

_ : to 2 ≡ x0 x1 nil
_ = refl

_ : to 3 ≡ x1 x1 nil
_ = refl

_ : to 4 ≡ x0 x0 x1 nil
_ = refl

_ : from (x0 x0 x1 nil) ≡ 4
_ = refl

_ : from (x1 x1 nil) ≡ 3
_ = refl

_ : from (x0 x1 nil) ≡ 2
_ = refl

_ : from (x1 nil)  ≡ 1
_ = refl

_ : from (x0 nil) ≡ 0
_ = refl
```

## Induction

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Answer: monus and times

Give an example of an operator that has an identity and is
associative but is not commutative.

Answer: ­ 

#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m

```agda
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p) 
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p  ⟩
    n + (m + p)
  ∎
```

#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.


```agda
*-distrib-+' : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+' zero n p = refl
*-distrib-+' (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨⟩ 
    suc (m + n) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+' m n p) ⟩
    p + ( m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    p +  m * p + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎
```

With `rewrite`:

```agda
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl
```

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

```agda
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p)  ⟩
    n * p + (m * (n * p))
  ≡⟨⟩
    (suc m) * (n * p)
  ∎
```

With rewrite

```agda
*-assoc' : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc' zero n p = refl
*-assoc' (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl
```

#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

```agda
*-zero : ∀ (m : ℕ) → zero * m ≡ m * zero
*-zero zero = refl
*-zero (suc m) =
  begin
    zero * m
  ≡⟨⟩
    zero
  ≡⟨ cong (zero +_) (*-zero m) ⟩
   zero + m * zero
  ≡⟨⟩
    suc m * zero
  ∎

*-suc : ∀ ( m n : ℕ) → m * (suc n) ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | sym (+-assoc n m (m * n)) | +-comm n m | +-assoc m n (m * n) =  refl

-- without rewrite

*-suc' : ∀ ( m n : ℕ) → m * (suc n) ≡ m + m * n
*-suc' zero n = refl
*-suc' (suc m) n =
  begin
    suc m * (suc n)
  ≡⟨⟩
    suc n + (m * (suc n))
  ≡⟨ cong (suc n +_) (*-suc' m n) ⟩
    suc n + (m + m * n)
  ≡⟨⟩ -- induction
    suc (n + (m + m * n))
  ≡⟨ cong (suc) (sym (+-assoc n m (m * n))) ⟩
    suc (n + m + m * n)
  ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m ) ⟩
    suc (m + n + m * n)
  ≡⟨ cong (suc) (+-assoc m n (m * n)) ⟩
    suc (m + ( n  +  m * n))
  ≡⟨⟩ -- ↑ induction using definitions of + and *
    suc m + ((suc m) * n)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n  rewrite (sym (*-zero n)) = refl
*-comm (suc m) n rewrite (sym (*-comm m n)) | *-suc n m | cong (n +_) (*-comm m n)  = refl
```

#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

```agda
zero-monus : ∀ (n : ℕ) → zero ∸ n ≡ zero
zero-monus zero = refl
zero-monus (suc n) = refl
```

No, only the base cases were required.


#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

```agda
monus-plus-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
monus-plus-assoc m zero p = refl
monus-plus-assoc zero (suc n) p rewrite zero-monus p =  refl
monus-plus-assoc (suc m) (suc n) p =
  begin
    m ∸ n ∸ p
  ≡⟨  monus-plus-assoc m n p ⟩
    m ∸ (n + p)
  ≡⟨⟩
    suc m ∸ suc (n + p)
  ∎
```

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


## Relations

```
_ : 1 ≤ 4
_ = s≤s z≤n
```


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

    _<_

Give an example of a partial order that is not a preorder.

    _==_

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


These cases cannot arise since the first inequality implies that
the middle value is zero which is already covered by the first
case.

#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

```agda
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s (s<s n<p) =  z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)
```

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

```agda
data Trichotomy (m n : ℕ) : Set where
  forward :
      m < n
      -----
   →  Trichotomy m n

  flipped :
      n < m
      -----
    → Trichotomy m n

  equal :
      m ≡ n 
      -----
    → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equal refl
<-trichotomy zero (suc n) = forward z<s
<-trichotomy (suc m) zero = flipped z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                             | forward m<n = forward (s<s m<n)
...                             | flipped n<m = flipped (s<s n<m)
...                             | equal refl  = equal refl
```

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

```
+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm  n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)
```

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

```agda
≤-iff-< : ∀ {m n : ℕ}
  → suc m ≤ n
    ---------
  → m < n
≤-iff-<  (s≤s z≤n) = z<s
≤-iff-<  (s≤s (s≤s m≤n)) = s<s (≤-iff-< (s≤s m≤n))

<-iff-≤ : ∀ {m n : ℕ}
  → m < n
    ---------
  → suc m ≤ n
<-iff-≤  z<s = s≤s z≤n
<-iff-≤ (s<s m<n) = s≤s (<-iff-≤ m<n)
```

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relationship between strict inequality and inequality and
the fact that inequality is transitive.

```agda
<-trans-revisited : ∀ { m n p : ℕ }
  → m < n
  → n < p
    -----
  → m < p
<-trans-revisited m<n (s<s n<p) = ≤-iff-< ((≤-trans (<-iff-≤ m<n) (<-iff-≤ (mylemma n<p))))
  where
    mylemma : ∀ { m n : ℕ }
      → m < n
        ---------
      → m < suc n
    mylemma z<s = z<s
    mylemma (s<s m<n) = s<s (mylemma m<n)
```


#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)
