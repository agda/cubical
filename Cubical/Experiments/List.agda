{-

An experiment of transporting ++-rev-distr from lists to snoc-lists
inspired by section 2 of https://arxiv.org/abs/2010.00774

Note that Agda doesn't care about the order of constructors so we
can't do exactly the same example.

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

infixr 5 _∷_
infixl 5 _∷ʳ_
infixr 5 _++_

-- Normal lists
data List (A : Type) : Type where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

-- Snoc lists
data List' (A : Type) : Type where
  []  : List' A
  _∷ʳ_ : (xs : List' A) (x : A) → List' A

variable
  A : Type


-- Some operations and properties for List

[_] : A → List A
[ a ] = a ∷ []

_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

rev : List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ [ x ]

++-unit-r : (xs : List A) → xs ++ [] ≡ xs
++-unit-r [] = refl
++-unit-r (x ∷ xs) = cong (_∷_ x) (++-unit-r xs)

++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

rev-++-distr : (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-++-distr [] ys       = sym (++-unit-r (rev ys))
rev-++-distr (x ∷ xs) ys = cong (λ zs → zs ++ [ x ]) (rev-++-distr xs ys)
                         ∙ ++-assoc (rev ys) (rev xs) [ x ]



-- We now want to transport this to List'. For this we first establish
-- an isomorphism of the types.

toList' : List A → List' A
toList' []       = []
toList' (x ∷ xs) = toList' xs ∷ʳ x

fromList' : List' A → List A
fromList' []        = []
fromList' (xs ∷ʳ x) =  x ∷ fromList' xs

toFrom : (xs : List' A) → toList' (fromList' xs) ≡ xs
toFrom []          = refl
toFrom (xs ∷ʳ x) i = toFrom xs i ∷ʳ x

fromTo : (xs : List A) → fromList' (toList' xs) ≡ xs
fromTo []          = refl
fromTo (x ∷ xs) i =  x ∷ fromTo xs i

ListIso : Iso (List A) (List' A)
ListIso = iso toList' fromList' toFrom fromTo

-- We then use univalence to turn this into a path
ListPath : (A : Type) → List A ≡ List' A
ListPath A = isoToPath (ListIso {A = A})


-- We can now use this path to transport the operations and properties
-- from List to List'

-- First make a suitable Σ-type packaging what we need for the
-- transport (note that _++_ and rev here are part of the Σ-type).
-- It should be possible to automatically generate this given a module/file.
T : Type → Type
T X = Σ[ _++_ ∈ (X → X → X) ] Σ[ rev ∈ (X → X) ] ((xs ys : X) → rev (xs ++ ys) ≡ rev ys ++ rev xs)

-- We can now transport the instance of T for List to List'
T-List' : T (List' A)
T-List' {A = A} = transport (λ i → T (ListPath A i)) (_++_ , rev , rev-++-distr)

-- Getting the operations and property for List' is then just a matter of projecting them out
_++'_ : List' A → List' A → List' A
_++'_ = T-List' .fst

rev' : List' A → List' A
rev' = T-List' .snd .fst

rev-++-distr' : (xs ys : List' A) → rev' (xs ++' ys) ≡ rev' ys ++' rev' xs
rev-++-distr' = T-List' .snd .snd










-- To connect this with the Cubical Agda paper consider the following
-- (painfully) manual transport.
module manual where

  _++''_ : List' A → List' A → List' A
  _++''_ {A = A} = transport (λ i → ListPath A i → ListPath A i → ListPath A i) _++_

  rev'' : List' A → List' A
  rev'' {A = A} = transport (λ i → ListPath A i → ListPath A i) rev

  rev-++-distr'' : (xs ys : List' A) → rev'' (xs ++' ys) ≡ rev'' ys ++'' rev'' xs
  rev-++-distr'' {A = A} = transport (λ i → (xs ys : ListPath A i)
                                         → revP i (appP i xs ys) ≡ appP i (revP i ys) (revP i xs))
                                    rev-++-distr
    where
    appP : PathP (λ i → ListPath A i → ListPath A i → ListPath A i) _++_ _++''_
    appP i = transp (λ j → ListPath A (i ∧ j) → ListPath A (i ∧ j) → ListPath A (i ∧ j)) (~ i) _++_

    revP : PathP (λ i → ListPath A i → ListPath A i) rev rev''
    revP i = transp (λ j → ListPath A (i ∧ j) → ListPath A (i ∧ j)) (~ i) rev
