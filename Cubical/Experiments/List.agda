{-

An experiment of transporting rev-++-distr from lists to lists where
the arguments to cons have been flipped inspired by section 2 of
https://arxiv.org/abs/2010.00774

Note that Agda doesn't care about the order of constructors so we
can't do exactly the same example.

-}
{-# OPTIONS --safe #-}
module Cubical.Experiments.List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

infixr 5 _∷_
infixl 5 _∷'_
infixr 5 _++_

-- Normal lists
data List (A : Type) : Type where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

-- Lists where the arguments to cons have been flipped
data List' (A : Type) : Type where
  []  : List' A
  _∷'_ : (xs : List' A) (x : A) → List' A

variable
  A : Type


-- Some operations and properties for List

_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

rev : List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

++-unit-r : (xs : List A) → xs ++ [] ≡ xs
++-unit-r [] = refl
++-unit-r (x ∷ xs) = cong (_∷_ x) (++-unit-r xs)

++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

rev-++-distr : (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-++-distr [] ys       = sym (++-unit-r (rev ys))
rev-++-distr (x ∷ xs) ys = cong (_++ _) (rev-++-distr xs ys) ∙ ++-assoc (rev ys) (rev xs) (x ∷ [])



-- We now want to transport this to List'. For this we first establish
-- an isomorphism of the types.

toList' : List A → List' A
toList' []       = []
toList' (x ∷ xs) = toList' xs ∷' x

fromList' : List' A → List A
fromList' []        = []
fromList' (xs ∷' x) =  x ∷ fromList' xs

toFrom : (xs : List' A) → toList' (fromList' xs) ≡ xs
toFrom []          = refl
toFrom (xs ∷' x) i = toFrom xs i ∷' x

fromTo : (xs : List A) → fromList' (toList' xs) ≡ xs
fromTo []          = refl
fromTo (x ∷ xs) i =  x ∷ fromTo xs i

ListIso : Iso (List A) (List' A)
ListIso = iso toList' fromList' toFrom fromTo

ListEquiv : List A ≃ List' A
ListEquiv = isoToEquiv ListIso

-- We then use univalence to turn this into a path
ListPath : (A : Type) → List A ≡ List' A
ListPath A = isoToPath (ListIso {A = A})


-- We can now use this path to transport the operations and properties
-- from List to List'
module transport where

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
-- (painfully) manual transport. This is really what the above code
-- unfolds to.
module manualtransport where

  _++'_ : List' A → List' A → List' A
  _++'_ {A = A} = transport (λ i → ListPath A i → ListPath A i → ListPath A i) _++_

  rev' : List' A → List' A
  rev' {A = A} = transport (λ i → ListPath A i → ListPath A i) rev

  rev-++-distr' : (xs ys : List' A) → rev' (xs ++' ys) ≡ rev' ys ++' rev' xs
  rev-++-distr' {A = A} = transport (λ i → (xs ys : ListPath A i)
                                         → revP i (appP i xs ys) ≡ appP i (revP i ys) (revP i xs))
                                    rev-++-distr
    where
    appP : PathP (λ i → ListPath A i → ListPath A i → ListPath A i) _++_ _++'_
    appP i = transp (λ j → ListPath A (i ∧ j) → ListPath A (i ∧ j) → ListPath A (i ∧ j)) (~ i) _++_

    revP : PathP (λ i → ListPath A i → ListPath A i) rev rev'
    revP i = transp (λ j → ListPath A (i ∧ j) → ListPath A (i ∧ j)) (~ i) rev



-- The above operations for List' are derived by going back and
-- forth. With the SIP we can do better and transport properties for
-- user defined operations (assuming that the operations are
-- well-defined wrt to the forward direction of the equivalence).
open import Cubical.Foundations.SIP
open import Cubical.Structures.Axioms
open import Cubical.Structures.Product
open import Cubical.Structures.Pointed
open import Cubical.Structures.Function


-- For illustrative purposes we first apply the SIP manually. This
-- requires quite a bit of boilerplate code which is automated in the
-- next module.
module manualSIP (A : Type) where

  -- First define the raw structure without axioms. This is just the
  -- signature of _++_ and rev.
  RawStruct : Type → Type
  RawStruct X = (X → X → X) × (X → X)

  -- Some boilerplate code which can be automated
  e1 : StrEquiv (λ x → x → x → x) ℓ-zero
  e1 = FunctionEquivStr+ pointedEquivAction
                         (FunctionEquivStr+ pointedEquivAction PointedEquivStr)

  e2 : StrEquiv (λ x → x → x) ℓ-zero
  e2 = FunctionEquivStr+ pointedEquivAction PointedEquivStr

  RawEquivStr : StrEquiv RawStruct _
  RawEquivStr = ProductEquivStr e1 e2

  rawUnivalentStr : UnivalentStr _ RawEquivStr
  rawUnivalentStr = productUnivalentStr e1 he1 e2 he2
    where
    he2 : UnivalentStr (λ z → z → z) e2
    he2 = functionUnivalentStr+ pointedEquivAction pointedTransportStr
                                PointedEquivStr pointedUnivalentStr

    he1 : UnivalentStr (λ z → z → z → z) e1
    he1 = functionUnivalentStr+ pointedEquivAction pointedTransportStr e2 he2

  -- Now the property that we want to transport
  P : (X : Type) → RawStruct X → Type
  P X (_++_ , rev) = ((xs ys : X) → rev (xs ++ ys) ≡ rev ys ++ rev xs)

  -- Package things up for List
  List-Struct : Σ[ X ∈ Type ] (Σ[ s ∈ RawStruct X ] (P X s))
  List-Struct = List A , (_++_ , rev) , rev-++-distr


  -- We now give direct definitions of ++' and rev' for List'
  _++'_ : List' A → List' A → List' A
  [] ++' ys        = ys
  (xs ∷' x) ++' ys = (xs ++' ys) ∷' x

  rev' : List' A → List' A
  rev' [] = []
  rev' (xs ∷' x) = rev' xs ++' ([] ∷' x)

  -- We then package this up into a raw structure on List'
  List'-RawStruct : Σ[ X ∈ Type ] (RawStruct X)
  List'-RawStruct = List' A , (_++'_ , rev')

  -- Finally we prove that toList' commutes with _++_ and rev. Note
  -- that this could be a lot more complex, see for example the Matrix
  -- example (Cubical.Algebra.Matrix).
  toList'-++ : (xs ys : List A) → toList' (xs ++ ys) ≡ toList' xs ++' toList' ys
  toList'-++ [] ys = refl
  toList'-++ (x ∷ xs) ys i = toList'-++ xs ys i ∷' x

  toList'-rev : (xs : List A) → toList' (rev xs) ≡ rev' (toList' xs)
  toList'-rev [] = refl
  toList'-rev (x ∷ xs) = toList'-++ (rev xs) (x ∷ []) ∙ cong (_++' ([] ∷' x)) (toList'-rev xs)

  -- We can now get the property for ++' and rev' via the SIP
  rev-++-distr' : (xs ys : List' A) → rev' (xs ++' ys) ≡ rev' ys ++' rev' xs
  rev-++-distr' = transferAxioms rawUnivalentStr List-Struct List'-RawStruct
                        (ListEquiv , toList'-++ , toList'-rev)

  -- Note that rev-++-distr' is really talking about the direct
  -- definitions of ++' and rev', not the transported operations as in
  -- the previous attempt.



-- We now automate parts of the above construction
open import Cubical.Structures.Auto

module SIP-auto (A : Type) where

  -- First define the raw structure without axioms. This is just the
  -- signature of _++_ and rev.
  RawStruct : Type → Type
  RawStruct X = (X → X → X) × (X → X)

  -- Some automated SIP magic
  RawEquivStr : _
  RawEquivStr = AutoEquivStr RawStruct

  rawUnivalentStr : UnivalentStr _ RawEquivStr
  rawUnivalentStr = autoUnivalentStr RawStruct

  -- Now the property that we want to transport
  P : (X : Type) → RawStruct X → Type
  P X (_++_ , rev) = ((xs ys : X) → rev (xs ++ ys) ≡ rev ys ++ rev xs)

  -- Package things up for List
  List-Struct : Σ[ X ∈ Type ] (Σ[ s ∈ RawStruct X ] (P X s))
  List-Struct = List A , (_++_ , rev) , rev-++-distr


  -- We now give direct definitions of ++' and rev' for List'
  _++'_ : List' A → List' A → List' A
  [] ++' ys        = ys
  (xs ∷' x) ++' ys = (xs ++' ys) ∷' x

  rev' : List' A → List' A
  rev' [] = []
  rev' (xs ∷' x) = rev' xs ++' ([] ∷' x)

  -- We then package this up into a raw structure on List'
  List'-RawStruct : Σ[ X ∈ Type ] (RawStruct X)
  List'-RawStruct = List' A , (_++'_ , rev')

  -- Finally we prove that toList' commutes with _++_ and rev. Note
  -- that this could be a lot more complex, see for example the Matrix
  -- example (Cubical.Algebra.Matrix).
  toList'-++ : (xs ys : List A) → toList' (xs ++ ys) ≡ toList' xs ++' toList' ys
  toList'-++ [] ys = refl
  toList'-++ (x ∷ xs) ys i = toList'-++ xs ys i ∷' x

  toList'-rev : (xs : List A) → toList' (rev xs) ≡ rev' (toList' xs)
  toList'-rev [] = refl
  toList'-rev (x ∷ xs) = toList'-++ (rev xs) (x ∷ []) ∙ cong (_++' ([] ∷' x)) (toList'-rev xs)

  -- We can now get the property for ++' and rev' via the SIP
  rev-++-distr' : (xs ys : List' A) → rev' (xs ++' ys) ≡ rev' ys ++' rev' xs
  rev-++-distr' = transferAxioms rawUnivalentStr List-Struct List'-RawStruct
                        (ListEquiv , toList'-++ , toList'-rev)

  -- Note that rev-++-distr' is really talking about the direct
  -- definitions of ++' and rev', not the transported operations as in
  -- the previous attempt.
