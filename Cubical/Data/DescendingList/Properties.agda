------------------------------------------------------------------------
-- Descending lists
--
-- Anders Mörtberg and Chuangjie Xu, October 2019
--
-- We define descending lists via simultaneous definitions and show
-- that they are isomorphic to finite multisets.  The conversion from
-- finite multisets to descending lists is exactly insertion sort.  We
-- obtain the concatenation operation on descending lists and its
-- properties by transporting those on finite multisets.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.List using (List ; [] ; _∷_)

open import Cubical.Relation.Nullary

open import Cubical.HITs.FiniteMultiset as FMSet hiding ([_])


module Cubical.Data.DescendingList.Properties
 (A : Type₀)
 (_≥_ : A → A → Type₀)
 where

open import Cubical.Data.DescendingList.Base A _≥_

toFMSet : DL → FMSet A
toFMSet []           = []
toFMSet (cons x u _) = x ∷ toFMSet u

toList : DL → List A
toList [] = []
toList (cons x u _) = x ∷ toList u

-- "x ≥ ALL the elements of u"
data _≥ᴬ_ (x : A) : List A → Type₀ where
 ≥ᴬ[]   : x ≥ᴬ []
 ≥ᴬcons : {y : A} {u : List A} → x ≥ y → x ≥ᴬ u → x ≥ᴬ (y ∷ u)

data descending : List A → Type₀ where
 []-descending   : descending []
 cons-descending : {x : A} {u : List A} → x ≥ᴬ u → descending u → descending (x ∷ u)

module DescendingDL
 (≥trans : {x y z : A} → x ≥ y → y ≥ z → x ≥ z)
 where

 ≥≥ᴴtrans : {x y : A} {u : DL}
          → x ≥ y → y ≥ᴴ u → x ≥ᴴ u
 ≥≥ᴴtrans _   ≥ᴴ[]         = ≥ᴴ[]
 ≥≥ᴴtrans x≥y (≥ᴴcons y≥z) = ≥ᴴcons (≥trans x≥y y≥z)

 ≥ᴴ→≥ᴬ : {x : A} {u : DL} → x ≥ᴴ u → x ≥ᴬ toList u
 ≥ᴴ→≥ᴬ ≥ᴴ[]                   = ≥ᴬ[]
 ≥ᴴ→≥ᴬ (≥ᴴcons {r = y≥u} x≥y) = ≥ᴬcons x≥y (≥ᴴ→≥ᴬ (≥≥ᴴtrans x≥y y≥u))

 descendingDL : (u : DL) → descending (toList u)
 descendingDL []             = []-descending
 descendingDL (cons x u x≥u) = cons-descending (≥ᴴ→≥ᴬ x≥u) (descendingDL u)


------------------------------------------------------------------------
-- Descending lists are a set.

head≡ : {x y : A} {u v : DL} {r : x ≥ᴴ u} {s : y ≥ᴴ v}
      → cons x u r ≡ cons y v s → x ≡ y
head≡ {x} = cong head
 where
  head : DL → A
  head []           = x
  head (cons z _ _) = z

tail≡ : {x y : A} {u v : DL} {r : x ≥ᴴ u} {s : y ≥ᴴ v}
      → cons x u r ≡ cons y v s → u ≡ v
tail≡ = cong tail
 where
  tail : DL → DL
  tail []           = []
  tail (cons _ u _) = u

caseDL : ∀ {ℓ} → {X : Type ℓ} → (x y : X) → DL → X
caseDL x y []           = x
caseDL x y (cons _ _ _) = y

[]≢cons : {x : A} {u : DL} {r : x ≥ᴴ u} → ¬ ([] ≡ cons x u r)
[]≢cons p = subst (caseDL Unit ⊥) p tt

cons≢[] : {x : A} {u : DL} {r : x ≥ᴴ u} → ¬ (cons x u r ≡ [])
cons≢[] p = subst (caseDL ⊥ Unit) p tt

module isSetDL
 (≥isPropValued : {x y : A} → isProp (x ≥ y))
 (discreteA : Discrete A)
 where

 ≥ᴴisPropValued : {x : A} {u : DL} → isProp (x ≥ᴴ u)
 ≥ᴴisPropValued ≥ᴴ[]         ≥ᴴ[]          = refl
 ≥ᴴisPropValued (≥ᴴcons x≥y) (≥ᴴcons x≥y') = cong ≥ᴴcons (≥isPropValued x≥y x≥y')

 cons≡ : {x y : A} {u v : DL} {r : x ≥ᴴ u} {s : y ≥ᴴ v}
       → x ≡ y → u ≡ v → cons x u r ≡ cons y v s
 cons≡ {x} p = subst P p d
  where
   P : A → Type₀
   P y = {u v : DL} {r : x ≥ᴴ u} {s : y ≥ᴴ v} → u ≡ v → cons x u r ≡ cons y v s
   d : P x
   d {u} q = subst Q q c
    where
     Q : (v : DL) → Type₀
     Q v = {r : x ≥ᴴ u} {s : x ≥ᴴ v} → cons x u r ≡ cons x v s
     c : Q u
     c = cong (cons x u) (≥ᴴisPropValued _ _)

 discreteDL : Discrete DL
 discreteDL []           []           = yes refl
 discreteDL []           (cons y v s) = no []≢cons
 discreteDL (cons x u r) []           = no cons≢[]
 discreteDL (cons x u r) (cons y v s) with discreteA x y
 discreteDL (cons x u r) (cons y v s) | yes x≡y with discreteDL u v
 discreteDL (cons x u r) (cons y v s) | yes x≡y | yes u≡v = yes (cons≡ x≡y u≡v)
 discreteDL (cons x u r) (cons y v s) | yes x≡y | no  u≢v = no (λ e → u≢v (tail≡ e))
 discreteDL (cons x u r) (cons y v s) | no  x≢y = no (λ e → x≢y (head≡ e))

 isSetDL : isSet DL
 isSetDL = Discrete→isSet discreteDL


------------------------------------------------------------------------
-- Descending lists are isomorphic to finite multisets.

module IsoToFMSet
 (discreteA : Discrete A)
 (≥dec : (x y : A) → Dec (x ≥ y))
 (≥isPropValued : {x y : A} → isProp (x ≥ y))
 (≥trans : {x y z : A} → x ≥ y → y ≥ z → x ≥ z)
 (≰→≥ : {x y : A} → ¬ (x ≥ y) → y ≥ x)
 (≤≥→≡ : {x y : A} → x ≥ y → y ≥ x → x ≡ y)
 where

 ------------------------------------------------------------------------
 -- The insert function
 --
 -- The type DL is defined simultaneously with the relation _≥ᴴ_.
 -- Hence the insert function has to be defined by simultaneously
 -- proving a property of _≥ᴴ_.

 insert : A → DL → DL
 ≥ᴴinsert : {x y : A} {u : DL}
          → y ≥ᴴ u → ¬ (x ≥ y) → y ≥ᴴ insert x u

 insert x  []          = [ x ]
 insert x (cons y u r) with ≥dec x y
 insert x (cons y u r) | yes x≥y = cons x (cons y u r) (≥ᴴcons x≥y)
 insert x (cons y u r) | no  x≱y = cons y (insert x u) (≥ᴴinsert r x≱y)

 ≥ᴴinsert ≥ᴴ[] x≱y = ≥ᴴcons (≰→≥ x≱y)
 ≥ᴴinsert {x} {y} {cons z u z≥u} (≥ᴴcons y≥z) x≱y with ≥dec x z
 ≥ᴴinsert {x} {y} {cons z u z≥u} (≥ᴴcons y≥z) x≱y | yes x≥z = ≥ᴴcons (≰→≥ x≱y)
 ≥ᴴinsert {x} {y} {cons z u z≥u} (≥ᴴcons y≥z) x≱y | no  x≱z = ≥ᴴcons y≥z

 open isSetDL ≥isPropValued discreteA

 insert-swap : (x y : A) (u : DL)
             → insert x (insert y u) ≡ insert y (insert x u)
 insert-swap x y [] with ≥dec x y
 insert-swap x y [] | yes x≥y with ≥dec y x
 insert-swap x y [] | yes x≥y | yes y≥x = cons≡ (≤≥→≡ x≥y y≥x) (cons≡ (≤≥→≡ y≥x x≥y) refl)
 insert-swap x y [] | yes x≥y | no  y≱x = cons≡ refl (cons≡ refl refl)
 insert-swap x y [] | no  x≱y with ≥dec y x
 insert-swap x y [] | no  x≱y | yes y≥x = cons≡ refl (cons≡ refl refl)
 insert-swap x y [] | no  x≱y | no  y≱x = ⊥.rec (x≱y (≰→≥ y≱x))
 insert-swap x y (cons z u z≥u) with ≥dec y z
 insert-swap x y (cons z u z≥u) | yes y≥z with ≥dec x y
 insert-swap x y (cons z u z≥u) | yes y≥z | yes x≥y with ≥dec x z
 insert-swap x y (cons z u z≥u) | yes y≥z | yes x≥y | yes x≥z with ≥dec y x
 insert-swap x y (cons z u z≥u) | yes y≥z | yes x≥y | yes x≥z | yes y≥x = cons≡ (≤≥→≡ x≥y y≥x) (cons≡ (≤≥→≡ y≥x x≥y) refl)
 insert-swap x y (cons z u z≥u) | yes y≥z | yes x≥y | yes x≥z | no  y≱x with ≥dec y z
 insert-swap x y (cons z u z≥u) | yes y≥z | yes x≥y | yes x≥z | no  y≱x | yes y≥z' = cons≡ refl (cons≡ refl refl)
 insert-swap x y (cons z u z≥u) | yes y≥z | yes x≥y | yes x≥z | no  y≱x | no  y≱z  = ⊥.rec (y≱z y≥z)
 insert-swap x y (cons z u z≥u) | yes y≥z | yes x≥y | no  x≱z = ⊥.rec (x≱z (≥trans x≥y y≥z))
 insert-swap x y (cons z u z≥u) | yes y≥z | no  x≱y with ≥dec x z
 insert-swap x y (cons z u z≥u) | yes y≥z | no  x≱y | yes x≥z with ≥dec y x
 insert-swap x y (cons z u z≥u) | yes y≥z | no  x≱y | yes x≥z | yes y≥x = cons≡ refl (cons≡ refl refl)
 insert-swap x y (cons z u z≥u) | yes y≥z | no  x≱y | yes x≥z | no  y≱x = ⊥.rec (x≱y (≰→≥ y≱x))
 insert-swap x y (cons z u z≥u) | yes y≥z | no  x≱y | no  x≱z with ≥dec y z
 insert-swap x y (cons z u z≥u) | yes y≥z | no  x≱y | no  x≱z | yes y≥z' = cons≡ refl (cons≡ refl refl)
 insert-swap x y (cons z u z≥u) | yes y≥z | no  x≱y | no  x≱z | no  y≱z  = ⊥.rec (y≱z y≥z)
 insert-swap x y (cons z u z≥u) | no  y≱z with ≥dec x z
 insert-swap x y (cons z u z≥u) | no  y≱z | yes x≥z with ≥dec y x
 insert-swap x y (cons z u z≥u) | no  y≱z | yes x≥z | yes y≥x = ⊥.rec (y≱z (≥trans y≥x x≥z))
 insert-swap x y (cons z u z≥u) | no  y≱z | yes x≥z | no  y≱x with ≥dec y z
 insert-swap x y (cons z u z≥u) | no  y≱z | yes x≥z | no  y≱x | yes y≥z  = ⊥.rec (y≱z y≥z)
 insert-swap x y (cons z u z≥u) | no  y≱z | yes x≥z | no  y≱x | no  y≱z' = cons≡ refl (cons≡ refl refl)
 insert-swap x y (cons z u z≥u) | no  y≱z | no  x≱z with ≥dec y z
 insert-swap x y (cons z u z≥u) | no  y≱z | no  x≱z | yes y≥z  = ⊥.rec (y≱z y≥z)
 insert-swap x y (cons z u z≥u) | no  y≱z | no  x≱z | no  y≱z' = cons≡ refl (insert-swap x y u)

 -- Insertion sort
 toDL : FMSet A → DL
 toDL = FMSet.Rec.f isSetDL [] insert insert-swap
 {-
 toDL []                  = []
 toDL (x ∷ u)             = insert x (toDL u)
 toDL (comm x y u i)      = insert-swap x y (toDL u) i
 toDL (trunc x y p q i j) = isSetDL (toDL x) (toDL y) (cong toDL p) (cong toDL q) i j
 -}

 insert-cons : (x : A) (u : DL) (r : x ≥ᴴ u)
             → insert x u ≡ cons x u r
 insert-cons x [] _ = cons≡ refl refl
 insert-cons x (cons y u _) _ with ≥dec x y
 insert-cons x (cons y u _) _            | yes x≥y = cons≡ refl refl
 insert-cons x (cons y u _) (≥ᴴcons x≥y) | no  x≱y = ⊥.rec (x≱y x≥y)

 toDL∘toFMSet≡id : (u : DL) → toDL (toFMSet u) ≡ u
 toDL∘toFMSet≡id [] = refl
 toDL∘toFMSet≡id (cons x u r) i =
   hcomp (λ j → λ { (i = i0) → insert x (toDL∘toFMSet≡id u (~ j))
                  ; (i = i1) → cons x u r })
         (insert-cons x u r i)

 insert-∷ : (x : A) (u : DL)
          → toFMSet (insert x u) ≡ x ∷ toFMSet u
 insert-∷ x [] = refl
 insert-∷ x (cons y u _) with ≥dec x y
 insert-∷ x (cons y u _) | yes x≥y = refl
 insert-∷ x (cons y u _) | no  x≱y = cong (λ z → y ∷ z) (insert-∷ x u) ∙ comm y x (toFMSet u)

 toFMSet∘toDL≡id : (u : FMSet A) → toFMSet (toDL u) ≡ u
 toFMSet∘toDL≡id = FMSet.ElimProp.f (trunc _ _)
                                    refl
                                    (λ x {u} p → insert-∷ x (toDL u) ∙ cong (λ z → x ∷ z) p)

 FMSet≡DL : FMSet A ≡ DL
 FMSet≡DL = isoToPath (iso toDL toFMSet toDL∘toFMSet≡id toFMSet∘toDL≡id)

 ------------------------------------------------------------------------
 -- Concatenation of sorted lists
 --
 -- Defined by transporting the one on finite multisets

 infixr 30 _++ᴰᴸ_

 _++ᴰᴸ_ : DL → DL → DL
 _++ᴰᴸ_ = transport (λ i → FMSet≡DL i → FMSet≡DL i → FMSet≡DL i) _++_

 []Path : PathP (λ i → FMSet≡DL i) [] []
 []Path i = transp (λ j → FMSet≡DL (i ∧ j)) (~ i) []

 ++Path : PathP (λ i → FMSet≡DL i → FMSet≡DL i → FMSet≡DL i) _++_ _++ᴰᴸ_
 ++Path i = transp (λ j → FMSet≡DL (i ∧ j) → FMSet≡DL (i ∧ j) → FMSet≡DL (i ∧ j)) (~ i) _++_

 unitl-++ᴰᴸ : ∀ u → [] ++ᴰᴸ u ≡ u
 unitl-++ᴰᴸ = transport (λ i → (u : FMSet≡DL i) → ++Path i ([]Path i) u ≡ u) unitl-++

 unitr-++ᴰᴸ : ∀ u → u ++ᴰᴸ [] ≡ u
 unitr-++ᴰᴸ = transport (λ i → (u : FMSet≡DL i) → ++Path i u ([]Path i) ≡ u) unitr-++

 assoc-++ᴰᴸ : ∀ u v w → u ++ᴰᴸ (v ++ᴰᴸ w) ≡ (u ++ᴰᴸ v) ++ᴰᴸ w
 assoc-++ᴰᴸ = transport (λ i → (u v w : FMSet≡DL i)
                             → ++Path i u (++Path i v w) ≡ ++Path i (++Path i u v) w)
                        assoc-++

 comm-++ᴰᴸ : ∀ u v → u ++ᴰᴸ v ≡ v ++ᴰᴸ u
 comm-++ᴰᴸ = transport (λ i → (u v : FMSet≡DL i) → ++Path i u v ≡ ++Path i v u) comm-++


 ------------------------------------------------------------------------
 -- Converting multisets to (descending) lists

 FMSet→List : FMSet A → List A
 FMSet→List u = toList (toDL u)
