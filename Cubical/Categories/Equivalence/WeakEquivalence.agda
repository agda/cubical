{-

Weak Equivalence between Categories

-}
{-# OPTIONS --safe #-}

module Cubical.Categories.Equivalence.WeakEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  renaming (isEquiv to isEquivMap ; equivFun to _≃$_)
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary

open import Cubical.Functions.Surjection
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Category.Path


private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    F : Functor C D

open Functor


-- Weak equivalences of categories,
-- namely fully-faithful and essentially surjective functors

record isWeakEquivalence {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
        (func : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field

    fullfaith : isFullyFaithful   func
    esssurj   : isEssentiallySurj func

record WeakEquivalence (C : Category ℓC ℓC') (D : Category ℓD ℓD')
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  constructor weakEquivalence
  field

    func : Functor C D
    isWeakEquiv : isWeakEquivalence func

open isWeakEquivalence
open WeakEquivalence

isPropIsWeakEquivalence : isProp (isWeakEquivalence F)
isPropIsWeakEquivalence =
  isPropRetract (λ x → fullfaith x , esssurj x) _ (λ _ → refl)
         (isProp× (isPropΠ2 λ _ _ → isPropIsEquiv _)
                  (isPropΠ λ _ → squash₁))

-- Equivalence is always weak equivalence.

isEquiv→isWeakEquiv : isEquivalence F → isWeakEquivalence F
isEquiv→isWeakEquiv isequiv .fullfaith = isEquiv→FullyFaithful isequiv
isEquiv→isWeakEquiv isequiv .esssurj   = isEquiv→Surj isequiv

isWeakEquivalenceTransportFunctor : (p : C ≡ D) → isWeakEquivalence (TransportFunctor p)
fullfaith (isWeakEquivalenceTransportFunctor {C = C} p) x y = isEquivTransport
  λ i → cong Category.Hom[_,_] p i
   (transport-filler (cong Category.ob p) x i)
   (transport-filler (cong Category.ob p) y i)
esssurj (isWeakEquivalenceTransportFunctor {C = C} p) d =
  ∣ (subst⁻ Category.ob p d) , pathToIso (substSubst⁻ Category.ob p _) ∣₁

≡→WeakEquivlance : C ≡ D → WeakEquivalence C D
func (≡→WeakEquivlance _) = _
isWeakEquiv (≡→WeakEquivlance b) = isWeakEquivalenceTransportFunctor b


-- Weak equivalence between univalent categories is equivalence,
-- in other words, they admit explicit inverse functor.

module _
  (isUnivC : isUnivalent C)
  (isUnivD : isUnivalent D)
  where

  open isUnivalent

  isEquivF-ob : {F : Functor C D} → isWeakEquivalence F → isEquivMap (F .F-ob)
  isEquivF-ob {F = F} is-w-equiv = isEmbedding×isSurjection→isEquiv
    (isFullyFaithful→isEmbd-ob isUnivC isUnivD {F = F} (is-w-equiv .fullfaith) ,
     isSurj→isSurj-ob isUnivD {F = F} (is-w-equiv .esssurj))

  isWeakEquiv→isEquiv : {F : Functor C D} → isWeakEquivalence F → isEquivalence F
  isWeakEquiv→isEquiv is-w-equiv =
    isFullyFaithful+isEquivF-ob→isEquiv (is-w-equiv .fullfaith) (isEquivF-ob is-w-equiv)

  Equivalence≃WeakEquivalence : C ≃ᶜ D ≃ WeakEquivalence C D
  Equivalence≃WeakEquivalence =
        isoToEquiv (iso _ (uncurry equivᶜ) (λ _ → refl) λ _ → refl)
     ∙ₑ Σ-cong-equiv-snd
           (λ _ → propBiimpl→Equiv squash₁ isPropIsWeakEquivalence
               isEquiv→isWeakEquiv isWeakEquiv→isEquiv)
     ∙ₑ isoToEquiv (iso (uncurry weakEquivalence) _ (λ _ → refl) λ _ → refl)


module _
  {C C' : Category ℓC ℓC'}
  (isUnivC : isUnivalent C)
  (isUnivC' : isUnivalent C')
  where

 open CategoryPath

 module _ {F : Functor C C'} (we : isWeakEquivalence F) where

  open Category

  ob≃ : C .ob ≃ C' .ob
  ob≃ = _ , isEquivF-ob isUnivC isUnivC' we

  Hom≃ : ∀ x y → C [ x , y ] ≃ C' [ ob≃ ≃$ x , ob≃ ≃$ y ]
  Hom≃ _ _ = F-hom F , fullfaith we _ _

  HomPathP : PathP (λ i → ua ob≃ i → ua ob≃ i → Type ℓC')
               (C [_,_]) (C' [_,_])
  HomPathP = RelPathP _ Hom≃

  WeakEquivlance→CategoryPath : CategoryPath C C'
  ob≡ WeakEquivlance→CategoryPath = ua ob≃
  Hom≡ WeakEquivlance→CategoryPath = HomPathP
  id≡ WeakEquivlance→CategoryPath = EquivJRel {_∻_ = C' [_,_]}
    (λ Ob e H[_,_] h[_,_] →
      (id* : ∀ {x : Ob} → H[ x , x ]) →
      ({x : Ob} → (h[ x , _ ] ≃$ id*) ≡ C' .id {e ≃$ x} )
      → PathP (λ i → {x : ua e i} →
          RelPathP e {_} {C' [_,_]} h[_,_] i x x) id* λ {x} → C' .id {x})
    (λ _ x i → glue (λ {(i = i0) → _ ; (i = i1) → _ }) (x i)) _ _ Hom≃ (C .id) (F-id F)

  ⋆≡ WeakEquivlance→CategoryPath = EquivJRel {_∻_ = C' [_,_]}
    (λ Ob e H[_,_] h[_,_] → (⋆* : BinaryRelation.isTrans' H[_,_]) →
      (∀ {x y z : Ob} f g → (h[ x , z ] ≃$ (⋆* f g)) ≡
            C' ._⋆_ (h[ x , _ ] ≃$ f) (h[ y , _ ] ≃$ g) )
      → PathP (λ i → BinaryRelation.isTrans' (RelPathP e h[_,_] i))
           ⋆*  (λ {x y z} → C' ._⋆_ {x} {y} {z}))
    (λ _ x i f g → glue (λ {(i = i0) → _ ; (i = i1) → _ })
        (x (unglue (i ∨ ~ i) f) (unglue (i ∨ ~ i) g) i  ))
      _ _ Hom≃ (C ._⋆_) (F-seq F)

 open Iso

 IsoCategoryPath : Iso (WeakEquivalence C C') (CategoryPath C C')
 fun IsoCategoryPath = WeakEquivlance→CategoryPath ∘f isWeakEquiv
 inv IsoCategoryPath = ≡→WeakEquivlance ∘f mk≡
 rightInv IsoCategoryPath b = CategoryPath≡
   (WeakEquivlance→CategoryPath (isWeakEquiv (≡→WeakEquivlance (mk≡ b)))) b
   (λ i j → Glue (C' .Category.ob) {φ = ~ j ∨ j ∨ i}
         (λ _ → _ , equivPathP
         {e = ob≃ (isWeakEquiv (≡→WeakEquivlance (mk≡ b)))} {f = idEquiv _}
         (transport-fillerExt⁻ (ob≡ b)) j))
    λ i j x y → Glue (C' [ unglue (~ j ∨ j ∨ i) x , unglue (~ j ∨ j ∨ i) y ])
        λ {(j = i0) → _ , Hom≃ (isWeakEquiv (≡→WeakEquivlance (mk≡ b))) _ _
          ;(j = i1) → _ , idEquiv _
          ;(i = i1) → _ , _
            , isProp→PathP (λ j → isPropΠ2 λ x y → isPropIsEquiv (transp (λ i₂ →
               let tr = transp (λ j' → ob≡ b (j ∨ (i₂ ∧ j'))) (~ i₂ ∨ j)
               in Hom≡ b (i₂ ∨ j) (tr x) (tr y)) j))
                (λ _ _ → fullfaith (isWeakEquiv (≡→WeakEquivlance (mk≡ b))) _ _)
                (λ _ _ → idIsEquiv _) j x y }


 leftInv IsoCategoryPath we = cong₂ weakEquivalence
   (Functor≡ (transportRefl ∘f (F-ob (func we)))
              λ {c} {c'} f → (λ j → transport
      (λ i → HomPathP (isWeakEquiv we) i
         (transport-filler-ua (ob≃ (isWeakEquiv we)) c  j i)
         (transport-filler-ua (ob≃ (isWeakEquiv we)) c' j i))
      f) ▷ transportRefl _ )
   (isProp→PathP (λ _ → isPropIsWeakEquivalence) _ _ )

 WeakEquivalence≃Path : WeakEquivalence C C' ≃ (C ≡ C')
 WeakEquivalence≃Path =
   isoToEquiv (compIso IsoCategoryPath CategoryPathIso)

 Equivalence≃Path : C ≃ᶜ C' ≃ (C ≡ C')
 Equivalence≃Path = Equivalence≃WeakEquivalence isUnivC isUnivC' ∙ₑ WeakEquivalence≃Path

is2GroupoidUnivalentCategory : is2Groupoid (Σ (Category ℓC ℓC') isUnivalent)
is2GroupoidUnivalentCategory (C , isUnivalentC) (C' , isUnivalentC') =
  isOfHLevelRespectEquiv 3
   (isoToEquiv (iso (uncurry weakEquivalence) _ (λ _ → refl) λ _ → refl)
      ∙ₑ WeakEquivalence≃Path isUnivalentC isUnivalentC' ∙ₑ Σ≡PropEquiv λ _ → isPropIsUnivalent)
    λ _ _ → isOfHLevelRespectEquiv 2 (Σ≡PropEquiv λ _ → isPropIsWeakEquivalence)
       (isOfHLevelFunctor 1 (isUnivalent.isGroupoid-ob isUnivalentC') _ _)
