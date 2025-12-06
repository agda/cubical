{-

This module represents a path between categories (defined as records) as equivalent
to records of paths between fields.
It omits contractible fields for efficiency.

This helps greatly with efficiency in Cubical.Categories.Equivalence.WeakEquivalence.

This construction can be viewed as repeated application of `ΣPath≃PathΣ` and `Σ-contractSnd`.

-}

module Cubical.Categories.Category.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Relation.Binary.Base

open import Cubical.Categories.Category.Base



open Category

private
  variable
    ℓ ℓ' : Level

record CategoryPath (C C' : Category ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
 no-eta-equality
 field
   ob≡ : C .ob ≡ C' .ob
   Hom≡ : PathP (λ i → ob≡ i → ob≡ i → Type ℓ') (C .Hom[_,_]) (C' .Hom[_,_])
   id≡ : PathP (λ i → BinaryRelation.isRefl' (Hom≡ i)) (C .id) (C' .id)
   ⋆≡ : PathP (λ i → BinaryRelation.isTrans' (Hom≡ i)) (C ._⋆_) (C' ._⋆_)


 isSetHom≡ : PathP (λ i → ∀ {x y} → isSet (Hom≡ i x y))
   (C .isSetHom) (C' .isSetHom)
 isSetHom≡ = isProp→PathP (λ _ → isPropImplicitΠ2 λ _ _ → isPropIsSet) _ _

 mk≡ : C ≡ C'
 ob (mk≡ i) = ob≡ i
 Hom[_,_] (mk≡ i) = Hom≡ i
 id (mk≡ i) = id≡ i
 _⋆_ (mk≡ i) = ⋆≡ i
 ⋆IdL (mk≡ i) =
   isProp→PathP
   (λ i → isPropImplicitΠ2 λ x y → isPropΠ
    λ f → isOfHLevelPath' 1 (isSetHom≡ i {x} {y}) (⋆≡ i (id≡ i) f) f)
    (C .⋆IdL) (C' .⋆IdL) i
 ⋆IdR (mk≡ i) =
   isProp→PathP
   (λ i → isPropImplicitΠ2 λ x y → isPropΠ
    λ f → isOfHLevelPath' 1 (isSetHom≡ i {x} {y}) (⋆≡ i f (id≡ i)) f)
    (C .⋆IdR) (C' .⋆IdR) i
 ⋆Assoc (mk≡ i) =
     isProp→PathP
   (λ i → isPropImplicitΠ4 λ x y z w → isPropΠ3
    λ f f' f'' → isOfHLevelPath' 1 (isSetHom≡ i {x} {w})
     (⋆≡ i (⋆≡ i {x} {y} {z} f f') f'') (⋆≡ i f (⋆≡ i f' f'')))
    (C .⋆Assoc) (C' .⋆Assoc) i
 isSetHom (mk≡ i) = isSetHom≡ i


module _ {C C' : Category ℓ ℓ'} where

 open CategoryPath

 ≡→CategoryPath : C ≡ C' → CategoryPath C C'
 ≡→CategoryPath pa = c
  where
  c : CategoryPath C C'
  ob≡ c = cong ob pa
  Hom≡ c = cong Hom[_,_] pa
  id≡ c = cong id pa
  ⋆≡ c = cong _⋆_ pa


 module _ (b : C ≡ C') where
   private
     cp = ≡→CategoryPath b
     b' = CategoryPath.mk≡ cp

   CategoryPathIsoRightInv : mk≡ (≡→CategoryPath b) ≡ b
   CategoryPathIsoRightInv i j .ob = b j .ob
   CategoryPathIsoRightInv i j .Hom[_,_] = b j .Hom[_,_]
   CategoryPathIsoRightInv i j .id = b j .id
   CategoryPathIsoRightInv i j ._⋆_ = b j ._⋆_
   CategoryPathIsoRightInv i j .⋆IdL = isProp→SquareP (λ i j →
      isPropImplicitΠ2 λ x y → isPropΠ λ f →
        (isSetHom≡ cp j {x} {y})
         (b j ._⋆_ (b j .id) f) f)
      refl refl (λ j → b' j .⋆IdL) (λ j → b j .⋆IdL) i j
   CategoryPathIsoRightInv i j .⋆IdR = isProp→SquareP (λ i j →
      isPropImplicitΠ2 λ x y → isPropΠ λ f →
        (isSetHom≡ cp j {x} {y})
         (b j ._⋆_ f (b j .id)) f)
      refl refl (λ j → b' j .⋆IdR) (λ j → b j .⋆IdR) i j
   CategoryPathIsoRightInv i j .⋆Assoc = isProp→SquareP (λ i j →
      isPropImplicitΠ4 λ x y z w → isPropΠ3 λ f g h →
        (isSetHom≡ cp j {x} {w})
         (b j ._⋆_ (b j ._⋆_ {x} {y} {z} f g) h)
         (b j ._⋆_ f (b j ._⋆_ g h)))
      refl refl (λ j → b' j .⋆Assoc) (λ j → b j .⋆Assoc) i j
   CategoryPathIsoRightInv i j .isSetHom = isProp→SquareP (λ i j →
      isPropImplicitΠ2 λ x y → isPropIsSet {A = b j .Hom[_,_] x y})
      refl refl (λ j → b' j .isSetHom) (λ j → b j .isSetHom) i j

 CategoryPathIso : Iso (CategoryPath C C') (C ≡ C')
 Iso.fun CategoryPathIso = CategoryPath.mk≡
 Iso.inv CategoryPathIso = ≡→CategoryPath
 Iso.rightInv CategoryPathIso = CategoryPathIsoRightInv

 ob≡ (Iso.leftInv CategoryPathIso a i) = ob≡ a
 Hom≡ (Iso.leftInv CategoryPathIso a i) = Hom≡ a
 id≡ (Iso.leftInv CategoryPathIso a i) = id≡ a
 ⋆≡ (Iso.leftInv CategoryPathIso a i) = ⋆≡ a

 CategoryPath≡ : (cp cp' : CategoryPath C C') →
     (p≡ : ob≡ cp ≡ ob≡ cp') →
     SquareP (λ i j → (p≡ i) j → (p≡ i) j → Type ℓ')
          (Hom≡ cp) (Hom≡ cp') (λ _ → C .Hom[_,_]) (λ _ → C' .Hom[_,_])
          → cp ≡ cp'
 ob≡ (CategoryPath≡ _ _ p≡ _ i) = p≡ i
 Hom≡ (CategoryPath≡ _ _ p≡ h≡ i) = h≡ i
 id≡ (CategoryPath≡ cp cp' p≡ h≡ i) j {x} = isSet→SquareP
     (λ i j → isProp→PathP (λ i →
       isPropIsSet {A = BinaryRelation.isRefl' (h≡ i j)})
       (isSetImplicitΠ λ x → isSetHom≡ cp  j {x} {x})
       (isSetImplicitΠ λ x → isSetHom≡ cp' j {x} {x}) i)
    (id≡ cp) (id≡ cp') (λ _ → C .id) (λ _ → C' .id)
    i j {x}
 ⋆≡ (CategoryPath≡ cp cp' p≡ h≡ i) j {x} {y} {z} = isSet→SquareP
    (λ i j → isProp→PathP (λ i →
        isPropIsSet {A = BinaryRelation.isTrans' (h≡ i j)})
         (isSetImplicitΠ3 (λ x _ z → isSetΠ2 λ _ _ → isSetHom≡ cp  j {x} {z}))
         (isSetImplicitΠ3 (λ x _ z → isSetΠ2 λ _ _ → isSetHom≡ cp' j {x} {z})) i)
    (⋆≡ cp) (⋆≡ cp') (λ _ → C ._⋆_) (λ _ → C' ._⋆_)
    i j {x} {y} {z}
