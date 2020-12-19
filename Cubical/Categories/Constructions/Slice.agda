{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Foundations.HLevels
open Precategory

module Cubical.Categories.Constructions.Slice {ℓ ℓ' : Level} (C : Precategory ℓ ℓ') (c : C .ob) {{isC : isCategory C}} where

open import Cubical.Data.Sigma


TypeC : Type (ℓ-suc (ℓ-max ℓ ℓ'))
TypeC = Type (ℓ-max ℓ ℓ')

record SliceOb : TypeC where
  constructor sliceob
  field
    {S-ob} : C .ob
    S-arr : C [ S-ob , c ]

open SliceOb public

record SliceHom (a b : SliceOb) : Type ℓ' where
  constructor slicehom
  field
    S-hom : C [ S-ob a , S-ob b ]
    -- commutative diagram
    S-comm : S-hom ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a

open SliceHom

-- intro and elim for working with SliceHom equalities
SliceHom-≡-intro : ∀ {a b} {f g} {c₁} {c₂}
                → (p : f ≡ g)
                → PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
                → slicehom f c₁ ≡ slicehom g c₂
SliceHom-≡-intro p q = λ i → slicehom (p i) (q i)

SliceHom-≡-elim : ∀ {a b} {f g} {c₁} {c₂}
                → slicehom f c₁ ≡ slicehom g c₂
                → Σ[ p ∈ f ≡ g ] PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
SliceHom-≡-elim r = (λ i → S-hom (r i)) , λ i → S-comm (r i)

-- SliceHom is isomorphic to the Sigma type with the same components
SliceHom-Σ-Iso : ∀ {a b}
            → Iso (SliceHom a b) (Σ[ h ∈ C [ S-ob a , S-ob b ] ] h ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a)
fun SliceHom-Σ-Iso (slicehom h c) = h , c
inv SliceHom-Σ-Iso (h , c) = slicehom h c
rightInv SliceHom-Σ-Iso = λ x → refl
leftInv SliceHom-Σ-Iso = λ x → refl


-- Precategory definition

SliceCat : Precategory _ _
ob SliceCat = SliceOb
Hom[_,_] SliceCat = SliceHom
id SliceCat (sliceob {x} f) = slicehom (C .id x) (C .⋆IdL _)
_⋆_ SliceCat {sliceob j} {sliceob k} {sliceob l} (slicehom f p) (slicehom g p') =
  slicehom
    (f ⋆⟨ C ⟩ g)
    ( f ⋆⟨ C ⟩ g ⋆⟨ C ⟩ l
    ≡⟨ C .⋆Assoc _ _ _ ⟩
      f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ l)
    ≡⟨ cong (λ v → f ⋆⟨ C ⟩ v) p' ⟩
      f ⋆⟨ C ⟩ k
    ≡⟨ p ⟩
      j
    ∎)
⋆IdL SliceCat (slicehom S-hom S-comm) =
  SliceHom-≡-intro (⋆IdL C _) (toPathP (isC .homIsSet _ _ _ _))
⋆IdR SliceCat (slicehom S-hom S-comm) =
  SliceHom-≡-intro (⋆IdR C _) (toPathP (isC .homIsSet _ _ _ _))
⋆Assoc SliceCat f g h =
  SliceHom-≡-intro (⋆Assoc C _ _ _) (toPathP (isC .homIsSet _ _ _ _))


-- SliceCat is a Category

instance
  SliceIsCat : isCategory SliceCat
  homIsSet SliceIsCat {a} {b} (slicehom f c₁) (slicehom g c₂) p q = cong isoP p'≡q'
    where
      -- paths between SliceHoms are equivalent to the projection paths
      p' : Σ[ p ∈ f ≡ g ] PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
      p' = SliceHom-≡-elim p
      q' : Σ[ p ∈ f ≡ g ] PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
      q' = SliceHom-≡-elim q

      -- we want all paths between (dependent) paths of this type to be equal
      B = λ v → v ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a

      homIsGroupoidDep : isOfHLevelDep 2 B
      homIsGroupoidDep = isOfHLevel→isOfHLevelDep 2 (λ v x y → isSet→isGroupoid (isC .homIsSet) _ _ x y)

      -- we first prove that the projected paths are equal
      p'≡q' : p' ≡ q'
      p'≡q' = ΣPathP ((isC .homIsSet _ _ _ _) , toPathP (homIsGroupoidDep _ _ _ _ _))

      -- and then we can use equivalence to lift these paths up
      -- to actual SliceHom paths
      isoP = λ g → cong (inv SliceHom-Σ-Iso) (fun (ΣPathIsoPathΣ) g)
