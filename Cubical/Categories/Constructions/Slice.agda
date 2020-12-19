{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
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

record SliceHom (a b : SliceOb) : TypeC where
  constructor slicehom
  field
    S-hom : C [ S-ob a , S-ob b ]
    -- commutative diagram
    S-comm : S-hom ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a


SliceOb-≡-intro : ∀ {x y} {f : C [ x , c ]} {g : C [ y , c ]}
                → (p : x ≡ y)
                → PathP (λ i → C [ p i , c ]) f g
                → sliceob {x} f ≡ sliceob {y} g
SliceOb-≡-intro p q = λ i → sliceob (q i)

SliceHom-≡-intro : ∀ {a b} {f g} {c₁} {c₂}
                → (p : f ≡ g)
                → PathP (λ i → (p i) ⋆⟨ C ⟩ (S-arr b) ≡ S-arr a) c₁ c₂
                → slicehom f c₁ ≡ slicehom g c₂
SliceHom-≡-intro p q = λ i → slicehom (p i) (q i)
-- SliceOb-≡-intro p q = λ i → sliceob (q i)

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

instance
  SliceIsCat : isCategory SliceCat
  homIsSet SliceIsCat = λ x₁ y₁ x₂ y₂ → {!!}
