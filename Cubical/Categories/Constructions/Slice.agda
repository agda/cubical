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

SliceCat : Precategory _ _
ob SliceCat = SliceOb
Hom[_,_] SliceCat = SliceHom
id SliceCat (sliceob {x} f) = slicehom (C .id x) (C .⋆IdL _)
_⋆_ SliceCat (slicehom f p) (slicehom g p') = slicehom (f ⋆⟨ C ⟩ g) {!!}

-- private
--   variable
--     ℓ ℓ' : Level

-- record SlibO

-- record SliceCat (C : Precategory ℓ ℓ') (c : Precategory.ob C) {{isC : isCategory C}}: Type (ℓ-max ℓ ℓ') where
--   open Precategory C
--   field
--     sliceOb : Σ[ x ∈ ob ] C [ x , c ]
--     sliceHom : ∀ {x y} Σ[ f ∈ C [ x , y ] ] 
