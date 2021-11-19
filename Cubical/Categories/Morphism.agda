{-# OPTIONS --safe #-}
module Cubical.Categories.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where
  open Precategory C

  private
    variable
      x y z w : ob

  isMonic : Hom[ x , y ] → Type (ℓ-max ℓ ℓ')
  isMonic {x} {y} f =
    ∀ {z} {a a' : Hom[ z , x ]} → f ∘ a ≡ f ∘ a' → a ≡ a'

  isEpic : (Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
  isEpic {x} {y} g =
    ∀ {z} {b b' : Hom[ y , z ]} → b ∘ g ≡ b' ∘ g → b ≡ b'

  -- A morphism is split monic if it has a *retraction*
  isSplitMon : (Hom[ x , y ]) → Type ℓ'
  isSplitMon {x} {y} f = ∃[ r ∈ Hom[ y , x ] ] r ∘ f ≡ id

  -- A morphism is split epic if it has a *section*
  isSplitEpi : (Hom[ x , y ]) → Type ℓ'
  isSplitEpi {x} {y} g = ∃[ s ∈ Hom[ y , x ] ] g ∘ s ≡ id

  record areInv (f : Hom[ x , y ]) (g : Hom[ y , x ]) : Type ℓ' where
    field
      sec : g ⋆ f ≡ id
      ret : f ⋆ g ≡ id

  open areInv

  symAreInv : {f : Hom[ x , y ]} {g : Hom[ y , x ]} → areInv f g → areInv g f
  sec (symAreInv x) = ret x
  ret (symAreInv x) = sec x

  -- equational reasoning with inverses
  invMoveR : ∀ {f : Hom[ x , y ]} {g : Hom[ y , x ]} {h : Hom[ z , x ]} {k : Hom[ z , y ]}
           → areInv f g
           → h ⋆ f ≡ k
           → h ≡ k ⋆ g
  invMoveR {f = f} {g} {h} {k} ai p
    = h
    ≡⟨ sym (⋆IdR _) ⟩
      (h ⋆ id)
    ≡⟨ cong (h ⋆_) (sym (ai .ret)) ⟩
      (h ⋆ (f ⋆ g))
    ≡⟨ sym (⋆Assoc _ _ _) ⟩
      ((h ⋆ f) ⋆ g)
    ≡⟨ cong (_⋆ g) p ⟩
      k ⋆ g
    ∎

  invMoveL : ∀ {f : Hom[ x , y ]} {g : Hom[ y , x ]} {h : Hom[ y , z ]} {k : Hom[ x , z ]}
          → areInv f g
          → f ⋆ h ≡ k
          → h ≡ g ⋆ k
  invMoveL {f = f} {g} {h} {k} ai p
    = h
    ≡⟨ sym (⋆IdL _) ⟩
      id ⋆ h
    ≡⟨ cong (_⋆ h) (sym (ai .sec)) ⟩
      (g ⋆ f) ⋆ h
    ≡⟨ ⋆Assoc _ _ _ ⟩
      g ⋆ (f ⋆ h)
    ≡⟨ cong (g ⋆_) p ⟩
      (g ⋆ k)
    ∎

  record isIso (f : Hom[ x , y ]) : Type ℓ' where
    field
      inv : Hom[ y , x ]
      sec : inv ⋆ f ≡ id
      ret : f ⋆ inv ≡ id

  open isIso

  isIso→areInv : ∀ {f : Hom[ x , y ]}
               → (isI : isIso f)
               → areInv f (isI .inv)
  sec (isIso→areInv isI) = sec isI
  ret (isIso→areInv isI) = ret isI

  open CatIso

  -- isIso agrees with CatIso
  isIso→CatIso : ∀ {f : C [ x , y ]}
               → isIso f
               → CatIso {C = C} x y
  mor (isIso→CatIso {f = f} x) = f
  inv (isIso→CatIso x) = inv x
  sec (isIso→CatIso x) = sec x
  ret (isIso→CatIso x) = ret x

  CatIso→isIso : (cIso : CatIso {C = C} x y)
               → isIso (cIso .mor)
  inv (CatIso→isIso f) = inv f
  sec (CatIso→isIso f) = sec f
  ret (CatIso→isIso f) = ret f

  CatIso→areInv : (cIso : CatIso {C = C} x y)
                → areInv (cIso .mor) (cIso .inv)
  CatIso→areInv cIso = isIso→areInv (CatIso→isIso cIso)

  -- reverse of an iso is also an iso
  symCatIso : ∀ {x y}
             → CatIso {C = C} x y
             → CatIso {C = C} y x
  symCatIso (catiso mor inv sec ret) = catiso inv mor ret sec
