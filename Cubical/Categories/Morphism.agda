{-# OPTIONS --cubical --no-import-sorts --safe #-}

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

  isMonic : (Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
  isMonic {x} {y} f = ∀ {z : ob} {a a' : Hom[ z , x ]}
    → (f ∘ a ≡ f ∘ a') → (a ≡ a')

  isEpic : (Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
  isEpic {x} {y} g = ∀ {z : ob} {b b' : Hom[ y , z ]}
    → (b ∘ g ≡ b' ∘ g) → (b ≡ b')

  -- A morphism is split monic if it has a *retraction*
  isSplitMon : (Hom[ x , y ]) → Type ℓ'
  isSplitMon {x} {y} f = ∃[ r ∈ Hom[ y , x ] ] r ∘ f ≡ id x

  -- A morphism is split epic if it has a *section*
  isSplitEpi : (Hom[ x , y ]) → Type ℓ'
  isSplitEpi {x} {y} g = ∃[ s ∈ Hom[ y , x ] ] g ∘ s ≡ id y

  record areInv (f : Hom[ x , y ]) (g : Hom[ y , x ]) : Type ℓ' where
    field
      sec : g ⋆ f ≡ id y
      ret : f ⋆ g ≡ id x

  open areInv

  symAreInv : ∀ {f : Hom[ x , y ]} {g : Hom[ y , x ]}
            → areInv f g
            → areInv g f
  symAreInv record { sec = sec ; ret = ret } = record { sec = ret ; ret = sec }

  -- equational reasoning with inverses
  invMoveR : ∀ {f : Hom[ x , y ]} {g : Hom[ y , x ]} {h : Hom[ z , x ]} {k : Hom[ z , y ]}
           → areInv f g
           → h ⋆ f ≡ k
           → h ≡ k ⋆ g
  invMoveR {f = f} {g} {h} {k} ai p
    = h
    ≡⟨ sym (⋆IdR _) ⟩
      (h ⋆ id _)
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
      id _ ⋆ h
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
      sec : inv ⋆ f ≡ id y
      ret : f ⋆ inv ≡ id x

  open isIso

  isIso→areInv : ∀ {f : Hom[ x , y ]}
               → (isI : isIso f)
               → areInv f (isI .inv)
  isIso→areInv record { inv = inv ; sec = sec ; ret = ret } = record { sec = sec ; ret = ret }

  open CatIso

  -- isIso agrees with CatIso
  isIso→CatIso : ∀ {f : C [ x , y ]}
               → isIso f
               → CatIso {C = C} x y
  isIso→CatIso {f = f} record { inv = f⁻¹ ; sec = sec ; ret = ret } = catiso f f⁻¹ sec ret

  CatIso→isIso : (cIso : CatIso {C = C} x y)
               → isIso (cIso .mor)
  CatIso→isIso (catiso mor inv sec ret) = record { inv = inv ; sec = sec ; ret = ret }

  CatIso→areInv : (cIso : CatIso {C = C} x y)
                → areInv (cIso .mor) (cIso .inv)
  CatIso→areInv cIso = isIso→areInv (CatIso→isIso cIso)

  -- reverse of an iso is also an iso
  symCatIso : ∀ {x y}
             → CatIso {C = C} x y
             → CatIso {C = C} y x
  symCatIso (catiso mor inv sec ret) = catiso inv mor ret sec
