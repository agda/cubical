{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Commutativity where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where
  open Precategory C
  -- -- commutative squares
  -- squareCommutes : ∀ {x y z w}
  --                → (f : C [ x , y ]) (g : C [ y , w ]) (h : C [ x , z ]) (k : C [ z , w ])
  --                → Type ℓ'
  -- squareCommutes f g h k = f ⋆ g ≡ h ⋆ k

  -- commutative squares compose
  _<>_ : ∀ {x y z w u v} {f : C [ x , y ]} {g h} {k : C [ z , w ]} {l} {m : C [ u , v ]} {n}
       -- square 1
       → f ⋆ g ≡ h ⋆ k
       -- square 2 (sharing g)
       → l ⋆ m ≡ g ⋆ n
       → (f ⋆ l) ⋆ m ≡ h ⋆ (k ⋆ n)
  _<>_ {f = f} {g} {h} {k} {l} {m} {n} p q
    = (f ⋆ l) ⋆ m
    ≡⟨ ⋆Assoc _ _ _ ⟩
      f ⋆ (l ⋆ m)
    ≡⟨ cong (f ⋆_) q ⟩
      f ⋆ (g ⋆ n)
    ≡⟨ sym (⋆Assoc _ _ _) ⟩
      (f ⋆ g) ⋆ n
    ≡⟨ cong (_⋆ n) p ⟩
      (h ⋆ k) ⋆ 
    ≡⟨ ⋆Assoc _ _ _ ⟩
      h ⋆ (k ⋆ n)
    ∎
