{-# OPTIONS --safe #-}

module Cubical.Categories.Commutativity where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} where
  open Category C

  compSq : ∀ {x y z w u v} {f : C [ x , y ]} {g h} {k : C [ z , w ]} {l} {m} {n : C [ u , v ]}
       -- square 1
       → f ⋆ g ≡ h ⋆ k
       -- square 2 (sharing g)
       → k ⋆ l ≡ m ⋆ n
       → f ⋆ (g ⋆ l) ≡ (h ⋆ m) ⋆ n
  compSq {f = f} {g} {h} {k} {l} {m} {n} p q
    = f ⋆ (g ⋆ l)
    ≡⟨ sym (⋆Assoc _ _ _) ⟩
      (f ⋆ g) ⋆ l
    ≡⟨ cong (_⋆ l) p ⟩
      (h ⋆ k) ⋆ l
    ≡⟨ ⋆Assoc _ _ _ ⟩
      h ⋆ (k ⋆ l)
    ≡⟨ cong (h ⋆_) q ⟩
      h ⋆ (m ⋆ n)
    ≡⟨ sym (⋆Assoc _ _ _) ⟩
      (h ⋆ m) ⋆ n
    ∎
