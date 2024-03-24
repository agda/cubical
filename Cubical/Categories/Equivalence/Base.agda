{-# OPTIONS --safe #-}
module Cubical.Categories.Equivalence.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open Category
open Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

record WeakInverse {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                     (func : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    invFunc : Functor D C

    η : 𝟙⟨ C ⟩ ≅ᶜ invFunc ∘F func
    ε : func ∘F invFunc ≅ᶜ 𝟙⟨ D ⟩

-- Composition of weak inverses is a weak inverse
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {F : Functor C D} {G : Functor D E}
  where

  open Category
  open Functor
  open NatTrans
  open WeakInverse
  open NatIso
  open isIso

  isEquivalenceComp : WeakInverse F → WeakInverse G → WeakInverse (G ∘F F)
  isEquivalenceComp Feq Geq = record { invFunc = F'∘G' ;
                                       η = η-iso ;
                                       ε = ε-iso } where
    F'∘G' : Functor E C
    F'∘G' = Feq .invFunc ∘F  Geq .invFunc
    η-iso : NatIso 𝟙⟨ C ⟩ (F'∘G' ∘F (G ∘F F))
    η-iso = seqNatIso
      -- proof that 1 and (F' F) are iso
      (Feq .η)
      -- proof that (F' F) and (F' G') (G F) are iso
      (seqNatIso
        -- precompose nested iso with F'
        ((Feq .invFunc) ∘ʳi seqNatIso
          -- proof that F and (G' G) F are isomorphic
          (seqNatIso
            -- proof that F and 1 F are iso
            (symNatIso (CAT⋆IdR {F = F}))
            -- proof that 1 F and (G' G) F are iso (whisker with F)
            (F ∘ˡi (Geq .η)))
          -- associate the parentheses (G' G) F and G' (G F)
          (symNatIso (CAT⋆Assoc F G (Geq .invFunc)))
        )
        -- fix final assoc F' (G' (G F)) iso to (F' G') (G F)
        (CAT⋆Assoc (G ∘F F) (Geq .invFunc) (Feq .invFunc))
      )

    ε-iso : NatIso ((G ∘F F) ∘F F'∘G') 𝟙⟨ E ⟩
    ε-iso = seqNatIso
      -- proof that (G F) (F' G') and G G' are iso
      (seqNatIso
        -- proof that (G F) (F' G') and G (F (F' G')) are iso
        (symNatIso (CAT⋆Assoc (F'∘G') F G))
        -- post compose nested proof with G
        (G ∘ʳi seqNatIso
          -- proof that F (F' G') and 1 G' are iso
          (seqNatIso
            -- proof that F (F' G') and (F F') G' are iso
            (CAT⋆Assoc (Geq .invFunc) (Feq .invFunc) F)
            -- proof that (F F') G' and 1 G' are iso (whisker with G')
            ((Geq .invFunc) ∘ˡi (Feq .ε))
          )
          -- proof that (1 G') and G are iso
          (CAT⋆IdR {F = Geq .invFunc})
        )
      )
      -- proof that G G' and 1 are iso
      (Geq .ε)


-- I don't know of a good alternative representation of isEquivalence that
-- avoids truncation in the general case.  If the categories are univalent, then
-- an adjoint equivalence might be enough.
isEquivalence : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
              → (func : Functor C D) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
isEquivalence func = ∥ WeakInverse func ∥₁

record _≃ᶜ_ (C : Category ℓC ℓC') (D : Category ℓD ℓD') :
               Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  constructor equivᶜ
  field
    func : Functor C D
    isEquiv : isEquivalence func
