{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Functors where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Morphism renaming (isIso to isIsoC)
open import Cubical.Foundations.Prelude

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  open NatTrans
  open Functor

  FUNCTOR : Category (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  ob FUNCTOR           = Functor C D
  Hom[_,_] FUNCTOR     = NatTrans
  id FUNCTOR {F}       = idTrans F
  _⋆_ FUNCTOR          = seqTrans
  ⋆IdL FUNCTOR α       = makeNatTransPath λ i x → D .⋆IdL (α .N-ob x) i
  ⋆IdR FUNCTOR α       = makeNatTransPath λ i x → D .⋆IdR (α .N-ob x) i
  ⋆Assoc FUNCTOR α β γ = makeNatTransPath λ i x → D .⋆Assoc (α .N-ob x) (β .N-ob x) (γ .N-ob x) i
  isSetHom FUNCTOR     = isSetNatTrans

  open isIsoC renaming (inv to invC)
  -- componentwise iso is an iso in Functor
  FUNCTORIso : ∀ {F G : Functor C D} (α : F ⇒ G)
             → (∀ (c : C .ob) → isIsoC D (α ⟦ c ⟧))
             → isIsoC FUNCTOR α
  FUNCTORIso α is .invC .N-ob c = (is c) .invC
  FUNCTORIso {F} {G} α is .invC .N-hom {c} {d} f
    = invMoveL areInv-αc
               ( α ⟦ c ⟧ ⋆⟨ D ⟩ (G ⟪ f ⟫ ⋆⟨ D ⟩ is d .invC)
               ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
                 (α ⟦ c ⟧ ⋆⟨ D ⟩ G ⟪ f ⟫) ⋆⟨ D ⟩ is d .invC
               ≡⟨ sym (invMoveR areInv-αd (α .N-hom f)) ⟩
                 F ⟪ f ⟫
               ∎ )
    where
      areInv-αc : areInv _ (α ⟦ c ⟧) ((is c) .invC)
      areInv-αc = isIso→areInv (is c)

      areInv-αd : areInv _ (α ⟦ d ⟧) ((is d) .invC)
      areInv-αd = isIso→areInv (is d)
  FUNCTORIso α is .sec = makeNatTransPath (funExt (λ c → (is c) .sec))
  FUNCTORIso α is .ret = makeNatTransPath (funExt (λ c → (is c) .ret))
