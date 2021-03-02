{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Instances.Functors where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism renaming (isIso to isIsoC)
open import Cubical.Foundations.Prelude

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') ⦃ isCatD : isCategory D ⦄ where
  open Precategory
  open NatTrans
  open Functor

  FUNCTOR : Precategory (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  FUNCTOR .ob = Functor C D
  FUNCTOR .Hom[_,_] = NatTrans
  FUNCTOR .id = idTrans
  FUNCTOR ._⋆_ = seqTrans
  FUNCTOR .⋆IdL α = makeNatTransPath λ i x → D .⋆IdL (α .N-ob x) i
  FUNCTOR .⋆IdR α = makeNatTransPath λ i x → D .⋆IdR (α .N-ob x) i
  FUNCTOR .⋆Assoc α β γ = makeNatTransPath λ i x → D .⋆Assoc (α .N-ob x) (β .N-ob x) (γ .N-ob x) i

  instance
    isCatFUNCTOR : isCategory FUNCTOR
    isCatFUNCTOR .isSetHom = isSetNat

  open isIsoC renaming (inv to invC)
  -- component wise iso is an iso in Functor
  FUNCTORIso : ∀ {F G : Functor C D} (α : F ⇒ G)
             → (∀ (c : C .ob) → isIsoC {C = D} (α ⟦ c ⟧))
             → isIsoC {C = FUNCTOR} α
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
      areInv-αc : areInv (α ⟦ c ⟧) ((is c) .invC)
      areInv-αc = isIso→areInv (is c)

      areInv-αd : areInv (α ⟦ d ⟧) ((is d) .invC)
      areInv-αd = isIso→areInv (is d)
  FUNCTORIso α is .sec = makeNatTransPath (funExt (λ c → (is c) .sec))
  FUNCTORIso α is .ret = makeNatTransPath (funExt (λ c → (is c) .ret))
