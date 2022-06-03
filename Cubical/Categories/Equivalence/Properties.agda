{-# OPTIONS --safe #-}

module Cubical.Categories.Equivalence.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  renaming (isEquiv to isEquivMap)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism
open import Cubical.Categories.Equivalence.Base
open import Cubical.HITs.PropositionalTruncation.Base

open Category
open Functor
open NatIso
open isIso
open NatTrans
open isEquivalence

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

-- Equivalence implies Full, Faithul, and Essentially Surjective

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  symEquiv : ∀ {F : Functor C D} → (e : isEquivalence F) → isEquivalence (e .invFunc)
  symEquiv {F} record { invFunc = G ; η = η ; ε = ε } = record { invFunc = F ; η = symNatIso ε ; ε = symNatIso η }

  isEquiv→Faithful : ∀ {F : Functor C D} → isEquivalence F → isFaithful F
  isEquiv→Faithful {F} record { invFunc = G
                              ; η = η
                              ; ε = _ }
                   c c' f g p = f
                              ≡⟨ sqRL η ⟩
                                cIso .fst ⋆⟨ C ⟩ G ⟪ F ⟪ f ⟫ ⟫ ⋆⟨ C ⟩ c'Iso .snd .inv
                              ≡⟨ cong (λ v → cIso .fst ⋆⟨ C ⟩ (G ⟪ v ⟫) ⋆⟨ C ⟩ c'Iso .snd .inv) p ⟩
                                cIso .fst ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⟫ ⋆⟨ C ⟩ c'Iso .snd .inv
                              ≡⟨ sym (sqRL η) ⟩
                                g
                              ∎
    where

      -- isomorphism between c and GFc
      cIso = isIso→CatIso (η .nIso c)
      -- isomorphism between c' and GFc'
      c'Iso = isIso→CatIso (η .nIso c')

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  isEquiv→Full : ∀ {F : Functor C D} → isEquivalence F → isFull F
  isEquiv→Full {F} eq@record { invFunc = G
                             ; η = η
                             ; ε = _ }
               c c' g = ∣ h , isEquiv→Faithful (symEquiv eq) _ _ _ _ GFh≡Gg ∣₁ -- apply faithfulness of G
    where
      -- isomorphism between c and GFc
      cIso = isIso→CatIso (η .nIso c)
      -- isomorphism between c' and GFc'
      c'Iso = isIso→CatIso (η .nIso c')

      -- reverses
      cIso⁻ = symCatIso cIso
      c'Iso⁻ = symCatIso c'Iso

      h = cIso .fst ⋆⟨ C ⟩ G ⟪ g ⟫ ⋆⟨ C ⟩ c'Iso .snd .inv

      -- we show that both `G ⟪ g ⟫` and `G ⟪ F ⟪ h ⟫ ⟫`
      -- are equal to the same thing
      -- namely : cIso .inv ⋆⟨ C ⟩ h ⋆⟨ C ⟩ c'Iso .mor
      Gg≡ηhη : G ⟪ g ⟫ ≡ cIso .snd .inv ⋆⟨ C ⟩ h ⋆⟨ C ⟩ c'Iso .fst
      Gg≡ηhη = invMoveL cAreInv move-c' ∙ sym (C .⋆Assoc _ _ _)
        where
          cAreInv : areInv _ (cIso .fst) (cIso .snd .inv)
          cAreInv = CatIso→areInv cIso

          c'AreInv : areInv _ (c'Iso .fst) (c'Iso .snd .inv)
          c'AreInv = CatIso→areInv c'Iso

          move-c' : cIso .fst ⋆⟨ C ⟩ G ⟪ g ⟫ ≡ h ⋆⟨ C ⟩ c'Iso .fst
          move-c' = invMoveR (symAreInv c'AreInv) refl

      GFh≡Gg : G ⟪ F ⟪ h ⟫ ⟫ ≡ G ⟪ g ⟫
      GFh≡Gg = G ⟪ F ⟪ h ⟫ ⟫
             ≡⟨ sqLR η ⟩
               cIso .snd .inv ⋆⟨ C ⟩ h ⋆⟨ C ⟩ c'Iso .fst
             ≡⟨ sym Gg≡ηhη ⟩
               G ⟪ g ⟫
             ∎

  isEquiv→FullyFaithful :  ∀ {F : Functor C D} → isEquivalence F → isFullyFaithful F
  isEquiv→FullyFaithful {F = F} h = isFull+Faithful→isFullyFaithful {F = F} (isEquiv→Full h) (isEquiv→Faithful h)

  isEquiv→Surj : ∀ {F : Functor C D} → isEquivalence F → isEssentiallySurj F
  isEquiv→Surj isE d = ∣ (isE .invFunc ⟅ d ⟆) , isIso→CatIso ((isE .ε .nIso) d) ∣₁


-- A fully-faithful functor that induces equivalences on objects is an equivalence

Mor : (C : Category ℓC ℓC') → Type _
Mor C = Σ[ x ∈ C .ob ] Σ[ y ∈ C .ob ] C [ x , y ]

projMor : {C : Category ℓC ℓC'} → Mor C → C .ob × C .ob
projMor (x , y , _) = x , y

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} where

  F-Mor : Mor C → Mor D
  F-Mor (x , y , f) = F .F-ob x , F .F-ob y , F .F-hom f

  isFullyFaithful+isEquivF-ob→isEquiv : isFullyFaithful F → isEquivMap (F .F-ob) → isEquivalence F
  isFullyFaithful+isEquivF-ob→isEquiv fullfaith isequiv = w
    where
    isEquivF-Mor : isEquivMap F-Mor
    isEquivF-Mor = {!!}

    w-inv-ob : D .ob → C .ob
    w-inv-ob = invIsEq isequiv

    w-hom-path : {x y : D .ob}(f : D [ x , y ])
      → (i : I) → D [ secIsEq isequiv x (~ i) , secIsEq isequiv y (~ i) ]
    w-hom-path {x = x} {y = y} f i =
      transport-filler (λ i → D [ secIsEq isequiv x (~ i) , secIsEq isequiv y (~ i) ]) f i

    w-inv : Functor D C
    w-inv .F-ob = invIsEq isequiv
    w-inv .F-hom f = invIsEq (fullfaith _ _) (w-hom-path f i1)
    w-inv .F-id = {!!}
    w-inv .F-seq = {!!}

    w-η-path : 𝟙⟨ C ⟩ ≡ w-inv ∘F F
    w-η-path = Functor≡ (λ x → sym (retIsEq isequiv x)) {!!}

    w-ε-path : F ∘F w-inv ≡ 𝟙⟨ D ⟩
    w-ε-path = Functor≡ (λ x → secIsEq isequiv x) {!!}

    w : isEquivalence F
    w .invFunc = w-inv
    w .η = pathToNatIso w-η-path
    w .ε = pathToNatIso w-ε-path
