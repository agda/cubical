
module Cubical.Categories.Equivalence.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  renaming (isEquiv to isEquivMap)
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism
open import Cubical.Categories.Equivalence.Base
open import Cubical.HITs.PropositionalTruncation

open Category
open Functor
open NatIso
open isIso
open WeakInverse

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

-- Equivalence implies Full, Faithul, and Essentially Surjective

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  symWeakInverse : ∀ {F : Functor C D} → (e : WeakInverse F) → WeakInverse (e .invFunc)
  symWeakInverse {F} record { invFunc = G ; η = η ; ε = ε } = record { invFunc = F ; η = symNatIso ε ; ε = symNatIso η }

  isEquiv→Faithful : ∀ {F : Functor C D} → isEquivalence F → isFaithful F
  isEquiv→Faithful {F} = rec (isPropΠ5 (λ _ _ _ _ _ → C .isSetHom _ _)) lifted
    where
      lifted : WeakInverse F → isFaithful F
      lifted record { invFunc = G
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
  isEquiv→Full {F} = rec (isPropΠ3 (λ _ _ _ → isPropPropTrunc)) lifted
    where
      lifted : WeakInverse F → isFull F
      lifted eq@record { invFunc = G
                             ; η = η
                             ; ε = _ }
        c c' g = ∣ h , isEquiv→Faithful ∣ symWeakInverse eq ∣₁ _ _ _ _ GFh≡Gg ∣₁ -- apply faithfulness of G
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
  isEquiv→Surj = rec (isPropΠ (λ _ → isPropPropTrunc))
    (λ wkInv d → ∣ (wkInv .invFunc ⟅ d ⟆) , isIso→CatIso ((wkInv .ε .nIso) d) ∣₁)


-- A fully-faithful functor that induces equivalence on objects is an equivalence

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} where

  isFullyFaithful+isEquivF-ob→isEquiv : isFullyFaithful F → isEquivMap (F .F-ob) → isEquivalence F
  isFullyFaithful+isEquivF-ob→isEquiv fullfaith isequiv = ∣ w ∣₁
    where
    open Iso
    open IsoOver

    MorC : C .ob × C .ob → Type _
    MorC (x , y) = C [ x , y ]

    MorD : D .ob × D .ob → Type _
    MorD (x , y) = D [ x , y ]

    F-Mor : ((x , y) : C .ob × C .ob) → C [ x , y ] → D [ F .F-ob x , F .F-ob y ]
    F-Mor _ = F .F-hom

    equiv-ob² : C .ob × C .ob ≃ D .ob × D .ob
    equiv-ob² = ≃-× (_ , isequiv) (_ , isequiv)

    iso-ob  = equivToIso (_ , isequiv)
    iso-hom = equivOver→IsoOver {P = MorC} {Q = MorD} equiv-ob² F-Mor (λ (x , y) → fullfaith x y)

    w-inv : Functor D C
    w-inv .F-ob = iso-ob .inv
    w-inv .F-hom = iso-hom .inv _
    w-inv .F-id {x = x} = isFullyFaithful→Faithful {F = F} fullfaith _ _ _ _ (p ∙ sym (F .F-id))
      where
      p : _
      p i =
        comp
        (λ j → D [ iso-ob .sec x (~ j) , iso-ob .sec x (~ j) ])
        (λ j → λ
          { (i = i0) → iso-hom .rightInv _ (D .id {x = x}) (~ j)
          ; (i = i1) → D .id {x = iso-ob .sec x (~ j)} })
        (D .id {x = x})
    w-inv .F-seq {x = x} {z = z} f g = isFullyFaithful→Faithful {F = F} fullfaith _ _ _ _ (p ∙ sym (F .F-seq _ _))
      where
      p : _
      p i =
        comp
        (λ j → D [ iso-ob .sec x (~ j) , iso-ob .sec z (~ j) ])
        (λ j → λ
          { (i = i0) → iso-hom .rightInv _ (f ⋆⟨ D ⟩ g) (~ j)
          ; (i = i1) → iso-hom .rightInv _ f (~ j) ⋆⟨ D ⟩ iso-hom .rightInv _ g (~ j) })
        (f ⋆⟨ D ⟩ g)

    w-η-path : 𝟙⟨ C ⟩ ≡ w-inv ∘F F
    w-η-path = Functor≡ (λ x → sym (retIsEq isequiv x)) (λ {x} {y} f → (λ i → iso-hom .leftInv (x , y) f (~ i)))

    w-ε-path : F ∘F w-inv ≡ 𝟙⟨ D ⟩
    w-ε-path = Functor≡ (λ x → secIsEq isequiv x) (λ {x} {y} f i → iso-hom .rightInv (x , y) f i)

    w : WeakInverse F
    w .invFunc = w-inv
    w .η = pathToNatIso w-η-path
    w .ε = pathToNatIso w-ε-path
