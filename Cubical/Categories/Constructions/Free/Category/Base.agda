-- Free category over a directed graph/quiver
-- This time without any assumptions on the HLevels of the graph
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.Category.Base where

open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.UnderlyingGraph
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sigma

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

open Category
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans

module FreeCategory (G : Graph ℓg ℓg') where
    data Exp : G .Node → G .Node → Type (ℓ-max ℓg ℓg') where
      ↑_   : ∀ {A B} → G .Edge A B → Exp A B
      idₑ  : ∀ {A} → Exp A A
      _⋆ₑ_ : ∀ {A B C} → Exp A B → Exp B C → Exp A C
      ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
      ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
      ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
              → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
      isSetExp : ∀ {A B} → isSet (Exp A B)

    FreeCat : Category ℓg (ℓ-max ℓg ℓg')
    FreeCat .ob = G .Node
    FreeCat .Hom[_,_] = Exp
    FreeCat .id = idₑ
    FreeCat ._⋆_ = _⋆ₑ_
    FreeCat .⋆IdL = ⋆ₑIdL
    FreeCat .⋆IdR = ⋆ₑIdR
    FreeCat .⋆Assoc = ⋆ₑAssoc
    FreeCat .isSetHom = isSetExp

    η : Interp G FreeCat
    η ._$g_ = λ z → z
    η ._<$g>_ = ↑_

    module Semantics {ℓc ℓc'} (𝓒 : Category ℓc ℓc') (ı : GraphHom G (Ugr 𝓒)) where
      ⟦_⟧ : ∀ {A B} → Exp A B → 𝓒 [ ı $g A , ı $g B ]
      ⟦ ↑ x ⟧ = ı <$g> x
      ⟦ idₑ ⟧ = 𝓒 .id
      ⟦ e ⋆ₑ e' ⟧ = ⟦ e ⟧ ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧
      ⟦ ⋆ₑIdL e i ⟧ = 𝓒 .⋆IdL ⟦ e ⟧ i
      ⟦ ⋆ₑIdR e i ⟧ = 𝓒 .⋆IdR ⟦ e ⟧ i
      ⟦ ⋆ₑAssoc e e' e'' i ⟧ = 𝓒 .⋆Assoc ⟦ e ⟧ ⟦ e' ⟧ ⟦ e'' ⟧ i
      ⟦ isSetExp e e' p q i j ⟧ = 𝓒 .isSetHom ⟦ e ⟧ ⟦ e' ⟧ (cong ⟦_⟧ p) (cong ⟦_⟧ q) i j

      sem : Functor FreeCat 𝓒
      sem .Functor.F-ob v = ı $g v
      sem .Functor.F-hom e = ⟦ e ⟧
      sem .Functor.F-id = refl
      sem .Functor.F-seq e e' = refl

      sem-extends-ı : (η ⋆Interp sem) ≡ ı
      sem-extends-ı = refl

      sem-uniq : ∀ {F : Functor FreeCat 𝓒} → ((Uhom F ∘GrHom η) ≡ ı) → F ≡ sem
      sem-uniq {F} agree-on-generators = Functor≡ agree-on-objects agree-on-morphisms where
        agree-on-objects : ∀ v → F ⟅ v ⟆ ≡ ı $g v
        agree-on-objects v i = agree-on-generators i $g v

        aom-type : ∀ {v w} → (f : FreeCat [ v , w ]) → Type _
        aom-type {v}{w} f = PathP (λ i → 𝓒 [ agree-on-objects v i , agree-on-objects w i ]) (F ⟪ f ⟫) ⟦ f ⟧

        aom-id : ∀ {v} → aom-type {v} idₑ
        aom-id {v} = toPathP⁻ (F .F-id ∙ fromPathP⁻ (λ i → 𝓒 .id {agree-on-objects v i}))

        aom-seq : ∀ {v w x} → (f : FreeCat [ v , w ]) (g : FreeCat [ w , x ])
                            → aom-type f
                            → aom-type g
                            → aom-type (f ⋆ₑ g)
        aom-seq f g pf pg = toPathP⁻ (F .F-seq f g ∙ fromPathP⁻ (λ i → pf i ⋆⟨ 𝓒 ⟩ pg i))

        agree-on-morphisms : ∀ {v w} → (f : FreeCat [ v , w ]) → aom-type f
        agree-on-morphisms (↑ x) = λ i → agree-on-generators i <$g> x
        agree-on-morphisms idₑ = aom-id
        agree-on-morphisms (f ⋆ₑ g) = aom-seq f g (agree-on-morphisms f) (agree-on-morphisms g)
        agree-on-morphisms (⋆ₑIdL f i) j = isSet→SquareP (λ i j → 𝓒 .isSetHom) (aom-seq idₑ f aom-id (agree-on-morphisms f)) (agree-on-morphisms f) (λ i → F ⟪ ⋆ₑIdL f i ⟫) (λ i → 𝓒 .⋆IdL ⟦ f ⟧ i) i j
        agree-on-morphisms (⋆ₑIdR f i) j = isSet→SquareP (λ i j → 𝓒 .isSetHom) (aom-seq f idₑ (agree-on-morphisms f) aom-id) (agree-on-morphisms f) (λ i → F ⟪ ⋆ₑIdR f i ⟫) (𝓒 .⋆IdR ⟦ f ⟧) i j
        agree-on-morphisms (⋆ₑAssoc f f₁ f₂ i) j = isSet→SquareP (λ i j → 𝓒 .isSetHom) (aom-seq (f ⋆ₑ f₁) f₂ (aom-seq f f₁ (agree-on-morphisms f) (agree-on-morphisms f₁)) (agree-on-morphisms f₂)) (aom-seq f (f₁ ⋆ₑ f₂) (agree-on-morphisms f) (aom-seq f₁ f₂ (agree-on-morphisms f₁) (agree-on-morphisms f₂))) (λ i → F ⟪ ⋆ₑAssoc f f₁ f₂ i ⟫) (𝓒 .⋆Assoc ⟦ f ⟧ ⟦ f₁ ⟧ ⟦ f₂ ⟧) i j
        agree-on-morphisms (isSetExp f g p q i j) k =
          isSet→SquareP {A = λ i j → PathP (λ k → 𝓒 [ agree-on-objects _ k , agree-on-objects _ k ]) (F ⟪ (isSetExp f g p q i j) ⟫) (⟦ (isSetExp f g p q i j) ⟧)}
            (λ i j → isOfHLevelPathP
                       {A = λ k → 𝓒 [ agree-on-objects _ k , agree-on-objects _ k ]}
                       2 (𝓒 .isSetHom) (F ⟪ isSetExp f g p q i j ⟫) ⟦ isSetExp f g p q i j ⟧)
            (λ j k → agree-on-morphisms (p j) k)
            (λ j k → agree-on-morphisms (q j) k)
            (λ i k → agree-on-morphisms f k)
            (λ i k → agree-on-morphisms g k)
            i j k

      sem-contr : ∃![ F ∈ Functor FreeCat 𝓒 ] Uhom F ∘GrHom η ≡ ı
      sem-contr .fst = sem , sem-extends-ı
      sem-contr .snd (sem' , sem'-extends-ı) = ΣPathP paths
        where
          paths : Σ[ p ∈ sem ≡ sem' ] PathP (λ i → Uhom (p i) ∘GrHom η ≡ ı) sem-extends-ı sem'-extends-ı
          paths .fst = sym (sem-uniq sem'-extends-ı)
          paths .snd i j = sem'-extends-ı ((~ i) ∨ j)

    free-cat-functor-η-expansion : {𝓒 : Category ℓc ℓc'} (F : Functor FreeCat 𝓒)
      → F ≡ Semantics.sem 𝓒 (F ∘Interp η)
    free-cat-functor-η-expansion F = Semantics.sem-uniq _ (F ∘Interp η) refl

    free-cat-functor-ind : {𝓒 : Category ℓc ℓc'} (F F' : Functor FreeCat 𝓒)
      → (F ∘Interp η) ≡ (F' ∘Interp η)
      → F ≡ F'
    free-cat-functor-ind {𝓒 = 𝓒} F F' p =
      free-cat-functor-η-expansion F
      ∙ (cong (Semantics.sem 𝓒) p)
      ∙ sym (free-cat-functor-η-expansion F')

-- co-unit of the 2-adjunction
module _ {𝓒 : Category ℓc ℓc'} where
  open FreeCategory (Ugr 𝓒)
  ε : Functor FreeCat 𝓒
  ε = Semantics.sem 𝓒 (Uhom {𝓓 = 𝓒} Id)

  ε-reasoning : {𝓓 : Category ℓd ℓd'}
            → (𝓕 : Functor 𝓒 𝓓)
            → 𝓕 ∘F ε ≡ Semantics.sem 𝓓 (Uhom 𝓕)
  ε-reasoning {𝓓 = 𝓓} 𝓕 = Semantics.sem-uniq 𝓓 (Uhom 𝓕) refl
