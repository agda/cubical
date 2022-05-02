-- Internal monoid in a strict monoidal category
{-# OPTIONS --safe #-}

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Categories.Functor.Base
open import Cubical.Reflection.RecordEquiv hiding (unit)

module Cubical.Categories.Monoidal.Strict.Monoid {ℓ ℓ' : Level} (C : StrictMonCategory ℓ ℓ') where

module _ where
    open StrictMonCategory C

    record Monoid : Type (ℓ-max ℓ ℓ') where
      constructor monoid
      field
        carrier : ob
        η : Hom[ unit , carrier ]
        μ : Hom[ carrier ⊗ carrier , carrier ]
        assoc-μ : PathP (λ i → Hom[ assoc carrier carrier carrier i , carrier ]) (μ ∘ (id ⊗ₕ μ)) (μ ∘ (μ ⊗ₕ id))
        idl-μ : PathP (λ i → Hom[ idl carrier i , carrier ]) (μ ∘ (η ⊗ₕ id)) id
        idr-μ : PathP (λ i → Hom[ idr carrier i , carrier ]) (μ ∘ (id ⊗ₕ η)) id

    open Monoid

    record Monoid[_,_] (monA monB : Monoid) : Type ℓ' where
      constructor monoidHom
      field
        carrierHom : Hom[ carrier monA , carrier monB ]
        nat-η : carrierHom ∘ η monA ≡ η monB
        nat-μ : carrierHom ∘ μ monA ≡ μ monB ∘ (carrierHom ⊗ₕ carrierHom)

    open Monoid[_,_]

    monoidHomExt : {monA monB : Monoid} (f g : Monoid[ monA , monB ]) → carrierHom f ≡ carrierHom g → f ≡ g
    carrierHom (monoidHomExt f g p i) = p i
    nat-η (monoidHomExt {monA} {monB} f g p i) = lemma i
      where lemma : PathP (λ i₁ → p i₁ ∘ η monA ≡ η monB) (nat-η f) (nat-η g)
            lemma = toPathP (isSetHom _ _ _ _)
    nat-μ (monoidHomExt {monA} {monB} f g p i) = lemma i
      where lemma : PathP (λ i₁ → p i₁ ∘ μ monA ≡ μ monB ∘ (p i₁ ⊗ₕ p i₁)) (nat-μ f) (nat-μ g)
            lemma = toPathP (isSetHom _ _ _ _)

module C = StrictMonCategory C
open Category
open Monoid
open Monoid[_,_]
open Functor

monoidCategory : Category (ℓ-max ℓ ℓ') ℓ'
ob monoidCategory = Monoid
Hom[_,_] monoidCategory = Monoid[_,_]
carrierHom (id monoidCategory) = C.id
nat-η (id monoidCategory {monA}) = C.⋆IdR (η monA)
nat-μ (id monoidCategory {monA}) =
  C.id C.∘ μ monA
    ≡⟨ C.⋆IdR (μ monA) ⟩
  μ monA
    ≡⟨ sym (C.⋆IdL (μ monA)) ⟩
  μ monA C.∘ id C.C
    ≡⟨ cong (μ monA C.∘_) (sym (F-id C.─⊗─)) ⟩
  μ monA C.∘ (C.id C.⊗ₕ C.id) ∎
carrierHom (_⋆_ monoidCategory f g) = carrierHom g C.∘ carrierHom f
nat-η (_⋆_ monoidCategory {monA} {monB} {monC} f g) =
  (carrierHom g C.∘ carrierHom f) C.∘ η monA
    ≡⟨ sym (C.⋆Assoc (η monA) (carrierHom f) (carrierHom g)) ⟩
  carrierHom g C.∘ (carrierHom f C.∘ η monA)
    ≡⟨ cong (carrierHom g C.∘_) (nat-η f) ⟩
  carrierHom g C.∘ η monB
    ≡⟨ nat-η g ⟩
  η monC ∎
nat-μ (_⋆_ monoidCategory {monA} {monB} {monC} f g) =
  (carrierHom g C.∘ carrierHom f) C.∘ μ monA
    ≡⟨ sym (C.⋆Assoc (μ monA) (carrierHom f) (carrierHom g)) ⟩
  carrierHom g C.∘ (carrierHom f C.∘ μ monA)
    ≡⟨ cong (carrierHom g C.∘_) (nat-μ f) ⟩
  carrierHom g C.∘ (μ monB C.∘ (carrierHom f C.⊗ₕ carrierHom f))
    ≡⟨ C.⋆Assoc (carrierHom f C.⊗ₕ carrierHom f) (μ monB) (carrierHom g) ⟩
  (carrierHom g C.∘ μ monB) C.∘ (carrierHom f C.⊗ₕ carrierHom f)
    ≡⟨ cong (C._∘ (carrierHom f C.⊗ₕ carrierHom f)) (nat-μ g) ⟩
  (μ monC C.∘ (carrierHom g C.⊗ₕ carrierHom g)) C.∘ (carrierHom f C.⊗ₕ carrierHom f)
    ≡⟨ sym (C.⋆Assoc (carrierHom f C.⊗ₕ carrierHom f) (carrierHom g C.⊗ₕ carrierHom g) (μ monC)) ⟩
  μ monC C.∘ ((carrierHom g C.⊗ₕ carrierHom g) C.∘ (carrierHom f C.⊗ₕ carrierHom f))
    ≡⟨ cong (μ monC C.∘_) (sym (F-seq C.─⊗─ (carrierHom f , carrierHom f) (carrierHom g , carrierHom g))) ⟩
  μ monC C.∘ ((carrierHom g C.∘ carrierHom f) C.⊗ₕ (carrierHom g C.∘ carrierHom f)) ∎
⋆IdL monoidCategory {monA} f = monoidHomExt _ _ (C.⋆IdL (carrierHom f))
⋆IdR monoidCategory {monA} f = monoidHomExt _ _ (C.⋆IdR (carrierHom f))
⋆Assoc monoidCategory {monA} {monB} {monC} {monD} f g h =
  monoidHomExt _ _ (C.⋆Assoc (carrierHom f) (carrierHom g) (carrierHom h))
isSetHom monoidCategory {monA} {monB} =
  isOfHLevelRetractFromIso 2 isoToΣ
    (isSetΣ C.isSetHom λ _ → isProp→isSet (isProp× (C.isSetHom _ _) (C.isSetHom _ _)))
  where
  unquoteDecl isoToΣ = declareRecordIsoΣ isoToΣ (quote Monoid[_,_])
