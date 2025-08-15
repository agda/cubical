{-# OPTIONS --safe #-}

module Cubical.Categories.Dagger.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

private variable
  ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C
  private variable
    x y z w : ob

  record IsDagger (_† : {x y : ob} → Hom[ x , y ] → Hom[ y , x ]) : Type (ℓ-max ℓ ℓ') where
    field
      †-invol : (f : Hom[ x , y ]) → f † † ≡ f
      †-id : id † ≡ id {x}
      †-seq : (f : Hom[ x , y ]) (g : Hom[ y , z ]) → (f ⋆ g) † ≡ g † ⋆ f †

  open IsDagger

  makeIsDagger : {_† : {x y : ob} → Hom[ x , y ] → Hom[ y , x ]}
               → (∀ {x y} (f : Hom[ x , y ]) → f † † ≡ f)
               → (∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → (f ⋆ g) † ≡ g † ⋆ f †)
               → IsDagger _†
  makeIsDagger {_†} †-invol †-seq .†-invol = †-invol
  makeIsDagger {_†} †-invol †-seq .†-seq   = †-seq
  makeIsDagger {_†} †-invol †-seq .†-id    = -- this actually follows from the other axioms
    id †          ≡⟨ sym (⋆IdR _) ⟩
    id † ⋆ id     ≡⟨ congR _⋆_ (sym (†-invol id)) ⟩
    id † ⋆ id † † ≡⟨ sym (†-seq (id †) id) ⟩
    (id † ⋆ id) † ≡⟨ cong _† (⋆IdR _) ⟩
    id † †        ≡⟨ †-invol id ⟩
    id            ∎

  record DaggerStr : Type (ℓ-max ℓ ℓ') where
    field
      _† : Hom[ x , y ] → Hom[ y , x ]
      is-dag : IsDagger _†

    open IsDagger is-dag public


record †Category (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality

  field
    cat : Category ℓ ℓ'
    dagstr : DaggerStr cat

  open DaggerStr dagstr public
  open Category cat public

open IsDagger
open DaggerStr
open †Category

dag : ∀ (C : †Category ℓ ℓ') {x y} → C .cat [ x , y ] → C .cat [ y , x ]
dag C f = C ._† f

syntax dag C f = f †[ C ]
