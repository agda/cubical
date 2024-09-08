{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Subset where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Functions.Embedding
open import Cubical.Functions.Preimage

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ₀ ℓ₁ : Level

module _
  (P : Poset ℓ ℓ')
  where
    private
      _≤_ = PosetStr._≤_ (snd P)

      is = PosetStr.isPoset (snd P)
      prop = IsPoset.is-prop-valued is

      rfl = IsPoset.is-refl is
      anti = IsPoset.is-antisym is
      trans = IsPoset.is-trans is

    module _
      (S : Embedding ⟨ P ⟩ ℓ'')
      where
        private
          f = S .snd .fst
        isDownset : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
        isDownset = ∀ x → ∀ y → y ≤ f x → y ∈ₑ S

        isPropIsDownset : isProp isDownset
        isPropIsDownset = isPropΠ3 λ _ y _ → isProp∈ₑ y S

        isUpset : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
        isUpset = ∀ x → ∀ y → f x ≤ y → y ∈ₑ S

        isPropIsUpset : isProp isUpset
        isPropIsUpset = isPropΠ3 λ _ y _ → isProp∈ₑ y S

    module _
      (A : Embedding ⟨ P ⟩ ℓ₀)
      (B : Embedding ⟨ P ⟩ ℓ₁)
      where
        module _
          (downA : isDownset A)
          (downB : isDownset B)
          where
            isDownset∩ : isDownset (A ∩ₑ B)
            isDownset∩ (x , (a , a≡x) , (b , b≡x)) y y≤x
              = (y , (downA a y (subst (y ≤_) (sym a≡x) y≤x) ,
                      downB b y (subst (y ≤_) (sym b≡x) y≤x))) , refl

            isDownset∪ : isDownset (A ∪ₑ B)
            isDownset∪ (x , A⊎B) y y≤x
              = ∥₁.rec (isProp∈ₑ y (A ∪ₑ B))
                       (⊎.rec (λ { (a , a≡x) →
                              (y , ∣ inl (downA a y (subst (y ≤_)
                                                           (sym a≡x) y≤x)) ∣₁) , refl })
                              (λ { (b , b≡x) →
                              (y , ∣ inr (downB b y (subst (y ≤_)
                                                           (sym b≡x) y≤x)) ∣₁) , refl })) A⊎B

        module _
          (upA : isUpset A)
          (upB : isUpset B)
          where
            isUpset∩ : isUpset (A ∩ₑ B)
            isUpset∩ (x , (a , a≡x) , (b , b≡x)) y x≤y
              = (y , (upA a y (subst (_≤ y) (sym a≡x) x≤y) ,
                      upB b y (subst (_≤ y) (sym b≡x) x≤y))) , refl

            isUpset∪ : isUpset (A ∪ₑ B)
            isUpset∪ (x , A⊎B) y x≤y
              = ∥₁.rec (isProp∈ₑ y (A ∪ₑ B))
                       (⊎.rec (λ { (a , a≡x) →
                              (y , ∣ inl (upA a y (subst (_≤ y)
                                                         (sym a≡x) x≤y)) ∣₁) , refl })
                              (λ { (b , b≡x) →
                              (y , ∣ inr (upB b y (subst (_≤ y)
                                                         (sym b≡x) x≤y)) ∣₁) , refl })) A⊎B

    module _
      {I : Type ℓ''}
      (S : I → Embedding ⟨ P ⟩ ℓ''')
      where
        module _
          (downS : ∀ i → isDownset (S i))
          where
            isDownset⋂ : isDownset (⋂ₑ S)
            isDownset⋂ (x , ∀x) y y≤x
              = (y , λ i → downS i (∀x i .fst) y (subst (y ≤_) (sym (∀x i .snd)) y≤x)) , refl

            isDownset⋃ : isDownset (⋃ₑ S)
            isDownset⋃ (x , ∃i) y y≤x
              = (y , (∥₁.map (λ { (i , a , a≡x) → i , downS i a y (subst (y ≤_) (sym a≡x) y≤x) }) ∃i)) , refl

        module _
          (upS : ∀ i → isUpset (S i))
          where
            isUpset⋂ : isUpset (⋂ₑ S)
            isUpset⋂ (x , ∀x) y x≤y
              = (y , λ i → upS i (∀x i .fst) y (subst (_≤ y) (sym (∀x i .snd)) x≤y)) , refl

            isUpset⋃ : isUpset (⋃ₑ S)
            isUpset⋃ (x , ∃i) y x≤y
              = (y , (∥₁.map (λ { (i , a , a≡x) → i , upS i a y (subst (_≤ y) (sym a≡x) x≤y)  }) ∃i)) , refl


    module _
      (x : ⟨ P ⟩)
      where
        principalDownset : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ')
        principalDownset = (Σ[ y ∈ ⟨ P ⟩ ] y ≤ x) , EmbeddingΣProp λ _ → prop _ x

        principalUpset : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ')
        principalUpset = (Σ[ y ∈ ⟨ P ⟩ ] x ≤ y) , EmbeddingΣProp λ _ → prop x _

    isDownsetPrincipalDownset : ∀ x → isDownset (principalDownset x)
    isDownsetPrincipalDownset x (y , y≤x) z z≤y = (z , (trans z y x z≤y y≤x)) , refl

    isUpsetPrincipalUpset : ∀ x → isUpset (principalUpset x)
    isUpsetPrincipalUpset x (y , x≤y) z y≤z = (z , (trans x y z x≤y y≤z)) , refl

    principalDownsetMembership : ∀ x y
                               → x ≤ y
                               ≃ x ∈ₑ principalDownset y
    principalDownsetMembership x y
      = propBiimpl→Equiv (prop x y)
                         (isProp∈ₑ x (principalDownset y))
                         (λ x≤y → (x , x≤y) , refl)
                          λ { ((a , a≤y) , fib) → subst (_≤ y) fib a≤y}

    principalUpsetMembership : ∀ x y
                             → x ≤ y
                             ≃ y ∈ₑ principalUpset x
    principalUpsetMembership x y
      = propBiimpl→Equiv (prop x y)
                         (isProp∈ₑ y (principalUpset x))
                         (λ x≤y → (y , x≤y) , refl)
                          λ { ((a , x≤a) , fib) → subst (x ≤_) fib x≤a }

    principalUpsetInclusion : ∀ x y
                            → x ≤ y
                            → principalUpset y ⊆ₑ principalUpset x
    principalUpsetInclusion x y x≤y z z∈y↑
      = equivFun (principalUpsetMembership x z)
                 (trans x y z x≤y (invEq (principalUpsetMembership y z) z∈y↑))

    principalDownsetInclusion : ∀ x y
                              → x ≤ y
                              → principalDownset x ⊆ₑ principalDownset y
    principalDownsetInclusion x y x≤y z z∈x↓
      = equivFun (principalDownsetMembership z y)
                 (trans z x y (invEq (principalDownsetMembership z x) z∈x↓) x≤y)

    module _
      (S : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ'))
      where
        isPrincipalDownset : Type _
        isPrincipalDownset = Σ[ x ∈ ⟨ P ⟩ ] S ≡ (principalDownset x)

        isPropIsPrincipalDownset : isProp isPrincipalDownset
        isPropIsPrincipalDownset (x , S≡x↓) (y , S≡y↓)
          = Σ≡Prop (λ x → isSetEmbedding S (principalDownset x))
                    (anti x y x≤y y≤x)
          where x≤y : x ≤ y
                x≤y = invEq (principalDownsetMembership x y)
                            (subst (x ∈ₑ_)
                                   (sym S≡x↓ ∙ S≡y↓)
                                   (equivFun (principalDownsetMembership x x) (rfl x)))

                y≤x : y ≤ x
                y≤x = invEq (principalDownsetMembership y x)
                            (subst (y ∈ₑ_)
                                   (sym S≡y↓ ∙ S≡x↓)
                                   (equivFun (principalDownsetMembership y y) (rfl y)))

        isPrincipalUpset : Type _
        isPrincipalUpset = Σ[ x ∈ ⟨ P ⟩ ] S ≡ (principalUpset x)

        isPropIsPrincipalUpset : isProp isPrincipalUpset
        isPropIsPrincipalUpset (x , S≡x↑) (y , S≡y↑)
          = Σ≡Prop (λ x → isSetEmbedding S (principalUpset x))
                    (anti x y x≤y y≤x)
          where x≤y : x ≤ y
                x≤y = invEq (principalUpsetMembership x y)
                             (subst (y ∈ₑ_)
                                    (sym S≡y↑ ∙ S≡x↑)
                                    (equivFun (principalUpsetMembership y y) (rfl y)))

                y≤x : y ≤ x
                y≤x = invEq (principalUpsetMembership y x)
                            (subst (x ∈ₑ_)
                                   (sym S≡x↑ ∙ S≡y↑)
                                   (equivFun (principalUpsetMembership x x) (rfl x)))

        isPrincipalDownset→isDownset : isPrincipalDownset → (isDownset S)
        isPrincipalDownset→isDownset (x , p) = transport⁻ (cong isDownset p) (isDownsetPrincipalDownset x)

        isPrincipalUpset→isUpset : isPrincipalUpset → (isUpset S)
        isPrincipalUpset→isUpset (x , p) = transport⁻ (cong isUpset p) (isUpsetPrincipalUpset x)

module PosetDownset (P' : Poset ℓ ℓ') where
  private P = ⟨ P' ⟩
  open PosetStr (snd P')

  ↓ : P → Type (ℓ-max ℓ ℓ')
  ↓ u = principalDownset P' u .fst

  ↓ᴾ : P → Poset (ℓ-max ℓ ℓ') ℓ'
  fst (↓ᴾ u) = ↓ u
  PosetStr._≤_ (snd (↓ᴾ u)) v w = v .fst ≤ w .fst
  PosetStr.isPoset (snd (↓ᴾ u)) =
    isPosetInduced
      (PosetStr.isPoset (snd P'))
       _
      (principalDownset P' u .snd)

module PosetUpset (P' : Poset ℓ ℓ') where
  private P = ⟨ P' ⟩
  open PosetStr (snd P')

  ↑ : P → Type (ℓ-max ℓ ℓ')
  ↑ u = principalUpset P' u .fst

  ↑ᴾ : P → Poset (ℓ-max ℓ ℓ') ℓ'
  fst (↑ᴾ u) = principalUpset P' u .fst
  PosetStr._≤_ (snd (↑ᴾ u)) v w = v .fst ≤ w .fst
  PosetStr.isPoset (snd (↑ᴾ u)) =
    isPosetInduced
      (PosetStr.isPoset (snd P'))
       _
      (principalUpset P' u .snd)
