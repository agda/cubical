{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Mappings where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.Semigroup

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Functions.Embedding
open import Cubical.Functions.Image
open import Cubical.Functions.Logic using (_⊔′_)
open import Cubical.Functions.Preimage

open import Cubical.Reflection.RecordEquiv

open import Cubical.HITs.PropositionalTruncation as ∥₁
open import Cubical.HITs.SetQuotients

open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties
open import Cubical.Relation.Binary.Order.Poset.Instances.Embedding
open import Cubical.Relation.Binary.Order.Proset
open import Cubical.Relation.Binary.Base


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ₀ ℓ₀' ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

record IsIsotone {A : Type ℓ₀} {B : Type ℓ₁}
  (M : PosetStr ℓ₀' A) (f : A → B) (N : PosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  -- Shorter qualified names
  private
    module M = PosetStr M
    module N = PosetStr N

  field
    pres≤ : (x y : A) → x M.≤ y → f x N.≤ f y

unquoteDecl IsIsotoneIsoΣ = declareRecordIsoΣ IsIsotoneIsoΣ (quote IsIsotone)

isPropIsIsotone : {A : Type ℓ₀} {B : Type ℓ₁}
                  (M : PosetStr ℓ₀' A) (f : A → B) (N : PosetStr ℓ₁' B)
                → isProp (IsIsotone M f N)
isPropIsIsotone M f N = isOfHLevelRetractFromIso 1 IsIsotoneIsoΣ
  (isPropΠ3 λ x y _ → IsPoset.is-prop-valued (PosetStr.isPoset N) (f x) (f y))

IsIsotone-∘ : {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
            → (M : PosetStr ℓ₀' A) (f : A → B)
              (N : PosetStr ℓ₁' B) (g : B → C) (O : PosetStr ℓ₂' C)
            → IsIsotone M f N
            → IsIsotone N g O
            → IsIsotone M (g ∘ f) O
IsIsotone.pres≤ (IsIsotone-∘ M f N g O isf isg) x y x≤y
  = IsIsotone.pres≤ isg (f x) (f y) (IsIsotone.pres≤ isf x y x≤y)

record IsAntitone {A : Type ℓ₀} {B : Type ℓ₁}
  (M : PosetStr ℓ₀' A) (f : A → B) (N : PosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
    isantitone
  -- Shorter qualified names
  private
    module M = PosetStr M
    module N = PosetStr N

  field
    inv≤ : (x y : A) → x M.≤ y → f y N.≤ f x

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

-- Isotone maps are characterized by their actions on down-sets and up-sets
module _
  {P : Poset ℓ₀ ℓ₀'}
  {S : Poset ℓ₁ ℓ₁'}
  (f : ⟨ P ⟩ → ⟨ S ⟩)
  where
    private
      isP = PosetStr.isPoset (snd P)
      isS = PosetStr.isPoset (snd S)

      _≤P_ = PosetStr._≤_ (snd P)
      _≤S_ = PosetStr._≤_ (snd S)

      propS = IsPoset.is-prop-valued isS
      rflS = IsPoset.is-refl isS
      transS = IsPoset.is-trans isS

    IsIsotone→PreimagePrincipalDownsetIsDownset : IsIsotone (snd P) f (snd S)
                                                → ∀ y → isDownset P (f ⃖ (principalDownset S y))
    IsIsotone→PreimagePrincipalDownsetIsDownset is y (x , inPrex) z z≤x
      = ∥₁.rec (isEmbedding→hasPropFibers (preimageInclusion f (principalDownset S y) .snd) z)
               (λ { ((b , b≤y) , fibb) →
                    (z , ∣ (f z , transS (f z) (f x) y
                                         (IsIsotone.pres≤ is z x z≤x)
                                         (subst (_≤S y) fibb b≤y)) ,
                                          refl ∣₁) ,
                     refl }) inPrex

    IsIsotone→PreimagePrincipalUpsetIsUpset : IsIsotone (snd P) f (snd S)
                                            → ∀ y → isUpset P (f ⃖ (principalUpset S y))
    IsIsotone→PreimagePrincipalUpsetIsUpset is y (x , inPrex) z x≤z
      = ∥₁.rec (isEmbedding→hasPropFibers (preimageInclusion f (principalUpset S y) .snd) z)
               (λ { ((b , y≤b) , fibb) →
                    (z , ∣ (f z , transS y (f x) (f z)
                                        (subst (y ≤S_) fibb y≤b)
                                        (IsIsotone.pres≤ is x z x≤z)) ,
                                         refl ∣₁) ,
                     refl }) inPrex

    PreimagePrincipalDownsetIsDownset→IsIsotone : (∀ x → isDownset P (f ⃖ (principalDownset S x)))
                                                → IsIsotone (snd P) f (snd S)
    IsIsotone.pres≤ (PreimagePrincipalDownsetIsDownset→IsIsotone down) y x y≤x
      = ∥₁.rec (propS _ _) (λ { ((b , b≤fx) , fibb) → subst (_≤S f x) (fibb ∙ cong f fiba) b≤fx }) pre
        where fib = down (f x) (x , ∣ ((f x) , (rflS (f x))) , refl ∣₁) y y≤x

              pre = fib .fst .snd
              fiba = fib .snd

    PreimagePrincipalUpsetIsUpset→IsIsotone : (∀ x → isUpset P (f ⃖ (principalUpset S x)))
                                            → IsIsotone (snd P) f (snd S)
    IsIsotone.pres≤ (PreimagePrincipalUpsetIsUpset→IsIsotone up) x y x≤y
      = ∥₁.rec (propS _ _) (λ { ((b , fx≤b) , fibb) → subst (f x ≤S_) (fibb ∙ cong f fiba) fx≤b }) pre
        where fib = up (f x) (x , ∣ ((f x) , (rflS (f x))) , refl ∣₁) y x≤y

              pre = fib .fst .snd
              fiba = fib .snd

-- The next part requires our posets to operate over the same universes
module _
  (P S : Poset ℓ ℓ')
  (f : ⟨ P ⟩ → ⟨ S ⟩)
  where
    private
      isP = PosetStr.isPoset (snd P)
      isS = PosetStr.isPoset (snd S)

      _≤P_ = PosetStr._≤_ (snd P)
      _≤S_ = PosetStr._≤_ (snd S)

      propP = IsPoset.is-prop-valued isP
      rflP = IsPoset.is-refl isP
      antiP = IsPoset.is-antisym isP
      transP = IsPoset.is-trans isP

      propS = IsPoset.is-prop-valued isS
      rflS = IsPoset.is-refl isS
      antiS = IsPoset.is-antisym isS
      transS = IsPoset.is-trans isS

    -- We can now define the type of residuated maps
    isResiduated : Type _
    isResiduated = ∀ y → isPrincipalDownset P (f ⃖ (principalDownset S y))

    hasResidual : Type (ℓ-max ℓ ℓ')
    hasResidual = (IsIsotone (snd P) f (snd S)) ×
                   (Σ[ g ∈ (⟨ S ⟩ → ⟨ P ⟩) ] (IsIsotone (snd S) g (snd P) ×
                                             (∀ x → x ≤P (g ∘ f) x) ×
                                             (∀ x → (f ∘ g) x ≤S x)))

    isResiduated→hasResidual : isResiduated
                             → hasResidual
    isResiduated→hasResidual down = isotonef , g , isotoneg , g∘f , f∘g
      where isotonef : IsIsotone (snd P) f (snd S)
            isotonef = PreimagePrincipalDownsetIsDownset→IsIsotone f
                       λ x → isPrincipalDownset→isDownset P (f ⃖ principalDownset S x) (down x)

            isotonef⃖ : ∀ x y → x ≤S y → (f ⃖ (principalDownset S x)) ⊆ₑ (f ⃖ (principalDownset S y))
            isotonef⃖ x y x≤y z ((a , pre) , fiba)
              = ∥₁.rec (isProp∈ₑ z (f ⃖ principalDownset S y))
                       (λ { ((b , b≤x) , fibb) → (a , ∣ (b , (transS b x y b≤x x≤y)) , fibb ∣₁) , fiba }) pre

            g : ⟨ S ⟩ → ⟨ P ⟩
            g x = down x .fst

            isotoneg : IsIsotone (snd S) g (snd P)
            IsIsotone.pres≤ isotoneg x y x≤y
              = invEq
                  (principalDownsetMembership P (g x) (g y))
                  (subst
                    (g x ∈ₑ_)
                    (down y .snd)
                    (isotonef⃖ x y x≤y (g x)
                      (subst (g x ∈ₑ_)
                        (sym (down x .snd))
                        (equivFun (principalDownsetMembership P (g x) (g x)) (rflP (g x))))))

            g∘f : ∀ x → x ≤P (g ∘ f) x
            g∘f x = invEq (principalDownsetMembership P x (g (f x)))
                          (subst (x ∈ₑ_) (down (f x) .snd)
                                 ((x , ∣ ((f x) , (rflS (f x))) , refl ∣₁) , refl))

            f∘g : ∀ y → (f ∘ g) y ≤S y
            f∘g y = ∥₁.rec (propS _ _)
                           (λ { ((a , a≤y) , fib) →
                                subst (_≤S y) (fib ∙ cong f (gy∈pre .snd)) a≤y })
                           (gy∈pre .fst .snd)
              where gy∈pre : g y ∈ₑ (f ⃖ (principalDownset S y))
                    gy∈pre = subst (g y ∈ₑ_) (sym (down y .snd))
                                   (equivFun (principalDownsetMembership P (g y) (g y)) (rflP (g y)))

    hasResidual→isResiduated : hasResidual
                             → isResiduated
    hasResidual→isResiduated (isf , g , isg , g∘f , f∘g) y
      = (g y) , (equivFun (EmbeddingIP _ _)
                ((λ x ((a , pre) , fiba) →
                  ∥₁.rec (isProp∈ₑ x (principalDownset P (g y)))
                                     (λ { ((b , b≤y) , fibb) →
                                          equivFun (principalDownsetMembership P x (g y))
                                                   (transP x (g (f x)) (g y) (g∘f x)
                                                     (IsIsotone.pres≤ isg (f x) y
                                                       (subst (_≤S y)
                                                         (fibb ∙ cong f fiba) b≤y))) }) pre) ,
                  λ x x∈g → (x , ∣ ((f x) ,
                                   (transS (f x) (f (g y)) y
                                     (IsIsotone.pres≤ isf x (g y)
                                       (invEq (principalDownsetMembership P x (g y)) x∈g))
                                     (f∘g y))) , refl ∣₁) , refl))

    isPropIsResiduated : isProp isResiduated
    isPropIsResiduated = isPropΠ λ _ → isPropIsPrincipalDownset P _

    residualUnique : (p q : hasResidual)
                   → p .snd .fst ≡ q .snd .fst
    residualUnique (isf₀ , g  , isg  , g∘f  , f∘g)
                   (isf₁ , g* , isg* , g*∘f , f∘g*)
                   = funExt λ x → antiP (g x) (g* x) (g≤g* x) (g*≤g x)
                   where g≤g* : ∀ x → g x ≤P g* x
                         g≤g* x = transP (g x) ((g* ∘ f) (g x)) (g* x) (g*∘f (g x))
                                          (IsIsotone.pres≤ isg* (f (g x)) x (f∘g x))

                         g*≤g : ∀ x → g* x ≤P g x
                         g*≤g x = transP (g* x) ((g ∘ f) (g* x)) (g x) (g∘f (g* x))
                                         (IsIsotone.pres≤ isg (f (g* x)) x (f∘g* x))

    isPropHasResidual : isProp hasResidual
    isPropHasResidual p q = ≡-× (isPropIsIsotone _ f _ _ _)
                                 (Σ≡Prop (λ g → isProp× (isPropIsIsotone _ g _)
                                                (isProp× (isPropΠ (λ x → propP x (g (f x))))
                                                         (isPropΠ λ x → propS (f (g x)) x)))
                                          (residualUnique p q))

    residual : hasResidual → ⟨ S ⟩ → ⟨ P ⟩
    residual (_ , g , _) = g

    AbsorbResidual : (res : hasResidual)
                   → f ∘ (residual res) ∘ f ≡ f
    AbsorbResidual (isf , f⁺ , _ , f⁺∘f , f∘f⁺)
      = funExt λ x → antiS ((f ∘ f⁺ ∘ f) x) (f x)
                           (f∘f⁺ (f x))
                           (IsIsotone.pres≤ isf x (f⁺ (f x)) (f⁺∘f x))

    ResidualAbsorb : (res : hasResidual)
                   → (residual res) ∘ f ∘ (residual res) ≡ (residual res)
    ResidualAbsorb (_ , f⁺ , isf⁺ , f⁺∘f , f∘f⁺)
      = funExt λ x → antiP ((f⁺ ∘ f ∘ f⁺) x) (f⁺ x)
                           (IsIsotone.pres≤ isf⁺ (f (f⁺ x)) x (f∘f⁺ x))
                           (f⁺∘f (f⁺ x))

isResidual : (P S : Poset ℓ ℓ')
           → (f⁺ : ⟨ S ⟩ → ⟨ P ⟩)
           → Type (ℓ-max ℓ ℓ')
isResidual P S f⁺ = Σ[ f ∈ (⟨ P ⟩ → ⟨ S ⟩) ] (Σ[ res ∈ hasResidual P S f ] f⁺ ≡ residual P S f res)

isResidualOfUnique : (P S : Poset ℓ ℓ')
                   → (f⁺ : ⟨ S ⟩ → ⟨ P ⟩)
                   → (p q : isResidual P S f⁺)
                   → p .fst ≡ q .fst
isResidualOfUnique P S h (f , (isf , f⁺ , isf⁺ , f⁺∘f , f∘f⁺) , h≡f⁺)
                         (g , (isg , g⁺ , isg⁺ , g⁺∘g , g∘g⁺) , h≡g⁺)
                   = funExt λ x → anti (f x) (g x)
                                 (trans (f x) (f (f⁺ (g x))) (g x)
                                        (IsIsotone.pres≤ isf x (f⁺ (g x))
                                          (subst (x ≤_) (sym (p (g x))) (g⁺∘g x)))
                                        (f∘f⁺ (g x)))
                                  (trans (g x) (g (g⁺ (f x))) (f x)
                                         (IsIsotone.pres≤ isg x (g⁺ (f x))
                                           (subst (x ≤_) (p (f x)) (f⁺∘f x)))
                                         (g∘g⁺ (f x)))
                   where _≤_ = PosetStr._≤_ (snd P)
                         anti = IsPoset.is-antisym (PosetStr.isPoset (snd S))
                         trans = IsPoset.is-trans (PosetStr.isPoset (snd S))
                         p = funExt⁻ ((sym h≡f⁺) ∙ h≡g⁺)

isPropIsResidual : (P S : Poset ℓ ℓ')
                 → (f⁺ : ⟨ S ⟩ → ⟨ P ⟩)
                 → isProp (isResidual P S f⁺)
isPropIsResidual P S f⁺ p q
  = Σ≡Prop (λ f → isPropΣ (isPropHasResidual P S f)
                            λ _ → isSet→ (IsPoset.is-set (PosetStr.isPoset (snd P))) _ _)
                           (isResidualOfUnique P S f⁺ p q)

hasResidual-∘ : (E F G : Poset ℓ ℓ')
              → (f : ⟨ E ⟩ → ⟨ F ⟩)
              → (g : ⟨ F ⟩ → ⟨ G ⟩)
              → hasResidual E F f
              → hasResidual F G g
              → hasResidual E G (g ∘ f)
hasResidual-∘ E F G f g (isf , f⁺ , isf⁺ , f⁺∘f , f∘f⁺) (isg , g⁺ , isg⁺ , g⁺∘g , g∘g⁺)
  = is , f⁺ ∘ g⁺ , is⁺ , ⁺∘ , ∘⁺
  where _≤E_ = PosetStr._≤_ (snd E)
        _≤G_ = PosetStr._≤_ (snd G)

        transE = IsPoset.is-trans (PosetStr.isPoset (snd E))
        transG = IsPoset.is-trans (PosetStr.isPoset (snd G))

        is : IsIsotone (snd E) (g ∘ f) (snd G)
        is = IsIsotone-∘ (snd E) f (snd F) g (snd G) isf isg

        is⁺ : IsIsotone (snd G) (f⁺ ∘ g⁺) (snd E)
        is⁺ = IsIsotone-∘ (snd G) g⁺ (snd F) f⁺ (snd E) isg⁺ isf⁺

        ⁺∘ : ∀ x → x ≤E ((f⁺ ∘ g⁺) ∘ (g ∘ f)) x
        ⁺∘ x = transE x ((f⁺ ∘ f) x) (((f⁺ ∘ g⁺) ∘ g ∘ f) x)
                      (f⁺∘f x)
                      (IsIsotone.pres≤ isf⁺ (f x) (g⁺ (g (f x))) (g⁺∘g (f x)))

        ∘⁺ : ∀ x → ((g ∘ f) ∘ (f⁺ ∘ g⁺)) x ≤G x
        ∘⁺ x = transG (((g ∘ f) ∘ f⁺ ∘ g⁺) x) ((g ∘ g⁺) x) x
                      (IsIsotone.pres≤ isg (f (f⁺ (g⁺ x))) (g⁺ x) (f∘f⁺ (g⁺ x)))
                      (g∘g⁺ x)

isResidual-∘ : (E F G : Poset ℓ ℓ')
             → (f⁺ : ⟨ F ⟩ → ⟨ E ⟩)
             → (g⁺ : ⟨ G ⟩ → ⟨ F ⟩)
             → isResidual E F f⁺
             → isResidual F G g⁺
             → isResidual E G (f⁺ ∘ g⁺)
isResidual-∘ E F G f⁺ g⁺ (f , resf , f⁺≡f*)
                         (g , resg , g⁺≡g*)
             = (g ∘ f) ,
               (hasResidual-∘ E F G f g resf resg) ,
               (funExt (λ x → cong f⁺ (funExt⁻ g⁺≡g* x) ∙ funExt⁻ f⁺≡f* _))

Res : Poset ℓ ℓ' → Semigroup (ℓ-max ℓ ℓ')
fst (Res E) = Σ[ f ∈ (⟨ E ⟩ → ⟨ E ⟩) ] hasResidual E E f
SemigroupStr._·_ (snd (Res E)) (f , resf) (g , resg)
  = (g ∘ f) , (hasResidual-∘ E E E f g resf resg)
IsSemigroup.is-set (SemigroupStr.isSemigroup (snd (Res E)))
  = isSetΣ (isSet→ (IsPoset.is-set (PosetStr.isPoset (snd E))))
      λ f → isProp→isSet (isPropHasResidual E E f)
IsSemigroup.·Assoc (SemigroupStr.isSemigroup (snd (Res E))) (f , _) (g , _) (h , _)
  = Σ≡Prop (λ f → isPropHasResidual E E f) refl

Res⁺ : Poset ℓ ℓ' → Semigroup (ℓ-max ℓ ℓ')
fst (Res⁺ E) = Σ[ f⁺ ∈ (⟨ E ⟩ → ⟨ E ⟩) ] isResidual E E f⁺
SemigroupStr._·_ (snd (Res⁺ E)) (f⁺ , isresf⁺) (g⁺ , isresg⁺)
  = (f⁺ ∘ g⁺) , isResidual-∘ E E E f⁺ g⁺ isresf⁺ isresg⁺
IsSemigroup.is-set (SemigroupStr.isSemigroup (snd (Res⁺ E)))
  = isSetΣ (isSet→ (IsPoset.is-set (PosetStr.isPoset (snd E))))
      λ f⁺ → isProp→isSet (isPropIsResidual E E f⁺)
IsSemigroup.·Assoc (SemigroupStr.isSemigroup (snd (Res⁺ E))) (f⁺ , _) (g⁺ , _) (h⁺ , _)
  = Σ≡Prop (λ f⁺ → isPropIsResidual E E f⁺) refl

isClosure : (E : Poset ℓ ℓ')
            (f : ⟨ E ⟩ → ⟨ E ⟩)
          → Type (ℓ-max ℓ ℓ')
isClosure E f = IsIsotone (snd E) f (snd E) × (f ≡ f ∘ f) × (∀ x → x ≤ f x)
  where _≤_ = PosetStr._≤_ (snd E)

isDualClosure : (E : Poset ℓ ℓ')
                (f : ⟨ E ⟩ → ⟨ E ⟩)
              → Type (ℓ-max ℓ ℓ')
isDualClosure E f = IsIsotone (snd E) f (snd E) × (f ≡ f ∘ f) × (∀ x → f x ≤ x)
  where _≤_ = PosetStr._≤_ (snd E)

-- This can be made more succinct
isClosure' : (E : Poset ℓ ℓ')
             (f : ⟨ E ⟩ → ⟨ E ⟩)
           → Type (ℓ-max ℓ ℓ')
isClosure' E f = ∀ x y → x ≤ f y ≃ f x ≤ f y
  where _≤_ = PosetStr._≤_ (snd E)

isDualClosure' : (E : Poset ℓ ℓ')
                 (f : ⟨ E ⟩ → ⟨ E ⟩)
               → Type (ℓ-max ℓ ℓ')
isDualClosure' E f = ∀ x y → f x ≤ y ≃ f x ≤ f y
  where _≤_ = PosetStr._≤_ (snd E)

isClosure→isClosure' : (E : Poset ℓ ℓ')
                     → ∀ f
                     → isClosure E f
                     → isClosure' E f
isClosure→isClosure' E f (isf , f≡f∘f , x≤fx) x y
  = propBiimpl→Equiv (prop _ _) (prop _ _)
                     (λ x≤fy → subst (f x ≤_) (sym (funExt⁻ f≡f∘f y))
                                     (IsIsotone.pres≤ isf x (f y) x≤fy))
                     (trans x (f x) (f y) (x≤fx x))
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)

        prop = IsPoset.is-prop-valued is
        trans = IsPoset.is-trans is

isDualClosure→isDualClosure' : (E : Poset ℓ ℓ')
                             → ∀ f
                             → isDualClosure E f
                             → isDualClosure' E f
isDualClosure→isDualClosure' E f (isf , f≡f∘f , fx≤x) x y
  = propBiimpl→Equiv (prop _ _) (prop _ _)
                     (λ fx≤y → subst (_≤ f y) (sym (funExt⁻ f≡f∘f x))
                                     (IsIsotone.pres≤ isf (f x) y fx≤y))
                      λ fx≤fy → trans (f x) (f y) y fx≤fy (fx≤x y)
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)

        prop = IsPoset.is-prop-valued is
        trans = IsPoset.is-trans is

isClosure'→isClosure : (E : Poset ℓ ℓ')
                     → ∀ f
                     → isClosure' E f
                     → isClosure E f
isClosure'→isClosure E f eq
  = isf ,
   (funExt λ x → anti (f x) (f (f x))
                      (IsIsotone.pres≤ isf x (f x) (x≤fx x))
                      (equivFun (eq (f x) x) (rfl (f x)))) ,
    x≤fx
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)

        rfl = IsPoset.is-refl is
        anti = IsPoset.is-antisym is
        trans = IsPoset.is-trans is

        x≤fx : ∀ x → x ≤ f x
        x≤fx x = invEq (eq x x) (rfl (f x))

        isf : IsIsotone (snd E) f (snd E)
        IsIsotone.pres≤ isf x y x≤y
          = equivFun (eq x y)
                     (trans x y (f y) x≤y (x≤fx y))

isDualClosure'→isDualClosure : (E : Poset ℓ ℓ')
                             → ∀ f
                             → isDualClosure' E f
                             → isDualClosure E f
isDualClosure'→isDualClosure E f eq
  = isf ,
    (funExt (λ x → anti (f x) (f (f x))
                        (equivFun (eq x (f x)) (rfl (f x)))
                        (IsIsotone.pres≤ isf (f x) x (fx≤x x)))) ,
    fx≤x
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)

        rfl = IsPoset.is-refl is
        anti = IsPoset.is-antisym is
        trans = IsPoset.is-trans is

        fx≤x : ∀ x → f x ≤ x
        fx≤x x = invEq (eq x x) (rfl (f x))

        isf : IsIsotone (snd E) f (snd E)
        IsIsotone.pres≤ isf x y x≤y
          = equivFun (eq x y)
                     (trans (f x) x y (fx≤x x) x≤y)

isClosure→ComposedResidual : {E : Poset ℓ ℓ'}
                             {f : ⟨ E ⟩ → ⟨ E ⟩}
                           → isClosure E f
                           → Σ[ F ∈ Poset ℓ ℓ' ] (Σ[ g ∈ (⟨ E ⟩ → ⟨ F ⟩) ] (Σ[ res ∈ hasResidual E F g ] f ≡ (residual E F g res) ∘ g))
isClosure→ComposedResidual {ℓ} {ℓ'} {E = E} {f = f} (isf , f≡f∘f , x≤fx) = F , ♮ , (is♮ , ♮⁺ , is♮⁺ , x≤fx , ♮∘♮⁺) , refl
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)
        set = IsPoset.is-set is
        prop = IsPoset.is-prop-valued is
        rfl = IsPoset.is-refl is
        anti = IsPoset.is-antisym is
        trans = IsPoset.is-trans is

        kerf : Rel ⟨ E ⟩ ⟨ E ⟩ ℓ
        kerf x y = f x ≡ f y

        F' = ⟨ E ⟩ / kerf

        _⊑'_ : F' → F' → hProp _
        _⊑'_ = fun
          where
            fun₀ : ⟨ E ⟩ → F' → hProp _
            fst (fun₀ x [ y ]) = f x ≤ f y
            snd (fun₀ x [ y ]) = prop (f x) (f y)
            fun₀ x (eq/ a b fa≡fb i) = record
              { fst = cong (f x ≤_) fa≡fb i
              ; snd = isProp→PathP (λ i → isPropIsProp {A = cong (f x ≤_) fa≡fb i})
                                   (prop (f x) (f a)) (prop (f x) (f b)) i
              }
            fun₀ x (squash/ a b p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
              (λ _ → fun₀ x a)
              (λ _ → fun₀ x b)
              (λ i → fun₀ x (p i))
              (λ i → fun₀ x (q i)) j i

            toPath : ∀ a b (p : kerf a b) (y : F') → fun₀ a y ≡ fun₀ b y
            toPath a b fa≡fb = elimProp (λ _ → isSetHProp _ _) λ c →
              Σ≡Prop (λ _ → isPropIsProp) (cong (_≤ f c) fa≡fb)

            fun : F' → F' → hProp _
            fun [ a ] y = fun₀ a y
            fun (eq/ a b fa≡fb i) y = toPath a b fa≡fb y i
            fun (squash/ x y p q i j) z = isSet→SquareP (λ _ _ → isSetHProp)
              (λ _ → fun x z) (λ _ → fun y z) (λ i → fun (p i) z) (λ i → fun (q i) z) j i

        _⊑_ : Rel F' F' ℓ'
        a ⊑ b = (a ⊑' b) .fst

        open BinaryRelation _⊑_

        isProp⊑ : isPropValued
        isProp⊑ a b = (a ⊑' b) .snd

        isRefl⊑ : isRefl
        isRefl⊑ = elimProp (λ x → isProp⊑ x x)
                           (rfl ∘ f)

        isAntisym⊑ : isAntisym
        isAntisym⊑ = elimProp2 (λ x y → isPropΠ2 λ _ _ → squash/ x y)
                                λ a b fa≤fb fb≤fa → eq/ a b (anti (f a) (f b) fa≤fb fb≤fa)

        isTrans⊑ : isTrans
        isTrans⊑ = elimProp3 (λ x _ z → isPropΠ2 λ _ _ → isProp⊑ x z)
                              λ a b c → trans (f a) (f b) (f c)

        poset⊑ : IsPoset _⊑_
        poset⊑ = isposet squash/ isProp⊑ isRefl⊑ isTrans⊑ isAntisym⊑

        F : Poset ℓ ℓ'
        F = F' , (posetstr _⊑_ poset⊑)

        ♮ : ⟨ E ⟩ → ⟨ F ⟩
        ♮ = [_]

        is♮ : IsIsotone (snd E) ♮ (snd F)
        IsIsotone.pres≤ is♮ x y x≤y = IsIsotone.pres≤ isf x y x≤y

        ♮⁺ : ⟨ F ⟩ → ⟨ E ⟩
        ♮⁺ [ x ] = f x
        ♮⁺ (eq/ a b fa≡fb i) = fa≡fb i
        ♮⁺ (squash/ x y p q i j) = isSet→SquareP (λ _ _ → set)
          (λ _ → ♮⁺ x)
          (λ _ → ♮⁺ y)
          (λ i → ♮⁺ (p i))
          (λ i → ♮⁺ (q i)) j i

        is♮⁺ : IsIsotone (snd F) ♮⁺ (snd E)
        IsIsotone.pres≤ is♮⁺ = elimProp2 (λ x y → isPropΠ λ _ → prop (♮⁺ x) (♮⁺ y))
                                          λ x y fx≤fy → fx≤fy

        ♮∘♮⁺ : ∀ x → (♮ ∘ ♮⁺) x ⊑ x
        ♮∘♮⁺ = elimProp (λ x → isProp⊑ ((♮ ∘ ♮⁺) x) x)
                        λ x → subst (_≤ f x) (funExt⁻ f≡f∘f x) (rfl (f x))

isDualClosure→ComposedResidual : {E : Poset ℓ ℓ'}
                                 {f : ⟨ E ⟩ → ⟨ E ⟩}
                               → isDualClosure E f
                               → Σ[ F ∈ Poset ℓ ℓ' ] (Σ[ g ∈ (⟨ F ⟩ → ⟨ E ⟩) ] (Σ[ res ∈ hasResidual F E g ] f ≡ g ∘ (residual F E g res)))
isDualClosure→ComposedResidual {ℓ} {ℓ'} {E = E} {f = f} (isf , f≡f∘f , fx≤x) = F , ♮ , (is♮ , ♮⁺ , is♮⁺ , ♮⁺∘♮ , fx≤x) , refl
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)
        set = IsPoset.is-set is
        prop = IsPoset.is-prop-valued is
        rfl = IsPoset.is-refl is
        anti = IsPoset.is-antisym is
        trans = IsPoset.is-trans is

        kerf : Rel ⟨ E ⟩ ⟨ E ⟩ ℓ
        kerf x y = f x ≡ f y

        F' = ⟨ E ⟩ / kerf

        _⊑'_ : F' → F' → hProp _
        _⊑'_ = fun
          where
            fun₀ : ⟨ E ⟩ → F' → hProp _
            fst (fun₀ x [ y ]) = f x ≤ f y
            snd (fun₀ x [ y ]) = prop (f x) (f y)
            fun₀ x (eq/ a b fa≡fb i) = record
              { fst = cong (f x ≤_) fa≡fb i
              ; snd = isProp→PathP (λ i → isPropIsProp {A = cong (f x ≤_) fa≡fb i})
                                   (prop (f x) (f a)) (prop (f x) (f b)) i
              }
            fun₀ x (squash/ a b p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
              (λ _ → fun₀ x a)
              (λ _ → fun₀ x b)
              (λ i → fun₀ x (p i))
              (λ i → fun₀ x (q i)) j i

            toPath : ∀ a b (p : kerf a b) (y : F') → fun₀ a y ≡ fun₀ b y
            toPath a b fa≡fb = elimProp (λ _ → isSetHProp _ _) λ c →
              Σ≡Prop (λ _ → isPropIsProp) (cong (_≤ f c) fa≡fb)

            fun : F' → F' → hProp _
            fun [ a ] y = fun₀ a y
            fun (eq/ a b fa≡fb i) y = toPath a b fa≡fb y i
            fun (squash/ x y p q i j) z = isSet→SquareP (λ _ _ → isSetHProp)
              (λ _ → fun x z) (λ _ → fun y z) (λ i → fun (p i) z) (λ i → fun (q i) z) j i

        _⊑_ : Rel F' F' ℓ'
        a ⊑ b = (a ⊑' b) .fst

        open BinaryRelation _⊑_

        isProp⊑ : isPropValued
        isProp⊑ a b = (a ⊑' b) .snd

        isRefl⊑ : isRefl
        isRefl⊑ = elimProp (λ x → isProp⊑ x x)
                           (rfl ∘ f)

        isAntisym⊑ : isAntisym
        isAntisym⊑ = elimProp2 (λ x y → isPropΠ2 λ _ _ → squash/ x y)
                                λ a b fa≤fb fb≤fa → eq/ a b (anti (f a) (f b) fa≤fb fb≤fa)

        isTrans⊑ : isTrans
        isTrans⊑ = elimProp3 (λ x _ z → isPropΠ2 λ _ _ → isProp⊑ x z)
                              λ a b c → trans (f a) (f b) (f c)

        poset⊑ : IsPoset _⊑_
        poset⊑ = isposet squash/ isProp⊑ isRefl⊑ isTrans⊑ isAntisym⊑

        F : Poset ℓ ℓ'
        F = F' , (posetstr _⊑_ poset⊑)

        ♮⁺ : ⟨ E ⟩ → ⟨ F ⟩
        ♮⁺ = [_]

        is♮⁺ : IsIsotone (snd E) ♮⁺ (snd F)
        IsIsotone.pres≤ is♮⁺ x y x≤y = IsIsotone.pres≤ isf x y x≤y

        ♮ : ⟨ F ⟩ → ⟨ E ⟩
        ♮ [ x ] = f x
        ♮ (eq/ a b fa≡fb i) = fa≡fb i
        ♮ (squash/ x y p q i j) = isSet→SquareP (λ _ _ → set)
          (λ _ → ♮ x)
          (λ _ → ♮ y)
          (λ i → ♮ (p i))
          (λ i → ♮ (q i)) j i

        is♮ : IsIsotone (snd F) ♮ (snd E)
        IsIsotone.pres≤ is♮ = elimProp2 (λ x y → isPropΠ λ _ → prop (♮ x) (♮ y))
                                         λ x y fx≤fy → fx≤fy

        ♮⁺∘♮ : ∀ x → x ⊑ (♮⁺ ∘ ♮) x
        ♮⁺∘♮ = elimProp (λ x → isProp⊑ x ((♮⁺ ∘ ♮) x))
                        λ x → subst (f x ≤_) (funExt⁻ f≡f∘f x) (rfl (f x))

ComposedResidual→isClosure : {E : Poset ℓ ℓ'}
                             {f : ⟨ E ⟩ → ⟨ E ⟩}
                           → Σ[ F ∈ Poset ℓ ℓ' ] (Σ[ g ∈ (⟨ E ⟩ → ⟨ F ⟩) ] (Σ[ res ∈ hasResidual E F g ] f ≡ (residual E F g res) ∘ g))
                           → isClosure E f
ComposedResidual→isClosure {E = E} {f = f} (F , g , (isg , g⁺ , isg⁺ , g⁺∘g , g∘g⁺) , f≡g⁺∘g)
  = subst (λ x → IsIsotone (snd E) x (snd E)) (sym f≡g⁺∘g) (IsIsotone-∘ (snd E) g (snd F) g⁺ (snd E) isg isg⁺) ,
    f≡g⁺∘g ∙
    sym (cong (g⁺ ∘_)
              (AbsorbResidual E F g (isg , g⁺ , isg⁺ , g⁺∘g , g∘g⁺))) ∙
    cong (_∘ g⁺ ∘ g) (sym f≡g⁺∘g) ∙
    cong (f ∘_) (sym f≡g⁺∘g) ,
    λ x → subst (x ≤_) (sym (funExt⁻ f≡g⁺∘g x)) (g⁺∘g x)
    where _≤_ = PosetStr._≤_ (snd E)

ComposedResidual→isDualClosure : {E : Poset ℓ ℓ'}
                                 {f : ⟨ E ⟩ → ⟨ E ⟩}
                               → Σ[ F ∈ Poset ℓ ℓ' ] (Σ[ g ∈ (⟨ F ⟩ → ⟨ E ⟩) ] (Σ[ res ∈ hasResidual F E g ] f ≡ g ∘ (residual F E g res)))
                               → isDualClosure E f
ComposedResidual→isDualClosure {E = E} {f = f} (F , g , (isg , g⁺ , isg⁺ , g⁺∘g , g∘g⁺) , f≡g∘g⁺)
  = subst (λ x → IsIsotone (snd E) x (snd E)) (sym f≡g∘g⁺) (IsIsotone-∘ (snd E) g⁺ (snd F) g (snd E) isg⁺ isg) ,
  f≡g∘g⁺ ∙
  sym (cong (g ∘_) (ResidualAbsorb F E g (isg , g⁺ , isg⁺ , g⁺∘g , g∘g⁺))) ∙
  cong (_∘ g ∘ g⁺) (sym f≡g∘g⁺) ∙
  cong (f ∘_) (sym f≡g∘g⁺) ,
  λ x → subst (_≤ x) (sym (funExt⁻ f≡g∘g⁺ x)) (g∘g⁺ x)
  where _≤_ = PosetStr._≤_ (snd E)

isPropIsClosure : {E : Poset ℓ ℓ'}
                  {f : ⟨ E ⟩ → ⟨ E ⟩}
                → isProp (isClosure E f)
isPropIsClosure {E = E} {f = f}
  = isProp× (isPropIsIsotone (snd E) f (snd E))
            (isProp× (isSet→ (IsPoset.is-set is) _ _)
                     (isPropΠ λ x → IsPoset.is-prop-valued is x (f x)))
  where is = PosetStr.isPoset (snd E)

isPropIsClosure' : {E : Poset ℓ ℓ'}
                   {f : ⟨ E ⟩ → ⟨ E ⟩}
                 → isProp (isClosure' E f)
isPropIsClosure' {E = E} {f = f}
  = isPropΠ2 λ x y → isOfHLevel≃ 1 (prop x (f y)) (prop (f x) (f y))
  where prop = IsPoset.is-prop-valued (PosetStr.isPoset (snd E))

isPropIsDualClosure : {E : Poset ℓ ℓ'}
                      {f : ⟨ E ⟩ → ⟨ E ⟩}
                    → isProp (isDualClosure E f)
isPropIsDualClosure {E = E} {f = f}
  = isProp× (isPropIsIsotone (snd E) f (snd E))
            (isProp× (isSet→ (IsPoset.is-set is) _ _)
                     (isPropΠ λ x → IsPoset.is-prop-valued is (f x) x))
  where is = PosetStr.isPoset (snd E)

isPropIsDualClosure' : {E : Poset ℓ ℓ'}
                       {f : ⟨ E ⟩ → ⟨ E ⟩}
                     → isProp (isDualClosure' E f)
isPropIsDualClosure' {E = E} {f = f}
  = isPropΠ2 λ x y → isOfHLevel≃ 1 (prop (f x) y) (prop (f x) (f y))
  where prop = IsPoset.is-prop-valued (PosetStr.isPoset (snd E))

isClosureSubset : (E : Poset ℓ ℓ')
                → (F : Embedding ⟨ E ⟩ ℓ)
                → Type _
isClosureSubset E F = Σ[ f ∈ (⟨ E ⟩ → ⟨ E ⟩) ] (isClosure E f × (F ≡ (Image f , imageInclusion f)))

isDualClosureSubset : (E : Poset ℓ ℓ')
                    → (F : Embedding ⟨ E ⟩ ℓ)
                    → Type _
isDualClosureSubset E F = Σ[ f ∈ (⟨ E ⟩ → ⟨ E ⟩) ] (isDualClosure E f × (F ≡ (Image f , imageInclusion f)))

ClosureSubsetOperatorUnique : {E : Poset ℓ ℓ'}
                              {F : Embedding ⟨ E ⟩ ℓ}
                            → (f g : isClosureSubset E F)
                            → f .fst ≡ g .fst
ClosureSubsetOperatorUnique {E = E} {F = F}
                            (f , (isf , f≡f∘f , x≤fx) , F≡Imf)
                            (g , (isg , g≡g∘g , x≤gx) , F≡Img)
  = funExt λ x → anti (f x) (g x) (fx≤gx x) (gx≤fx x)
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)

        prop = IsPoset.is-prop-valued is
        anti = IsPoset.is-antisym is

        Imf⊆Img : (Image f , imageInclusion f) ⊆ₑ (Image g , imageInclusion g)
        Imf⊆Img x = subst (x ∈ₑ_) (sym F≡Imf ∙ F≡Img)

        Img⊆Imf : (Image g , imageInclusion g) ⊆ₑ (Image f , imageInclusion f)
        Img⊆Imf x = subst (x ∈ₑ_) (sym F≡Img ∙ F≡Imf)

        fx≤gx : ∀ x → f x ≤ g x
        fx≤gx x = ∥₁.rec (prop (f x) (g x))
                          (λ { (a , fa≡gx) → subst (f x ≤_)
                                               (sym (funExt⁻ f≡f∘f a) ∙
                                                fa≡gx ∙
                                                lemma .snd)
                                               (IsIsotone.pres≤ isf x (f a)
                                                (subst (x ≤_)
                                                  (sym (fa≡gx ∙ lemma .snd))
                                                    (x≤gx x))) })
                          (lemma .fst .snd)
              where lemma = Img⊆Imf (g x) (((g x) , ∣ x , refl ∣₁) , refl)

        gx≤fx : ∀ x → g x ≤ f x
        gx≤fx x = ∥₁.rec (prop (g x) (f x))
                         (λ { (a , ga≡fx) → subst (g x ≤_)
                                              (sym (funExt⁻ g≡g∘g a) ∙
                                                    ga≡fx ∙
                                                    lemma .snd)
                                              (IsIsotone.pres≤ isg x (g a)
                                               (subst (x ≤_)
                                                 (sym (ga≡fx ∙ lemma .snd))
                                                   (x≤fx x))) })
                         (lemma .fst .snd)
              where lemma = Imf⊆Img (f x) (((f x) , ∣ x , refl ∣₁) , refl)

DualClosureSubsetOperatorUnique : {E : Poset ℓ ℓ'}
                                  {F : Embedding ⟨ E ⟩ ℓ}
                                → (f g : isDualClosureSubset E F)
                                → f .fst ≡ g .fst
DualClosureSubsetOperatorUnique {E = E} {F = F}
                                (f , (isf , f≡f∘f , fx≤x) , F≡Imf)
                                (g , (isg , g≡g∘g , gx≤x) , F≡Img)
  = funExt λ x → anti (f x) (g x) (fx≤gx x) (gx≤fx x)
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)

        prop = IsPoset.is-prop-valued is
        anti = IsPoset.is-antisym is

        Imf⊆Img : (Image f , imageInclusion f) ⊆ₑ (Image g , imageInclusion g)
        Imf⊆Img x = subst (x ∈ₑ_) (sym F≡Imf ∙ F≡Img)

        Img⊆Imf : (Image g , imageInclusion g) ⊆ₑ (Image f , imageInclusion f)
        Img⊆Imf x = subst (x ∈ₑ_) (sym F≡Img ∙ F≡Imf)

        gx≤fx : ∀ x → g x ≤ f x
        gx≤fx x = ∥₁.rec (prop (g x) (f x))
                         (λ { (a , fa≡gx) → subst (_≤ f x) (sym (funExt⁻ f≡f∘f a) ∙
                                                                  fa≡gx ∙
                                                                  lemma .snd)
                                                            (IsIsotone.pres≤ isf (f a) x
                                                             (subst (_≤ x)
                                                               (sym (fa≡gx ∙ lemma .snd))
                                                                 (gx≤x x))) })
                         (lemma .fst .snd)
              where lemma = Img⊆Imf (g x) (((g x) , ∣ x , refl ∣₁) , refl)

        fx≤gx : ∀ x → f x ≤ g x
        fx≤gx x = ∥₁.rec (prop (f x) (g x))
                         (λ { (a , ga≡fx) → subst (_≤ g x)
                                              (sym (funExt⁻ g≡g∘g a) ∙
                                                    ga≡fx ∙
                                                    lemma .snd)
                                              (IsIsotone.pres≤ isg (g a) x
                                                (subst (_≤ x)
                                                  (sym (ga≡fx ∙ lemma .snd))
                                                    (fx≤x x))) })
                         (lemma .fst .snd)
              where lemma = Imf⊆Img (f x) (((f x) , ∣ x , refl ∣₁) , refl)

isPropIsClosureSubset : {E : Poset ℓ ℓ'}
                        {F : Embedding ⟨ E ⟩ ℓ}
                      → isProp (isClosureSubset E F)
isPropIsClosureSubset p q = Σ≡Prop (λ f → isProp× isPropIsClosure (isSetEmbedding _ _))
                                    (ClosureSubsetOperatorUnique p q)

isPropIsDualClosureSubset : {E : Poset ℓ ℓ'}
                            {F : Embedding ⟨ E ⟩ ℓ}
                          → isProp (isDualClosureSubset E F)
isPropIsDualClosureSubset p q = Σ≡Prop (λ f → isProp× isPropIsDualClosure (isSetEmbedding _ _))
                                        (DualClosureSubsetOperatorUnique p q)

isClosureSubset→IntersectionBottom : (E : Poset ℓ ℓ')
                                     (F : Embedding ⟨ E ⟩ ℓ)
                                   → isClosureSubset E F
                                   → ∀ x
                                   → Least (isPoset→isProset (PosetStr.isPoset (snd E))) (principalUpset E x ∩ₑ F)
isClosureSubset→IntersectionBottom E F (f , (isf , f≡f∘f , x≤fx) , F≡Imf) x
  = (f x , fx∈x↑ , fx∈F ) , least
  where _≤_ = PosetStr._≤_ (snd E)
        is = PosetStr.isPoset (snd E)

        prop = IsPoset.is-prop-valued is

        fx∈x↑ : f x ∈ₑ principalUpset E x
        fx∈x↑ = equivFun (principalUpsetMembership E x (f x)) (x≤fx x)

        fx∈F : f x ∈ₑ F
        fx∈F = subst (f x ∈ₑ_) (sym F≡Imf) ((f x , ∣ x , refl ∣₁) , refl)

        least : isLeast (isPoset→isProset is) (principalUpset E x ∩ₑ F) (f x , fx∈x↑ , fx∈F)
        least (y , y∈x↑ , y∈F) = ∥₁.rec (prop _ _)
                                        (λ { (a , fa≡fz)
                                           → subst (f x ≤_)
                                            (sym (funExt⁻ f≡f∘f a ∙
                                                 cong f (fa≡fz ∙
                                                         lemma .snd)) ∙
                                                 fa≡fz ∙
                                                 lemma .snd)
                                            (IsIsotone.pres≤ isf x y
                                              (invEq (principalUpsetMembership E x y) y∈x↑)) })
                                         (lemma .fst .snd)
          where lemma = subst (y ∈ₑ_) F≡Imf y∈F

IntersectionBottom→isClosureSubset : (E : Poset ℓ ℓ)
                                     (F : Embedding ⟨ E ⟩ ℓ)
                                   → (∀ x → Least (isPoset→isProset (PosetStr.isPoset (snd E))) (principalUpset E x ∩ₑ F))
                                   → isClosureSubset E F
IntersectionBottom→isClosureSubset E F least
  = f , (isf , f≡f∘f , x≤f) , F≡Imf
    where _≤_ = PosetStr._≤_ (snd E)
          is = PosetStr.isPoset (snd E)

          rfl = IsPoset.is-refl is
          anti = IsPoset.is-antisym is

          f : ⟨ E ⟩ → ⟨ E ⟩
          f x = least x .fst .fst

          isf : IsIsotone (snd E) f (snd E)
          IsIsotone.pres≤ isf x y x≤y = least x .snd (f y , y↑∩F⊆x↑∩F (f y) ((least y .fst) , refl) .fst .snd)
            where x↑ = principalUpset E x
                  y↑ = principalUpset E y

                  y↑⊆x↑ = principalUpsetInclusion E x y x≤y
                  y↑∩F⊆x↑∩F = isMeetIsotone
                              (isPoset→isProset isPoset⊆ₑ) y↑ x↑ F F
                              (y↑ ∩ₑ F)
                              (x↑ ∩ₑ F)
                              (isMeet∩ₑ y↑ F)
                              (isMeet∩ₑ x↑ F)
                               y↑⊆x↑
                              (isRefl⊆ₑ F)

          x≤f : ∀ x → x ≤ f x
          x≤f x = invEq (principalUpsetMembership E x (f x)) (least x .fst .snd .fst)

          F≡fF : ∀ y → y ∈ₑ F
                      → y ≡ f y
          F≡fF y y∈F = anti y (f y) (x≤f y)
                       (least y .snd (y , equivFun (principalUpsetMembership E y y) (rfl y) , y∈F))

          f≡f∘f : f ≡ (f ∘ f)
          f≡f∘f = funExt λ x → F≡fF (f x) (least x .fst .snd .snd)

          F⊆Imf : F ⊆ₑ (Image f , imageInclusion f)
          F⊆Imf x x∈F = (x , ∣ x , (sym (F≡fF x x∈F)) ∣₁) , refl

          Imf⊆F : (Image f , imageInclusion f) ⊆ₑ F
          Imf⊆F x ((a , ima) , fib)
            = ∥₁.rec (isProp∈ₑ x F)
                     (λ { (b , fb≡a) →
                           subst (_∈ₑ F)
                                 (fb≡a ∙ fib)
                                 (least b .fst .snd .snd) }) ima

          F≡Imf : F ≡ (Image f , imageInclusion f)
          F≡Imf = isAntisym⊆ₑ F (Image f , imageInclusion f) F⊆Imf Imf⊆F
