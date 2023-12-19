{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Mappings where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Algebra.Semigroup

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Functions.Embedding
open import Cubical.Functions.Logic using (_⊔′_)
open import Cubical.Functions.Preimage

open import Cubical.Reflection.RecordEquiv

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Order.Poset.Base


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

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
            isDownset× : isDownset (((Σ[ x ∈ ⟨ P ⟩ ] (x ∈ₑ A × x ∈ₑ B)) ,
                                   EmbeddingΣProp λ x → isProp× (isProp∈ₑ x A)
                                                                (isProp∈ₑ x B)))
            isDownset× (x , (a , a≡x) , (b , b≡x)) y y≤x
              = (y , (downA a y (subst (y ≤_) (sym a≡x) y≤x) ,
                      downB b y (subst (y ≤_) (sym b≡x) y≤x))) , refl

            isDownset⊎ : isDownset (((Σ[ x ∈ ⟨ P ⟩ ] (x ∈ₑ A ⊔′ x ∈ₑ B)) ,
                                   EmbeddingΣProp λ _ → isPropPropTrunc))
            isDownset⊎ (x , A⊎B) y y≤x
              = ∥₁.rec (isProp∈ₑ y ((Σ[ x ∈ ⟨ P ⟩ ] (x ∈ₑ A ⊔′ x ∈ₑ B)) ,
                                   EmbeddingΣProp λ _ → isPropPropTrunc))
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
            isUpset× : isUpset (((Σ[ x ∈ ⟨ P ⟩ ] (x ∈ₑ A × x ∈ₑ B)) ,
                               EmbeddingΣProp λ x → isProp× (isProp∈ₑ x A)
                                                            (isProp∈ₑ x B)))
            isUpset× (x , (a , a≡x) , (b , b≡x)) y x≤y
              = (y , (upA a y (subst (_≤ y) (sym a≡x) x≤y) ,
                      upB b y (subst (_≤ y) (sym b≡x) x≤y))) , refl

            isUpset⊎ : isUpset (((Σ[ x ∈ ⟨ P ⟩ ] (x ∈ₑ A ⊔′ x ∈ₑ B)) ,
                               EmbeddingΣProp λ _ → isPropPropTrunc))
            isUpset⊎ (x , A⊎B) y x≤y
              = ∥₁.rec (isProp∈ₑ y ((Σ[ x ∈ ⟨ P ⟩ ] (x ∈ₑ A ⊔′ x ∈ₑ B)) ,
                                   EmbeddingΣProp λ _ → isPropPropTrunc))
                       (⊎.rec (λ { (a , a≡x) →
                              (y , ∣ inl (upA a y (subst (_≤ y)
                                                         (sym a≡x) x≤y)) ∣₁) , refl })
                              (λ { (b , b≡x) →
                              (y , ∣ inr (upB b y (subst (_≤ y)
                                                         (sym b≡x) x≤y)) ∣₁) , refl })) A⊎B

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
                         λ x →
                           isPrincipalDownset→isDownset P (f ⃖ principalDownset S x) (down x)

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
