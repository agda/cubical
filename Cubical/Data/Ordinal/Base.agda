{-

This file contains:

- Ordinals as well-ordered sets

-}
{-# OPTIONS --safe #-}
module Cubical.Data.Ordinal.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Extensionality
open import Cubical.Relation.Binary.Order.Woset

private
  variable
    ℓ : Level

infix 7 _·_
infix 6 _+_

-- Ordinals are simply well-ordered sets
Ord : ∀ {ℓ} → Type _
Ord {ℓ} = Woset ℓ ℓ

isSetOrd : isSet (Ord {ℓ})
isSetOrd = isSetWoset

-- The successor ordinal is simply the union with unit
suc : Ord {ℓ} → Ord {ℓ}
suc {ℓ} (A , ordStr) = (A ⊎ Unit* {ℓ}) , wosetstr _≺_ iswos
  where _≺ₐ_ = WosetStr._≺_ ordStr
        wosA = WosetStr.isWoset ordStr
        setA = IsWoset.is-set wosA
        propA = IsWoset.is-prop-valued wosA
        wellA = IsWoset.is-well-founded wosA
        weakA = IsWoset.is-weakly-extensional wosA
        transA = IsWoset.is-trans wosA


        _≺_ : Rel (A ⊎ Unit* {ℓ}) (A ⊎ Unit* {ℓ}) ℓ
        inl a ≺ inl b = a ≺ₐ b
        inl _ ≺ inr * = Unit* {ℓ}
        inr * ≺ _ = ⊥* {ℓ}

        open BinaryRelation

        set : isSet (A ⊎ Unit*)
        set = isSet⊎ setA isSetUnit*

        prop : isPropValued _≺_
        prop (inl a) (inl b) = propA a b
        prop (inl _) (inr *) = isPropUnit*
        prop (inr *) _ = isProp⊥*

        well : WellFounded _≺_
        well (inl x) = WFI.induction wellA {P = λ x → Acc _≺_ (inl x)}
                     (λ _ ind → acc (λ { (inl y) → ind y
                                       ; (inr *) () })) x
        well (inr *) = acc (λ { (inl y) _ → well (inl y)
                              ; (inr *) () })

        weak : isWeaklyExtensional _≺_
        weak = ≺×→≡→isWeaklyExtensional _≺_ set prop
             λ { (inl x) (inl y) ex → cong inl
                 (isWeaklyExtensional→≺Equiv→≡ _≺ₐ_ weakA x y λ z
                 → propBiimpl→Equiv (propA z x) (propA z y)
                   (ex (inl z) .fst)
                   (ex (inl z) .snd))
               ; (inl x) (inr *) ex → ⊥.rec
                   (WellFounded→isIrrefl _≺ₐ_ wellA x (ex (inl x) .snd tt*))
               ; (inr *) (inl x) ex → ⊥.rec
                   (WellFounded→isIrrefl _≺ₐ_ wellA x (ex (inl x) .fst tt*))
               ; (inr *) (inr _) _ → refl
               }

        trans : isTrans _≺_
        trans (inl a) (inl b) (inl c) = transA a b c
        trans (inl _) (inl _) (inr *) _ _ = tt*
        trans (inl a) (inr *) _ _ ()
        trans (inr *) _ _ ()

        iswos : IsWoset _≺_
        iswos = iswoset set prop well weak trans

-- Ordinal addition is handled similarly
_+_ : Ord {ℓ} → Ord {ℓ} → Ord {ℓ}
A + B = (⟨ A ⟩ ⊎ ⟨ B ⟩) , wosetstr _≺_ wos
  where _≺ᵣ_ = WosetStr._≺_ (str A)
        _≺ₛ_ = WosetStr._≺_ (str B)

        wosA = WosetStr.isWoset (str A)
        setA = IsWoset.is-set wosA
        propA = IsWoset.is-prop-valued wosA
        wellA = IsWoset.is-well-founded wosA
        weakA = IsWoset.is-weakly-extensional wosA
        transA = IsWoset.is-trans wosA

        wosB = WosetStr.isWoset (str B)
        setB = IsWoset.is-set wosB
        propB = IsWoset.is-prop-valued wosB
        wellB = IsWoset.is-well-founded wosB
        weakB = IsWoset.is-weakly-extensional wosB
        transB = IsWoset.is-trans wosB

        _≺_ : Rel (⟨ A ⟩ ⊎ ⟨ B ⟩) (⟨ A ⟩ ⊎ ⟨ B ⟩) _
        inl a₀ ≺ inl a₁ = a₀ ≺ᵣ a₁
        inl a₀ ≺ inr b₁ = Unit*
        inr b₀ ≺ inl a₁ = ⊥*
        inr b₀ ≺ inr b₁ = b₀ ≺ₛ b₁

        open BinaryRelation

        set : isSet (⟨ A ⟩ ⊎ ⟨ B ⟩)
        set = isSet⊎ setA setB

        prop : isPropValued _≺_
        prop (inl a₀) (inl a₁) = propA a₀ a₁
        prop (inl a₀) (inr b₁) = isPropUnit*
        prop (inr b₀) (inl a₁) = isProp⊥*
        prop (inr b₀) (inr b₁) = propB b₀ b₁

        well : WellFounded _≺_
        well (inl a₀) = WFI.induction wellA {P = λ a → Acc _≺_ (inl a)}
          (λ _ ind → acc λ { (inl a₁) → ind a₁
                           ; (inr b₁) () }) a₀
        well (inr b₀) = WFI.induction wellB {P = λ b → Acc _≺_ (inr b)}
          (λ _ ind → acc λ { (inl a₁) _ → well (inl a₁)
                           ; (inr b₁) → ind b₁ }) b₀

        weak : isWeaklyExtensional _≺_
        weak = ≺×→≡→isWeaklyExtensional _≺_ set prop
          λ { (inl a₀) (inl a₁) ex → cong inl
              (isWeaklyExtensional→≺Equiv→≡ _≺ᵣ_ weakA a₀ a₁ λ c →
                propBiimpl→Equiv (propA c a₀) (propA c a₁)
                (ex (inl c) .fst)
                (ex (inl c) .snd))
            ; (inl a₀) (inr _) ex →
              ⊥.rec (WellFounded→isIrrefl _≺ᵣ_ wellA a₀ (ex (inl a₀) .snd tt*))
            ; (inr _) (inl a₁) ex →
              ⊥.rec (WellFounded→isIrrefl _≺ᵣ_ wellA a₁ (ex (inl a₁) .fst tt*))
            ; (inr b₀) (inr b₁) ex → cong inr
              (isWeaklyExtensional→≺Equiv→≡ _≺ₛ_ weakB b₀ b₁ λ c →
                propBiimpl→Equiv (propB c b₀) (propB c b₁)
                (ex (inr c) .fst)
                (ex (inr c) .snd))
            }

        trans : isTrans _≺_
        trans (inl a) (inl b) (inl c) = transA a b c
        trans (inl _) _ (inr _) _ _ = tt*
        trans _ (inr _) (inl _) _ ()
        trans (inr _) (inl _) _ ()
        trans (inr a) (inr b) (inr c) = transB a b c

        wos : IsWoset _≺_
        wos = iswoset set prop well weak trans

-- Ordinal multiplication is handled lexicographically
_·_ : Ord {ℓ} → Ord {ℓ} → Ord {ℓ}
A · B = ⟨ A ⟩ × ⟨ B ⟩ , wosetstr _≺_ wos
  where _≺ᵣ_ = WosetStr._≺_ (str A)
        _≺ₛ_ = WosetStr._≺_ (str B)

        wosA = WosetStr.isWoset (str A)
        setA = IsWoset.is-set wosA
        propA = IsWoset.is-prop-valued wosA
        wellA = IsWoset.is-well-founded wosA
        weakA = IsWoset.is-weakly-extensional wosA
        transA = IsWoset.is-trans wosA

        wosB = WosetStr.isWoset (str B)
        setB = IsWoset.is-set wosB
        propB = IsWoset.is-prop-valued wosB
        wellB = IsWoset.is-well-founded wosB
        weakB = IsWoset.is-weakly-extensional wosB
        transB = IsWoset.is-trans wosB

        _≺_ : Rel (⟨ A ⟩ × ⟨ B ⟩) (⟨ A ⟩ × ⟨ B ⟩) _
        (a₀ , b₀) ≺ (a₁ , b₁) = (b₀ ≺ₛ b₁) ⊎ ((b₀ ≡ b₁) × (a₀ ≺ᵣ a₁))

        open BinaryRelation

        set : isSet (⟨ A ⟩ × ⟨ B ⟩)
        set = isSet× setA setB

        prop : isPropValued _≺_
        prop (a₀ , b₀) (a₁ , b₁)
          = isProp⊎ (propB _ _) (isProp× (setB _ _) (propA _ _))
            λ b₀≺b₁ (b₀≡b₁ , _)
          → WellFounded→isIrrefl _≺ₛ_ wellB b₁ (subst (_≺ₛ b₁) b₀≡b₁ b₀≺b₁)

        well : WellFounded _≺_
        well (a₀ , b₀) = WFI.induction wellB {P = λ b → ∀ a → Acc _≺_ (a , b)}
          (λ b₁ indB → WFI.induction wellA {P = λ a → Acc _≺_ (a , b₁)}
           λ a₂ indA → acc λ { (a , b) (inl b≺b₁) → indB b b≺b₁ a
                             ; (a , b) (inr (b≡b₁ , a≺a₁))
                             → subst (λ x → Acc _≺_ (a , x))
                                     (sym b≡b₁)
                                     (indA a a≺a₁) }) b₀ a₀

        weak : isWeaklyExtensional _≺_
        weak = ≺×→≡→isWeaklyExtensional _≺_ set prop λ (a₀ , b₀) (a₁ , b₁) ex →
             ΣPathP ((isWeaklyExtensional→≺Equiv→≡ _≺ᵣ_ weakA a₀ a₁
               (λ a₂ → propBiimpl→Equiv (propA a₂ a₀) (propA a₂ a₁)
               (λ a₂≺a₀ → ⊎.rec (λ b₀≺b₁ → ⊥.rec
                          (WellFounded→isIrrefl _≺ₛ_ wellB b₁
                          (subst (_≺ₛ b₁) (lemma a₀ a₁ b₀ b₁ ex) b₀≺b₁))) snd
                          (ex (a₂ , b₀) .fst (inr (refl , a₂≺a₀))))
               λ a₂≺a₁ → ⊎.rec (λ b₁≺b₀ → ⊥.rec
                         (WellFounded→isIrrefl _≺ₛ_ wellB b₁
                         (subst (b₁ ≺ₛ_) (lemma a₀ a₁ b₀ b₁ ex) b₁≺b₀))) snd
                         (ex (a₂ , b₁) .snd (inr (refl , a₂≺a₁)))))
               , lemma a₀ a₁ b₀ b₁ ex)
             where lemma : ∀ a₀ a₁ b₀ b₁
                         → (∀ c → (c ≺ (a₀ , b₀) → c ≺ (a₁ , b₁))
                                × (c ≺ (a₁ , b₁) → c ≺ (a₀ , b₀)))
                         → b₀ ≡ b₁
                   lemma a₀ a₁ b₀ b₁ ex
                     = isWeaklyExtensional→≺Equiv→≡ _≺ₛ_ weakB b₀ b₁
                       λ b₂ → propBiimpl→Equiv (propB b₂ b₀) (propB b₂ b₁)
                         (λ b₂≺b₀ → ⊎.rec (λ b₂≺b₁ → b₂≺b₁)
                            (λ (_ , a₁≺a₁)
                            → ⊥.rec (WellFounded→isIrrefl _≺ᵣ_ wellA a₁ a₁≺a₁))
                              (ex (a₁ , b₂) .fst (inl b₂≺b₀)))
                         λ b₂≺b₁ → ⊎.rec (λ b₂≺b₀ → b₂≺b₀)
                           (λ (_ , a₀≺a₀)
                           → ⊥.rec (WellFounded→isIrrefl _≺ᵣ_ wellA a₀ a₀≺a₀))
                             (ex (a₀ , b₂) .snd (inl b₂≺b₁))

        trans : isTrans _≺_
        trans (_ , b₀) (_ , b₁) (_ , b₂) (inl b₀≺b₁) (inl b₁≺b₂)
          = inl (transB b₀ b₁ b₂ b₀≺b₁ b₁≺b₂)
        trans (_ , b₀) _ _ (inl b₀≺b₁) (inr (b₁≡b₂ , _))
          = inl (subst (b₀ ≺ₛ_) b₁≡b₂ b₀≺b₁)
        trans _ _ (_ , b₂) (inr (b₀≡b₁ , _)) (inl b₁≺b₂)
          = inl (subst (_≺ₛ b₂) (sym b₀≡b₁) b₁≺b₂)
        trans (a₀ , _) (a₁ , _) (a₂ , _)
              (inr (b₀≡b₁ , a₀≺a₁))
              (inr (b₁≡b₂ , a₁≺a₂))
          = inr ((b₀≡b₁ ∙ b₁≡b₂) , (transA a₀ a₁ a₂ a₀≺a₁ a₁≺a₂))

        wos : IsWoset _≺_
        wos = iswoset set prop well weak trans
