{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Woset.Simulation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Induction.WellFounded

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Binary.Order.Woset.Base
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Extensionality

private
  variable
    ℓ ℓ' : Level

isSimulation : (A B : Woset ℓ ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isSimulation A B f = respectsRel × existsFib
  where _≺ᵣ_ = WosetStr._≺_ (str A)
        _≺ₛ_ = WosetStr._≺_ (str B)

        respectsRel = ∀ a a' → a ≺ᵣ a' → (f a) ≺ₛ (f a')

        less : ∀ a → Type _
        less a = Σ[ a' ∈ ⟨ A ⟩ ] a' ≺ᵣ a

        existsFib = ∀ a → ∀ b → b ≺ₛ (f a) → fiber {A = less a} (f ∘ fst) b

isSimulation→isEmbedding : (A B : Woset ℓ ℓ') → ∀ f
                         → isSimulation A B f → isEmbedding f
isSimulation→isEmbedding A B f (rrel , efib)
  = injEmbedding setB
    λ {a b} → WFI.induction wellR {P = λ a' → ∀ b' → f a' ≡ f b' → a' ≡ b'}
            (λ a' inda b' fa'≡fb' → isWeaklyExtensional→≺Equiv→≡
               _≺ᵣ_ weakR a' b' λ c → propBiimpl→Equiv
                 (propR c a') (propR c b')
                 (λ c≺ᵣa' → subst (_≺ᵣ b')
                            (sym (inda c c≺ᵣa'
                                 (efib b' (f c)
                                   (subst (f c ≺ₛ_) fa'≡fb'
                                          (rrel c a' c≺ᵣa')) .fst .fst)
                                 (sym (efib b' (f c) (subst (f c ≺ₛ_)
                                      fa'≡fb' (rrel c a' c≺ᵣa')) .snd))))
                            (efib b' (f c) (subst (f c ≺ₛ_) fa'≡fb'
                                             (rrel c a' c≺ᵣa')) .fst .snd))
                  λ c≺ᵣb' → subst (_≺ᵣ a')
                            (inda (efib a' (f c) (subst (f c ≺ₛ_)
                              (sym fa'≡fb') (rrel c b' c≺ᵣb')) .fst .fst)
                                (efib a' (f c) (subst (f c ≺ₛ_)
                                  (sym fa'≡fb') (rrel c b' c≺ᵣb')) .fst .snd)
                                c (efib a' (f c) (subst (f c ≺ₛ_)
                                  (sym fa'≡fb') (rrel c b' c≺ᵣb')) .snd))
                              (efib a' (f c) (subst (f c ≺ₛ_)
                                (sym fa'≡fb') (rrel c b' c≺ᵣb')) .fst .snd)) a b
    where _≺ᵣ_ = WosetStr._≺_ (str A)
          _≺ₛ_ = WosetStr._≺_ (str B)

          IsWosetR = WosetStr.isWoset (str A)
          IsWosetS = WosetStr.isWoset (str B)

          setB = IsWoset.is-set IsWosetS

          wellR = IsWoset.is-well-founded IsWosetR

          weakR = IsWoset.is-weakly-extensional IsWosetR

          propR = IsWoset.is-prop-valued IsWosetR

isPropIsSimulation : (A B : Woset ℓ ℓ') → ∀ f → isProp (isSimulation A B f)
isPropIsSimulation A B f sim₀
  = isProp× (isPropΠ3 λ _ _ _ → propS _ _)
            (isPropΠ3 (λ _ b _ → isEmbedding→hasPropFibers
                                 (isEmbedding-∘
                                 (isSimulation→isEmbedding A B f sim₀)
                                 λ w x → isEmbeddingFstΣProp
                                         λ _ → propR _ _) b)) sim₀
  where propR = IsWoset.is-prop-valued (WosetStr.isWoset (str A))
        propS = IsWoset.is-prop-valued (WosetStr.isWoset (str B))
