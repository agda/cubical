{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Woset.Simulation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Induction.WellFounded

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Order.Woset.Base
open import Cubical.Relation.Binary.Order.Poset.Base
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

        existsFib = ∀ a b → b ≺ₛ (f a) → fiber {A = less a} (f ∘ fst) b

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

_≤_ : Rel (Woset ℓ ℓ') (Woset ℓ ℓ') (ℓ-max ℓ ℓ')
A ≤ B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] isSimulation A B f

-- Necessary intermediary steps to prove that simulations form a poset
private
  isRefl≤ : BinaryRelation.isRefl {A = Woset ℓ ℓ'} _≤_
  isRefl≤ A = (idfun ⟨ A ⟩) , ((λ _ _ a≺ᵣa' → a≺ᵣa')
                            , λ a b b≺ₛfa → (b , b≺ₛfa) , refl)

  isSimulation-∘ : (A B C : Woset ℓ ℓ') → ∀ f g
                 → isSimulation A B f
                 → isSimulation B C g
                 → isSimulation A C (g ∘ f)
  isSimulation-∘ A B C f g (rreff , fibf) (rrefg , fibg)
    = (λ a a' a≺ᵣa' → rrefg (f a) (f a') (rreff a a' a≺ᵣa'))
    , λ a c c≺ₜgfa → ((fibf a (fibg (f a) c c≺ₜgfa .fst .fst)
                              (fibg (f a) c c≺ₜgfa .fst .snd) .fst .fst)
                     , fibf a (fibg (f a) c c≺ₜgfa .fst .fst)
                              (fibg (f a) c c≺ₜgfa .fst .snd) .fst .snd)
                     , cong g (fibf a (fibg (f a) c c≺ₜgfa .fst .fst)
                              (fibg (f a) c c≺ₜgfa .fst .snd) .snd)
                     ∙ fibg (f a) c c≺ₜgfa .snd

  isTrans≤ : BinaryRelation.isTrans {A = Woset ℓ ℓ'} _≤_
  isTrans≤ A B C (f , simf) (g , simg)
    = (g ∘ f) , (isSimulation-∘ A B C f g simf simg)

  isSimulationRespectsId : (A : Type ℓ) (_<_ _≺_ : Rel A A ℓ')
                         → (wosR : IsWoset _<_) (wosS : IsWoset _≺_)
                         → isSimulation (woset A _<_ wosR)
                                        (woset A _≺_ wosS) (idfun A)
                         → isSimulation (woset A _≺_ wosS)
                                        (woset A _<_ wosR) (idfun A)
                         → _<_ ≡ _≺_
  isSimulationRespectsId A _<_ _≺_ wosR wosS (rrefl< , _) (rrefl≺ , _)
    = funExt λ a → funExt λ b
    → isoToPath (isProp→Iso (IsWoset.is-prop-valued wosR a b)
                            (IsWoset.is-prop-valued wosS a b)
                            (λ a<b → rrefl< a b a<b)
                            λ a≺b → rrefl≺ a b a≺b)

  isPropValued≤ : BinaryRelation.isPropValued {A = Woset ℓ ℓ'} _≤_
  isPropValued≤ A B (f , (rreff , fibf)) (g , (rrefg , fibg))
    = Σ≡Prop (λ _ → isPropIsSimulation A B _)
             (funExt (WFI.induction wellR λ a ind
                     → isWeaklyExtensional→≺Equiv→≡ _≺ₛ_ weakS (f a) (g a) λ b
                       → propBiimpl→Equiv (propS b (f a)) (propS b (g a))
                         (λ b≺ₛfa → subst (_≺ₛ g a)
                            (sym (sym (fibf a b b≺ₛfa .snd)
                              ∙ ind (fibf a b b≺ₛfa .fst .fst)
                                    (fibf a b b≺ₛfa .fst .snd)))
                            (rrefg (fibf a b b≺ₛfa .fst .fst) a
                                   (fibf a b b≺ₛfa .fst .snd)))
                            λ b≺ₛga → subst (_≺ₛ f a)
                            (ind (fibg a b b≺ₛga .fst .fst)
                                 (fibg a b b≺ₛga .fst .snd)
                                 ∙ fibg a b b≺ₛga .snd)
                            (rreff (fibg a b b≺ₛga .fst .fst) a
                                   (fibg a b b≺ₛga .fst .snd))))
    where _≺ᵣ_ = WosetStr._≺_ (str A)
          _≺ₛ_ = WosetStr._≺_ (str B)

          wosR = WosetStr.isWoset (str A)
          wosS = WosetStr.isWoset (str B)

          wellR = IsWoset.is-well-founded wosR

          weakS = IsWoset.is-weakly-extensional wosS

          propS = IsWoset.is-prop-valued wosS

  isAntisym≤ : BinaryRelation.isAntisym {A = Woset ℓ ℓ'} _≤_
  isAntisym≤ A B (f , simf) (g , simg) = WosetPath A B .fst (isoToEquiv is
    , (makeIsWosetEquiv (isoToEquiv is)
                        (fst simf)
                        (fst simg)))
    where is : Iso ⟨ A ⟩ ⟨ B ⟩
          Iso.fun is = f
          Iso.inv is = g
          Iso.rightInv is b i
            = cong (_$_ ∘ fst)
              (isPropValued≤ B B (isTrans≤ B A B (g , simg) (f , simf))
                (isRefl≤ B)) i b
          Iso.leftInv is a i
            = cong (_$_ ∘ fst)
              (isPropValued≤ A A (isTrans≤ A B A (f , simf) (g , simg))
                (isRefl≤ A)) i a

isPoset≤ : IsPoset {A = Woset ℓ ℓ'} _≤_
isPoset≤ = isposet
           isSetWoset
           isPropValued≤
           isRefl≤
           isTrans≤
           isAntisym≤

_↓_ : (A : Woset ℓ ℓ') → (a : ⟨ A ⟩ ) → Woset (ℓ-max ℓ ℓ') ℓ'
A ↓ a = (Σ[ b ∈ ⟨ A ⟩ ] b ≺ a)
      , wosetstr _≺ᵢ_ (iswoset
        setᵢ
        propᵢ
        (λ (x , x≺a)
        → WFI.induction well {P = λ x' → (x'≺a : x' ≺ a)
                                       → Acc _≺ᵢ_ (x' , x'≺a)}
            (λ _ ind _ → acc (λ (y , y≺a) y≺x'
                       → ind y y≺x' y≺a)) x x≺a)
        (≺Equiv→≡→isWeaklyExtensional _≺ᵢ_ setᵢ propᵢ
          (λ (x , x≺a) (y , y≺a) f
           → Σ≡Prop (λ b → prop b a)
             (isWeaklyExtensional→≺Equiv→≡ _≺_ weak x y
              λ c → propBiimpl→Equiv (prop c x) (prop c y)
               (λ c≺x → f (c , trans c x a c≺x x≺a) .fst c≺x)
                λ c≺y → f (c , trans c y a c≺y y≺a) .snd c≺y)))
         λ (x , _) (y , _) (z , _) x≺y y≺z → trans x y z x≺y y≺z)
  where _≺_ = WosetStr._≺_ (str A)
        wos = WosetStr.isWoset (str A)
        set = IsWoset.is-set wos
        prop = IsWoset.is-prop-valued wos
        well = IsWoset.is-well-founded wos
        weak = IsWoset.is-weakly-extensional wos
        trans = IsWoset.is-trans wos

        _≺ᵢ_ = BinaryRelation.InducedRelation _≺_
               ((Σ[ b ∈ ⟨ A ⟩ ] b ≺ a)
               , EmbeddingΣProp λ b → prop b a)
        setᵢ = isSetΣ set (λ b → isProp→isSet (prop b a))
        propᵢ = λ (x , _) (y , _) → prop x y
