{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Woset.Simulation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.HITs.SetQuotients

open import Cubical.Induction.WellFounded

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Order.Woset.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Extensionality

private
  variable
    ℓ ℓ' : Level

isSimulation : (A B : Woset ℓ ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isSimulation A B f = monotone × lifting
  where _≺ᵣ_ = WosetStr._≺_ (str A)
        _≺ₛ_ = WosetStr._≺_ (str B)

        monotone = ∀ a a' → a ≺ᵣ a' → (f a) ≺ₛ (f a')

        less : ∀ a → Type _
        less a = Σ[ a' ∈ ⟨ A ⟩ ] a' ≺ᵣ a

        lifting = ∀ a b → b ≺ₛ (f a) → fiber {A = less a} (f ∘ fst) b

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

_≼_ : Rel (Woset ℓ ℓ') (Woset ℓ ℓ') (ℓ-max ℓ ℓ')
A ≼ B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] isSimulation A B f

-- Necessary intermediary steps to prove that simulations form a poset
private
  isRefl≼ : BinaryRelation.isRefl {A = Woset ℓ ℓ'} _≼_
  isRefl≼ A = (idfun ⟨ A ⟩) , ((λ _ _ a≺ᵣa' → a≺ᵣa')
                            , λ _ b b≺ₛfa → (b , b≺ₛfa) , refl)

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

  isTrans≼ : BinaryRelation.isTrans {A = Woset ℓ ℓ'} _≼_
  isTrans≼ A B C (f , simf) (g , simg)
    = (g ∘ f) , (isSimulation-∘ A B C f g simf simg)

  isPropValued≼ : BinaryRelation.isPropValued {A = Woset ℓ ℓ'} _≼_
  isPropValued≼ A B (f , (rreff , fibf)) (g , (rrefg , fibg))
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

  isAntisym≼ : BinaryRelation.isAntisym {A = Woset ℓ ℓ'} _≼_
  isAntisym≼ A B (f , simf) (g , simg) = WosetPath A B .fst (isoToEquiv is
    , (makeIsWosetEquiv (isoToEquiv is)
                        (fst simf)
                        (fst simg)))
    where is : Iso ⟨ A ⟩ ⟨ B ⟩
          Iso.fun is = f
          Iso.inv is = g
          Iso.rightInv is b i
            = cong (_$_ ∘ fst)
              (isPropValued≼ B B (isTrans≼ B A B (g , simg) (f , simf))
                (isRefl≼ B)) i b
          Iso.leftInv is a i
            = cong (_$_ ∘ fst)
              (isPropValued≼ A A (isTrans≼ A B A (f , simf) (g , simg))
                (isRefl≼ A)) i a

isPoset≼ : IsPoset {A = Woset ℓ ℓ'} _≼_
isPoset≼ = isposet
           isSetWoset
           isPropValued≼
           isRefl≼
           isTrans≼
           isAntisym≼

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
        (≺×→≡→isWeaklyExtensional _≺ᵢ_ setᵢ propᵢ
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

isEmbedding↓ : (A : Woset ℓ ℓ') → isEmbedding (A ↓_)
isEmbedding↓ A = injEmbedding isSetWoset (unique _ _)
  where _≺_ = WosetStr._≺_ (str A)
        wos = WosetStr.isWoset (str A)
        prop = IsWoset.is-prop-valued wos
        well = IsWoset.is-well-founded wos
        weak = IsWoset.is-weakly-extensional wos
        trans = IsWoset.is-trans wos

        unique : ∀ a b → (A ↓ a) ≡ (A ↓ b) → a ≡ b
        unique a b p = isWeaklyExtensional→≺Equiv→≡ _≺_ weak a b λ c
          → propBiimpl→Equiv (prop c a) (prop c b)
            (λ c≺a → subst (_≺ b) (sym (to≡ c c≺a)) (snd (to (c , c≺a))))
            λ c≺b → subst (_≺ a) (sym (inv≡ c c≺b)) (snd (inv (c , c≺b)))
          where weq = invEq (WosetPath (A ↓ a) (A ↓ b)) p
                to = equivFun (fst weq)
                inv = invEq (fst weq)

                pres≺ = IsWosetEquiv.pres≺ (snd weq)
                pres≺⁻ = IsWosetEquiv.pres≺⁻ (snd weq)

                to≡ : ∀ c → (c≺a : c ≺ a) → c ≡ fst (to (c , c≺a))
                to≡ = WFI.induction well λ a' ind a'≺a
                  → isWeaklyExtensional→≺Equiv→≡ _≺_ weak
                    a' _ λ c
                    → propBiimpl→Equiv (prop c a') (prop c _)
                    (λ c≺a' → subst (_≺ fst (to (a' , a'≺a)))
                      (sym (ind c c≺a' (trans c a' a c≺a' a'≺a)))
                      (equivFun (pres≺ (c , trans c a' a c≺a' a'≺a)
                                        (a' , a'≺a)) c≺a'))
                     λ c≺toa' → subst (_≺ a') (ind (fst (inv (c , c≺b c≺toa')))
                       (subst (fst (inv (c , c≺b c≺toa')) ≺_) (invtoa'≡a' a'≺a)
                       (equivFun (pres≺⁻ (c , c≺b c≺toa') (to (a' , a'≺a))) c≺toa'))
                       (snd (inv (c , c≺b c≺toa'))) ∙ invc≡toinvc (c≺b c≺toa'))
                       (subst (fst (inv (c , c≺b c≺toa')) ≺_) (invtoa'≡a' a'≺a)
                       (equivFun (pres≺⁻ (c , (c≺b c≺toa')) (to (a' , a'≺a))) c≺toa'))
                  where c≺b : ∀ {c a'}
                               → {a'≺a : a' ≺ a}
                               → c ≺ fst (to (a' , a'≺a))
                               → c ≺ b
                        c≺b {c} {a'} {a'≺a} c≺toa'
                          = trans c _ b c≺toa' (snd (to (a' , a'≺a)))

                        invtoa'≡a' : ∀ {a'}
                                   → (a'≺a : a' ≺ a)
                                   → fst (inv (to (a' , a'≺a))) ≡ a'
                        invtoa'≡a' {a'} a'≺a
                          = fst (PathPΣ (retEq (fst weq) (a' , a'≺a)))

                        invc≡toinvc : ∀ {c}
                                     → (c≺b : c ≺ b)
                                     → fst (to (inv (c , c≺b))) ≡ c
                        invc≡toinvc {c} c≺b
                          = fst (PathPΣ (secEq (fst weq) (c , c≺b)))

                inv≡ : ∀ c → (c≺b : c ≺ b) → c ≡ fst (inv (c , c≺b))
                inv≡ = WFI.induction well λ b' ind b'≺b
                  → isWeaklyExtensional→≺Equiv→≡ _≺_ weak
                    b' _ λ c
                    → propBiimpl→Equiv (prop c b') (prop c _)
                    (λ c≺b' → subst (_≺ fst (inv (b' , b'≺b)))
                      (sym (ind c c≺b' (trans c b' b c≺b' b'≺b)))
                      (equivFun (pres≺⁻ (c , trans c b' b c≺b' b'≺b)
                                         (b' , b'≺b)) c≺b'))
                     λ c≺invb' → subst (_≺ b') (ind (fst (to (c , c≺a c≺invb')))
                       (subst (fst (to (c , c≺a c≺invb')) ≺_) (toinvb'≡b' b'≺b)
                       (equivFun (pres≺ (c , c≺a c≺invb') (inv (b' , b'≺b))) c≺invb'))
                       (snd (to (c , c≺a c≺invb'))) ∙ toc≡invtoc (c≺a c≺invb'))
                       (subst (fst (to (c , c≺a c≺invb')) ≺_) (toinvb'≡b' b'≺b)
                       (equivFun (pres≺ (c , (c≺a c≺invb')) (inv (b' , b'≺b))) c≺invb'))
                  where c≺a : ∀ {c b'}
                               → {b'≺b : b' ≺ b}
                               → c ≺ fst (inv (b' , b'≺b))
                               → c ≺ a
                        c≺a {c} {b'} {b'≺b} c≺invb'
                          = trans c _ a c≺invb' (snd (inv (b' , b'≺b)))

                        toinvb'≡b' : ∀ {b'}
                                   → (b'≺b : b' ≺ b)
                                   → fst (to (inv (b' , b'≺b))) ≡ b'
                        toinvb'≡b' {b'} b'≺b
                          = fst (PathPΣ (secEq (fst weq) (b' , b'≺b)))

                        toc≡invtoc : ∀ {c}
                                     → (c≺a : c ≺ a)
                                     → fst (inv (to (c , c≺a))) ≡ c
                        toc≡invtoc {c} c≺a
                          = fst (PathPΣ (retEq (fst weq) (c , c≺a)))

↓Absorb : (A : Woset ℓ ℓ') → ∀ a b
        → (b≺a : WosetStr._≺_ (str A) b a)
        → (A ↓ a) ↓ (b , b≺a) ≡ A ↓ b
↓Absorb A a b b≺a = isAntisym≼ _ _ (f , simf) (g , simg)
  where _≺_ = WosetStr._≺_ (str A)
        wos = WosetStr.isWoset (str A)
        prop = IsWoset.is-prop-valued wos
        trans = IsWoset.is-trans wos

        f : ⟨ (A ↓ a) ↓ (b , b≺a) ⟩ → ⟨ A ↓ b ⟩
        f ((c , c≺a) , c≺b) = (c , c≺b)

        simf : isSimulation ((A ↓ a) ↓ (b , b≺a)) (A ↓ b) f
        simf = (λ _ _ p → p)
          , λ ((a' , a'≺a) , a'≺b) (b' , b'≺b) b'≺fa
          → (((b' , trans b' b a b'≺b b≺a) , b'≺b) , b'≺fa) , refl

        g : ⟨ A ↓ b ⟩ → ⟨ (A ↓ a) ↓ (b , b≺a) ⟩
        g (c , c≺b) = ((c , trans c b a c≺b b≺a) , c≺b)

        simg : isSimulation (A ↓ b) ((A ↓ a) ↓ (b , b≺a)) g
        simg = (λ _ _ p → p)
          , λ (a' , a'≺b) ((b' , b'≺a) , b'≺b) b'≺ga
          → ((b' , b'≺b) , b'≺ga)
          , Σ≡Prop (λ _ → prop _ _)
           (Σ≡Prop (λ _ → prop _ _) refl)

_≺_ : Rel (Woset ℓ ℓ) (Woset ℓ ℓ) (ℓ-suc ℓ)
A ≺ B = fiber (B ↓_) A

-- To avoid having this wind up in a higher universe, we define the same with equivalences
_≺'_ : Rel (Woset ℓ ℓ) (Woset ℓ ℓ) ℓ
A ≺' B = Σ[ b ∈ ⟨ B ⟩ ] WosetEquiv (B ↓ b) A

≺≃≺' : (A B : Woset ℓ ℓ) → A ≺ B ≃ A ≺' B
≺≃≺' A B = invEquiv (Σ-cong-equiv (idEquiv ⟨ B ⟩) λ b → WosetPath (B ↓ b) A)

↓Decreasing : (A : Woset ℓ ℓ) → ∀ a
            → (A ↓ a) ≺ A
↓Decreasing A a = a , refl

↓Respects≺ : (A : Woset ℓ ℓ) → ∀ a b
           → WosetStr._≺_ (str A) a b
           → (A ↓ a) ≺ (A ↓ b)
↓Respects≺ A a b a≺b = (a , a≺b) , (↓Absorb A b a a≺b)

↓Respects≺⁻ : (A : Woset ℓ ℓ) → ∀ a b
            → (A ↓ a) ≺ (A ↓ b)
            → WosetStr._≺_ (str A) a b
↓Respects≺⁻ A a b ((c , c≺b) , A↓b↓c≡A↓a)
  = subst (_≺ᵣ b) (isEmbedding→Inj (isEmbedding↓ A) c a
          (sym (↓Absorb A b c c≺b) ∙ A↓b↓c≡A↓a)) c≺b
  where _≺ᵣ_ = WosetStr._≺_ (str A)

≺Absorb↓ : (A B : Woset ℓ ℓ)
         → Σ[ b ∈ ⟨ B ⟩ ] A ≺ (B ↓ b)
         → A ≺ B
≺Absorb↓ A B (b , (b' , b'≺b) , B↓b↓b'≡A) = b'
         , sym (↓Absorb B b b' b'≺b) ∙ B↓b↓b'≡A

-- Necessary intermediates to show that _<_ is well-ordered
private
  isPropValued≺ : BinaryRelation.isPropValued (_≺_ {ℓ = ℓ})
  isPropValued≺ A B = isEmbedding→hasPropFibers (isEmbedding↓ B) A

  isAcc↓ : (A : Woset ℓ ℓ) → ∀ a → Acc _≺_ (A ↓ a)
  isAcc↓ A = WFI.induction well λ a ind → acc (λ B B<A↓a
           → subst (Acc _≺_)
             (sym (↓Absorb A a (B<A↓a .fst .fst) (B<A↓a .fst .snd))
             ∙ B<A↓a .snd) (ind (B<A↓a .fst .fst) (B<A↓a .fst .snd)))
    where _≺ᵣ_ = WosetStr._≺_ (str A)
          wos = WosetStr.isWoset (str A)
          well = IsWoset.is-well-founded wos

  isWellFounded≺ : WellFounded (_≺_ {ℓ = ℓ})
  isWellFounded≺ A = acc (λ B B<A → subst (Acc _≺_) (B<A .snd) (isAcc↓ A (B<A .fst)))

  isTrans≺ : BinaryRelation.isTrans (_≺_ {ℓ = ℓ})
  isTrans≺ A _ C A<B (c , C↓c≡B) = ≺Absorb↓ A C (c , (subst (A ≺_) (sym C↓c≡B) A<B))

  isWeaklyExtensional≺ : isWeaklyExtensional (_≺_ {ℓ = ℓ})
  isWeaklyExtensional≺
    = ≺Equiv→≡→isWeaklyExtensional _≺_ isSetWoset isPropValued≺ λ A B ex
    → path A B ex
      where path : (A B : Woset ℓ ℓ)
                 → (∀ C → (C ≺ A) ≃ (C ≺ B))
                 → A ≡ B
            path A B ex = equivFun (WosetPath A B)
                 (isoToEquiv (is A B ex)
               , (makeIsWosetEquiv (isoToEquiv (is A B ex))
                 (λ a a' a≺a' → ↓Respects≺⁻ B _ _
                   (subst2 _≺_
                     (sym (equivFun (ex (A ↓ a)) (↓Decreasing A a) .snd))
                     (sym (equivFun (ex (A ↓ a')) (↓Decreasing A a') .snd))
                     (↓Respects≺ A a a' a≺a')))
                 λ b b' b≺b' → ↓Respects≺⁻ A _ _
                   (subst2 _≺_
                     (sym (invEq (ex (B ↓ b)) (↓Decreasing B b) .snd))
                     (sym (invEq (ex (B ↓ b')) (↓Decreasing B b') .snd))
                     (↓Respects≺ B b b' b≺b'))))
              where is : (A B : Woset ℓ ℓ)
                       → (∀ C → (C ≺ A) ≃ (C ≺ B))
                       → Iso ⟨ A ⟩ ⟨ B ⟩
                    Iso.fun (is A B ex) a = equivFun (ex (A ↓ a))
                                            (↓Decreasing A a) .fst
                    Iso.inv (is A B ex) b = invEq (ex (B ↓ b))
                                            (↓Decreasing B b) .fst
                    Iso.rightInv (is A B ex) p = isEmbedding→Inj
                                 (isEmbedding↓ B) _ p
                                 (equivFun (ex (A ↓ _)) (↓Decreasing A _) .snd
                                 ∙ invEq (ex (B ↓ p)) (↓Decreasing B p) .snd)
                    Iso.leftInv (is A B ex) p  = isEmbedding→Inj
                                (isEmbedding↓ A) _ p
                                (invEq (ex (B ↓ _)) (↓Decreasing B _) .snd
                                ∙ equivFun (ex (A ↓ p)) (↓Decreasing A p) .snd)

isWoset≺ : IsWoset (_≺_ {ℓ = ℓ})
isWoset≺ = iswoset
           isSetWoset
           isPropValued≺
           isWellFounded≺
           isWeaklyExtensional≺
           isTrans≺

{- With all of the above handled, we now need the notion of suprema.
   For that, though, we will expand upon the direction taken in
   lemma 10.3.22 of the HoTT book by Tom de Jong in
   https://www.cs.bham.ac.uk/~mhe/agda/Ordinals.OrdinalOfOrdinalsSuprema.html#2612
-}

private
  module _
    { I : Type ℓ }
    ( F : I → Woset ℓ ℓ)
    where

    ΣF : Type ℓ
    ΣF = Σ[ i ∈ I ] ⟨ F i ⟩

    _≈_ : ΣF → ΣF → Type (ℓ-suc ℓ)
    (i , x) ≈ (j , y) = (F i ↓ x) ≡ (F j ↓ y)

    _<_ : ΣF → ΣF → Type (ℓ-suc ℓ)
    (i , x) < (j , y) = (F i ↓ x) ≺ (F j ↓ y)

    isPropValued< : BinaryRelation.isPropValued _<_
    isPropValued< (i , x) (j , y) = isPropValued≺ (F i ↓ x) (F j ↓ y)

    isTrans< : BinaryRelation.isTrans _<_
    isTrans< (i , x) (j , y) (k , z)
      = isTrans≺ (F i ↓ x) (F j ↓ y) (F k ↓ z)

    isWellFounded< : WellFounded _<_
    isWellFounded< (i , x) = WFI.induction isWellFounded≺
      {P = λ a → ((i , x) : ΣF) → (a ≡ F i ↓ x) → Acc _<_ (i , x)}
      (λ a ind (i' , x') a≡Fi'↓x' → acc (λ (j , y) y'≺x'
       → ind (F j ↓ y) (subst (_ ≺_) (sym a≡Fi'↓x') y'≺x') (j , y) refl))
      (F i ↓ x) (i , x) refl

    -- We get weak extensionality up to ≈
    isWeaklyExtensionalUpTo≈< : (α β : ΣF)
                               → (∀ γ → (γ < α → γ < β) × (γ < β → γ < α))
                               → α ≈ β
    isWeaklyExtensionalUpTo≈< (i , x) (j , y) ex
      = isWeaklyExtensional→≺Equiv→≡ _≺_ isWeaklyExtensional≺
        (F i ↓ x) (F j ↓ y) λ z
        → propBiimpl→Equiv (isPropValued≺ z (F i ↓ x))
                           (isPropValued≺ z (F j ↓ y))
          (λ ((x' , x'≺x) , p) → subst (_≺ (F j ↓ y))
                               (sym (↓Absorb (F i) x x' x'≺x) ∙ p)
                               (ex (i , x') .fst ((x' , x'≺x)
                                 , ↓Absorb (F i) x x' x'≺x)))
          λ ((y' , y'≺y) , q) → subst (_≺ (F i ↓ x))
                              (sym (↓Absorb (F j) y y' y'≺y) ∙ q)
                                (ex (j , y') .snd ((y' , y'≺y)
                                  , ↓Absorb (F j) y y' y'≺y))

  {- Given the above, it seems apparent that this will properly be an ordinal
     under the set quotient. Before that, we want to show this will be
     the supremum.
  -}

    ι : (i : I) → ⟨ F i ⟩ → ΣF
    ι i x = (i , x)
