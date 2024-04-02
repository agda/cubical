{-# OPTIONS --safe #-}
{-
  This treatment of well-orderings follows chapter 10.3 of the HoTT book
-}
module Cubical.Relation.Binary.Order.Woset.Simulation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.HITs.PropositionalTruncation as ∥₁
open import Cubical.HITs.SetQuotients as /₂

open import Cubical.Induction.WellFounded

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Order.Woset.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Extensionality
open import Cubical.Relation.Binary.Order.Properties

private
  variable
    ℓ ℓ' ℓa ℓa' ℓb ℓb' ℓc ℓc' ℓd ℓd' : Level

-- We start with the presumption that the lifting property for a simulation
-- must be truncated, but will prove subsequently that simulations are embeddings
-- and that no truncation is needed
isSimulation∃ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') (f : ⟨ A ⟩ → ⟨ B ⟩)
              → Type (ℓ-max (ℓ-max (ℓ-max ℓa ℓa') ℓb) ℓb')
isSimulation∃ A B f = monotone × ∃lifting
  where _≺ᵣ_ = WosetStr._≺_ (str A)
        _≺ₛ_ = WosetStr._≺_ (str B)

        monotone = ∀ a a' → a ≺ᵣ a' → (f a) ≺ₛ (f a')

        less : ∀ a → Type _
        less a = Σ[ a' ∈ ⟨ A ⟩ ] a' ≺ᵣ a

        ∃lifting = ∀ a b → b ≺ₛ (f a) → ∃[ (a' , _) ∈ less a ] f a' ≡ b

isSimulation∃→isEmbedding : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') → ∀ f
                          → isSimulation∃ A B f → isEmbedding f
isSimulation∃→isEmbedding A B f (rrel , efib)
  = injEmbedding setB
    λ {a b} → WFI.induction wellR {P = λ a' → ∀ b' → f a' ≡ f b' → a' ≡ b'}
              (λ a' ind b' fa'≡fb'
                 → isWeaklyExtensional→≺Equiv→≡ _≺ᵣ_ weakR a' b'
                   λ c → propBiimpl→Equiv (propR c a') (propR c b')
                     (λ c≺ᵣa' → ∥₁.rec (propR c b')
                                       (λ ((a'' , fa''≺ᵣb') , fc≡fa'')
                                       → subst (_≺ᵣ b') (sym
                                               (ind c c≺ᵣa' a'' (sym fc≡fa'')))
                                         fa''≺ᵣb')
                                  (efib b' (f c) (subst (f c ≺ₛ_) fa'≡fb'
                                                        (rrel c a' c≺ᵣa'))))
                     λ c≺ᵣb' → ∥₁.rec (propR c a')
                                      (λ ((b'' , fb''≺ᵣa') , fc≡fb'')
                                      → subst (_≺ᵣ a')
                                              (ind b'' fb''≺ᵣa' c
                                                fc≡fb'') fb''≺ᵣa')
                                 (efib a' (f c) (subst (f c ≺ₛ_)
                                       (sym fa'≡fb') (rrel c b' c≺ᵣb')))) a b
    where _≺ᵣ_ = WosetStr._≺_ (str A)
          _≺ₛ_ = WosetStr._≺_ (str B)

          wosR = WosetStr.isWoset (str A)
          wosS = WosetStr.isWoset (str B)

          setB = IsWoset.is-set wosS

          wellR = IsWoset.is-well-founded wosR
          weakR = IsWoset.is-weakly-extensional wosR
          propR = IsWoset.is-prop-valued wosR

-- With the fact that it's an embedding, we can do away with the truncation
isSimulation : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') (f : ⟨ A ⟩ → ⟨ B ⟩)
             → Type (ℓ-max (ℓ-max (ℓ-max ℓa ℓa') ℓb) ℓb')
isSimulation A B f = monotone × lifting
  where _≺ᵣ_ = WosetStr._≺_ (str A)
        _≺ₛ_ = WosetStr._≺_ (str B)

        monotone = ∀ a a' → a ≺ᵣ a' → (f a) ≺ₛ (f a')

        less : ∀ a → Type _
        less a = Σ[ a' ∈ ⟨ A ⟩ ] a' ≺ᵣ a

        lifting = ∀ a b → b ≺ₛ (f a) → fiber {A = less a} (f ∘ fst) b

isSimulation∃→isSimulation : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') → ∀ f
                           → isSimulation∃ A B f → isSimulation A B f
isSimulation∃→isSimulation A B f (mono , lifting) = mono
                           , (λ a b b≺fa → ∥₁.rec
                           (isEmbedding→hasPropFibers (isEmbedding-∘
                             (isSimulation∃→isEmbedding A B f (mono , lifting))
                             (λ _ _ → isEmbeddingFstΣProp λ _ → propR _ _)) b)
                             (λ x → x) (lifting a b b≺fa))
                           where propR = IsWoset.is-prop-valued (WosetStr.isWoset (str A))

isSimulation→isEmbedding : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') → ∀ f
                         → isSimulation A B f → isEmbedding f
isSimulation→isEmbedding A B f (rrel , efib)
  = injEmbedding setB
    λ {a b} → WFI.induction wellR {P = λ a' → ∀ b' → f a' ≡ f b' → a' ≡ b'}
            (λ a' ind b' fa'≡fb' → isWeaklyExtensional→≺Equiv→≡
               _≺ᵣ_ weakR a' b' λ c → propBiimpl→Equiv
                 (propR c a') (propR c b')
                 (λ c≺ᵣa' → subst (_≺ᵣ b')
                            (sym (ind c c≺ᵣa'
                                 (efib b' (f c)
                                   (subst (f c ≺ₛ_) fa'≡fb'
                                          (rrel c a' c≺ᵣa')) .fst .fst)
                                 (sym (efib b' (f c) (subst (f c ≺ₛ_)
                                      fa'≡fb' (rrel c a' c≺ᵣa')) .snd))))
                            (efib b' (f c) (subst (f c ≺ₛ_) fa'≡fb'
                                             (rrel c a' c≺ᵣa')) .fst .snd))
                  λ c≺ᵣb' → subst (_≺ᵣ a')
                            (ind (efib a' (f c) (subst (f c ≺ₛ_)
                              (sym fa'≡fb') (rrel c b' c≺ᵣb')) .fst .fst)
                                (efib a' (f c) (subst (f c ≺ₛ_)
                                  (sym fa'≡fb') (rrel c b' c≺ᵣb')) .fst .snd)
                                c (efib a' (f c) (subst (f c ≺ₛ_)
                                  (sym fa'≡fb') (rrel c b' c≺ᵣb')) .snd))
                              (efib a' (f c) (subst (f c ≺ₛ_)
                                (sym fa'≡fb') (rrel c b' c≺ᵣb')) .fst .snd)) a b
    where _≺ᵣ_ = WosetStr._≺_ (str A)
          _≺ₛ_ = WosetStr._≺_ (str B)

          wosR = WosetStr.isWoset (str A)
          wosS = WosetStr.isWoset (str B)

          setB = IsWoset.is-set wosS

          wellR = IsWoset.is-well-founded wosR
          weakR = IsWoset.is-weakly-extensional wosR
          propR = IsWoset.is-prop-valued wosR

isSimulationUnique : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb')
                   → ∀ f g → isSimulation A B f → isSimulation A B g
                   → f ≡ g
isSimulationUnique A B f g (rreff , fibf) (rrefg , fibg) =
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
  where _≺ₛ_ = WosetStr._≺_ (str B)

        wosR = WosetStr.isWoset (str A)
        wosS = WosetStr.isWoset (str B)

        wellR = IsWoset.is-well-founded wosR

        weakS = IsWoset.is-weakly-extensional wosS

        propS = IsWoset.is-prop-valued wosS

isPropIsSimulation : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb')
                   → ∀ f → isProp (isSimulation A B f)
isPropIsSimulation A B f sim₀
  = isProp× (isPropΠ3 λ _ _ _ → propS _ _)
            (isPropΠ3 (λ _ b _ → isEmbedding→hasPropFibers
                                 (isEmbedding-∘
                                 (isSimulation→isEmbedding A B f sim₀)
                                 λ _ _ → isEmbeddingFstΣProp
                                         λ _ → propR _ _) b)) sim₀
  where propR = IsWoset.is-prop-valued (WosetStr.isWoset (str A))
        propS = IsWoset.is-prop-valued (WosetStr.isWoset (str B))

_≼_ : Rel (Woset ℓa ℓa') (Woset ℓb ℓb') (ℓ-max (ℓ-max (ℓ-max ℓa ℓa') ℓb) ℓb')
A ≼ B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] isSimulation A B f

-- Necessary intermediary steps to prove that simulations form a poset
isRefl≼ : BinaryRelation.isRefl {A = Woset ℓ ℓ'} _≼_
isRefl≼ A = (idfun ⟨ A ⟩) , ((λ _ _ a≺ᵣa' → a≺ᵣa')
                          , λ _ b b≺ₛfa → (b , b≺ₛfa) , refl)

isSimulation-∘ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') (C : Woset ℓc ℓc')
               → ∀ f g
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

isTrans≼ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') (C : Woset ℓc ℓc')
         → A ≼ B → B ≼ C → A ≼ C
isTrans≼ A B C (f , simf) (g , simg)
  = (g ∘ f) , (isSimulation-∘ A B C f g simf simg)

isPropValued≼ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') → isProp (A ≼ B)
isPropValued≼ A B (f , simf) (g , simg)
  = Σ≡Prop (λ _ → isPropIsSimulation A B _)
           (isSimulationUnique A B f g simf simg)

isAntisym≼Equiv : (A : Woset ℓa ℓa') (B  : Woset ℓb ℓb')
                → A ≼ B → B ≼ A → WosetEquiv A B
isAntisym≼Equiv A B (f , simf) (g , simg)
  = (isoToEquiv is
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

isAntisym≼ : BinaryRelation.isAntisym {A = Woset ℓ ℓ'} _≼_
isAntisym≼ A B A≼B B≼A = equivFun (WosetPath A B) (isAntisym≼Equiv A B A≼B B≼A)

isPoset≼ : IsPoset {A = Woset ℓ ℓ'} _≼_
isPoset≼ = isposet
           isSetWoset
           isPropValued≼
           isRefl≼
           isTrans≼
           isAntisym≼

isWosetEquiv→isSimulation : {A : Woset ℓa ℓa'} {B : Woset ℓb ℓb'}
                          → ((eq , _) : WosetEquiv A B)
                          → isSimulation A B (equivFun eq)
isWosetEquiv→isSimulation {A = A} (A≃B , wqAB)
                          = ((λ a a' → equivFun (IsWosetEquiv.pres≺ wqAB a a'))
                          , λ a b b≺fa → ((invEq A≃B b)
                          , subst (invEq A≃B b ≺ᵣ_) (retEq A≃B a)
                            (equivFun (IsWosetEquiv.pres≺⁻ wqAB b
                                      (equivFun A≃B a)) b≺fa))
                          , secEq A≃B b)
                          where _≺ᵣ_ = WosetStr._≺_ (str A)

WosetEquiv→≼ : {A : Woset ℓa ℓa'} {B : Woset ℓb ℓb'}
             → WosetEquiv A B
             → A ≼ B
WosetEquiv→≼ (A≃B , wqAB) = (equivFun A≃B) , isWosetEquiv→isSimulation (A≃B , wqAB)

isPropValuedWosetEquiv : {A : Woset ℓa ℓa'} {B : Woset ℓb ℓb'}
                       → (M : WosetEquiv A B)
                       → (N : WosetEquiv A B)
                       → M ≡ N
isPropValuedWosetEquiv {A = A} {B = B} M N
  = Σ≡Prop (λ _ → isPropIsWosetEquiv _ _ _)
    (Σ≡Prop (λ _ → isPropIsEquiv _)
    (isSimulationUnique A B (M .fst .fst) (N .fst .fst)
      (isWosetEquiv→isSimulation M)
      (isWosetEquiv→isSimulation N)))

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

↓AbsorbEquiv : (A : Woset ℓ ℓ') → ∀ a b
             → (b≺a : WosetStr._≺_ (str A) b a)
             → WosetEquiv ((A ↓ a) ↓ (b , b≺a)) (A ↓ b)
↓AbsorbEquiv A a b b≺a = subst (λ x → WosetEquiv ((A ↓ a) ↓ (b , b≺a)) x)
                               (↓Absorb A a b b≺a) reflWosetEquiv

↓Monotone : (A : Woset ℓ ℓ') → ∀ a
          → (A ↓ a) ≼ A
↓Monotone A a = f , sim
  where _≺ᵣ_ = WosetStr._≺_ (str (A ↓ a))
        _≺ₛ_ = WosetStr._≺_ (str A)

        trans = IsWoset.is-trans (WosetStr.isWoset (str A))

        f : ⟨ A ↓ a ⟩ → ⟨ A ⟩
        f (a' , _) = a'

        sim : isSimulation (A ↓ a) A f
        sim = mono , lifting
          where mono : ∀ a' a'' → a' ≺ᵣ a'' → (f a') ≺ₛ (f a'')
                mono _ _ a'≺ᵣa'' = a'≺ᵣa''

                lifting : ∀ a' b → b ≺ₛ (f a')
                        → fiber {A = Σ[ a'' ∈ ⟨ A ↓ a ⟩ ] a'' ≺ᵣ a'} (f ∘ fst) b
                lifting (a' , a'≺ᵣa) b b≺ₛfa'
                  = ((b , trans b a' a b≺ₛfa' a'≺ᵣa) , b≺ₛfa') , refl

-- To avoid having this wind up in a higher universe, we define with an equivalence
_≺_ : Rel (Woset ℓa ℓa') (Woset ℓb ℓb') (ℓ-max (ℓ-max (ℓ-max ℓa ℓa') ℓb) ℓb')
A ≺ B = Σ[ b ∈ ⟨ B ⟩ ] WosetEquiv (B ↓ b) A

↓Decreasing : (A : Woset ℓ ℓ') → ∀ a
             → (A ↓ a) ≺ A
↓Decreasing A a = a , (invEq (WosetPath (A ↓ a) (A ↓ a)) refl)

↓Respects≺ : (A : Woset ℓ ℓ') → ∀ a b
            → WosetStr._≺_ (str A) a b
            → (A ↓ a) ≺ (A ↓ b)
↓Respects≺ A a b a≺b = (a , a≺b) , (invEq (WosetPath _ (A ↓ a)) (↓Absorb A b a a≺b))

↓Respects≺⁻ : (A : Woset ℓ ℓ') → ∀ a b
              → (A ↓ a) ≺ (A ↓ b)
              → WosetStr._≺_ (str A) a b
↓Respects≺⁻ A a b ((c , c≺b) , A↓b↓c≃A↓a)
  = subst (_≺ᵣ b)
      (isEmbedding→Inj (isEmbedding↓ A) c a
       (sym (↓Absorb A b c c≺b) ∙ A↓b↓c≡A↓a))
      c≺b
  where _≺ᵣ_ = WosetStr._≺_ (str A)
        A↓b↓c≡A↓a = equivFun (WosetPath _ (A ↓ a)) A↓b↓c≃A↓a

↓RespectsEquiv : {A : Woset ℓa ℓa'} {B : Woset ℓb ℓb'}
               → (e : WosetEquiv A B)
               → ∀ a → WosetEquiv (A ↓ a) (B ↓ equivFun (fst e) a)
↓RespectsEquiv {A = A} {B = B} e a = eq
               , makeIsWosetEquiv eq
                 (λ (x , _) (y , _) x≺y
                 → equivFun (IsWosetEquiv.pres≺ (snd e) x y) x≺y)
                 λ (x , _) (y , _) x≺y
                 → equivFun (IsWosetEquiv.pres≺⁻ (snd e) x y) x≺y
  where wosA = WosetStr.isWoset (str A)
        wosB = WosetStr.isWoset (str B)

        propA = IsWoset.is-prop-valued wosA
        propB = IsWoset.is-prop-valued wosB

        eq : ⟨ A ↓ a ⟩ ≃ ⟨ B ↓ equivFun (fst e) a ⟩
        eq = Σ-cong-equiv (fst e)
             λ x → propBiimpl→Equiv (propA _ _) (propB _ _)
                   (equivFun (IsWosetEquiv.pres≺ (snd e) x a))
                   (invEq (IsWosetEquiv.pres≺ (snd e) x a))

↓RespectsEquiv⁻ : {A : Woset ℓa ℓa'} {B : Woset ℓb ℓb'}
                → (e : WosetEquiv A B)
                → ∀ b → WosetEquiv (A ↓ invEq (fst e) b) (B ↓ b)
↓RespectsEquiv⁻ {A = A} {B = B} e b = eq
                , makeIsWosetEquiv eq
                  (λ (x , _) (y , _) x≺y
                  → equivFun (IsWosetEquiv.pres≺ (snd e) x y) x≺y)
                  λ (x , _) (y , _) x≺y
                  → equivFun (IsWosetEquiv.pres≺⁻ (snd e) x y) x≺y
  where wosA = WosetStr.isWoset (str A)
        wosB = WosetStr.isWoset (str B)

        propA = IsWoset.is-prop-valued wosA
        propB = IsWoset.is-prop-valued wosB

        eq : ⟨ A ↓ invEq (fst e) b ⟩ ≃ ⟨ B ↓ b ⟩
        eq = invEquiv (Σ-cong-equiv (invEquiv (fst e))
             λ x → propBiimpl→Equiv (propB _ _) (propA _ _)
                   (equivFun (IsWosetEquiv.pres≺⁻ (snd e) x b))
                   (invEq (IsWosetEquiv.pres≺⁻ (snd e) x b)))

≺Absorb↓ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb')
           → Σ[ b ∈ ⟨ B ⟩ ] A ≺ (B ↓ b)
           → A ≺ B
≺Absorb↓ A B (b , (b' , b'≺b) , B↓b↓b'≃A) = b'
          , subst (λ x → WosetEquiv x A) (↓Absorb B b b' b'≺b) B↓b↓b'≃A

≺Weaken≼ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb')
           → A ≺ B
           → A ≼ B
≺Weaken≼ A B (b , B↓b≃A) = isTrans≼ A (B ↓ b) B
  (WosetEquiv→≼ (invWosetEquiv B↓b≃A)) (↓Monotone B b)

≺Trans≼ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') (C : Woset ℓc ℓc')
         → A ≺ B
         → B ≼ C
         → A ≺ C
≺Trans≼ A B C (b , B↓b≃A) (f , (mono , lifting))
  = (f b) , compWosetEquiv eq B↓b≃A
    where _≺ᵣ_ = WosetStr._≺_ (str C)
          _≺ₛ_ = WosetStr._≺_ (str B)

          wosC = WosetStr.isWoset (str C)
          wosB = WosetStr.isWoset (str B)

          propC = IsWoset.is-prop-valued wosC
          propB = IsWoset.is-prop-valued wosB

          transB = IsWoset.is-trans wosB

          eq : WosetEquiv (C ↓ f b) (B ↓ b)
          eq = isAntisym≼Equiv (C ↓ f b) (B ↓ b)
               (fun , simf)
               (inv , simg)
             where fun : ⟨ C ↓ f b ⟩ → ⟨ B ↓ b ⟩
                   fun (c , c≺fb) = lifting b c c≺fb .fst

                   funIdem : ∀ b' → (ineq : ((f b') ≺ᵣ (f b)))
                           → fun (f b' , ineq) .fst ≡ b'
                   funIdem b' fb'≺fb
                     = isEmbedding→Inj (isSimulation→isEmbedding B C f
                                       (mono , lifting)) _ b'
                       (lifting b (f b') fb'≺fb .snd)

                   simf : isSimulation (C ↓ f b) (B ↓ b) fun
                   simf = m
                        , λ (c , c≺fb) (b' , b'≺b) b'≺func
                        → (((f b') , (mono b' b b'≺b))
                        , (subst (f b' ≺ᵣ_) (lifting b c c≺fb .snd)
                          (mono b' (fun (c , c≺fb) .fst) b'≺func)))
                        , Σ≡Prop (λ _ → propB _ _)
                          (funIdem b' (mono b' b b'≺b))
                        where m : ∀ c c' → c .fst ≺ᵣ c' .fst
                                → fun c .fst ≺ₛ fun c' .fst
                              m (c , c≺fb) (c' , c'≺fb) c≺c'
                                = subst (_≺ₛ fun (c' , c'≺fb) .fst)
                                        b'''≡b'
                                        b'''≺b'
                                  where b' = fun (c , c≺fb) .fst
                                        b'' = fun (c' , c'≺fb) .fst

                                        fb'≡c = lifting b c c≺fb .snd
                                        fb''≡c' = lifting b c' c'≺fb .snd

                                        fb'≺fb'' = subst2 (_≺ᵣ_)
                                                   (sym fb'≡c)
                                                   (sym fb''≡c')
                                                   c≺c'

                                        b''' = lifting b'' (f b')
                                                       fb'≺fb'' .fst .fst

                                        b'''≺b' = lifting b'' (f b')
                                                          fb'≺fb'' .fst .snd

                                        fb'''≡fb' = lifting b'' (f b')
                                                            fb'≺fb'' .snd

                                        b'''≡b' = isEmbedding→Inj
                                                  (isSimulation→isEmbedding B C
                                                    f (mono , lifting))
                                                  b''' b' fb'''≡fb'

                   inv : ⟨ B ↓ b ⟩ → ⟨ C ↓ f b ⟩
                   inv (b' , b'≺b) = (f b') , (mono b' b b'≺b)

                   simg : isSimulation (B ↓ b) (C ↓ f b) inv
                   simg = (λ (b' , _) (b'' , _) b'≺b'' → mono b' b'' b'≺b'')
                           , λ (b' , b'≺b) (c , c≺fb) c≺fb'
                           → (((lifting b' c c≺fb' .fst .fst)
                           , transB _ b' b (lifting b' c c≺fb' .fst .snd) b'≺b)
                           , lifting b' c c≺fb' .fst .snd)
                           , Σ≡Prop (λ _ → propC _ _) (lifting b' c c≺fb' .snd)

≺RespectsEquivL : {A : Woset ℓa ℓa'} {B : Woset ℓb ℓb'} (C : Woset ℓc ℓc')
                 → WosetEquiv A B
                 → A ≺ C
                 → B ≺ C
≺RespectsEquivL _ A≃B (c , C↓c≃A) = c , compWosetEquiv C↓c≃A A≃B

≺RespectsEquivR : (A : Woset ℓa ℓa') {B : Woset ℓb ℓb'} {C : Woset ℓc ℓc'}
                 → WosetEquiv B C
                 → A ≺ B
                 → A ≺ C
≺RespectsEquivR _ B≃C (b , B↓b≃A)
  = (equivFun (B≃C .fst) b)
  , (compWosetEquiv (invWosetEquiv (↓RespectsEquiv B≃C b)) B↓b≃A)

≺RespectsEquiv : {A : Woset ℓa ℓa'} {B : Woset ℓb ℓb'}
                  {C : Woset ℓc ℓc'} {D : Woset ℓd ℓd'}
                → WosetEquiv A C
                → WosetEquiv B D
                → A ≺ B
                → C ≺ D
≺RespectsEquiv {B = B} {C = C} A≃C B≃D A≺'B
  = ≺RespectsEquivR C B≃D (≺RespectsEquivL B A≃C A≺'B)

-- Necessary intermediates to show that _≺_ is well-ordered

isPropValued≺ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb')
               → isProp (A ≺ B)
isPropValued≺ A B (b , p) (b' , q)
  = Σ≡Prop (λ _ → isPropValuedWosetEquiv)
    (isEmbedding→Inj (isEmbedding↓ B) b b'
      (equivFun (WosetPath (B ↓ b) (B ↓ b'))
        (compWosetEquiv p (invWosetEquiv q))))

isWellFounded≺ : WellFounded (_≺_ {ℓa = ℓ} {ℓa' = ℓ})
isWellFounded≺ A = acc (λ B (a , A↓a≃B)
                    → subst (Acc _≺_)
                            (equivFun (WosetPath (A ↓ a) B) A↓a≃B)
                            (isAcc↓ A a))
  where isAcc↓ : (A : Woset ℓ ℓ) → ∀ a → Acc _≺_ (A ↓ a)
        isAcc↓ A = WFI.induction well λ a ind
                 → acc (λ B ((a' , a'≺a) , A↓a↓a'≃B)
                 → subst (Acc _≺_)
                   (sym (↓Absorb A a a' a'≺a)
                     ∙ equivFun (WosetPath _ B) A↓a↓a'≃B)
                   (ind a' a'≺a))
          where _≺ᵣ_ = WosetStr._≺_ (str A)
                wos = WosetStr.isWoset (str A)
                well = IsWoset.is-well-founded wos

isTrans≺ : (A : Woset ℓa ℓa') (B : Woset ℓb ℓb') (C : Woset ℓc ℓc')
          → A ≺ B → B ≺ C → A ≺ C
isTrans≺ A B C (b , B↓b≃A) (c , C↓c≃B) = ≺Absorb↓ A C (c , (invEq (fst C↓c≃B) b
                                 , compWosetEquiv (↓RespectsEquiv⁻ C↓c≃B b) B↓b≃A))

isWeaklyExtensional≺ : isWeaklyExtensional (_≺_ {ℓa = ℓ} {ℓa' = ℓ})
isWeaklyExtensional≺
  = ≺Equiv→≡→isWeaklyExtensional _≺_ isSetWoset isPropValued≺
      λ A B ex → path A B ex
  where path : (A B : Woset ℓ ℓ)
             → ((C : Woset ℓ ℓ) → (C ≺ A) ≃ (C ≺ B))
             → A ≡ B
        path A B ex = equivFun (WosetPath A B)
                      (eq , (makeIsWosetEquiv eq
                            (λ a a' a≺a'
                              → ↓Respects≺⁻ B (equivFun eq a) (equivFun eq a')
                                (≺RespectsEquiv
                                  (invWosetEquiv (equivFun (ex (A ↓ a))
                                                 (↓Decreasing A a) .snd))
                                  (invWosetEquiv (equivFun (ex (A ↓ a'))
                                                 (↓Decreasing A a') .snd))
                                  (↓Respects≺ A a a' a≺a')))
                            (λ b b' b≺b'
                              → ↓Respects≺⁻ A (invEq eq b) (invEq eq b')
                                (≺RespectsEquiv
                                   (invWosetEquiv (invEq (ex (B ↓ b))
                                                  (↓Decreasing B b) .snd))
                                   (invWosetEquiv (invEq (ex (B ↓ b'))
                                                  (↓Decreasing B b') .snd))
                                   (↓Respects≺ B b b' b≺b')))))
          where is : Iso ⟨ A ⟩ ⟨ B ⟩
                Iso.fun is a = equivFun (ex (A ↓ a)) (↓Decreasing A a) .fst
                Iso.inv is b = invEq (ex (B ↓ b)) (↓Decreasing B b) .fst
                Iso.rightInv is p = isEmbedding→Inj (isEmbedding↓ B) q p
                                    (equivFun (WosetPath (B ↓ q) (B ↓ p))
                                      (compWosetEquiv
                                        (equivFun (ex (A ↓ (Iso.inv is p)))
                                                  (↓Decreasing A (Iso.inv is p)) .snd)
                                        (invEq (ex (B ↓ p)) (↓Decreasing B p) .snd)))
                                      where q = Iso.fun is (Iso.inv is p)
                Iso.leftInv  is p = isEmbedding→Inj (isEmbedding↓ A) q p
                                    (equivFun (WosetPath (A ↓ q) (A ↓ p))
                                      (compWosetEquiv
                                        (invEq (ex (B ↓ (Iso.fun is p)))
                                               (↓Decreasing B (Iso.fun is p)) .snd)
                                        (equivFun (ex (A ↓ p)) (↓Decreasing A p) .snd)))
                                      where q = Iso.inv is (Iso.fun is p)

                eq : ⟨ A ⟩ ≃ ⟨ B ⟩
                eq = isoToEquiv is

isWoset≺ : IsWoset (_≺_ {ℓa = ℓ} {ℓa' = ℓ})
isWoset≺ = iswoset
           isSetWoset
           isPropValued≺
           isWellFounded≺
           isWeaklyExtensional≺
           isTrans≺

{- With all of the above handled, we now need the notion of suprema.
   For that, though, we will expand upon the direction taken in
   lemma 10.3.22 of the HoTT book by Tom de Jong in
   https://www.cs.bham.ac.uk/~mhe/agda/Ordinals.OrdinalOfOrdinalsSuprema.html
-}

private
  module _
    { I : Type ℓ' }
    ( F : I → Woset ℓ ℓ)
    where

    open BinaryRelation

    ΣF : Type (ℓ-max ℓ ℓ')
    ΣF = Σ[ i ∈ I ] ⟨ F i ⟩

    _≈_ : ΣF → ΣF → Type ℓ
    (i , x) ≈ (j , y) = WosetEquiv (F i ↓ x) (F j ↓ y)

    _<_ : ΣF → ΣF → Type ℓ
    (i , x) < (j , y) = (F i ↓ x) ≺ (F j ↓ y)

    isPropValued< : isPropValued _<_
    isPropValued< (i , x) (j , y) = isPropValued≺ (F i ↓ x) (F j ↓ y)

    isTrans< : isTrans _<_
    isTrans< (i , x) (j , y) (k , z)
      = isTrans≺ (F i ↓ x) (F j ↓ y) (F k ↓ z)

    isWellFounded< : WellFounded _<_
    isWellFounded< (i , x) = WFI.induction isWellFounded≺
      {P = λ a → ((i , x) : ΣF) → (WosetEquiv a (F i ↓ x)) → Acc _<_ (i , x)}
      (λ a ind (i' , x') a≃Fi'↓x' → acc (λ (j , y) y'≺x'
       → ind (F j ↓ y) (≺RespectsEquivR _ (invWosetEquiv a≃Fi'↓x') y'≺x')
             (j , y) (reflWosetEquiv)))
      (F i ↓ x) (i , x) (reflWosetEquiv)

    -- We get weak extensionality up to ≈
    isWeaklyExtensionalUpTo≈< : (α β : ΣF)
                               → (∀ γ → (γ < α → γ < β) × (γ < β → γ < α))
                               → α ≈ β
    isWeaklyExtensionalUpTo≈< (i , x) (j , y) ex
      = invEq (WosetPath _ _)
        (isWeaklyExtensional→≺Equiv→≡ _≺_ isWeaklyExtensional≺
        (F i ↓ x) (F j ↓ y) λ z
        → propBiimpl→Equiv (isPropValued≺ z (F i ↓ x))
                           (isPropValued≺ z (F j ↓ y))
          (λ ((x' , x'≺x) , p) → ≺RespectsEquivL (F j ↓ y)
            (subst (λ x → WosetEquiv x z) (↓Absorb (F i) x x' x'≺x) p)
                   (ex (i , x') .fst ((x' , x'≺x)
            , ↓AbsorbEquiv (F i) x x' x'≺x)))
          λ ((y' , y'≺y) , q) → ≺RespectsEquivL (F i ↓ x)
            (subst (λ x → WosetEquiv x z) (↓Absorb (F j) y y' y'≺y) q)
                   (ex (j , y') .snd ((y' , y'≺y)
            , ↓AbsorbEquiv (F j) y y' y'≺y)))

  {- Given the above, it seems apparent that this will properly be an ordinal
     under the set quotient. Before that, we want to show this will be
     the supremum.
  -}

    ι : (i : I) → ⟨ F i ⟩ → ΣF
    ι i x = (i , x)

    ιPreservesOrder : (i : I) (x y : ⟨ F i ⟩)
                    → WosetStr._≺_ (str (F i)) x y → ι i x < ι i y
    ιPreservesOrder i x y x≺y = ↓Respects≺ (F i) x y x≺y

    ι≈↓ : (i : I) (x : ⟨ F i ⟩) ((j , y) : ΣF)
        → (j , y) < ι i x
        → Σ[ x' ∈ ⟨ F i ⟩ ] WosetStr._≺_ (str (F i)) x' x × ι i x' ≈ (j , y)
    ι≈↓ i x (j , y) ((x' , x'≺x) , e) = x' , x'≺x
        , compWosetEquiv (invWosetEquiv (↓AbsorbEquiv (F (fst (ι i x))) x x' x'≺x)) e

    module _
      (β : Woset ℓ ℓ)
      (upβ : (i : I) → F i ≼ β)
      where

      f : (i : I) → ⟨ F i ⟩ → ⟨ β ⟩
      f i x = upβ i .fst x

      fCommF : (i : I) (x : ⟨ F i ⟩) → F i ↓ x ≡ β ↓ (f i x)
      fCommF i x = sym (equivFun (WosetPath (β ↓ (f i x)) (F i ↓ x))
        (≺Trans≼ (F i ↓ x) (F i) β (↓Decreasing (F i) x) (upβ i) .snd))

      f⃕ : ΣF → ⟨ β ⟩
      f⃕ (i , x) = f i x

      f⃕Respects≈ : {p q : ΣF} → p ≈ q → f⃕ p ≡ f⃕ q
      f⃕Respects≈ {(i , x)} {(j , y)} e
        = isEmbedding→Inj (isEmbedding↓ β) (f⃕ (i , x)) (f⃕ (j , y))
          ((β ↓ f⃕ (i , x)) ≡⟨ sym (fCommF i x) ⟩
           (F i ↓ x)        ≡⟨ equivFun (WosetPath (F i ↓ x) (F j ↓ y)) e ⟩
           (F j ↓ y)        ≡⟨ fCommF j y ⟩
           (β ↓ f⃕ (j , y)) ∎)

      f⃕presβ≺ : (p q : ΣF) → p < q → WosetStr._≺_ (str β) (f⃕ p) (f⃕ q)
      f⃕presβ≺ (i , x) (j , y) p<q = ↓Respects≺⁻ β (f⃕ (i , x)) (f⃕ (j , y))
        (subst2 _≺_ (fCommF i x) (fCommF j y) p<q)

      f⃕InitialSegment : (p : ΣF) (b : ⟨ β ⟩)
                       → WosetStr._≺_ (str β) b (f⃕ p)
                       → fiber {A = Σ[ q ∈ ΣF ] q < p} (f⃕ ∘ fst) b
      f⃕InitialSegment (i , x) b b≺fp  = ((i , x') , u) , v
        where lemma = upβ i .snd .snd

              x' = lemma x b b≺fp .fst .fst
              x'<x = lemma x b b≺fp .fst .snd

              u = ↓Respects≺ (F i) x' x x'<x
              v = lemma x b b≺fp .snd

    -- A quick proof that ≈ is an equivalence relation
    ≋ : isEquivRel _≈_
    isEquivRel.reflexive ≋ = λ _ → reflWosetEquiv
    isEquivRel.symmetric ≋ = λ _ _ → invWosetEquiv
    isEquivRel.transitive ≋ = λ _ _ _ → compWosetEquiv

    -- And now, we forge our quotient type

    F/ : Type (ℓ-max ℓ ℓ')
    F/ = ΣF / _≈_

    _<'_ : ΣF → ΣF → hProp _
    x <' y = (x < y , isPropValued< x y)

    <Congruence : { p q p' q' : ΣF} → p ≈ p' → q ≈ q'
                → p <' q ≡ p' <' q'
    <Congruence {(i , x)} {(j , y)} {(i' , x')} {(j' , y')} eqp eqq
      = Σ≡Prop (λ _ → isPropIsProp)
        (isoToPath (isProp→Iso (isPropValued< _ _) (isPropValued< _ _)
        (λ x<y → ≺RespectsEquiv eqp eqq x<y)
        λ y<x → ≺RespectsEquiv (invWosetEquiv eqp) (invWosetEquiv eqq) y<x))

    _</'_ : F/ → F/ → hProp _
    x </' y = /₂.rec2 isSetHProp _<'_
              (λ _ _ c a≈b → <Congruence a≈b (isEquivRel.reflexive ≋ c))
              (λ a _ _ b≈c → <Congruence (isEquivRel.reflexive ≋ a) b≈c) x y

    _</_ : F/ → F/ → Type ℓ
    x </ y = ⟨ x </' y ⟩

    isPropValued</ : isPropValued _</_
    isPropValued</ x y = str (x </' y)

    isTrans</ : isTrans _</_
    isTrans</ = elimProp3 (λ x _ z → isPropΠ2 λ _ _ → isPropValued</ x z) isTrans<

    isWeaklyExtensional</ : isWeaklyExtensional _</_
    isWeaklyExtensional</ = ≺×→≡→isWeaklyExtensional _</_ squash/ isPropValued</
      (elimProp2 (λ _ _ → isPropΠ λ _ → squash/ _ _)
      λ a b z → eq/ a b (isWeaklyExtensionalUpTo≈< a b
        λ c → z [ c ]))

    isWellFounded</ : WellFounded _</_
    isWellFounded</ = elimProp (λ _ → isPropAcc _)
      (WFI.induction isWellFounded< λ a ind
        → acc (elimProp (λ _ → isPropΠ λ _ → isPropAcc _)
              λ b b<a → ind b b<a))

    isWoset</ : IsWoset _</_
    isWoset</ = iswoset squash/
                        isPropValued</
                        isWellFounded</
                        isWeaklyExtensional</
                        isTrans</

    F/-Ord : Woset (ℓ-max ℓ' ℓ) ℓ
    F/-Ord = F/ , wosetstr _</_ isWoset</

    -- Now we verify that it's an upper bound
    F/IsUpperBound : (i : I) → F i ≼ F/-Ord
    F/IsUpperBound i = [_] ∘ ι i
      , isSimulation∃→isSimulation (F i) F/-Ord ([_] ∘ ι i)
       (ιPreservesOrder i
      , λ x → elimProp (λ _ → isPropΠ λ _ → isPropPropTrunc)
        λ (j , y) l → ∣ ((ι≈↓ i x (j , y) l .fst)
                      , (ι≈↓ i x (j , y) l .snd .fst))
                      , (eq/ (i , l .fst .fst) (j , y)
                        (ι≈↓ i x (j , y) l .snd .snd)) ∣₁)

    -- And that more specifically, it's the supremum
    F/IsSupremum : (β : Woset ℓ ℓ)
                 → ((i : I) → F i ≼ β)
                 → F/-Ord ≼ β
    F/IsSupremum β upβ = f/ , sim
      where wosβ = WosetStr.isWoset (str β)
            setβ = IsWoset.is-set wosβ
            propβ = IsWoset.is-prop-valued wosβ

            f/ : ⟨ F/-Ord ⟩ → ⟨ β ⟩
            f/ = /₂.rec setβ
                        (f⃕ β upβ)
                        λ a b → f⃕Respects≈ β upβ {a} {b}

            sim : isSimulation F/-Ord β f/
            sim = isSimulation∃→isSimulation F/-Ord β f/
                  ((elimProp2 (λ _ _ → isPropΠ λ _ → propβ _ _)
                    (f⃕presβ≺ β upβ))
                , elimProp (λ _ → isPropΠ2 λ _ _ → isPropPropTrunc)
                  λ a b b≺fa → ∣ ([ f⃕InitialSegment β upβ a b b≺fa .fst .fst ]
                                 , (f⃕InitialSegment β upβ a b b≺fa .fst .snd))
                                 , (f⃕InitialSegment β upβ a b b≺fa .snd) ∣₁)

-- With all of that done, we can now define supremum of small ordinal collections
sup : {I : Type ℓ'} (F : I → Woset ℓ ℓ)
    → Σ[ β ∈ Woset (ℓ-max ℓ' ℓ) ℓ ]
         ((i : I) → F i ≼ β)
       × ((γ : Woset ℓ ℓ) → ((i : I) → F i ≼ γ) → β ≼ γ)
sup F = (F/-Ord F) , (F/IsUpperBound F) , (F/IsSupremum F)
