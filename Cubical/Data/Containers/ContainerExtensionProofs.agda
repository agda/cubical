{- 2 presentations of the proof that the functor ⟦_⟧ : Cont → Func
   is full and faithful

- First one is adapted from 'Containers: Constructing strictly positive types'
  by Abbott, Altenkirch, Ghani

- Second one uses the Yoneda lemma

-}

{-# OPTIONS --safe #-}

open import Agda.Builtin.Cubical.HCompU

open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Yoneda
open import Cubical.Data.Containers.Base
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism 
open import Cubical.Foundations.Function

module Cubical.Data.Containers.ContainerExtensionProofs where

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

open Category hiding (_∘_)
open Functor
open NatTrans
open Iso

module _ {C : Category ℓ ℓ'} where

    open Conts {ℓ} {ℓ'} {C}   

    -- Proof 1 that the functor ⟦_⟧ is full and faithful
    -- Adapted from 'Containers: Constructing strictly positive types'

    ⟦_⟧FullyFaithful : isFullyFaithful ⟦_⟧
    equiv-proof (⟦_⟧FullyFaithful (S ◁ P & set-S) (T ◁ Q & set-T)) (natTrans mors nat) =
      (fib (natTrans mors nat) , fib-pf) , unique
      where
        fib : NatTrans ⟦ (S ◁ P & set-S) ⟧-obj ⟦ (T ◁ Q & set-T) ⟧-obj →
              (S ◁ P & set-S) ⇒c (T ◁ Q & set-T)
        fib (natTrans mors _) = (fst ∘ tq) ◁ (snd ∘ tq)
          where
            tq : (s : S) → cont-func T Q (P s)
            tq s = mors (P s) (s , C .id {P s}) 

        fib-pf : ⟦ fib (natTrans mors nat) ⟧-mor ≡ (natTrans mors nat)
        fib-pf = cong₂
                   natTrans
                   ((funExt λ X → funExt λ {(s , h) →
                     sym (funExt⁻ (nat h) (s , C .id)) ∙ cong (λ Z → mors X (s , Z)) (C .⋆IdL h)})) 
                   (isProp→PathP (λ i → isPropImplicitΠ2 (λ X Y → isPropΠ (λ f →
                     isSetΠ (λ _ → isSetContFunc T Q Y set-T) _ _))) _ _) 

        ret : ∀ X→Y → fib (⟦ X→Y ⟧-mor) ≡ X→Y
        ret (u ◁ f) i = u ◁ λ s → C .⋆IdR (f s) i
        
        unique : (y : Helpers.fiber (⟦_⟧-mor) (natTrans mors nat)) → (fib (natTrans mors nat) , fib-pf) ≡ y
        unique (m , m-eq) = ΣPathP (cong (fib) (sym m-eq) ∙ ret m , square)
          where
            square : Square (λ i → fib-pf i)
                            (λ i → m-eq i)
                            (λ i → F-hom ⟦_⟧ (((λ j → fib (m-eq (~ j))) ∙ ret m) i))
                            refl
            square = isSet→SquareP (λ _ _ → isSetNatTrans) _ _ _ _

    -- Proof 2 that the functor ⟦_⟧ is full and faithful
    -- Uses the Yoneda lemma

    ⟦_⟧FullyFaithful' : isFullyFaithful ⟦_⟧
    equiv-proof (⟦_⟧FullyFaithful' (S ◁ P & set-S) (T ◁ Q & set-T)) (natTrans mors nat) =
      (mor , mor-eq) , unique
      where
        -- Distributivity of Π over Σ
        distrΠΣ : {A : Type ℓ''}{B : A → Type ℓ'''}{C : (a : A) → B a → Type ℓ''''} →
                  Iso ((a : A) → Σ (B a) (λ b → C a b))
                      (Σ ((a : A) → B a) (λ f → (a : A) → C a (f a)))
        fun distrΠΣ f = (λ a → fst (f a)) , λ a → snd (f a)
        inv distrΠΣ (f , g) a = f a , g a
        rightInv distrΠΣ _ = refl
        leftInv distrΠΣ _ = refl

        -- Compose heterogenous with homogenous equality
        compHetHomP : {A : I → Type ℓ'} (x : A i0) (y : A i1) (z : A i1) →
                       PathP (λ i → A i) x y → y ≡ z → PathP (λ i → A i) x z
        compHetHomP {A} x y z p eq i = subst (λ c → PathP A x c) eq p i
        
        nat-trans : (s : S) → FUNCTOR C (SET ℓ') [ C [ P s ,-] , ⟦ T ◁ Q & set-T ⟧-obj ]
        nat-trans s = natTrans (λ X → curry (mors X) s) nat'
          where
            nat' : N-hom-Type (C [ P s ,-]) ⟦ T ◁ Q & set-T ⟧-obj (λ X → curry (mors X) s)
            nat' {X} {Y} X→Y = funExt (λ Ps→X → funExt⁻ (nat {X} {Y} X→Y) (s , Ps→X))

        apply-yo : (s : S) → cont-func T Q (P s)
        apply-yo s = (fun (yoneda ⟦ T ◁ Q & set-T ⟧-obj (P s))) (nat-trans s)

        apply-distrΠΣ : Σ (S → T) (λ f → (s : S) → C [ Q (f s) , P s ])
        apply-distrΠΣ = (fun distrΠΣ) (apply-yo)

        mor : (S ◁ P & set-S) ⇒c (T ◁ Q & set-T)
        mor = fst apply-distrΠΣ ◁ snd apply-distrΠΣ
        
        mor-eq : ⟦ mor ⟧-mor ≡ natTrans mors nat
        mor-eq = cong₂
                   natTrans
                   (funExt (λ X → funExt (λ {(s , f) →
                     sym (funExt⁻ (nat {P s} {X} f) (s , C .id)) ∙
                     cong (λ Z → mors X (s , Z)) (C .⋆IdL f)})))
                   ((isProp→PathP (λ i → isPropImplicitΠ2 (λ X Y → isPropΠ (λ f →
                     isSetΠ (λ _ → isSetContFunc T Q Y set-T) _ _))) _ _))

        
        
        unique : (y : Helpers.fiber (⟦_⟧-mor) (natTrans mors nat)) → (mor , mor-eq) ≡ y
        unique ((u ◁ f) , m-eq) =
          ΣPathP
            (cong₂ _◁_ (funExt (λ s i → fst (N-ob (m-eq (~ i)) (P s) (s , C .id))))
                       (funExt (λ s i → compHetHomP
                                         (snd (mors (P s) (s , C .id)))
                                         (f s ⋆⟨ C ⟩ (C .id))
                                         (f s)
                                         (λ j → snd (N-ob (m-eq (~ j)) (P s) (s , C .id)))
                                         (C .⋆IdR (f s)) i))
            ,
            square)
             where
               square : Square (λ i → mor-eq i)
                               (λ i → m-eq i)
                               (λ i → ⟦_⟧-mor {S ◁ P & set-S} {T ◁ Q & set-T}
                                              (funExt (λ s j → fst (N-ob (m-eq (~ j)) (P s) (s , C .id))) i ◁
                                              funExt (λ s j → compHetHomP
                                                                 (snd (mors (P s) (s , C .id)))
                                                                 (seq' C (f s) (C .id)) (f s)
                                                                 (λ k → snd (N-ob (m-eq (~ k)) (P s) (s , C .id)))
                                                                 (C .⋆IdR (f s)) j) i))
                               (λ j → natTrans mors nat)
               square = isSet→SquareP (λ _ _ → isSetNatTrans) _ _ _ _
               
