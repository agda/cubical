{- 2 presentations of the proof that the functor ⟦_⟧ : Cont → Func
   is full and faithful

- First one is adapted from 'Containers: Constructing strictly positive types'
  by Abbott, Altenkirch, Ghani

- Second one uses the Yoneda lemma

-}

{-# OPTIONS --safe #-}

module Cubical.Data.Containers.ContainerExtensionProofs where

open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Yoneda

open import Cubical.Data.Containers.Base
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

open Category hiding (_∘_)
open Functor
open NatTrans
open Iso

module _ {C : Category ℓ ℓ'} where

    open Conts {ℓ} {ℓ'} C

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
        fib-pf = makeNatTransPath
          (funExt₂ λ X (s , h) → sym (funExt⁻ (nat h) (s , C .id)) ∙
                                 cong (λ Z → mors X (s , Z)) (C .⋆IdL h))

        ret : ∀ X→Y → fib (⟦ X→Y ⟧-mor) ≡ X→Y
        ret (u ◁ f) i = u ◁ λ s → C .⋆IdR (f s) i

        unique : (y : fiber (⟦_⟧-mor) (natTrans mors nat)) → (fib (natTrans mors nat) , fib-pf) ≡ y
        unique (m , m-eq) = Σ≡Prop (λ _ → isSetNatTrans _ _) (cong fib (sym m-eq) ∙ ret m)

    -- Proof 2 that the functor ⟦_⟧ is full and faithful
    -- Uses the Yoneda lemma

    ⟦_⟧FullyFaithful' : isFullyFaithful ⟦_⟧
    equiv-proof (⟦_⟧FullyFaithful' (S ◁ P & set-S) (T ◁ Q & set-T)) (natTrans mors nat) =
      (mor , mor-eq) , unique
      where
        -- Compose heterogenous with homogenous equality
        compHetHomP : {A : I → Type ℓ'} {x : A i0} {y : A i1} {z : A i1} →
                       PathP (λ i → A i) x y → y ≡ z → PathP (λ i → A i) x z
        compHetHomP {A} {x} {y} {z} p eq i = subst (λ c → PathP A x c) eq p i

        nat-trans : (s : S) → FUNCTOR C (SET ℓ') [ C [ P s ,-] , ⟦ T ◁ Q & set-T ⟧-obj ]
        N-ob (nat-trans s) X = curry (mors X) s
        N-hom (nat-trans s) X→Y i Ps→X = nat X→Y i (s , Ps→X)

        apply-yo : (s : S) → cont-func T Q (P s)
        apply-yo s = yoneda ⟦ T ◁ Q & set-T ⟧-obj (P s) .fun (nat-trans s)

        apply-Σ-Π-Iso : Σ (S → T) (λ f → (s : S) → C [ Q (f s) , P s ])
        apply-Σ-Π-Iso = Σ-Π-Iso .fun apply-yo

        mor : (S ◁ P & set-S) ⇒c (T ◁ Q & set-T)
        mor = fst apply-Σ-Π-Iso ◁ snd apply-Σ-Π-Iso

        mor-eq : ⟦ mor ⟧-mor ≡ natTrans mors nat
        mor-eq = makeNatTransPath
                   (funExt₂ λ X (s , f) → sym (funExt⁻ (nat f) (s , C .id)) ∙
                   cong (λ Z → mors X (s , Z)) (C .⋆IdL f))

        unique : (y : fiber (⟦_⟧-mor) (natTrans mors nat)) → (mor , mor-eq) ≡ y
        unique ((u ◁ f) , m-eq) = Σ≡Prop (λ _ → isSetNatTrans _ _)
                                         λ i → (λ s → fst (N-ob (m-eq (~ i)) (P s) (s , C .id))) ◁
                                                λ s → compHetHomP
                                                       (λ j → snd (N-ob (m-eq (~ j)) (P s) (s , C .id)))
                                                       (C .⋆IdR (f s)) i
