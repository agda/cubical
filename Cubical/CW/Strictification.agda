{-# OPTIONS --lossy-unification #-}
{-
This file contains
1. A 'strictification' functor
   strictCWskel : CWskel -> CWskel s.t. strictCWskel C ≡ C
   the strictified version of C satisfies the pushout condition
   definitionally
2. The same thing for cellular maps
-}
module Cubical.CW.Strictification where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.Nat

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout

open import Cubical.CW.Base
open import Cubical.CW.Map

open SequenceMap renaming (map to ∣_∣)
open CWskel-fields


-- Strictification of CW skels
module _ {ℓ : Level} (B : CWskel ℓ) where
  open CWskel-fields
  strictifyFam : ℕ → Type ℓ
  strictifyFam≡ : (n : ℕ) → strictifyFam n ≡ fst B n
  strictifyFame : (n : ℕ) → fst B n ≃ strictifyFam n
  strictifyFamα : (n : ℕ) → Fin (fst (B .snd) n) × S⁻ n → strictifyFam n
  strictifyFame2 : (n : ℕ)
    → (Pushout (α B n) fst) ≃ (Pushout (strictifyFamα n) fst)
  strictifyFam zero = fst B 0
  strictifyFam (suc n) = Pushout (strictifyFamα n) fst
  strictifyFamα n = fst (strictifyFame n) ∘ α B n
  strictifyFame zero = idEquiv _
  strictifyFame (suc n) =
    compEquiv (e B n)
              (strictifyFame2 n)
  strictifyFame2 n =
    pushoutEquiv _ _ _ _ (idEquiv _) (strictifyFame n) (idEquiv _)
                   (λ _ x → fst (strictifyFame n) (α B n x))
                   (λ _ x → fst x)
  strictifyFam≡ zero = refl
  strictifyFam≡ (suc n) = ua (invEquiv (strictifyFame (suc n)))

  strictCWskel : CWskel ℓ
  fst strictCWskel = strictifyFam
  fst (snd strictCWskel) = card B
  fst (snd (snd strictCWskel)) = strictifyFamα
  fst (snd (snd (snd strictCWskel))) = fst (snd (snd (snd B)))
  snd (snd (snd (snd strictCWskel))) = λ _ → idEquiv _

  strict≡Gen : ∀ {ℓ ℓ'} {A : Type ℓ} {C D : Type ℓ'}
    (α : A → C) (e : C ≃ D) (x : A)
    → PathP (λ i → ua (invEquiv e) i) (fst e (α x)) (α x)
  strict≡Gen α e x i =
    hcomp (λ k → λ {(i = i0) → fst e (α x)
                   ; (i = i1) → retEq e (α x) k})
          (ua-gluePt (invEquiv e) i (fst e (α x)))

  strict≡GenT' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C D : Type ℓ''}
    {E : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))} (g : A → B)
    (e : C ≃ D)  (α : A → C) (e' : E ≃ Pushout (λ x₁ → α x₁) g)
    → PathP (λ k → ua (invEquiv (compEquiv {C = Pushout (fst e ∘ α) g} e'
                       (pushoutEquiv _ _ _ _ (idEquiv A) e (idEquiv B)
                         (λ i x → fst e (α x)) λ i x → g x))) k
                 ≃ Pushout (λ x₁ → strict≡Gen α e x₁ k) g)
            (idEquiv _)
            e'
  strict≡GenT' {A = A} {B} {C} {D} {E} g =
    EquivJ (λ C e → (α : A → C) (e' : E ≃ Pushout (λ x₁ → α x₁) g)
    → PathP (λ k → ua (invEquiv (compEquiv {C = Pushout (fst e ∘ α) g} e'
                       (pushoutEquiv _ _ _ _ (idEquiv A) e (idEquiv B)
                         (λ i x → fst e (α x)) λ i x → g x))) k
                  ≃ Pushout (λ x₁ → strict≡Gen α e x₁ k) g)
            (idEquiv _) e') λ a →
     EquivJ (λ E e'
    → PathP (λ k → ua (invEquiv (compEquiv e'
                         (pushoutEquiv a g a g (idEquiv A) (idEquiv D) (idEquiv B)
                           (λ i x → a x) (λ i → g)))) k
                  ≃ Pushout (λ x₁ → strict≡Gen a (idEquiv D) x₁ k) g)
                     (idEquiv (Pushout (λ x → idfun D (a x)) g)) e')
      (ΣPathPProp isPropIsEquiv
        (transport (λ k
    → PathP (λ i → (sym (lem g a)
                   ∙ sym (cong (ua ∘ invEquiv) (compEquivIdEquiv (pushoutEquiv a g
                       (λ z → idfun D (a z)) g (idEquiv A) (idEquiv D)
                         (idEquiv B) (λ i₁ x → idfun D (a x)) (λ i₁ → g))))) k i
                  → Pushout (λ x₁ → strict≡GenId a x₁ (~ k) i) g)
             (idfun _) (idfun _))
        (funExt (main _ _))))
    where
    strict≡GenId : ∀ {ℓ ℓ'} {A : Type ℓ} {C : Type ℓ'} (α : A → C)(x : A)
       → strict≡Gen α (idEquiv C) x
       ≡ λ i → ua-gluePt (invEquiv (idEquiv C)) i (α x)
    strict≡GenId {C = C} α x j i =
      hcomp (λ k → λ {(i = i0) → α x
                     ; (i = i1) → α x
                     ; (j = i1) → ua-gluePt (invEquiv (idEquiv C)) i (α x)})
            (ua-gluePt (invEquiv (idEquiv C)) i (α x))

    lem : (g : A → B) (α : A → D)
      → ua (invEquiv (pushoutEquiv α g α g
                       (idEquiv A) (idEquiv D) (idEquiv B) refl refl))
      ≡ refl
    lem g a = cong ua
      (cong invEquiv (Σ≡Prop isPropIsEquiv {v = idEquiv _}
                       (funExt λ { (inl x) → refl ; (inr x) → refl
                                 ; (push a i) j → rUnit (push a) (~ j) i}))
                       ∙ invEquivIdEquiv _) ∙ uaIdEquiv

    main : (g : A → B) (α : A → D) (w : _)
      → PathP (λ i → Pushout (λ s → ua-gluePt (invEquiv (idEquiv D)) i (α s)) g)
               w w
    main g α (inl x) i = inl (ua-gluePt (invEquiv (idEquiv D)) i x)
    main g α (inr x) i = inr x
    main g α (push a j) i = push a j

  strict≡α : (n : ℕ) (x : Fin (card B n)) (y : S⁻ n)
    → PathP (λ i → strictifyFam≡ n i)

              (strictifyFamα n (x , y))
              (α B n (x , y))
  strict≡α (suc n) x y =
    strict≡Gen (α B (suc n)) (strictifyFame (suc n)) (x , y)

  strict≡e : (n : ℕ)
    → PathP (λ i → strictifyFam≡ (suc n) i
                   ≃ Pushout (λ x → strict≡α n (fst x) (snd x) i) fst)
             (idEquiv _) (e B n)
  strict≡e zero =
    ΣPathPProp (λ _ → isPropIsEquiv _)
    (symP (toPathP (funExt
     λ { (inl x) → ⊥.rec (B .snd .snd .snd .fst x)
       ; (inr x)
         → cong (transport (λ i → Pushout (λ s → strict≡α zero
                                                    (fst s) (snd s) (~ i)) fst))
                (cong (e B 0 .fst) (transportRefl (invEq (e B 0) (inr x)))
              ∙ secEq (e B 0) (inr x))
          ∙ λ j → inr (transportRefl x j)})))
  strict≡e (suc n) =
    strict≡GenT' fst (strictifyFame (suc n)) (α B (suc n)) (e B (suc n))

  strict≡ : strictCWskel ≡ B
  fst (strict≡ i) n = strictifyFam≡ n i
  fst (snd (strict≡ i)) = card B
  fst (snd (snd (strict≡ i))) n (x , y) = strict≡α n x y i
  fst (snd (snd (snd (strict≡ i)))) = fst (snd (snd (snd B)))
  snd (snd (snd (snd (strict≡ i)))) n = strict≡e n i

-- Associated elimination principle
module _ {ℓ ℓ'} {P : CWskel ℓ → Type ℓ'}
  (e : (B : CWskel ℓ) → P (strictCWskel B)) where

  elimStrictCW : (B : _) → P B
  elimStrictCW B = subst P (strict≡ B) (e B)

  elimStrictCWβ : (B : _) → elimStrictCW (strictCWskel B) ≡ e B
  elimStrictCWβ B =
    (λ j → subst P (λ i → H strictCWskel (funExt (λ x → sym (strict≡ x))) B i j)
                 (e (strict≡ B j)))
    ∙ transportRefl (e B)
    where
    H : ∀ {ℓ} {A : Type ℓ}  (F : A → A) (s : (λ x → x) ≡ F) (a : A)
      → Square (λ i → F (s (~ i) a)) refl (λ i → s (~ i) (F a)) refl
    H = J> λ _ → refl

-- Strictification of cellular maps
module _ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'}
  (f : cellMap (strictCWskel C) (strictCWskel D)) where

  strictMapFun : (n : ℕ) → strictifyFam C n → strictifyFam D n
  strictMapComm : (n : ℕ) (x : strictifyFam C n) →
      strictMapFun n x ≡ ∣ f ∣ n x
  strictMapFun zero x = ∣ f ∣ 0 x
  strictMapFun (suc n) (inl x) = inl (strictMapFun n x)
  strictMapFun (suc n) (inr x) = ∣ f ∣ (suc n) (inr x)
  strictMapFun (suc (suc n)) (push c i) =
    (((λ i → inl (strictMapComm (suc n) (α (strictCWskel C) (suc n) c) i))
        ∙ comm f (suc n) (α (strictCWskel C) (suc n) c))
        ∙ cong (∣ f ∣ (suc (suc n))) (push c)) i
  strictMapComm zero x = refl
  strictMapComm (suc n) (inl x) = (λ i → inl (strictMapComm n x i)) ∙ comm f n x
  strictMapComm (suc n) (inr x) = refl
  strictMapComm (suc (suc n)) (push c i) j =
    compPath-filler'
      ((λ i → inl (strictMapComm (suc n) (α (strictCWskel C) (suc n) c) i))
        ∙ comm f (suc n) (α (strictCWskel C) (suc n) c))
      (cong (∣ f ∣ (suc (suc n))) (push c)) (~ j) i

  strictCwMap : cellMap (strictCWskel C) (strictCWskel D)
  SequenceMap.map strictCwMap = strictMapFun
  SequenceMap.comm strictCwMap n x = refl

  strictCwMap≡ : strictCwMap ≡ f
  ∣_∣ (strictCwMap≡ i) n x = strictMapComm n x i
  comm (strictCwMap≡ i) n x j =
   compPath-filler ((λ i₁ → inl (strictMapComm n x i₁))) (comm f n x) j i
