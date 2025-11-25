{-# OPTIONS --lossy-unification #-}

{-This file contains elimination principles and basic properties of CW
complexes/skeleta.
-}

module Cubical.CW.Properties where

open import Cubical.CW.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Properties

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Unit
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sequence

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as TR

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Axiom.Choice

open import Cubical.Relation.Nullary

open import Cubical.Homotopy.Connected

open Sequence



private
  variable
    ℓ ℓ' ℓ'' : Level

CW₀-empty : (C : CWskel ℓ) → ¬ fst C 0
CW₀-empty C = snd (snd (snd C)) .fst

CW₁-discrete : (C : CWskel ℓ) → fst C 1 ≃ Fin (snd C .fst 0)
CW₁-discrete C = compEquiv (snd C .snd .snd .snd 0) (isoToEquiv main)
  where
  main : Iso (Pushout (fst (snd C .snd) 0) fst) (Fin (snd C .fst 0))
  Iso.fun main (inl x) = ⊥.rec (CW₀-empty C x)
  Iso.fun main (inr x) = x
  Iso.inv main = inr
  Iso.rightInv main x = refl
  Iso.leftInv main (inl x) = ⊥.rec (CW₀-empty C x)
  Iso.leftInv main (inr x) = refl

-- elimination from Cₙ into prop
CWskel→Prop : (C : CWskel ℓ) {A : (n : ℕ) → fst C n → Type ℓ'}
  → ((n : ℕ) (x : _) → isProp (A n x))
  → ((a : _) → A (suc zero) a)
  → ((n : ℕ) (a : _) → (A (suc n) a → A (suc (suc n)) (CW↪ C (suc n) a)))
  → (n : _) (c : fst C n) → A n c
CWskel→Prop C {A = A} pr b eqs zero c = ⊥.rec (CW₀-empty C c)
CWskel→Prop C {A = A} pr b eqs (suc zero) = b
CWskel→Prop C {A = A} pr b eqs (suc (suc n)) c =
  subst (A (suc (suc n)))
        (retEq (snd C .snd .snd .snd (suc n)) c)
        (help (CWskel→Prop C pr b eqs (suc n)) _)
  where
  help : (inder : (c₁ : fst C (suc n)) → A (suc n) c₁)
       → (a : Pushout _ fst)
       → A (suc (suc n)) (invEq (snd C .snd .snd .snd (suc n)) a)
  help inder =
    elimProp _ (λ _ → pr _ _) (λ b → eqs n _ (inder b))
     λ c → subst (A (suc (suc n)))
                  (cong (invEq (snd C .snd .snd .snd (suc n))) (push (c , ptSn n)))
                  (eqs n _ (inder _))

isSet-CW₀ : (C : CWskel ℓ) → isSet (fst C (suc zero))
isSet-CW₀ C =
   isOfHLevelRetractFromIso 2 (equivToIso (CW₁-discrete C))
    isSetFin

-- eliminating from CW complex into prop
CW→Prop : (C : CWskel ℓ) {A : realise C → Type ℓ'}
  → ((x : _) → isProp (A x))
  → ((a : _) → A (incl {n = suc zero} a))
  → (a : _) → A a
CW→Prop C {A = A} pr ind  =
  SeqColim→Prop pr (CWskel→Prop C (λ _ _ → pr _)
    ind
    λ n a → subst A (push a))

-- realisation of finite complex
realiseFin : (n : ℕ) (C : finCWskel ℓ n) → Iso (fst C n) (realise (finCWskel→CWskel n C))
realiseFin n C = converges→ColimIso n (snd C .snd)

-- elimination principles for CW complexes
module _ {ℓ : Level} (C : CWskel ℓ) where
  open CWskel-fields C
  module _ (n : ℕ) {B : fst C (suc n) → Type ℓ'}
         (inler : (x : fst C n) → B (invEq (e n) (inl x)))
         (inrer : (x : A n) → B (invEq (e n) (inr x)))
         (pusher : (x : A n) (y : S⁻ n)
        → PathP (λ i → B (invEq (e n) (push (x , y) i)))
                 (inler (α n (x , y)))
                 (inrer x)) where
    private
      gen : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : A → Type ℓ')
                  (e : A ≃ B)
               → ((x : B) → C (invEq e x))
               → (x : A) → C x
      gen C e h x = subst C (retEq e x) (h (fst e x))

      gen-coh : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : A → Type ℓ')
                  (e : A ≃ B) (h : (x : B) → C (invEq e x))
               → (b : B)
               → gen C e h (invEq e b) ≡ h b
      gen-coh {ℓ' = ℓ'} {A = A} {B = B} C e =
        EquivJ (λ A e → (C : A → Type ℓ') (h : (x : B) → C (invEq e x))
               → (b : B)
               → gen C e h (invEq e b) ≡ h b)
               (λ C h b → transportRefl (h b)) e C

      main : (x : _) → B (invEq (e n) x)
      main (inl x) = inler x
      main (inr x) = inrer x
      main (push (x , y) i) = pusher x y i

    CWskel-elim : (x : _) → B x
    CWskel-elim = gen B (e n) main

    CWskel-elim-inl : (x : _) → CWskel-elim (invEq (e n) (inl x)) ≡ inler x
    CWskel-elim-inl x = gen-coh B (e n) main (inl x)

  module _ (n : ℕ) {B : fst C (suc (suc n)) → Type ℓ'}
           (inler : (x : fst C (suc n))
                  → B (invEq (e (suc n)) (inl x)))
           (ind : ((x : A (suc n)) (y : S₊ n)
           → PathP (λ i → B (invEq (e (suc n))
                                   ((push (x , y) ∙ sym (push (x , ptSn n))) i)))
                   (inler (α (suc n) (x , y)))
                   (inler (α (suc n) (x , ptSn n))))) where
    CWskel-elim' : (x : _) → B x
    CWskel-elim' =
      CWskel-elim (suc n) inler
        (λ x → subst (λ t → B (invEq (e (suc n)) t))
                      (push (x , ptSn n))
                      (inler (α (suc n) (x , ptSn n))))
        λ x y → toPathP (sym (substSubst⁻ (B ∘ invEq (e (suc n)))  _ _)
           ∙ cong (subst (λ t → B (invEq (e (suc n)) t))
                         (push (x , ptSn n)))
                  (sym (substComposite (B ∘ invEq (e (suc n))) _ _ _)
            ∙ fromPathP (ind x y)))

    CWskel-elim'-inl : (x : _)
      → CWskel-elim' (invEq (e (suc n)) (inl x)) ≡ inler x
    CWskel-elim'-inl = CWskel-elim-inl (suc n) {B = B} inler _ _

finCWskel≃ : (n : ℕ) (C : finCWskel ℓ n) (m : ℕ) → n ≤ m → fst C n ≃ fst C m
finCWskel≃ n C m (zero , diff) = substEquiv (λ n → fst C n) diff
finCWskel≃ n C zero (suc x , diff) = ⊥.rec (snotz diff)
finCWskel≃ n C (suc m) (suc x , diff) =
  compEquiv (finCWskel≃ n C m (x , cong predℕ diff))
            (compEquiv (substEquiv (λ n → fst C n) (sym (cong predℕ diff)))
            (compEquiv (_ , snd C .snd x)
            (substEquiv (λ n → fst C n) diff)))

-- C₁ satisfies AC
satAC-CW₁ : (n : ℕ) (C : CWskel ℓ) → satAC ℓ' n (fst C (suc zero))
satAC-CW₁ n C A =
  subst isEquiv (choicefun≡ n) (isoToIsEquiv (choicefun' n))
  where
  fin = Fin (snd C .fst zero)
  satAC' : (n : ℕ) → satAC ℓ' n fin
  satAC' n = InductiveFinSatAC _ _

  fin→ : fin ≃ fst C 1
  fin→ = invEquiv (CW₁-discrete C)


  choicefun' : (n : ℕ) → Iso (hLevelTrunc n ((a : fst C 1) → A a))
           ((a : fst C 1) → hLevelTrunc n (A a))
  choicefun' n = compIso (mapCompIso (domIsoDep (equivToIso fin→)))
        (compIso (equivToIso (_ , satAC' n (λ a → A (fst fin→ a))))
        (invIso (domIsoDep (equivToIso fin→))))


  choicefun≡ : (n : ℕ) → Iso.fun (choicefun' n) ≡ choiceMap n
  choicefun≡ zero = refl
  choicefun≡ (suc n) = funExt (TR.elim
    (λ _ → isOfHLevelPath (suc n)
      (isOfHLevelΠ (suc n) (λ _ → isOfHLevelTrunc (suc n))) _ _)
    λ f → funExt λ a → cong ∣_∣
      (funExt⁻ ((Iso.leftInv (domIsoDep (equivToIso fin→))) f) a))

satAC∃Fin-C0 : (C : CWskel ℓ) → satAC∃ ℓ' ℓ'' (fst C 1)
satAC∃Fin-C0 C =
  subst (satAC∃ _ _)
  (ua (compEquiv (invEquiv LiftEquiv) (invEquiv (CW₁-discrete C))))
    λ T c → isoToIsEquiv (iso _
      (λ f → PT.map (λ p → (λ { (lift x) → p .fst x})
                            , λ { (lift x) → p .snd x})
              (invEq (_ , (InductiveFinSatAC∃ (snd C .fst 0))
                     (T ∘ lift) (c ∘ lift)) (f ∘ lift)))
      (λ _ → (isPropΠ λ _ → squash₁) _ _)
      λ _ → squash₁ _ _)

--- Connectivity of CW complexes
-- The embedding of stage n into stage n+1 is (n+1)-connected
-- 2 calls to univalence in there
isConnected-CW↪ : (n : ℕ) (C : CWskel ℓ) → isConnectedFun n (CW↪ C n)
isConnected-CW↪ zero C x = isContrUnit*
isConnected-CW↪ (suc n) C =
  EquivJ (λ X E → isConnectedFun (suc n) (λ x → invEq E (inl x)))
                   inPushoutConnected (e₊ (suc n))
  where
    A = snd C .fst
    α = snd C .snd .fst
    e₊ = snd C .snd .snd .snd

    inPushout : fst C (suc n) → Pushout (α (suc n)) fst
    inPushout x = inl x

    fstProjPath : (b : Fin (A (suc n))) → S₊ n ≡ fiber fst b
    fstProjPath b = ua (fiberProjEquiv (Fin (A (suc n))) (λ _ → S₊ n) b)

    inPushoutConnected : isConnectedFun (suc n) inPushout
    inPushoutConnected = inlConnected (suc n) (α (suc n)) fst
      λ b → subst (isConnected (suc n)) (fstProjPath b) (sphereConnected n)

-- The embedding of stage n into the colimit is (n+1)-connected
isConnected-CW↪∞ : (n : ℕ) (C : CWskel ℓ) → isConnectedFun n (CW↪∞ C n)
isConnected-CW↪∞ zero C b = isContrUnit*
isConnected-CW↪∞ (suc n) C = isConnectedIncl∞ (realiseSeq C) (suc n) (suc n) subtr
  where
    subtr : (k : ℕ) → isConnectedFun (suc n) (CW↪ C (k +ℕ (suc n)))
    subtr k = isConnectedFunSubtr (suc n) k (CW↪ C (k +ℕ (suc n)))
                                   (isConnected-CW↪ (k +ℕ (suc n)) C)

-- The m-skeleton of an n-connected complex (m≤n) is n-connected
isConnectedCW→isConnectedSkel : (C : CWskel ℓ)
  → (m : ℕ) (n : Fin (suc m))
  → isConnected (fst n) (realise C)
  → isConnected (fst n) (C .fst m)
isConnectedCW→isConnectedSkel C m (n , p) =
  isOfHLevelRetractFromIso 0
    (compIso (truncOfTruncIso n t₀)
      (compIso
        (mapCompIso
          (subst (λ k → Iso (hLevelTrunc k (C .fst m))
                             (hLevelTrunc k (realise C)))
                  (sym teq)
                  (connectedTruncIso m _
                    (isConnected-CW↪∞ m C))))
        (invIso (truncOfTruncIso n t₀))))
  where
  t = <ᵗ→< p
  t₀ = fst t
  teq : t₀ +ℕ n ≡ m
  teq = cong predℕ (sym (+-suc t₀ n) ∙ snd t)

truncCWIso : (A : CWskel ℓ) (n : ℕ)
  → Iso (hLevelTrunc n (realise A)) (hLevelTrunc n (fst A n))
truncCWIso A n = invIso (connectedTruncIso n incl (isConnected-CW↪∞ n A))

isConnectedColim→isConnectedSkel :
  (A : CWskel ℓ) (n : ℕ)
  → isConnected n (realise A)
  → isConnected n (fst A n)
isConnectedColim→isConnectedSkel A n c =
  isOfHLevelRetractFromIso 0
    (invIso (truncCWIso A n)) c
