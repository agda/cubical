{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.FiberOrCofiberSequences.CofiberBase where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.Pushout
open import Cubical.HITs.SetTruncation renaming (elim to setElim)

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.LES

open import Cubical.CW.Base
open import Cubical.CW.Instances.Pushout renaming (isFinCWPushout to isFinCWPushout')

open import Cubical.Homotopy.Serre.PointedHITs

open import Cubical.Homotopy.Serre.ConnectedCovers.TruncationLevelFacts
open import Cubical.Homotopy.Serre.FiniteCW
open import Cubical.Homotopy.Serre.Pullback.IsPullback

private
  variable
    ℓ : Level

isConnectedTrnspConnected* : {W X Y Z : Type ℓ} {n : ℕ} (p : Y ≡ Z) (q : X ≡ W) (f : X → Y)
  → isConnectedFun n f
  → isConnectedFun n (transport (λ i → (q i) → (p i)) f)
isConnectedTrnspConnected* {X = X} {n = n} p q f conf  =
  transport (λ i → isConnectedFun n
                    (transp (λ j → (q (j ∧ i)) → (p (j ∧ i))) (~ i) f))
    conf


Unit-map : {A : Type ℓ} → PathP (λ _ → A → Unit* {ℓ})
                                 (equivFun (Unit≃Unit* {ℓ})
                                 ∘ (λ (_ : A) → tt))
                                 (λ (_ : A) → tt*)
Unit-map = funExt (λ _ → refl)



pushoutFunEqIso^ : ∀ {ℓA ℓA' ℓC ℓB}
  {A : Type ℓA} {A' : Type ℓA'}
  {C : Type ℓC} {B : Type ℓB}
  (f : A → B) (g : A → C) (h : A' → B) (k : A' → C)
  (K : Iso A A')
  (q : f ≡ h ∘ Iso.fun K)
  (p : g ∘ Iso.inv K ≡ k)
  → Iso (Pushout f g) (Pushout h k)
pushoutFunEqIso^ f g h k K q p =
  pushoutIso f g h k (isoToEquiv K) (idEquiv _) (idEquiv _)
    q (funExt (λ x → cong g (sym (Iso.ret K x)))
    ∙ cong (_∘ Iso.fun K) p)

pushoutLevelMix^ : ∀ {ℓA ℓB ℓC ℓC'}
  {A : Type ℓA} {C : Type ℓC} {B : Type ℓB} {C' : Type ℓC'}
   (f : A → B) (g : A → C) (g' : A → C')
   (K : Iso C C')
   (q : Iso.fun K ∘ g ≡ g')
   → Iso (Pushout f g) (Pushout f g')
pushoutLevelMix^ f g g' K q =
  pushoutIso f g f g' (idEquiv _) (idEquiv _) (isoToEquiv K) refl q

pushoutLevelMix^* : ∀ {ℓA ℓB ℓB' ℓC}
  {A : Type ℓA} {C : Type ℓC} {B : Type ℓB} {B' : Type ℓB'}
  (f : A → B) (f' : A → B') (g : A → C)
  (H : Iso B B')
  (q : Iso.fun H ∘ f ≡ f')
  → Iso (Pushout f g) (Pushout f' g)
pushoutLevelMix^* f f' g H q =
  pushoutIso f g f' g (idEquiv _) (isoToEquiv H) (idEquiv _) q refl

unitLevelMix^ : Iso (Unit* {ℓ}) (Unit)
unitLevelMix^ = invIso LiftIso

unitLevelMix'^ : {B : Type ℓ}
  → (λ (x : B) → (Iso.inv (unitLevelMix^ {ℓ})) ((λ (_ : B) → tt) x))
  ≡ (λ (_ : B) → tt*)
unitLevelMix'^ = refl





cofiber∙ : {A B : Pointed ℓ} (f : A →∙ B) → Pointed ℓ
cofiber∙ f = (cofib (fst f) , inl tt)

cofiberMap∙ : {A B : Pointed ℓ} (f : A →∙ B)
              → (B →∙ (cofiber∙ f))
fst (cofiberMap∙ f) = inr
snd (cofiberMap∙ {A = A} f) = (push (pt A) ∙ cong inr (snd f)) ⁻¹

record CofiberSeq (A B C : Pointed ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    incl : A →∙ B
    proj : B →∙ C
    eqCof : PathP (λ _ → Σ[ X ∈ Pointed ℓ ] (B →∙ X))
                  (C , proj)
                  (cofiber∙ incl , cofiberMap∙ incl)

CofiberSeqDom : {A B C : Pointed ℓ} → CofiberSeq A B C → Pointed ℓ
CofiberSeqDom {A = A} S = A

CofiberSeqDom-Id : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                      → CofiberSeqDom S ≡ A
CofiberSeqDom-Id = refl

CofiberSeqExt : {A B C : Pointed ℓ} → CofiberSeq A B C → Pointed ℓ
CofiberSeqExt {B = B} S = B

CofiberSeqExt-Id : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                     → CofiberSeqExt S ≡ B
CofiberSeqExt-Id = refl

CofiberSeqCof : {A B C : Pointed ℓ} → CofiberSeq A B C → Pointed ℓ
CofiberSeqCof {C = C} S = C

CofiberSeqCof-Id : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                     → CofiberSeqCof S ≡ C
CofiberSeqCof-Id = refl

CofiberSeqInc : {A B C : Pointed ℓ} (S : CofiberSeq A B C)
                  → ((CofiberSeqDom S) →∙ (CofiberSeqExt S))
CofiberSeqInc S = CofiberSeq.incl S

CofiberSeqProj : {A B C : Pointed ℓ} (S : CofiberSeq A B C)
                   → ((CofiberSeqExt S) →∙ (CofiberSeqCof S))
CofiberSeqProj S = CofiberSeq.proj S

cofiber-CofiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
    → CofiberSeq A B (cofib (fst f) , inl tt)
CofiberSeq.incl (cofiber-CofiberSeq f) = f
CofiberSeq.proj (cofiber-CofiberSeq f) = cofiberMap∙ f
CofiberSeq.eqCof (cofiber-CofiberSeq f) = refl

cofiber-isPushout' : {A B : Pointed ℓ} (f : A →∙ B)
  → typ (CofiberSeqCof (cofiber-CofiberSeq f))
     ≡ Pushout (λ _ → tt) (fst f)
cofiber-isPushout' f = refl

cofiber-isPushout : {A B : Pointed ℓ} (f : A →∙ B)
  → typ (CofiberSeqCof (cofiber-CofiberSeq f))
     ≡ Pushout {B = Unit* {ℓ}} (λ _ → tt*) (fst f)
cofiber-isPushout {ℓ} f =
  cofiber-isPushout' f
  ∙ ua (isoToEquiv
       (pushoutLevelMix^* (λ _ → tt) (λ _ → tt*) (fst f)
                          (invIso unitLevelMix^) unitLevelMix'^))

cofiber-isPushout∙ : {A B : Pointed ℓ} (f : A →∙ B)
  → CofiberSeqCof (cofiber-CofiberSeq f)
   ≡ (Pushout {B = Unit* {ℓ}} (λ _ → tt*) (fst f) , inl tt*)
cofiber-isPushout∙ f =
  ua∙
   (isoToEquiv
    (pushoutLevelMix^* (λ _ → tt) (λ _ → tt*) (fst f)
                       (invIso unitLevelMix^) unitLevelMix'^))
    refl

Cof-isPushout : {A B C : Pointed ℓ} (S : CofiberSeq A B C)
  → typ (CofiberSeqCof S)
   ≡ Pushout {B = Unit* {ℓ}} (λ _ → tt*) (fst (CofiberSeq.incl S))
Cof-isPushout S = (λ i → typ (fst (CofiberSeq.eqCof S i)))
                ∙ cofiber-isPushout (CofiberSeq.incl S)

Cof-isPushout∙ : {A B C : Pointed ℓ} (S : CofiberSeq A B C)
  → CofiberSeqCof S
  ≡ (Pushout {B = Unit* {ℓ}} (λ _ → tt*) (fst (CofiberSeq.incl S)) ,
             inl tt*)
Cof-isPushout∙ S = (λ i → fst (CofiberSeq.eqCof S i))
                   ∙ cofiber-isPushout∙ (CofiberSeq.incl S)

isFinCWCofiberSeq-cofiber : {A B : Pointed ℓ} (f : A →∙ B)
    → (isFinCW (typ (CofiberSeqDom (cofiber-CofiberSeq f))))
    → (isFinCW (typ (CofiberSeqExt (cofiber-CofiberSeq f))))
    → (isFinCW (typ (CofiberSeqCof (cofiber-CofiberSeq f))))
isFinCWCofiberSeq-cofiber {ℓ} f hA hB =
  transport (λ i → isFinCW (cofiber-isPushout f (~ i)))
            (isFinCWPushout (λ _ → tt*) (fst f) hA isFinCWUnit hB)

isFinCWCofiberSeq : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                      → (isFinCW (typ (CofiberSeqDom S)))
                      → (isFinCW (typ (CofiberSeqExt S)))
                      → (isFinCW (typ (CofiberSeqCof S)))
isFinCWCofiberSeq {S = S} hA hB =
  transport (λ i → isFinCW (typ (fst (CofiberSeq.eqCof S (~ i)))))
            (isFinCWCofiberSeq-cofiber (CofiberSeq.incl S) hA hB)

CofiberSeqMap : {A B C A' B' C' : Pointed ℓ}
    (S : CofiberSeq A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom S) →∙ (CofiberSeqDom S'))
    (g : (CofiberSeqExt S) →∙ (CofiberSeqExt S'))
    → (g ∘∙ CofiberSeqInc S) ≡ (CofiberSeqInc S' ∘∙ f)
    → ((CofiberSeqCof S) →∙ (CofiberSeqCof S'))
CofiberSeqMap S S' f g H =
  transport (λ i → (Cof-isPushout∙ S (~ i))
                 →∙ (Cof-isPushout∙ S' (~ i)))
    (Pushout→ (λ _ → tt*) (fst (CofiberSeq.incl S)) (λ _ → tt*)
                         (fst (CofiberSeq.incl S')) (fst f) (λ _ → tt*)
                         (fst g) refl (λ i → (fst (H i)))
             , refl)

CofiberSeqMapConn : (n : ℕ) {A B C A' B' C' : Pointed ℓ}
    (S : CofiberSeq A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom S) →∙ (CofiberSeqDom S'))
    (g : (CofiberSeqExt S) →∙ (CofiberSeqExt S'))
    (p : (g ∘∙ CofiberSeqInc S) ≡ (CofiberSeqInc S' ∘∙ f))
    → isConnectedFun n (fst f)
    → isConnectedFun (1 + n) (fst g)
    → isConnectedFun (1 + n) (fst (CofiberSeqMap S S' f g p))
CofiberSeqMapConn n S S' f g p hf hg =
  isConnectedTrnspConnected*
    (λ i → typ ((Cof-isPushout∙ S' ⁻¹) i))
    (λ i → typ ((Cof-isPushout∙ S ⁻¹) i))
    (Pushout→ (λ _ → tt*) (fst (CofiberSeq.incl S)) (λ _ → tt*)
               (fst (CofiberSeq.incl S')) (fst f) (λ _ → tt*) (fst g)
               refl λ i → fst (p i))
    (isConnectedPushout→ (λ _ → tt*) (fst (CofiberSeq.incl S)) (λ _ → tt*)
     (fst (CofiberSeq.incl S')) (fst f) (λ _ → tt*)
       (fst g) refl (λ i → fst (p i)) n hf
       (isEquiv→isConnected (λ _ → tt*)
       (isoToIsEquiv (iso (λ _ → tt*) (λ _ → tt*)
       (λ _ → refl) (λ _ → refl))) (1 + n)) hg)

-- cofiber sequences for unpointed maps
cofiber : {A B : Type ℓ} (f : A → B) → Pointed ℓ
cofiber f = (cofib f , inl tt)

cofiberMap : {A B : Type ℓ} (f : A → B)
              → (B → fst (cofiber f))
cofiberMap f = inr

record CofiberSeq₋ (A B : Type ℓ) (C : Pointed ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    incl : A → B
    proj : B → (typ C)
    eqCof : PathP (λ _ → Σ[ X ∈ Pointed ℓ ] (B → typ X))
                  (C , proj)
                  (cofiber incl , cofiberMap incl)


CofiberSeqDom₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Type ℓ
CofiberSeqDom₋ {A = A} S = A

CofiberSeqDom-Eq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqDom₋ S ≃ A
CofiberSeqDom-Eq₋ = idEquiv _

CofiberSeqDom-Id₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqDom₋ S ≡ A
CofiberSeqDom-Id₋ = refl

CofiberSeqExt₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Type ℓ
CofiberSeqExt₋ {B = B} S = B

CofiberSeqExt-Eq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqExt₋ S ≃ B
CofiberSeqExt-Eq₋ = idEquiv _

CofiberSeqExt-Id₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                     → CofiberSeqExt₋ S ≡ B
CofiberSeqExt-Id₋ = refl

CofiberSeqCof₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Pointed ℓ
CofiberSeqCof₋ {C = C} S = C

CofiberSeqCof-Eq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqCof₋ S ≃∙ C
CofiberSeqCof-Eq₋ = idEquiv∙ _

CofiberSeqCof-Id₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                     → CofiberSeqCof₋ S ≡ C
CofiberSeqCof-Id₋ = refl

CofiberSeqInc₋ : {A B : Type ℓ} {C : Pointed ℓ} (S : CofiberSeq₋ A B C)
                  → ((CofiberSeqDom₋ S) → (CofiberSeqExt₋ S))
CofiberSeqInc₋ S = CofiberSeq₋.incl S

CofiberSeqProj₋ : {A B : Type ℓ} {C : Pointed ℓ} (S : CofiberSeq₋ A B C)
                   → ((CofiberSeqExt₋ S) → typ (CofiberSeqCof₋ S))
CofiberSeqProj₋ S = CofiberSeq₋.proj S

cofiber-CofiberSeq₋ : {A B : Type ℓ} (f : A → B)
    → CofiberSeq₋ A B (cofib f , inl tt)
CofiberSeq₋.incl (cofiber-CofiberSeq₋ f) = f
CofiberSeq₋.proj (cofiber-CofiberSeq₋ f) = cofiberMap f
CofiberSeq₋.eqCof (cofiber-CofiberSeq₋ f) = refl

cofiber₋-isPushout' : {A B : Type ℓ} (f : A → B)
  → typ (CofiberSeqCof₋ (cofiber-CofiberSeq₋ f))
     ≡ Pushout (λ _ → tt) f
cofiber₋-isPushout' f = refl

cofiber₋-isPushout : {A B : Type ℓ} (f : A → B)
  → typ (CofiberSeqCof₋ (cofiber-CofiberSeq₋ f))
     ≡ Pushout {B = Unit* {ℓ}} (λ _ → tt*) f
cofiber₋-isPushout {ℓ} f =
  cofiber₋-isPushout' f
  ∙ ua (isoToEquiv
       (pushoutLevelMix^* (λ _ → tt) (λ _ → tt*) f
                          (invIso unitLevelMix^) unitLevelMix'^))

cofiber₋-isPushout∙ : {A B : Type ℓ} (f : A → B)
  → CofiberSeqCof₋ (cofiber-CofiberSeq₋ f)
   ≡ (Pushout {B = Unit* {ℓ}} (λ _ → tt*) f , inl tt*)
cofiber₋-isPushout∙ f =
  ua∙ (isoToEquiv (pushoutLevelMix^* (λ _ → tt) (λ _ → tt*) f
                   (invIso unitLevelMix^) unitLevelMix'^))
      refl



Cof₋-isPushout : {A B : Type ℓ} {C : Pointed ℓ} (S : CofiberSeq₋ A B C)
  → typ (CofiberSeqCof₋ S)
   ≡ Pushout {B = Unit* {ℓ}} (λ _ → tt*) (CofiberSeq₋.incl S)
Cof₋-isPushout S = (λ i → typ (fst (CofiberSeq₋.eqCof S i)))
                 ∙ cofiber₋-isPushout (CofiberSeq₋.incl S)

Cof₋-isPushout∙ : {A B : Type ℓ} {C : Pointed ℓ} (S : CofiberSeq₋ A B C)
  → CofiberSeqCof₋ S
   ≡ (Pushout {B = Unit* {ℓ}} (λ _ → tt*) (CofiberSeq₋.incl S) , inl tt*)
Cof₋-isPushout∙ S = (λ i → fst (CofiberSeq₋.eqCof S i))
                   ∙ cofiber₋-isPushout∙ (CofiberSeq₋.incl S)

cofiber-CofiberSeqInc₋ : {A B : Type ℓ} (f : A → B)
    → f ≡ equivFun (CofiberSeqExt-Eq₋ {S = cofiber-CofiberSeq₋ f})
           ∘ CofiberSeqInc₋ (cofiber-CofiberSeq₋ f)
           ∘ invEq (CofiberSeqDom-Eq₋ {S = cofiber-CofiberSeq₋ f})
cofiber-CofiberSeqInc₋ f = refl

isFinCWCofiberSeq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → (isFinCW (CofiberSeqDom₋ S))
                      → (isFinCW (CofiberSeqExt₋ S))
                      → (isFinCW (typ (CofiberSeqCof₋ S)))
isFinCWCofiberSeq₋ {S = S} hA hB =
  transport (λ i → isFinCW (typ (fst (CofiberSeq₋.eqCof S (~ i)))))
  (transport (λ i → isFinCW (cofiber₋-isPushout (CofiberSeq₋.incl S) (~ i)))
            (isFinCWPushout (λ _ → tt*) (CofiberSeq₋.incl S) hA isFinCWUnit hB))

cofiberDom-isFinCWCofiberSeq₋ : {A B : Type ℓ} (f : A → B)
                                  → isFinCW A
                                  → isFinCW (CofiberSeqDom₋
                                       (cofiber-CofiberSeq₋ f))
cofiberDom-isFinCWCofiberSeq₋ f x = x


cofiberExt-isFinCWCofiberSeq₋ : {A B : Type ℓ} (f : A → B)
                                  → isFinCW B
                                  → isFinCW (CofiberSeqExt₋
                                       (cofiber-CofiberSeq₋ f))
cofiberExt-isFinCWCofiberSeq₋ = λ f x → x

CofiberSeqMap-mix : {A B : Type ℓ} {C A' B' C' : Pointed ℓ}
    (S : CofiberSeq₋ A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom₋ S) → typ (CofiberSeqDom S'))
    (g : (CofiberSeqExt₋ S) → typ (CofiberSeqExt S'))
    → (g ∘ CofiberSeqInc₋ S) ≡ ((fst (CofiberSeqInc S')) ∘ f)
    → ((CofiberSeqCof₋ S) →∙ (CofiberSeqCof S'))
CofiberSeqMap-mix S S' f g H =
  transport (λ i → (Cof₋-isPushout∙ S (~ i)) →∙ (Cof-isPushout∙ S' (~ i)))
            ((Pushout→ (λ _ → tt*) (CofiberSeq₋.incl S) (λ _ → tt*)
                        (fst (CofiberSeq.incl S')) f (λ _ → tt*)
                        g refl H)
            , refl)

CofiberSeqMapConn-mix : (n : ℕ) {A B : Type ℓ} {C A' B' C' : Pointed ℓ}
    (S : CofiberSeq₋ A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom₋ S) → typ (CofiberSeqDom S'))
    (g : (CofiberSeqExt₋ S) → typ (CofiberSeqExt S'))
    (p : (g ∘ CofiberSeqInc₋ S) ≡ ((fst (CofiberSeqInc S')) ∘ f))
    → isConnectedFun n f
    → isConnectedFun (1 + n) g
    → isConnectedFun (1 + n) (fst (CofiberSeqMap-mix S S' f g p))
CofiberSeqMapConn-mix n S S' f g p hf hg =
  isConnectedTrnspConnected* (λ i → typ (Cof-isPushout∙ S' (~ i)))
                             (λ i → typ (Cof₋-isPushout∙ S (~ i)))
    (Pushout→ (λ _ → tt*) (CofiberSeq₋.incl S) (λ _ → tt*)
               (fst (CofiberSeq.incl S')) f (λ _ → tt*) g refl p)
    (isConnectedPushout→ (λ _ → tt*) (CofiberSeq₋.incl S) (λ _ → tt*)
       (fst (CofiberSeq.incl S')) f (λ _ → tt*) g refl p n hf
       (isEquiv→isConnected (λ _ → tt*)
         (isoToIsEquiv (iso (λ _ → tt*) (λ _ → tt*)
          (λ _ → refl) (λ _ → refl))) (1 + n))
        hg)

CofiberSeqMap-cofiber : {A B : Type ℓ} {A' B' C' : Pointed ℓ}
    (m : A → B) (S' : CofiberSeq A' B' C')
    (f : A → typ (CofiberSeqDom S'))
    (g : B → typ (CofiberSeqExt S'))
    → (g ∘ m) ≡ ((fst (CofiberSeqInc S')) ∘ f)
    → ((CofiberSeqCof₋ (cofiber-CofiberSeq₋ m)) →∙ (CofiberSeqCof S'))
CofiberSeqMap-cofiber m S' f g H =
  CofiberSeqMap-mix (cofiber-CofiberSeq₋ m) S' f g H

CofiberSeqMapConn-cofiber : (n : ℕ) {A B : Type ℓ} {A' B' C' : Pointed ℓ}
    (m : A → B) (S' : CofiberSeq A' B' C')
    (f : A → typ (CofiberSeqDom S'))
    (g : B → typ (CofiberSeqExt S'))
    (p : (g ∘ m) ≡ ((fst (CofiberSeqInc S')) ∘ f))
    → isConnectedFun n f
    → isConnectedFun (1 + n) g
    → isConnectedFun (1 + n) (fst (CofiberSeqMap-cofiber m S' f g p))
CofiberSeqMapConn-cofiber n m S' f g p hf hg =
  CofiberSeqMapConn-mix n (cofiber-CofiberSeq₋ m) S' f g p hf hg

CofiberSeq₋→CofiberSeq : {A B C : Pointed ℓ}
    (S : CofiberSeq₋ (typ A) (typ B) C)
    (p : equivFun (CofiberSeqExt-Eq₋ {S = S})
           (CofiberSeqInc₋ S
            (invEq (CofiberSeqDom-Eq₋ {S = S}) (pt A))) ≡ pt B)
  → CofiberSeq A B C
CofiberSeq.incl (CofiberSeq₋→CofiberSeq S p) = (CofiberSeqInc₋ S) , p
CofiberSeq.proj (CofiberSeq₋→CofiberSeq {A = A} {B = B} S p) =
  (CofiberSeqProj₋ S)
  , transport (λ i → (snd (CofiberSeq₋.eqCof S (~ i))) (pt B)
                    ≡ (snd (fst (CofiberSeq₋.eqCof S (~ i)))))
              ((push (pt A) ∙ cong inr p) ⁻¹)
CofiberSeq.eqCof (CofiberSeq₋→CofiberSeq {ℓ = ℓ} {A = A} {B = B} S p) =
  J (λ Y q → PathP (λ _ → Σ[ X ∈ Pointed ℓ ] (B →∙ X))
                    (fst Y , (snd Y
                           , transport (λ i → snd (q i) (pt B)
                                               ≡ (snd (fst (q i))))
                             ((push (pt A) ∙ cong inr p) ⁻¹)))
                    (cofiber∙ (CofiberSeq₋.incl S , p)
                    , cofiberMap∙ (CofiberSeq₋.incl S , p)))
    (ΣPathP (refl , (ΣPathP (refl , (transportRefl _)))))
    (sym (CofiberSeq₋.eqCof S))
