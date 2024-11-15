{-
This file contains a definition of the co-H-space structure on
joins and a proof that it is equivalent to that on suspensions
-}

{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.Join.CoHSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma renaming (fst to proj₁; snd to proj₂)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sum

open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)

open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Pushout
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓ' ℓ'' : Level

open Iso

-- Standard loop in Ω (join A B)
ℓ* : (A : Pointed ℓ) (B : Pointed ℓ')
  → fst A → fst B → Ω (join∙ A B) .fst
ℓ* A B a b = push (pt A) (pt B)
           ∙ (push a (pt B) ⁻¹ ∙∙ push a b ∙∙ (push (pt A) b ⁻¹))

ℓ*IdL : (A : Pointed ℓ) (B : Pointed ℓ')
  → (b : fst B) → ℓ* A B (pt A) b ≡ refl
ℓ*IdL A B b =
  cong₂ _∙_ refl
            (doubleCompPath≡compPath _ _ _
            ∙ cong (push (pt A) (pt B) ⁻¹ ∙_) (rCancel _)
            ∙ sym (rUnit _))
  ∙ rCancel _

ℓ*IdR : (A : Pointed ℓ) (B : Pointed ℓ')
  → (a : typ A) → ℓ* A B a (pt B) ≡ refl
ℓ*IdR A B a =
    cong₂ _∙_ refl
            (doubleCompPath≡compPath _ _ _
            ∙ assoc _ _ _
            ∙ cong (_∙ push (pt A) (pt B) ⁻¹) (rCancel _)
            ∙ sym (lUnit _))
  ∙ rCancel _

-- Addition of functions join A B → C
_+*_ : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (f g : join∙ A B →∙ C) → join∙ A B →∙ C
fst (_+*_ {C = C} f g) (inl x) = pt C
fst (_+*_ {C = C} f g) (inr x) = pt C
fst (_+*_ {A = A} {B = B} f g) (push a b i) =
  (Ω→ f .fst (ℓ* A B a b) ∙ Ω→ g .fst (ℓ* A B a b)) i
snd (f +* g) = refl

-- Inversion
-* : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
     (f : join∙ A B →∙ C) → join∙ A B →∙ C
fst (-* {C = C} f) (inl x) = pt C
fst (-* {C = C} f) (inr x) = pt C
fst (-* {A = A} {B} f) (push a b i) = Ω→ f .fst (ℓ* A B a b) (~ i)
snd (-* f) = refl

-- Iterated inversion
-*^ : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
      (n : ℕ) (f : join∙ A B →∙ C)
     → join∙ A B →∙ C
-*^ n = iter n -*

-- Neutral element
0* : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  → join∙ A B →∙ C
0* = const∙ _ _

-- Mapping space join∙ A B →∙ C is equivalent to Susp (A ⋀ B) →∙ C
fromSusp≅fromJoin : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
   → Iso (Susp∙ (A ⋀ B) →∙ C) (join∙ A B →∙ C)
fromSusp≅fromJoin {A = A} {B = B} =
  post∘∙equiv (isoToEquiv SmashJoinIso , sym (push (pt A) (pt B)))

-- Goal now: show that this is an equivalence of H-spaces

-- Technical lemma
Ω→ℓ⋀ : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
    (f : join∙ A B →∙ C)
    (x : fst A) (y : fst B)
  → Ω→ f .fst (ℓ* A B x y)
   ≡ Ω→ (inv fromSusp≅fromJoin f) .fst (σ (A ⋀∙ B) (inr (x , y)))
Ω→ℓ⋀ f x y =
   (cong₃ _∙∙_∙∙_ (symDistr _ _)
                  (cong-∙ (fst (inv fromSusp≅fromJoin f)) _ _ ∙ cong₂ _∙_ refl refl)
                  refl
  ∙ doubleCompPath≡compPath _ _ _
  ∙ sym (assoc _ _ _)
  ∙ cong (snd f ⁻¹ ∙_) (assoc _ _ _ ∙ assoc _ _ _)
  ∙ sym (doubleCompPath≡compPath _ _ _)
  ∙ cong₃ _∙∙_∙∙_
      refl
      (sym (assoc _ _ _)
        ∙ cong₂ _∙_ refl
          ((sym (assoc _ _ _) ∙ cong₂ _∙_ refl (rCancel _)) ∙ sym (rUnit _))
        ∙ sym (cong-∙ (fst f) _ _))
      refl) ⁻¹

-- We'll show it for the inverse function
-- Inverse function preseves neutral elements
fromSusp≅fromJoin⁻Pres0* : (A : Pointed ℓ) (B : Pointed ℓ') {C : Pointed ℓ''}
  → inv fromSusp≅fromJoin (const∙ (join∙ A B) C) ≡ const∙ _ _
fromSusp≅fromJoin⁻Pres0* A B = ΣPathP (refl , (sym (rUnit refl)))

-- Inverse function preseves +*
fromSusp≅fromJoin⁻Pres+* : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
   → (f g : join∙ A B →∙ C)
   → Iso.inv fromSusp≅fromJoin (f +* g)
   ≡ ·Susp (A ⋀∙ B) (Iso.inv fromSusp≅fromJoin f)
                     (Iso.inv fromSusp≅fromJoin g)
fromSusp≅fromJoin⁻Pres+* {A = A} {B = B} f g =
  ΣPathP ((funExt λ { north → refl
                    ; south → refl
                    ; (merid a i) j → main j a i})
        , (sym (rUnit _)
        ∙ cong sym (cong₂ _∙_ (cong (Ω→ f .fst) (ℓ*IdR A B (pt A)) ∙ Ω→ f .snd)
                              (cong (Ω→ g .fst) (ℓ*IdR A B (pt A)) ∙ Ω→ g .snd))
                 ∙ sym (rUnit _)))
    where
    main : cong (fst (f +* g) ∘ (SuspSmash→Join {A = A} {B = B})) ∘ merid
           ≡ λ a → Ω→ (Iso.inv fromSusp≅fromJoin f) .fst (σ (A ⋀∙ B) a)
                  ∙ Ω→ (Iso.inv fromSusp≅fromJoin g) .fst (σ (A ⋀∙ B) a)
    main = ⋀→Homogeneous≡ (isHomogeneousPath _ _)
           λ x y → cong-∙∙ (fst (f +* g)) _ _ _
                  ∙ cong₃ _∙∙_∙∙_
                    (cong sym (cong₂ _∙_ (cong (Ω→ f .fst) (ℓ*IdR A B x)
                              ∙  Ω→ f .snd)
                              (cong (Ω→ g .fst) (ℓ*IdR A B x)
                              ∙  Ω→ g .snd)
                              ∙ sym (rUnit refl)))
                    refl
                    (cong sym ((cong₂ _∙_ (cong (Ω→ f .fst) (ℓ*IdL A B y)
                              ∙  Ω→ f .snd)
                              (cong (Ω→ g .fst) (ℓ*IdL A B y)
                              ∙  Ω→ g .snd)
                              ∙ sym (rUnit refl))))
                  ∙ sym (rUnit _)
                  ∙ cong₂ _∙_ (Ω→ℓ⋀ f x y) (Ω→ℓ⋀ g x y)

-- Inverse function preseves inversion
fromSusp≅fromJoin⁻Pres-* :
  {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
   → (f : join∙ A B →∙ C)
   → inv fromSusp≅fromJoin (-* f)
   ≡ -Susp (A ⋀∙ B) (inv fromSusp≅fromJoin f)
fromSusp≅fromJoin⁻Pres-* {A = A} {B = B} {C = C} f =
  ΣPathP ((funExt (λ { north → refl
                     ; south → refl
                     ; (merid a i) j → lem j a i}))
        , sym (rUnit _)
        ∙ (cong (Ω→ f .fst) (ℓ*IdR A B (pt A))
         ∙ Ω→ f .snd))
  where
  lem : cong (fst (-* f) ∘ SuspSmash→Join) ∘ merid
      ≡ λ a → cong (-Susp (A ⋀∙ B) (inv fromSusp≅fromJoin f) .fst) (merid a)
  lem = ⋀→Homogeneous≡ (isHomogeneousPath _ _)
         λ x y → cong-∙∙ (fst (-* f)) _ _ _
               ∙∙ cong₃ _∙∙_∙∙_ ((cong (Ω→ f .fst) (ℓ*IdR A B x) ∙ Ω→ f .snd))
                                refl
                                (cong (Ω→ f .fst) (ℓ*IdL A B y) ∙ Ω→ f .snd)
                ∙ cong₂ _∙_ (doubleCompPath≡compPath _ _ _
                           ∙ (cong (sym (snd f) ∙_)
                                   (cong (_∙ snd f)
                               (cong sym (cong-∙ (fst f) _ _)
                               ∙ symDistr _ _
                               ∙ (cong₂ _∙_ (lUnit _
                               ∙ cong₂ _∙_ (sym (rCancel _)) refl
                                         ∙ sym (assoc _ _ _)) refl
                               ∙ sym (assoc _ _ _))
                               ∙ cong₂ _∙_
                                   refl
                                   (cong₂ _∙_ (sym (symDistr _ _)) refl)))
                           ∙ (assoc _ _ _
                           ∙ cong₂ _∙_ (assoc _ _ _ ∙ assoc _ _ _) refl)
                           ∙ sym (assoc _ _ _))
                           ∙ sym (assoc _ _ _)
                           ∙ doubleCompPath≡compPath _ _ _ ⁻¹ --
                           ∙ cong₃ _∙∙_∙∙_
                             (sym (symDistr _ _))
                              (cong sym (sym (cong-∙ (fst (inv fromSusp≅fromJoin f)) _ _)))
                                refl)
                  (sym ((cong (Ω→ (inv fromSusp≅fromJoin f) .fst)
                        (rCancel (merid (inl tt))))
                      ∙ ∙∙lCancel _))
               ∙∙ sym (cong-∙ (-Susp (A ⋀∙ B)  (inv fromSusp≅fromJoin f) .fst) _ _)
               ∙∙ rUnit _
               ∙∙  Ω→-Susp _ (inv fromSusp≅fromJoin f) (inr (x , y)) --

-- Same lemmas again, this time the other direction
fromSusp≅fromJoinPres+* :
  {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
   → (f g : Susp∙ (A ⋀ B) →∙ C)
   → Iso.fun fromSusp≅fromJoin (·Susp (A ⋀∙ B) f g)
   ≡ (Iso.fun fromSusp≅fromJoin f) +* (Iso.fun fromSusp≅fromJoin g)
fromSusp≅fromJoinPres+* {A = A} {B = B} f g =
  cong (fun fromSusp≅fromJoin)
       (cong₂ (·Susp (A ⋀∙ B))
              (sym (leftInv fromSusp≅fromJoin f))
              (sym (leftInv fromSusp≅fromJoin g)))
  ∙∙ sym (cong (fun fromSusp≅fromJoin)
               (fromSusp≅fromJoin⁻Pres+*
                 (fun fromSusp≅fromJoin f)
                 (fun fromSusp≅fromJoin g)))
  ∙∙ rightInv fromSusp≅fromJoin _

fromSusp≅fromJoinPres-* :
  {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
   → (f : Susp∙ (A ⋀ B) →∙ C)
   → fun fromSusp≅fromJoin (-Susp (A ⋀∙ B) f)
   ≡ -* (fun fromSusp≅fromJoin f)
fromSusp≅fromJoinPres-* {A = A} {B = B} f  =
    cong (fun fromSusp≅fromJoin ∘ -Susp (A ⋀∙ B))
         (sym (leftInv fromSusp≅fromJoin f))
  ∙ sym (cong (fun fromSusp≅fromJoin)
           (fromSusp≅fromJoin⁻Pres-* (fun fromSusp≅fromJoin f)))
  ∙ rightInv fromSusp≅fromJoin _

fromSusp≅fromJoinPres0* : (A : Pointed ℓ) (B : Pointed ℓ') {C : Pointed ℓ''}
   → fun fromSusp≅fromJoin (const∙ (Susp∙ (A ⋀ B)) C)
   ≡ const∙ _ _
fromSusp≅fromJoinPres0* A B = ΣPathP (refl , (sym (rUnit refl)))


--- We use the above to transport the HSpace proofs from suspensions to joins
module _ {ℓ ℓ' ℓ'' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} where
  private
    P = isoToPath (fromSusp≅fromJoin {A = A} {B = B} {C = C})
    ·Susp-+*-PathP : PathP (λ i → P i → P i → P i) (·Susp (A ⋀∙ B)) _+*_
    ·Susp-+*-PathP  =
      toPathP (funExt λ f → funExt λ g
      → transportRefl _
        ∙ (cong₂ _∘∙_ (cong₂ (·Susp (A ⋀∙ B))
                             (cong₂ _∘∙_ (transportRefl f) refl)
                             (cong₂ _∘∙_ (transportRefl g) refl)) refl)
        ∙ fromSusp≅fromJoinPres+* (inv fromSusp≅fromJoin f) (inv fromSusp≅fromJoin g)
        ∙ cong₂ _+*_ (rightInv fromSusp≅fromJoin f) (rightInv fromSusp≅fromJoin g))

    ·Susp--*-PathP : PathP (λ i → P i → P i) (-Susp (A ⋀∙ B)) -*
    ·Susp--*-PathP =
      toPathP (funExt λ x → transportRefl _
        ∙ cong₂ _∘∙_ (cong (-Susp (A ⋀∙ B)) (cong₂ _∘∙_ (transportRefl _) refl)) refl
        ∙ fromSusp≅fromJoinPres-* (inv fromSusp≅fromJoin x)
        ∙ cong -* (rightInv fromSusp≅fromJoin x))

    ·Susp-0*-PathP : PathP (λ i → P i) (const∙ _ _) (const∙ _ _)
    ·Susp-0*-PathP = symP (toPathP (cong₂ _∘∙_ (transportRefl _) refl
                          ∙ ΣPathP (refl , (sym (rUnit _)))))

  -- The laws
  +*HSpace : Σ[ r ∈ ((f : join∙ A B →∙ C) → (f +* 0*) ≡ f) ]
             Σ[ l ∈ ((f : join∙ A B →∙ C) → (0* +* f) ≡ f) ]
             r 0* ≡ l 0*
  +*HSpace =
    transport (λ i
      →  Σ[ r ∈ ((f : P i) → ·Susp-+*-PathP i f (·Susp-0*-PathP i) ≡ f) ]
          Σ[ l ∈ ((f : P i) → ·Susp-+*-PathP i (·Susp-0*-PathP i) f ≡ f) ]
           r (·Susp-0*-PathP i) ≡ l (·Susp-0*-PathP i))
      ((·SuspIdR _) , (·SuspIdL _) , (sym (·SuspIdL≡·SuspIdR _)))

  +*IdR : (f : join∙ A B →∙ C) → (f +* 0*) ≡ f
  +*IdR = +*HSpace .fst

  +*IdL : (f : join∙ A B →∙ C) → (0* +* f) ≡ f
  +*IdL = +*HSpace .snd .fst

  +*InvR : (f : join∙ A B →∙ C) → (f +* (-* f)) ≡ 0*
  +*InvR = transport (λ i → (f : P i) → ·Susp-+*-PathP i f (·Susp--*-PathP i f)
                                       ≡ ·Susp-0*-PathP i)
                     (·SuspInvR _)

  +*InvL : (f : join∙ A B →∙ C) → ((-* f) +* f) ≡ 0*
  +*InvL = transport (λ i → (f : P i) → ·Susp-+*-PathP i (·Susp--*-PathP i f) f
                                        ≡ ·Susp-0*-PathP i)
                     (·SuspInvL _)

  +*Assoc : (f g h : join∙ A B →∙ C) → (f +* (g +* h)) ≡ ((f +* g) +* h)
  +*Assoc =
    transport (λ i → (f g h : P i)
                    → ·Susp-+*-PathP i f (·Susp-+*-PathP i g h)
                    ≡ ·Susp-+*-PathP i (·Susp-+*-PathP i f g) h)
              (·SuspAssoc _)

  +*Comm : (Σ[ A' ∈ Pointed ℓ ] A ≃∙ Susp∙ (fst A'))
         ⊎ (Σ[ B' ∈ Pointed ℓ' ] B ≃∙ Susp∙ (fst B'))
    → (f g : join∙ A B →∙ C) → (f +* g) ≡ (g +* f)
  +*Comm (inl (A' , e)) =
    transport (λ i → (f g : P i)
                   → ·Susp-+*-PathP i f g
                    ≡ ·Susp-+*-PathP i g f)
             (·SuspComm' _ (A' ⋀∙ B)
                           (compEquiv∙ (⋀≃ e (idEquiv∙ B) , refl)
                           (isoToEquiv SuspSmashCommIso , refl)))
  +*Comm (inr (B' , e)) =
    transport (λ i → (f g : P i)
                   → ·Susp-+*-PathP i f g
                    ≡ ·Susp-+*-PathP i g f)
              (·SuspComm' _ (A ⋀∙ B')
                (compEquiv∙
                (compEquiv∙ (compEquiv∙ (⋀≃ (idEquiv∙ A) e , refl)
                  (isoToEquiv ⋀CommIso , refl))
                  (isoToEquiv SuspSmashCommIso , refl))
                  (congSuspEquiv (isoToEquiv ⋀CommIso) , refl)))

  -*² : (f : join∙ A B →∙ C) → -* (-* f) ≡ f
  -*² f =
    sym (+*IdR (-* (-* f)))
    ∙ cong (-* (-* f) +*_) (sym (+*InvL f))
    ∙ +*Assoc  _ _ _
    ∙ cong (_+* f) ( +*InvL (-* f))
    ∙ +*IdL f
    where
    help : (-* (-* f)) +* (-* f) ≡ f +* (-* f)
    help = +*InvL (-* f) ∙ sym (+*InvR f)

join-commFun-ℓ* : (A : Pointed ℓ) (B : Pointed ℓ') (a : fst A) (b : fst B)
  → cong join-commFun (ℓ* A B a b)
   ≡ (sym (push (pt B) (pt A)) ∙∙ sym (ℓ* B A b a) ∙∙ push (pt B) (pt A))
join-commFun-ℓ* A B a b =
    cong-∙ join-commFun (push (pt A) (pt B)) _
  ∙ cong₂ _∙_ refl (cong-∙∙ join-commFun _ _ _)
  ∙ sym (doubleCompPath≡compPath _ _ _
      ∙ cong₂ _∙_ refl
         (cong₂ _∙_ (symDistr _ _) refl
        ∙ sym (assoc _ _ _) ∙ cong₂ _∙_ refl (lCancel _)
        ∙ sym (rUnit _)))
