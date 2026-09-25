{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.CorollariesToGanea where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.Int renaming (ℤAbGroup to ℤ)
open import Cubical.Algebra.AbGroup.Instances.IntMod renaming (ℤAbGroup/_ to ℤMod)
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Sum as ⊎ hiding (rec)

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.HITs.Join renaming (inl to inlj ; inr to inrj)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Serre.Connectedness
open import Cubical.Homotopy.Serre.SAF
open import Cubical.Homotopy.Serre.FPAbGroup
open import Cubical.Homotopy.Serre.PointedHITs

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.CofiberBase

private
  variable
    ℓ : Level

join∙-comm : {X Y : Pointed ℓ} → join∙ X Y ≡ join∙ Y X
join∙-comm = ua∙ (isoToEquiv join-comm) (sym (push _ _))

join∙^ : ℕ → (Pointed ℓ) → Pointed ℓ → Pointed ℓ
join∙^ zero F G = F
join∙^ (suc n) F G = join∙ (join∙^ n F G) G


module _ (F G : Pointed ℓ) where
  join∙^-connected : (n : ℕ)
                  → isConnected 1 (typ G)
                  → isConnected n (typ (join∙^ n F G))
  join∙^-connected zero cG = isConnectedZero (typ F)
  join∙^-connected (suc n) cG =
    transport (λ i → isConnected (+-comm n 1 i) (typ (join∙^ (suc n) F G)))
              (isConnectedJoin n 1 (n + 1) ≤-refl (join∙^-connected n cG) cG)

  join∙^-connected' : (n : ℕ)
                  → isConnected 1 (typ F)
                  → isConnected 2 (typ G)
                  → isConnected (1 + n) (typ (join∙^ n F G))
  join∙^-connected' zero cF cG = cF
  join∙^-connected' (suc n) cF cG =
    transport (λ i → isConnected (+-comm n 2 i) (typ (join∙^ (suc n) F G)))
              (isConnectedJoin (1 + n) 2 (n + 2) (≤-suc ≤-refl) (join∙^-connected' n cF cG) cG)

  join∙^-SNFnt : (m n : ℕ)
                 → stablyNFinite n F
                 → isConnected 1 (typ G)
                 → stablyNFinite (suc n) G
                 → stablyNFinite (m + n) (join∙^ m F G)
  join∙^-SNFnt zero n sF cG sG = sF
  join∙^-SNFnt (suc m) n sF cG sG =
    stablyNFiniteJoin m (m + n) 1 (suc n) ≤SumLeft (join∙^-connected m cG) (join∙^-SNFnt m n sF cG sG) cG sG (suc (m + n)) order2 order3
     where


       arthritis : suc (m + n) ≡ (m + n + 1)
       arthritis = +-comm 1 (m + n)

       order2 : suc (m + n) ≤ (m + n + 1)
       order2 = transport (λ i → suc (m + n) ≤ (arthritis i))
                          ≤-refl

       order3 : (suc (m + n)) ≤ suc (n + m)
       order3 = suc-≤-suc (transport (λ i → (m + n) ≤ (+-comm m n i))
                                    ≤-refl)

  join∙^-SNFnt' : (m n : ℕ)
                 → stablyNFinite (2 + n) F
                 → isConnected 1 (typ F)
                 → isConnected 2 (typ G)
                 → stablyNFinite (2 + n) G
                 → stablyNFinite (2 + m + n) (join∙^ m F G)
  join∙^-SNFnt' zero n sF cF cG sG = sF
  join∙^-SNFnt' (suc m) n sF cF cG sG =
    stablyNFiniteJoin (1 + m) (1 + m + n) 2 (2 + n)
    ≤SumLeft (join∙^-connected' m cF cG)
    (transport (λ i → stablyNFinite (arthritis (~ i)) (join∙^ m F G))
    (join∙^-SNFnt m (1 + n) (stablyNFiniteDrop (1 + n) sF)
    (isConnectedSubtr 1 1 cG) sG)) cG sG (2 + suc m + n) order2 order3
     where
       arthritis : suc (m + n) ≡ (m + (suc n))
       arthritis = sym (+-suc m n)

       order2 : suc (suc (suc (m + n))) ≤ suc (m + n + 2)
       order2 = 0 , +-comm 2 (suc (m + n))

       order3 : suc (suc (suc (m + n))) ≤ suc (suc (n + (suc m)))
       order3 = 0 , cong suc (cong suc (+-comm (suc m) n))

  join∙^-saf : (n : ℕ) → saf F
                       → saf G
                       → isConnected 1 (fst G)
                       → saf (join∙^ n F G)
  join∙^-saf n hF hG cG k = stablyNFiniteLower n k
                               (join∙^-SNFnt n k (hF k) cG
                                                    (hG (suc k)))

isConnected→mere-path : {X : Type ℓ} → isConnected 3 X
                                  → (x y : X)
                                  → ∥ x ≡ y ∥ 1
isConnected→mere-path isCon x y =
  rec (isProp→isSet (isOfHLevelTrunc 1))
      ∣_∣ (isConnectedPath 2 isCon x y .fst)

isConnected→mere-path' : {X : Type ℓ} → isConnected 2 X
                                   → (x y : X)
                                   → ∥ x ≡ y ∥ 1
isConnected→mere-path' isC x y =
  rec (isOfHLevelTrunc 1)
      ∣_∣ (isConnectedPath 1 isC x y .fst)

isConnected→isConnectedFun* : (n : ℕ) {X : Type ℓ}
  → isConnected n X → isConnectedFun {ℓ} {ℓ} n (λ (_ : X) → tt*)
isConnected→isConnectedFun* n isC (lift b) =
  isConnectedRetractFromIso n
    (Σ-cong-iso idIso λ x
      → invIso (congIso LiftIso))
    (isConnected→isConnectedFun n isC b)


pushoutFunEqIso : ∀ {ℓA ℓA' ℓC ℓB}
  {A : Type ℓA} {A' : Type ℓA'}
  {C : Type ℓC} {B : Type ℓB}
  (f : A → B) (g : A → C) (h : A' → B) (k : A' → C)
  (K : Iso A A')
  (q : f ≡ h ∘ Iso.fun K)
  (p : g ∘ Iso.inv K ≡ k)
  → Iso (Pushout f g) (Pushout h k)
pushoutFunEqIso f g h k K q p =
  pushoutIso f g h k (isoToEquiv K) (idEquiv _) (idEquiv _)
    q (funExt (λ x → cong g (sym (Iso.ret K x)))
    ∙ cong (_∘ Iso.fun K) p)

pushoutLevelMix : ∀ {ℓA ℓB ℓC ℓC'}
  {A : Type ℓA} {C : Type ℓC} {B : Type ℓB} {C' : Type ℓC'}
   (f : A → B) (g : A → C) (g' : A → C')
   (K : Iso C C')
   (q : Iso.fun K ∘ g ≡ g')
   → Iso (Pushout f g) (Pushout f g')
pushoutLevelMix f g g' K q =
  pushoutIso f g f g' (idEquiv _) (idEquiv _) (isoToEquiv K) refl q

unitLevelMix : Iso (Unit* {ℓ}) (Unit)
unitLevelMix = invIso LiftIso

unitLevelMix' : {B : Type ℓ}
  → (λ (x : B) → (Iso.fun (unitLevelMix {ℓ})) ((λ (_ : B) → tt*) x))
  ≡ (λ (_ : B) → tt)
unitLevelMix' = refl



join-iso-join : (X X' Y : Type ℓ)
  → Iso X X' → Iso (join X Y) (join X' Y)
join-iso-join X X' Y is = Iso→joinIso is idIso

join-iso-join∙ : (X X' Y : Pointed ℓ) (H : Iso (typ X) (typ X'))
  (p : Iso.fun H (pt X) ≡ (pt X'))
  → Iso.fun (join-iso-join (typ X) (typ X') (typ Y) H) (pt (join∙ X Y))
     ≡ (pt (join∙ X' Y))
join-iso-join∙ X X' Y H p = cong inlj p

module Ganea^ {A : Pointed ℓ} {B : Pointed ℓ} (f : A →∙ B) where

  mutual
    E : ℕ → (Pointed ℓ)
    E zero = A
    E (suc n) = fib-cofib (p n) , inr (pt (E n))

    p : (n : ℕ) → (E n →∙ B)
    p zero = f
    p (suc n) = (GaneaMap (p n)) , (snd (p n))

  sntychk : (GaneaMap f) ≡ (fst (p 1))
  sntychk = refl

  F : ℕ → (Pointed ℓ)
  F zero = fiber (fst f) (pt B) , pt A , snd f
  F (suc n) = (GaneaFib (p n)) , ((pt (E (1 + n))) , snd (p n))

  join-F : ℕ → (Pointed ℓ)
  join-F n = join∙^ n (F 0) (Ω B)

  Ganea^Iso : (n : ℕ) → Iso (fst (F n)) (fst (join-F n))
  Ganea^Iso zero = idIso
  Ganea^Iso (suc zero) = GaneaIso f
  Ganea^Iso (suc (suc n)) =
    compIso (GaneaIso (p (suc n)))
            (join-iso-join (typ (F (suc n)))
                        (typ (join-F (suc n))) (typ (Ω B))
                        (Ganea^Iso (suc n)))

  Ganea^≡ : (n : ℕ) → (fst (F n)) ≡ (fst (join-F n))
  Ganea^≡ n = ua (isoToEquiv (Ganea^Iso n))

  Ganea^Iso∙ : (n : ℕ) → Iso.fun (Ganea^Iso n) (pt (F n)) ≡ (pt (join-F n))
  Ganea^Iso∙ zero = refl
  Ganea^Iso∙ (suc zero) = refl
  Ganea^Iso∙ (suc (suc n)) =
    join-iso-join∙ (F (suc n)) (join-F (suc n)) (Ω B)
                   (Ganea^Iso (suc n)) (Ganea^Iso∙ (suc n))


  Ganea^≃∙ : (n : ℕ) → (F n) ≃∙ (join-F n)
  fst (Ganea^≃∙ n) = isoToEquiv (Ganea^Iso n)
  snd (Ganea^≃∙ n) = Ganea^Iso∙ n

  Ganea^≡∙ : (n : ℕ) → (F n) ≡ (join-F n)
  Ganea^≡∙ n = ua∙ (fst (Ganea^≃∙ n)) (snd (Ganea^≃∙ n))

  GaneaCofiberSeq'₋ : (n : ℕ) → CofiberSeq₋ (typ (F n)) (typ (E n))
                                           (typ (E (1 + n)) , inl tt)
  GaneaCofiberSeq'₋ zero = cofiber-CofiberSeq₋ fst
  GaneaCofiberSeq'₋ (suc n) = cofiber-CofiberSeq₋ fst

  GaneaCofiberSeq''₋ : (n : ℕ) → CofiberSeq₋ (typ (F n)) (typ (E n))
                                    (E (1 + n))
  GaneaCofiberSeq''₋ n = transport (λ i → CofiberSeq₋ (typ (F n)) (typ (E n))
                                                (fib-cofib (p n) , push (pt (E n) , (snd (p n))) i))
                                                (GaneaCofiberSeq'₋ n)

  GaneaCofiberSeq₋ : (n : ℕ) → CofiberSeq₋ (typ (join-F n)) (typ (E n))
                                            (E (1 + n))
  GaneaCofiberSeq₋ n = transport (λ i → CofiberSeq₋ (Ganea^≡ n i) (typ (E n))
                                                     (E (1 + n)))
                                  (GaneaCofiberSeq''₋ n)

  GaneaCofiberSeq' : (n : ℕ) → CofiberSeq (F n) (E n)
                                           (typ (E (1 + n)) , inl tt)
  GaneaCofiberSeq' zero = CofiberSeq₋→CofiberSeq (GaneaCofiberSeq'₋ 0)
                          (transport (λ i → (cofiber-CofiberSeqInc₋ fst i)
                            (pt (F 0)) ≡ pt A) refl)
  GaneaCofiberSeq' (suc n) =
    CofiberSeq₋→CofiberSeq (GaneaCofiberSeq'₋ (suc n))
       (transport (λ i → (cofiber-CofiberSeqInc₋ fst i)
                          (pt (F (suc n))) ≡ pt (E (suc n))) refl)

  GaneaCofiberSeq'' : (n : ℕ) → CofiberSeq (F n) (E n)
                                    (E (1 + n))
  GaneaCofiberSeq'' n = transport (λ i → CofiberSeq (F n) (E n)
                                                (fib-cofib (p n) , push (pt (E n) , (snd (p n))) i))
                                                (GaneaCofiberSeq' n)

  GaneaCofiberSeq : (n : ℕ) → CofiberSeq (join-F n) (E n)
                                          (E (1 + n))
  GaneaCofiberSeq n =
    transport
      (λ i → CofiberSeq (ua∙ (fst (Ganea^≃∙ n)) (snd (Ganea^≃∙ n)) i)
                         (E n) (E (1 + n)))
      (GaneaCofiberSeq'' n)

safΩ→saf : {B : Pointed ℓ} (cB : isConnected 2 (typ B)) → saf (Ω B) → saf B
safΩ→saf {ℓ} {B} cB hB = γ
  where
    open Ganea^ ((λ (_ : Unit*) → (pt B)) , refl)

    ΩB-connected : isConnected 1 (typ (Ω B))
    ΩB-connected = isConnectedPath 1 cB (pt B) (pt B)

    F0-Iso : Iso (typ (F 0)) (typ (Ω B))
    Iso.fun F0-Iso (tt* , p) = p
    Iso.inv F0-Iso p = tt* , p
    Iso.sec F0-Iso = λ _ → refl
    Iso.ret F0-Iso = λ _ → refl

    F0-Eq∙ : (F 0) ≃∙ (Ω B)
    fst F0-Eq∙ = isoToEquiv F0-Iso
    snd F0-Eq∙ = refl

    F0-≡ : (F 0) ≡ (Ω B)
    F0-≡ = ua∙ (fst F0-Eq∙) (snd F0-Eq∙)

    connected-join-F' : (k : ℕ) → isConnected (suc k)
                                               (typ (join-F (suc k)))
    connected-join-F' k = join∙^-connected (F 0) (Ω B) (suc k) ΩB-connected

    connected-p : (k : ℕ) → isConnectedFun (suc k)
                                            (fst (p (suc k)))
    connected-p k b =
      rec isPropIsContr
          (λ q → transport (λ i → isConnected (suc k) (fiber (fst (p (suc k))) (q (~ i))))
          (transport (λ i → isConnected (suc k) (Ganea^≡ (suc k) (~ i)))
                     (connected-join-F' k)))
          (isConnected→mere-path' cB b (pt B))

    frthmetic : (k : ℕ) → ((suc k) + 1) ≡ (suc (suc k))
    frthmetic k = +-comm (suc k) 1

    sNFnt-join-F : (k : ℕ) → saf (join-F k)
    sNFnt-join-F k = join∙^-saf (F 0) (Ω B) k
                     (transport (cong saf (F0-≡ ⁻¹)) hB)
                     hB ΩB-connected


    sNFnt-E : (k : ℕ) → saf (E k)
    sNFnt-E zero = saf-Unit
    sNFnt-E (suc k) = safCofiber (GaneaCofiberSeq k) (sNFnt-join-F k)
                                 (sNFnt-E k)

    γ : saf B
    γ n = stablyNFiniteLower 1 n
          (stablyNFiniteApprox (p (suc n)) (suc n) (connected-p n)
           (sNFnt-E (suc n) (suc n)))







saf→safΩ : {B : Pointed ℓ} (scB : isConnected 3 (typ B)) → saf B → saf (Ω B)
saf→safΩ {ℓ} {B} scB hB = γ
  where
    open Ganea^ ((λ (_ : Unit*) → (pt B)) , refl)

    order-silly : (n : ℕ) → (3 + n) ≤ suc (n + 2)
    order-silly n = transport (λ i → (3 + n) ≤ suc (+-comm 2 n i))
                               ≤-refl


    ΩB-connected : isConnected 2 (typ (Ω B))
    ΩB-connected = isConnectedPath 2 scB (pt B) (pt B)

    ΩB-stably1Finite : stablyNFinite 1 (Ω B)
    ΩB-stably1Finite =
      stablyNFiniteApprox' ((λ _ → tt*) , refl) 1
      (isConnected→isConnectedFun* 2 ΩB-connected)
      (saf-Unit 1)

    F0-Iso : Iso (typ (F 0)) (typ (Ω B))
    Iso.fun F0-Iso (tt* , p) = p
    Iso.inv F0-Iso p = tt* , p
    Iso.sec F0-Iso = λ _ → refl
    Iso.ret F0-Iso = λ _ → refl

    F0-Eq∙ : (F 0) ≃∙ (Ω B)
    fst F0-Eq∙ = isoToEquiv F0-Iso
    snd F0-Eq∙ = refl

    F0-≡ : (F 0) ≡ (Ω B)
    F0-≡ = ua∙ (fst F0-Eq∙) (snd F0-Eq∙)

    connected-join-F : (k : ℕ) → isConnected 2 (typ (join-F k))
    connected-join-F 0 = transport (λ i → isConnected 2 (typ (F0-≡ (~ i))))
                (isConnectedPath 2 scB (pt B) (pt B))
    connected-join-F (suc k) =
      isConnectedJoin 1 1 2 ≤-refl
        (isConnectedSubtr 1 1 (connected-join-F k))
        (isConnectedSubtr 1 1 (isConnectedPath 2 scB (pt B) (pt B)))

    connected-join-F' : (k : ℕ) → isConnected (2 + k)
                                               (typ (join-F (suc k)))
    connected-join-F' k = join∙^-connected' (F 0) (Ω B) (suc k)
                          (isConnectedSubtr 1 1
                           (transport (λ i → isConnected 2 (typ (F0-≡ (~ i))))
                                      ΩB-connected))
                          ΩB-connected

    connected-p : (k : ℕ) → isConnectedFun (suc (suc k))
                                            (fst (p (suc k)))
    connected-p k b =
      rec isPropIsContr
          (λ q → transport (λ i → isConnected (2 + k) (fiber (fst (p (suc k))) (q (~ i))))
          (transport (λ i → isConnected (2 + k) (Ganea^≡ (suc k) (~ i)))
                     (connected-join-F' k)))
          (isConnected→mere-path scB b (pt B))

    connected-p' : (k : ℕ) → isConnectedFun (suc k)
                                            (fst (p (suc k)))
    connected-p' k = isConnectedFunSubtr (1 + k) 1 (fst (p (suc k))) (connected-p k)


    ΩB→Fn-stablyNFinite0 : (n : ℕ) → stablyNFinite 1 (Ω B)
      → stablyNFinite n (F n)
    ΩB→Fn-stablyNFinite0 n sΩB =
     transport (λ i → stablyNFinite (+-comm n 0 i) (Ganea^≡∙ n (~ i)))
               (join∙^-SNFnt (F 0) (Ω (fst B , pt B)) n 0
                (transport (λ i → stablyNFinite 0 (F0-≡ (~ i)))
                           (stablyNFiniteDrop 0 sΩB))
                           (isConnectedSubtr 1 1 ΩB-connected) sΩB)

    ΩB→Fn-stablyNFinite-aux : (n : ℕ) → stablyNFinite (1 + n) (Ω B)
      → ((2 ≤ (1 + n)) ⊎ (2 > (1 + n))) → stablyNFinite (3 + n) (F 1)
    ΩB→Fn-stablyNFinite-aux n H (inl p₁) =
      transport (λ i → stablyNFinite (3 + n) (Ganea^≡∙ 1 (~ i)))
        (stablyNFiniteJoin 2 (1 + n) 2 (1 + n) p₁
          (transport (λ i → isConnected 2 (typ (F0-≡ (~ i))))
           ΩB-connected)
          (transport (λ i → stablyNFinite (suc n) (F0-≡ (~ i)))
           H)
          ΩB-connected H (3 + n) (order-silly n) (order-silly n))
    ΩB→Fn-stablyNFinite-aux n H (inr p₁) =
      transport (λ i → stablyNFinite (3 + n) (Ganea^≡∙ 1 (~ i)))
        (stablyNFiniteJoin-alt 0 2 (1 + n)
          (transport (λ i → isConnected 2 (typ (F0-≡ (~ i))))
           ΩB-connected)
          (transport (λ i → stablyNFinite 1 (F0-≡ (~ i)))
          (stablyNFiniteLower n 1
           (transport (λ i → stablyNFinite (+-comm 1 n i) (Ω B))
            H)))
         ΩB-connected H (3 + n)
        (suc-≤-suc p₁) (order-silly n))

    ΩB→Fn-stablyNFinite : (n : ℕ) → stablyNFinite (1 + n) (Ω B)
      → (k : ℕ) → stablyNFinite (3 + n) (F (1 + k))
    ΩB→Fn-stablyNFinite n Hyp zero =
      ΩB→Fn-stablyNFinite-aux n Hyp (Dichotomyℕ 2 (1 + n))
    ΩB→Fn-stablyNFinite n Hyp (suc k) =
      transport (λ i → stablyNFinite (3 + n) (Ganea^≡∙ (2 + k) (~ i)))
        (stablyNFiniteJoin 2 (3 + n) 0 (1 + n)
          (≤-suc ≤SumLeft) (connected-join-F (1 + k))
          (transport (λ i → stablyNFinite (3 + n) (Ganea^≡∙ (1 + k) i))
            (ΩB→Fn-stablyNFinite n Hyp k))
              (isConnectedZero (typ (Ω B))) Hyp (3 + n)
              (transport (λ i → suc (suc (suc n)) ≤ (suc (suc (suc (+-comm 0 n i))))) ≤-refl) (order-silly n))

    ΩB→Fn-stablyNFinite0' : stablyNFinite 1 (Ω B) → stablyNFinite 4 (F 3)
    ΩB→Fn-stablyNFinite0' sΩB =
      transport (λ i → stablyNFinite 4 (Ganea^≡∙ 3 (~ i)))
      (transport (λ i → stablyNFinite 4 (join∙-comm {X = Ω B} {Y = join-F 2} i))
                 (stablyNFiniteJoin-alt 0 3 2 ΩB-connected sΩB
                 (join∙^-connected' (F 0) (Ω B) 2
                  (transport (λ i → isConnected 1 (typ (F0-≡ (~ i))))
                             (isConnectedSubtr 1 1 ΩB-connected))
                             ΩB-connected)
                 (transport (λ i → stablyNFinite 2 (Ganea^≡∙ 2 i))
                            (ΩB→Fn-stablyNFinite0 2 sΩB)) 4 ≤-refl ≤-refl))


    eventuallySNFnt : (n k : ℕ) → ((m : ℕ) → stablyNFinite k (F (suc m)))
                                → stablyNFinite k (E (suc n))
                                → stablyNFinite k (E 1)
    eventuallySNFnt zero k hypF hypE = hypE
    eventuallySNFnt (suc n) k hypF hypE =
      eventuallySNFnt n k hypF
        (stablyNFiniteExtension (GaneaCofiberSeq' (suc n))
          (hypF n) hypE)


    E1-Iso'' : Iso (typ (E 1)) (Pushout {C = Unit* {ℓ}}
                                        (λ (_ : typ (Ω B)) → tt)
                                        (λ _ → tt*))
    E1-Iso'' = pushoutFunEqIso (λ _ → tt) (λ _ → tt*)
                 (λ _ → tt) (λ r → tt*) F0-Iso refl refl

    E1-Iso' : Iso (typ (E 1)) (PushoutSusp (typ (Ω B)))
    E1-Iso' = compIso E1-Iso''
              (pushoutLevelMix (λ _ → tt) (λ _ → tt*) (λ _ → tt)
                unitLevelMix unitLevelMix')

    E1-Iso : Iso (typ (E 1)) (Susp (typ (Ω B)))
    E1-Iso = compIso E1-Iso' PushoutSuspIsoSusp

    E1-≡ : (typ (E 1)) ≡ (Susp (typ (Ω B)))
    E1-≡ = ua (isoToEquiv E1-Iso)

    E1→SuspΩB-SNFnt : (n : ℕ) → stablyNFinite n (E 1)
                               → (stablyNFinite n (S∙ (Ω B)))
    E1→SuspΩB-SNFnt n hyp = pointIrrelSNFnt n
      ((Susp (typ (Ω B))) , (Iso.fun (E1-Iso) (pt {ℓ} (E 1))))
      (pt (S∙ (Ω B))) (transport (λ i → stablyNFinite n
      (ua∙ {A = (E 1)} {B = Susp (typ (Ω B)) , fst (isoToEquiv E1-Iso)
      (snd (E 1))} (isoToEquiv E1-Iso) (refl) i)) hyp)

    γ : saf (Ω B)
    γ 0 = stablyNFiniteDrop 0 (ΩB-stably1Finite)
    γ 1 = ΩB-stably1Finite
    γ (suc (suc n)) =
      stablyNFiniteOfSusp (2 + n) (Ω B)
        (E1→SuspΩB-SNFnt (3 + n)
         (eventuallySNFnt (3 + n) (3 + n) (ΩB→Fn-stablyNFinite n (γ (suc n)))
           (stablyNFiniteApprox' (p (4 + n)) (3 + n) (connected-p' (3 + n)) (hB (3 + n)))))


safTotal : {F E B : Pointed ℓ} (S : FiberSeq F E B) (scB : isConnected 3 (typ B))
    → saf B → saf F → saf E
safTotal {ℓ} {F'} {E'} {B} S scB hB hF' k = saf-E k (suc k) (saf-En k)
  where
    open Ganea^ (FiberSeqProj S)

    ΩB-connected : isConnected 2 (typ (Ω B))
    ΩB-connected = isConnectedPath 2 scB (pt B) (pt B)


    F0-≡ : F 0 ≡ F'
    F0-≡ = fst (PathPΣ (FibsEqOfFibSeq (FiberFiberSeq (FiberSeqProj S)) S refl))

    saf-ΩB : saf (Ω B)
    saf-ΩB = saf→safΩ scB hB

    saf-Fn : (n : ℕ) → saf (join-F n)
    saf-Fn n = join∙^-saf (F 0) (Ω B) n
               (transport (λ i → saf (F0-≡ (~ i))) hF')
               saf-ΩB (isConnectedSubtr 1 1 ΩB-connected)

    connected-join-F' : (k : ℕ) → isConnected (suc k)
                                               (typ (join-F (suc k)))
    connected-join-F' k = join∙^-connected (F 0) (Ω B) (suc k)
                          (isConnectedSubtr 1 1 ΩB-connected)

    connected-p : (k : ℕ) → isConnectedFun (suc k)
                                            (fst (p (suc k)))
    connected-p k b =
      rec isPropIsContr
          (λ q → transport (λ i → isConnected (suc k) (fiber (fst (p (suc k))) (q (~ i))))
          (transport (λ i → isConnected (suc k) (Ganea^≡ (suc k) (~ i)))
                     (connected-join-F' k)))
          (isConnected→mere-path scB b (pt B))

    saf-En : (k : ℕ) → stablyNFinite k (E (suc k))
    saf-En k = stablyNFiniteApprox' (p (suc k)) k (connected-p k) (hB k)

    saf-E : (n k : ℕ) → stablyNFinite n (E k) → stablyNFinite n (E 0)
    saf-E n zero hE = hE
    saf-E n (suc k) hE =
      saf-E n k (stablyNFiniteExtension (GaneaCofiberSeq k) (saf-Fn k n)
                hE)



EMℤMod-saf : (n m : ℕ) → saf {ℓ = ℓ-zero} (EM∙ (ℤMod (suc n)) (suc m))
EMℤMod-saf n zero = safΩ→saf (isConnectedEM 1)
                    (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤMod (suc n)} 0 i))
                    (transport (λ i → saf (ua∙ {A = EM∙ (ℤMod (suc n)) 0}
                                               (ℤMod-finite n) refl (~ i)))
                               (saf-Fin (suc n) _)))
EMℤMod-saf n (suc m) =
  safΩ→saf (isConnectedSubtr 2 (1 + m)
               (transport (λ i → isConnected (+-comm 2 (1 + m) i)
                                    (typ (EM∙ (ℤMod (suc n)) (suc (suc m)))))
                          (isConnectedEM (2 + m))))
            (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤMod (suc n)} (suc m) i))
                       (EMℤMod-saf n m))

EMℤMod-saf' : (n m : ℕ) (G : AbGroup ℓ) → AbGroupIso G (ℤMod (suc n))
  → saf (EM∙ G (suc m))
EMℤMod-saf' n m G v =
  safOfIso (invIso (Iso→EMIso (GroupIso→GroupEquiv v) (suc m))) (EMℤMod-saf n m)

EMℤ-saf : (m : ℕ) → saf {ℓ = ℓ-zero} (EM∙ ℤ (suc m))
EMℤ-saf zero = transport (λ i → saf (EM₁ℤ (~ i)))
                         (saf-Sn 1)
EMℤ-saf (suc m) =
  safΩ→saf (isConnectedSubtr 2 (1 + m)
               (transport (λ i → isConnected (+-comm 2 (1 + m) i)
                                    (typ (EM∙ ℤ (2 + m))))
                          (isConnectedEM (2 + m))))
               (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤ} (suc m) i))
                         (EMℤ-saf m))

EMℤ-saf' : (m : ℕ) (G : AbGroup ℓ) → AbGroupIso G ℤ → saf (EM∙ G (suc m))
EMℤ-saf' m G v =
  safOfIso (invIso (Iso→EMIso (GroupIso→GroupEquiv v) (suc m))) (EMℤ-saf m)

saf-dir-prod : (H K : AbGroup ℓ)
  → ((n : ℕ) → saf (EM∙ H (suc n)))
  → ((n : ℕ) → saf (EM∙ K (suc n)))
  → (n : ℕ)
  → saf (EM∙ (AbDirProd H K) (suc n))
saf-dir-prod H K hH hK n =
  transport (λ i → saf (EMDirProd H K (suc n) (~ i)))
            (saf× (hH n) (hK n))

isFP→safEM : (A : AbGroup ℓ-zero) (fpA : isFP A) (n : ℕ)
  → saf (EM∙ A (suc n))
isFP→safEM =
  indFP (λ A → (n : ℕ) → saf (EM∙ A (suc n)))
        (λ A → isOfHLevelΠ 1 λ n → saf-isProp {X = EM∙ A (suc n)})
        (λ { zero m → EMℤ-saf m ; (suc n) m → EMℤMod-saf n m})
        saf-dir-prod

isFP→safEM' : (A : AbGroup ℓ) (fpA : isFP A) (n : ℕ)
  → saf (EM∙ A (suc n))
isFP→safEM' =
 indFP' (λ A → (n : ℕ) → saf (EM∙ A (suc n)))
        (λ A → isOfHLevelΠ 1 λ n → saf-isProp {X = EM∙ A (suc n)})
        (λ { zero G v m → EMℤ-saf' m G v ; (suc n) G v m → EMℤMod-saf' n m G v })
        saf-dir-prod
