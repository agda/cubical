{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.ConnectedCovers.TruncationLevelFacts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma.Properties

open import Cubical.HITs.Truncation

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base

open import Cubical.Relation.Nullary.Base

open import Cubical.Homotopy.Serre.HomotopyGroups

private
  variable
    ℓ : Level

≱→<Dec : (m n : ℕ) → ¬ m ≥ n → (Dec (m < n)) → m < n
≱→<Dec m n x (yes p) = p
≱→<Dec m n ¬m≥n (no ¬p) = <-asym' λ n<m+1 → ¬m≥n (<-asym' ¬p)

≱→< : (m n : ℕ) → ¬ m ≥ n → m < n
≱→< m n x = ≱→<Dec m n x (<Dec m n)

≰→≥ : (m n : ℕ) → ¬ m ≤ n → n ≤ m
≰→≥ m n x = <-weaken (≱→< n m x)

equivToContr : {A B : Type ℓ} (e : A ≃ B) → isContr B → isContr A
equivToContr =
 EquivJ (λ A e → isContr _ → isContr A) λ x → x

singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' a = Σ _ (λ x → x ≡ a)

transportlemma : {A : Type ℓ} {a x : A} (p : x ≡ a)
  → transport (λ i → (p ⁻¹) i ≡ a) (λ _ → a) ≡ p
transportlemma = J (λ y p → transport (λ i → (p ⁻¹) i ≡ y) refl ≡ p)
 (transportRefl refl)

isContrSingl' : {A : Type ℓ} (a : A) → isContr (singl' a)
fst (isContrSingl' a) = a , refl
snd (isContrSingl' a) (x , p) = ΣPathP ((p ⁻¹) ,
 toPathP (transportlemma p))

concatPathEq : {X : Type ℓ} {x y z : X} (p : x ≡ y) (q : x ≡ y) (r : x ≡ z)
  → (p ≡ q) ≃ ((r ⁻¹) ∙ p ≡ (r ⁻¹) ∙ q)
concatPathEq p q =
 J (λ z r → (p ≡ q) ≃ ((r ⁻¹) ∙ p ≡ (r ⁻¹) ∙ q))
   (compEquiv (compPathlEquiv (cong (_∙ p) (symRefl ⁻¹) ∙ (lUnit p) ⁻¹))
              (compPathrEquiv (lUnit q ∙ cong (_∙ q) symRefl)))

swapPathltr : {X : Type ℓ} {x y : X} (p : x ≡ y) (q : x ≡ y)
  → (q ⁻¹ ∙ p ≡ refl) ≃ (p ≡ q)
swapPathltr =
  J (λ y p → (q : _ ≡ y) → (q ⁻¹ ∙ p ≡ refl) ≃ (p ≡ q))
    λ q → concatPathEq (q ⁻¹ ∙ refl) refl (q ⁻¹)
    ∙ₑ compEquiv
       (compPathlEquiv ((lCancel (q ⁻¹)) ⁻¹ ∙ cong ((q ⁻¹) ⁻¹ ∙_) (rUnit _)))
       (compPathrEquiv ((rUnit _) ⁻¹ ∙ (symInvo _) ⁻¹))

trunc∙ : {X : Pointed ℓ} (n : ℕ) → (X →∙ hLevelTrunc∙ n X)
trunc∙ zero = ∣_∣ₕ , refl
trunc∙ (suc n) = ∣_∣ₕ , refl

trunc : {X : Pointed ℓ} (n : ℕ) → typ X → typ (hLevelTrunc∙ n X)
trunc {X = X} n = fst (trunc∙ {X = X} n)

AbGrpTruncEq : (X : Pointed ℓ) (n : ℕ)
  → AbGroupEquiv (πAb n (hLevelTrunc∙ (4 + n) X)) (πAb n X)
AbGrpTruncEq X n =
  invGroupEquiv
  ( (isoToEquiv
     ( fst (πTruncGroupIso (1 + n))))
  , snd (πTruncGroupIso (1 + n)))

≤Dec→TruncCommutesIso : (X : Type ℓ) (m n : ℕ) → (Dec (m ≤ n))
  → Iso (hLevelTrunc n (hLevelTrunc m X)) (hLevelTrunc m (hLevelTrunc n X))
≤Dec→TruncCommutesIso X m n (yes (h , p)) =
       hLevelTrunc n (hLevelTrunc m X)
  Iso⟨
       transport
       ( λ i → Iso
                ( hLevelTrunc (p i) (hLevelTrunc m X))
                ( hLevelTrunc (h + m) (hLevelTrunc m X)))
       ( idIso)
     ⟩
       hLevelTrunc (h + m) (hLevelTrunc m X)
  Iso⟨
       truncOfTruncIso2 m h
     ⟩
       hLevelTrunc m X
  Iso⟨
       truncOfTruncIso m h
     ⟩
       hLevelTrunc m (hLevelTrunc (h + m) X)
  Iso⟨
       transport
       ( λ i → Iso
               ( hLevelTrunc m (hLevelTrunc (p (~ i)) X))
               ( hLevelTrunc m (hLevelTrunc n X)))
       ( idIso)
     ⟩
       hLevelTrunc m (hLevelTrunc n X) ∎Iso
≤Dec→TruncCommutesIso X m n (no ¬p) =
       hLevelTrunc n (hLevelTrunc m X)
  Iso⟨
       transport
       ( λ i → Iso
                ( hLevelTrunc n (hLevelTrunc (snd (≰→≥ m n ¬p) i) X))
                ( hLevelTrunc n (hLevelTrunc ((fst (≰→≥ m n ¬p)) + n) X)))
       ( idIso)
     ⟩
       hLevelTrunc n (hLevelTrunc ((fst (≰→≥ m n ¬p)) + n) X)
  Iso⟨
       invIso
       ( truncOfTruncIso n (fst (≰→≥ m n ¬p)))
     ⟩
       hLevelTrunc n X
  Iso⟨
       invIso
       ( truncOfTruncIso2 n (fst (≰→≥ m n ¬p)))
     ⟩
       hLevelTrunc ((fst (≰→≥ m n ¬p)) + n) (hLevelTrunc n X)
  Iso⟨
       transport
       ( λ i → Iso
                ( hLevelTrunc ((snd (≰→≥ m n ¬p)) (~ i)) (hLevelTrunc n X))
                ( hLevelTrunc m (hLevelTrunc n X)))
       ( idIso)
     ⟩
       hLevelTrunc m (hLevelTrunc n X) ∎Iso

TruncCommutesIso : (X : Type ℓ) (m n : ℕ)
  → Iso
     ( hLevelTrunc n (hLevelTrunc m X))
     ( hLevelTrunc m (hLevelTrunc n X))
TruncCommutesIso X m n = ≤Dec→TruncCommutesIso X m n (≤Dec m n)

m≤n→ConnToHLevelTruncConn : (X : Type ℓ) (m n : ℕ)
  → m ≤ n → isConnected n X → isConnected n (hLevelTrunc m X)
m≤n→ConnToHLevelTruncConn X m n p cX =
  transport
  ( λ i → isContr (ua (isoToEquiv (TruncCommutesIso X n m)) i))
  ( isContr→isContr∥ m cX)

m>n→ConnToHLevelTruncConn : (X : Type ℓ) (m n : ℕ)
  → n < m → isConnected n X → isConnected n (hLevelTrunc m X)
m>n→ConnToHLevelTruncConn X m n p cX =
  transport
  ( cong isContr
    ( ua
      ( truncOfTruncEq
        ( n)
        ( fst (<-weaken p)))
    ∙ cong
      ( λ m' → hLevelTrunc n (hLevelTrunc m' X))
      ( snd (<-weaken p))))
  ( cX)

Dec<nm→ConnToHLevelTruncConn : (X : Type ℓ) (m n : ℕ)
  → (Dec (n < m)) → isConnected n X → isConnected n (hLevelTrunc m X)
Dec<nm→ConnToHLevelTruncConn X m n (yes p) cX =
  m>n→ConnToHLevelTruncConn X m n p cX
Dec<nm→ConnToHLevelTruncConn X m n (no ¬p) cX =
  m≤n→ConnToHLevelTruncConn X m n (<-asym' ¬p) cX

ConnToHLevelTruncConn : (X : Type ℓ) (m n : ℕ)
  → isConnected n X → isConnected n (hLevelTrunc m X)
ConnToHLevelTruncConn X m n cX =
  Dec<nm→ConnToHLevelTruncConn X m n (<Dec n m) cX


module _ (A : Pointed ℓ) (a : typ A) (n m : ℕ) where

 substlemma :
  (q : a ≡ pt A)
  (p : (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) (pt A)))
  → subst
     ( λ a' → trunc {X = A} (suc n) a' ≡ trunc {X = A} (suc n) (pt A))
     ( q)
     ( p)
   ≡ (cong ∣_∣ₕ q) ⁻¹ ∙ p
 substlemma =
  J ( λ y q →
        ( p : (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) y)) →
           subst
           ( λ a' → trunc {X = A} (suc n) a' ≡ trunc {X = A} (suc n) y)
           ( q)
           ( p)
         ≡ (cong ∣_∣ₕ q) ⁻¹ ∙ p)
    ( λ p → transportRefl p ∙ lUnit p)

 transportPathΣEquiv : (q : a ≡ pt A)
   → (Σ[ p ∈ (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) (pt A)) ]
        ( transport
          ( λ i → (trunc {X = A} (suc n) (q i))
                ≡ (trunc {X = A} (suc n) (pt A)))
          ( p))
        ≡ refl) ≃
      (Σ[ p ∈ (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) (pt A)) ]
        ( p ≡ cong ∣_∣ₕ q))
 transportPathΣEquiv q =
   Σ-cong-equiv-snd
   ( λ p → compEquiv (compPathlEquiv ((substlemma q p) ⁻¹))
   ( swapPathltr p (cong ∣_∣ₕ q)))


 transportOfPathPathContr : (q : a ≡ pt A)
  → isContr
     ( Σ[ p  ∈ (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) (pt A)) ]
        ( (transport
           ( λ i → (trunc {X = A} (suc n) (q i))
                  ≡ (trunc {X = A} (suc n) (pt A)))
           ( p))
        ≡ refl))
 transportOfPathPathContr q =
   equivToContr
   ( transportPathΣEquiv q)
   ( isContrSingl' (cong ∣_∣ₕ q))
