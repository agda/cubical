{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.ConnectedCovers.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function

open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.HITs.Truncation as TR

open import Cubical.Homotopy.Connected

open import Cubical.Relation.Nullary.Base

open import Cubical.Homotopy.Serre.HomotopyGroups

open import Cubical.Homotopy.Serre.ConnectedCovers.PointedEquivalences
open import Cubical.Homotopy.Serre.ConnectedCovers.TruncationLevelFacts

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base

private
  variable
    ℓ : Level

-- This should be in library
truncIsConnected : (X : Pointed ℓ) (n : ℕ) → isConnectedFun n (trunc {X = X} n)
truncIsConnected X zero _ = tt* , λ _ → refl
truncIsConnected X (suc n) =
  TR.elim (λ _ → isProp→isOfHLevelSuc n isPropIsContr)
    λ x → isOfHLevelRetractFromIso 0
             (mapCompIso (Σ-cong-iso-snd λ w → PathIdTruncIso n))
             (contrLem x n)
  where
  contrLem : (x : typ X) (n : ℕ) → isContr (∥ (Σ[ a ∈ fst X ] ∥ a ≡ x ∥ n) ∥ (suc n))
  contrLem x n .fst = ∣ x , ∣ refl ∣ₕ ∣
  contrLem x n .snd =
    TR.elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
      (uncurry λ a →
        TR.elim (λ _ → isOfHLevelPath' n (isOfHLevelTrunc (suc n)) _ _)
        (λ q → cong ∣_∣ₕ (ΣPathP (sym q , λ j → ∣ (λ i → q (~ j ∨ i)) ∣ₕ))))

-- n+2 (or n, depending on the convention) connected cover
_<_> : (X : Pointed ℓ) → ℕ → Pointed ℓ
X < zero > = fiber∙ {A = X} (trunc∙ 2)
X < suc n > = fiber∙ {A = X < n >} (trunc∙ (3 + n))

ConnCovEqFiberZero : (X : Pointed ℓ)
  → (X < 0 >) ≡ (fiber∙ {A = X} (trunc∙ 2))
ConnCovEqFiberZero X = refl

ConnCovEqFiberConnCov : (X : Pointed ℓ) (n : ℕ)
  → (X < (suc n) >) ≡ (fiber∙ {A = X < n >} (trunc∙ (3 + n)))
ConnCovEqFiberConnCov X n = refl


ConnCovEqFiberConnCovTypZero : (X : Pointed ℓ)
  → typ (X < 0 >) ≡ typ (fiber∙ {A = X} (trunc∙ 2))
ConnCovEqFiberConnCovTypZero X = refl

ConnCovEqFiberConnCovTyp : (X : Pointed ℓ) (n : ℕ)
  → typ (X < (suc n) >) ≡ typ (fiber∙ {A = X < n >} (trunc∙ (3 + n)))
ConnCovEqFiberConnCovTyp X n = refl


ConnCovIsConn : (X : Pointed ℓ) (n : ℕ)
  → isConnected (2 + n) (typ (X < n >))
ConnCovIsConn X zero = truncIsConnected X 2 (trunc {X = X} 2 (pt X))
ConnCovIsConn X (suc n) =
  truncIsConnected (X < n >) (3 + n) (trunc {X = X < n >} (3 + n) (pt (X < n >)))

ConnCovEqFiber : (X : Pointed ℓ) (n : ℕ) →
  (X < n >) ≡ (fiber∙ {A = X} (trunc∙ (2 + n)))
ConnCovEqFiber X zero = ConnCovEqFiberZero X
ConnCovEqFiber X (suc n) = ConnCovEqFiberConnCov X n ∙
  ua∙' (fiber∙ (trunc∙ (3 + n))) (fiber∙ (trunc∙ (3 + n)))
  (fiber∙ (trunc∙ (3 + n))
 ≃∙⟨
     ΣFamBaseChange
     ( hLevelTrunc∙ (3 + n))
     ( λ A → trunc∙ (3 + n))
     ( au∙ (X < n >) (fiber∙ {A = X} (trunc∙ (2 + n))) ( ConnCovEqFiber X n))
   ⟩
  (Σ (typ (fiber∙ {A = X} (trunc∙ (2 + n))))
  (truncFam
   ( 3 + n)
   { A* = fiber∙ {A = X} (trunc∙ (2 + n))})
  , (pt X , refl) , refl)
 ≃∙⟨
     ΣAssoc∙ refl refl
   ⟩
  (Σ (typ X) (λ x →
  Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
   trunc
   { X = fiber∙ {A = X} (trunc∙ (2 + n))}
   ( 3 + n)
   ( x , p)
  ≡ trunc
    { X = fiber∙ {A = X} (trunc∙ (2 + n))}
    ( 3 + n)
    ( pt X , refl))) ,
   pt X , refl , refl
 ≃∙⟨ -- **opens a long block in the pointed equivalence proof**
     Σ∙FibEq
     (      ( (λ x →
                  Σ[ p ∈ trunc {X = X} (2 + n) x
                       ≡ trunc {X = X} (2 + n) (pt X) ]
                    trunc
                    { X = fiber∙ {A = X} (trunc∙ (2 + n))}
                    ( 3 + n)
                    ( x , p)
                  ≡ trunc
                    { X = fiber∙ {A = X} (trunc∙ (2 + n))}
                    ( 3 + n)
                    ( pt X , refl))
            , (refl , refl))
       ≃∙F⟨
            ( λ x →
                 Σ-cong-equiv-snd
                 ( λ p → isoToEquiv (PathIdTruncIso (2 + n))))
            , ΣPathP (refl , (cong ∣_∣ₕ (transportRefl refl)))
          ⟩
       (    ( (λ x →
                  Σ[ p ∈ trunc {X = X} (2 + n) x
                       ≡ trunc {X = X} (2 + n) (pt X) ]
                    hLevelTrunc (2 + n)
                    ( (x , p)
                    ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)})))
            , (refl , ∣ refl ∣ₕ))
       ≃∙F⟨
            ( λ x →
                 invEquiv
                 ( truncIdempotent≃ (2 + n)
                   ( isOfHLevelΣ (2 + n)
                     ( isOfHLevelSuc (1 + n)
                       ( isOfHLevelPath' (1 + n)
                         ( isOfHLevelTrunc (2 + n)) _ _))
                     ( λ _ → isOfHLevelTrunc (2 + n)))))
            , refl
          ⟩
       (    ( (λ x →
                  hLevelTrunc (2 + n)
                  ( Σ[ p ∈ trunc {X = X} (2 + n) x
                         ≡ trunc {X = X} (2 + n) (pt X) ]
                      hLevelTrunc (2 + n)
                      ( (x , p)
                      ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)}))))
            , (∣ refl , ∣ refl ∣ₕ ∣ₕ))
       ≃∙F⟨
            ( λ x →
                 invEquiv (isoToEquiv (truncOfΣIso (2 + n))))
            , refl
          ⟩
       (    ( (λ x →
                  hLevelTrunc (2 + n)
                  ( Σ[ p ∈ trunc {X = X} (2 + n) x
                         ≡ trunc {X = X} (2 + n) (pt X) ]
                     ( (x , p)
                     ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)}))))
            , (∣ refl , refl ∣ₕ))
       ≃∙F⟨ --opens a long block
            hLevelCong≃∙F (2 + n) _ _
            ( ΣΣ∙FibEq
              (     ( (λ x p →
                            (x , p)
                          ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)}))
                    , refl)
              ≃∙FF⟨
                    ( λ x p → invEquiv ΣPathP≃PathPΣ)
                    , refl
                  ⟩
              (     ( (λ x p →
                            Σ[ q ∈ x ≡ pt X ]
                             PathP
                             ( λ i → trunc {X = X} (2 + n) (q i)
                                    ≡ trunc {X = X} (2 + n) (pt X))
                             ( p)
                             ( refl))
                    , (refl , refl))
              ≃∙FF⟨
                    ( λ x p → Σ-cong-equiv-snd
                               ( λ q →
                                    PathP≃Path
                                    ( λ i → trunc {X = X} (2 + n) (q i)
                                           ≡ trunc {X = X} (2 + n) (pt X))
                                    ( p)
                                    ( refl)))
                    , refl
                  ⟩
              (     ( (λ x p →
                            Σ[ q ∈ x ≡ pt X ]
                             transport
                             ( λ i → trunc {X = X} (2 + n) (q i)
                                    ≡ trunc {X = X} (2 + n) (pt X))
                             ( p)
                             ≡ refl)
                    , (refl , fromPathP refl)) ≃∙FF∎))))
          ⟩ --closes a long block
       (    ( (λ x →
                  hLevelTrunc (2 + n)
                  ( Σ[ p ∈ trunc {X = X} (2 + n) x
                         ≡ trunc {X = X} (2 + n) (pt X) ]
                    Σ[ q ∈ x ≡ pt X ]
                     transport
                     ( λ i → trunc {X = X} (2 + n) (q i)
                            ≡ trunc {X = X} (2 + n) (pt X))
                     ( p)
                     ≡ refl))
            , (∣ refl , (refl , fromPathP refl) ∣ₕ))
       ≃∙F⟨
            ( λ x →
                 cong≃
                 ( hLevelTrunc (2 + n))
                 ( ΣSwapNested))
            , transportRefl (∣ refl , (refl , fromPathP refl) ∣ₕ)
          ⟩
       (    ( (λ x →
                  hLevelTrunc (2 + n)
                  ( Σ[ q ∈ x ≡ pt X ]
                    Σ[ p ∈ trunc {X = X} (2 + n) x
                         ≡ trunc {X = X} (2 + n) (pt X) ]
                     transport
                     ( λ i → trunc {X = X} (2 + n) (q i)
                            ≡ trunc {X = X} (2 + n) (pt X))
                     ( p)
                     ≡ refl))
            , (∣ refl , (refl , fromPathP refl) ∣ₕ))
       ≃∙F⟨
            ( λ x →
                 cong≃
                 ( hLevelTrunc (2 + n))
                 ( Σ-contractSnd
                   ( transportOfPathPathContr X x (1 + n) (2 + n))))
            , transportRefl ∣ refl ∣ₕ
          ⟩
       (    ( (λ x → hLevelTrunc (2 + n) (x ≡ pt X))
            , ∣ refl ∣ₕ)
       ≃∙F⟨
            ( λ x →
                 invEquiv (isoToEquiv (PathIdTruncIso (2 + n))))
            , refl
          ⟩
       (    ( (λ x → trunc {X = X} (3 + n) x ≡ trunc {X = X} (3 + n) (pt X))
            , refl)
       ≃∙F∎))))))))
   ⟩ -- **closes the long block in the pointed equivalence proof**
  fiber∙ {A = X} (trunc∙ (3 + n)) ∎≃∙)


ConnCovFiberSeqZero : (X : Pointed ℓ)
  → FiberSeq (X < 0 >) X (hLevelTrunc∙ 2 X)
ConnCovFiberSeqZero X =
  FiberEqFiberSeq
  ( ConnCovEqFiberZero X)
  ( FiberFiberSeq (trunc∙ 2))


ConnCovFiberSeq : (X : Pointed ℓ) (n : ℕ)
  → FiberSeq (X < (suc n) >) (X < n >) (hLevelTrunc∙ (3 + n) (X < n >))
ConnCovFiberSeq X n =
  FiberEqFiberSeq
  ( ConnCovEqFiberConnCov X n)
  ( FiberFiberSeq
    ( trunc∙ (3 + n)))

AlternativeFiberSeq : (X : Pointed ℓ) (n : ℕ)
   → FiberSeq (X < (suc n) >) X (hLevelTrunc∙ (3 + n) X)
AlternativeFiberSeq X n =
  FiberEqFiberSeq
  ( ConnCovEqFiber X (suc n) ⁻¹)
  ( FiberFiberSeq (trunc∙ (3 + n)))


Conn→Eq≥ConnCov : (X : Pointed ℓ) (m n : ℕ) → m ≥ (2 + n)
  → isConnected m (typ X) → X ≡ (X < n >)
Conn→Eq≥ConnCov X m zero (k , p) cX =
  ContrBase→TotalEqFib
  ( isConnectedSubtr 2 k (transport (λ i → isConnected (p (~ i)) (typ X)) cX))
  ( ConnCovFiberSeqZero X) ⁻¹
Conn→Eq≥ConnCov X m (suc n) (k , p) cX =
  ContrBase→TotalEqFib
  ( isConnectedSubtr (3 + n) k
    ( transport (λ i → isConnected (p (~ i)) (typ X)) cX))
  ( AlternativeFiberSeq X n) ⁻¹


1ConnCovEq : (X : Pointed ℓ) (scX : isConnected 3 (typ X))
  → X ≡ (X < 1 >)
1ConnCovEq X scX = Conn→Eq≥ConnCov X 3 1 (0 , refl) scX


Conn→Conn<ConnCov : (X : Pointed ℓ) (m n : ℕ) → (m < (2 + n))
  → isConnected m (typ X) → isConnected m (typ (X < n >))
Conn→Conn<ConnCov X m n (k , k+m+1≡2+n) cX =
  isConnectedSubtr m (k + 1)
  ( transport
    ( λ i → isConnected ((((+-assoc k 1 m) ⁻¹) ∙ k+m+1≡2+n) (~ i))
    ( typ (X < n >)))
    ( ConnCovIsConn X n))


Conn→Conn≥ConnCov : (X : Pointed ℓ) (m n : ℕ) → (m ≥ (2 + n))
  → isConnected m (typ X) → isConnected m (typ (X < n >))
Conn→Conn≥ConnCov X m n hmn cX =
  transport (λ i → isConnected m (typ ((Conn→Eq≥ConnCov X m n hmn cX) i))) cX


Conn→Dec≥→ConnConnCov : (X : Pointed ℓ) (m n : ℕ) → Dec (m ≥ (2 + n))
  → isConnected m (typ X) → isConnected m (typ (X < n >))
Conn→Dec≥→ConnConnCov X m n (yes p) cX =
  Conn→Conn≥ConnCov X m n p cX
Conn→Dec≥→ConnConnCov X m n (no ¬p) cX =
  Conn→Conn<ConnCov X m n (≱→< m (2 + n) ¬p) cX


Conn→ConnConnCov : (X : Pointed ℓ) (m n : ℕ)
  → isConnected m (typ X) → isConnected m (typ (X < n >))
Conn→ConnConnCov X m n = Conn→Dec≥→ConnConnCov X m n (≤Dec (2 + n) m)
