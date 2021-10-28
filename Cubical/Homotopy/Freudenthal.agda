{-

Freudenthal suspension theorem

-}
{-# OPTIONS --safe #-}
module Cubical.Homotopy.Freudenthal where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec ; elim to trElim)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.SmashProduct
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to ⊥-rec)

open import Cubical.HITs.S1 hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.Foundations.Equiv.HalfAdjoint

module _ {ℓ} (n : HLevel) {A : Pointed ℓ} (connA : isConnected (suc (suc n)) (typ A)) where

  private
    2n+2 = suc n + suc n

    module WC (p : north ≡ north) =
      WedgeConnectivity (suc n) (suc n) A connA A connA
        (λ a b →
          ( (σ A b ≡ p → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p))
          , isOfHLevelΠ 2n+2 λ _ → isOfHLevelTrunc 2n+2
          ))
        (λ a r → ∣ a , (rCancel' (merid a) ∙ rCancel' (merid (pt A)) ⁻¹) ∙ r ∣)
        (λ b r → ∣ b , r ∣)
        (funExt λ r →
          cong′ (λ w → ∣ pt A , w ∣)
            (cong (_∙ r) (rCancel' (rCancel' (merid (pt A))))
              ∙ lUnit r ⁻¹))

    fwd : (p : north ≡ north) (a : typ A)
      → hLevelTrunc 2n+2 (fiber (σ A) p)
      → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
    fwd p a = Trunc.rec (isOfHLevelTrunc 2n+2) (uncurry (WC.extension p a))

    isEquivFwd : (p : north ≡ north) (a : typ A) → isEquiv (fwd p a)
    isEquivFwd p a .equiv-proof =
      elim.isEquivPrecompose (λ _ → pt A) (suc n)
        (λ a →
          ( (∀ t → isContr (fiber (fwd p a) t))
          , isProp→isOfHLevelSuc n (isPropΠ λ _ → isPropIsContr)
          ))

        (isConnectedPoint (suc n) connA (pt A))
        .equiv-proof
        (λ _ → Trunc.elim
          (λ _ → isProp→isOfHLevelSuc (n + suc n) isPropIsContr)
         (λ fib →
            subst (λ k → isContr (fiber k ∣ fib ∣))
              (cong (Trunc.rec (isOfHLevelTrunc 2n+2) ∘ uncurry)
                (funExt (WC.right p) ⁻¹))
              (subst isEquiv
                (funExt (Trunc.mapId) ⁻¹)
                (idIsEquiv _)
                .equiv-proof ∣ fib ∣)
             ))
        .fst .fst a

    interpolate : (a : typ A)
      → PathP (λ i → typ A → north ≡ merid a i) (λ x → merid x ∙ merid a ⁻¹) merid
    interpolate a i x j = compPath-filler (merid x) (merid a ⁻¹) (~ i) j

  Code : (y : Susp (typ A)) → north ≡ y → Type ℓ
  Code north p = hLevelTrunc 2n+2 (fiber (σ A) p)
  Code south q = hLevelTrunc 2n+2 (fiber merid q)
  Code (merid a i) p =
    Glue
      (hLevelTrunc 2n+2 (fiber (interpolate a i) p))
      (λ
        { (i = i0) → _ , (fwd p a , isEquivFwd p a)
        ; (i = i1) → _ , idEquiv _
        })

  encode : (y : Susp (typ A)) (p : north ≡ y) → Code y p
  encode y = J Code ∣ pt A , rCancel' (merid (pt A)) ∣

  encodeMerid : (a : typ A) → encode south (merid a) ≡ ∣ a , refl ∣
  encodeMerid a =
    cong (transport (λ i → gluePath i))
      (funExt⁻ (WC.left refl a) _ ∙ λ i → ∣ a , lem (rCancel' (merid a)) (rCancel' (merid (pt A))) i ∣)
    ∙ transport (PathP≡Path gluePath _ _)
      (λ i → ∣ a , (λ j k → rCancel-filler' (merid a) i j k) ∣)
    where
    gluePath : I → Type _
    gluePath i = hLevelTrunc 2n+2 (fiber (interpolate a i) (λ j → merid a (i ∧ j)))

    lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → (p ∙ q ⁻¹) ∙ q ≡ p
    lem p q = assoc p (q ⁻¹) q ⁻¹ ∙∙ cong (p ∙_) (lCancel q) ∙∙ rUnit p ⁻¹

  contractCodeSouth : (p : north ≡ south) (c : Code south p) → encode south p ≡ c
  contractCodeSouth p =
    Trunc.elim
      (λ _ → isOfHLevelPath 2n+2 (isOfHLevelTrunc 2n+2) _ _)
      (uncurry λ a →
        J (λ p r → encode south p ≡ ∣ a , r ∣) (encodeMerid a))

  isConnectedMerid : isConnectedFun 2n+2 (merid {A = typ A})
  isConnectedMerid p = encode south p , contractCodeSouth p

  isConnectedσ : isConnectedFun 2n+2 (σ A)
  isConnectedσ =
    transport (λ i → isConnectedFun 2n+2 (interpolate (pt A) (~ i))) isConnectedMerid

isConn→isConnSusp : ∀ {ℓ} {A : Pointed ℓ} → isConnected 2 (typ A) → isConnected 2 (Susp (typ A))
isConn→isConnSusp {A = A} iscon = ∣ north ∣
                                , trElim (λ _ → isOfHLevelSuc 1 (isOfHLevelTrunc 2 _ _))
                                         (suspToPropElim (pt A) (λ _ → isOfHLevelTrunc 2 _ _)
                                         refl)

FreudenthalEquiv : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
                → isConnected (2 + n) (typ A)
                → hLevelTrunc ((suc n) + (suc n)) (typ A)
                 ≃ hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north)))
FreudenthalEquiv n A iscon = connectedTruncEquiv _
                                                 (σ A)
                                                 (isConnectedσ _ iscon)
FreudenthalIso : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
                → isConnected (2 + n) (typ A)
                → Iso (hLevelTrunc ((suc n) + (suc n)) (typ A))
                      (hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north))))
FreudenthalIso n A iscon = connectedTruncIso _ (σ A) (isConnectedσ _ iscon)


{- connectedness of congⁿ σ (called suspMapΩ here) -}
∙∙lCancel-fill : ∀ {ℓ} {A : Type ℓ} {x y : A}
         → (p : x ≡ y)
         → I → I → I → A
∙∙lCancel-fill p i j k =
  hfill (λ k → λ { (i = i1) → p k
                  ; (j = i0) → p k
                  ; (j = i1) → p k})
        (inS (p i0)) k

∙∙lCancel : ∀ {ℓ} {A : Type ℓ} {x y : A}
         → (p : x ≡ y)
         → sym p ∙∙ refl ∙∙ p ≡ refl
∙∙lCancel p i j = ∙∙lCancel-fill p i j i1

suspMapΩ∙ : ∀ {ℓ} {A : Pointed ℓ}(n : ℕ)
        → ((Ω^ n) A)
        →∙ ((Ω^ (suc n)) (Susp∙ (typ A)))
fst (suspMapΩ∙ {A = A} zero) a = merid a ∙ sym (merid (pt A))
snd (suspMapΩ∙ {A = A} zero) = rCancel (merid (pt A))
fst (suspMapΩ∙ {A = A} (suc n)) p = sym (snd (suspMapΩ∙ n)) ∙∙ cong (fst (suspMapΩ∙ n)) p ∙∙ snd (suspMapΩ∙ n)
snd (suspMapΩ∙ {A = A} (suc n)) = ∙∙lCancel (snd (suspMapΩ∙ n))

suspMapΩ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
         → typ ((Ω^ n) A) → typ ((Ω^ (suc n)) (Susp∙ (typ A)))
suspMapΩ {A = A} n = suspMapΩ∙ {A = A} n .fst

isConnectedCong' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x : A} {y : B}
     (n : ℕ) (f : A → B)
  → isConnectedFun (suc n) f
  → (p : f x ≡ y)
  → isConnectedFun n
      λ (q : x ≡ x) → sym p ∙∙ cong f q ∙∙ p
isConnectedCong' {x = x} n f conf p =
  transport (λ i → (isConnectedFun n
                    λ (q : x ≡ x)
                    → doubleCompPath-filler (sym p) (cong f q) p i))
    (isConnectedCong n f conf)

suspMapΩ-connected : ∀ {ℓ} (n : HLevel) (m : ℕ) {A : Pointed ℓ}
     (connA : isConnected (suc (suc n)) (typ A))
  → isConnectedFun ((suc n + suc n) ∸ m) (suspMapΩ {A = A} m)
suspMapΩ-connected n zero {A = A} connA = isConnectedσ n connA
suspMapΩ-connected n (suc m) {A = A} connA with ((n + suc n) ≟ m)
... | (lt p) = subst (λ x → isConnectedFun x (suspMapΩ {A = A} (suc m)))
                     (sym (h _ m p))
                     λ b → tt* , (λ {tt* → refl})
  where
  h : (n m : ℕ) → n < m → (n ∸ m) ≡ 0
  h zero zero p = refl
  h (suc n) zero p = ⊥-rec (¬-<-zero p)
  h zero (suc m) p = refl
  h (suc n) (suc m) p = h n m (pred-≤-pred p)
... | (eq q) = subst (λ x → isConnectedFun x (suspMapΩ {A = A} (suc m)))
                     (sym (help m) ∙ cong (_∸ m) (sym q))
                     λ b → tt* , (λ {tt* → refl})
  where
  help : (n : ℕ) → n ∸ n ≡ 0
  help zero = refl
  help (suc n) = help n
... | (gt p) = isConnectedCong' (n + suc n ∸ m) (suspMapΩ {A = A} m)
    (subst (λ x → isConnectedFun x (suspMapΩ {A = A} m))
           (sym (help (n + suc n) m p))
           (suspMapΩ-connected n m connA))
    (snd (suspMapΩ∙ m))
  where
  help : (n m : ℕ) → m < n → suc (n ∸ m) ≡ (suc n) ∸ m
  help zero zero p = refl
  help zero (suc m) p = ⊥-rec (¬-<-zero p)
  help (suc n) zero p = refl
  help (suc n) (suc m) p = (help n m (pred-≤-pred p))
