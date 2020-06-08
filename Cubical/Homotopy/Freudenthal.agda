{-

Freudenthal suspension theorem

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Homotopy.Freudenthal where

open import Cubical.Foundations.Everything
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
import Cubical.Data.NatMinusTwo as ℕ₋₂
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Loopspace

module _ {ℓ} (n : ℕ) {A : Pointed ℓ} (connA : isHLevelConnected (suc (suc n)) (typ A)) where

  σ : typ A → typ (Ω (∙Susp (typ A)))
  σ a = merid a ∙ merid (pt A) ⁻¹

  private
    2n+2 = suc n + suc n

    module WC (p : north ≡ north) =
      WedgeConnectivity (suc n) (suc n) A connA A connA
        (λ a b →
          ( (σ b ≡ p → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p))
          , isOfHLevelΠ 2n+2 λ _ → isOfHLevelTrunc 2n+2
          ))
        (λ a r → ∣ a , (rCancel' (merid a) ∙ rCancel' (merid (pt A)) ⁻¹) ∙ r ∣)
        (λ b r → ∣ b , r ∣)
        (funExt λ r →
          cong′ (λ w → ∣ pt A , w ∣)
            (cong (_∙ r) (rCancel' (rCancel' (merid (pt A))))
              ∙ lUnit r ⁻¹))

    fwd : (p : north ≡ north) (a : typ A)
      → hLevelTrunc 2n+2 (fiber σ p)
      → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
    fwd p a = Trunc.rec (isOfHLevelTrunc 2n+2) (uncurry (WC.extension p a))

    isEquivFwd : (p : north ≡ north) (a : typ A) → isEquiv (fwd p a)
    isEquivFwd p a .equiv-proof =
      elim.isEquivPrecompose (λ _ → pt A) (suc n)
        (λ a →
          ( (∀ t → isContr (fiber (fwd p a) t))
          , isProp→isOfHLevelSuc n (isPropΠ λ _ → isPropIsContr)
          ))

        (isHLevelConnectedPoint (suc n) connA (pt A))
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
  Code north p = hLevelTrunc 2n+2 (fiber σ p)
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
      (funExt⁻ (WC.left refl a) _ ∙ cong ∣_∣ (cong (a ,_) (lem _ _)))
    ∙ transport (PathP≡Path gluePath _ _)
      (λ i → ∣ a , (λ j k → rCancel-filler' (merid a) i j k) ∣)
    where
    gluePath : I → Type _
    gluePath i = hLevelTrunc 2n+2 (fiber (interpolate a i) (λ j → merid a (i ∧ j)))

    lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → (p ∙ q ⁻¹) ∙ q ≡ p
    lem p q = assoc p (q ⁻¹) q ⁻¹ ∙ cong (p ∙_) (lCancel q) ∙ rUnit p ⁻¹

  contractCodeSouth : (p : north ≡ south) (c : Code south p) → encode south p ≡ c
  contractCodeSouth p =
    Trunc.elim
      (λ _ → isOfHLevelPath 2n+2 (isOfHLevelTrunc 2n+2) _ _)
      (uncurry λ a →
        J (λ p r → encode south p ≡ ∣ a , r ∣) (encodeMerid a))

  isConnectedMerid : isHLevelConnectedFun 2n+2 (merid {A = typ A})
  isConnectedMerid p = encode south p , contractCodeSouth p

  isConnectedσ : isHLevelConnectedFun 2n+2 σ
  isConnectedσ =
    transport (λ i → isHLevelConnectedFun 2n+2 (interpolate (pt A) (~ i))) isConnectedMerid


FreudenthalEquiv : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ)
                → isHLevelConnected (2 + n) (typ A)
                → hLevelTrunc ((suc n) + (suc n)) (typ A)
                 ≃ hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north)))
FreudenthalEquiv n A iscon = connectedTruncEquiv _
                                                 (σ n {A = A} iscon)
                                                 (isConnectedσ _ iscon)
FreudenthalIso : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ)
                → isHLevelConnected (2 + n) (typ A)
                → Iso (hLevelTrunc ((suc n) + (suc n)) (typ A))
                       (hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north))))
FreudenthalIso n A iscon = connectedTruncIso _ (σ n {A = A} iscon) (isConnectedσ _ iscon)
