{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.altToFreudenthal where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace 
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Group.Base hiding (_≃_ ; Iso)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    A' : Pointed ℓ
    B' : Pointed ℓ'


test : ∀ n → hLevelTrunc (3 + n) (S₊ (1 + n)) → hLevelTrunc (3 + n) (Path (S₊ (2 + n)) north south)
test n = trRec (isOfHLevelTrunc (3 + n)) λ x → ∣ merid x ∣

isEquivMerid : ∀ n →  isHLevelConnectedFun (3 + n) (test n)
isEquivMerid n = trElim {!!} λ a → isHLevelConnectedPoint2 _ (∣ {!!} ∣ , {!a!}) {!!}
  where
  ou : (b : Path (S₊ (suc (suc n))) north south) → Iso (fiber (test n) ∣ b ∣) (fiber {A = Unit} {B = hLevelTrunc (suc (suc (suc n))) (Path (S₊ (suc (suc n))) north south)} (λ {tt → ∣ b ∣}) ∣ b ∣)
  Iso.fun (ou b) (p , q) = tt , refl
  Iso.inv (ou b) (p , q) = ∣ {!!} ∣ , {!!}
  Iso.rightInv (ou b) = {!!}
  Iso.leftInv (ou b) = {!!}
    where
    king : (b : Path (S₊ (suc (suc n))) north south) → Iso (fiber (test n) ∣ b ∣) ( hLevelTrunc (suc (suc (suc n))) (S₊ (2 + n)))
    Iso.fun (king b) (p , q) = trRec {A = (S₊ (suc n))} (isOfHLevelTrunc (3 + n)) (λ p → ∣ fun p ∣) p
      where
      fun : S₊ (suc n) → S₊ (suc (suc n))
      fun north = north
      fun south = south
      fun (merid a i) = merid (merid a i) i
    Iso.inv (king b) = {!!}
    Iso.rightInv (king b) = {!merid ? ?!}
    Iso.leftInv (king b) = {!!}

-- id : (n : ℕ) → typ ((Ω^ (1 + n)) A')
-- id zero = refl
-- id (suc n) = λ _ → refl

-- indEquiv : (n : ℕ) → ((x : S₊ (suc n)) → typ (Ω ((Ω^ n) (S₊ (suc n) , x)))) → typ (Ω (Ω ((Ω^ n) (Type₀ , S₊ (suc n)))))
-- indEquiv zero f = {!!}
-- indEquiv (suc n) f = {!!}


-- funcTypeEq : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → Iso (typ ((Ω^ (2 + n)) (Type₀ , S₊ (1 + n)))) ((x : S₊ (1 + n)) → typ ((Ω^ (1 + n)) (S₊ (1 + n) , x)))
-- Iso.fun (funcTypeEq zero) f x = {!transport  !}
-- Iso.fun (funcTypeEq (suc zero)) f x i = {!cong !}
-- Iso.fun (funcTypeEq (suc (suc n))) f x i = {!!}
-- Iso.inv (funcTypeEq n) f i = {!f north !}
-- Iso.rightInv (funcTypeEq n) = {!!}
-- Iso.leftInv (funcTypeEq n) = {!!}

-- idToIso : ∀ {ℓ} {A : Type ℓ} (p : A ≡ A) → Iso A A
-- Iso.fun (idToIso {A = A} p) = transport p
-- Iso.inv (idToIso {A = A} p) = transport (sym p)
-- Iso.rightInv (idToIso {A = A} p) = transportTransport⁻ p
-- Iso.leftInv (idToIso {A = A} p) = transport⁻Transport p

-- test : ∀ {ℓ} {A : Type ℓ} (p : A ≡ A) → (typ (Ω ((A ≡ A) , p))) ≃ (typ (Ω ((A ≃ A) , pathToEquiv p)))
-- test {ℓ = ℓ} {A = A} p = transport (λ i → helper2 (~ i) ≃ typ (Ω ((A ≃ A) , (pathToEquiv p)))) (compEquiv (invEquiv helper3) (pathToEquiv λ i → typ (Ω (_ , transportRefl (pathToEquiv p) i))))
--   where
--   helper2 : typ (Ω ((A ≡ A) , p)) ≡ typ (Ω (Lift (A ≃ A) , transport (univalencePath {A = A} {B = A}) p ))
--   helper2 i = typ (Ω ((univalencePath {A = A} {B = A} i) , transp (λ j → univalencePath {A = A} {B = A} (j ∧ i)) (~ i) p))
--   helper3 : typ (Ω ((A ≃ A) , _))
--           ≃ typ (Ω (Lift (A ≃ A) , transport (univalencePath {A = A} {B = A}) p))
          
--   helper3 = congEquiv LiftEquiv

-- test2 : ∀ {ℓ} {A : Type ℓ} (p : A ≡ A) → typ (Ω ((A ≃ A) , pathToEquiv p)) ≃ (typ (Ω ((A → A) , transport p)))
-- test2 {A = A} p = EquivCat
--   where
--   EquivCat : (pathToEquiv p ≡ pathToEquiv p) ≃ (pathToEquiv p .fst ≡ pathToEquiv p .fst)
--   EquivCat = compEquiv (invEquiv Σ≡) helper -- {!sym ua Σ≡!} ∙ {!!} ∙ {!!}
--     where
--     helper : Σ (fst (pathToEquiv p) ≡ fst (pathToEquiv p)) (λ p₁ → PathP (λ i → isEquiv (p₁ i)) (snd (pathToEquiv p)) (snd (pathToEquiv p))) ≃ (pathToEquiv p .fst ≡ pathToEquiv p .fst)
--     helper = helper2 λ x → toPathP (isPropIsEquiv _ _ _) , λ y → {!!}
--       where
--       helper2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → isContr (B x)) → Σ A B ≃ A
--       helper2 contr = isoToEquiv (iso (λ { (a , p) → a}) (λ a → a , (contr a .fst)) (λ b → refl) λ { (a , p) i → a , (contr a .snd p) i  })

-- withJ : (p q : A ≃ B) →  Iso (Path (A ≃ B) p q) (Path (A → B) (p .fst) (q .fst))
-- Iso.fun (withJ {A = A} {B = B} p q) = cong fst
-- Iso.inv (withJ {A = A} p q) path = J (λ f r → (x : isEquiv f) → p ≡ (f , x)) (λ x i → (path i) , {!!}) refl (q .snd)
-- Iso.rightInv (withJ p q) a = {!a!}
-- Iso.leftInv (withJ p q) = {!!}

-- together : ∀ {ℓ} (n : ℕ) {A : Type ℓ} (p : A ≡ A) → (typ ((Ω^ (1 + n)) ((A ≡ A) , p))) ≃ (typ ((Ω^ (1 + n)) ((A → A) , transport p)))
-- toghelper : ∀ {ℓ} (n : ℕ) {A : Type ℓ} (p : A ≡ A) → together n p .fst (snd (Ω ((Ω^ n) ((A ≡ A) , p)))) ≡ snd (Ω ((Ω^ n) ((A → A) , transport p)))
-- toghelper zero {A = A} p = {!!}

-- toghelper (suc n) {A = A} p = {!refl!}

-- together zero {A = A} p = helper2 -- (compEquiv (test p) (test2 p))
--   where
--   helper : ∀ B p → typ (Ω ((A ≃ B) , univalence .fst p)) ≃ typ (Ω ((A → B) , transport p))
--   helper B p = isoToEquiv (iso (cong fst) {!!} {!!} {!!}) -- isoToEquiv (iso (cong fst) {!univalence .fst p!} {!!} {!!})
--   helper2 : typ (Ω ((A ≡ A) , p)) ≃ typ (Ω ((A → A) , transport p))
--   helper2 = compEquiv (congEquiv univalence) {!!}
-- together (suc n) {A = A} p = isoToEquiv helper
--   where
--   helper : Iso (typ (Ω (Ω ((Ω^ n) ((A ≡ A) , p))))) (typ (Ω (Ω ((Ω^ n) ((A → A) , transport p)))))
--   Iso.fun helper a = sym (toghelper n p) ∙ cong (together n p .fst) a ∙ toghelper n p
--   Iso.inv helper a = {!? ∙ ? ∙ ?!}
--   Iso.rightInv helper = {!!}
--   Iso.leftInv helper = {!!}

--   test6 : Iso (A ≡ A) (A ≃ A)
--   Iso.fun test6 p = transportEquiv p
--   Iso.inv test6 p = ua p
--   Iso.rightInv test6 b i = funExt (uaβ b) i ,  hcomp {!!} (transp (λ j → isEquiv (funExt (λ x → transportRefl (b .fst x)) (i ∧ j))) (~ i) (transp (λ i₁ → isEquiv (transp (λ j → ua b (i₁ ∧ j)) (~ i₁))) i0 (idIsEquiv A)))
--   Iso.leftInv test6 b = {! .fst!}


-- -- S∙ : (n : ℕ) → Pointed₀
-- -- S∙ n = (S₊ n) , north

-- -- ΩS : (n : ℕ) → Type₀
-- -- ΩS n = typ (Ω' (S₊ n , north))

-- -- promote : (n : ℕ) → S₊ n → ΩS (1 + n)
-- -- promote n north = merid north ∙ sym (merid north)
-- -- promote n south = merid south ∙ sym (merid north)
-- -- promote n (merid a i) = merid (merid a i) ∙ sym (merid north)

-- -- decode' : (n : ℕ) → hLevelTrunc (2 + n) (S₊ n) → hLevelTrunc (2 + n) (ΩS (1 + n))
-- -- decode' n = trRec (isOfHLevelTrunc (2 + n))
-- --                   λ a → ∣ promote n a ∣


-- -- Codes : (n : ℕ) → S₊ (suc n) → Type₀
-- -- Codes n north = hLevelTrunc (3 + n) (S₊ (1 + n))
-- -- Codes n south = hLevelTrunc (3 + n) (S₊ (1 + n))
-- -- Codes n (merid a i) = {!!}

-- -- SEquiv1 : (m : ℕ) → Iso (ℕ → S₊ (suc m)) (S₊ (suc m) → S₊ (suc m))
-- -- Iso.fun (SEquiv1 m) f north = north
-- -- Iso.fun (SEquiv1 m) f south = south
-- -- Iso.fun (SEquiv1 m) f (merid a i) = {!!}
-- -- Iso.inv (SEquiv1 m) f k = {!!}
-- -- Iso.rightInv (SEquiv1 m) = {!!}
-- -- Iso.leftInv (SEquiv1 m) = {!!}







-- -- -- SEquiv1 : (n : ℕ) → S₊ (suc n) → S₊ (suc n) → Iso (S₊ (suc n)) (S₊ (suc n))
-- -- -- Iso.fun (SEquiv1 n north north) north = north
-- -- -- Iso.fun (SEquiv1 n north north) south = north
-- -- -- Iso.fun (SEquiv1 n north north) (merid a i) = (merid a ∙ sym (merid north)) i
-- -- -- Iso.fun (SEquiv1 n north south) north = north
-- -- -- Iso.fun (SEquiv1 n north south) south = south
-- -- -- Iso.fun (SEquiv1 n north south) (merid a i) = merid a i
-- -- -- Iso.fun (SEquiv1 n north (merid a i)) = {!!}
-- -- -- Iso.fun (SEquiv1 n south t) = {!!}
-- -- -- Iso.fun (SEquiv1 n (merid a i) t) = {!!}
-- -- -- Iso.inv (SEquiv1 n s t) = {!!}
-- -- -- Iso.rightInv (SEquiv1 n s t) = {!!}
-- -- -- Iso.leftInv (SEquiv1 n s t) = {!!}

-- -- -- SEquiv : (n : ℕ) → S₊ (suc n) ≃ S₊ (suc n)
-- -- -- SEquiv n = isoToEquiv {!!}
-- -- --   where
-- -- --   isot : Iso (S₊ (suc n)) (S₊ (suc n))
-- -- --   Iso.fun isot north = {!!}
-- -- --   Iso.fun isot south = {!!}
-- -- --   Iso.fun isot (merid a i) = {!!}
-- -- --   Iso.inv isot = {!!}
-- -- --   Iso.rightInv isot = {!!}
-- -- --   Iso.leftInv isot = {!!}
