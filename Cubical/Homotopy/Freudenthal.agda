{-

Freudenthal suspension theorem

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Homotopy.Freudenthal where

open import Cubical.Foundations.Everything
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Loopspace

module _ {ℓ} (n : HLevel) {A : Pointed ℓ} (connA : isConnected (suc (suc n)) (typ A)) where

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

  isConnectedMerid : isConnectedFun 2n+2 (merid {A = typ A})
  isConnectedMerid p = encode south p , contractCodeSouth p

  isConnectedσ : isConnectedFun 2n+2 σ
  isConnectedσ =
    transport (λ i → isConnectedFun 2n+2 (interpolate (pt A) (~ i))) isConnectedMerid


FreudenthalEquiv : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
                → isConnected (2 + n) (typ A)
                → hLevelTrunc ((suc n) + (suc n)) (typ A)
                 ≃ hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north)))
FreudenthalEquiv n A iscon = connectedTruncEquiv _
                                                 (σ n {A = A} iscon)
                                                 (isConnectedσ _ iscon)
FreudenthalIso : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
                → isConnected (2 + n) (typ A)
                → Iso (hLevelTrunc ((suc n) + (suc n)) (typ A))
                      (hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north))))
FreudenthalIso n A iscon = connectedTruncIso _ (σ n {A = A} iscon) (isConnectedσ _ iscon)

-- -- Tests
-- open import Cubical.Homotopy.Loopspace
-- open import Cubical.HITs.Sn

-- truncIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : HLevel)
--          → Iso A B
--          → Iso (hLevelTrunc n A) (hLevelTrunc n B)
-- Iso.fun (truncIso n i) = map (Iso.fun i)
-- Iso.inv (truncIso n i) = map (Iso.inv i)
-- Iso.rightInv (truncIso n i) = Trunc.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (Iso.rightInv i a)
-- Iso.leftInv (truncIso n i) = Trunc.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (Iso.leftInv i a)

-- π₀-S¹ : Iso (hLevelTrunc 2 (S₊ 1)) {!!}
-- π₀-S¹ = {!!}

-- LoopSpaceIso : {!!}
-- LoopSpaceIso = {!!}
-- open import Cubical.Foundations.Equiv.HalfAdjoint


-- base-change : (x : ∥ S₊ 2 ∥ 4) →  Iso (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , x))) (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- Iso.fun (base-change x) =
--   Trunc.elim {B = λ x → (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , x))) → (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))}
--              (λ _ → isOfHLevelΠ 4 {!!})
--              (λ {north → idfun _
--                ; south → transport (λ i → typ ((Ω^ 2) ((∥ S₊ 2 ∥ 4) , ∣ merid north (~ i) ∣)))
--                ; (merid north i) → {!!}
--                ; (merid south i) → {!!}
--                ; (merid (merid a j) i) → {!isOfHLevelDep!}}) x
-- Iso.inv (base-change x) = {!!}
-- Iso.rightInv (base-change x) = {!!}
-- Iso.leftInv (base-change x) = {!!}

-- FreudTest-2 : (π 3 (S₊ 3 , north)) ≡ (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- FreudTest-2 = isoToPath (compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
--                 (compIso
--                   (congIso (invIso (ΩTrunc.IsoFinal 3 ∣ refl ∣ ∣ refl ∣)))
--                   (congIso (congIso helper))))
--            ∙∙ isoToPath {!!}
--            ∙∙ {!!}
--   where
--   helper : Iso (∥ typ (Ω (S₊ 3 , north)) ∥ 4) (∥ S₊ 2 ∥ 4)
--   helper = invIso (FreudenthalIso 1 (S₊ 2 , north) (sphereConnected 2))

--   test2 : Iso.inv helper ∣ north ∣ ≡ ∣ refl ∣
--   test2 = cong ∣_∣ (rCancel (merid north))

--   test4 : ΩTrunc.decode-fun {B = Path (S₊ 3) north north} {n = 4} (∣ refl {x = north} ∣) (∣ refl {x = north} ∣) (∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣) ≡ refl
--   test4 = refl

--   test : Iso.fun helper ∣ refl ∣ ≡ ∣ north ∣ -- cannot normalise LHS (or very slow/big)
--   test = cong (Iso.fun helper) (sym test2) ∙ Iso.rightInv helper _

--   test5 : (Iso.fun (congIso helper) (ΩTrunc.decode-fun (∣ (λ _ → north) ∣) ∣ (λ _ → north) ∣
--         ∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣)) ≡ {!!}
--   test5 = refl

-- FreudTest-1 : Iso (π 3 (S₊ 3 , north)) (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- FreudTest-1 = compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
--                 (compIso
--                   (congIso (invIso (ΩTrunc.IsoFinal 3 ∣ refl ∣ ∣ refl ∣)))
--                   (compIso (congIso (congIso helper))
--                   (compIso
--                     (pathToIso {!λ i → typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , test i))!})
--                     (compIso {!!} {!!}))))
--   where
--   helper : Iso (∥ typ (Ω (S₊ 3 , north)) ∥ 4) (∥ S₊ 2 ∥ 4)
--   helper = invIso (FreudenthalIso 1 (S₊ 2 , north) (sphereConnected 2))

--   test2 : Iso.inv helper ∣ north ∣ ≡ ∣ refl ∣
--   test2 = cong ∣_∣ (rCancel (merid north))

--   test4 : ΩTrunc.decode-fun {B = Path (S₊ 3) north north} {n = 4} (∣ refl {x = north} ∣) (∣ refl {x = north} ∣) (∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣) ≡ refl
--   test4 = refl

--   test : Iso.fun helper ∣ refl ∣ ≡ ∣ north ∣ -- cannot normalise LHS (or very slow/big)
--   test = cong (Iso.fun helper) (sym test2) ∙ Iso.rightInv helper _

--   test5 : (Iso.fun (congIso helper) (ΩTrunc.decode-fun (∣ (λ _ → north) ∣) ∣ (λ _ → north) ∣
--         ∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣)) ≡ {!!}
--   test5 = refl




-- -- testIso : Iso (hLevelTrunc 2 (typ (Ω (S₊ 2 , north)))) (hLevelTrunc 2 (S₊ 1))
-- -- testIso = invIso (FreudenthalIso 0 (S₊ 1 , north) (sphereConnected 1))


-- -- stabSpheres : Iso (π 2 (S₊ 2 , north)) (π 1 (S₊ 1 , north)) 
-- -- stabSpheres =
-- --   compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
-- --       (compIso helper
-- --                (ΩTrunc.IsoFinal 2 ∣ north ∣ ∣ north ∣))
-- --   where
-- --   helper1 : Iso (∥ typ (Ω ((S₊ 2) , north)) ∥ 3) (∥ S₊ 1 ∥ 3)
-- --   helper1 = {!FreudenthalIso 1!}

  

-- --   helper : Iso (typ (Ω ((∥ typ (Ω ((S₊ 2) , north)) ∥ 3) , ∣ refl ∣))) (typ (Ω ((∥ (S₊ 1) ∥ 3) , ∣ north ∣)))
-- --   helper =
-- --     compIso (congIso (truncOfTruncIso 3 1))
-- --       (compIso {!truncIso 3 ?!} {!!})
-- --       where
-- --       test2 : Iso.fun (truncOfTruncIso {A = typ (Ω (S₊ 2 , north))} 3 1) ∣ refl ∣ ≡ ∣ ∣ refl ∣ ∣
-- --       test2 = refl

-- --       test : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Iso (p ∙ sym p ≡ p ∙ sym p) (refl {x = x} ≡ refl {x = x}) 
-- --       test = {!!}



