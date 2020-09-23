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
open import Cubical.HITs.Truncation.FromNegOne as Trunc renaming (rec to trRec ; elim to trElim)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.SmashProduct

open import Cubical.HITs.S1 hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.Foundations.Equiv.HalfAdjoint

private
  variable
    ℓ : Level
    ℓ' : Level

module BL where

  pointedIso : {A : Pointed ℓ} {B : Type ℓ'} {b : B} (e : Iso (typ A) B) → Iso.fun e (pt A) ≡ b → Iso (typ (Ω A)) (typ (Ω (B , b)))
  pointedIso {A = A} {B = B} {b = b} e id = compIso (congIso e) helpIso -- (transport (λ i → Iso (id (~ i) ≡ id (~ i)) (b ≡ b)) idIso)
    where
    oui : ∀ {ℓ} {A : Type ℓ} {x y : A} {p : x ≡ x} {q : x ≡ y} → q ∙∙ (sym q ∙∙ p ∙∙ q) ∙∙ sym q ≡ p
    oui {p = p} {q = q} = (λ i → (λ j → q (~ i ∧ j)) ∙∙ ((λ j → q (~ i ∧ ~ j)) ∙∙ p ∙∙ λ j → q (~ i ∧ j)) ∙∙ λ j → q (~ i ∧ ~ j))
                        ∙ (λ i → rUnit (rUnit p (~ i)) (~ i))

    helpIso : Iso (Iso.fun e (snd A) ≡ Iso.fun e (snd A)) (typ (Ω (B , b)))
    Iso.fun helpIso p = sym id ∙∙ p ∙∙ id
    Iso.inv helpIso p = id ∙∙ p ∙∙ sym id
    Iso.rightInv helpIso p = oui
    Iso.leftInv helpIso p = oui
  
    
  typPathCharac : {A : Type ℓ} → Iso (typ ((Ω^ 2) (Type ℓ , A))) (typ (Ω ((A ≃ A) , idEquiv (A))))
  typPathCharac = pointedIso (equivToIso univalence) (Σ≡Prop isPropIsEquiv (funExt transportRefl))

  equivPathCharacGen : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (eq1 eq2 : A ≃ B) → Iso (eq1 ≡ eq2) (fst eq1 ≡ fst eq2)
  Iso.fun (equivPathCharacGen eq1 eq2) = cong fst
  Iso.inv (equivPathCharacGen eq1 eq2) = Σ≡Prop isPropIsEquiv
  Iso.rightInv (equivPathCharacGen eq1 eq2) p = refl
  Iso.leftInv (equivPathCharacGen eq1 eq2) = J (λ eq2 p → Σ≡Prop isPropIsEquiv (cong fst p) ≡ p) λ i j → (fst eq1) , {!snd eq1!}

  equivPathCharac : ∀ {ℓ } {A : Type ℓ} → Iso (typ (Ω ((A ≃ A) , idEquiv A))) (typ (Ω ((A → A) , idfun A)))
  Iso.fun equivPathCharac p = cong fst p
  Iso.inv equivPathCharac p = Σ≡Prop isPropIsEquiv p
  Iso.rightInv equivPathCharac p = refl
  Iso.leftInv (equivPathCharac {A = A}) p i j =
    (fst (p j)) , (hcomp (λ k → λ {(i = i0) → isPropIsEquiv (fst (p j)) (transp (λ z → isEquiv (fst (p (z ∧ j)))) (~ j) (snd (idEquiv A)))
                                                                        ((snd (Iso.inv equivPathCharac (Iso.fun equivPathCharac p) j))) k
                                 ; (i = i1) → isPropIsEquiv (fst (p j)) (transp (λ z → isEquiv (fst (p j))) (~ j) (snd (p j)))
                                                                        (snd (p j)) k
                                 ; (j = i0) → isPropIsEquiv (idfun A) (snd (idEquiv A))
                                                                      (snd (idEquiv A)) k
                                 ; (j = i1) → isPropIsEquiv (idfun A) (transport (λ z → isEquiv (fst (p (z ∨ i)))) (snd (p i)))
                                                                      (snd (idEquiv A)) k })
                          (transp (λ z → isEquiv (fst (p ((z ∨ i) ∧ j)))) (~ j)
                                  (snd (p (i ∧ j)))))

  test3Gen : ∀ {ℓ} {A : Type ℓ} → {p q : idfun A ≡ idfun A} {r : p ≡ q} → Iso (r ≡ r) {!!} -- Iso (typ ((Ω^ 2) ((A → A) , idfun A))) ((x : A) → typ ((Ω^ 2) (A , x)))
  Iso.fun test3Gen f = {!!} -- funExt⁻ (cong funExt⁻ f)
  Iso.inv test3Gen f = {!!} -- cong funExt (funExt f)
  Iso.rightInv test3Gen f = {!!} -- refl
  Iso.leftInv test3Gen f = {!!} -- refl


  test3 : ∀ {ℓ} {A : Type ℓ} → Iso (typ ((Ω^ 2) ((A → A) , idfun A))) ((x : A) → typ ((Ω^ 2) (A , x)))
  Iso.fun test3 f = funExt⁻ (cong funExt⁻ f)
  Iso.inv test3 f = cong funExt (funExt f)
  Iso.rightInv test3 f = refl
  Iso.leftInv test3 f = refl

  testHelper : ∀{ℓ} {A : Type ℓ} {x y : A} {p : x ≡ y} → transport (λ i → p i ≡ p i) refl ≡ refl
  testHelper {p = p} = J (λ y p → transport (λ i → p i ≡ p i) refl ≡ refl) (transportRefl refl) p

  fixpath : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙∙ refl ∙∙ sym p ≡ refl
  fixpath p = (λ i → (λ j → p (~ i ∧ j)) ∙∙ refl ∙∙ λ j → p (~ i ∧ ~ j)) ∙ sym (rUnit refl)

  equivPathCharacRefl : (p : ((x : (hLevelTrunc 4 (S²))) → typ ((Ω^ 2) (hLevelTrunc 4 (S²) , x))))
                       → sym (Iso.leftInv equivPathCharac refl) ∙∙ cong (Σ≡Prop isPropIsEquiv) (cong funExt (funExt p)) ∙∙ Iso.leftInv equivPathCharac refl ≡ refl
  equivPathCharacRefl p = (λ i → {!!} ∙∙ {!!} ∙∙ {!!}) ∙ {!!} ∙ {!!}


  mainIso : Iso (typ ((Ω^ 3) (Type₀ , (hLevelTrunc 4 (S²))))) ((x : (hLevelTrunc 4 (S²))) → typ ((Ω^ 2) (hLevelTrunc 4 (S²) , x)))
  mainIso = compIso (pointedIso {b = refl} typPathCharac (fixpath (sym (Σ≡Prop isPropIsEquiv (funExt transportRefl)))))
                    (compIso (congIso equivPathCharac) test3)

  cons : ((x : (hLevelTrunc 4 (S²))) → typ ((Ω^ 2) (hLevelTrunc 4 (S²) , x)))
  cons = trElim (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) _ _)
                (S²ToSetRec (λ _ → isOfHLevelTrunc 4 _ _ _ _)
                            λ i j → ∣ surf i j ∣)

  code : S³ → Type₀
  code base = hLevelTrunc 4 S²
  code (surf i j z) = Iso.inv mainIso cons i j z

  encode' : hLevelTrunc 4 (typ (Ω (S³ , base))) → hLevelTrunc 4 S²
  encode' = trRec (isOfHLevelTrunc 4) λ p → transport (cong code p) ∣ base ∣

  promote : S² → typ (Ω (S³ , base))
  promote base = refl
  promote (surf i i₁) k = surf i i₁ k

  decode' : hLevelTrunc 4 S² → hLevelTrunc 4 (typ (Ω (S³ , base)))
  decode' = Trunc.map promote

  cong₂∘ : refl {x = refl {x = hLevelTrunc 4 S²}} ≡ refl {x = refl {x = hLevelTrunc 4 S²}}
  cong₂∘ i j k = hcomp {!!} (isoToPath apath (i ∧ j ∧ k))
    where
    stupidAgda : Path (Path S² base base) refl refl
    stupidAgda = surf
    apath : Iso S² S²
    Iso.fun apath = λ {base → base ; (surf i j) → surf j i}
    Iso.inv apath = λ {base → base ; (surf i j) → surf j i}
    Iso.rightInv apath = λ {base → refl ; (surf i j) → refl}
    Iso.leftInv apath = λ {base → refl ; (surf i j) → refl}
  swappie : Iso.fun mainIso cong₂∘ ≡ cons
  swappie = {!refl!}

  oneway : (x : hLevelTrunc 4 S²) → encode' (decode' x) ≡ x
  oneway = 
    trElim {!Iso.inv mainIso cons!}
           λ {base → refl ; (surf i j) → cong (λ x → x i j) helper2}
    where
    helper : cong (cong promote) surf ≡ surf -- Iso.inv mainIso cons ≡ λ i j z → {!!}
    helper = refl

    helper2 : cong (cong ((λ p → transport (cong code p) ∣ base ∣))) surf  ≡ λ i j → ∣ surf i j ∣
    helper2 = {!!} {- (λ i → (λ i i₁ → transport (λ i₂ → Iso.inv mainIso cons i i₁ i₂) ∣ base ∣))
           ∙∙ (λ i → cong (cong ((λ p → transport p ∣ base ∣) ∘ cong (code))) surf )
           ∙∙ ((λ i → cong (cong ((λ p → transport p ∣ base ∣))) (Iso.inv mainIso cons))
           ∙∙ ((λ i → cong (cong ((λ p → transport p ∣ base ∣))) {!!})) ∙∙ {!!}) -}
      where
      abstract
        cons' : _
        cons' = cons

      testhelp : Iso.inv (congIso {x = refl} {y = refl} (equivPathCharac {A = hLevelTrunc 4 S²})) (Iso.inv (test3 {A = hLevelTrunc 4 S²}) cons') ≡ (sym (Iso.leftInv (equivPathCharac {A = hLevelTrunc 4 S²}) refl) ∙∙ cong (Iso.inv (equivPathCharac {A = hLevelTrunc 4 S²})) (cong funExt (funExt cons')) ∙∙ Iso.leftInv (equivPathCharac {A = hLevelTrunc 4 S²}) refl)
      testhelp = refl

      testhelp2 : Iso.inv mainIso cons' ≡ Iso.inv (congIso typPathCharac) ((fixpath (sym (Σ≡Prop isPropIsEquiv (funExt transportRefl)))) ∙∙ (sym (Iso.leftInv equivPathCharac refl) ∙∙ cong (Σ≡Prop isPropIsEquiv) (cong funExt (funExt cons')) ∙∙ Iso.leftInv equivPathCharac refl) ∙∙ sym (fixpath (sym (Σ≡Prop isPropIsEquiv (funExt transportRefl))))) 
      testhelp2 = refl

-- cong^ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (n : ℕ) (f : typ A → B) → typ ((Ω^ n) A) → typ ((Ω^ n) (B , (f (pt A))))
-- cong^ {A = (A , pt)}zero f p = f pt
-- cong^ {A = A , pt} (suc zero) f p = cong f p
-- cong^ {A = A , pt} (suc (suc zero)) f p = cong (cong f) p
-- cong^ {A = A , pt} (suc (suc (suc n))) f p i j k = {!!}

-- cong^3 : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (n : ℕ) (f : typ A → B) → typ ((Ω^ 3) A) → typ ((Ω^ 3) (B , (f (pt A))))
-- cong^3 n f p = cong (cong (cong f)) p






-- test : {!!}
-- test = {!!}

-- loopSpaceCharacSpecLem1 : Iso (typ ((Ω^ 3) (Type₀ , (hLevelTrunc 4 (S₊ 2))))) (typ ((Ω^ 2) ((hLevelTrunc 4 (S₊ 2) → (hLevelTrunc 4 (S₊ 2))) , (idfun (hLevelTrunc 4 (S₊ 2))))))
-- Iso.fun loopSpaceCharacSpecLem1 p = {!!}
-- Iso.inv loopSpaceCharacSpecLem1 = {!!}
-- Iso.rightInv loopSpaceCharacSpecLem1 = {!!}
-- Iso.leftInv loopSpaceCharacSpecLem1 = {!!}

-- loopSpaceCharacSpec : Iso (typ ((Ω^ 3) (Type₀ , (hLevelTrunc 4 (S₊ 2))))) ((x : (hLevelTrunc 4 (S₊ 2))) → typ ((Ω^ 2) (hLevelTrunc 4 (S₊ 2) , x)))
-- Iso.fun loopSpaceCharacSpec p x = {!!}
-- Iso.inv loopSpaceCharacSpec = {!!}
-- Iso.rightInv loopSpaceCharacSpec = {!!}
-- Iso.leftInv loopSpaceCharacSpec = {!!}

-- dirProof : (y : ∥ S² ∥ 4) (p : ∣ base ∣ ≡ y) → Iso (∥ S₊ 1 ∥ 3) (Path (∥ S² ∥ 4) ∣ base ∣ y)
-- Iso.fun (dirProof y p) = trRec (isOfHLevelTrunc 4 ∣ base ∣ y) (J (λ y p → (a : S¹) → Path (∥ S² ∥ 4) ∣ base ∣ y) (λ {base → refl ; (loop i) → λ j → ∣ surf (i ∧ j) (i ∨ j) ∣}) p)
-- Iso.inv (dirProof y p) = J (λ z p → (Path (∥ S² ∥ 4) ∣ base ∣ z) → ∥ S₊ 1 ∥ 3) (λ _ → ∣ base ∣) p
-- Iso.rightInv (dirProof y p) q = J (λ y q → (p : ∣ base ∣ ≡ y) → Iso.fun (dirProof y p) (Iso.inv (dirProof y p) q) ≡ q) (Iso.inv (elim.isIsoPrecompose {A = Unit} {B = (Path (∥ S² ∥ 4) ∣ base ∣ ∣ base ∣)} (λ _ → refl) 2 (λ p → (Iso.fun (dirProof ∣ base ∣ p) (Iso.inv (dirProof ∣ base ∣ p) refl) ≡ refl) , isOfHLevelTrunc 4 _ _ _ _) (isConnectedPoint 2 (isConnectedPath 3 {!sphereConnected 2!} _ _) refl)) λ _ → transportRefl refl) q p -- elim.isIsoPrecompose {A = Unit} {B = (Path (∥ S² ∥ 4) ∣ base ∣ ∣ base ∣)} (λ _ → refl) ? (λ p → (Iso.fun (dirProof ∣ base ∣ p) (Iso.inv (dirProof ∣ base ∣ p) refl) ≡ refl) , ?) ? ) q p
-- Iso.leftInv (dirProof y p) = {!elim.isIsoPrecompose {A = Unit} {B = (Path (∥ S² ∥ 4) ∣ base ∣ ∣ base ∣)} (λ _ → refl) {!!} (λ p → (Iso.fun (dirProof ∣ base ∣ p) (Iso.inv (dirProof ∣ base ∣ p) refl) ≡ refl) , ?)!}


-- testfun : (x : S¹) (y : ∥ S₊ 3 ∥ 5) (p : ∣ north ∣ ≡ y) → Smash (S¹ , x) (S¹ , base) → Path (∥ S₊ 3 ∥ 5) ∣ north ∣ y
-- testfun x y p basel = p
-- testfun x y p baser = p
-- testfun x y p (proj a b) = (({!!} ∙ {!!}) ∙ sym {!λ i → ∣ !}) ∙ p
-- testfun x y p (gluel a i) = {!λ {base → ? ; (loop j) → ?}!}
-- testfun x y p (gluer b i) = {!!}

-- suspLoopComm : Iso (∥  Smash (S₊∙ 1) (S₊∙ 1)  ∥ 4) (typ (Ω ((∥ S₊ 3 ∥ 5) , ∣ north ∣)))
-- Iso.fun suspLoopComm = trRec {!!} {!!}
-- Iso.inv suspLoopComm = {!!}
-- Iso.rightInv suspLoopComm = {!!}
-- Iso.leftInv suspLoopComm = {!!}

-- test15 : (n : ℕ) → Iso (∥ Σ[ f ∈ ( S₊ 1  → S₊ (suc (suc n))) ] f base ≡ north ∥ (3 + n)) (Σ[ f ∈ ∥ (S₊ 1 → S₊ (suc (suc n))) ∥ (3 + n) ] (∥ Trunc.map (λ g → g base) f ≡ ∣ north ∣  ∥ (3 + n)))
-- Iso.fun (test15 zero) = trElim (λ x → isOfHLevelΣ 3 (isOfHLevelTrunc 3) λ _ → isOfHLevelTrunc 3) λ {(f , pt) → ∣ f ∣ , ∣ (λ i → ∣ pt i ∣) ∣}
-- Iso.inv (test15 zero) = uncurry (trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelTrunc 3) λ f → trElim (λ _ → isOfHLevelTrunc 3) λ a → trRec {!!} (λ p → ∣ f , p ∣) (Iso.fun (PathIdTruncIso 2) a) )
-- Iso.rightInv (test15 zero) = uncurry (trElim {!!} λ f → trElim {!!} λ p → ΣPathP ({!!} , {!!}))
-- Iso.leftInv (test15 zero) = {!!}
-- test15 (suc n) = {!!}

-- isCommSusp : (A : Type₀) → ((x : A) (p q : x ≡ x) → p ∙ q ≡ q ∙ p) → (x : Susp A) (p q : x ≡ x ) → p ∙ q ≡ q ∙ p
-- isCommSusp A comm x p q = {!!}

-- open import Cubical.Foundations.Pointed

-- CODES : (n : ℕ) (y : hLevelTrunc (5 + n) (S₊ (3 + n))) → (∣ north ∣ ≡ y) → TypeOfHLevel ℓ-zero (4 + n)
-- CODES n = trElim (λ _ → isOfHLevelΠ (5 + n) λ _ → isOfHLevelTypeOfHLevel (4 + n))
--                  {!!}
--   where
--   helpfun : (a : Susp (Susp (S₊ (suc n)))) → Path (hLevelTrunc (5 + n) (S₊ (3 + n))) ∣ north ∣ ∣ a ∣ → TypeOfHLevel ℓ-zero (suc (suc (suc (suc n))))
--   helpfun north p = (hLevelTrunc (4 + n) (S₊ (2 + n))) , (isOfHLevelTrunc (4 + n))
--   helpfun south p = (hLevelTrunc (4 + n) (S₊ (2 + n))) , (isOfHLevelTrunc (4 + n))
--   helpfun (merid a i) p = {!hLevelTrunc (4 + n) (S₊ (2 + n))!} , {!!}
--     where
--     uaAp : (hLevelTrunc (4 + n) (S₊ (2 + n))) ≡ (hLevelTrunc (4 + n) (S₊ (2 + n)))
--     uaAp = isoToPath (iso (trRec (isOfHLevelTrunc (4 + n)) (λ {north → ∣ north ∣ ; south → ∣ south ∣ ; (merid b i) → {!!}})) {!!} {!!} {!!})

-- higherPath : (n m : ℕ) → S₊ (suc n) → (S₊ (suc (suc (m + n))))
-- higherPath n zero x = {!!}
-- higherPath zero (suc m) x = {!!}
-- higherPath (suc n) (suc m) north = north
-- higherPath (suc n) (suc m) south = south
-- higherPath (suc n) (suc m) (merid a i) = {!merid (higherPath _ _ a) i!}

-- -- test2 : (n : ℕ) (x y : Susp (S₊ ((suc n + suc n)))) → (q : south ≡ x) → (p : Path (Susp (S₊ (suc n + suc n))) north x)  → Σ[ a ∈ (S₊ (suc n + suc n)) ] p ≡ merid a ∙ q 
-- -- test2 n x = {!!}

-- -- test3 : (n : ℕ) → isConnectedFun ((suc n) + (suc n)) λ (x : S₊ (suc n + suc n)) → merid x
-- -- test3 zero = λ b → {!!} , {!!}
-- -- test3 (suc n) = elim.isConnectedPrecompose _ _ λ P → (λ f b → {!!}) , {!!}

-- --   where
-- --   module _ (P : {!!} → TypeOfHLevel ℓ-zero (suc (suc (n + suc (suc n))))) where
 
-- --     maybe : hasSection (λ s → s ∘ (λ z → merid z))
-- --     maybe = {!!} , {!!}

-- -- module _ {ℓ} (n : HLevel) {A : Pointed ℓ} (connA : isConnected (suc (suc n)) (typ A)) where

-- --   σ : typ A → typ (Ω (∙Susp (typ A)))
-- --   σ a = merid a ∙ merid (pt A) ⁻¹

-- --   private
-- --     2n+2 = suc n + suc n

-- --     module WC (p : north ≡ north) =
-- --       WedgeConnectivity (suc n) (suc n) A connA A connA
-- --         (λ a b →
-- --           ( (σ b ≡ p → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p))
-- --           , isOfHLevelΠ 2n+2 λ _ → isOfHLevelTrunc 2n+2
-- --           ))
-- --         (λ a r → ∣ a , (rCancel' (merid a) ∙ rCancel' (merid (pt A)) ⁻¹) ∙ r ∣)
-- --         (λ b r → ∣ b , r ∣)
-- --         (funExt λ r →
-- --           cong′ (λ w → ∣ pt A , w ∣)
-- --             (cong (_∙ r) (rCancel' (rCancel' (merid (pt A))))
-- --               ∙ lUnit r ⁻¹))

-- --     fwd : (p : north ≡ north) (a : typ A)
-- --       → hLevelTrunc 2n+2 (fiber σ p)
-- --       → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
-- --     fwd p a = Trunc.rec (isOfHLevelTrunc 2n+2) (uncurry (WC.extension p a))

-- --     isEquivFwd : (p : north ≡ north) (a : typ A) → isEquiv (fwd p a)
-- --     isEquivFwd p a .equiv-proof =
-- --       elim.isEquivPrecompose (λ _ → pt A) (suc n)
-- --         (λ a →
-- --           ( (∀ t → isContr (fiber (fwd p a) t))
-- --           , isProp→isOfHLevelSuc n (isPropΠ λ _ → isPropIsContr)
-- --           ))

-- --         (isConnectedPoint (suc n) connA (pt A))
-- --         .equiv-proof
-- --         (λ _ → Trunc.elim
-- --           (λ _ → isProp→isOfHLevelSuc (n + suc n) isPropIsContr)
-- --          (λ fib →
-- --             subst (λ k → isContr (fiber k ∣ fib ∣))
-- --               (cong (Trunc.rec (isOfHLevelTrunc 2n+2) ∘ uncurry)
-- --                 (funExt (WC.right p) ⁻¹))
-- --               (subst isEquiv
-- --                 (funExt (Trunc.mapId) ⁻¹)
-- --                 (idIsEquiv _)
-- --                 .equiv-proof ∣ fib ∣)
-- --              ))
-- --         .fst .fst a

-- --     interpolate : (a : typ A)
-- --       → PathP (λ i → typ A → north ≡ merid a i) (λ x → merid x ∙ merid a ⁻¹) merid
-- --     interpolate a i x j = compPath-filler (merid x) (merid a ⁻¹) (~ i) j

-- --   Code : (y : Susp (typ A)) → north ≡ y → Type ℓ
-- --   Code north p = hLevelTrunc 2n+2 (fiber σ p)
-- --   Code south q = hLevelTrunc 2n+2 (fiber merid q)
-- --   Code (merid a i) p =
-- --     Glue
-- --       (hLevelTrunc 2n+2 (fiber (interpolate a i) p))
-- --       (λ
-- --         { (i = i0) → _ , (fwd p a , isEquivFwd p a)
-- --         ; (i = i1) → _ , idEquiv _
-- --         })

-- --   encode : (y : Susp (typ A)) (p : north ≡ y) → Code y p
-- --   encode y = J Code ∣ pt A , rCancel' (merid (pt A)) ∣

-- --   encodeMerid : (a : typ A) → encode south (merid a) ≡ ∣ a , refl ∣
-- --   encodeMerid a =
-- --     cong (transport (λ i → gluePath i))
-- --       (funExt⁻ (WC.left refl a) _ ∙ λ i → ∣ a , (lem (rCancel' (merid a)) (rCancel' (merid (pt A)))) i ∣)
-- --     ∙ transport (PathP≡Path gluePath _ _)
-- --       (λ i → ∣ a , (λ j k → rCancel-filler' (merid a) i j k) ∣)
-- --     where
-- --     gluePath : I → Type _
-- --     gluePath i = hLevelTrunc 2n+2 (fiber (interpolate a i) (λ j → merid a (i ∧ j)))

-- --     lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → (p ∙ q ⁻¹) ∙ q ≡ p
-- --     lem p q = assoc p (q ⁻¹) q ⁻¹ ∙ cong (p ∙_) (lCancel q) ∙ rUnit p ⁻¹

-- --   contractCodeSouth : (p : north ≡ south) (c : Code south p) → encode south p ≡ c
-- --   contractCodeSouth p =
-- --     Trunc.elim
-- --       (λ _ → isOfHLevelPath 2n+2 (isOfHLevelTrunc 2n+2) _ _)
-- --       (uncurry λ a →
-- --         J (λ p r → encode south p ≡ ∣ a , r ∣) (encodeMerid a))

-- --   isConnectedMerid : isConnectedFun 2n+2 (merid {A = typ A})
-- --   isConnectedMerid p = encode south p , contractCodeSouth p

-- --   isConnectedσ : isConnectedFun 2n+2 σ
-- --   isConnectedσ =
-- --     transport (λ i → isConnectedFun 2n+2 (interpolate (pt A) (~ i))) isConnectedMerid

-- -- open import Cubical.Foundations.Pointed
-- -- open import Cubical.Data.Bool

-- -- isConn→isConnSusp : ∀ {ℓ} {A : Pointed ℓ} → isConnected 2 (typ A) → isConnected 2 (Susp (typ A))
-- -- isConn→isConnSusp {A = A} iscon = ∣ north ∣ , (trElim (λ _ → isOfHLevelSuc 1 (isOfHLevelTrunc 2 _ _)) (suspToPropRec (pt A) (λ _ → isOfHLevelTrunc 2 _ _) refl))

-- -- FreudenthalIso1 : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
-- --                 → isConnected (2 + n) (typ A)
-- --                 → Iso (hLevelTrunc ((suc n) + (suc n)) (typ A))
-- --                       (hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north))))
-- -- FreudenthalIso1 zero A iscon = isContr→Iso iscon isConnΩ
-- --   where
-- --   isConnΩ : isContr (hLevelTrunc 2 (typ (Ω (Susp (typ A) , north)))) 
-- --   isConnΩ = {!Iso.inv (Trunc.PathIdTruncIso {A = Susp (typ A)} {a = north} {b = north} 2) !}
-- -- FreudenthalIso1 (suc n) A iscon = {!!}


-- -- FreudenthalEquiv : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
-- --                 → isConnected (2 + n) (typ A)
-- --                 → hLevelTrunc ((suc n) + (suc n)) (typ A)
-- --                  ≃ hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north)))
-- -- FreudenthalEquiv n A iscon = connectedTruncEquiv _
-- --                                                  (σ n {A = A} iscon)
-- --                                                  (isConnectedσ _ iscon)
-- -- FreudenthalIso : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
-- --                 → isConnected (2 + n) (typ A)
-- --                 → Iso (hLevelTrunc ((suc n) + (suc n)) (typ A))
-- --                       (hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north))))
-- -- FreudenthalIso zero A iscon = iso (Trunc.map (σ 0 {A = A} iscon))
-- --                                   {!!}
-- --                                   {!!}
-- --                                   {!!}
-- -- -- connectedTruncIso _ (σ 0 {A = A} iscon) (isConnectedσ _ iscon) -- pattern matching to prevent Agda from expanding
-- -- FreudenthalIso (suc zero) A iscon = connectedTruncIso _ (σ 1 {A = A} iscon) (isConnectedσ _ iscon)
-- -- FreudenthalIso (suc (suc zero)) A iscon = connectedTruncIso _ (σ 2 {A = A} iscon) (isConnectedσ _ iscon)
-- -- FreudenthalIso (suc (suc (suc zero))) A iscon = connectedTruncIso _ (σ 3 {A = A} iscon) (isConnectedσ _ iscon)
-- -- FreudenthalIso (suc (suc (suc (suc zero)))) A iscon = connectedTruncIso _ (σ 4 {A = A} iscon) (isConnectedσ _ iscon)
-- -- FreudenthalIso (suc (suc (suc (suc (suc n))))) A iscon = connectedTruncIso _ (σ (5 + n) {A = A} iscon) (isConnectedσ _ iscon)

-- -- -- -- Tests
-- -- -- open import Cubical.Homotopy.Loopspace
-- -- -- open import Cubical.HITs.Sn

-- -- -- truncIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : HLevel)
-- -- --          → Iso A B
-- -- --          → Iso (hLevelTrunc n A) (hLevelTrunc n B)
-- -- -- Iso.fun (truncIso n i) = map (Iso.fun i)
-- -- -- Iso.inv (truncIso n i) = map (Iso.inv i)
-- -- -- Iso.rightInv (truncIso n i) = Trunc.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (Iso.rightInv i a)
-- -- -- Iso.leftInv (truncIso n i) = Trunc.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (Iso.leftInv i a)

-- -- -- π₀-S¹ : Iso (hLevelTrunc 2 (S₊ 1)) {!!}
-- -- -- π₀-S¹ = {!!}

-- -- -- LoopSpaceIso : {!!}
-- -- -- LoopSpaceIso = {!!}
-- -- -- open import Cubical.Foundations.Equiv.HalfAdjoint


-- -- -- base-change : (x : ∥ S₊ 2 ∥ 4) →  Iso (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , x))) (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- -- -- Iso.fun (base-change x) =
-- -- --   Trunc.elim {B = λ x → (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , x))) → (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))}
-- -- --              (λ _ → isOfHLevelΠ 4 {!!})
-- -- --              (λ {north → idfun _
-- -- --                ; south → transport (λ i → typ ((Ω^ 2) ((∥ S₊ 2 ∥ 4) , ∣ merid north (~ i) ∣)))
-- -- --                ; (merid north i) → {!!}
-- -- --                ; (merid south i) → {!!}
-- -- --                ; (merid (merid a j) i) → {!isOfHLevelDep!}}) x
-- -- -- Iso.inv (base-change x) = {!!}
-- -- -- Iso.rightInv (base-change x) = {!!}
-- -- -- Iso.leftInv (base-change x) = {!!}

-- -- -- FreudTest-2 : (π 3 (S₊ 3 , north)) ≡ (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- -- -- FreudTest-2 = isoToPath (compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
-- -- --                 (compIso
-- -- --                   (congIso (invIso (ΩTrunc.IsoFinal 3 ∣ refl ∣ ∣ refl ∣)))
-- -- --                   (congIso (congIso helper))))
-- -- --            ∙∙ isoToPath {!!}
-- -- --            ∙∙ {!!}
-- -- --   where
-- -- --   helper : Iso (∥ typ (Ω (S₊ 3 , north)) ∥ 4) (∥ S₊ 2 ∥ 4)
-- -- --   helper = invIso (FreudenthalIso 1 (S₊ 2 , north) (sphereConnected 2))

-- -- --   test2 : Iso.inv helper ∣ north ∣ ≡ ∣ refl ∣
-- -- --   test2 = cong ∣_∣ (rCancel (merid north))

-- -- --   test4 : ΩTrunc.decode-fun {B = Path (S₊ 3) north north} {n = 4} (∣ refl {x = north} ∣) (∣ refl {x = north} ∣) (∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣) ≡ refl
-- -- --   test4 = refl

-- -- --   test : Iso.fun helper ∣ refl ∣ ≡ ∣ north ∣ -- cannot normalise LHS (or very slow/big)
-- -- --   test = cong (Iso.fun helper) (sym test2) ∙ Iso.rightInv helper _

-- -- --   test5 : (Iso.fun (congIso helper) (ΩTrunc.decode-fun (∣ (λ _ → north) ∣) ∣ (λ _ → north) ∣
-- -- --         ∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣)) ≡ {!!}
-- -- --   test5 = refl

-- -- -- -- FreudTest-1 : Iso (π 3 (S₊ 3 , north)) (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- -- -- -- FreudTest-1 = compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
-- -- -- --                 (compIso
-- -- -- --                   (congIso (invIso (ΩTrunc.IsoFinal 3 ∣ refl ∣ ∣ refl ∣)))
-- -- -- --                   (compIso (congIso (congIso helper))
-- -- -- --                   (compIso
-- -- -- --                     (pathToIso {!λ i → typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , test i))!})
-- -- -- --                     (compIso {!!} {!!}))))
-- -- -- --   where
-- -- -- --   helper : Iso (∥ typ (Ω (S₊ 3 , north)) ∥ 4) (∥ S₊ 2 ∥ 4)
-- -- -- --   helper = invIso (FreudenthalIso 1 (S₊ 2 , north) (sphereConnected 2))

-- -- -- --   test2 : Iso.inv helper ∣ north ∣ ≡ ∣ refl ∣
-- -- -- --   test2 = cong ∣_∣ (rCancel (merid north))

-- -- -- --   test4 : ΩTrunc.decode-fun {B = Path (S₊ 3) north north} {n = 4} (∣ refl {x = north} ∣) (∣ refl {x = north} ∣) (∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣) ≡ refl
-- -- -- --   test4 = refl

-- -- -- --   test : Iso.fun helper ∣ refl ∣ ≡ ∣ north ∣ -- cannot normalise LHS (or very slow/big)
-- -- -- --   test = {!Iso.fun helper ∣ refl ∣!} -- cong (Iso.fun helper) (sym test2) ∙ Iso.rightInv helper _

-- -- -- --   test5 : (Iso.fun (congIso helper) (ΩTrunc.decode-fun (∣ (λ _ → north) ∣) ∣ (λ _ → north) ∣
-- -- -- --         ∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣)) ≡ {!!}
-- -- -- --   test5 = refl




-- -- -- -- -- testIso : Iso (hLevelTrunc 2 (typ (Ω (S₊ 2 , north)))) (hLevelTrunc 2 (S₊ 1))
-- -- -- -- -- testIso = invIso (FreudenthalIso 0 (S₊ 1 , north) (sphereConnected 1))


-- -- -- -- -- stabSpheres : Iso (π 2 (S₊ 2 , north)) (π 1 (S₊ 1 , north)) 
-- -- -- -- -- stabSpheres =
-- -- -- -- --   compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
-- -- -- -- --       (compIso helper
-- -- -- -- --                (ΩTrunc.IsoFinal 2 ∣ north ∣ ∣ north ∣))
-- -- -- -- --   where
-- -- -- -- --   helper1 : Iso (∥ typ (Ω ((S₊ 2) , north)) ∥ 3) (∥ S₊ 1 ∥ 3)
-- -- -- -- --   helper1 = {!FreudenthalIso 1!}

  

-- -- -- -- --   helper : Iso (typ (Ω ((∥ typ (Ω ((S₊ 2) , north)) ∥ 3) , ∣ refl ∣))) (typ (Ω ((∥ (S₊ 1) ∥ 3) , ∣ north ∣)))
-- -- -- -- --   helper =
-- -- -- -- --     compIso (congIso (truncOfTruncIso 3 1))
-- -- -- -- --       (compIso {!truncIso 3 ?!} {!!})
-- -- -- -- --       where
-- -- -- -- --       test2 : Iso.fun (truncOfTruncIso {A = typ (Ω (S₊ 2 , north))} 3 1) ∣ refl ∣ ≡ ∣ ∣ refl ∣ ∣
-- -- -- -- --       test2 = refl

-- -- -- -- --       test : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Iso (p ∙ sym p ≡ p ∙ sym p) (refl {x = x} ≡ refl {x = x}) 
-- -- -- -- --       test = {!!}



