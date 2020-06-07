{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Sn.Sn where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.S1.S1
open import Cubical.HITs.S1
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisReduced
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
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
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; recElim to trRec ; rec to trRec2 ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso ; invIso to invGrIso ; idIso to idGrIso)
open import Cubical.Data.Group.GroupLibrary
open import Cubical.ZCohomology.coHomZero-map
open import Cubical.HITs.Wedge


open import Cubical.ZCohomology.KcompPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)



funIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → Iso (A → B × C) ((A → B) × (A → C))
Iso.fun funIso = λ f → (λ a → proj₁ (f a)) , (λ a → proj₂ (f a))
Iso.inv funIso (f , g) = λ a → (f a) , (g a)
Iso.rightInv funIso (f , g) = refl
Iso.leftInv funIso b = funExt λ a → sym (×-η _)

schonfIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → Iso (A × B → C) (A → B → C)
Iso.fun schonfIso f a b = f (a , b)
Iso.inv schonfIso f (a , b) = f a b
Iso.rightInv schonfIso a = refl
Iso.leftInv schonfIso f = funExt λ {(a , b) → refl}

toProdElimSuspRec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Type ℓ'} (a : A)
                 → ((x : Susp A) → isProp (B x))
                 → B north
                 → (x : Susp A) → B x
toProdElimSuspRec a isProp Bnorth north = Bnorth
toProdElimSuspRec {B = B} a isProp Bnorth south = subst B (merid a) Bnorth
toProdElimSuspRec {B = B} a isProp Bnorth (merid a₁ i) =
  hcomp (λ k → λ {(i = i0) → Bnorth ;
                   (i = i1) → isProp south (subst B (merid a₁) Bnorth) (subst B (merid a) Bnorth) k})
        (transp (λ j → B (merid a₁ (j ∧ i))) (~ i) Bnorth)

toProdElimSuspElim2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Susp A → Type ℓ'} (a : A)
                 → ((x y : Susp A) → isProp (B x y))
                 → B north north
                 → (x y : Susp A) → B x y
toProdElimSuspElim2 a isProp Bnorth =
  toProdElimSuspRec a (λ x → isOfHLevelΠ 1 λ y → isProp x y)
                      (toProdElimSuspRec a (λ x → isProp north x) Bnorth)

cong₂Funct2 : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} {B : Type ℓ'} (f : A → A → B) →
        (p : x ≡ y) →
        {u v : A} (q : u ≡ v) →
        cong₂ f p q ≡ cong (λ x → f x u) p ∙ cong (f y) q
cong₂Funct2 {x = x} {y = y} f p {u = u} {v = v} q j i =
  hcomp (λ k → λ { (i = i0) → f x u
                  ; (i = i1) → f y (q k)
                  ; (j = i0) → f (p i) (q (i ∧ k))})
       (f (p i) u)

cong₂Sym : ∀ {ℓ} {A : Type ℓ} {x : A}
           (p : x ≡ x) →
           (refl ≡ p) → 
           (P : p ≡ p) →
           cong₂ (λ x y → x ∙ y) P (sym P) ≡ refl
cong₂Sym {x = x} p = J (λ p _ → (P : p ≡ p) → cong₂ (λ x y → x ∙ y) P (sym P) ≡ refl)
                       λ P → cong₂Funct2 (λ x y → x ∙ y) P (sym P)
                            ∙ PathP→compPathR (λ j → cong (λ x → rUnit x (~ j)) P ∙ cong (λ x → lUnit x (~ j)) (sym P))
                            ∙ (λ j → (sym (rUnit refl)) ∙ rCancel P j ∙ lUnit refl)
                            ∙ (λ j → sym (rUnit refl) ∙ lUnit (lUnit refl) (~ j) )
                            ∙ rCancel (sym (rUnit refl))

abstract
  cong₂Sym1 : ∀ {ℓ} {A : Type ℓ} {x : A}
             (p : x ≡ x) →
             (refl ≡ p) → 
             (P : p ≡ p) →
             cong (λ x → x ∙ p) P ≡ cong (λ x → p ∙ x) P
  cong₂Sym1 {x = x} p id P = rUnit _
                           ∙ (λ i → cong (λ x → x ∙ p) P ∙ lCancel (λ i → p ∙ P i) (~ i)) -- cong (λ x → cong (λ x → x ∙ p) P ∙ x) {!!}
                           ∙ assoc _ _ _
                           ∙ (λ j → cong₂Funct2 (λ x y → x ∙ y) P (sym P) (~ j) ∙ (λ i → p ∙ P i))
                           ∙ (λ j → cong₂Sym p id P j ∙ (λ i → p ∙ P i))
                           ∙ sym (lUnit _)


prodId : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A × B} → proj₁ x ≡ proj₁ y → proj₂ x ≡ proj₂ y → x ≡ y
prodId {x = (a , b)} {y = (c , d)} id1 id2 i = (id1 i) , (id2 i)





test13 : Iso (S₊ 1 → hLevelTrunc 4 (S₊ 2)) (hLevelTrunc 4 (S₊ 2) × hLevelTrunc 3 (S₊ 1))
Iso.fun test13 f = f north , ΩKn+1→Kn (sym (rCancelₖ (f north))
                         ∙ (λ i → f (merid south i) +ₖ (-ₖ f (merid north i)))
                         ∙ rCancelₖ (f south))
Iso.inv test13 (a , b) north = a +ₖ 0ₖ
Iso.inv test13 (a , b) south = a +ₖ 0ₖ
Iso.inv test13 (a , b) (merid south i) = a +ₖ (Kn→ΩKn+1 1 b i)
Iso.inv test13 (a , b) (merid north i) = a +ₖ 0ₖ
Iso.rightInv test13 (a , b) =
  ×≡ (rUnitₖ a)
     ((cong ΩKn+1→Kn (congHelper++ (Kn→ΩKn+1 1 b) (λ x → (a +ₖ x) +ₖ (-ₖ (a +ₖ 0ₖ))) (funExt (λ x → sym (cancelHelper a x))) (rCancelₖ (a +ₖ 0ₖ))))
    ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 1) b)
    where
    cancelHelper : (a b : hLevelTrunc 4 (S₊ 2)) → (a +ₖ b) +ₖ (-ₖ (a +ₖ 0ₖ)) ≡ b
    cancelHelper a b =
      (a +ₖ b) +ₖ (-ₖ (a +ₖ 0ₖ)) ≡⟨ (λ i → (a +ₖ b) +ₖ (-ₖ (rUnitₖ a i))) ⟩
      (a +ₖ b) +ₖ (-ₖ a) ≡⟨ cong (λ x → x +ₖ (-ₖ a)) (commₖ a b) ⟩
      (b +ₖ a) +ₖ (-ₖ a) ≡⟨ assocₖ b a (-ₖ a) ⟩
      b +ₖ a +ₖ (-ₖ a) ≡⟨ cong (λ x → b +ₖ x) (rCancelₖ a) ⟩
      b +ₖ 0ₖ ≡⟨ rUnitₖ b ⟩
      b ∎

    abstract
      commHelper : (p q : Path (hLevelTrunc 4 (S₊ 2)) 0ₖ 0ₖ) → p ∙ q ≡ q ∙ p
      commHelper p q =
          cong₂ _∙_ (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) p))
                    (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) q))
        ∙ sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) (Kn→ΩKn+1 1 (ΩKn+1→Kn p) ∙ Kn→ΩKn+1 1 (ΩKn+1→Kn q)))
        ∙ cong (Kn→ΩKn+1 1) (commₖ (ΩKn+1→Kn p) (ΩKn+1→Kn q))
        ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 1) (Kn→ΩKn+1 1 (ΩKn+1→Kn q) ∙ Kn→ΩKn+1 1 (ΩKn+1→Kn p))
        ∙ sym (cong₂ _∙_ (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) q))
                         (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) p)))

    moveabout : {x : hLevelTrunc 4 (S₊ 2)} (p q : x ≡ 0ₖ) (mid : 0ₖ ≡ 0ₖ)
              → sym q ∙ (p ∙ mid ∙ sym p) ∙ q ≡ mid
    moveabout p q mid = assoc (sym q) _ _
                      ∙ cong (_∙ q) (assoc (sym q) p (mid ∙ sym p))
                      ∙ sym (assoc (sym q ∙ p) (mid ∙ sym p) q)
                      ∙ cong ((sym q ∙ p) ∙_) (sym (assoc mid (sym p) q))
                      ∙ cong (λ x → (sym q ∙ p) ∙ (mid ∙ x)) (sym (symDistr (sym q) p))
                      ∙ cong ((sym q ∙ p)∙_) (commHelper mid _)
                      ∙ assoc _ _ _
                      ∙ cong (_∙ mid) (rCancel (sym q ∙ p))
                      ∙ sym (lUnit mid)
    



-- (cong (λ x → (a +ₖ 0ₖ) +ₖ x) (-distrₖ a 0ₖ)
    congHelper : ∀ {ℓ} {A : Type ℓ} {a1 : A} (p : a1 ≡ a1) (f : A → A) (id : (λ x → x) ≡ f) 
               → cong f p ≡ sym (funExt⁻ id a1) ∙ p ∙ funExt⁻ id a1
    congHelper {a1 = a1}  p f id =
        (λ i → lUnit (rUnit (cong f p) i) i)
      ∙ (λ i → (λ j → id ((~ i) ∨ (~ j)) a1) ∙ cong (id (~ i)) p ∙ λ j → id (~ i ∨ j) a1)


    congHelper++ : (p : 0ₖ ≡ 0ₖ) (f : hLevelTrunc 4 (S₊ 2) → hLevelTrunc 4 (S₊ 2)) (id : (λ x → x) ≡ f)
                → (q : (f 0ₖ) ≡ 0ₖ)
                → (sym q) ∙ cong f p ∙ q ≡ p
    congHelper++ p f id q =
      cong (λ x → sym q ∙ x ∙ q) (congHelper p f id) ∙
      moveabout (sym (funExt⁻ id ∣ north ∣)) q p
    
Iso.leftInv test13 a =
  funExt λ {north → rUnitₖ (a north)
          ; south → rUnitₖ (a north) ∙ cong a (merid north)
          ; (merid south i) j → {!!}
          ; (merid north i) → {!!}}




-- S1→S¹ : S₊ 1 → S¹
-- S1→S¹ x = SuspBool→S¹ (S1→SuspBool x)

-- S¹→S1 : S¹ → S₊ 1
-- S¹→S1 x = SuspBool→S1 (S¹→SuspBool x)

-- S1→S¹-sect : section S1→S¹ S¹→S1
-- S1→S¹-sect x =
--     cong SuspBool→S¹ (SuspBool→S1-retr (S¹→SuspBool x))
--   ∙ S¹→SuspBool→S¹ x

-- S1→S¹-retr : retract S1→S¹ S¹→S1
-- S1→S¹-retr x =
--     cong SuspBool→S1 (SuspBool→S¹→SuspBool (S1→SuspBool x))
--   ∙ SuspBool→S1-sect x


-- prodElim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : ∥ A ∥₀ × ∥ B ∥₀ → Type ℓ''}
--         → ((x : ∥ A ∥₀ × ∥ B ∥₀) → isOfHLevel 2 (C x))
--         → ((a : A) (b : B) → C (∣ a ∣₀ , ∣ b ∣₀))
--         → (x : ∥ A ∥₀ × ∥ B ∥₀) → C x
-- prodElim {A = A} {B = B} {C = C} hlevel ind (a , b) = schonf a b
--   where
--   schonf : (a : ∥ A ∥₀) (b : ∥ B ∥₀) → C (a , b)
--   schonf = sElim (λ x → isOfHLevelΠ 2 λ y → hlevel (_ , _)) λ a → sElim (λ x → hlevel (_ , _))
--                  λ b → ind a b

-- setTruncOfProdIso :  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso ∥ A × B ∥₀ (∥ A ∥₀ × ∥ B ∥₀) 
-- Iso.fun setTruncOfProdIso = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) λ { (a , b) → ∣ a ∣₀ , ∣ b ∣₀ }
-- Iso.inv setTruncOfProdIso = prodElim (λ _ → setTruncIsSet) λ a b → ∣ a , b ∣₀
-- Iso.rightInv setTruncOfProdIso = prodElim (λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
--                                           λ _ _ → refl
-- Iso.leftInv setTruncOfProdIso = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--                                       λ {(a , b) → refl}


-- isGroupoidS1 : isGroupoid (S₊ 1)
-- isGroupoidS1 = transport (λ i → isGroupoid (S¹≡S1 (~ i))) isGroupoidS¹
-- isConnectedS1 : (x : S₊ 1) → ∥ north ≡ x ∥₋₁
-- isConnectedS1 x = pRec propTruncIsProp
--                        (λ p → ∣ cong (transport (sym (S¹≡S1))) p ∙ transport⁻Transport (S¹≡S1) x ∣₋₁)
--                        (isConnectedS¹ (transport S¹≡S1 x))


-- open import Cubical.HITs.S2

-- test : (S₊ 2) → S₊ 1
-- test north = north
-- test south = south
-- test (merid a i) = merid north i

-- test2 : (S₊ 1) → (S₊ 2)
-- test2 north = north
-- test2 south = south
-- test2 (merid a i) = merid (merid a i) i

-- S1test : ∀ {ℓ} {A : S¹ → Type ℓ} → (Abase : A base) → subst A loop Abase ≡ Abase →  (x : S¹) → A x
-- S1test = {!!}

-- testS² : S² → S¹
-- testS² base = base
-- testS² (surf i i₁) = base

-- test4 : S₊ 1 → hLevelTrunc 4 (S₊ 2)
-- test4 north = ∣ north ∣
-- test4 south = ∣ north ∣
-- test4 (merid a i) = (Kn→ΩKn+1 1 ∣ south ∣) i

-- test3 : hLevelTrunc 4 (S₊ 2) → S₊ 1
-- test3 =
--   trElim (λ _ → {!!})
--          λ {north → north ; south → north ; (merid a i) → loop* i}

-- testIso2 : Iso ((S₊ 1) → hLevelTrunc 4 (S₊ 2)) ((S₊ 1) × hLevelTrunc 4 (S₊ 2))
-- Iso.fun testIso2 f = (test3 (f north)) , trElim (λ _ → isOfHLevelTrunc 4) (λ s → ΩKn+1→Kn (cong ∣_∣ (merid s ∙ sym (merid north)))) (f north)
-- Iso.inv testIso2 (x , p) y = (test4 x) +ₖ (test4 y) +ₖ p
-- Iso.rightInv testIso2 (s , s2) = trElim {B = λ s2 → Iso.fun testIso2 (Iso.inv testIso2 (s , s2)) ≡ (s , s2)}
--                                         {!!}
--                                         (λ s3 → ×≡ {!!} {!!})
--                                         s2
-- Iso.leftInv testIso2 a = funExt λ x → {!!}

-- testIso : Iso (S¹ → hLevelTrunc 4 S²) (S¹ × hLevelTrunc 4 S²)
-- Iso.fun testIso f = {!(f base)!} , {!!} -- trElim (λ _ → isOfHLevelSuc 3 (isGroupoidS1)) test (f north) , (f north)
-- Iso.inv testIso (s , tr) x = tr
-- Iso.rightInv testIso (x , tr) = {!!}
-- Iso.leftInv testIso a = funExt (S1test (cong a loop) {!!}) -- funExt (toPropElim {B = λ x → a base ≡ a x} {!a base!} refl)




-- coHom0Torus : grIso (coHomGr 0 (S₊ 1 × S₊ 1)) intGroup
-- coHom0Torus =
--   Iso'→Iso
--     (iso'
--       (iso (sRec isSetInt (λ f → f (north , north)))
--            (λ a → ∣ (λ x → a) ∣₀)
--            (λ a → refl)
--            (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--                   λ f → cong ∣_∣₀
--                       (funExt λ {(x , y) → toProdElimSuspElim2
--                                                   {B = λ x y → f (north , north) ≡ f (x , y)}
--                                                   north
--                                                   (λ _ _ → isSetInt _ _)
--                                                   refl
--                                                   x y})))
--       (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ a b → addLemma (a (north , north)) (b (north , north))))

-- -- private
-- --   S¹map : hLevelTrunc 3 S¹ → S¹
-- --   S¹map = trElim (λ _ → isGroupoidS¹) (idfun S¹)

-- --   S¹map-id : (x : hLevelTrunc 3 S¹) → Path (hLevelTrunc 3 S¹) ∣ S¹map x ∣ x
-- --   S¹map-id = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
-- --                     λ a → refl

-- --   S1map : hLevelTrunc 3 (S₊ 1) → (S₊ 1)
-- --   S1map = trElim (λ _ → isGroupoidS1) (idfun _)


-- -- S¹→S¹ : Iso (S¹ → hLevelTrunc 3 S¹) (S¹ × Int)
-- -- Iso.fun S¹→S¹ f = S¹map (f base)
-- --                  , winding (basechange2⁻ (S¹map (f base)) λ i → S¹map (f (loop i)))
-- -- Iso.inv S¹→S¹ (s , int) base = ∣ s ∣
-- -- Iso.inv S¹→S¹ (s , int) (loop i) = ∣ basechange2 s (intLoop int) i ∣
-- -- Iso.rightInv S¹→S¹ (s , int) = ×≡ refl ((λ i → winding (basechange2-retr s (λ i → intLoop int i) i))
-- --                                        ∙ windingIntLoop int)
-- -- Iso.leftInv S¹→S¹ f = funExt λ { base → S¹map-id (f base)
-- --                                ; (loop i) j → helper2 j i}
-- --   where
-- --   helper2 : PathP (λ i → S¹map-id (f base) i ≡ S¹map-id (f base) i)
-- --                   (λ i → ∣ basechange2 (S¹map (f base)) (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁)))))) i ∣)
-- --                   (cong f loop)
-- --   helper2 i j = 
-- --     hcomp (λ k → λ { (i = i0) → cong ∣_∣ (basechange2 (S¹map (f base)) (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁))))))) j
-- --                     ; (i = i1) → S¹map-id (f (loop j)) k
-- --                     ; (j = i0) → S¹map-id (f base) (i ∧ k)
-- --                     ; (j = i1) → S¹map-id (f base) (i ∧ k)})
-- --           (helper4 i j)
-- --     where
-- --     helper4 : Path (Path (hLevelTrunc 3 _) _ _)
-- --                    (cong ∣_∣ (basechange2 (S¹map (f base))
-- --                                          (intLoop
-- --                                            (winding
-- --                                              (basechange2⁻ (S¹map (f base))
-- --                                                            (λ i₁ → S¹map (f (loop i₁))))))))
-- --                    λ i → ∣ S¹map (f (loop i)) ∣
-- --     helper4 i =
-- --       cong ∣_∣
-- --            ((cong (basechange2 (S¹map (f base)))
-- --                    (decodeEncode base (basechange2⁻ (S¹map (f base))
-- --                                                     (λ i₁ → S¹map (f (loop i₁)))))
-- --             ∙ basechange2-sect (S¹map (f base))
-- --                                (λ i → S¹map (f (loop i)))) i)

-- -- S1→S1→S1×Int : Iso ((S₊ 1) → hLevelTrunc 3 (S₊ 1)) ((hLevelTrunc 3 (S₊ 1)) × Int)
-- -- S1→S1→S1×Int = compIso helper2 (compIso S¹→S¹ helper)
-- --   where
-- --   helper : Iso (S¹ × Int) (hLevelTrunc 3 (S₊ 1) × Int)
-- --   Iso.fun helper (s , int) = ∣ S¹→S1 s  ∣ , int
-- --   Iso.inv helper (s , int) = (S1→S¹ (S1map s)) , int
-- --   Iso.rightInv helper (s , int) =
-- --     trElim {B = λ s → (∣ S¹→S1 (S1→S¹ (S1map s)) ∣ , int) ≡ (s , int)}
-- --            (λ _ → isOfHLevelPath 3 (isOfHLevelProd 3 (isOfHLevelTrunc 3) (isOfHLevelSuc 2 isSetInt)) _ _)
-- --            (λ a → ×≡ (cong ∣_∣ (S1→S¹-retr a)) refl)
-- --            s
-- --   Iso.leftInv helper (s , int) = ×≡ (S1→S¹-sect s) refl

-- --   helper2 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → hLevelTrunc 3 S¹)
-- --   Iso.fun helper2 f x = trMap S1→S¹ (f (S¹→S1 x))
-- --   Iso.inv helper2 f x = trMap S¹→S1 (f (S1→S¹ x))
-- --   Iso.rightInv helper2 f = funExt λ x i → helper3 (f (S1→S¹-sect x i)) i
-- --     where
-- --     helper3 : (x : hLevelTrunc 3 S¹) → trMap S1→S¹ (trMap S¹→S1 x) ≡ x
-- --     helper3 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
-- --                      λ a → cong ∣_∣ (S1→S¹-sect a)
-- --   Iso.leftInv helper2 f = funExt λ x i → helper3 (f (S1→S¹-retr x i)) i
-- --     where
-- --     helper3 : (x : hLevelTrunc 3 (S₊ 1)) → trMap S¹→S1 (trMap S1→S¹ x) ≡ x
-- --     helper3 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
-- --                      λ a → cong ∣_∣ (S1→S¹-retr a)

-- -- S¹→S¹≡S1→S1 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → hLevelTrunc 3 S¹)
-- -- Iso.fun S¹→S¹≡S1→S1 f x = trMap S1→S¹ (f (S¹→S1 x))
-- -- Iso.inv S¹→S¹≡S1→S1 f x = trMap S¹→S1 (f (S1→S¹ x))
-- -- Iso.rightInv S¹→S¹≡S1→S1 F = funExt λ x i → helper2 (F (S1→S¹-sect x i)) i
-- --   where
-- --   helper2 : (x : hLevelTrunc 3 S¹) → trMap S1→S¹ (trMap S¹→S1 x) ≡ x
-- --   helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
-- --                   λ a → cong ∣_∣ (S1→S¹-sect a)
-- -- Iso.leftInv S¹→S¹≡S1→S1 F = funExt λ x i → helper2 (F (S1→S¹-retr x i)) i
-- --   where
-- --   helper2 : (x : hLevelTrunc 3 (S₊ 1)) → trMap S¹→S1 (trMap S1→S¹ x) ≡ x
-- --   helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
-- --                   λ a → cong ∣_∣ (S1→S¹-retr a)




-- -- basechange-lemma : ∀ {ℓ} {A : Type ℓ} {a : A} (x y : S¹) (F : a ≡ a → S¹) (f : S¹ → a ≡ a) (g : S¹ → a ≡ a)
-- --                   → (f base ≡ refl)
-- --                   → (g base ≡ refl)
-- --                   → basechange2⁻ (F (f base ∙ g base)) (cong₂ {A = S¹} {B = λ x → S¹} (λ x y → F (f x ∙ g y)) loop loop)
-- --                    ≡ basechange2⁻ (F (f base)) (cong (λ x → F (f x)) loop) ∙ basechange2⁻ (F (g base)) (cong (λ x → F (g x)) loop)
-- -- basechange-lemma x y F f g frefl grefl  =
-- --     (λ i → basechange2⁻ (F (f base ∙ g base)) (cong₂Funct2 (λ x y → F (f x ∙ g y)) loop loop i))
-- --   ∙ (λ i → basechange2⁻ (F (f base ∙ g base)) (cong (λ x₁ → F (f x₁ ∙ g base)) loop ∙ cong (λ y₁ → F (f base ∙ g y₁)) loop))
-- --   ∙ basechange2⁻-morph (F (f base ∙ g base)) _ _
-- --   ∙ (λ j → basechange2⁻ (F (f base ∙ grefl j))
-- --                         (λ i → F (f (loop i) ∙ grefl j))
-- --           ∙ basechange2⁻ (F (frefl j ∙ g base))
-- --                         (λ i → F (frefl j ∙ g (loop i))))
-- --   ∙ ((λ j → basechange2⁻ (F (rUnit (f base) (~ j)))
-- --                         (λ i → F (rUnit (f (loop i)) (~ j)))
-- --           ∙ basechange2⁻ (F (lUnit (g base) (~ j)))
-- --                         (λ i → F (lUnit (g (loop i)) (~ j)))))


-- -- basechange-lemma2 : (f g : S¹ → hLevelTrunc 3 (S₊ 1)) (F : hLevelTrunc 3 (S₊ 1) → S¹)
-- --                  → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
-- --                   ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
-- --                   ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
-- -- basechange-lemma2 f g F = coInd f g F (f base) (g base) refl refl
-- --   where
-- --   coInd : (f g : S¹ → hLevelTrunc 3 (S₊ 1)) (F : hLevelTrunc 3 (S₊ 1) → S¹) (x y : hLevelTrunc 3 (S₊ 1))
-- --                    → f base ≡ x
-- --                    → g base ≡ y
-- --                    → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
-- --                     ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
-- --                     ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
-- --   coInd f g F =
-- --     elim2 (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isGroupoidS¹ base base)) _ _ )
-- --           (toProdElimSuspElim2
-- --             north
-- --             (λ _ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → isGroupoidS¹ _ _ _ _)
-- --             λ fid gid →
-- --                 (λ i → basechange2⁻ (F (f base +ₖ g base)) (cong₂Funct2 (λ x y → F (f x +ₖ g y)) loop loop i)) -- (λ i → F (f (loop i) +ₖ g (loop i))))
-- --               ∙ (basechange2⁻-morph (F (f base +ₖ g base))
-- --                                     (cong (λ x → F (f x +ₖ g base)) loop)
-- --                                     (cong (λ x → F (f base +ₖ g x)) loop))
-- --               ∙ (λ i → basechange2⁻ (F (f base +ₖ gid i)) (cong (λ x → F (f x +ₖ gid i)) loop)
-- --                       ∙ basechange2⁻ (F (fid i +ₖ g base)) (cong (λ x → F (fid i +ₖ g x)) loop))
-- --               ∙ (λ i → basechange2⁻ (F (rUnitₖ (f base) i)) (cong (λ x → F (rUnitₖ (f x) i)) loop)
-- --                       ∙ basechange2⁻ (F (lUnitₖ (g base) i)) (cong (λ x → F (lUnitₖ (g x) i)) loop)))



-- -- coHom1S1≃ℤ : grIso (coHomGr 1 (S₊ 1)) intGroup
-- -- coHom1S1≃ℤ =
-- --   Iso'→Iso
-- --     (iso'
-- --       (iso
-- --         (sRec isSetInt (λ f → proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f))))
-- --         (λ a → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹ (base , a)) ∣₀)
-- --          (λ a → (λ i → proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹ (base , a))))))
-- --               ∙ (λ i → proj₂ (Iso.fun S¹→S¹ (Iso.rightInv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹ (base , a)) i)))
-- --               ∙ λ i → proj₂ (Iso.rightInv S¹→S¹ (base , a) i)) 
-- --         (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --                λ f → (λ i → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹ (base , proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₀)
-- --                     ∙ (λ i → sRec setTruncIsSet
-- --                                   (λ x → ∣ Iso.inv S¹→S¹≡S1→S1 x ∣₀)
-- --                                   (sRec setTruncIsSet
-- --                                         (λ x → ∣ Iso.inv S¹→S¹ (x , (proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₀)
-- --                                         ∣ base ∣₀))
-- --                     ∙ (λ i → sRec setTruncIsSet
-- --                                   (λ x → ∣ Iso.inv S¹→S¹≡S1→S1 x ∣₀)
-- --                                   (sRec setTruncIsSet
-- --                                         (λ x → ∣ Iso.inv S¹→S¹ (x , (proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₀)
-- --                                         (Iso.inv PathIdTrunc₀Iso (isConnectedS¹ (proj₁ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f)))) i)))
-- --                     ∙ (λ i → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.leftInv S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f) i) ∣₀)
-- --                     ∙ (λ i → ∣ Iso.leftInv S¹→S¹≡S1→S1 f i ∣₀)))
-- --       (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
-- --               λ f g → (λ i → winding (basechange2⁻ (S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base))))))
-- --                                        (λ i → S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i)))))))))
-- --                     ∙ cong winding (helper2 (f (S¹→S1 base)) (g (S¹→S1 base)) f g refl refl)
-- --                     ∙ winding-hom ((basechange2⁻ (S¹map (trMap S1→S¹ (f north)))
-- --                                                  (λ i → S¹map (trMap S1→S¹ (f (S¹→S1 (loop i)))))))
-- --                                    ((basechange2⁻ (S¹map (trMap S1→S¹ (g north)))
-- --                                                  (λ i → S¹map (trMap S1→S¹ (g (S¹→S1 (loop i)))))))))


-- --   where
-- --   helper2 : (x y : hLevelTrunc 3 (S₊ 1)) (f g : S₊ 1 → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1)
-- --         → (f (S¹→S1 base)) ≡ x
-- --         → (g (S¹→S1 base)) ≡ y
-- --         → (basechange2⁻ (S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base)))))))
-- --                         (λ i → S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i)))))))
-- --           ≡ (basechange2⁻ (S¹map (trMap S1→S¹ ((f (S¹→S1 base))))))
-- --                           (λ i → S¹map (trMap S1→S¹ (f (S¹→S1 (loop i)))))
-- --           ∙ (basechange2⁻ (S¹map (trMap S1→S¹ ((g (S¹→S1 base)))))
-- --                           (λ i → S¹map (trMap S1→S¹ ((g (S¹→S1 (loop i)))))))
-- --   helper2 = elim2
-- --              (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3
-- --                  λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3
-- --                      λ _ → isOfHLevelPath 3 (isOfHLevelSuc 3 (isGroupoidS¹) base base) _ _)
-- --              (toProdElimSuspElim2 {A = S₊ 0} north
-- --                   (λ _ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → (isGroupoidS¹) _ _ _ _ )
-- --                   λ f g reflf reflg →
-- --                  (basechange-lemma
-- --                     base
-- --                     base
-- --                     (λ x → S¹map (trMap S1→S¹ (ΩKn+1→Kn x)))
-- --                     (λ x → Kn→ΩKn+1 1 (f (S¹→S1 x))) ((λ x → Kn→ΩKn+1 1 (g (S¹→S1 x))))
-- --                     (cong (Kn→ΩKn+1 1) reflf ∙ Kn→ΩKn+10ₖ 1)
-- --                     (cong (Kn→ΩKn+1 1) reflg ∙ Kn→ΩKn+10ₖ 1))
-- --                ∙ λ j → basechange2⁻ (S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 base)) j)))
-- --                                      (λ i → S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 (loop i))) j)))
-- --                       ∙ basechange2⁻ (S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 base)) j)))
-- --                                      (λ i → S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 (loop i))) j))))








-- -- indIntGroup : ∀ {ℓ} {G : Group ℓ} → (ϕ : Int → Group.type G)
-- --           → ϕ 0 ≡ isGroup.id (Group.groupStruc G)
-- --           → ((a : Int) → ϕ (a +ℤ 1) ≡ isGroup.comp (Group.groupStruc G) (ϕ a) (ϕ 1))
-- --           → ((n : Int) → ϕ (predInt n) ≡ isGroup.comp (Group.groupStruc G) (ϕ n) (ϕ (negsuc zero)))
-- --           → isMorph intGroup G ϕ
-- -- indIntGroup {G = group G gSet (group-struct _ _ _+G_ _ rUnit₁ _ _ _)} ϕ  zeroId _  _ n (pos zero) =
-- --   sym (rUnit₁ (ϕ n)) ∙ cong (λ x → ϕ n +G x) (sym zeroId)
-- -- indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)} ϕ zeroId oneId minOneId n (pos (suc m)) =
-- --     (λ i → ϕ ((n +pos m) +ℤ 1))
-- --   ∙ oneId (n +pos m)
-- --   ∙ cong (λ x → x +G ϕ (pos 1))
-- --          (indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)}
-- --                       ϕ zeroId oneId minOneId n (pos m))
-- --   ∙ assoc₁ (ϕ n) (ϕ (pos m)) (ϕ (pos 1))
-- --   ∙ sym (cong (λ x → ϕ n +G x) (oneId (pos m)))
-- -- indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)} ϕ zeroId _ minOneId n (negsuc zero) = minOneId n
-- -- indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)} ϕ zeroId a minOneId n (negsuc (suc m)) =
-- --     (λ i → ϕ ((n +negsuc m) +ℤ (negsuc zero)))
-- --   ∙ minOneId (n +negsuc m)
-- --   ∙ cong (λ x → x +G ϕ (negsuc zero)) (indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)} ϕ zeroId a minOneId n (negsuc m))
-- --   ∙ assoc₁ (ϕ n) (ϕ (negsuc m)) (ϕ (negsuc zero))
-- --   ∙ cong (λ x → ϕ n +G x) (sym (minOneId (negsuc m)))

-- -- pushoutSn : (n : ℕ) → Iso (S₊ (suc n)) (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt)
-- -- Iso.fun (pushoutSn n) north = inl tt
-- -- Iso.fun (pushoutSn n) south = inr tt
-- -- Iso.fun (pushoutSn n) (merid a i) = push a i
-- -- Iso.inv (pushoutSn n) (inl x) = north
-- -- Iso.inv (pushoutSn n) (inr x) = south
-- -- Iso.inv (pushoutSn n) (push a i) = merid a i
-- -- Iso.rightInv (pushoutSn n) (inl x) = refl
-- -- Iso.rightInv (pushoutSn n) (inr x) = refl
-- -- Iso.rightInv (pushoutSn n) (push a i) = refl
-- -- Iso.leftInv (pushoutSn n) north = refl
-- -- Iso.leftInv (pushoutSn n) south = refl
-- -- Iso.leftInv (pushoutSn n) (merid a i) = refl

-- -- Sn≡Pushout : (n : ℕ) → (S₊ (suc n)) ≡ (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt)
-- -- Sn≡Pushout n = isoToPath (pushoutSn n)

-- -- coHomPushout≡coHomSn' : (n m : ℕ) → grIso (coHomGr m (S₊ (suc n))) (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))
-- -- morph.fun (grIso.fun (coHomPushout≡coHomSn' n m)) =
-- --   sRec setTruncIsSet
-- --        λ f → ∣ (λ {(inl x) → f north ; (inr x) → f south ; (push a i) → f (merid a i)}) ∣₀
-- -- morph.ismorph (grIso.fun (coHomPushout≡coHomSn' n m)) =
-- --   sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --          λ a b → cong ∣_∣₀ (funExt λ {(inl x) → refl ; (inr x) → refl ; (push a i) → refl })
-- -- morph.fun (grIso.inv (coHomPushout≡coHomSn' n m)) = sRec setTruncIsSet (λ f → ∣ (λ {north → f (inl tt) ; south → f (inr tt) ; (merid a i) → f (push a i)}) ∣₀)
-- -- morph.ismorph (grIso.inv (coHomPushout≡coHomSn' n m)) = 
-- --   sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --          λ a b → cong ∣_∣₀ (funExt λ {north → refl ; south → refl ; (merid a i) → refl })
-- -- grIso.rightInv (coHomPushout≡coHomSn' n m) =
-- --   sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --          λ f → cong ∣_∣₀ (funExt λ {(inl x) → refl ; (inr x) → refl ; (push a i) → refl })
-- -- grIso.leftInv (coHomPushout≡coHomSn' n m) =
-- --   sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --          λ f → cong ∣_∣₀ (funExt λ {north → refl ; south → refl ; (merid a i) → refl })


-- -- isContr→≡Unit : {A : Type₀} → isContr A → A ≡ Unit
-- -- isContr→≡Unit contr = isoToPath (iso (λ _ → tt) (λ _ → fst contr) (λ _ → refl) λ _ → snd contr _)

-- -- isContr→isContrTrunc : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A → isContr (hLevelTrunc n A)
-- -- isContr→isContrTrunc n contr = ∣ fst contr ∣ , (trElim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (snd contr a))
-- -- isContr→isContrSetTrunc : ∀ {ℓ} {A : Type ℓ} → isContr A → isContr (∥ A ∥₀)
-- -- isContr→isContrSetTrunc contr = ∣ fst contr ∣₀ , sElim (λ _ → isOfHLevelPath 2 (setTruncIsSet) _ _) λ a → cong ∣_∣₀ (snd contr a)

-- -- coHomGrUnit0 : grIso (coHomGr 0 Unit) intGroup
-- -- grIso.fun coHomGrUnit0 = mph (sRec isSetInt (λ f → f tt))
-- --                              (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
-- --                                      (λ a b → addLemma (a tt) (b tt)))
-- -- grIso.inv coHomGrUnit0 = mph (λ a → ∣ (λ _ → a) ∣₀) (λ a b i → ∣ (λ _ → addLemma a b (~ i)) ∣₀)
-- -- grIso.rightInv coHomGrUnit0 a = refl
-- -- grIso.leftInv coHomGrUnit0 = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ a → refl

-- -- isContrCohomUnit : (n : ℕ) → isContr (coHom (suc n) Unit)
-- -- isContrCohomUnit n = subst isContr (λ i → ∥ UnitToTypeId (coHomK (suc n)) (~ i) ∥₀) (helper n)
-- --   where
-- --   helper : (n : ℕ) → isContr (∥ coHomK (suc n) ∥₀)
-- --   helper n = subst isContr ((isoToPath (truncOfTruncIso {A = S₊ (1 + n)} 2 (1 + n))) ∙ sym propTrunc≡Trunc0 ∙ λ i → ∥ hLevelTrunc (suc (+-comm n 2 i)) (S₊ (1 + n)) ∥₀)
-- --                             (isConnectedSubtr 2 (helper2 n .fst) (subst (λ x → isHLevelConnected x (S₊ (suc n))) (sym (helper2 n .snd)) (sphereConnected (suc n))) )
-- --     where
-- --     helper2 : (n : ℕ) → Σ[ m ∈ ℕ ] m + 2  ≡ 2 + n
-- --     helper2 zero = 0 , refl
-- --     helper2 (suc n) = (suc n) , λ i → suc (+-comm n 2 i)

-- -- coHomGrUnit≥1 : (n : ℕ) → grIso (coHomGr (suc n) Unit) trivialGroup
-- -- grIso.fun (coHomGrUnit≥1 n) = mph (λ _ → tt) (λ _ _ → refl)
-- -- grIso.inv (coHomGrUnit≥1 n) = mph (λ _ → ∣ (λ _ → ∣ north ∣) ∣₀) (λ _ _ → sym (rUnitₕ 0ₕ))
-- -- grIso.rightInv (coHomGrUnit≥1 n) a = refl
-- -- grIso.leftInv (coHomGrUnit≥1 n) a = sym (isContrCohomUnit n .snd 0ₕ) ∙ isContrCohomUnit n .snd a

-- -- S0→Int : (a : Int × Int) → S₊ 0 → Int
-- -- S0→Int a north = proj₁ a
-- -- S0→Int a south = proj₂ a

-- -- coHom0-S0 : grIso (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
-- -- coHom0-S0 =
-- --   Iso'→Iso
-- --     (iso'
-- --       (iso (sRec (isOfHLevelProd 2 isSetInt isSetInt)
-- --                  λ f → (f north) , (f south))
-- --            (λ a → ∣ S0→Int a ∣₀)
-- --            (λ { (a , b) → refl})
-- --            (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ f → cong ∣_∣₀ (funExt (λ {north → refl ; south → refl}))))
-- --       (sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 isSetInt isSetInt) _ _)
-- --               λ a b i → addLemma (a north) (b north) i , addLemma (a south) (b south) i))

-- -- ×morph : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group ℓ} {B : Group ℓ'} {C : Group ℓ''} {D : Group ℓ'''} → morph A B → morph C D → morph (dirProd A C) (dirProd B D) 
-- -- morph.fun (×morph mf1 mf2) =
-- --   (λ {(a , b) → (morph.fun mf1 a) , morph.fun mf2 b}) 
-- -- morph.ismorph (×morph mf1 mf2) =
-- --   (λ {(a , b) (c , d) i → morph.ismorph mf1 a c i , morph.ismorph mf2 b d i})


-- -- coHom0S1 : grIso intGroup (coHomGr 0 (S₊ 1))
-- -- coHom0S1 =
-- --   Iso'→Iso
-- --     (iso'
-- --       (iso
-- --         (λ a → ∣ (λ x → a) ∣₀)
-- --         (sRec isSetInt (λ f → f north))
-- --         (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --                λ f → cong ∣_∣₀ (funExt (toProdElimSuspRec north (λ _ → isSetInt _ _) refl)))
-- --         (λ a → refl))
-- --       λ a b → cong ∣_∣₀ (funExt λ x → sym (addLemma a b)))

-- -- coHom1S1 : grIso  intGroup (coHomGr 1 (S₊ 1))
-- -- coHom1S1 =
-- --   compGrIso
-- --     (diagonalIso1
-- --       _
-- --       (coHomGr 0 (S₊ 0))
-- --       _
-- --       (invGrIso coHom0-S0)
-- --       (d-morph _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0)
-- --       (λ x → MV.Ker-i⊂Im-d _ _(S₊ 0) (λ _ → tt) (λ _ → tt) 0 x
-- --                            (×≡ (isOfHLevelSuc 0 (isContrCohomUnit 0) _ _)
-- --                                (isOfHLevelSuc 0 (isContrCohomUnit 0) _ _)))
-- --       (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- --              (λ x inker
-- --                    → pRec propTruncIsProp
-- --                            (λ {((f , g) , id') → helper x f g id' inker})
-- --                            ((MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ x ∣₀ inker))))
-- --       (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --              λ F surj
-- --                → pRec (setTruncIsSet _ _) (λ { (x , id) → MV.Im-Δ⊂Ker-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₀ ∣ (∣ (λ _ → x) ∣₀ , ∣ (λ _ → 0) ∣₀) ,
-- --                                               (cong ∣_∣₀ (funExt (surjHelper x))) ∙ sym id ∣₋₁ }) surj) )
-- --     (invGrIso (coHomPushout≡coHomSn' 0 1))
                                              
-- --   where
-- --   surjHelper :  (x : Int) (x₁ : S₊ 0) → x +ₖ (-ₖ pos 0) ≡ S0→Int (x , x) x₁
-- --   surjHelper x north = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x
-- --   surjHelper x south = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x

-- --   helper : (F : S₊ 0 → Int) (f g : ∥ (Unit → Int) ∥₀) (id : MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (f , g) ≡ ∣ F ∣₀)
-- --          → isInKer (coHomGr 0 (S₊ 0))
-- --                     (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt)))
-- --                     (morph.fun (d-morph Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0))
-- --                     ∣ F ∣₀
-- --          → ∃[ x ∈ Int ] ∣ F ∣₀ ≡ morph.fun (grIso.inv coHom0-S0) (x , x)
-- --   helper F =
-- --     sElim2 (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- --            λ f g id inker
-- --              → pRec propTruncIsProp
-- --                      (λ {((a , b) , id2)
-- --                         → sElim2 {B = λ f g → MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (f , g) ≡ ∣ F ∣₀ → _ }
-- --                                   (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- --                                   (λ f g id → ∣ (helper2 f g .fst) , (sym id ∙ sym (helper2 f g .snd)) ∣₋₁)
-- --                                   a b id2})
-- --                      (MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₀ inker)
-- --     where
-- --     helper2 : (f g : Unit → Int)
-- --             → Σ[ x ∈ Int ] morph.fun (grIso.inv coHom0-S0) (x , x)
-- --              ≡ MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (∣ f ∣₀ , ∣ g ∣₀)
-- --     helper2 f g = (f _ +ₖ (-ₖ g _) ) , cong ∣_∣₀ (funExt (λ {north → refl ; south → refl})) 


-- -- coHom-n-Sn : (n : ℕ) → grIso intGroup (coHomGr (suc n) (S₊ (suc n)))
-- -- coHom-n-Sn zero = coHom1S1
-- -- coHom-n-Sn (suc n) =
-- --   compGrIso
-- --     (compGrIso
-- --       (coHom-n-Sn n)
-- --       theIso)
-- --     (invGrIso (coHomPushout≡coHomSn' (suc n) (suc (suc n))))
-- --   where
-- --   theIso : grIso (coHomGr (suc n) (S₊ (suc n))) (coHomGr (suc (suc n))
-- --                  (Pushout {A = S₊ (suc n)} (λ _ → tt) (λ _ → tt)))
-- --   theIso =
-- --     SES→Iso
-- --       (×coHomGr (suc n) Unit Unit)
-- --       (×coHomGr (suc (suc n)) Unit Unit)
-- --       (ses (λ p q → ×≡ (isOfHLevelSuc 0 (isContrCohomUnit n) (proj₁ p) (proj₁ q))
-- --                         (isOfHLevelSuc 0 (isContrCohomUnit n) (proj₂ p) (proj₂ q)))
-- --            (λ p q → ×≡ (isOfHLevelSuc 0 (isContrCohomUnit (suc n)) (proj₁ p) (proj₁ q))
-- --                         (isOfHLevelSuc 0 (isContrCohomUnit (suc n)) (proj₂ p) (proj₂ q)))
-- --            (Δ-morph _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
-- --            (i-morph _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (2 + n))
-- --            (d-morph _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
-- --            (MV.Ker-d⊂Im-Δ _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
-- --            (MV.Ker-i⊂Im-d _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n)))


-- -- setTruncIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso A B → Iso ∥ A ∥₀ ∥ B ∥₀
-- -- Iso.fun (setTruncIso is) = sRec setTruncIsSet (λ x → ∣ Iso.fun is x ∣₀)
-- -- Iso.inv (setTruncIso is) = sRec setTruncIsSet (λ x → ∣ Iso.inv is x ∣₀)
-- -- Iso.rightInv (setTruncIso is) = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ a → cong ∣_∣₀ (Iso.rightInv is a)
-- -- Iso.leftInv (setTruncIso is) = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ a → cong ∣_∣₀ (Iso.leftInv is a)

-- -- targetIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → Iso B C → Iso (A → B) (A → C)
-- -- Iso.fun (targetIso is) f a = Iso.fun is (f a)
-- -- Iso.inv (targetIso is) f a = Iso.inv is (f a)
-- -- Iso.rightInv (targetIso is) f = funExt λ a → Iso.rightInv is (f a)
-- -- Iso.leftInv (targetIso is) f = funExt λ a → Iso.leftInv is (f a)

-- -- coHom1Torus : grIso (coHomGr 1 ((S₊ 1) × (S₊ 1))) (dirProd intGroup intGroup)
-- -- coHom1Torus =
-- --   compGrIso
-- --     (Iso'→Iso
-- --       (iso' (compIso
-- --                 (setTruncIso (compIso
-- --                                schonfIso
-- --                                (compIso
-- --                                  (targetIso S1→S1→S1×Int)
-- --                                  funIso)))
-- --                 (setTruncOfProdIso))
-- --                 (sElim2
-- --                     (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
-- --                     λ f g → ×≡ (cong ∣_∣₀
-- --                                      (funExt (λ x → helper (f (x , S¹→S1 base) +ₖ g (x , S¹→S1 base))
-- --                                                    ∙ sym (cong₂ (λ x y → x +ₖ y)
-- --                                                                 (helper (f (x , S¹→S1 base)))
-- --                                                                 (helper (g (x , S¹→S1 base)))))))
-- --                                 (cong ∣_∣₀
-- --                                    (funExt
-- --                                      (toProdElimSuspRec
-- --                                         north
-- --                                         (λ _ → isSetInt _ _)
-- --                                         (cong winding
-- --                                               (basechange-lemma2
-- --                                                 (λ x → f (north , S¹→S1 x))
-- --                                                 (λ x → g (north , S¹→S1 x))
-- --                                                 λ x → S¹map (trMap S1→S¹ x))
-- --                                        ∙ winding-hom
-- --                                            (basechange2⁻
-- --                                                (S¹map (trMap S1→S¹ (f (north , S¹→S1 base))))
-- --                                                (λ i → S¹map (trMap S1→S¹ (f (north , S¹→S1 (loop i))))))
-- --                                            (basechange2⁻
-- --                                                (S¹map (trMap S1→S¹ (g (north , S¹→S1 base))))
-- --                                                (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i))))))
-- --                                        ∙ sym (addLemma
-- --                                                (winding
-- --                                                  (basechange2⁻
-- --                                                    (S¹map (trMap S1→S¹ (f (north , S¹→S1 base))))
-- --                                                    (λ i → S¹map (trMap S1→S¹ (f (north , S¹→S1 (loop i)))))))
-- --                                                (winding
-- --                                                  (basechange2⁻
-- --                                                    (S¹map (trMap S1→S¹ (g (north , S¹→S1 base))))
-- --                                                    (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i)))))))))))))))
-- --     (dirProdIso (invGrIso (coHom-n-Sn 0)) (invGrIso coHom0S1))

-- --   where
-- --   helper : (x : hLevelTrunc 3 (S₊ 1)) → ∣ S¹→S1 (S¹map (trMap S1→S¹ x)) ∣ ≡ x
-- --   helper = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ a → cong ∣_∣ (S1→S¹-retr a)




-- -- -- basechange* : (x y : S¹) → x ≡ y → x ≡ y → ΩS¹
-- -- -- basechange* x y = J (λ y p → (x ≡ y) → ΩS¹) (basechange x)


-- -- -- test1 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S₊ 1 × Int)
-- -- -- Iso.fun test1 f = (trRec isGroupoidS1 (λ a → a) (f north))
-- -- --                 , winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec2 isGroupoidS1 (λ x → x) (f (loop* i)))))
-- -- -- Iso.inv test1 (north , b) x = ∣ x ∣
-- -- -- Iso.inv test1 (south , b) x = ∣ x ∣
-- -- -- Iso.inv test1 (merid a i , b) x = {!!}
-- -- -- Iso.rightInv test1 = {!!}
-- -- -- Iso.leftInv test1 = {!!}

-- -- -- funRec : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) {C : (A → hLevelTrunc n B) → Type ℓ''}
-- -- --        → isOfHLevel n B
-- -- --        → ((f : A → B) → C (λ a → ∣ f a ∣))
-- -- --        → (f : A → hLevelTrunc n B) → C f
-- -- -- funRec {A = A} {B = B} n {C = C} hLev ind f = subst C (helper f) (ind (λ a → trRec hLev (λ x → x) (f a)))
-- -- --   where
-- -- --   helper : retract {A = A → hLevelTrunc n B} {B = A → B} (λ f₁ a → trRec hLev (λ x → x) (f₁ a)) (λ f₁ a → ∣ f₁ a ∣)
-- -- --   helper f = funExt λ a → helper2 (f a)
-- -- --     where
-- -- --     helper2 : (x : hLevelTrunc n B) → ∣ trRec hLev (λ x → x) x ∣ ≡ x
-- -- --     helper2 = trElim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → refl

-- -- -- invMapSurj : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') (ϕ : morph G H) → ((x : Group.type H) → isInIm G H (fst ϕ) x)
-- -- --           → morph H G
-- -- -- fst (invMapSurj G H (ϕ , pf) surj) a = {!pRec!}
-- -- -- snd (invMapSurj G H (ϕ , pf) surj) = {!!}

-- -- {-
-- -- ImIso : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') (ϕ : morph G H) → ((x : Group.type H) → isInIm G H (fst ϕ) x)
-- --       → grIso H (imGroup G H ϕ)
-- -- ImIso G H (ϕ , mf) surj =
-- --  let idH = isGroup.id (Group.groupStruc H)
-- --      idG = isGroup.id (Group.groupStruc G)
-- --      _+G_ = isGroup.comp (Group.groupStruc G)
-- --      _+H_ = isGroup.comp (Group.groupStruc H)
-- --      _+Im_ = isGroup.comp (Group.groupStruc (imGroup G H (ϕ , mf)))
-- --      invG = isGroup.inv (Group.groupStruc G)
-- --      invH = isGroup.inv (Group.groupStruc H)
-- --      lUnit = isGroup.lUnit (Group.groupStruc H)
-- --      lCancel = isGroup.rCancel (Group.groupStruc H)
-- --  in
-- --   Iso''→Iso _ _
-- --     (iso'' ((λ x → x , pRec propTruncIsProp (λ (a , b) → ∣ a , b ∣₋₁) (surj x))
-- --            , λ a b → pRec (Group.setStruc (imGroup G H (ϕ , mf)) _ _)
-- --                           (λ surja → pRec (Group.setStruc (imGroup G H (ϕ , mf)) _ _)
-- --                              (λ surjb →
-- --                                pRec (Group.setStruc (imGroup G H (ϕ , mf)) _ _)
-- --                                 (λ surja+b →
-- --                                 (λ i → (a +H b) , (pRec (propTruncIsProp)
-- --                                                          (λ (a , b) → ∣ a , b ∣₋₁)
-- --                                                          (propTruncIsProp (surj (isGroup.comp (Group.groupStruc H) a b)) ∣ surja+b ∣₋₁ i))) ∙
-- --                                  (λ i → (a +H b) , ∣ (fst surja+b) , (snd surja+b) ∣₋₁) ∙
-- --                                  ΣProp≡ (λ _ → propTruncIsProp) refl  ∙
-- --                                  λ i → (a +H b) ,  pRec (propTruncIsProp)
-- --                                                            (λ p1 →
-- --                                                               pRec (λ x y → squash x y)
-- --                                                               (λ p2 →
-- --                                                                  ∣
-- --                                                                  isGroup.comp (Group.groupStruc G) (fst p1) (fst p2) ,
-- --                                                                  mf (fst p1) (fst p2) ∙
-- --                                                                  cong₂ (isGroup.comp (Group.groupStruc H)) (snd p1) (snd p2)
-- --                                                                  ∣₋₁)
-- --                                                               (pRec (propTruncIsProp)
-- --                                                                ∣_∣₋₁ (propTruncIsProp ∣ surjb ∣₋₁ (surj b) i)))
-- --                                                            (pRec (propTruncIsProp)
-- --                                                             ∣_∣₋₁ (propTruncIsProp ∣ surja ∣₋₁ (surj a) i )))
-- --                                 (surj (isGroup.comp (Group.groupStruc H) a b)))
-- --                              (surj b))
-- --                           (surj a))
-- --            (λ x inker → cong fst inker)
-- --            λ x → pRec propTruncIsProp (λ inimx → ∣ (ϕ (inimx .fst)) , ΣProp≡ (λ _ → propTruncIsProp) (inimx .snd) ∣₋₁) (snd x))
-- -- -}


-- -- {-
-- -- H¹-S¹≃Int : grIso intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- H¹-S¹≃Int =
-- --   Iso''→Iso _ _
-- --     (iso'' ((λ x → ∣ theFuns x ∣₀) , λ a b → cong ∣_∣₀ (funExt λ x → sym (Iso.leftInv (Iso3-Kn-ΩKn+1 1) _) ∙ sym (cong (ΩKn+1→Kn) (theFunsId2 a b x))))
-- --            (λ x inker → pRec (isSetInt _ _) (inj x) (Iso.fun PathIdTrunc₀Iso inker))
-- --            finIm)
-- --   where
-- --   d : _
-- --   d = MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0

-- --   i : _
-- --   i = MV.i _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 1

-- --   Δ : _
-- --   Δ = MV.Δ _ _ (S₊ 1) (λ _ → tt) (λ _ → tt) 0


-- --   d-surj : (x : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- --          → isInIm (coHomGr 0 (S₊ 0)) (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0) x
-- --   d-surj = sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- --                   λ x → MV.Ker-i⊂Im-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ x ∣₀
-- --                         (sym (isContrHelper .snd _))
-- --       where
-- --       isContrHelper : isContr (Group.type (×coHomGr 1 Unit Unit))
-- --       isContrHelper = (∣ (λ _ → ∣ north ∣) ∣₀ , ∣ (λ _ → ∣ north ∣) ∣₀)
-- --                      , λ y → prodId (cong ∣_∣₀ (λ i _ → ∣ merid north i ∣) ∙ isContrCohomUnit 0 .snd (proj₁ y))
-- --                                      (cong ∣_∣₀ (λ i _ → ∣ merid north i ∣) ∙ isContrCohomUnit 0 .snd (proj₂ y))

-- --   theFuns : (a : Int) → Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt) → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1
-- --   theFuns a (inl x) = 0ₖ
-- --   theFuns a (inr x) = 0ₖ
-- --   theFuns a (push north i) = Kn→ΩKn+1 0 a i
-- --   theFuns a (push south i) = 0ₖ


-- --   theFunsId2 : (a b : Int) (x : Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))
-- --              → Kn→ΩKn+1 1 (theFuns a x) ∙ Kn→ΩKn+1 1 (theFuns b x) ≡ Kn→ΩKn+1 1 (theFuns (a +ℤ b) x)
-- --   theFunsId2 a b (inl x) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣) ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣))
-- --   theFunsId2 a b (inr x) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣) ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣))
-- --   theFunsId2 a b (push north i) j = 
-- --     hcomp (λ k → λ {(i = i0) → ((λ i₁ →
-- --              (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- --           ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
-- --          j
-- --                    ; (i = i1) → ((λ i₁ →
-- --              (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- --           ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
-- --          j
-- --                    ; (j = i0) → cong₂Funct2 (λ p q → Kn→ΩKn+1 1 p ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 a) (Kn→ΩKn+1 0 b) (~ k) i 
-- --                    ; (j = i1) → (helper2 a b) k i })
-- --           (hcomp (λ k → λ { (j = i0) → compPath-filler (cong (λ x₁ → Kn→ΩKn+1 1 x₁ ∙ Kn→ΩKn+1 1 ∣ north ∣) (Kn→ΩKn+1 0 a)) (cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b)) k i
-- --                            ; (j = i1) → compPath-filler (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a)) (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b)) k i
-- --                            ; (i = i1) → RHS-filler b j k
-- --                            ; (i = i0) → ((λ i₁ →
-- --              (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- --           ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
-- --          j})
-- --                  (bottom-filler a j i))

-- --     where

-- --     bottom-filler : (a : Int) →
-- --                   PathP (λ j → (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- --        (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣)
-- --        ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))
-- --       j ≡ (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- --        (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣)
-- --        ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))
-- --       j) (cong (λ x₁ → Kn→ΩKn+1 1 x₁ ∙ Kn→ΩKn+1 1 ∣ north ∣) (Kn→ΩKn+1 0 a)) (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a))
-- --     bottom-filler a j i =
-- --       hcomp (λ k → λ {(j = i0) → helper2 (~ k) i ;
-- --                        (j = i1) → cong (λ x → lUnit (Kn→ΩKn+1 1 x) (~ k)) (Kn→ΩKn+1 0 a) i})
-- --             ((λ j₂ → ∣ rCancel (merid north) j j₂ ∣) ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))

-- --        where
-- --        helper2 : Path (Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 ∣ north ∣ ≡ Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- --                       (λ i → Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- --                       (λ i → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))
-- --        helper2 = cong₂Sym1 (Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) (~ i) j ∣) (λ i → Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))

-- --     RHS-filler : (b : Int) →
-- --                PathP (λ j → (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) i j ∣) ∙ (sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))) j
-- --                            ≡ (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) i j ∣) ∙ (sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))) j)
-- --                      (cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b))
-- --                      (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b))
-- --     RHS-filler b j i =
-- --       hcomp (λ k → λ {(j = i0) → cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b) i ;
-- --                        (j = i1) → cong (λ x → lUnit (Kn→ΩKn+1 1 x) (~ k)) (Kn→ΩKn+1 0 b) i})
-- --             (cong (λ q → (λ i → ∣ rCancel (merid north) j i ∣) ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b) i)

-- --     helper2 : (a b : Int) → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a) ∙ cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b) ≡ cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (a +ℤ b))
-- --     helper2 a b =
-- --         sym (congFunct (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a) (Kn→ΩKn+1 0 b))
-- --       ∙ (λ i → cong (Kn→ΩKn+1 1) (Iso.rightInv (Iso3-Kn-ΩKn+1 0) (Kn→ΩKn+1 0 a ∙ Kn→ΩKn+1 0 b) (~ i)))
-- --       ∙ (λ i → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (a +ₖ b)) )
-- --       ∙ (λ i → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (addLemma a b i)))

-- --   theFunsId2 a b (push south i) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- --                                 ∙ sym (lUnit _)

-- --   inj : (a : Int) → theFuns a ≡ (λ _ → ∣ north ∣) → a ≡ pos 0
-- --   inj a id =
-- --     pRec (isSetInt _ _)
-- --          (sigmaElim (λ _ → isOfHLevelPath 2 isSetInt _ _)
-- --                     (λ a p → pRec (isSetInt _ _)
-- --                     (λ id2 →  sym (Iso.leftInv (Iso3-Kn-ΩKn+1 0) _)
-- --                              ∙ cong (ΩKn+1→Kn)
-- --                                  (PathP→compPathR
-- --                                    (cong (λ f → cong f (push north)) id)
-- --                                      ∙ test))
-- --                     (Iso.fun PathIdTrunc₀Iso p))) (d-surj ∣ theFuns a ∣₀)
-- --     where

-- --     test : (λ i → id i (inl tt)) ∙ (λ i → ∣ north ∣) ∙ sym (λ i → id i (inr tt)) ≡ refl
-- --     test = (λ i → cong (λ f → f (inl tt)) id
-- --          ∙ lUnit (sym (cong (λ f → f (inr tt)) id)) (~ i))
-- --          ∙ (λ i → cong (λ f → f (push south i)) id
-- --          ∙ sym (cong (λ f → f (inr tt)) id))
-- --          ∙ rCancel (cong (λ f → f (inr tt)) id)


-- --   consMember : (a : Int) → coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))
-- --   consMember a = d ∣ (λ _ → a) ∣₀

-- --   consMember≡0 : (a : Int) → consMember a ≡ 0ₕ
-- --   consMember≡0 a =
-- --            (MV.Im-Δ⊂Ker-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ (λ _ → a) ∣₀ ∣
-- --                 (∣ (λ _ → a) ∣₀ , ∣ (λ _ → 0) ∣₀)
-- --                 , cong ∣_∣₀ (λ i x → (rUnitₖ a i)) ∣₋₁)

-- --   f+consMember' : (f : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) → ∃[ x ∈ Int × Int ] (f +ₕ (-ₕ (consMember (proj₁ x))) ≡ ∣ theFuns (proj₂ x) ∣₀)
-- --   f+consMember' =
-- --     sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- --           λ f → pRec propTruncIsProp
-- --                       (sigmaElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- --                                  (λ g id → ∣ ((g south) , ((g north) +ₖ (-ₖ g south)))
-- --                                            , (pRec (setTruncIsSet _ _)
-- --                                                     (λ id → (λ i → ∣ id (~ i) ∣₀ +ₕ -ₕ ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (λ _ → g south) ∣₀) ∙ funId1 g)
-- --                                                     (Iso.fun PathIdTrunc₀Iso id)) ∣₋₁))
-- --                       (d-surj ∣ f ∣₀)
-- --     where
-- --     funId1 : (g : S₊ 0 → Int)
-- --            → ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g ∣₀ +ₕ -ₕ ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (λ _ → g south) ∣₀ ≡
-- --              ∣ theFuns ((g north) +ₖ (-ₖ (g south))) ∣₀
-- --     funId1 g = (λ i → ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g ∣₀
-- --                     +ₕ (morphMinus (coHomGr 0 (S₊ 0)) (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) d
-- --                                    (MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) ∣ (λ _ → g south) ∣₀ (~ i)))
-- --              ∙ sym (MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ g ∣₀ (-ₕ ∣ (λ _ → g south) ∣₀))
-- --              ∙ (cong (λ x → d ∣ x ∣₀) g'Id)
-- --              ∙ cong ∣_∣₀ helper
-- --       where
-- --       g' : S₊ 0 → Int
-- --       g' north = (g north) +ₖ (-ₖ (g south))
-- --       g' south = 0

-- --       g'Id : (λ x → g x +ₖ (-ₖ (g south))) ≡ g'
-- --       g'Id = funExt (λ {north → refl
-- --                       ; south → rCancelₖ (g south)})

-- --       helper : MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g' ≡ theFuns (g north +ₖ (-ₖ g south))
-- --       helper = funExt λ {(inl tt) → refl
-- --                        ; (inr tt) → refl
-- --                        ; (push north i) → refl
-- --                        ; (push south i) → refl}
-- --   finIm : (f : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) → ∃[ x ∈ Int ] (∣ theFuns x ∣₀ ≡ f)
-- --   finIm f =
-- --     pRec propTruncIsProp
-- --           (λ {((a , b) , id) → ∣ b , (sym id ∙ cong (λ x → f +ₕ x) ((λ i → (-ₕ (consMember≡0 a i))) ∙ sym (lUnitₕ (-ₕ 0ₕ)) ∙ rCancelₕ 0ₕ) ∙ (rUnitₕ f)) ∣₋₁})
-- --          (f+consMember' f)
-- -- -}



-- -- -- Hⁿ-Sⁿ≃Int : (n : ℕ) → grIso intGroup (coHomGr (suc n) (S₊ (suc n)))
-- -- -- Hⁿ-Sⁿ≃Int zero =
-- -- --   compGrIso {F = intGroup} {G = {!!}} {H = {!coHomGr 1 (S₊ 1)!}}
-- -- --     (Iso''→Iso
-- -- --       (iso'' ((λ x → ∣ theFuns x ∣₀) , λ a b → cong ∣_∣₀ (funExt λ x → sym (Iso.leftInv (Iso3-Kn-ΩKn+1 1) _) ∙ sym (cong (ΩKn+1→Kn) (theFunsId2 a b x))))
-- -- --              (λ x inker → pRec (isSetInt _ _) (inj x) (Iso.fun PathIdTrunc₀Iso inker))
-- -- --              finIm))
-- -- --     {!invGrIso _ _ (coHomPushout≡coHomSn 0 1)!}
-- -- --   where
-- -- --   d : _
-- -- --   d = MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0

-- -- --   i : _
-- -- --   i = MV.i _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 1

-- -- --   Δ : _
-- -- --   Δ = MV.Δ _ _ (S₊ 1) (λ _ → tt) (λ _ → tt) 0


-- -- --   d-surj : (x : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- --          → isInIm (coHomGr 0 (S₊ 0)) (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0) x
-- -- --   d-surj = sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- -- --                   λ x → MV.Ker-i⊂Im-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ x ∣₀
-- -- --                         (sym (isContrHelper .snd _))
-- -- --       where
-- -- --       isContrHelper : isContr (Group.type (×coHomGr 1 Unit Unit))
-- -- --       isContrHelper = (∣ (λ _ → ∣ north ∣) ∣₀ , ∣ (λ _ → ∣ north ∣) ∣₀)
-- -- --                      , λ y → prodId (cong ∣_∣₀ (λ i _ → ∣ merid north i ∣) ∙ isContrCohomUnit 0 .snd (proj₁ y))
-- -- --                                      (cong ∣_∣₀ (λ i _ → ∣ merid north i ∣) ∙ isContrCohomUnit 0 .snd (proj₂ y))

-- -- --   theFuns : (a : Int) → Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt) → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1
-- -- --   theFuns a (inl x) = 0ₖ
-- -- --   theFuns a (inr x) = 0ₖ
-- -- --   theFuns a (push north i) = Kn→ΩKn+1 0 a i
-- -- --   theFuns a (push south i) = 0ₖ


-- -- --   theFunsId2 : (a b : Int) (x : Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))
-- -- --              → Kn→ΩKn+1 1 (theFuns a x) ∙ Kn→ΩKn+1 1 (theFuns b x) ≡ Kn→ΩKn+1 1 (theFuns (a +ℤ b) x)
-- -- --   theFunsId2 a b (inl x) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣) ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣))
-- -- --   theFunsId2 a b (inr x) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣) ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣))
-- -- --   theFunsId2 a b (push north i) j = 
-- -- --     hcomp (λ k → λ {(i = i0) → ((λ i₁ →
-- -- --              (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- -- --           ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
-- -- --          j
-- -- --                    ; (i = i1) → ((λ i₁ →
-- -- --              (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- -- --           ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
-- -- --          j
-- -- --                    ; (j = i0) → cong₂Funct2 (λ p q → Kn→ΩKn+1 1 p ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 a) (Kn→ΩKn+1 0 b) (~ k) i 
-- -- --                    ; (j = i1) → (helper2 a b) k i })
-- -- --           (hcomp (λ k → λ { (j = i0) → compPath-filler (cong (λ x₁ → Kn→ΩKn+1 1 x₁ ∙ Kn→ΩKn+1 1 ∣ north ∣) (Kn→ΩKn+1 0 a)) (cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b)) k i
-- -- --                            ; (j = i1) → compPath-filler (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a)) (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b)) k i
-- -- --                            ; (i = i1) → RHS-filler b j k
-- -- --                            ; (i = i0) → ((λ i₁ →
-- -- --              (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- -- --           ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
-- -- --          j})
-- -- --                  (bottom-filler a j i))

-- -- --     where

-- -- --     bottom-filler : (a : Int) →
-- -- --                   PathP (λ j → (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- -- --        (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣)
-- -- --        ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))
-- -- --       j ≡ (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- -- --        (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣)
-- -- --        ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))
-- -- --       j) (cong (λ x₁ → Kn→ΩKn+1 1 x₁ ∙ Kn→ΩKn+1 1 ∣ north ∣) (Kn→ΩKn+1 0 a)) (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a))
-- -- --     bottom-filler a j i =
-- -- --       hcomp (λ k → λ {(j = i0) → helper2 (~ k) i ;
-- -- --                        (j = i1) → cong (λ x → lUnit (Kn→ΩKn+1 1 x) (~ k)) (Kn→ΩKn+1 0 a) i})
-- -- --             ((λ j₂ → ∣ rCancel (merid north) j j₂ ∣) ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))

-- -- --        where
-- -- --        helper2 : Path (Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 ∣ north ∣ ≡ Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- -- --                       (λ i → Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- -- --                       (λ i → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))
-- -- --        helper2 = cong₂Sym1 (Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) (~ i) j ∣) (λ i → Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))

-- -- --     RHS-filler : (b : Int) →
-- -- --                PathP (λ j → (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) i j ∣) ∙ (sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))) j
-- -- --                            ≡ (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) i j ∣) ∙ (sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))) j)
-- -- --                      (cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b))
-- -- --                      (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b))
-- -- --     RHS-filler b j i =
-- -- --       hcomp (λ k → λ {(j = i0) → cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b) i ;
-- -- --                        (j = i1) → cong (λ x → lUnit (Kn→ΩKn+1 1 x) (~ k)) (Kn→ΩKn+1 0 b) i})
-- -- --             (cong (λ q → (λ i → ∣ rCancel (merid north) j i ∣) ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b) i)

-- -- --     helper2 : (a b : Int) → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a) ∙ cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b) ≡ cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (a +ℤ b))
-- -- --     helper2 a b =
-- -- --         sym (congFunct (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a) (Kn→ΩKn+1 0 b))
-- -- --       ∙ (λ i → cong (Kn→ΩKn+1 1) (Iso.rightInv (Iso3-Kn-ΩKn+1 0) (Kn→ΩKn+1 0 a ∙ Kn→ΩKn+1 0 b) (~ i)))
-- -- --       ∙ (λ i → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (a +ₖ b)) )
-- -- --       ∙ (λ i → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (addLemma a b i)))

-- -- --   theFunsId2 a b (push south i) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
-- -- --                                 ∙ sym (lUnit _)

-- -- --   inj : (a : Int) → theFuns a ≡ (λ _ → ∣ north ∣) → a ≡ pos 0
-- -- --   inj a id =
-- -- --     pRec (isSetInt _ _)
-- -- --          (sigmaElim (λ _ → isOfHLevelPath 2 isSetInt _ _)
-- -- --                     (λ a p → pRec (isSetInt _ _)
-- -- --                     (λ id2 →  sym (Iso.leftInv (Iso3-Kn-ΩKn+1 0) _)
-- -- --                              ∙ cong (ΩKn+1→Kn)
-- -- --                                  (PathP→compPathR
-- -- --                                    (cong (λ f → cong f (push north)) id)
-- -- --                                      ∙ test))
-- -- --                     (Iso.fun PathIdTrunc₀Iso p))) (d-surj ∣ theFuns a ∣₀)
-- -- --     where

-- -- --     test : (λ i → id i (inl tt)) ∙ (λ i → ∣ north ∣) ∙ sym (λ i → id i (inr tt)) ≡ refl
-- -- --     test = (λ i → cong (λ f → f (inl tt)) id
-- -- --          ∙ lUnit (sym (cong (λ f → f (inr tt)) id)) (~ i))
-- -- --          ∙ (λ i → cong (λ f → f (push south i)) id
-- -- --          ∙ sym (cong (λ f → f (inr tt)) id))
-- -- --          ∙ rCancel (cong (λ f → f (inr tt)) id)


-- -- --   consMember : (a : Int) → coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))
-- -- --   consMember a = d ∣ (λ _ → a) ∣₀

-- -- --   consMember≡0 : (a : Int) → consMember a ≡ 0ₕ
-- -- --   consMember≡0 a =
-- -- --            (MV.Im-Δ⊂Ker-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ (λ _ → a) ∣₀ ∣
-- -- --                 (∣ (λ _ → a) ∣₀ , ∣ (λ _ → 0) ∣₀)
-- -- --                 , cong ∣_∣₀ (λ i x → (rUnitₖ a i)) ∣₋₁)

-- -- --   f+consMember' : (f : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) → ∃[ x ∈ Int × Int ] (f +ₕ (-ₕ (consMember (proj₁ x))) ≡ ∣ theFuns (proj₂ x) ∣₀)
-- -- --   f+consMember' =
-- -- --     sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- -- --           λ f → pRec propTruncIsProp
-- -- --                       (sigmaElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- -- --                                  (λ g id → ∣ ((g south) , ((g north) +ₖ (-ₖ g south)))
-- -- --                                            , (pRec (setTruncIsSet _ _)
-- -- --                                                     (λ id → (λ i → ∣ id (~ i) ∣₀ +ₕ -ₕ ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (λ _ → g south) ∣₀) ∙ funId1 g)
-- -- --                                                     (Iso.fun PathIdTrunc₀Iso id)) ∣₋₁))
-- -- --                       (d-surj ∣ f ∣₀)
-- -- --     where
-- -- --     funId1 : (g : S₊ 0 → Int)
-- -- --            → ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g ∣₀ +ₕ -ₕ ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (λ _ → g south) ∣₀ ≡
-- -- --              ∣ theFuns ((g north) +ₖ (-ₖ (g south))) ∣₀
-- -- --     funId1 g = (λ i → ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g ∣₀
-- -- --                     +ₕ (morphMinus (coHomGr 0 (S₊ 0)) (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) d
-- -- --                                    (MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) ∣ (λ _ → g south) ∣₀ (~ i)))
-- -- --              ∙ sym (MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ g ∣₀ (-ₕ ∣ (λ _ → g south) ∣₀))
-- -- --              ∙ (cong (λ x → d ∣ x ∣₀) g'Id)
-- -- --              ∙ cong ∣_∣₀ helper
-- -- --       where
-- -- --       g' : S₊ 0 → Int
-- -- --       g' north = (g north) +ₖ (-ₖ (g south))
-- -- --       g' south = 0

-- -- --       g'Id : (λ x → g x +ₖ (-ₖ (g south))) ≡ g'
-- -- --       g'Id = funExt (λ {north → refl
-- -- --                       ; south → rCancelₖ (g south)})

-- -- --       helper : MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g' ≡ theFuns (g north +ₖ (-ₖ g south))
-- -- --       helper = funExt λ {(inl tt) → refl
-- -- --                        ; (inr tt) → refl
-- -- --                        ; (push north i) → refl
-- -- --                        ; (push south i) → refl}
-- -- --   finIm : (f : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) → ∃[ x ∈ Int ] (∣ theFuns x ∣₀ ≡ f)
-- -- --   finIm f =
-- -- --     pRec propTruncIsProp
-- -- --           (λ {((a , b) , id) → ∣ b , (sym id ∙ cong (λ x → f +ₕ x) ((λ i → (-ₕ (consMember≡0 a i))) ∙ sym (lUnitₕ (-ₕ 0ₕ)) ∙ rCancelₕ 0ₕ) ∙ (rUnitₕ f)) ∣₋₁})
-- -- --          (f+consMember' f)
-- -- -- Hⁿ-Sⁿ≃Int (suc n) =
-- -- --   compGrIso (Hⁿ-Sⁿ≃Int n)
-- -- --             (transport (λ i → grIso {!!} {!coHomGr (suc (suc n)) (Pushout (λ _ → tt) (λ _ → tt))!}) {!!})


-- -- -- {-
-- -- -- coHom1S1≃ℤ : grIso intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- grIso.fun coHom1S1≃ℤ = grIso.fun {!compGrIso coHom1Iso (invGrIso _ _ (ImIso _ _ (d-morph _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0) ?))!}
-- -- -- grIso.inv coHom1S1≃ℤ = {!!}
-- -- -- grIso.rightInv coHom1S1≃ℤ = {!!}
-- -- -- grIso.leftInv coHom1S1≃ℤ = {!!}
-- -- -- -}

-- -- -- -- compGrIso coHom1Iso (invGrIso _ _ (ImIso _ _ {!d-morph _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0!} {!!}))


-- -- -- -- coHomGrIm : grIso (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- --                   (imGroup (coHomGr 0 (S₊ 0))
-- -- -- --                            (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- --                            (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0
-- -- -- --                            , MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0))
-- -- -- -- coHomGrIm =
-- -- -- --   ImIso _
-- -- -- --         _
-- -- -- --         _
-- -- -- --         {!!}


-- -- -- -- -- coHom1RedS1 : Iso (coHom 1 (S₊ 1)) (coHomRed 1 (S₊ 1 , north))
-- -- -- -- -- Iso.fun coHom1RedS1 = sRec setTruncIsSet λ f → ∣ f , (pRec {!!} {!!} ((transport (λ i → (b : truncIdempotent 3 {!S₊ 1!} (~ i)) → ∥ (transp (λ j → truncIdempotent {!3!} {!!} (~ i ∨ (~ j))) (~ i) north) ≡ b ∥₋₁) isConnectedS1) (f north)) ) ∣₀
-- -- -- -- -- Iso.inv coHom1RedS1 = {!!}
-- -- -- -- -- Iso.rightInv coHom1RedS1 = {!setTruncIdempotent!}
-- -- -- -- -- Iso.leftInv coHom1RedS1 = {!!}

-- -- -- -- -- coHom1Red : ∀ {ℓ} (A : Pointed ℓ) → Iso (coHom 1 (typ A)) (coHomRed 1 A)
-- -- -- -- -- Iso.fun (coHom1Red A) = sRec setTruncIsSet λ f → ∣ f , {!!} ∣₀
-- -- -- -- -- Iso.inv (coHom1Red A) = {!!}
-- -- -- -- -- Iso.rightInv (coHom1Red A) = {!!}
-- -- -- -- -- Iso.leftInv (coHom1Red A) = {!!}

-- -- -- -- -- -- morphtest : morph (coHomGr 1 (S₊ 1)) intGroup
-- -- -- -- -- -- fst morphtest = sRec isSetInt λ f → winding (basechange _  λ i → SuspBool→S¹ (S1→SuspBool (trRec2 isGroupoidS1 (λ x → x) (f (loop* i)))))
-- -- -- -- -- -- snd morphtest = sElim2 {!!}
-- -- -- -- -- --                        (funRec 3 isGroupoidS1
-- -- -- -- -- --                          λ f → funRec 3 isGroupoidS1
-- -- -- -- -- --                            λ g → pRec (isSetInt _ _)
-- -- -- -- -- --                                    (λ n=fn →
-- -- -- -- -- --                                      pRec (isSetInt _ _)
-- -- -- -- -- --                                           (λ n=gn → (λ j → winding (basechange  (SuspBool→S¹ (S1→SuspBool (trRec2 isGroupoidS1 (λ x → x) (∣ f (north) ∣ +ₖ ∣ n=gn (~ j) ∣))))  (λ i → SuspBool→S¹ (S1→SuspBool (trRec2 isGroupoidS1 (λ x → x) (∣ f (loop* i) ∣ +ₖ ∣ transp (λ i → n=gn ((~ i) ∨ (~ j)) ≡ n=gn ((~ i) ∨ (~ j))) (~ j) (λ i → g (loop* i)) i ∣)))))) 
-- -- -- -- -- --                                                    ∙ {!!}
-- -- -- -- -- --                                                    ∙ {!!})
-- -- -- -- -- --                                           (isConnectedS1 (g north)))
-- -- -- -- -- --                                    (isConnectedS1 (f north)))


-- -- -- -- -- -- {- (λ i → winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (∣ f (loop* i) ∣ +ₖ ∣ g (loop* i) ∣)))))
-- -- -- -- -- --                                 ∙ (λ i → winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn (Kn→ΩKn+1 1 ∣ f (loop* i) ∣ ∙ Kn→ΩKn+1 1 ∣ g (loop* i) ∣))))))
-- -- -- -- -- --                                 ∙ (λ j → winding (basechange _ (cong (λ x → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn (Kn→ΩKn+1 1 ∣ f x ∣ ∙ Kn→ΩKn+1 1 ∣ g x ∣))))) loop*)) )
-- -- -- -- -- --                                 ∙ (λ i → winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn ((cong ∣_∣ (merid (f (loop* i)) ∙ sym (merid north)) ∙ cong ∣_∣ (merid (g (loop* i)) ∙ sym (merid north)))))))))
-- -- -- -- -- --                                 ∙ (λ j → winding (basechange _  λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn (congFunct ∣_∣ (merid (f (loop* i)) ∙ sym (merid north)) (merid (g (loop* i)) ∙ sym (merid north)) (~ j)))))))
-- -- -- -- -- --                                 ∙ (λ j → winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn (cong ∣_∣ (({!!} ∙ {!!}) ∙ {!!})))))))
-- -- -- -- -- --                                 ∙ {!!}
-- -- -- -- -- --                                 ∙ {!!}
-- -- -- -- -- --                                 ∙ {!!}) -}

-- -- -- -- -- --   where
-- -- -- -- -- --   helper : ∀ {ℓ} {A : Type ℓ} (a : A) (f : A → S¹) (p q : a ≡ a) → winding (basechange (f a) (cong f (p ∙ q))) ≡ winding (basechange (f a) (cong f p ∙ cong f q))
-- -- -- -- -- --   helper a f p q i = winding (basechange (f a) (congFunct f p q i))
-- -- -- -- -- --   helper2 : (x : S¹) (p q : x ≡ x) → basechange x (p ∙ q) ≡ basechange x p ∙ basechange x q
-- -- -- -- -- --   helper2 base p q = refl
-- -- -- -- -- --   helper2 (loop i) p q = {!!}
-- -- -- -- -- --   helper4 : (x y z : S¹) (p : x ≡ z) (q r : x ≡ y) (s : y ≡ z) → basechange* x z p (q ∙ s)  ≡ basechange* x y {!!} q ∙ {!!} 
-- -- -- -- -- --   helper4 = {!!}
-- -- -- -- -- --   helper3 : (p q : ΩS¹) → winding (p ∙ q) ≡ (winding p +ℤ winding q)
-- -- -- -- -- --   helper3 = {!!}


-- -- -- -- -- -- -- fstmap : morph (dirProd intGroup intGroup) (coHomGr 0 (S₊ 0))
-- -- -- -- -- -- -- fstmap = compMorph {F = dirProd intGroup intGroup} {G = ×coHomGr 0 Unit Unit} {H = coHomGr 0 (S₊ 0)}
-- -- -- -- -- -- --                    (×morph (grIso.inv coHomGrUnit0) (grIso.inv coHomGrUnit0))
-- -- -- -- -- -- --                    (((MV.Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) zero)) ,
-- -- -- -- -- -- --                      {!MV.ΔIsHom _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) zero!})

-- -- -- -- -- -- -- fstMapId : (a : Int × Int) → fstmap .fst a ≡ ∣ (λ _ → proj₁ a +ℤ (0 - proj₂ a)) ∣₀
-- -- -- -- -- -- -- fstMapId (a , b) = (λ i → ∣ (λ _ → a +ₖ (-ₖ b)) ∣₀) ∙ {!addLemma!} ∙ {!!} ∙ {!!}

-- -- -- -- -- -- -- isoAgain : grIso intGroup (coHomGr 1 (S₊ 1))
-- -- -- -- -- -- -- isoAgain =
-- -- -- -- -- -- --   Iso''→Iso _ _
-- -- -- -- -- -- --              (iso'' ((λ a → ∣ (λ {north → 0ₖ ; south → 0ₖ ; (merid north i) → {!a!} ; (merid south i) → {!!}}) ∣₀) , {!!})
-- -- -- -- -- -- --                     {!!}
-- -- -- -- -- -- --                     {!!})

-- -- -- -- -- -- -- -- -- test2 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → S¹) 
-- -- -- -- -- -- -- -- -- Iso.fun test2 f = {!!}
-- -- -- -- -- -- -- -- -- Iso.inv test2 f north = ∣ transport (sym S¹≡S1) (f base) ∣
-- -- -- -- -- -- -- -- -- Iso.inv test2 f south = ∣ transport (sym S¹≡S1) (f base) ∣
-- -- -- -- -- -- -- -- -- Iso.inv test2 f (merid a i) = cong ∣_∣ {!transport (sym S¹≡S1) (f base)!} i
-- -- -- -- -- -- -- -- -- Iso.rightInv test2 = {!!}
-- -- -- -- -- -- -- -- -- Iso.leftInv test2 = {!!}

-- -- -- -- -- -- -- -- -- F : winding (basechange base loop) ≡ 1
-- -- -- -- -- -- -- -- -- F = refl

-- -- -- -- -- -- -- -- -- another : (f g : Int) → winding (basechange {!!} {!!}) ≡ {!!}
-- -- -- -- -- -- -- -- -- another = {!!}

-- -- -- -- -- -- -- -- -- test : Iso (S¹ → S¹) (S¹ × Int)
-- -- -- -- -- -- -- -- -- Iso.fun test f = f base , winding (basechange (f base) (cong f loop))
-- -- -- -- -- -- -- -- -- Iso.inv test (x , int) base = x
-- -- -- -- -- -- -- -- -- Iso.inv test (x , int) (loop i) = {!!}
-- -- -- -- -- -- -- -- -- Iso.rightInv test = {!!}
-- -- -- -- -- -- -- -- -- Iso.leftInv test = {!!}

-- -- -- -- -- -- -- -- -- -- test13 : Iso ∥ (S¹ → S¹) ∥₀ Int
-- -- -- -- -- -- -- -- -- -- Iso.fun test13 = sRec isSetInt λ f → winding (basechange (f base) (λ i → f (loop i)))
-- -- -- -- -- -- -- -- -- -- Iso.inv test13 a = ∣ (λ {base → {!!} ; (loop i) → {!!}}) ∣₀
-- -- -- -- -- -- -- -- -- -- Iso.rightInv test13 = {!!}
-- -- -- -- -- -- -- -- -- -- Iso.leftInv test13 = {!!}

-- -- -- -- -- -- -- -- -- -- test : Iso (S¹ → S¹) (S¹ × Int)
-- -- -- -- -- -- -- -- -- -- Iso.fun test f = (f base) , transport (basedΩS¹≡Int (f base)) λ i → f (loop i)
-- -- -- -- -- -- -- -- -- -- Iso.inv test (x , int) base = x
-- -- -- -- -- -- -- -- -- -- Iso.inv test (x , int) (loop i) = transport (sym (basedΩS¹≡Int x)) int i
-- -- -- -- -- -- -- -- -- -- Iso.rightInv test (x , int) i = (x , transportTransport⁻ (basedΩS¹≡Int x) int i)
-- -- -- -- -- -- -- -- -- -- Iso.leftInv test f =
-- -- -- -- -- -- -- -- -- --   funExt λ { base → refl
-- -- -- -- -- -- -- -- -- --           ; (loop i) j → transport⁻Transport (basedΩS¹≡Int (f base)) (λ i → f (loop i)) j i}


-- -- -- -- -- -- -- -- -- -- lem : S¹ ≡ hLevelTrunc 3 (S₊ 1) 
-- -- -- -- -- -- -- -- -- -- lem = sym (truncIdempotent 3 isGroupoidS¹) ∙ λ i → hLevelTrunc 3 (S¹≡S1 (~ i))

-- -- -- -- -- -- -- -- -- -- prodId : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a b : A × B) → proj₁ a ≡ proj₁ b → proj₂ a ≡ proj₂ b → a ≡ b
-- -- -- -- -- -- -- -- -- -- prodId (_ , _) (_ , _) id1 id2 i = (id1 i) , (id2 i)

-- -- -- -- -- -- -- -- -- -- test22 : Iso (S₊ 1 → coHomK 1) (S₊ 1 × Int)
-- -- -- -- -- -- -- -- -- -- Iso.fun test22 f = {!f north!} , {!!}
-- -- -- -- -- -- -- -- -- -- Iso.inv test22 = {!!}
-- -- -- -- -- -- -- -- -- -- Iso.rightInv test22 = {!!}
-- -- -- -- -- -- -- -- -- -- Iso.leftInv test22 = {!!}






-- -- -- -- -- -- -- -- -- -- coHom1≃∥S1×ℤ∥₀ : Iso (coHom 1 (S₊ 1)) ∥ S₊ 1 × Int ∥₀
-- -- -- -- -- -- -- -- -- -- coHom1≃∥S1×ℤ∥₀ = setTruncIso test2
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   test2 : Iso (S₊ 1 → coHomK 1) (S₊ 1 × Int)
-- -- -- -- -- -- -- -- -- --   Iso.fun test2 f = transport (λ i → S¹≡S1 (~ i) × Int) (Iso.fun test (transport (λ i → (S¹≡S1 i → lem (~ i))) f))
-- -- -- -- -- -- -- -- -- --   Iso.inv test2 x = transport (λ i → (S¹≡S1 (~ i) → lem i)) (Iso.inv test (transport (λ i → S¹≡S1 i × Int) x))
-- -- -- -- -- -- -- -- -- --   Iso.rightInv test2 (s , int) = prodId _ _ {!!} {!!}
-- -- -- -- -- -- -- -- -- --   Iso.leftInv test2 f = {!!} ∙ {!!} ∙ {!!}

-- -- -- -- -- -- -- -- -- --   test2Id : (a b : (S₊ 1 → coHomK 1)) → proj₂ (Iso.fun test2 (λ x →  a x +ₖ b x)) ≡ (proj₂ (Iso.fun test2 a) +ₖ proj₂ (Iso.fun test2 a))
-- -- -- -- -- -- -- -- -- --   test2Id a b = {!
-- -- -- -- -- -- -- -- -- --     transport
-- -- -- -- -- -- -- -- -- --       (basedΩS¹≡Int
-- -- -- -- -- -- -- -- -- --        (transport (λ i → S¹≡S1 i → lem (~ i)) (λ x → a x +ₖ b x) base))
-- -- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- -- --          transport (λ i₁ → S¹≡S1 i₁ → lem (~ i₁)) (λ x → a x +ₖ b x)
-- -- -- -- -- -- -- -- -- --          (loop i))!} ∙ {!transport (λ i → S¹≡S1 i → lem (~ i)) (λ x → a x +ₖ b x) base!}


-- -- -- -- -- -- -- -- -- -- main : grIso intGroup (coHomGr 1 (S₊ 1))
-- -- -- -- -- -- -- -- -- -- main = Iso'→Iso
-- -- -- -- -- -- -- -- -- --        (iso' {!!}
-- -- -- -- -- -- -- -- -- --              {!!})


-- -- -- -- -- -- -- -- coHom1 : grIso (coHomGr 1 (S₊ 1)) intGroup
-- -- -- -- -- -- -- -- coHom1 =
-- -- -- -- -- -- -- --   Iso'→Iso
-- -- -- -- -- -- -- --     (iso' (iso ({!!} ∘ {!!} ∘ {!!} ∘ {!!})
-- -- -- -- -- -- -- --                {!!}
-- -- -- -- -- -- -- --                {!!}
-- -- -- -- -- -- -- --                {!!})
-- -- -- -- -- -- -- --           {!!})



-- -- -- -- -- -- -- -- schonf : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : (A × B) → Type ℓ''}
-- -- -- -- -- -- -- --          → ((a : A) (b : B) → C (a , b))
-- -- -- -- -- -- -- --          → (x : A × B) → C x
-- -- -- -- -- -- -- -- schonf f (a , b) = f a b

-- -- -- -- -- -- -- -- -- -- setTruncProdIso : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Iso ∥ (A × B) ∥₀ (∥ A ∥₀ × ∥ B ∥₀)
-- -- -- -- -- -- -- -- -- -- Iso.fun (setTruncProdIso A B) = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) λ {(a , b) → ∣ a ∣₀ , ∣ b ∣₀}
-- -- -- -- -- -- -- -- -- -- Iso.inv (setTruncProdIso A B) (a , b) = sRec setTruncIsSet (λ a → sRec setTruncIsSet (λ b → ∣ a , b ∣₀) b) a
-- -- -- -- -- -- -- -- -- -- Iso.rightInv (setTruncProdIso A B) =
-- -- -- -- -- -- -- -- -- --   schonf (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
-- -- -- -- -- -- -- -- -- --                  λ _ → sElim (λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
-- -- -- -- -- -- -- -- -- --                                λ _ → refl)
-- -- -- -- -- -- -- -- -- -- Iso.leftInv (setTruncProdIso A B) = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ {(a , b) → refl}

-- -- -- -- -- -- -- -- -- -- setTruncProdLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a1 a2 : A) (b : B) → isHLevelConnected 2 A
-- -- -- -- -- -- -- -- -- --                  → Path ∥ A × B ∥₀ ∣ a1 , b ∣₀ ∣ a2 , b ∣₀ 
-- -- -- -- -- -- -- -- -- -- setTruncProdLemma {A = A} {B = B} a1 a2 b conA i = Iso.inv (setTruncProdIso A B) (Iso.inv setTruncTrunc0Iso ((sym (conA .snd ∣ a1 ∣) ∙ (conA .snd ∣ a2 ∣)) i) , ∣ b ∣₀)

-- -- -- -- -- -- -- -- -- -- test3 : Iso ∥ S₊ 1 × Int ∥₀ Int 
-- -- -- -- -- -- -- -- -- -- Iso.fun test3 = sRec isSetInt proj₂
-- -- -- -- -- -- -- -- -- -- Iso.inv test3 a = ∣ north , a ∣₀
-- -- -- -- -- -- -- -- -- -- Iso.rightInv test3 a = refl
-- -- -- -- -- -- -- -- -- -- Iso.leftInv test3 =
-- -- -- -- -- -- -- -- -- --   sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- -- -- -- -- -- -- -- -- --         λ {(s , int) → setTruncProdLemma north s int (sphereConnected 1)}

-- -- -- -- -- -- -- -- -- -- coHomGr0-S1 : grIso intGroup (coHomGr 1 (S₊ 1))
-- -- -- -- -- -- -- -- -- -- coHomGr0-S1 =
-- -- -- -- -- -- -- -- -- --   Iso'→Iso
-- -- -- -- -- -- -- -- -- --     (iso' (compIso (symIso test3) (symIso coHom1≃∥S1×ℤ∥₀))
-- -- -- -- -- -- -- -- -- --           (indIntGroup {G = coHomGr 1 (S₊ 1)}
-- -- -- -- -- -- -- -- -- --                        (Iso.fun (compIso (symIso test3) (symIso coHom1≃∥S1×ℤ∥₀)))
-- -- -- -- -- -- -- -- -- --                        ((λ i → ∣ transport (λ i → (S¹≡S1 (~ i) → lem i)) (Iso.inv test (base , 0)) ∣₀)
-- -- -- -- -- -- -- -- -- --                          ∙ (λ i → ∣ transport (λ i → (S¹≡S1 (~ i) → lem i)) (helper2 i) ∣₀)
-- -- -- -- -- -- -- -- -- --                          ∙ cong ∣_∣₀ (funExt λ {north → refl ; south → refl ; (merid a i) → {!!}}))
-- -- -- -- -- -- -- -- -- --                        {!!}
-- -- -- -- -- -- -- -- -- --                        {!!}))
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     helper : basedΩS¹≡ΩS¹ base ≡ {!basechange!}
-- -- -- -- -- -- -- -- -- --     helper = {!substComposite!}

-- -- -- -- -- -- -- -- -- --     substComposite2 : ∀ {ℓ} {A B C : Type ℓ}
-- -- -- -- -- -- -- -- -- --                       (P : A ≡ B) (Q : B ≡ C) (a : A)
-- -- -- -- -- -- -- -- -- --                    → transport (P ∙ Q) a ≡ transport Q (transport P a) 
-- -- -- -- -- -- -- -- -- --     substComposite2 = {!!}

-- -- -- -- -- -- -- -- -- --     helper1 : transport (λ i → S¹≡S1 i × Int) (north , 0) ≡ (base , 0)
-- -- -- -- -- -- -- -- -- --     helper1 = refl
-- -- -- -- -- -- -- -- -- --     helper3 : transport (sym (basedΩS¹≡Int base)) 0 ≡ refl
-- -- -- -- -- -- -- -- -- --     helper3 = (λ i → transport (symDistr (basedΩS¹≡ΩS¹ base) ΩS¹≡Int i) 0)
-- -- -- -- -- -- -- -- -- --             ∙ substComposite2 (sym ΩS¹≡Int) (sym (basedΩS¹≡ΩS¹ base)) 0
-- -- -- -- -- -- -- -- -- --             ∙ (λ i → transport (λ i → basedΩS¹≡ΩS¹ base (~ i)) refl) -- 
-- -- -- -- -- -- -- -- -- --             ∙ transportRefl ((equiv-proof (basechange-isequiv base) refl) .fst .fst)
-- -- -- -- -- -- -- -- -- --             ∙ (λ i → equiv-proof (transport (λ j → isEquiv (refl-conjugation j)) (basedΩS¹→ΩS¹-isequiv i0)) refl .fst .fst)
-- -- -- -- -- -- -- -- -- --             ∙ (λ i → {!equiv-proof (transport (λ j → isEquiv (refl-conjugation j)) (basedΩS¹→ΩS¹-isequiv i0)) refl .fst!})
-- -- -- -- -- -- -- -- -- --             ∙ {!basedΩS¹→ΩS¹!}
-- -- -- -- -- -- -- -- -- --             ∙ {!!}
-- -- -- -- -- -- -- -- -- --             ∙ {!!}
-- -- -- -- -- -- -- -- -- --     helper4 : (x : S¹) → Iso.inv test (base , 0) x ≡ x
-- -- -- -- -- -- -- -- -- --     helper4 = {!!}
-- -- -- -- -- -- -- -- -- --     helper2 : Iso.inv test (transport (λ i → S¹≡S1 i × Int) (north , 0)) ≡ λ x → x
-- -- -- -- -- -- -- -- -- --     helper2 = (λ i → Iso.inv test (base , 0)) ∙ {!!} ∙ {!!}

-- -- -- -- -- -- -- -- prodId : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A × B} → proj₁ x ≡ proj₁ y → proj₂ x ≡ proj₂ y → x ≡ y
-- -- -- -- -- -- -- -- prodId {x = (a , b)} {y = (c , d)} id1 id2 i = (id1 i) , (id2 i)

-- -- -- -- -- -- -- -- fstFunHelper : (x : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- -- -- -- -- --              → isInIm (coHomGr 0 (S₊ 0)) (coHomGr 1 _) (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) x
-- -- -- -- -- -- -- -- fstFunHelper a = MV.Ker-i⊂Im-d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 a
-- -- -- -- -- -- -- --                  (sym (isContrH1Unit×H1Unit .snd _) ∙ (isContrH1Unit×H1Unit .snd _))
-- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- --    isContrH1Unit×H1Unit : isContr (Group.type (×coHomGr 1 Unit Unit))
-- -- -- -- -- -- -- --    isContrH1Unit×H1Unit = (∣ (λ _ → ∣ north ∣) ∣₀ , ∣ (λ _ → ∣ north ∣) ∣₀)
-- -- -- -- -- -- -- --                         ,  λ {(a , b) → sigmaProdElim {D = λ (x : Σ[ x ∈ Group.type (×coHomGr 1 Unit Unit)] Unit) → (∣ (λ _ → ∣ north ∣) ∣₀ , ∣ (λ _ → ∣ north ∣) ∣₀) ≡ fst x}
-- -- -- -- -- -- -- --                                                        (λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
-- -- -- -- -- -- -- --                                                        (λ a b _ → prodId (grIso.leftInv (coHomGrUnit≥1 0) ∣ a ∣₀) (grIso.leftInv (coHomGrUnit≥1 0) ∣ b ∣₀)) ((a , b) , tt)}



-- -- -- -- -- -- -- -- helperMorph : isMorph intGroup (dirProd intGroup intGroup) λ a → a , (0 - a)
-- -- -- -- -- -- -- -- helperMorph =
-- -- -- -- -- -- -- --   indIntGroup {G = dirProd intGroup intGroup}
-- -- -- -- -- -- -- --                (λ a → a , (0 - a))
-- -- -- -- -- -- -- --                refl
-- -- -- -- -- -- -- --                (λ a → prodId refl (helper2 a))
-- -- -- -- -- -- -- --                λ a → prodId refl (helper3 a)
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   helper1 : (a : Int) → predInt (sucInt a) ≡ a
-- -- -- -- -- -- -- --   helper1 (pos zero) = refl
-- -- -- -- -- -- -- --   helper1 (pos (suc n)) = refl
-- -- -- -- -- -- -- --   helper1 (negsuc zero) = refl
-- -- -- -- -- -- -- --   helper1 (negsuc (suc n)) = refl

-- -- -- -- -- -- -- --   helper4 : (a : Int) → sucInt (predInt a) ≡ a
-- -- -- -- -- -- -- --   helper4 (pos zero) = refl
-- -- -- -- -- -- -- --   helper4 (pos (suc n)) = refl
-- -- -- -- -- -- -- --   helper4 (negsuc zero) = refl
-- -- -- -- -- -- -- --   helper4 (negsuc (suc n)) = refl

-- -- -- -- -- -- -- --   helper2 : (a : Int) → (pos 0 - sucInt a) ≡ predInt (pos 0 - a)
-- -- -- -- -- -- -- --   helper2 (pos zero) = refl
-- -- -- -- -- -- -- --   helper2 (pos (suc n)) = refl
-- -- -- -- -- -- -- --   helper2 (negsuc zero) = refl
-- -- -- -- -- -- -- --   helper2 (negsuc (suc n)) = sym (helper1 _)

-- -- -- -- -- -- -- --   helper3 : (a : Int) → (pos 0 - predInt a) ≡ sucInt (pos 0 - a)
-- -- -- -- -- -- -- --   helper3 (pos zero) = refl
-- -- -- -- -- -- -- --   helper3 (pos (suc zero)) = refl
-- -- -- -- -- -- -- --   helper3 (pos (suc (suc n))) = sym (helper4 _)
-- -- -- -- -- -- -- --   helper3 (negsuc zero) = refl
-- -- -- -- -- -- -- --   helper3 (negsuc (suc n)) = refl

-- -- -- -- -- -- -- --   helper : (a b : Int) → (pos 0 - (a +ℤ b)) ≡ ((pos 0 - a) +ℤ (pos 0 - b))
-- -- -- -- -- -- -- --   helper a (pos zero) = refl
-- -- -- -- -- -- -- --   helper (pos zero) (pos (suc n)) =
-- -- -- -- -- -- -- --       cong (λ x → pos 0 - sucInt x) (+ℤ-comm (pos zero) (pos n))
-- -- -- -- -- -- -- --     ∙ +ℤ-comm (pos 0 +negsuc n) (pos zero)
-- -- -- -- -- -- -- --   helper (pos (suc n₁)) (pos (suc n)) =
-- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- --   helper (negsuc n₁) (pos (suc n)) = {!!}
-- -- -- -- -- -- -- --   helper a (negsuc n) = {!!}

-- -- -- -- -- -- -- -- fun : morph intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- -- -- -- -- -- fst fun = MV.d _ _ _ (λ _ → tt) (λ _ → tt) 0 ∘ grIso.inv coHom0-S0 .fst  ∘ λ a → a , (0 - a)
-- -- -- -- -- -- -- -- snd fun = {!!}
-- -- -- -- -- -- -- -- {- compMorph {F = intGroup} {G = dirProd intGroup intGroup} {H = coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))}
-- -- -- -- -- -- -- --                     ((λ a → a , a) , (λ a b → refl))
-- -- -- -- -- -- -- --                     (compMorph {F = dirProd intGroup intGroup} {G = coHomGr 0 (S₊ 0)} {H = coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))} (grIso.inv coHom0-S0)
-- -- -- -- -- -- -- --                                (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0
-- -- -- -- -- -- -- --                                 , MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0)) .snd -}
-- -- -- -- -- -- -- -- {- theIso : grIso intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- -- -- -- -- -- theIso = Iso''→Iso _ _
-- -- -- -- -- -- -- --          (iso'' ((λ x → ∣ (λ {(inl tt) → 0ₖ ; (inr tt) → 0ₖ ; (push a i) → Kn→ΩKn+1 0 x i}) ∣₀) , {!!})
-- -- -- -- -- -- -- --                 {!!}
-- -- -- -- -- -- -- --                 {!MV.d!})
-- -- -- -- -- -- -- -- -}



-- -- -- -- -- -- -- -- theIso : grIso intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- -- -- -- -- -- theIso =
-- -- -- -- -- -- -- --   Iso''→Iso _ _
-- -- -- -- -- -- -- --    (iso'' fun
-- -- -- -- -- -- -- --           (λ x inker → {!MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0
-- -- -- -- -- -- -- --          (grIso.inv coHom0-S0 .fst (g , g))!})
-- -- -- -- -- -- -- --           (sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- -- -- -- -- -- -- --                  λ x → pRec propTruncIsProp
-- -- -- -- -- -- -- --                             (λ {(a , b) → {!fun!} })
-- -- -- -- -- -- -- --                             (fstFunHelper (∣ x ∣₀))))  
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   whoKnows : (a : S₊ 0 → Int) (x : MV.D Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt)) → MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (λ _ → a north) x
-- -- -- -- -- -- -- --       ≡ MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 a x
-- -- -- -- -- -- -- --   whoKnows a (inl x) = refl
-- -- -- -- -- -- -- --   whoKnows a (inr x) = refl
-- -- -- -- -- -- -- --   whoKnows a (push north i) = refl
-- -- -- -- -- -- -- --   whoKnows a (push south i) j = {!!}

-- -- -- -- -- -- -- --   helper : (a : Int) → (grIso.inv coHom0-S0 .fst (a , a)) ≡ ∣ S0→Int (a , a) ∣₀
-- -- -- -- -- -- -- --   helper a = {!have :

-- -- -- -- -- -- -- -- ∣
-- -- -- -- -- -- -- -- MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0
-- -- -- -- -- -- -- -- (S0→Int (x , x))
-- -- -- -- -- -- -- -- ∣₀
-- -- -- -- -- -- -- -- ≡ ∣ (λ _ → ∣ north ∣) ∣₀!}

-- -- -- -- -- -- -- --   helper2 : (a b : Int) → MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (a , a)) ≡ MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (b , b))
-- -- -- -- -- -- -- --          → a ≡ b
-- -- -- -- -- -- -- --   helper2 a b id = pRec (isSetInt a b) (λ {(pt , id) → {!!}}) (fstFunHelper ∣ (MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (a , a))) ∣₀)

-- -- -- -- -- -- -- --   idFun : (a : Int) → MV.D Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1
-- -- -- -- -- -- -- --   idFun a (inl x) = 0ₖ
-- -- -- -- -- -- -- --   idFun a (inr x) = 0ₖ
-- -- -- -- -- -- -- --   idFun a (push north i) = Kn→ΩKn+1 zero a i
-- -- -- -- -- -- -- --   idFun a (push south i) = Kn→ΩKn+1 zero a i

-- -- -- -- -- -- -- --   helper3 : (a : Int) → (MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (a , a))) ≡ idFun a
-- -- -- -- -- -- -- --   helper3 a = funExt λ {(inl x) → refl ; (inr x) → refl ; (push north i) → refl ; (push south i) → refl }

-- -- -- -- -- -- -- --   helper4 : (a b : Int) → MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (a , a))  ≡ MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (b , b))
-- -- -- -- -- -- -- --           → a ≡ b
-- -- -- -- -- -- -- --   helper4 a b id =
-- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- --    ∙ {!!}
-- -- -- -- -- -- -- --    ∙ {!!}
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     helper5 : {!!} --PathP (λ k → id k (inl tt) ≡ id k (inr tt)) (Kn→ΩKn+1 zero a) (Kn→ΩKn+1 zero a)
-- -- -- -- -- -- -- --     helper5 i j = {!id i!}

-- -- -- -- -- -- -- -- -- fun : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)) → coHom 0 (S₊ 0)
-- -- -- -- -- -- -- -- -- fun a = (pRec {P = Σ[ x ∈ coHom 0 (S₊ 0)] (MV.d _ _ _ (λ _ → tt) (λ _ → tt) 0 x ≡ a) × isInIm (×coHomGr 0 Unit Unit) (coHomGr 0 (S₊ 0)) (MV.Δ _ _ _ (λ _ → tt) (λ _ → tt) 0) x}
-- -- -- -- -- -- -- -- --               (λ {(a1 , b) (c , d) → ΣProp≡ (λ x → isOfHLevelProd 1 (setTruncIsSet _ _) propTruncIsProp)
-- -- -- -- -- -- -- -- --                                             (sElim2 {B = λ a1 c → (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 a1 ≡ a)
-- -- -- -- -- -- -- -- --                                                                 → MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 c ≡ a
-- -- -- -- -- -- -- -- --                                                                 → isInIm (×coHomGr 0 Unit Unit) (coHomGr 0 (S₊ 0))
-- -- -- -- -- -- -- -- --                                                                           (λ z → MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 z) a1
-- -- -- -- -- -- -- -- --                                                                 → isInIm (×coHomGr 0 Unit Unit) (coHomGr 0 (S₊ 0))
-- -- -- -- -- -- -- -- --                                                                    (λ z → MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 z) c → a1 ≡ c}
-- -- -- -- -- -- -- -- --                                                     (λ _ _ → {!!})
-- -- -- -- -- -- -- -- --                                                     (λ a c b1 d1 → pElim (λ _ → isOfHLevelΠ 1 λ _ → setTruncIsSet _ _)
-- -- -- -- -- -- -- -- --                                                                      λ b2 → pElim (λ _ → setTruncIsSet _ _)
-- -- -- -- -- -- -- -- --                                                                               λ d2 → {!d2!})
-- -- -- -- -- -- -- -- --                                                     a1 c (proj₁ b) (proj₁ d) (proj₂ b) (proj₂ d))})
-- -- -- -- -- -- -- -- --               (λ {(a , b) → a , b , MV.Ker-d⊂Im-Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 a {!!}})
-- -- -- -- -- -- -- -- --               (fstFunHelper a)) .fst -- pRec {!!} {!!} (fstFunHelper a)
