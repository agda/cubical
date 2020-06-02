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


open import Cubical.ZCohomology.KcompPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)



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

indIntGroup : ∀ {ℓ} {G : Group ℓ} → (ϕ : Int → Group.type G)
          → ϕ 0 ≡ isGroup.id (Group.groupStruc G)
          → ((a : Int) → ϕ (a +ℤ 1) ≡ isGroup.comp (Group.groupStruc G) (ϕ a) (ϕ 1))
          → ((n : Int) → ϕ (predInt n) ≡ isGroup.comp (Group.groupStruc G) (ϕ n) (ϕ (negsuc zero)))
          → isMorph intGroup G ϕ
indIntGroup {G = group G gSet (group-struct _ _ _+G_ _ rUnit₁ _ _ _)} ϕ  zeroId _  _ n (pos zero) =
  sym (rUnit₁ (ϕ n)) ∙ cong (λ x → ϕ n +G x) (sym zeroId)
indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)} ϕ zeroId oneId minOneId n (pos (suc m)) =
    (λ i → ϕ ((n +pos m) +ℤ 1))
  ∙ oneId (n +pos m)
  ∙ cong (λ x → x +G ϕ (pos 1))
         (indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)}
                      ϕ zeroId oneId minOneId n (pos m))
  ∙ assoc₁ (ϕ n) (ϕ (pos m)) (ϕ (pos 1))
  ∙ sym (cong (λ x → ϕ n +G x) (oneId (pos m)))
indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)} ϕ zeroId _ minOneId n (negsuc zero) = minOneId n
indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)} ϕ zeroId a minOneId n (negsuc (suc m)) =
    (λ i → ϕ ((n +negsuc m) +ℤ (negsuc zero)))
  ∙ minOneId (n +negsuc m)
  ∙ cong (λ x → x +G ϕ (negsuc zero)) (indIntGroup {G = group G gSet (group-struct id inv₁ _+G_ lUnit₁ rUnit₁ assoc₁ lCancel₁ rCancel₁)} ϕ zeroId a minOneId n (negsuc m))
  ∙ assoc₁ (ϕ n) (ϕ (negsuc m)) (ϕ (negsuc zero))
  ∙ cong (λ x → ϕ n +G x) (sym (minOneId (negsuc m)))

pushoutSn : (n : ℕ) → Iso (S₊ (suc n)) (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt)
Iso.fun (pushoutSn n) north = inl tt
Iso.fun (pushoutSn n) south = inr tt
Iso.fun (pushoutSn n) (merid a i) = push a i
Iso.inv (pushoutSn n) (inl x) = north
Iso.inv (pushoutSn n) (inr x) = south
Iso.inv (pushoutSn n) (push a i) = merid a i
Iso.rightInv (pushoutSn n) (inl x) = refl
Iso.rightInv (pushoutSn n) (inr x) = refl
Iso.rightInv (pushoutSn n) (push a i) = refl
Iso.leftInv (pushoutSn n) north = refl
Iso.leftInv (pushoutSn n) south = refl
Iso.leftInv (pushoutSn n) (merid a i) = refl

Sn≡Pushout : (n : ℕ) → (S₊ (suc n)) ≡ (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt)
Sn≡Pushout n = isoToPath (pushoutSn n)


coHomPushout≡coHomSn : (n m : ℕ) → grIso (coHomGr m (S₊ (suc n))) (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))
grIso.fun (coHomPushout≡coHomSn n m) = (sRec setTruncIsSet λ f → ∣ (λ {(inl x) → f north ; (inr x) → f south ; (push a i) → f (merid a i)}) ∣₀)
                                     , sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                              λ a b → cong ∣_∣₀ (funExt λ {(inl x) → refl ; (inr x) → refl ; (push a i) → refl })
grIso.inv (coHomPushout≡coHomSn n m) = sRec setTruncIsSet (λ f → ∣ (λ {north → f (inl tt) ; south → f (inr tt) ; (merid a i) → f (push a i)}) ∣₀)
                                     , sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                              λ a b → cong ∣_∣₀ (funExt λ {north → refl ; south → refl ; (merid a i) → refl })
grIso.rightInv (coHomPushout≡coHomSn n m) = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                                  λ f → cong ∣_∣₀ (funExt λ {(inl x) → refl ; (inr x) → refl ; (push a i) → refl })
grIso.leftInv (coHomPushout≡coHomSn n m) = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                                 λ f → cong ∣_∣₀ (funExt λ {north → refl ; south → refl ; (merid a i) → refl })

isContr→≡Unit : {A : Type₀} → isContr A → A ≡ Unit
isContr→≡Unit contr = isoToPath (iso (λ _ → tt) (λ _ → fst contr) (λ _ → refl) λ _ → snd contr _)

isContr→isContrTrunc : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A → isContr (hLevelTrunc n A)
isContr→isContrTrunc n contr = ∣ fst contr ∣ , (trElim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (snd contr a))
isContr→isContrSetTrunc : ∀ {ℓ} {A : Type ℓ} → isContr A → isContr (∥ A ∥₀)
isContr→isContrSetTrunc contr = ∣ fst contr ∣₀ , sElim (λ _ → isOfHLevelPath 2 (setTruncIsSet) _ _) λ a → cong ∣_∣₀ (snd contr a)

coHomGrUnit0 : grIso (coHomGr 0 Unit) intGroup
grIso.fun coHomGrUnit0 = sRec isSetInt (λ f → f tt) ,
                         sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ a b → addLemma (a tt) (b tt)
grIso.inv coHomGrUnit0 = (λ a → ∣ (λ _ → a) ∣₀) , λ a b i → ∣ (λ _ → addLemma a b (~ i)) ∣₀
grIso.rightInv coHomGrUnit0 a = refl
grIso.leftInv coHomGrUnit0 = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ a → refl

isContrCohomUnit : (n : ℕ) → isContr (coHom (suc n) Unit)
isContrCohomUnit n = subst isContr (λ i → ∥ UnitToTypeId (coHomK (suc n)) (~ i) ∥₀) (helper n)
  where
  helper : (n : ℕ) → isContr (∥ coHomK (suc n) ∥₀)
  helper n = subst isContr ((isoToPath (truncOfTruncIso {A = S₊ (1 + n)} 2 (1 + n))) ∙ sym propTrunc≡Trunc0 ∙ λ i → ∥ hLevelTrunc (suc (+-comm n 2 i)) (S₊ (1 + n)) ∥₀)
                            (isConnectedSubtr 2 (helper2 n .fst) (subst (λ x → isHLevelConnected x (S₊ (suc n))) (sym (helper2 n .snd)) (sphereConnected (suc n))) )
    where
    helper2 : (n : ℕ) → Σ[ m ∈ ℕ ] m + 2  ≡ 2 + n
    helper2 zero = 0 , refl
    helper2 (suc n) = (suc n) , λ i → suc (+-comm n 2 i)

coHomGrUnit≥1 : (n : ℕ) → grIso (coHomGr (suc n) Unit) trivialGroup
grIso.fun (coHomGrUnit≥1 n) = (λ _ → tt) , (λ _ _ → refl)
grIso.inv (coHomGrUnit≥1 n) = (λ _ → ∣ (λ _ → ∣ north ∣) ∣₀) , λ _ _ → sym (rUnitₕ 0ₕ)
grIso.rightInv (coHomGrUnit≥1 n) a = refl
grIso.leftInv (coHomGrUnit≥1 n) a = sym (isContrCohomUnit n .snd 0ₕ) ∙ isContrCohomUnit n .snd a

S0→Int : (a : Int × Int) → S₊ 0 → Int
S0→Int a north = proj₁ a
S0→Int a south = proj₂ a

coHom0-S0 : grIso (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
coHom0-S0 =
  Iso'→Iso
    (iso'
      (iso (sRec (isOfHLevelProd 2 isSetInt isSetInt)
                 λ f → (f north) , (f south))
           (λ a → ∣ S0→Int a ∣₀)
           (λ { (a , b) → refl})
           (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ f → cong ∣_∣₀ (funExt (λ {north → refl ; south → refl}))))
      (sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 isSetInt isSetInt) _ _)
              λ a b i → addLemma (a north) (b north) i , addLemma (a south) (b south) i))

×morph : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group ℓ} {B : Group ℓ'} {C : Group ℓ''} {D : Group ℓ'''} → morph A B → morph C D → morph (dirProd A C) (dirProd B D) 
×morph mf1 mf2 = (λ {(a , b) → (mf1 .fst a) , mf2 .fst b}) , λ {(a , b) (c , d) i → mf1 .snd a c i , mf2 .snd b d i}



isGroupoidS1 : isGroupoid (S₊ 1)
isGroupoidS1 = transport (λ i → isGroupoid (S¹≡S1 (~ i))) isGroupoidS¹
isConnectedS1 : (x : S₊ 1) → ∥ north ≡ x ∥₋₁
isConnectedS1 x = pRec propTruncIsProp
                       (λ p → ∣ cong (transport (sym (S¹≡S1))) p ∙ transport⁻Transport (S¹≡S1) x ∣₋₁)
                       (isConnectedS¹ (transport S¹≡S1 x))

-- basechange* : (x y : S¹) → x ≡ y → x ≡ y → ΩS¹
-- basechange* x y = J (λ y p → (x ≡ y) → ΩS¹) (basechange x)


-- test1 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S₊ 1 × Int)
-- Iso.fun test1 f = (trRec isGroupoidS1 (λ a → a) (f north))
--                 , winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec2 isGroupoidS1 (λ x → x) (f (loop* i)))))
-- Iso.inv test1 (north , b) x = ∣ x ∣
-- Iso.inv test1 (south , b) x = ∣ x ∣
-- Iso.inv test1 (merid a i , b) x = {!!}
-- Iso.rightInv test1 = {!!}
-- Iso.leftInv test1 = {!!}

-- funRec : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) {C : (A → hLevelTrunc n B) → Type ℓ''}
--        → isOfHLevel n B
--        → ((f : A → B) → C (λ a → ∣ f a ∣))
--        → (f : A → hLevelTrunc n B) → C f
-- funRec {A = A} {B = B} n {C = C} hLev ind f = subst C (helper f) (ind (λ a → trRec hLev (λ x → x) (f a)))
--   where
--   helper : retract {A = A → hLevelTrunc n B} {B = A → B} (λ f₁ a → trRec hLev (λ x → x) (f₁ a)) (λ f₁ a → ∣ f₁ a ∣)
--   helper f = funExt λ a → helper2 (f a)
--     where
--     helper2 : (x : hLevelTrunc n B) → ∣ trRec hLev (λ x → x) x ∣ ≡ x
--     helper2 = trElim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → refl

-- invMapSurj : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') (ϕ : morph G H) → ((x : Group.type H) → isInIm G H (fst ϕ) x)
--           → morph H G
-- fst (invMapSurj G H (ϕ , pf) surj) a = {!pRec!}
-- snd (invMapSurj G H (ϕ , pf) surj) = {!!}

ImIso : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') (ϕ : morph G H) → ((x : Group.type H) → isInIm G H (fst ϕ) x)
      → grIso H (imGroup G H ϕ)
ImIso G H (ϕ , mf) surj =
 let idH = isGroup.id (Group.groupStruc H)
     idG = isGroup.id (Group.groupStruc G)
     _+G_ = isGroup.comp (Group.groupStruc G)
     _+H_ = isGroup.comp (Group.groupStruc H)
     _+Im_ = isGroup.comp (Group.groupStruc (imGroup G H (ϕ , mf)))
     invG = isGroup.inv (Group.groupStruc G)
     invH = isGroup.inv (Group.groupStruc H)
     lUnit = isGroup.lUnit (Group.groupStruc H)
     lCancel = isGroup.rCancel (Group.groupStruc H)
 in
  Iso''→Iso _ _
    (iso'' ((λ x → x , pRec propTruncIsProp (λ (a , b) → ∣ a , b ∣₋₁) (surj x))
           , λ a b → pRec (Group.setStruc (imGroup G H (ϕ , mf)) _ _)
                          (λ surja → pRec (Group.setStruc (imGroup G H (ϕ , mf)) _ _)
                             (λ surjb →
                               pRec (Group.setStruc (imGroup G H (ϕ , mf)) _ _)
                                (λ surja+b →
                                (λ i → (a +H b) , (pRec (propTruncIsProp)
                                                         (λ (a , b) → ∣ a , b ∣₋₁)
                                                         (propTruncIsProp (surj (isGroup.comp (Group.groupStruc H) a b)) ∣ surja+b ∣₋₁ i))) ∙
                                 (λ i → (a +H b) , ∣ (fst surja+b) , (snd surja+b) ∣₋₁) ∙
                                 ΣProp≡ (λ _ → propTruncIsProp) refl  ∙
                                 λ i → (a +H b) ,  pRec (propTruncIsProp)
                                                           (λ p1 →
                                                              pRec (λ x y → squash x y)
                                                              (λ p2 →
                                                                 ∣
                                                                 isGroup.comp (Group.groupStruc G) (fst p1) (fst p2) ,
                                                                 mf (fst p1) (fst p2) ∙
                                                                 cong₂ (isGroup.comp (Group.groupStruc H)) (snd p1) (snd p2)
                                                                 ∣₋₁)
                                                              (pRec (propTruncIsProp)
                                                               ∣_∣₋₁ (propTruncIsProp ∣ surjb ∣₋₁ (surj b) i)))
                                                           (pRec (propTruncIsProp)
                                                            ∣_∣₋₁ (propTruncIsProp ∣ surja ∣₋₁ (surj a) i )))
                                (surj (isGroup.comp (Group.groupStruc H) a b)))
                             (surj b))
                          (surj a))
           (λ x inker → cong fst inker)
           λ x → pRec propTruncIsProp (λ inimx → ∣ (ϕ (inimx .fst)) , ΣProp≡ (λ _ → propTruncIsProp) (inimx .snd) ∣₋₁) (snd x))
{-
H¹-S¹≃Int : grIso intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
H¹-S¹≃Int =
  Iso''→Iso _ _
    (iso'' ((λ x → ∣ theFuns x ∣₀) , λ a b → cong ∣_∣₀ (funExt λ x → sym (Iso.leftInv (Iso3-Kn-ΩKn+1 1) _) ∙ sym (cong (ΩKn+1→Kn) (theFunsId2 a b x))))
           (λ x inker → pRec (isSetInt _ _) (inj x) (Iso.fun PathIdTrunc₀Iso inker))
           finIm)
  where
  d : _
  d = MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0

  i : _
  i = MV.i _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 1

  Δ : _
  Δ = MV.Δ _ _ (S₊ 1) (λ _ → tt) (λ _ → tt) 0


  d-surj : (x : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
         → isInIm (coHomGr 0 (S₊ 0)) (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0) x
  d-surj = sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
                  λ x → MV.Ker-i⊂Im-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ x ∣₀
                        (sym (isContrHelper .snd _))
      where
      isContrHelper : isContr (Group.type (×coHomGr 1 Unit Unit))
      isContrHelper = (∣ (λ _ → ∣ north ∣) ∣₀ , ∣ (λ _ → ∣ north ∣) ∣₀)
                     , λ y → prodId (cong ∣_∣₀ (λ i _ → ∣ merid north i ∣) ∙ isContrCohomUnit 0 .snd (proj₁ y))
                                     (cong ∣_∣₀ (λ i _ → ∣ merid north i ∣) ∙ isContrCohomUnit 0 .snd (proj₂ y))

  theFuns : (a : Int) → Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt) → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1
  theFuns a (inl x) = 0ₖ
  theFuns a (inr x) = 0ₖ
  theFuns a (push north i) = Kn→ΩKn+1 0 a i
  theFuns a (push south i) = 0ₖ


  theFunsId2 : (a b : Int) (x : Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))
             → Kn→ΩKn+1 1 (theFuns a x) ∙ Kn→ΩKn+1 1 (theFuns b x) ≡ Kn→ΩKn+1 1 (theFuns (a +ℤ b) x)
  theFunsId2 a b (inl x) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣) ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣))
  theFunsId2 a b (inr x) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣) ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣))
  theFunsId2 a b (push north i) j = 
    hcomp (λ k → λ {(i = i0) → ((λ i₁ →
             (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
          ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
         j
                   ; (i = i1) → ((λ i₁ →
             (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
          ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
         j
                   ; (j = i0) → cong₂Funct2 (λ p q → Kn→ΩKn+1 1 p ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 a) (Kn→ΩKn+1 0 b) (~ k) i 
                   ; (j = i1) → (helper2 a b) k i })
          (hcomp (λ k → λ { (j = i0) → compPath-filler (cong (λ x₁ → Kn→ΩKn+1 1 x₁ ∙ Kn→ΩKn+1 1 ∣ north ∣) (Kn→ΩKn+1 0 a)) (cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b)) k i
                           ; (j = i1) → compPath-filler (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a)) (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b)) k i
                           ; (i = i1) → RHS-filler b j k
                           ; (i = i0) → ((λ i₁ →
             (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
          ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
         j})
                 (bottom-filler a j i))

    where

    bottom-filler : (a : Int) →
                  PathP (λ j → (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣)
       (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣)
       ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))
      j ≡ (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣)
       (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣)
       ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))
      j) (cong (λ x₁ → Kn→ΩKn+1 1 x₁ ∙ Kn→ΩKn+1 1 ∣ north ∣) (Kn→ΩKn+1 0 a)) (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a))
    bottom-filler a j i =
      hcomp (λ k → λ {(j = i0) → helper2 (~ k) i ;
                       (j = i1) → cong (λ x → lUnit (Kn→ΩKn+1 1 x) (~ k)) (Kn→ΩKn+1 0 a) i})
            ((λ j₂ → ∣ rCancel (merid north) j j₂ ∣) ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))

       where
       helper2 : Path (Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 ∣ north ∣ ≡ Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 ∣ north ∣)
                      (λ i → Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i) ∙ Kn→ΩKn+1 1 ∣ north ∣)
                      (λ i → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))
       helper2 = cong₂Sym1 (Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) (~ i) j ∣) (λ i → Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))

    RHS-filler : (b : Int) →
               PathP (λ j → (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) i j ∣) ∙ (sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))) j
                           ≡ (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) i j ∣) ∙ (sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))) j)
                     (cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b))
                     (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b))
    RHS-filler b j i =
      hcomp (λ k → λ {(j = i0) → cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b) i ;
                       (j = i1) → cong (λ x → lUnit (Kn→ΩKn+1 1 x) (~ k)) (Kn→ΩKn+1 0 b) i})
            (cong (λ q → (λ i → ∣ rCancel (merid north) j i ∣) ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b) i)

    helper2 : (a b : Int) → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a) ∙ cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b) ≡ cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (a +ℤ b))
    helper2 a b =
        sym (congFunct (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a) (Kn→ΩKn+1 0 b))
      ∙ (λ i → cong (Kn→ΩKn+1 1) (Iso.rightInv (Iso3-Kn-ΩKn+1 0) (Kn→ΩKn+1 0 a ∙ Kn→ΩKn+1 0 b) (~ i)))
      ∙ (λ i → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (a +ₖ b)) )
      ∙ (λ i → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (addLemma a b i)))

  theFunsId2 a b (push south i) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
                                ∙ sym (lUnit _)

  inj : (a : Int) → theFuns a ≡ (λ _ → ∣ north ∣) → a ≡ pos 0
  inj a id =
    pRec (isSetInt _ _)
         (sigmaElim (λ _ → isOfHLevelPath 2 isSetInt _ _)
                    (λ a p → pRec (isSetInt _ _)
                    (λ id2 →  sym (Iso.leftInv (Iso3-Kn-ΩKn+1 0) _)
                             ∙ cong (ΩKn+1→Kn)
                                 (PathP→compPathR
                                   (cong (λ f → cong f (push north)) id)
                                     ∙ test))
                    (Iso.fun PathIdTrunc₀Iso p))) (d-surj ∣ theFuns a ∣₀)
    where

    test : (λ i → id i (inl tt)) ∙ (λ i → ∣ north ∣) ∙ sym (λ i → id i (inr tt)) ≡ refl
    test = (λ i → cong (λ f → f (inl tt)) id
         ∙ lUnit (sym (cong (λ f → f (inr tt)) id)) (~ i))
         ∙ (λ i → cong (λ f → f (push south i)) id
         ∙ sym (cong (λ f → f (inr tt)) id))
         ∙ rCancel (cong (λ f → f (inr tt)) id)


  consMember : (a : Int) → coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))
  consMember a = d ∣ (λ _ → a) ∣₀

  consMember≡0 : (a : Int) → consMember a ≡ 0ₕ
  consMember≡0 a =
           (MV.Im-Δ⊂Ker-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ (λ _ → a) ∣₀ ∣
                (∣ (λ _ → a) ∣₀ , ∣ (λ _ → 0) ∣₀)
                , cong ∣_∣₀ (λ i x → (rUnitₖ a i)) ∣₋₁)

  f+consMember' : (f : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) → ∃[ x ∈ Int × Int ] (f +ₕ (-ₕ (consMember (proj₁ x))) ≡ ∣ theFuns (proj₂ x) ∣₀)
  f+consMember' =
    sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
          λ f → pRec propTruncIsProp
                      (sigmaElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
                                 (λ g id → ∣ ((g south) , ((g north) +ₖ (-ₖ g south)))
                                           , (pRec (setTruncIsSet _ _)
                                                    (λ id → (λ i → ∣ id (~ i) ∣₀ +ₕ -ₕ ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (λ _ → g south) ∣₀) ∙ funId1 g)
                                                    (Iso.fun PathIdTrunc₀Iso id)) ∣₋₁))
                      (d-surj ∣ f ∣₀)
    where
    funId1 : (g : S₊ 0 → Int)
           → ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g ∣₀ +ₕ -ₕ ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (λ _ → g south) ∣₀ ≡
             ∣ theFuns ((g north) +ₖ (-ₖ (g south))) ∣₀
    funId1 g = (λ i → ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g ∣₀
                    +ₕ (morphMinus (coHomGr 0 (S₊ 0)) (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) d
                                   (MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) ∣ (λ _ → g south) ∣₀ (~ i)))
             ∙ sym (MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ g ∣₀ (-ₕ ∣ (λ _ → g south) ∣₀))
             ∙ (cong (λ x → d ∣ x ∣₀) g'Id)
             ∙ cong ∣_∣₀ helper
      where
      g' : S₊ 0 → Int
      g' north = (g north) +ₖ (-ₖ (g south))
      g' south = 0

      g'Id : (λ x → g x +ₖ (-ₖ (g south))) ≡ g'
      g'Id = funExt (λ {north → refl
                      ; south → rCancelₖ (g south)})

      helper : MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g' ≡ theFuns (g north +ₖ (-ₖ g south))
      helper = funExt λ {(inl tt) → refl
                       ; (inr tt) → refl
                       ; (push north i) → refl
                       ; (push south i) → refl}
  finIm : (f : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) → ∃[ x ∈ Int ] (∣ theFuns x ∣₀ ≡ f)
  finIm f =
    pRec propTruncIsProp
          (λ {((a , b) , id) → ∣ b , (sym id ∙ cong (λ x → f +ₕ x) ((λ i → (-ₕ (consMember≡0 a i))) ∙ sym (lUnitₕ (-ₕ 0ₕ)) ∙ rCancelₕ 0ₕ) ∙ (rUnitₕ f)) ∣₋₁})
         (f+consMember' f)
-}
Hⁿ-Sⁿ≃Int : (n : ℕ) → grIso intGroup (coHomGr (suc n) (S₊ (suc n)))
Hⁿ-Sⁿ≃Int zero =
  compGrIso {F = intGroup} {G = {!!}} {H = {!coHomGr 1 (S₊ 1)!}}
    (Iso''→Iso _ _
      (iso'' ((λ x → ∣ theFuns x ∣₀) , λ a b → cong ∣_∣₀ (funExt λ x → sym (Iso.leftInv (Iso3-Kn-ΩKn+1 1) _) ∙ sym (cong (ΩKn+1→Kn) (theFunsId2 a b x))))
             (λ x inker → pRec (isSetInt _ _) (inj x) (Iso.fun PathIdTrunc₀Iso inker))
             finIm))
    {!invGrIso _ _ (coHomPushout≡coHomSn 0 1)!}
  where
  d : _
  d = MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0

  i : _
  i = MV.i _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 1

  Δ : _
  Δ = MV.Δ _ _ (S₊ 1) (λ _ → tt) (λ _ → tt) 0


  d-surj : (x : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
         → isInIm (coHomGr 0 (S₊ 0)) (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0) x
  d-surj = sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
                  λ x → MV.Ker-i⊂Im-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ x ∣₀
                        (sym (isContrHelper .snd _))
      where
      isContrHelper : isContr (Group.type (×coHomGr 1 Unit Unit))
      isContrHelper = (∣ (λ _ → ∣ north ∣) ∣₀ , ∣ (λ _ → ∣ north ∣) ∣₀)
                     , λ y → prodId (cong ∣_∣₀ (λ i _ → ∣ merid north i ∣) ∙ isContrCohomUnit 0 .snd (proj₁ y))
                                     (cong ∣_∣₀ (λ i _ → ∣ merid north i ∣) ∙ isContrCohomUnit 0 .snd (proj₂ y))

  theFuns : (a : Int) → Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt) → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1
  theFuns a (inl x) = 0ₖ
  theFuns a (inr x) = 0ₖ
  theFuns a (push north i) = Kn→ΩKn+1 0 a i
  theFuns a (push south i) = 0ₖ


  theFunsId2 : (a b : Int) (x : Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))
             → Kn→ΩKn+1 1 (theFuns a x) ∙ Kn→ΩKn+1 1 (theFuns b x) ≡ Kn→ΩKn+1 1 (theFuns (a +ℤ b) x)
  theFunsId2 a b (inl x) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣) ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣))
  theFunsId2 a b (inr x) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣) ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣))
  theFunsId2 a b (push north i) j = 
    hcomp (λ k → λ {(i = i0) → ((λ i₁ →
             (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
          ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
         j
                   ; (i = i1) → ((λ i₁ →
             (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
          ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
         j
                   ; (j = i0) → cong₂Funct2 (λ p q → Kn→ΩKn+1 1 p ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 a) (Kn→ΩKn+1 0 b) (~ k) i 
                   ; (j = i1) → (helper2 a b) k i })
          (hcomp (λ k → λ { (j = i0) → compPath-filler (cong (λ x₁ → Kn→ΩKn+1 1 x₁ ∙ Kn→ΩKn+1 1 ∣ north ∣) (Kn→ΩKn+1 0 a)) (cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b)) k i
                           ; (j = i1) → compPath-filler (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a)) (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b)) k i
                           ; (i = i1) → RHS-filler b j k
                           ; (i = i0) → ((λ i₁ →
             (λ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
          ∙ (λ i₁ → lUnit (Kn→ΩKn+1 1 ∣ north ∣) (~ i₁)))
         j})
                 (bottom-filler a j i))

    where

    bottom-filler : (a : Int) →
                  PathP (λ j → (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣)
       (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣)
       ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))
      j ≡ (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣)
       (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣)
       ∙ sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))
      j) (cong (λ x₁ → Kn→ΩKn+1 1 x₁ ∙ Kn→ΩKn+1 1 ∣ north ∣) (Kn→ΩKn+1 0 a)) (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a))
    bottom-filler a j i =
      hcomp (λ k → λ {(j = i0) → helper2 (~ k) i ;
                       (j = i1) → cong (λ x → lUnit (Kn→ΩKn+1 1 x) (~ k)) (Kn→ΩKn+1 0 a) i})
            ((λ j₂ → ∣ rCancel (merid north) j j₂ ∣) ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))

       where
       helper2 : Path (Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 ∣ north ∣ ≡ Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 ∣ north ∣)
                      (λ i → Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i) ∙ Kn→ΩKn+1 1 ∣ north ∣)
                      (λ i → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))
       helper2 = cong₂Sym1 (Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) (~ i) j ∣) (λ i → Kn→ΩKn+1 1 (Kn→ΩKn+1 0 a i))

    RHS-filler : (b : Int) →
               PathP (λ j → (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) i j ∣) ∙ (sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))) j
                           ≡ (cong (λ x → x ∙ Kn→ΩKn+1 1 ∣ north ∣) (λ i j → ∣ rCancel (merid north) i j ∣) ∙ (sym (lUnit (Kn→ΩKn+1 1 ∣ north ∣)))) j)
                     (cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b))
                     (cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b))
    RHS-filler b j i =
      hcomp (λ k → λ {(j = i0) → cong (λ q → Kn→ΩKn+1 1 ∣ north ∣ ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b) i ;
                       (j = i1) → cong (λ x → lUnit (Kn→ΩKn+1 1 x) (~ k)) (Kn→ΩKn+1 0 b) i})
            (cong (λ q → (λ i → ∣ rCancel (merid north) j i ∣) ∙ Kn→ΩKn+1 1 q) (Kn→ΩKn+1 0 b) i)

    helper2 : (a b : Int) → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a) ∙ cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 b) ≡ cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (a +ℤ b))
    helper2 a b =
        sym (congFunct (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 a) (Kn→ΩKn+1 0 b))
      ∙ (λ i → cong (Kn→ΩKn+1 1) (Iso.rightInv (Iso3-Kn-ΩKn+1 0) (Kn→ΩKn+1 0 a ∙ Kn→ΩKn+1 0 b) (~ i)))
      ∙ (λ i → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (a +ₖ b)) )
      ∙ (λ i → cong (Kn→ΩKn+1 1) (Kn→ΩKn+1 0 (addLemma a b i)))

  theFunsId2 a b (push south i) = (λ i → (λ j → ∣ rCancel (merid north) i j ∣) ∙ Kn→ΩKn+1 1 ∣ north ∣)
                                ∙ sym (lUnit _)

  inj : (a : Int) → theFuns a ≡ (λ _ → ∣ north ∣) → a ≡ pos 0
  inj a id =
    pRec (isSetInt _ _)
         (sigmaElim (λ _ → isOfHLevelPath 2 isSetInt _ _)
                    (λ a p → pRec (isSetInt _ _)
                    (λ id2 →  sym (Iso.leftInv (Iso3-Kn-ΩKn+1 0) _)
                             ∙ cong (ΩKn+1→Kn)
                                 (PathP→compPathR
                                   (cong (λ f → cong f (push north)) id)
                                     ∙ test))
                    (Iso.fun PathIdTrunc₀Iso p))) (d-surj ∣ theFuns a ∣₀)
    where

    test : (λ i → id i (inl tt)) ∙ (λ i → ∣ north ∣) ∙ sym (λ i → id i (inr tt)) ≡ refl
    test = (λ i → cong (λ f → f (inl tt)) id
         ∙ lUnit (sym (cong (λ f → f (inr tt)) id)) (~ i))
         ∙ (λ i → cong (λ f → f (push south i)) id
         ∙ sym (cong (λ f → f (inr tt)) id))
         ∙ rCancel (cong (λ f → f (inr tt)) id)


  consMember : (a : Int) → coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))
  consMember a = d ∣ (λ _ → a) ∣₀

  consMember≡0 : (a : Int) → consMember a ≡ 0ₕ
  consMember≡0 a =
           (MV.Im-Δ⊂Ker-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ (λ _ → a) ∣₀ ∣
                (∣ (λ _ → a) ∣₀ , ∣ (λ _ → 0) ∣₀)
                , cong ∣_∣₀ (λ i x → (rUnitₖ a i)) ∣₋₁)

  f+consMember' : (f : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) → ∃[ x ∈ Int × Int ] (f +ₕ (-ₕ (consMember (proj₁ x))) ≡ ∣ theFuns (proj₂ x) ∣₀)
  f+consMember' =
    sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
          λ f → pRec propTruncIsProp
                      (sigmaElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
                                 (λ g id → ∣ ((g south) , ((g north) +ₖ (-ₖ g south)))
                                           , (pRec (setTruncIsSet _ _)
                                                    (λ id → (λ i → ∣ id (~ i) ∣₀ +ₕ -ₕ ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (λ _ → g south) ∣₀) ∙ funId1 g)
                                                    (Iso.fun PathIdTrunc₀Iso id)) ∣₋₁))
                      (d-surj ∣ f ∣₀)
    where
    funId1 : (g : S₊ 0 → Int)
           → ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g ∣₀ +ₕ -ₕ ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 (λ _ → g south) ∣₀ ≡
             ∣ theFuns ((g north) +ₖ (-ₖ (g south))) ∣₀
    funId1 g = (λ i → ∣ MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g ∣₀
                    +ₕ (morphMinus (coHomGr 0 (S₊ 0)) (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) d
                                   (MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) ∣ (λ _ → g south) ∣₀ (~ i)))
             ∙ sym (MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ g ∣₀ (-ₕ ∣ (λ _ → g south) ∣₀))
             ∙ (cong (λ x → d ∣ x ∣₀) g'Id)
             ∙ cong ∣_∣₀ helper
      where
      g' : S₊ 0 → Int
      g' north = (g north) +ₖ (-ₖ (g south))
      g' south = 0

      g'Id : (λ x → g x +ₖ (-ₖ (g south))) ≡ g'
      g'Id = funExt (λ {north → refl
                      ; south → rCancelₖ (g south)})

      helper : MV.d-pre Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 g' ≡ theFuns (g north +ₖ (-ₖ g south))
      helper = funExt λ {(inl tt) → refl
                       ; (inr tt) → refl
                       ; (push north i) → refl
                       ; (push south i) → refl}
  finIm : (f : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))) → ∃[ x ∈ Int ] (∣ theFuns x ∣₀ ≡ f)
  finIm f =
    pRec propTruncIsProp
          (λ {((a , b) , id) → ∣ b , (sym id ∙ cong (λ x → f +ₕ x) ((λ i → (-ₕ (consMember≡0 a i))) ∙ sym (lUnitₕ (-ₕ 0ₕ)) ∙ rCancelₕ 0ₕ) ∙ (rUnitₕ f)) ∣₋₁})
         (f+consMember' f)
Hⁿ-Sⁿ≃Int (suc n) =
  compGrIso (Hⁿ-Sⁿ≃Int n)
            (transport (λ i → grIso {!!} {!coHomGr (suc (suc n)) (Pushout (λ _ → tt) (λ _ → tt))!}) {!!})


{-
coHom1S1≃ℤ : grIso intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
grIso.fun coHom1S1≃ℤ = grIso.fun {!compGrIso coHom1Iso (invGrIso _ _ (ImIso _ _ (d-morph _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0) ?))!}
grIso.inv coHom1S1≃ℤ = {!!}
grIso.rightInv coHom1S1≃ℤ = {!!}
grIso.leftInv coHom1S1≃ℤ = {!!}
-}

-- compGrIso coHom1Iso (invGrIso _ _ (ImIso _ _ {!d-morph _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0!} {!!}))


-- coHomGrIm : grIso (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
--                   (imGroup (coHomGr 0 (S₊ 0))
--                            (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
--                            (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0
--                            , MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0))
-- coHomGrIm =
--   ImIso _
--         _
--         _
--         {!!}


-- -- coHom1RedS1 : Iso (coHom 1 (S₊ 1)) (coHomRed 1 (S₊ 1 , north))
-- -- Iso.fun coHom1RedS1 = sRec setTruncIsSet λ f → ∣ f , (pRec {!!} {!!} ((transport (λ i → (b : truncIdempotent 3 {!S₊ 1!} (~ i)) → ∥ (transp (λ j → truncIdempotent {!3!} {!!} (~ i ∨ (~ j))) (~ i) north) ≡ b ∥₋₁) isConnectedS1) (f north)) ) ∣₀
-- -- Iso.inv coHom1RedS1 = {!!}
-- -- Iso.rightInv coHom1RedS1 = {!setTruncIdempotent!}
-- -- Iso.leftInv coHom1RedS1 = {!!}

-- -- coHom1Red : ∀ {ℓ} (A : Pointed ℓ) → Iso (coHom 1 (typ A)) (coHomRed 1 A)
-- -- Iso.fun (coHom1Red A) = sRec setTruncIsSet λ f → ∣ f , {!!} ∣₀
-- -- Iso.inv (coHom1Red A) = {!!}
-- -- Iso.rightInv (coHom1Red A) = {!!}
-- -- Iso.leftInv (coHom1Red A) = {!!}

-- -- -- morphtest : morph (coHomGr 1 (S₊ 1)) intGroup
-- -- -- fst morphtest = sRec isSetInt λ f → winding (basechange _  λ i → SuspBool→S¹ (S1→SuspBool (trRec2 isGroupoidS1 (λ x → x) (f (loop* i)))))
-- -- -- snd morphtest = sElim2 {!!}
-- -- --                        (funRec 3 isGroupoidS1
-- -- --                          λ f → funRec 3 isGroupoidS1
-- -- --                            λ g → pRec (isSetInt _ _)
-- -- --                                    (λ n=fn →
-- -- --                                      pRec (isSetInt _ _)
-- -- --                                           (λ n=gn → (λ j → winding (basechange  (SuspBool→S¹ (S1→SuspBool (trRec2 isGroupoidS1 (λ x → x) (∣ f (north) ∣ +ₖ ∣ n=gn (~ j) ∣))))  (λ i → SuspBool→S¹ (S1→SuspBool (trRec2 isGroupoidS1 (λ x → x) (∣ f (loop* i) ∣ +ₖ ∣ transp (λ i → n=gn ((~ i) ∨ (~ j)) ≡ n=gn ((~ i) ∨ (~ j))) (~ j) (λ i → g (loop* i)) i ∣)))))) 
-- -- --                                                    ∙ {!!}
-- -- --                                                    ∙ {!!})
-- -- --                                           (isConnectedS1 (g north)))
-- -- --                                    (isConnectedS1 (f north)))


-- -- -- {- (λ i → winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (∣ f (loop* i) ∣ +ₖ ∣ g (loop* i) ∣)))))
-- -- --                                 ∙ (λ i → winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn (Kn→ΩKn+1 1 ∣ f (loop* i) ∣ ∙ Kn→ΩKn+1 1 ∣ g (loop* i) ∣))))))
-- -- --                                 ∙ (λ j → winding (basechange _ (cong (λ x → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn (Kn→ΩKn+1 1 ∣ f x ∣ ∙ Kn→ΩKn+1 1 ∣ g x ∣))))) loop*)) )
-- -- --                                 ∙ (λ i → winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn ((cong ∣_∣ (merid (f (loop* i)) ∙ sym (merid north)) ∙ cong ∣_∣ (merid (g (loop* i)) ∙ sym (merid north)))))))))
-- -- --                                 ∙ (λ j → winding (basechange _  λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn (congFunct ∣_∣ (merid (f (loop* i)) ∙ sym (merid north)) (merid (g (loop* i)) ∙ sym (merid north)) (~ j)))))))
-- -- --                                 ∙ (λ j → winding (basechange _ λ i → SuspBool→S¹ (S1→SuspBool (trRec isGroupoidS1 (λ x → x) (ΩKn+1→Kn (cong ∣_∣ (({!!} ∙ {!!}) ∙ {!!})))))))
-- -- --                                 ∙ {!!}
-- -- --                                 ∙ {!!}
-- -- --                                 ∙ {!!}) -}

-- -- --   where
-- -- --   helper : ∀ {ℓ} {A : Type ℓ} (a : A) (f : A → S¹) (p q : a ≡ a) → winding (basechange (f a) (cong f (p ∙ q))) ≡ winding (basechange (f a) (cong f p ∙ cong f q))
-- -- --   helper a f p q i = winding (basechange (f a) (congFunct f p q i))
-- -- --   helper2 : (x : S¹) (p q : x ≡ x) → basechange x (p ∙ q) ≡ basechange x p ∙ basechange x q
-- -- --   helper2 base p q = refl
-- -- --   helper2 (loop i) p q = {!!}
-- -- --   helper4 : (x y z : S¹) (p : x ≡ z) (q r : x ≡ y) (s : y ≡ z) → basechange* x z p (q ∙ s)  ≡ basechange* x y {!!} q ∙ {!!} 
-- -- --   helper4 = {!!}
-- -- --   helper3 : (p q : ΩS¹) → winding (p ∙ q) ≡ (winding p +ℤ winding q)
-- -- --   helper3 = {!!}


-- -- -- -- fstmap : morph (dirProd intGroup intGroup) (coHomGr 0 (S₊ 0))
-- -- -- -- fstmap = compMorph {F = dirProd intGroup intGroup} {G = ×coHomGr 0 Unit Unit} {H = coHomGr 0 (S₊ 0)}
-- -- -- --                    (×morph (grIso.inv coHomGrUnit0) (grIso.inv coHomGrUnit0))
-- -- -- --                    (((MV.Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) zero)) ,
-- -- -- --                      {!MV.ΔIsHom _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) zero!})

-- -- -- -- fstMapId : (a : Int × Int) → fstmap .fst a ≡ ∣ (λ _ → proj₁ a +ℤ (0 - proj₂ a)) ∣₀
-- -- -- -- fstMapId (a , b) = (λ i → ∣ (λ _ → a +ₖ (-ₖ b)) ∣₀) ∙ {!addLemma!} ∙ {!!} ∙ {!!}

-- -- -- -- isoAgain : grIso intGroup (coHomGr 1 (S₊ 1))
-- -- -- -- isoAgain =
-- -- -- --   Iso''→Iso _ _
-- -- -- --              (iso'' ((λ a → ∣ (λ {north → 0ₖ ; south → 0ₖ ; (merid north i) → {!a!} ; (merid south i) → {!!}}) ∣₀) , {!!})
-- -- -- --                     {!!}
-- -- -- --                     {!!})

-- -- -- -- -- -- test2 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → S¹) 
-- -- -- -- -- -- Iso.fun test2 f = {!!}
-- -- -- -- -- -- Iso.inv test2 f north = ∣ transport (sym S¹≡S1) (f base) ∣
-- -- -- -- -- -- Iso.inv test2 f south = ∣ transport (sym S¹≡S1) (f base) ∣
-- -- -- -- -- -- Iso.inv test2 f (merid a i) = cong ∣_∣ {!transport (sym S¹≡S1) (f base)!} i
-- -- -- -- -- -- Iso.rightInv test2 = {!!}
-- -- -- -- -- -- Iso.leftInv test2 = {!!}

-- -- -- -- -- -- F : winding (basechange base loop) ≡ 1
-- -- -- -- -- -- F = refl

-- -- -- -- -- -- another : (f g : Int) → winding (basechange {!!} {!!}) ≡ {!!}
-- -- -- -- -- -- another = {!!}

-- -- -- -- -- -- test : Iso (S¹ → S¹) (S¹ × Int)
-- -- -- -- -- -- Iso.fun test f = f base , winding (basechange (f base) (cong f loop))
-- -- -- -- -- -- Iso.inv test (x , int) base = x
-- -- -- -- -- -- Iso.inv test (x , int) (loop i) = {!!}
-- -- -- -- -- -- Iso.rightInv test = {!!}
-- -- -- -- -- -- Iso.leftInv test = {!!}

-- -- -- -- -- -- -- test13 : Iso ∥ (S¹ → S¹) ∥₀ Int
-- -- -- -- -- -- -- Iso.fun test13 = sRec isSetInt λ f → winding (basechange (f base) (λ i → f (loop i)))
-- -- -- -- -- -- -- Iso.inv test13 a = ∣ (λ {base → {!!} ; (loop i) → {!!}}) ∣₀
-- -- -- -- -- -- -- Iso.rightInv test13 = {!!}
-- -- -- -- -- -- -- Iso.leftInv test13 = {!!}

-- -- -- -- -- -- -- test : Iso (S¹ → S¹) (S¹ × Int)
-- -- -- -- -- -- -- Iso.fun test f = (f base) , transport (basedΩS¹≡Int (f base)) λ i → f (loop i)
-- -- -- -- -- -- -- Iso.inv test (x , int) base = x
-- -- -- -- -- -- -- Iso.inv test (x , int) (loop i) = transport (sym (basedΩS¹≡Int x)) int i
-- -- -- -- -- -- -- Iso.rightInv test (x , int) i = (x , transportTransport⁻ (basedΩS¹≡Int x) int i)
-- -- -- -- -- -- -- Iso.leftInv test f =
-- -- -- -- -- -- --   funExt λ { base → refl
-- -- -- -- -- -- --           ; (loop i) j → transport⁻Transport (basedΩS¹≡Int (f base)) (λ i → f (loop i)) j i}


-- -- -- -- -- -- -- lem : S¹ ≡ hLevelTrunc 3 (S₊ 1) 
-- -- -- -- -- -- -- lem = sym (truncIdempotent 3 isGroupoidS¹) ∙ λ i → hLevelTrunc 3 (S¹≡S1 (~ i))

-- -- -- -- -- -- -- prodId : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a b : A × B) → proj₁ a ≡ proj₁ b → proj₂ a ≡ proj₂ b → a ≡ b
-- -- -- -- -- -- -- prodId (_ , _) (_ , _) id1 id2 i = (id1 i) , (id2 i)

-- -- -- -- -- -- -- test22 : Iso (S₊ 1 → coHomK 1) (S₊ 1 × Int)
-- -- -- -- -- -- -- Iso.fun test22 f = {!f north!} , {!!}
-- -- -- -- -- -- -- Iso.inv test22 = {!!}
-- -- -- -- -- -- -- Iso.rightInv test22 = {!!}
-- -- -- -- -- -- -- Iso.leftInv test22 = {!!}






-- -- -- -- -- -- -- coHom1≃∥S1×ℤ∥₀ : Iso (coHom 1 (S₊ 1)) ∥ S₊ 1 × Int ∥₀
-- -- -- -- -- -- -- coHom1≃∥S1×ℤ∥₀ = setTruncIso test2
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   test2 : Iso (S₊ 1 → coHomK 1) (S₊ 1 × Int)
-- -- -- -- -- -- --   Iso.fun test2 f = transport (λ i → S¹≡S1 (~ i) × Int) (Iso.fun test (transport (λ i → (S¹≡S1 i → lem (~ i))) f))
-- -- -- -- -- -- --   Iso.inv test2 x = transport (λ i → (S¹≡S1 (~ i) → lem i)) (Iso.inv test (transport (λ i → S¹≡S1 i × Int) x))
-- -- -- -- -- -- --   Iso.rightInv test2 (s , int) = prodId _ _ {!!} {!!}
-- -- -- -- -- -- --   Iso.leftInv test2 f = {!!} ∙ {!!} ∙ {!!}

-- -- -- -- -- -- --   test2Id : (a b : (S₊ 1 → coHomK 1)) → proj₂ (Iso.fun test2 (λ x →  a x +ₖ b x)) ≡ (proj₂ (Iso.fun test2 a) +ₖ proj₂ (Iso.fun test2 a))
-- -- -- -- -- -- --   test2Id a b = {!
-- -- -- -- -- -- --     transport
-- -- -- -- -- -- --       (basedΩS¹≡Int
-- -- -- -- -- -- --        (transport (λ i → S¹≡S1 i → lem (~ i)) (λ x → a x +ₖ b x) base))
-- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- --          transport (λ i₁ → S¹≡S1 i₁ → lem (~ i₁)) (λ x → a x +ₖ b x)
-- -- -- -- -- -- --          (loop i))!} ∙ {!transport (λ i → S¹≡S1 i → lem (~ i)) (λ x → a x +ₖ b x) base!}


-- -- -- -- -- -- -- main : grIso intGroup (coHomGr 1 (S₊ 1))
-- -- -- -- -- -- -- main = Iso'→Iso
-- -- -- -- -- -- --        (iso' {!!}
-- -- -- -- -- -- --              {!!})


-- -- -- -- -- coHom1 : grIso (coHomGr 1 (S₊ 1)) intGroup
-- -- -- -- -- coHom1 =
-- -- -- -- --   Iso'→Iso
-- -- -- -- --     (iso' (iso ({!!} ∘ {!!} ∘ {!!} ∘ {!!})
-- -- -- -- --                {!!}
-- -- -- -- --                {!!}
-- -- -- -- --                {!!})
-- -- -- -- --           {!!})



-- -- -- -- -- schonf : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : (A × B) → Type ℓ''}
-- -- -- -- --          → ((a : A) (b : B) → C (a , b))
-- -- -- -- --          → (x : A × B) → C x
-- -- -- -- -- schonf f (a , b) = f a b

-- -- -- -- -- -- -- setTruncProdIso : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Iso ∥ (A × B) ∥₀ (∥ A ∥₀ × ∥ B ∥₀)
-- -- -- -- -- -- -- Iso.fun (setTruncProdIso A B) = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) λ {(a , b) → ∣ a ∣₀ , ∣ b ∣₀}
-- -- -- -- -- -- -- Iso.inv (setTruncProdIso A B) (a , b) = sRec setTruncIsSet (λ a → sRec setTruncIsSet (λ b → ∣ a , b ∣₀) b) a
-- -- -- -- -- -- -- Iso.rightInv (setTruncProdIso A B) =
-- -- -- -- -- -- --   schonf (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
-- -- -- -- -- -- --                  λ _ → sElim (λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
-- -- -- -- -- -- --                                λ _ → refl)
-- -- -- -- -- -- -- Iso.leftInv (setTruncProdIso A B) = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ {(a , b) → refl}

-- -- -- -- -- -- -- setTruncProdLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a1 a2 : A) (b : B) → isHLevelConnected 2 A
-- -- -- -- -- -- --                  → Path ∥ A × B ∥₀ ∣ a1 , b ∣₀ ∣ a2 , b ∣₀ 
-- -- -- -- -- -- -- setTruncProdLemma {A = A} {B = B} a1 a2 b conA i = Iso.inv (setTruncProdIso A B) (Iso.inv setTruncTrunc0Iso ((sym (conA .snd ∣ a1 ∣) ∙ (conA .snd ∣ a2 ∣)) i) , ∣ b ∣₀)

-- -- -- -- -- -- -- test3 : Iso ∥ S₊ 1 × Int ∥₀ Int 
-- -- -- -- -- -- -- Iso.fun test3 = sRec isSetInt proj₂
-- -- -- -- -- -- -- Iso.inv test3 a = ∣ north , a ∣₀
-- -- -- -- -- -- -- Iso.rightInv test3 a = refl
-- -- -- -- -- -- -- Iso.leftInv test3 =
-- -- -- -- -- -- --   sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- -- -- -- -- -- --         λ {(s , int) → setTruncProdLemma north s int (sphereConnected 1)}

-- -- -- -- -- -- -- coHomGr0-S1 : grIso intGroup (coHomGr 1 (S₊ 1))
-- -- -- -- -- -- -- coHomGr0-S1 =
-- -- -- -- -- -- --   Iso'→Iso
-- -- -- -- -- -- --     (iso' (compIso (symIso test3) (symIso coHom1≃∥S1×ℤ∥₀))
-- -- -- -- -- -- --           (indIntGroup {G = coHomGr 1 (S₊ 1)}
-- -- -- -- -- -- --                        (Iso.fun (compIso (symIso test3) (symIso coHom1≃∥S1×ℤ∥₀)))
-- -- -- -- -- -- --                        ((λ i → ∣ transport (λ i → (S¹≡S1 (~ i) → lem i)) (Iso.inv test (base , 0)) ∣₀)
-- -- -- -- -- -- --                          ∙ (λ i → ∣ transport (λ i → (S¹≡S1 (~ i) → lem i)) (helper2 i) ∣₀)
-- -- -- -- -- -- --                          ∙ cong ∣_∣₀ (funExt λ {north → refl ; south → refl ; (merid a i) → {!!}}))
-- -- -- -- -- -- --                        {!!}
-- -- -- -- -- -- --                        {!!}))
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     helper : basedΩS¹≡ΩS¹ base ≡ {!basechange!}
-- -- -- -- -- -- --     helper = {!substComposite!}

-- -- -- -- -- -- --     substComposite2 : ∀ {ℓ} {A B C : Type ℓ}
-- -- -- -- -- -- --                       (P : A ≡ B) (Q : B ≡ C) (a : A)
-- -- -- -- -- -- --                    → transport (P ∙ Q) a ≡ transport Q (transport P a) 
-- -- -- -- -- -- --     substComposite2 = {!!}

-- -- -- -- -- -- --     helper1 : transport (λ i → S¹≡S1 i × Int) (north , 0) ≡ (base , 0)
-- -- -- -- -- -- --     helper1 = refl
-- -- -- -- -- -- --     helper3 : transport (sym (basedΩS¹≡Int base)) 0 ≡ refl
-- -- -- -- -- -- --     helper3 = (λ i → transport (symDistr (basedΩS¹≡ΩS¹ base) ΩS¹≡Int i) 0)
-- -- -- -- -- -- --             ∙ substComposite2 (sym ΩS¹≡Int) (sym (basedΩS¹≡ΩS¹ base)) 0
-- -- -- -- -- -- --             ∙ (λ i → transport (λ i → basedΩS¹≡ΩS¹ base (~ i)) refl) -- 
-- -- -- -- -- -- --             ∙ transportRefl ((equiv-proof (basechange-isequiv base) refl) .fst .fst)
-- -- -- -- -- -- --             ∙ (λ i → equiv-proof (transport (λ j → isEquiv (refl-conjugation j)) (basedΩS¹→ΩS¹-isequiv i0)) refl .fst .fst)
-- -- -- -- -- -- --             ∙ (λ i → {!equiv-proof (transport (λ j → isEquiv (refl-conjugation j)) (basedΩS¹→ΩS¹-isequiv i0)) refl .fst!})
-- -- -- -- -- -- --             ∙ {!basedΩS¹→ΩS¹!}
-- -- -- -- -- -- --             ∙ {!!}
-- -- -- -- -- -- --             ∙ {!!}
-- -- -- -- -- -- --     helper4 : (x : S¹) → Iso.inv test (base , 0) x ≡ x
-- -- -- -- -- -- --     helper4 = {!!}
-- -- -- -- -- -- --     helper2 : Iso.inv test (transport (λ i → S¹≡S1 i × Int) (north , 0)) ≡ λ x → x
-- -- -- -- -- -- --     helper2 = (λ i → Iso.inv test (base , 0)) ∙ {!!} ∙ {!!}

-- -- -- -- -- prodId : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A × B} → proj₁ x ≡ proj₁ y → proj₂ x ≡ proj₂ y → x ≡ y
-- -- -- -- -- prodId {x = (a , b)} {y = (c , d)} id1 id2 i = (id1 i) , (id2 i)

-- -- -- -- -- fstFunHelper : (x : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- -- --              → isInIm (coHomGr 0 (S₊ 0)) (coHomGr 1 _) (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) x
-- -- -- -- -- fstFunHelper a = MV.Ker-i⊂Im-d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 a
-- -- -- -- --                  (sym (isContrH1Unit×H1Unit .snd _) ∙ (isContrH1Unit×H1Unit .snd _))
-- -- -- -- --    where
-- -- -- -- --    isContrH1Unit×H1Unit : isContr (Group.type (×coHomGr 1 Unit Unit))
-- -- -- -- --    isContrH1Unit×H1Unit = (∣ (λ _ → ∣ north ∣) ∣₀ , ∣ (λ _ → ∣ north ∣) ∣₀)
-- -- -- -- --                         ,  λ {(a , b) → sigmaProdElim {D = λ (x : Σ[ x ∈ Group.type (×coHomGr 1 Unit Unit)] Unit) → (∣ (λ _ → ∣ north ∣) ∣₀ , ∣ (λ _ → ∣ north ∣) ∣₀) ≡ fst x}
-- -- -- -- --                                                        (λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
-- -- -- -- --                                                        (λ a b _ → prodId (grIso.leftInv (coHomGrUnit≥1 0) ∣ a ∣₀) (grIso.leftInv (coHomGrUnit≥1 0) ∣ b ∣₀)) ((a , b) , tt)}



-- -- -- -- -- helperMorph : isMorph intGroup (dirProd intGroup intGroup) λ a → a , (0 - a)
-- -- -- -- -- helperMorph =
-- -- -- -- --   indIntGroup {G = dirProd intGroup intGroup}
-- -- -- -- --                (λ a → a , (0 - a))
-- -- -- -- --                refl
-- -- -- -- --                (λ a → prodId refl (helper2 a))
-- -- -- -- --                λ a → prodId refl (helper3 a)
-- -- -- -- --   where
-- -- -- -- --   helper1 : (a : Int) → predInt (sucInt a) ≡ a
-- -- -- -- --   helper1 (pos zero) = refl
-- -- -- -- --   helper1 (pos (suc n)) = refl
-- -- -- -- --   helper1 (negsuc zero) = refl
-- -- -- -- --   helper1 (negsuc (suc n)) = refl

-- -- -- -- --   helper4 : (a : Int) → sucInt (predInt a) ≡ a
-- -- -- -- --   helper4 (pos zero) = refl
-- -- -- -- --   helper4 (pos (suc n)) = refl
-- -- -- -- --   helper4 (negsuc zero) = refl
-- -- -- -- --   helper4 (negsuc (suc n)) = refl

-- -- -- -- --   helper2 : (a : Int) → (pos 0 - sucInt a) ≡ predInt (pos 0 - a)
-- -- -- -- --   helper2 (pos zero) = refl
-- -- -- -- --   helper2 (pos (suc n)) = refl
-- -- -- -- --   helper2 (negsuc zero) = refl
-- -- -- -- --   helper2 (negsuc (suc n)) = sym (helper1 _)

-- -- -- -- --   helper3 : (a : Int) → (pos 0 - predInt a) ≡ sucInt (pos 0 - a)
-- -- -- -- --   helper3 (pos zero) = refl
-- -- -- -- --   helper3 (pos (suc zero)) = refl
-- -- -- -- --   helper3 (pos (suc (suc n))) = sym (helper4 _)
-- -- -- -- --   helper3 (negsuc zero) = refl
-- -- -- -- --   helper3 (negsuc (suc n)) = refl

-- -- -- -- --   helper : (a b : Int) → (pos 0 - (a +ℤ b)) ≡ ((pos 0 - a) +ℤ (pos 0 - b))
-- -- -- -- --   helper a (pos zero) = refl
-- -- -- -- --   helper (pos zero) (pos (suc n)) =
-- -- -- -- --       cong (λ x → pos 0 - sucInt x) (+ℤ-comm (pos zero) (pos n))
-- -- -- -- --     ∙ +ℤ-comm (pos 0 +negsuc n) (pos zero)
-- -- -- -- --   helper (pos (suc n₁)) (pos (suc n)) =
-- -- -- -- --     {!!}
-- -- -- -- --   helper (negsuc n₁) (pos (suc n)) = {!!}
-- -- -- -- --   helper a (negsuc n) = {!!}

-- -- -- -- -- fun : morph intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- -- -- fst fun = MV.d _ _ _ (λ _ → tt) (λ _ → tt) 0 ∘ grIso.inv coHom0-S0 .fst  ∘ λ a → a , (0 - a)
-- -- -- -- -- snd fun = {!!}
-- -- -- -- -- {- compMorph {F = intGroup} {G = dirProd intGroup intGroup} {H = coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))}
-- -- -- -- --                     ((λ a → a , a) , (λ a b → refl))
-- -- -- -- --                     (compMorph {F = dirProd intGroup intGroup} {G = coHomGr 0 (S₊ 0)} {H = coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt))} (grIso.inv coHom0-S0)
-- -- -- -- --                                (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0
-- -- -- -- --                                 , MV.dIsHom Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0)) .snd -}
-- -- -- -- -- {- theIso : grIso intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- -- -- theIso = Iso''→Iso _ _
-- -- -- -- --          (iso'' ((λ x → ∣ (λ {(inl tt) → 0ₖ ; (inr tt) → 0ₖ ; (push a i) → Kn→ΩKn+1 0 x i}) ∣₀) , {!!})
-- -- -- -- --                 {!!}
-- -- -- -- --                 {!MV.d!})
-- -- -- -- -- -}



-- -- -- -- -- theIso : grIso intGroup (coHomGr 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)))
-- -- -- -- -- theIso =
-- -- -- -- --   Iso''→Iso _ _
-- -- -- -- --    (iso'' fun
-- -- -- -- --           (λ x inker → {!MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0
-- -- -- -- --          (grIso.inv coHom0-S0 .fst (g , g))!})
-- -- -- -- --           (sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
-- -- -- -- --                  λ x → pRec propTruncIsProp
-- -- -- -- --                             (λ {(a , b) → {!fun!} })
-- -- -- -- --                             (fstFunHelper (∣ x ∣₀))))  
-- -- -- -- --   where
-- -- -- -- --   whoKnows : (a : S₊ 0 → Int) (x : MV.D Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt)) → MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (λ _ → a north) x
-- -- -- -- --       ≡ MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 a x
-- -- -- -- --   whoKnows a (inl x) = refl
-- -- -- -- --   whoKnows a (inr x) = refl
-- -- -- -- --   whoKnows a (push north i) = refl
-- -- -- -- --   whoKnows a (push south i) j = {!!}

-- -- -- -- --   helper : (a : Int) → (grIso.inv coHom0-S0 .fst (a , a)) ≡ ∣ S0→Int (a , a) ∣₀
-- -- -- -- --   helper a = {!have :

-- -- -- -- -- ∣
-- -- -- -- -- MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0
-- -- -- -- -- (S0→Int (x , x))
-- -- -- -- -- ∣₀
-- -- -- -- -- ≡ ∣ (λ _ → ∣ north ∣) ∣₀!}

-- -- -- -- --   helper2 : (a b : Int) → MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (a , a)) ≡ MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (b , b))
-- -- -- -- --          → a ≡ b
-- -- -- -- --   helper2 a b id = pRec (isSetInt a b) (λ {(pt , id) → {!!}}) (fstFunHelper ∣ (MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (a , a))) ∣₀)

-- -- -- -- --   idFun : (a : Int) → MV.D Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1
-- -- -- -- --   idFun a (inl x) = 0ₖ
-- -- -- -- --   idFun a (inr x) = 0ₖ
-- -- -- -- --   idFun a (push north i) = Kn→ΩKn+1 zero a i
-- -- -- -- --   idFun a (push south i) = Kn→ΩKn+1 zero a i

-- -- -- -- --   helper3 : (a : Int) → (MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (a , a))) ≡ idFun a
-- -- -- -- --   helper3 a = funExt λ {(inl x) → refl ; (inr x) → refl ; (push north i) → refl ; (push south i) → refl }

-- -- -- -- --   helper4 : (a b : Int) → MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (a , a))  ≡ MV.d-pre Unit Unit (Susp ⊥) (λ _ → tt) (λ _ → tt) 0 (S0→Int (b , b))
-- -- -- -- --           → a ≡ b
-- -- -- -- --   helper4 a b id =
-- -- -- -- --      {!!}
-- -- -- -- --    ∙ {!!}
-- -- -- -- --    ∙ {!!}
-- -- -- -- --     where
-- -- -- -- --     helper5 : {!!} --PathP (λ k → id k (inl tt) ≡ id k (inr tt)) (Kn→ΩKn+1 zero a) (Kn→ΩKn+1 zero a)
-- -- -- -- --     helper5 i j = {!id i!}

-- -- -- -- -- -- fun : coHom 1 (Pushout {A = S₊ 0} (λ _ → tt) (λ _ → tt)) → coHom 0 (S₊ 0)
-- -- -- -- -- -- fun a = (pRec {P = Σ[ x ∈ coHom 0 (S₊ 0)] (MV.d _ _ _ (λ _ → tt) (λ _ → tt) 0 x ≡ a) × isInIm (×coHomGr 0 Unit Unit) (coHomGr 0 (S₊ 0)) (MV.Δ _ _ _ (λ _ → tt) (λ _ → tt) 0) x}
-- -- -- -- -- --               (λ {(a1 , b) (c , d) → ΣProp≡ (λ x → isOfHLevelProd 1 (setTruncIsSet _ _) propTruncIsProp)
-- -- -- -- -- --                                             (sElim2 {B = λ a1 c → (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 a1 ≡ a)
-- -- -- -- -- --                                                                 → MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 c ≡ a
-- -- -- -- -- --                                                                 → isInIm (×coHomGr 0 Unit Unit) (coHomGr 0 (S₊ 0))
-- -- -- -- -- --                                                                           (λ z → MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 z) a1
-- -- -- -- -- --                                                                 → isInIm (×coHomGr 0 Unit Unit) (coHomGr 0 (S₊ 0))
-- -- -- -- -- --                                                                    (λ z → MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 z) c → a1 ≡ c}
-- -- -- -- -- --                                                     (λ _ _ → {!!})
-- -- -- -- -- --                                                     (λ a c b1 d1 → pElim (λ _ → isOfHLevelΠ 1 λ _ → setTruncIsSet _ _)
-- -- -- -- -- --                                                                      λ b2 → pElim (λ _ → setTruncIsSet _ _)
-- -- -- -- -- --                                                                               λ d2 → {!d2!})
-- -- -- -- -- --                                                     a1 c (proj₁ b) (proj₁ d) (proj₂ b) (proj₂ d))})
-- -- -- -- -- --               (λ {(a , b) → a , b , MV.Ker-d⊂Im-Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0 a {!!}})
-- -- -- -- -- --               (fstFunHelper a)) .fst -- pRec {!!} {!!} (fstFunHelper a)
