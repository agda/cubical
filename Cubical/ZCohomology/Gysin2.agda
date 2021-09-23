{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Gysin2 where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

open import Cubical.Data.Sum
open import Cubical.Relation.Nullary

open import Cubical.Functions.Embedding

open import Cubical.Data.Fin

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function hiding (case_of_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup ; Unit to UnitGroup) hiding (Bool)

open import Cubical.HITs.Pushout.Flattening
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergSteenrod
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim ; elim2 to trElim2)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)

open import Cubical.Algebra.AbGroup

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Join

open import Cubical.Homotopy.Hopf

open import Cubical.HITs.SetQuotients renaming (_/_ to _/'_)
open import Cubical.ZCohomology.Gysin


rUnitℤ· : ∀ {ℓ} (G : Group ℓ) → (x : ℤ) → (x ℤ[ G ]· GroupStr.1g (snd G))
                                                     ≡ GroupStr.1g (snd G)
rUnitℤ· G (pos zero) = refl
rUnitℤ· G (pos (suc n)) =
    cong (GroupStr._·_ (snd G) (GroupStr.1g (snd G)))
      (rUnitℤ· G (pos n))
  ∙ GroupStr.lid (snd G) (GroupStr.1g (snd G))
rUnitℤ· G (negsuc zero) = GroupTheory.inv1g G
rUnitℤ· G (negsuc (suc n)) =
    cong₂ (GroupStr._·_ (snd G)) (GroupTheory.inv1g G) (rUnitℤ· G (negsuc n))
  ∙ GroupStr.lid (snd G) (GroupStr.1g (snd G))

rUnitℤ·ℤ : (x : ℤ) → (x ℤ[ ℤGroup ]· 1) ≡ x
rUnitℤ·ℤ (pos zero) = refl
rUnitℤ·ℤ (pos (suc n)) = cong (pos 1 +_) (rUnitℤ·ℤ (pos n)) ∙ sym (pos+ 1 n)
rUnitℤ·ℤ (negsuc zero) = refl
rUnitℤ·ℤ (negsuc (suc n)) = cong (-1 +_) (rUnitℤ·ℤ (negsuc n)) ∙ +Comm (negsuc 0) (negsuc n)

private
  precommℤ : ∀ {ℓ} (G : Group ℓ) → (g : fst G) (y : ℤ) → (snd G GroupStr.· (y ℤ[ G ]· g)) g
                                                         ≡ (sucℤ y ℤ[ G ]· g)
  precommℤ G g (pos zero) = GroupStr.lid (snd G) g
                         ∙ sym (GroupStr.rid (snd G) g)
  precommℤ G g (pos (suc n)) =
       sym (GroupStr.assoc (snd G) _ _ _)
     ∙ cong ((snd G GroupStr.· g)) (precommℤ G g (pos n))
  precommℤ G g (negsuc zero) =
    GroupStr.invl (snd G) g
  precommℤ G g (negsuc (suc n)) =
    sym (GroupStr.assoc (snd G) _ _ _)
    ∙ cong ((snd G GroupStr.· GroupStr.inv (snd G) g)) (precommℤ G g (negsuc n))
    ∙ negsucLem n
    where
    negsucLem : (n : ℕ) → (snd G GroupStr.· GroupStr.inv (snd G) g)
      (sucℤ (negsuc n) ℤ[ G ]· g)
      ≡ (sucℤ (negsuc (suc n)) ℤ[ G ]· g)
    negsucLem zero = (GroupStr.rid (snd G) _)
    negsucLem (suc n) = refl

distrℤ· : ∀ {ℓ} (G : Group ℓ) → (g : fst G) (x y : ℤ)
       → ((x + y) ℤ[ G ]· g)
         ≡ GroupStr._·_ (snd G) (x ℤ[ G ]· g) (y ℤ[ G ]· g)
distrℤ· G' g (pos zero) y = cong (_ℤ[ G' ]· g) (+Comm 0 y)
                          ∙ sym (GroupStr.lid (snd G') _)
distrℤ· G' g (pos (suc n)) (pos n₁) =
    cong (_ℤ[ G' ]· g) (sym (pos+ (suc n) n₁))
  ∙ cong (GroupStr._·_ (snd G') g) (cong (_ℤ[ G' ]· g) (pos+ n n₁) ∙ distrℤ· G' g (pos n) (pos n₁))
  ∙ GroupStr.assoc (snd G') _ _ _
distrℤ· G' g (pos (suc n)) (negsuc zero) =
    distrℤ· G' g (pos n) 0
  ∙ ((GroupStr.rid (snd G') (pos n ℤ[ G' ]· g) ∙ sym (GroupStr.lid (snd G') (pos n ℤ[ G' ]· g)))
  ∙ cong (λ x → GroupStr._·_ (snd G') x (pos n ℤ[ G' ]· g))
         (sym (GroupStr.invl (snd G') g)) ∙ sym (GroupStr.assoc (snd G') _ _ _))
  ∙ (GroupStr.assoc (snd G') _ _ _)
  ∙ cong (λ x → GroupStr._·_ (snd G')  x (pos n ℤ[ G' ]· g)) (GroupStr.invl (snd G') g)
  ∙ GroupStr.lid (snd G') _
  ∙ sym (GroupStr.rid (snd G') _)
  ∙ (cong (GroupStr._·_ (snd G') (pos n ℤ[ G' ]· g)) (sym (GroupStr.invr (snd G') g))
  ∙ GroupStr.assoc (snd G') _ _ _)
  ∙ cong (λ x → GroupStr._·_ (snd G')  x (GroupStr.inv (snd G') g))
         (precommℤ G' g (pos n))
distrℤ· G' g (pos (suc n)) (negsuc (suc n₁)) =
     cong (_ℤ[ G' ]· g) (predℤ+negsuc n₁ (pos (suc n)))
  ∙∙ distrℤ· G' g (pos n) (negsuc n₁)
  ∙∙ (cong (λ x → GroupStr._·_ (snd G') x (negsuc n₁ ℤ[ G' ]· g))
           ((sym (GroupStr.rid (snd G') (pos n ℤ[ G' ]· g))
           ∙ cong (GroupStr._·_ (snd G') (pos n ℤ[ G' ]· g)) (sym (GroupStr.invr (snd G') g)))
         ∙∙ GroupStr.assoc (snd G') _ _ _
         ∙∙ cong (λ x → GroupStr._·_ (snd G') x (GroupStr.inv (snd G') g)) (precommℤ G' g (pos n) ))
    ∙ sym (GroupStr.assoc (snd G') _ _ _))
distrℤ· G' g (negsuc zero) y =
    cong (_ℤ[ G' ]· g) (+Comm -1 y) ∙ lol1 y
  module _ where
  lol1 : (y : ℤ) → (predℤ y ℤ[ G' ]· g) ≡ (snd G' GroupStr.· GroupStr.inv (snd G') g) (y ℤ[ G' ]· g)
  lol1 (pos zero) = sym (GroupStr.rid (snd G') _)
  lol1 (pos (suc n)) =
       sym (GroupStr.lid (snd G') ((pos n ℤ[ G' ]· g)))
    ∙∙ cong (λ x → GroupStr._·_ (snd G') x (pos n ℤ[ G' ]· g)) (sym (GroupStr.invl (snd G') g))
    ∙∙ sym (GroupStr.assoc (snd G') _ _ _)
  lol1 (negsuc n) = refl
distrℤ· G' g (negsuc (suc n)) y =
     cong (_ℤ[ G' ]· g) (+Comm (negsuc (suc n)) y)
  ∙∙ lol1 G' g 0 (y +negsuc n)
  ∙∙ cong (snd G' GroupStr.· GroupStr.inv (snd G') g)
          (cong (_ℤ[ G' ]· g) (+Comm y (negsuc n)) ∙ distrℤ· G' g (negsuc n) y)
   ∙ (GroupStr.assoc (snd G') _ _ _)



HopfInvariantPushElim : ∀ {ℓ} n → (f : _) → {P : HopfInvariantPush n f → Type ℓ}
                        → (isOfHLevel (suc (suc (suc (suc (n +ℕ n))))) (P (inl tt)))
                        →  (e : P (inl tt))
                          (g : (x : _) → P (inr x))
                          (r : PathP (λ i → P (push north i)) e (g (f north)))
                          → (x : _) → P x
HopfInvariantPushElim n f {P = P} hlev e g r (inl x) = e
HopfInvariantPushElim n f {P = P} hlev e g r (inr x) = g x
HopfInvariantPushElim n f {P = P} hlev e g r (push a i₁) = help a i₁
  where
  help : (a : Susp (Susp (S₊ (suc (n +ℕ n))))) → PathP (λ i → P (push a i)) e (g (f a))
  help = sphereElim _ (sphereElim _ (λ _ → isProp→isOfHLevelSuc ((suc (suc (n +ℕ n)))) (isPropIsOfHLevel _))
                      (isOfHLevelPathP' (suc (suc (suc (n +ℕ n))))
                        (subst (isOfHLevel (suc (suc (suc (suc (n +ℕ n))))))
                               (cong P (push north))
                               hlev) _ _)) r

transportCohomIso : ∀ {ℓ} {A : Type ℓ} {n m : ℕ}
                  → (p : n ≡ m)
                  → GroupIso (coHomGr n A) (coHomGr m A)
Iso.fun (fst (transportCohomIso {A = A} p)) = subst (λ n → coHom n A) p
Iso.inv (fst (transportCohomIso {A = A} p)) = subst (λ n → coHom n A) (sym p)
Iso.rightInv (fst (transportCohomIso p)) = transportTransport⁻ _
Iso.leftInv (fst (transportCohomIso p)) = transportTransport⁻ _
snd (transportCohomIso {A = A} {n = n} {m = m} p) =
  makeIsGroupHom (λ x y → help x y p)
  where
  help : (x y : coHom n A) (p : n ≡ m) → subst (λ n → coHom n A) p (x +ₕ y)
                                        ≡ subst (λ n → coHom n A) p x +ₕ subst (λ n → coHom n A) p y
  help x y = J (λ m p → subst (λ n → coHom n A) p (x +ₕ y)
                       ≡ subst (λ n → coHom n A) p x +ₕ subst (λ n → coHom n A) p y)
               (transportRefl (x +ₕ y) ∙ cong₂ _+ₕ_ (sym (transportRefl x)) (sym (transportRefl y)))

α-hopfMap : abs (HopfFunction zero (hopfFun , λ _ → hopfFun (snd (S₊∙ 3)))) ≡ suc zero
α-hopfMap = cong abs (cong (Iso.fun (fst (Hopfβ-Iso zero (hopfFun , refl))))
                     (transportRefl (⌣-α 0 (hopfFun , refl)))) ∙ l3 (sym CP2≡CP2') GysinS1.e (Hopfα zero (hopfFun , refl))
               (l isGenerator≃ℤ-e)
               (GroupIso→GroupEquiv (Hopfα-Iso 0 (hopfFun , refl)) , refl)
               (snd (fst ⌣hom))
               (GroupIso→GroupEquiv (Hopfβ-Iso zero (hopfFun , refl)))
  where
  l : Σ-syntax (GroupIso (coHomGr 2 CP2) ℤGroup)
      (λ ϕ → abs (Iso.fun (fst ϕ) GysinS1.e) ≡ 1)
      → Σ-syntax (GroupEquiv (coHomGr 2 CP2) ℤGroup)
      (λ ϕ → abs (fst (fst ϕ) GysinS1.e) ≡ 1)
  l p = (GroupIso→GroupEquiv (fst p)) , (snd p)

·Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
·Π {A = A} {n = zero} p q = (λ _ → pt A) , refl
fst (·Π {A = A} {n = suc zero} (f , p) (g , q)) base = pt A
fst (·Π {A = A} {n = suc zero} (f , p) (g , q)) (loop j) =
  ((sym p ∙∙ cong f loop ∙∙ p) ∙ (sym q ∙∙ cong g loop ∙∙ q)) j
snd (·Π {A = A} {n = suc zero} (f , p) (g , q)) = refl
fst (·Π {A = A} {n = suc (suc n)} (f , p) (g , q)) north = pt A
fst (·Π {A = A} {n = suc (suc n)} (f , p) (g , q)) south = pt A
fst (·Π {A = A} {n = suc (suc n)} (f , p) (g , q)) (merid a j) =
   ((sym p ∙∙ cong f (merid a ∙ sym (merid (ptSn (suc n)))) ∙∙ p)
  ∙ (sym q ∙∙ cong g (merid a ∙ sym (merid (ptSn (suc n)))) ∙∙ q)) j
snd (·Π {A = A} {n = suc (suc n)} (f , p) (g , q)) = refl

flipLoopSpace : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
              → Iso (fst ((Ω^ (suc n)) A)) (fst ((Ω^ n) (Ω A)))
flipLoopSpace n = {!!}

module _ {ℓ : Level} {A : Pointed ℓ} where
  convertLoopFun→ : (n : ℕ) → (S₊∙ (suc n) →∙ Ω A) → (S₊∙ (suc (suc n)) →∙ A)
  fst (convertLoopFun→ n f) north = pt A
  fst (convertLoopFun→ n f) south = pt A
  fst (convertLoopFun→ n f) (merid a i₁) = fst f a i₁
  snd (convertLoopFun→ n f) = refl

  myFiller : (n : ℕ) → (S₊∙ (suc (suc n)) →∙ A) → I → I → I → fst A
  myFiller n f i j k =
    hfill (λ k → λ { (i = i0) → doubleCompPath-filler (sym (snd f)) (cong (fst f) (merid (ptSn _) ∙ sym (merid (ptSn _)))) (snd f) k j
                   ; (i = i1) → snd f k
                   ; (j = i0) → snd f k
                   ; (j = i1) → snd f k})
          (inS ((fst f) (rCancel (merid (ptSn _)) i j)))
          k

  convertLoopFun← : (n : ℕ) → (S₊∙ (suc (suc n)) →∙ A) → (S₊∙ (suc n) →∙ Ω A)
  fst (convertLoopFun← n f) a = sym (snd f) ∙∙ cong (fst f) (merid a ∙ sym (merid (ptSn _))) ∙∙ snd f
  snd (convertLoopFun← n f) i j = myFiller n f i j i1

  convertLoopFun :  (n : ℕ) → Iso (S₊∙ (suc n) →∙ Ω A) (S₊∙ (suc (suc n)) →∙ A)
  Iso.fun (convertLoopFun n) f = convertLoopFun→ n f
  Iso.inv (convertLoopFun n) f = convertLoopFun← n f
  Iso.rightInv (convertLoopFun n) (f , p) =
    ΣPathP (funExt help , λ i j → p (~ i ∨ j))
    where
    help : (x : _) → fst (convertLoopFun→ n (convertLoopFun← n (f , p))) x ≡ f x
    help north = sym p
    help south = sym p ∙ cong f (merid (ptSn _))
    help (merid a j) i =
      hcomp (λ k → λ { (i = i1) → f (merid a j)
                      ; (j = i0) → p (~ i ∧ k)
                      ; (j = i1) → compPath-filler' (sym p) (cong f (merid (ptSn _))) k i})
            (f (compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j))
  Iso.leftInv (convertLoopFun n) f =
    ΣPathP (funExt help34 , help2)
    where

    sillyFill₂ : (x : S₊ (suc n)) → I → I → I → fst A
    sillyFill₂ x i j k =
      hfill (λ k → λ { (i = i0) → convertLoopFun→ n f .fst (compPath-filler' (merid x) (sym (merid (ptSn _))) k j)
                      ; (i = i1) → snd A
                      ; (j = i0) → fst f x (i ∨ ~ k)
                      ; (j = i1) → snd A})
                   (inS (snd f i (~ j)))
                   k

    sillyFill : (x : S₊ (suc n)) → I → I → I → fst A
    sillyFill x i j k =
      hfill (λ k → λ { (i = i0) → doubleCompPath-filler refl (cong (convertLoopFun→ n f .fst) (merid x ∙ sym (merid (ptSn _)))) refl k j
                      ; (i = i1) → fst f x (j ∨ ~ k)
                      ; (j = i0) → fst f x (i ∧ ~ k)
                      ; (j = i1) → snd A})
            (inS (sillyFill₂ x i j i1))
            k



    help34 : (x : _) → fst (convertLoopFun← n (convertLoopFun→ n f)) x ≡ fst f x
    help34 x i j = sillyFill x i j i1

    help2 : PathP _ _ _
    help2 i j k =
      hcomp (λ r → λ {(i = i0) → myFiller n (convertLoopFun→ n f) j k r
                     ; (i = i1) → snd f j (k ∨ ~ r)
                     ; (j = i0) → sillyFill (ptSn _) i k r
                     ; (j = i1) → snd A
                     ; (k = i0) → snd f j (i ∧ ~ r)
                     ; (k = i1) → snd A})
            (hcomp ((λ r → λ {(i = i0) → {!!}
                     ; (i = i1) → {!!}
                     ; (j = i0) → {!!}
                     ; (j = i1) → {!!}
                     ; (k = i0) → {!!}
                     ; (k = i1) → {!!}}))
                   {!!})

    {-
    i = i0 ⊢ snd (convertLoopFun← n (Iso.fun (convertLoopFun n) f)) j k
i = i1 ⊢ snd f j k
j = i0 ⊢ funExt help i (snd (S₊∙ (suc n))) k
j = i1 ⊢ snd (Ω A) k
k = i0 ⊢ snd A
k = i1 ⊢ snd A
    -}

→' : {ℓ : Level} {A : Pointed ℓ} (n : ℕ) → (S₊∙ (suc n) →∙ A) → (fst ((Ω^ (suc n)) A))
→' zero (f , p) = sym p ∙∙ cong f loop ∙∙ p
→' {A = A} (suc n) (f , p) = Iso.inv (flipLoopSpace _) (→' {A = Ω A} n (Iso.inv (convertLoopFun _) (f , p)))

←' : {ℓ : Level} {A : Pointed ℓ} (n : ℕ) → (fst ((Ω^ (suc n)) A)) → (S₊∙ (suc n) →∙ A)
fst (←' {A = A} zero f) base = pt A
fst (←' {A = A} zero f) (loop i₁) = f i₁
snd (←' {A = A} zero f) = refl
←' {A = A} (suc n) f = Iso.fun (convertLoopFun _) (←' n (Iso.fun (flipLoopSpace _) f))

cancel-r : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
         → (x : fst ((Ω^ (suc n)) A))
         → →' n (←' n x) ≡ x
cancel-r zero x = sym (rUnit _)
cancel-r (suc n) x =
     cong (Iso.inv (flipLoopSpace (suc n)) ∘ →' n)
          (Iso.leftInv (convertLoopFun _)
          (←' n (Iso.fun (flipLoopSpace (suc n)) x)))
  ∙∙ cong (Iso.inv (flipLoopSpace (suc n)))
          (cancel-r n (Iso.fun (flipLoopSpace (suc n)) x))
  ∙∙ Iso.leftInv (flipLoopSpace (suc n)) x

cancel-l : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
         → (x : (S₊∙ (suc n) →∙ A))
         → ←' n (→' n x) ≡ x
cancel-l zero (f , p) = ΣPathP (funExt fstp , λ i j → p (~ i ∨ j))
  where
  fstp : (x : _) → _ ≡ f x
  fstp base = sym p
  fstp (loop i) j = doubleCompPath-filler (sym p) (cong f loop) p (~ j) i
cancel-l (suc n) f =
     cong (Iso.fun (convertLoopFun n) ∘ ←' n) (Iso.rightInv (flipLoopSpace (suc n))
          (→' n (Iso.inv (convertLoopFun n) f)))
  ∙∙ cong (Iso.fun (convertLoopFun n)) (cancel-l n (Iso.inv (convertLoopFun n) f))
  ∙∙ Iso.rightInv (convertLoopFun _) _

→∙Ω : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (S₊∙ n →∙ A) (fst ((Ω^ n) A))
Iso.fun (→∙Ω {A = A} zero) (f , p) = f false
fst (Iso.inv (→∙Ω {A = A} zero) a) false = a
fst (Iso.inv (→∙Ω {A = A} zero) a) true = pt A
snd (Iso.inv (→∙Ω {A = A} zero) a) = refl
Iso.rightInv (→∙Ω {A = A} zero) a = refl
Iso.leftInv (→∙Ω {A = A} zero) (f , p) = ΣPathP ((funExt (λ { false → refl ; true → sym p})) , λ i j → p (~ i ∨ j))
→∙Ω {A = A} (suc n) = {!!}

-- 0Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ} → (S₊∙ n →∙ A)
-- fst (0Π {A = A}) _ = pt A
-- snd (0Π {A = A}) = refl

-- comm·Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
--         → (f g : S₊∙ (suc (suc n)) →∙ A)
--         → ·Π f g ≡ ·Π g f
-- fst (comm·Π {A = A} {n = n} f g i) north = pt A
-- fst (comm·Π {A = A} {n = n} f g i) south = pt A
-- fst (comm·Π {A = A} {n = zero} f g i) (merid base j) = {!!}
-- fst (comm·Π {A = A} {n = zero} f g i) (merid (loop k) j) = {!!}
-- fst (comm·Π {A = A} {n = suc n} f g i) (merid a j) = {!!}
-- snd (comm·Π {A = A} {n = n} f g i) = refl

-- rUnit·Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
--         → (f : S₊∙ (suc n) →∙ A)
--         → ·Π f 0Π ≡ f
-- fst (rUnit·Π {A = A} {n = zero} f i) base = snd f (~ i)
-- fst (rUnit·Π {A = A} {n = zero} f i) (loop j) = help i j
--   where
--   help : PathP (λ i → snd f (~ i) ≡ snd f (~ i))
--                (((sym (snd f)) ∙∙ (cong (fst f) loop) ∙∙ snd f)
--                  ∙ (refl ∙ refl))
--                (cong (fst f) loop)
--   help = (cong ((sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f) ∙_) (sym (rUnit refl)) ∙ sym (rUnit _))
--         ◁ λ i j → doubleCompPath-filler (sym (snd f)) (cong (fst f) loop) (snd f) (~ i) j
-- snd (rUnit·Π {A = A} {n = zero} f i) j = snd f (~ i ∨ j)
-- fst (rUnit·Π {A = A} {n = suc n} f i) north = snd f (~ i)
-- fst (rUnit·Π {A = A} {n = suc n} f i) south = (sym (snd f) ∙ cong (fst f) (merid (ptSn (suc n)))) i
-- fst (rUnit·Π {A = A} {n = suc n} f i) (merid a j) = help i j
--   where
--   help : PathP (λ i → snd f (~ i) ≡ (sym (snd f) ∙ cong (fst f) (merid (ptSn (suc n)))) i)
--                (((sym (snd f)) ∙∙ (cong (fst f) (merid a ∙ sym (merid (ptSn (suc n))))) ∙∙ snd f)
--                  ∙ (refl ∙ refl))
--                (cong (fst f) (merid a))
--   help = (cong (((sym (snd f)) ∙∙ (cong (fst f) (merid a ∙ sym (merid (ptSn (suc n))))) ∙∙ snd f) ∙_)
--               (sym (rUnit refl))
--        ∙ sym (rUnit _))
--        ◁ λ i j → hcomp (λ k → λ { (j = i0) → snd f (~ i ∧ k)
--                                   ; (j = i1) → compPath-filler' (sym (snd f)) (cong (fst f) (merid (ptSn (suc n)))) k i
--                                   ; (i = i0) → doubleCompPath-filler (sym (snd f))
--                                                   (cong (fst f) (merid a ∙ sym (merid (ptSn (suc n)))))
--                                                   (snd f) k j
--                                   ; (i = i1) → fst f (merid a j)})
--                         (fst f (compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j))
-- snd (rUnit·Π {A = A} {n = suc n} f i) j = snd f (~ i ∨ j)

-- -- _·π_ : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
-- --   → ∥ S₊∙ n →∙ A ∥₂
-- --   → ∥ S₊∙ n →∙ A ∥₂
-- --   → ∥ S₊∙ n →∙ A ∥₂
-- -- _·π_ = sRec2 squash₂ λ f g → ∣ ·Π f g ∣₂

-- -- open import Cubical.HITs.Wedge
-- -- _∨→_ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
-- --       → (f : A →∙ C) (g : B →∙ C)
-- --       → A ⋁ B → fst C
-- -- (f ∨→ g) (inl x) = fst f x
-- -- (f ∨→ g) (inr x) = fst g x
-- -- (f ∨→ g) (push a i₁) = (snd f ∙ sym (snd g)) i₁


-- -- add2 : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ} → (f g : S₊∙ n →∙ A) → ((S₊∙ n) ⋁ (S₊∙ n) , inl (ptSn _)) →∙ A
-- -- fst (add2 {A = A} f g) = f ∨→ g
-- -- snd (add2 {A = A} f g) = snd f

-- -- C* : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Type _
-- -- C* n f g = Pushout (λ _ → tt) (fst (add2 f g))

-- -- θ : ∀ {ℓ} {A : Pointed ℓ} → Susp (fst A) → (Susp (fst A) , north) ⋁ (Susp (fst A) , north)
-- -- θ north = inl north
-- -- θ south = inr north
-- -- θ {A = A} (merid a i₁) =
-- --      ((λ i → inl ((merid a ∙ sym (merid (pt A))) i))
-- --   ∙∙ push tt
-- --   ∙∙ λ i → inr ((merid a ∙ sym (merid (pt A))) i)) i₁


-- -- help3 : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
-- --         → p ∙∙ q ∙∙ r ≡ p ∙ q ∙ r
-- -- help3 {x = x} {y = y} {z = z} {w = w} =
-- --   J (λ y p → (q : y ≡ z) (r : z ≡ w) →
-- --       (p ∙∙ q ∙∙ r) ≡ p ∙ q ∙ r)
-- --      λ q r → lUnit (q ∙ r)

-- -- +≡ : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --    → (x : _) → ·Π f g .fst x ≡ (f ∨→ g) (θ {A = S₊∙ _} x)
-- -- +≡ n f g north = sym (snd f)
-- -- +≡ n f g south = sym (snd g)
-- -- +≡ n f g (merid a i₁) j = main j i₁
-- --   where

-- --   help : cong (f ∨→ g) (cong (θ {A = S₊∙ _}) (merid a))
-- --        ≡ (refl ∙∙ cong (fst f) (merid a ∙ sym (merid north)) ∙∙ snd f)
-- --        ∙ (sym (snd g) ∙∙ cong (fst g) (merid a ∙ sym (merid north)) ∙∙ refl) 
-- --   help = cong-∙∙ (f ∨→ g) ((λ i → inl ((merid a ∙ sym (merid north)) i)))
-- --                            (push tt)
-- --                            (λ i → inr ((merid a ∙ sym (merid north)) i))
-- --       ∙∙ help3 _ _ _
-- --       ∙∙ cong (cong (f ∨→ g)
-- --               (λ i₂ → inl ((merid a ∙ (λ i₃ → merid north (~ i₃))) i₂)) ∙_)
-- --               (sym (assoc _ _ _))
-- --       ∙∙ assoc _ _ _
-- --       ∙∙ cong₂ _∙_ refl (compPath≡compPath' _ _)

-- --   main : PathP (λ i → snd f (~ i) ≡ snd g (~ i)) (λ i₁ → ·Π f g .fst (merid a i₁))
-- --                λ i₁ → (f ∨→ g) (θ {A = S₊∙ _} (merid a i₁))
-- --   main = (λ i → ((λ j → snd f (~ i ∧ ~ j)) ∙∙ cong (fst f) (merid a ∙ sym (merid north)) ∙∙ snd f)
-- --                 ∙ (sym (snd g) ∙∙ cong (fst g) (merid a ∙ sym (merid north)) ∙∙ λ j → snd g (~ i ∧ j)))
-- --        ▷ sym help

-- -- +≡' : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --        → ·Π f g ≡ ((f ∨→ g) ∘ (θ {A = S₊∙ _}) , snd f)
-- -- +≡' n f g = ΣPathP ((funExt (+≡ n f g)) , (λ j i → snd f (i ∨ ~ j)))

-- -- WedgeElim : (n : ℕ) → ∀ {ℓ} {P : S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))) → Type ℓ}
-- --           → ((x : _) → isOfHLevel (3 +ℕ n) (P x))
-- --           → P (inl north)
-- --           → (x : _) → P x
-- -- WedgeElim n {P = P} x s (inl x₁) =
-- --   sphereElim _ {A = P ∘ inl}
-- --     (λ _ → isOfHLevelPlus' {n = n} (3 +ℕ n) (x _)) s x₁
-- -- WedgeElim n {P = P} x s (inr x₁) =
-- --   sphereElim _ {A = P ∘ inr}
-- --     (sphereElim _ (λ _ → isProp→isOfHLevelSuc ((suc (suc (n +ℕ n))))
-- --       (isPropIsOfHLevel (suc (suc (suc (n +ℕ n))))))
-- --         (subst (isOfHLevel ((3 +ℕ n) +ℕ n)) (cong P (push tt))
-- --           (isOfHLevelPlus' {n = n} (3 +ℕ n) (x _))))
-- --         (subst P (push tt) s) x₁
-- -- WedgeElim n {P = P} x s (push a j) = transp (λ i → P (push tt (i ∧ j))) (~ j) s


-- -- H²-C* : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --      → GroupIso (coHomGr (2 +ℕ n) (C* n f g)) ℤGroup
-- -- H²-C* n f g = compGroupIso groupIso1 (Hⁿ-Sⁿ≅ℤ (suc n))
-- --   where
-- --   help : (coHom (2 +ℕ n) (C* n f g)) → coHom (2 +ℕ n) (S₊ (2 +ℕ n))
-- --   help = sMap λ f → f ∘ inr


-- --   invMapPrim : (S₊ (2 +ℕ n) → coHomK (2 +ℕ n)) → C* n f g → coHomK (2 +ℕ n)
-- --   invMapPrim h (inl x) = h (ptSn _)
-- --   invMapPrim h (inr x) = h x
-- --   invMapPrim h (push a i₁) = WedgeElim n {P = λ a → h north ≡ h (fst (add2 f g) a)}
-- --                                                (λ _ → isOfHLevelTrunc (4 +ℕ n) _ _)
-- --                                                (cong h (sym (snd f))) a i₁

-- --   invMap : coHom (2 +ℕ n) (S₊ (2 +ℕ n)) → (coHom (2 +ℕ n) (C* n f g))
-- --   invMap = sMap invMapPrim

-- --   ret1 : (x : coHom (2 +ℕ n) (S₊ (2 +ℕ n))) → help (invMap x) ≡ x
-- --   ret1 = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- --                λ a → refl

-- --   ret2 : (x : (coHom (2 +ℕ n) (C* n f g))) → invMap (help x) ≡ x
-- --   ret2 = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- --                λ h → cong ∣_∣₂ (funExt λ { (inl x) → cong h ((λ i →  inr ((snd f) (~ i)))
-- --                                                            ∙ sym (push (inl north)))
-- --                                          ; (inr x) → refl
-- --                                          ; (push a i₁) → help2 h a i₁})
-- --     where
-- --     help2 : (h : C* n f g → coHomK (2 +ℕ n))
-- --           → (a : _) → PathP (λ i → invMapPrim (h ∘ inr) (push a i) ≡ h (push a i))
-- --                   (cong h ((λ i →  inr ((snd f) (~ i))) ∙ sym (push (inl north))))
-- --                   refl
-- --     help2 h = WedgeElim n (λ _ → isOfHLevelPathP (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n) _ _) _ _)
-- --                         help4

-- --       where
-- --       help4 : PathP (λ i → invMapPrim (h ∘ inr) (push (inl north) i) ≡ h (push (inl north) i))
-- --                   (cong h ((λ i →  inr ((snd f) (~ i))) ∙ sym (push (inl north))))
-- --                   refl
-- --       help4 i j = h (hcomp (λ k → λ { (i = i1) → inr (fst f north)
-- --                                      ; (j = i0) → inr (snd f (~ i))
-- --                                      ; (j = i1) → push (inl north) (i ∨ ~ k)})
-- --                            (inr (snd f (~ i ∧ ~ j))))

-- --   groupIso1 : GroupIso ((coHomGr (2 +ℕ n) (C* n f g))) (coHomGr (2 +ℕ n) (S₊ (2 +ℕ n)))
-- --   Iso.fun (fst groupIso1) = help
-- --   Iso.inv (fst groupIso1) = invMap
-- --   Iso.rightInv (fst groupIso1) = ret1
-- --   Iso.leftInv (fst groupIso1) = ret2
-- --   snd groupIso1 = makeIsGroupHom
-- --     (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
-- --            λ f g → refl)


-- -- C+ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Type _
-- -- C+ n f g = Pushout (λ _ → tt) (·Π f g .fst)

-- -- H⁴-C∨ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --         → GroupIso (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C+ n f g))
-- --                     ℤGroup
-- -- H⁴-C∨ n f g = compGroupIso
-- --   (transportCohomIso (cong (3 +ℕ_) (+-suc n n))) (Hopfβ-Iso n (·Π f g))

-- -- lol : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) (x : ℤ)
-- --          → Iso.inv (fst (H⁴-C∨ n f g)) x
-- --          ≡ subst (λ m → coHom m (C+ n f g)) (sym (cong (3 +ℕ_) (+-suc n n))) (Iso.inv (fst (Hopfβ-Iso n (·Π f g))) x)
-- -- lol n f g = λ _ → refl

-- -- H²-C∨ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --       → GroupIso (coHomGr (2 +ℕ n) (C+ n f g))
-- --                   ℤGroup
-- -- H²-C∨ n f g = Hopfα-Iso n (·Π f g)


-- -- H⁴-C* : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --      → GroupIso (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
-- --                  (DirProd ℤGroup ℤGroup)
-- -- H⁴-C* n f g = compGroupIso (GroupEquiv→GroupIso (invGroupEquiv fstIso))
-- --                            (compGroupIso (transportCohomIso (cong (2 +ℕ_) (+-suc n n)))
-- --                              (compGroupIso (Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n))))) (S₊∙ (suc (suc (suc (n +ℕ n))))) _)
-- --                                (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ _) (Hⁿ-Sⁿ≅ℤ _))))
-- --   where
-- --   module Ms = MV _ _ _ (λ _ → tt) (fst (add2 f g))
-- --   fstIso : GroupEquiv (coHomGr ((suc (suc (n +ℕ suc n)))) (S₊∙ (3 +ℕ (n +ℕ n)) ⋁ S₊∙ (3 +ℕ (n +ℕ n))))
-- --                       (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
-- --   fst (fst fstIso) = Ms.d (suc (suc (n +ℕ suc n))) .fst
-- --   snd (fst fstIso) =
-- --     SES→Iso
-- --       (GroupPath _ _ .fst (compGroupEquiv (invEquiv (isContr→≃Unit ((tt , tt) , (λ _ → refl))) , makeIsGroupHom λ _ _ → refl)
-- --                           (GroupEquivDirProd
-- --                             (GroupIso→GroupEquiv (invGroupIso (Hⁿ-Unit≅0 _)))
-- --                             (GroupIso→GroupEquiv
-- --                               (invGroupIso
-- --                                 (Hⁿ-Sᵐ≅0 _ _ λ p → ¬lem 0 ((λ _ → north) , refl) n n (cong suc (sym (+-suc n n)) ∙ p)))))))
-- --       (GroupPath _ _ .fst
-- --         (compGroupEquiv ((invEquiv (isContr→≃Unit ((tt , tt) , (λ _ → refl))) , makeIsGroupHom λ _ _ → refl))
-- --             ((GroupEquivDirProd
-- --                             (GroupIso→GroupEquiv (invGroupIso (Hⁿ-Unit≅0 _)))
-- --                             (GroupIso→GroupEquiv
-- --                               (invGroupIso (Hⁿ-Sᵐ≅0 _ _ λ p → ¬lem 0 ((λ _ → north) , refl) n (suc n) (cong (2 +ℕ_) (sym (+-suc n n)) ∙ p))))))))
-- --       (Ms.Δ (suc (suc (n +ℕ suc n))))
-- --       (Ms.d (suc (suc (n +ℕ suc n))))
-- --       (Ms.i (suc (suc (suc (n +ℕ suc n)))))
-- --       (Ms.Ker-d⊂Im-Δ _)
-- --       (Ms.Ker-i⊂Im-d _)
-- --   snd fstIso = Ms.d (suc (suc (n +ℕ suc n))) .snd

-- -- Hopfie : {n : ℕ} → ∥ S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n) ∥₂ → ℤ
-- -- Hopfie = sRec isSetℤ (HopfFunction _)

-- -- subber : (n : ℕ) (f : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → _
-- -- subber n f = subst (λ x → coHom x (HopfInvariantPush n (fst f)))
-- --                    (λ i → suc (suc (suc (+-suc n n i)))) 

-- -- module _ (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) where

-- --   C+' = C+ n f g

-- --   βₗ : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
-- --   βₗ = Iso.inv (fst (H⁴-C* n f g)) (1 , 0)

-- --   βᵣ : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
-- --   βᵣ = Iso.inv (fst (H⁴-C* n f g)) (0 , 1)

-- --   βᵣ'-fun : C* n f g → coHomK ((4 +ℕ (n +ℕ n)))
-- --   βᵣ'-fun (inl x) = 0ₖ _
-- --   βᵣ'-fun (inr x) = 0ₖ _
-- --   βᵣ'-fun (push (inl x) i₁) = 0ₖ _
-- --   βᵣ'-fun (push (inr x) i₁) = Kn→ΩKn+1 _ ∣ x ∣ i₁
-- --   βᵣ'-fun (push (push a i₂) i₁) = Kn→ΩKn+10ₖ _ (~ i₂) i₁


-- --   βₗ'-fun : C* n f g → coHomK (4 +ℕ (n +ℕ n))
-- --   βₗ'-fun (inl x) = 0ₖ _
-- --   βₗ'-fun (inr x) = 0ₖ _
-- --   βₗ'-fun (push (inl x) i₁) = Kn→ΩKn+1 _ ∣ x ∣ i₁
-- --   βₗ'-fun (push (inr x) i₁) = 0ₖ _
-- --   βₗ'-fun (push (push a i₂) i₁) = Kn→ΩKn+10ₖ _ i₂ i₁

-- --   βₗ''-fun : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
-- --   βₗ''-fun = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))) ∣ βₗ'-fun ∣₂

-- --   βᵣ''-fun : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
-- --   βᵣ''-fun = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))) ∣ βᵣ'-fun ∣₂

-- --   α∨ : coHom (2 +ℕ n) (C* n f g)
-- --   α∨ = Iso.inv (fst (H²-C* n f g)) 1

-- --   private
-- --     pp : (a : _) → 0ₖ (suc (suc n)) ≡ ∣ (f ∨→ g) a ∣
-- --     pp = WedgeElim _ (λ _ → isOfHLevelTrunc (4 +ℕ n) _ _)
-- --                    (cong ∣_∣ₕ (sym (snd f)))

-- --   pp-inr : pp (inr north) ≡ cong ∣_∣ₕ (sym (snd g))
-- --   pp-inr = (λ j → transport (λ i →  0ₖ (2 +ℕ n) ≡ ∣ compPath-filler' (snd f) (sym (snd g)) (~ j) i ∣ₕ)
-- --                              λ i → ∣ snd f (~ i ∨ j) ∣ₕ)
-- --          ∙ λ j → transp (λ i → 0ₖ (2 +ℕ n) ≡ ∣ snd g (~ i ∧ ~ j) ∣ₕ) j λ i → ∣ snd g (~ i ∨ ~ j) ∣ₕ

-- --   α∨'-fun : C* n f g → coHomK (2 +ℕ n)
-- --   α∨'-fun (inl x) = 0ₖ _
-- --   α∨'-fun (inr x) = ∣ x ∣
-- --   α∨'-fun (push a i₁) = pp a i₁

-- --   α∨' : coHom (2 +ℕ n) (C* n f g)
-- --   α∨' = ∣ α∨'-fun ∣₂


-- --   β+ : coHom ((2 +ℕ n) +' (2 +ℕ n)) C+'
-- --   β+ = Iso.inv (fst (H⁴-C∨ n f g)) 1

-- --   q : C+' → C* n f g
-- --   q (inl x) = inl x
-- --   q (inr x) = inr x
-- --   q (push a i₁) = (push (θ a) ∙ λ i → inr (+≡ n f g a (~ i))) i₁

-- --   jₗ : HopfInvariantPush n (fst f) → C* n f g
-- --   jₗ (inl x) = inl x
-- --   jₗ (inr x) = inr x
-- --   jₗ (push a i₁) = push (inl a) i₁

-- --   jᵣ : HopfInvariantPush n (fst g) → C* n f g
-- --   jᵣ (inl x) = inl x
-- --   jᵣ (inr x) = inr x
-- --   jᵣ (push a i₁) = push (inr a) i₁

-- -- α-∨→1 : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --         → Iso.fun (fst (H²-C* n f g)) (α∨' n f g) ≡ 1
-- -- α-∨→1 n f g = sym (cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ (suc n)))) (h33 n))
-- --              ∙ Iso.rightInv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) (pos 1)

-- -- α-∨-lem : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --         → α∨ n f g ≡ α∨' n f g
-- -- α-∨-lem n f g = sym (Iso.leftInv (fst (H²-C* n f g)) _)
-- --              ∙∙ cong (Iso.inv (fst (H²-C* n f g))) help
-- --              ∙∙ Iso.leftInv (fst (H²-C* n f g)) _
-- --   where
-- --   help : Iso.fun (fst (H²-C* n f g)) (α∨ n f g) ≡ Iso.fun (fst (H²-C* n f g)) (α∨' n f g)
-- --   help = (Iso.rightInv (fst (H²-C* n f g)) (pos 1)) ∙ sym (α-∨→1 n f g)

-- -- q-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (q n f g) (α∨ n f g) ≡ Hopfα n (·Π f g)
-- -- q-α n f g = (λ i → coHomFun _ (q n f g) (α-∨-lem n f g i))
-- --           ∙ sym (Iso.leftInv is _)
-- --           ∙∙ cong (Iso.inv is) help
-- --           ∙∙ Iso.leftInv is _
-- --   where
-- --   is = fst (Hopfα-Iso n (·Π f g))

-- --   help : Iso.fun is (coHomFun _ (q n f g) (α∨' n f g))
-- --        ≡ Iso.fun is (Hopfα n (·Π f g))
-- --   help = sym (cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ (suc n)))) (h33 n))
-- --       ∙∙ Iso.rightInv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) (pos 1)
-- --       ∙∙ sym (Hopfα-Iso-α n (·Π f g))


-- -- βₗ≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → βₗ n f g ≡ βₗ''-fun n f g
-- -- βₗ≡ n f g = cong (FF ∘ subber2)
-- --                  (cong (Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n)))))
-- --                                             (S₊∙ (suc (suc (suc (n +ℕ n)))))
-- --                                 (((suc (suc (n +ℕ n))))))))) help
-- --                ∙ help2)
-- --           ∙ funExt⁻ FF∘subber ∣ wedgeGen ∣₂
-- --           ∙ cong subber3 (sym βₗ'-fun≡)
-- --   where
-- --   FF = MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) (suc (suc (n +ℕ suc n))) .fst
-- --   FF' = MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) (suc (suc (suc (n +ℕ n)))) .fst

-- --   help : Iso.inv (fst (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))) (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) (1 , 0)
-- --        ≡ (∣ ∣_∣ ∣₂ , 0ₕ _)
-- --   help = ΣPathP ((h33 _) , IsGroupHom.pres1 (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))))

-- --   subber3 = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))

-- --   subber2 = (subst (λ m → coHom m (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n))))))
-- --                                (sym (cong (2 +ℕ_) (+-suc n n))))

-- --   FF∘subber : FF ∘ subber2 ≡ subber3 ∘ FF'
-- --   FF∘subber =
-- --     funExt (λ a → (λ j → transp (λ i → coHom ((suc ∘ suc ∘ suc) (+-suc n n (~ i ∧ j))) (C* n f g)) (~ j)
-- --                    (MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) ((suc (suc (+-suc n n j)))) .fst
-- --                       (transp (λ i → coHom (2 +ℕ (+-suc n n (j ∨ ~ i)))
-- --                                             (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))))) j
-- --                               a))))

-- --   wedgeGen : (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))) →
-- --        coHomK (suc (suc (suc (n +ℕ n)))))
-- --   wedgeGen (inl x) = ∣ x ∣
-- --   wedgeGen (inr x) = 0ₖ _
-- --   wedgeGen (push a i₁) = 0ₖ _

-- --   βₗ'-fun≡ : ∣ βₗ'-fun n f g ∣₂ ≡ FF' ∣ wedgeGen ∣₂
-- --   βₗ'-fun≡ = cong ∣_∣₂ (funExt λ { (inl x) → refl
-- --                                 ; (inr x) → refl
-- --                                 ; (push (inl x) i₁) → refl
-- --                                 ; (push (inr x) i₁) j → Kn→ΩKn+10ₖ _ (~ j) i₁
-- --                                 ; (push (push a i₂) i₁) j → Kn→ΩKn+10ₖ _ (~ j ∧ i₂) i₁})

-- --   help2 : Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n))))) (S₊∙ (suc (suc (suc (n +ℕ n))))) (((suc (suc (n +ℕ n))))))))
-- --                    (∣ ∣_∣ ∣₂ , 0ₕ _)
-- --                    ≡ ∣ wedgeGen ∣₂
-- --   help2 = cong ∣_∣₂ (funExt λ { (inl x) → rUnitₖ (suc (suc (suc (n +ℕ n)))) ∣ x ∣
-- --                              ; (inr x) → refl
-- --                              ; (push a i₁) → refl})

-- -- βᵣ≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → βᵣ n f g ≡ βᵣ''-fun n f g
-- -- βᵣ≡ n f g =
-- --     cong (FF ∘ subber2)
-- --       (cong (Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n)))))
-- --                                             (S₊∙ (suc (suc (suc (n +ℕ n)))))
-- --                                 (((suc (suc (n +ℕ n)))))))))
-- --             help
-- --           ∙ help2)
-- --   ∙ funExt⁻ FF∘subber ∣ wedgeGen ∣₂
-- --   ∙ cong (subber3) (sym βᵣ'-fun≡)
-- --   where
-- --   FF = MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) (suc (suc (n +ℕ suc n))) .fst
-- --   FF' = MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) (suc (suc (suc (n +ℕ n)))) .fst

-- --   help : Iso.inv (fst (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))) (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) (0 , 1)
-- --        ≡ (0ₕ _ , ∣ ∣_∣ ∣₂)
-- --   help = ΣPathP (IsGroupHom.pres1 (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) , (h33 _))

-- --   subber3 = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))

-- --   subber2 = (subst (λ m → coHom m (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n))))))
-- --                                (sym (cong (2 +ℕ_) (+-suc n n))))

-- --   FF∘subber : FF ∘ subber2 ≡ subber3 ∘ FF'
-- --   FF∘subber =
-- --     funExt (λ a → (λ j → transp (λ i → coHom ((suc ∘ suc ∘ suc) (+-suc n n (~ i ∧ j))) (C* n f g)) (~ j)
-- --                    (MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) ((suc (suc (+-suc n n j)))) .fst
-- --                       (transp (λ i → coHom (2 +ℕ (+-suc n n (j ∨ ~ i)))
-- --                                             (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))))) j
-- --                               a))))

-- --   wedgeGen : (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))) →
-- --        coHomK (suc (suc (suc (n +ℕ n)))))
-- --   wedgeGen (inl x) = 0ₖ _
-- --   wedgeGen (inr x) = ∣ x ∣
-- --   wedgeGen (push a i₁) = 0ₖ _


-- --   help2 : Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n))))) (S₊∙ (suc (suc (suc (n +ℕ n))))) (((suc (suc (n +ℕ n))))))))
-- --                    (0ₕ _ , ∣ ∣_∣ ∣₂)
-- --                    ≡ ∣ wedgeGen ∣₂
-- --   help2 = cong ∣_∣₂ (funExt λ { (inl x) → refl
-- --                              ; (inr x) → lUnitₖ (suc (suc (suc (n +ℕ n)))) ∣ x ∣
-- --                              ; (push a i₁) → refl})

-- --   βᵣ'-fun≡ : ∣ βᵣ'-fun n f g ∣₂ ≡ FF' ∣ wedgeGen ∣₂
-- --   βᵣ'-fun≡ = cong ∣_∣₂ (funExt λ { (inl x) → refl
-- --                                 ; (inr x) → refl
-- --                                 ; (push (inl x) i₁) j → Kn→ΩKn+10ₖ _ (~ j) i₁
-- --                                 ; (push (inr x) i₁) → refl
-- --                                 ; (push (push a i₂) i₁) j → Kn→ΩKn+10ₖ _ (~ j ∧ ~ i₂) i₁})

-- -- q-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (q n f g) (βₗ n f g)
-- --     ≡ β+ n f g
-- -- q-βₗ n f g = cong (coHomFun _ (q n f g)) (βₗ≡ n f g)
-- --            ∙ transportLem
-- --            ∙ cong (subst (λ m → coHom m (C+' n f g))
-- --                   (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
-- --                         (sym (Iso.leftInv (fst (Hopfβ-Iso n (·Π f g))) (Hopfβ n (·Π f g)))
-- --                         ∙ cong (Iso.inv ((fst (Hopfβ-Iso n (·Π f g))))) (d-β n (·Π f g)))
-- --   where
-- --   transportLem : coHomFun (suc (suc (suc (n +ℕ suc n)))) (q n f g)
-- --       (βₗ''-fun n f g)
-- --      ≡ subst (λ m → coHom m (C+' n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --              (Hopfβ n (·Π f g))
-- --   transportLem =
-- --       natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (q n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --     ∙ cong (subst (λ m → coHom m (C+' n f g))
-- --       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
-- --         (cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → loll a i₁}))
-- --     where
-- --     open import Cubical.Foundations.Path
-- --     loll : (x : fst (S₊∙ (3 +ℕ (n +ℕ n)))) →
-- --       PathP
-- --       (λ i₁ →
-- --          βₗ'-fun n f g ((push (θ x) ∙ λ i → inr (+≡ n f g x (~ i))) i₁) ≡
-- --          MV.d-pre Unit (fst (S₊∙ (2 +ℕ n))) (fst (S₊∙ (3 +ℕ n +ℕ n)))
-- --          (λ _ → tt) (fst (·Π f g)) (3 +ℕ n +ℕ n) ∣_∣ (push x i₁))
-- --       (λ _ → βₗ'-fun n f g (q n f g (inl tt)))
-- --       (λ _ → βₗ'-fun n f g (q n f g (inr (·Π f g .fst x))))
-- --     loll x =
-- --       flipSquare (cong-∙ (βₗ'-fun n f g) (push (θ x)) (λ i → inr (+≡ n f g x (~ i)))
-- --               ∙∙ sym (rUnit _)
-- --               ∙∙ lem₁ x)

-- --       where
-- --       lem₁ : (x : _) → cong (βₗ'-fun n f g) (push (θ {A = S₊∙ _} x)) ≡ Kn→ΩKn+1 _ ∣ x ∣
-- --       lem₁ north = refl
-- --       lem₁ south = sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))
-- --       lem₁ (merid a j) k = lala k j
-- --         where
-- --         lala : PathP (λ k → Kn→ΩKn+1 _ ∣ north ∣ₕ ≡ (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))) k)
-- --                      (λ j → cong (βₗ'-fun n f g) (push (θ {A = S₊∙ _} (merid a j))))
-- --                      (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
-- --         lala = (cong-∙∙ (cong (βₗ'-fun n f g) ∘ push)
-- --                         ((λ i₁ → inl ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁)))
-- --                         (push tt)
-- --                         ((λ i₁ → inr ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁)))
-- --                         ∙ sym (compPath≡compPath' _ _)
-- --                         ∙ (λ _ → (λ j → Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∣ (merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) j ∣ₕ)
-- --                                ∙ Kn→ΩKn+10ₖ _)
-- --                         ∙ cong (_∙ Kn→ΩKn+10ₖ _) (cong-∙ ((Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ))
-- --                                (merid a) (sym (merid north)))
-- --                         ∙ sym (assoc _ _ _)
-- --                         ∙ cong (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a) ∙_)
-- --                                (sym (symDistr (sym ((Kn→ΩKn+10ₖ _))) (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))))))
-- --                         ◁ λ i j → compPath-filler (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
-- --                                                     (sym (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))))
-- --                                                                                      (cong ∣_∣ₕ (merid north))))
-- --                                                     (~ i) j

-- -- q-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (q n f g) (βᵣ n f g)
-- --     ≡ β+ n f g
-- -- q-βᵣ n f g = cong (coHomFun _ (q n f g)) (βᵣ≡ n f g)
-- --            ∙ transportLem
-- --            ∙ cong (subst (λ m → coHom m (C+' n f g))
-- --                   (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
-- --                         (sym (Iso.leftInv (fst (Hopfβ-Iso n (·Π f g))) (Hopfβ n (·Π f g)))
-- --                         ∙ cong (Iso.inv ((fst (Hopfβ-Iso n (·Π f g))))) (d-β n (·Π f g)))
-- --   where
-- --   transportLem : coHomFun (suc (suc (suc (n +ℕ suc n)))) (q n f g)
-- --       (βᵣ''-fun n f g)
-- --      ≡ subst (λ m → coHom m (C+' n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --              (Hopfβ n (·Π f g))
-- --   transportLem =
-- --       natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (q n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --     ∙ cong (subst (λ m → coHom m (C+' n f g))
-- --       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
-- --         (cong ∣_∣₂ (funExt λ { (inl x) → refl
-- --                             ; (inr x) → refl
-- --                             ; (push a i₁) → loll a i₁}))
-- --     where
-- --     open import Cubical.Foundations.Path
-- --     loll : (x : fst (S₊∙ (3 +ℕ (n +ℕ n)))) →
-- --       PathP
-- --       (λ i₁ →
-- --          βᵣ'-fun n f g ((push (θ x) ∙ λ i → inr (+≡ n f g x (~ i))) i₁) ≡
-- --          MV.d-pre Unit (fst (S₊∙ (2 +ℕ n))) (fst (S₊∙ (3 +ℕ n +ℕ n)))
-- --          (λ _ → tt) (fst (·Π f g)) (3 +ℕ n +ℕ n) ∣_∣ (push x i₁))
-- --       (λ _ → βᵣ'-fun n f g (q n f g (inl tt)))
-- --       (λ _ → βᵣ'-fun n f g (q n f g (inr (·Π f g .fst x))))
-- --     loll x = flipSquare (cong-∙ (βᵣ'-fun n f g) (push (θ x)) (λ i → inr (+≡ n f g x (~ i)))
-- --                      ∙∙ sym (rUnit _)
-- --                      ∙∙ lem₁ x)
-- --       where
-- --       lem₁ : (x : _) → cong (βᵣ'-fun n f g) (push (θ {A = S₊∙ _} x)) ≡ Kn→ΩKn+1 _ ∣ x ∣
-- --       lem₁ north = sym (Kn→ΩKn+10ₖ _)
-- --       lem₁ south = cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))
-- --       lem₁ (merid a j) k = lala k j -- lala k j
-- --         where
-- --         lala : PathP (λ k → (Kn→ΩKn+10ₖ _) (~ k) ≡ (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))) k)
-- --                      (λ j → cong (βᵣ'-fun n f g) (push (θ {A = S₊∙ _} (merid a j))))
-- --                      (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
-- --         lala = (cong-∙∙ (cong (βᵣ'-fun n f g) ∘ push)
-- --                         (λ i₁ → inl ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁))
-- --                         (push tt)
-- --                         (λ i₁ → inr ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁))
-- --              ∙∙ (cong (sym (Kn→ΩKn+10ₖ _) ∙_) (cong-∙ (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a) (sym (merid (ptSn _)))))
-- --              ∙∙ sym (help3 _ _ _))
-- --              ◁ symP (doubleCompPath-filler
-- --                       (sym (Kn→ΩKn+10ₖ _))
-- --                       (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
-- --                       (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (sym (merid north))))
-- -- open import Cubical.Foundations.Path
-- -- jₗ-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (jₗ n f g) (α∨ n f g)
-- --     ≡ Hopfα n f
-- -- jₗ-α n f g =
-- --     cong (coHomFun _ (jₗ n f g)) (α-∨-lem n f g)
-- --   ∙ cong ∣_∣₂ (funExt (HopfInvariantPushElim n (fst f)
-- --                       (isOfHLevelPath ((suc (suc (suc (suc (n +ℕ n))))))
-- --                         (isOfHLevelPlus' {n = n} (4 +ℕ n) (isOfHLevelTrunc (4 +ℕ n))) _ _)
-- --                       refl
-- --                       (λ _ → refl)
-- --                       λ j → refl))

-- -- jₗ-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (jₗ n f g) (βₗ n f g)
-- --     ≡ subst (λ m → coHom m (HopfInvariantPush n (fst f)))
-- --             (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --             (Hopfβ n f)
-- -- jₗ-βₗ n f g =
-- --      cong (coHomFun _ (jₗ n f g)) (βₗ≡ n f g)
-- --   ∙∙ natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (jₗ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --   ∙∙  cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
-- --       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
-- --         (cong ∣_∣₂
-- --           (funExt λ { (inl x) → refl
-- --                     ; (inr x) → refl
-- --                     ; (push a i₁) → refl}))

-- -- jₗ-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (jₗ n f g) (βᵣ n f g)
-- --     ≡ 0ₕ _
-- -- jₗ-βᵣ n f g =
-- --   cong (coHomFun _ (jₗ n f g)) (βᵣ≡ n f g)
-- --   ∙∙ natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (jₗ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --   ∙∙ cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
-- --       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
-- --       cool
-- --   where
-- --   cool : coHomFun (suc (suc (suc (suc (n +ℕ n))))) (jₗ n f g)
-- --       ∣ βᵣ'-fun n f g ∣₂ ≡ 0ₕ _
-- --   cool = cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → refl})

-- -- jᵣ-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (jᵣ n f g) (α∨ n f g)
-- --     ≡ Hopfα n g
-- -- jᵣ-α n f g = cong (coHomFun _ (jᵣ n f g)) (α-∨-lem n f g)
-- --   ∙ cong ∣_∣₂ (funExt (HopfInvariantPushElim n (fst g)
-- --                       (isOfHLevelPath ((suc (suc (suc (suc (n +ℕ n))))))
-- --                         (isOfHLevelPlus' {n = n} (4 +ℕ n) (isOfHLevelTrunc (4 +ℕ n))) _ _)
-- --                       refl
-- --                       (λ _ → refl)
-- --                       (flipSquare (pp-inr n f g))))

-- -- jᵣ-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (jᵣ n f g) (βₗ n f g) ≡ 0ₕ _
-- -- jᵣ-βₗ n f g =
-- --   cong (coHomFun _ (jᵣ n f g)) (βₗ≡ n f g)
-- --   ∙∙ natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (jᵣ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --   ∙∙ cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
-- --       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
-- --       cool
-- --   where
-- --   cool : coHomFun (suc (suc (suc (suc (n +ℕ n))))) (jᵣ n f g)
-- --       ∣ βₗ'-fun n f g ∣₂ ≡ 0ₕ _
-- --   cool = cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → refl})


-- -- jᵣ-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → coHomFun _ (jᵣ n f g) (βᵣ n f g)
-- --     ≡ subst (λ m → coHom m (HopfInvariantPush n (fst g)))
-- --             (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --             (Hopfβ n g)
-- -- jᵣ-βᵣ n f g =
-- --   cong (coHomFun _ (jᵣ n f g)) (βᵣ≡ n f g)
-- --   ∙∙ natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (jᵣ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --   ∙∙  cong (subst (λ m → coHom m (HopfInvariantPush n (fst g)))
-- --       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
-- --         (cong ∣_∣₂
-- --           (funExt λ { (inl x) → refl
-- --                     ; (inr x) → refl
-- --                     ; (push a i₁) → refl}))

-- -- gen₂ℤ×ℤ : gen₂-by (DirProd ℤGroup ℤGroup) (1 , 0) (0 , 1)
-- -- fst (gen₂ℤ×ℤ (x , y)) = x , y
-- -- snd (gen₂ℤ×ℤ (x , y)) =
-- --   ΣPathP ((cong₂ _+_ ((·Comm 1 x) ∙ cong fst (sym (distrLem 1 0 x))) ((·Comm 0 y) ∙ cong fst (sym (distrLem 0 1 y))))
-- --         , +Comm y 0 ∙ cong₂ _+_ (·Comm 0 x ∙ cong snd (sym (distrLem 1 0 x))) (·Comm 1 y ∙ cong snd (sym (distrLem 0 1 y))))
-- --   where
-- --   ℤ×ℤ = DirProd ℤGroup ℤGroup
-- --   _+''_ = GroupStr._·_ (snd ℤ×ℤ)

-- --   ll3 : (x : ℤ) → - x ≡ 0 - x
-- --   ll3 (pos zero) = refl
-- --   ll3 (pos (suc zero)) = refl
-- --   ll3 (pos (suc (suc n))) =
-- --     cong predℤ (ll3 (pos (suc n)))
-- --   ll3 (negsuc zero) = refl
-- --   ll3 (negsuc (suc n)) = cong sucℤ (ll3 (negsuc n))

-- --   distrLem : (x y : ℤ) (z : ℤ)
-- --          → Path (ℤ × ℤ) (z ℤ[ ℤ×ℤ ]· (x , y)) (z · x , z · y)
-- --   distrLem x y (pos zero) = refl
-- --   distrLem x y (pos (suc n)) =
-- --     (cong ((x , y) +''_) (distrLem x y (pos n)))
-- --   distrLem x y (negsuc zero) = ΣPathP (sym (ll3 x) , sym (ll3 y))
-- --   distrLem x y (negsuc (suc n)) =
-- --     cong₂ _+''_ (ΣPathP (sym (ll3 x) , sym (ll3 y)))
-- --                 (distrLem x y (negsuc n))
  
-- -- genH²ⁿC* : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --          → gen₂-by (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
-- --                     (βₗ n f g)
-- --                     (βᵣ n f g)
-- -- genH²ⁿC* n f g =
-- --   Iso-pres-gen₂ (DirProd ℤGroup ℤGroup)
-- --     (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
-- --     (1 , 0)
-- --     (0 , 1)
-- --     gen₂ℤ×ℤ
-- --     (invGroupIso (H⁴-C* n f g))

-- -- private

-- --   H⁴C* : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Group _
-- --   H⁴C* n f g = coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)

-- --   X : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --       → ℤ
-- --   X n f g = (genH²ⁿC* n f g) (α∨ n f g ⌣ α∨ n f g) .fst .fst
-- --   Y : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --       → ℤ
-- --   Y n  f g = (genH²ⁿC* n f g) (α∨ n f g ⌣ α∨ n f g) .fst .snd

-- --   α∨≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --       → α∨ n f g ⌣ α∨ n f g ≡ ((X n f g) ℤ[ H⁴C* n f g ]· βₗ n f g)
-- --                             +ₕ ((Y n f g) ℤ[ H⁴C* n f g ]· βᵣ n f g)
-- --   α∨≡ n f g = (genH²ⁿC* n f g) (α∨ n f g ⌣ α∨ n f g) .snd


-- -- eq₁ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → (Hopfα n (·Π f g)) ⌣ (Hopfα n (·Π f g))
-- --     ≡ ((X n f g + Y n f g) ℤ[ coHomGr _ _ ]· (β+ n f g))
-- -- eq₁ n f g =
-- --     cong (λ x → x ⌣ x) (sym (q-α n f g) ∙ cong (coHomFun (suc (suc n)) (q n f g)) (α-∨-lem n f g))
-- --   ∙ cong ((coHomFun _) (q _ f g)) (cong (λ x → x ⌣ x) (sym (α-∨-lem n f g))
-- --                        ∙ α∨≡ n f g)
-- --   ∙ IsGroupHom.pres· (coHomMorph _ (q n f g) .snd) _ _
-- --   ∙ cong₂ _+ₕ_ (hompres· (coHomMorph _ (q n f g)) (βₗ n f g) (X n f g)
-- --                        ∙ cong (λ z → (X n f g) ℤ[ coHomGr _ _ ]· z)
-- --                               (q-βₗ n f g))
-- --                (hompres· (coHomMorph _ (q n f g)) (βᵣ n f g) (Y n f g)
-- --                        ∙ cong (λ z → (Y n f g) ℤ[ coHomGr _ _ ]· z)
-- --                               (q-βᵣ n f g))
-- --   ∙ sym (distrℤ· (coHomGr _ _) (β+ n f g) (X n f g) (Y n f g))

-- -- coHomFun⌣ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
-- --           → (n : ℕ) (x y : coHom n B)
-- --           → coHomFun _ f (x ⌣ y) ≡ coHomFun _ f x ⌣ coHomFun _ f y
-- -- coHomFun⌣ f n = sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl

-- -- eq₂ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → Hopfα n f ⌣ Hopfα n f
-- --     ≡ (X n f g ℤ[ coHomGr _ _ ]· subst (λ m → coHom m (HopfInvariantPush n (fst f)))
-- --             (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --             (Hopfβ n f))
-- -- eq₂ n f g =
-- --      cong (λ x → x ⌣ x) (sym (jₗ-α n f g))
-- --   ∙∙ sym (coHomFun⌣ (jₗ n f g) _ _ _)
-- --   ∙∙ cong (coHomFun _ (jₗ n f g)) (α∨≡ n f g)
-- --   ∙∙ IsGroupHom.pres· (snd (coHomMorph _ (jₗ n f g))) _ _
-- --   ∙∙ cong₂ _+ₕ_ (hompres· (coHomMorph _ (jₗ n f g)) (βₗ n f g) (X n f g))
-- --                 (hompres· (coHomMorph _ (jₗ n f g)) (βᵣ n f g) (Y n f g)
-- --                           ∙ cong (λ z → (Y n f g) ℤ[ coHomGr _ _ ]· z)
-- --                                  (jₗ-βᵣ n f g))
-- --   ∙∙ cong₂ _+ₕ_ refl (rUnitℤ· (coHomGr _ _) (Y n f g))
-- --   ∙∙ (rUnitₕ _ _
-- --    ∙ cong (X n f g ℤ[ coHomGr _ _ ]·_) (jₗ-βₗ n f g))

-- -- eq₃ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --     → Hopfα n g ⌣ Hopfα n g
-- --     ≡ (Y n f g ℤ[ coHomGr _ _ ]· subst (λ m → coHom m (HopfInvariantPush n (fst f)))
-- --             (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
-- --             (Hopfβ n g))
-- -- eq₃ n f g =
-- --      cong (λ x → x ⌣ x) (sym (jᵣ-α n f g))
-- --   ∙∙ sym (coHomFun⌣ (jᵣ n f g) _ _ _)
-- --   ∙∙ cong (coHomFun _ (jᵣ n f g)) (α∨≡ n f g)
-- --   ∙∙ IsGroupHom.pres· (snd (coHomMorph _ (jᵣ n f g))) _ _
-- --   ∙∙ cong₂ _+ₕ_ (hompres· (coHomMorph _ (jᵣ n f g)) (βₗ n f g) (X n f g)
-- --                           ∙ cong (λ z → (X n f g) ℤ[ coHomGr _ _ ]· z)
-- --                                  (jᵣ-βₗ n f g))
-- --                 (hompres· (coHomMorph _ (jᵣ n f g)) (βᵣ n f g) (Y n f g))
-- --   ∙∙ cong₂ _+ₕ_ (rUnitℤ· (coHomGr _ _) (X n f g)) refl
-- --   ∙∙ ((lUnitₕ _ _) ∙ cong (Y n f g ℤ[ coHomGr _ _ ]·_) (jᵣ-βᵣ n f g))

-- -- eq₂-eq₂ : (n : ℕ) (f g : S₊∙ (suc (suc (suc (n +ℕ n)))) →∙ S₊∙ (suc (suc n)))
-- --         → HopfFunction n (·Π f g) ≡ HopfFunction n f + HopfFunction n g
-- -- eq₂-eq₂ n f g =
-- --       mainL
-- --    ∙ sym (cong₂ _+_ (help n f g) (helpg n f g))
-- --   where
-- --   transpLem : ∀ {ℓ} {G : ℕ → Group ℓ}
-- --              → (n m : ℕ)
-- --              → (x : ℤ)
-- --              → (p : m ≡ n)
-- --              → (g : fst (G n))
-- --              → subst (fst ∘ G) p (x ℤ[ G m ]· subst (fst ∘ G) (sym p) g) ≡ (x ℤ[ G n ]· g)
-- --   transpLem {G = G} n m x =
-- --     J (λ n p → (g : fst (G n)) → subst (fst ∘ G) p (x ℤ[ G m ]· subst (fst ∘ G) (sym p) g)
-- --                                 ≡ (x ℤ[ G n ]· g))
-- --       λ g → transportRefl _ ∙ cong (x ℤ[ G m ]·_) (transportRefl _)

-- --   mainL : HopfFunction n (·Π f g) ≡ X n f g + Y n f g
-- --   mainL = cong (Iso.fun (fst (Hopfβ-Iso n (·Π f g))))
-- --                (cong (subst (λ x → coHom x (HopfInvariantPush n (fst (·Π f g))))
-- --                             λ i₁ → suc (suc (suc (+-suc n n i₁))))
-- --                      (eq₁ n f g))
-- --        ∙∙ cong (Iso.fun (fst (Hopfβ-Iso n (·Π f g))))
-- --                (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst (·Π f g)))} _ _
-- --                           (X n f g + Y n f g) (λ i₁ → suc (suc (suc (+-suc n n i₁))))
-- --                           (Iso.inv (fst (Hopfβ-Iso n (·Π f g))) 1))
-- --        ∙∙ hompres· (_ , snd (Hopfβ-Iso n (·Π f g))) (Iso.inv (fst (Hopfβ-Iso n (·Π f g))) 1)
-- --                    (X n f g + Y n f g) 
-- --        ∙∙ cong ((X n f g + Y n f g) ℤ[ ℤ , ℤGroup .snd ]·_)
-- --                (Iso.rightInv ((fst (Hopfβ-Iso n (·Π f g)))) 1)
-- --        ∙∙ rUnitℤ·ℤ (X n f g + Y n f g)


-- --   help : (n : ℕ) (f g : _) → HopfFunction n f ≡ X n f g
-- --   help n f g = cong (Iso.fun (fst (Hopfβ-Iso n f)))
-- --               (cong (subst (λ x → coHom x (HopfInvariantPush n (fst f)))
-- --                     (λ i₁ → suc (suc (suc (+-suc n n i₁))))) (eq₂ n f g))
-- --             ∙ cong (Iso.fun (fst (Hopfβ-Iso n f)))
-- --                    (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst f))} _ _
-- --                               (X n f g)
-- --                               ((cong (suc ∘ suc ∘ suc) (+-suc n n)))
-- --                               (Hopfβ n f))
-- --             ∙ hompres· (_ , snd (Hopfβ-Iso n f)) (Hopfβ n f) (X n f g)
-- --             ∙ cong (X n f g ℤ[ ℤ , ℤGroup .snd ]·_) (d-β n f)
-- --             ∙ rUnitℤ·ℤ (X n f g)

-- --   helpg : (n : ℕ) (f g : _) → HopfFunction n g ≡ Y n f g
-- --   helpg n f g =
-- --        cong (Iso.fun (fst (Hopfβ-Iso n g)))
-- --             (cong (subst (λ x → coHom x (HopfInvariantPush n (fst g)))
-- --                     (λ i₁ → suc (suc (suc (+-suc n n i₁)))))
-- --                       (eq₃ n f g))
-- --     ∙∙ cong (Iso.fun (fst (Hopfβ-Iso n g)))
-- --                    (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst g))} _ _
-- --                               (Y n f g)
-- --                               ((cong (suc ∘ suc ∘ suc) (+-suc n n)))
-- --                               (Hopfβ n g))
-- --     ∙∙ hompres· (_ , snd (Hopfβ-Iso n g)) (Hopfβ n g) (Y n f g)
-- --     ∙∙ cong (Y n f g ℤ[ ℤ , ℤGroup .snd ]·_) (d-β n g)
-- --     ∙∙ rUnitℤ·ℤ (Y n f g)


-- -- {-
-- --   q-α : coHomFun _ q α∨ ≡ Hopfα n (·Π f g)
-- --   q-α with n
-- --   ... | zero = ?
-- --   ... | (suc n) = ?
-- --     where
-- --     helpMe! : Iso.fun (fst (Hopfα-Iso _ (·Π f g))) (Hopfα n (·Π f g))
-- --             ≡ Iso.fun (fst (Hopfα-Iso _ (·Π f g))) (coHomFun _ q α∨)
-- --     helpMe! = {!!}

-- --   q-βₗ : coHomFun _ q βₗ ≡ {!(Hopfβ n ?)!}
-- --   q-βₗ = {!!}

-- --   q-βᵣ : coHomFun _ q βᵣ ≡ {!!}
-- --   q-βᵣ = {!!} -}
    
-- -- --     helpi : {!(f : ? →∙ ?) (HopfInvariantPush n (fst f) → ?)!}
-- -- --     helpi = {!!}

-- -- -- lal : {!!}
-- -- -- lal = {!!}

-- -- -- isHomHopf : ∀ n → (x y : ∥ S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n) ∥₂)
-- -- --                 → Hopfie (x ·π y) ≡ Hopfie x + Hopfie y
-- -- -- isHomHopf n =
-- -- --   sElim2 (λ _ _ → isOfHLevelPath 2 isSetℤ _ _)
-- -- --     λ f g → (λ i → Iso.fun (fst (Hopfβ-Iso n (·Π f g))) (subber n (·Π f g) (⌣-α n (·Π f g))))
-- -- --            ∙ cong (Iso.fun (fst ((Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))))
-- -- --                   {!!}
-- -- --           ∙∙ IsGroupHom.pres· (((Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n))))) .snd)
-- -- --                 (invEq (fst (GroupEquiv1 n f)) (subber n f (⌣-α n f)))
-- -- --                 (invEq (fst (GroupEquiv1 n g)) (subber n g (⌣-α n g))) 
-- -- --           ∙∙ λ i → Iso.fun (fst (Hopfβ-Iso n f)) (subber n f (⌣-α n f))
-- -- --                   + Iso.fun (fst (Hopfβ-Iso n g)) (subber n g (⌣-α n g))
-- -- --   where
-- -- --   cool : (f g : _) → Iso.fun (fst (Hopfβ-Iso n (·Π f g))) (subber n (·Π f g) (⌣-α n f))
-- -- --                    ≡ Iso.fun (fst (Hopfβ-Iso n f)) (subber n f (⌣-α n f))
-- -- --   cool f g = {!!}
