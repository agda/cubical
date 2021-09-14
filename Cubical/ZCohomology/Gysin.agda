{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Gysin where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

open import Cubical.Functions.Embedding

open import Cubical.Data.Fin

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
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


S³+' : S₊ 3 → S₊ 3 → S₊ 3
S³+' north y = y
S³+' south y = y
S³+' (merid a i) north = (merid a ∙ sym (merid north)) i
S³+' (merid a i) south = (sym (merid north) ∙ merid a) i
S³+' (merid north i) (merid b j) = hcomp (λ k → λ { (i = i0) → merid b j
                                                   ; (i = i1) → merid b j
                                                   ; (j = i0) → rCancel (merid north) (~ k) i
                                                   ; (j = i1) → lCancel (merid north) (~ k) i})
                                         (merid b j)
S³+' (merid south i) (merid b j) = hcomp (λ k → λ { (i = i0) → merid b j
                                                   ; (i = i1) → merid b j
                                                   ; (j = i0) → (merid (merid base k) ∙ sym (merid north)) i
                                                   ; (j = i1) → (sym (merid north) ∙ merid (merid base k)) i})
                                          (hcomp (λ k → λ { (i = i0) → merid b j
                                                   ; (i = i1) → merid b j
                                                   ; (j = i0) → rCancel (merid north) (~ k) i
                                                   ; (j = i1) → lCancel (merid north) (~ k) i})
                                                  (merid b j))
S³+' (merid (merid a j) i) (merid b ik) = {!!}

S³+ : join S¹ S¹ → join S¹ S¹ → S₊ 3
S³+ (inl x) y = north
S³+ (inr x) y = north
S³+ (push a b i) (inl x) = north
S³+ (push a b i) (inr x) = north
S³+ (push a b i) (push c d j) =
  hcomp (λ k → λ { (i = i0) → north
                  ; (i  = i1) → north
                  ; (j = i0) → rCancel (merid north) k i
                  ; (j = i1) → rCancel (merid north) k i})
        ((merid ((merid ((a * c) * (b * c)) ∙ sym (merid base)) j) ∙ sym (merid north)) i)

rUnitS : (x : join S¹ S¹) → S³+ x (inl base) ≡ north
rUnitS (inl x) = refl
rUnitS (inr x) = refl
rUnitS (push a b i) = refl



-- sss : ∥ typ ((Ω^ 3) (S₊∙ 2)) ∥₂ → ∥ typ ((Ω^ 4) (S₊∙ 3)) ∥₂
-- sss = sMap (Ω→ (Ω→ (Ω→ ((λ x → merid x ∙ sym (merid north)) , (rCancel _)))) .fst)

-- sss' : typ ((Ω^ 3) (S₊∙ 2)) → typ ((Ω^ 4) (S₊∙ 3))
-- sss' x i j k l =
--   hcomp (λ r → λ { (i = i0) → rCancel (merid north) r l
--                   ; (i = i1) → rCancel (merid north) r l
--                   ; (j = i0) → rCancel (merid north) r l
--                   ; (j = i1) → rCancel (merid north) r l
--                   ; (k = i0) → rCancel (merid north) r l
--                   ; (k = i1) → rCancel (merid north) r l
--                   ; (l = i0) → north
--                   ; (l = i1) → north})
--         ((merid (x i j k) ∙ sym (merid north)) l)


-- sss≡ : (x : _) → sss' x ≡ sym (sss' x)
-- sss≡ x w i j k l =
--   hcomp ((λ r → λ { (i = i0) → rCancel (merid north) r l
--                   ; (i = i1) → rCancel (merid north) r l
--                   ; (j = i0) → rCancel (merid north) r l
--                   ; (j = i1) → rCancel (merid north) r l
--                   ; (k = i0) → rCancel (merid north) r l
--                   ; (k = i1) → rCancel (merid north) r l
--                   ; (l = i0) → north
--                   ; (l = i1) → north}))
--         (hcomp ((λ r → λ { (i = i0) → symDistr (merid (x i j k)) (sym (merid north)) (~ r) (~ l)
--                   ; (i = i1) → symDistr (merid (x i j k)) (sym (merid north)) (~ r) (~ l)
--                   ; (j = i0) → symDistr (merid (x i j k)) (sym (merid north)) (~ r) (~ l)
--                   ; (j = i1) → symDistr (merid (x i j k)) (sym (merid north)) (~ r) (~ l)
--                   ; (k = i0) → symDistr (merid (x i j k)) (sym (merid north)) (~ r) (~ l)
--                   ; (k = i1) → symDistr (merid (x i j k)) (sym (merid north)) (~ r) (~ l)
--                   ; (l = i0) → north
--                   ; (l = i1) → north
--                   ; (w = i0) → symDistr (merid (x i j k)) (sym (merid north)) (~ r) (~ l) -- (merid (x i j k) ∙ sym (merid north)) l
--                   ; (w = i1) → {!!}}))
--                   {!!}) -- ((merid (x i j k) ∙ sym (merid north)) ((~ l ∧ w) ∨ (l ∧ ~ w))))

-- Π₄S³ : Type _
-- Π₄S³ = ∥ typ ((Ω^ 3) (S₊∙ 2)) ∥₂ /' λ f g → sss f ≡ sss g
-- open import Cubical.Homotopy.Freudenthal

-- ll123 : Type _
-- ll123 = Pushout {A = {!!}} {B = {!!}} {!sss ∣ ? ∣₂!} (λ _ → tt)

-- isEquiv→isEquivΩ→ : {!!}
-- isEquiv→isEquivΩ→ = {!!}

-- module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {x y : A} (n : ℕ)
--          (f : A → B) (con : isConnectedFun (suc (suc n)) f) where
--   fib≡ : (b : B) (f1 f2 : fiber f b) → Iso (f1 ≡ f2) (fiber (cong f) (snd f1 ∙ sym (snd f2)))
--   fib≡ = {!!}

--   ll : (p : f x ≡ f y) → isContr (hLevelTrunc (suc n) (fiber (cong f) p))
--   ll  p = subst (isContr ∘ hLevelTrunc (suc n))
--                (isoToPath (fib≡ (f x)  (x , refl) (y , sym p))
--               ∙ cong (fiber (cong f)) (sym (lUnit p)))
--               (isOfHLevelRetractFromIso 0
--                 (invIso (PathIdTruncIso _))
--                   ((isContr→isProp (con (f x)) _ _)
--                   , isProp→isSet (isContr→isProp (con (f x))) _ _ _))

-- conbase : isConnectedFun 4 {A = (S₊ 2)} (σ 1 {A = S₊∙ 2} (sphereConnected 2))
-- conbase = isConnectedσ 1 (sphereConnected 2)

-- conn-cong : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} (n : ℕ)
--          → (f : A → B)
--          → isConnectedFun (suc (suc n)) f
--          → (p : _) → hLevelTrunc (suc n) (fiber (cong f) p)
-- conn-cong {x = x} {y = y} n f con p =
--   trRec (isOfHLevelTrunc (suc n))
--         (λ pp → ∣ (cong fst pp) , (cong sym (rUnit _)
--         ∙∙ cong sym (cong (sym (λ i₁ → f (fst (pp i₁))) ∙_) (rUnit refl))
--         ∙∙ cong sym (PathP→compPathL (cong snd pp))) ∣) l
--   where
--   l : hLevelTrunc (suc n) ((x , refl) ≡ (y , sym p))
--   l = Iso.fun (PathIdTruncIso _) (isContr→isProp (con (f x)) ∣ x , refl ∣ ∣ y , sym p ∣)

-- pr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} (n : ℕ)
--      → (f : A → B)
--      → isConnectedFun (suc (suc n)) f
--      → (p : _) → isProp (hLevelTrunc (suc n) (fiber {A = x ≡ y} (cong f) p))
-- pr {x = x} {y = y} n f co p =
--   trElim2 (λ _ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
--     (uncurry λ p2 P → uncurry λ q Q → trRec (isOfHLevelPath' n (isOfHLevelTrunc (suc n)) _ _)
--       (λ p3 → cong ∣_∣ₕ (ΣPathP ((sym (cong (cong fst) p3)) , {!cong (cong snd) p3!})))
--              (l q p2 Q P))
--     where
--     l : (q p2 : x ≡ y) (Q : cong f q ≡ p) (P : cong f p2 ≡ p)
--       → hLevelTrunc n (ΣPathP (q , λ j i → f (q (~ i ∧ j)))
--                       ≡ ΣPathP (p2 , compPathL→PathP (cong (sym (cong f p2) ∙_) (sym (rUnit refl))
--                                    ∙ sym (rUnit _)
--                                    ∙ cong sym (P ∙ sym Q))))
--     l q p2 Q P =
--       Iso.fun (PathIdTruncIso _) (isContr→isProp
--         (isConnectedPath _
--           (co (f x)) (x , refl) (y , (cong f (sym q))))
--             ∣ ΣPathP (q , λ j i → f (q (~ i ∧ j))) ∣
--               ∣ ΣPathP (p2 , compPathL→PathP (cong (sym (cong f p2) ∙_) (sym (rUnit refl))
--                                             ∙ sym (rUnit _)
--                                             ∙ cong sym (P ∙ sym Q))) ∣)

-- fib-sss : (f : ∥ typ ((Ω^ 4) (S₊∙ 3)) ∥₂) → fiber sss f
-- fib-sss = sElim {!!} λ f → trRec {!!} {!!} (conn-cong {!!}
--   (Ω→ (Ω→ ((λ x → merid x ∙ sym (merid north)) , (rCancel _))) .fst)
--     {!conn-cong _ ? ? ?!}
--     (Ω→
--       (Ω→
--        ((λ x → merid x ∙ (λ i → merid north (~ i))) ,
--         rCancel (merid north)))
--       .snd ∙∙ f ∙∙ sym (Ω→
--       (Ω→
--        ((λ x → merid x ∙ (λ i → merid north (~ i))) ,
--         rCancel (merid north)))
--       .snd)))


-- -- SES→Iso : ∀ {ℓ ℓ'} {L R : Group ℓ-zero}
-- --   → {G : Group ℓ} {H : Group ℓ'}
-- --   → UnitGroup ≡ L
-- --   → UnitGroup ≡ R
-- --   → (lhom : GroupHom L G) (midhom : GroupHom G H) (rhom : GroupHom H R)
-- --   → ((x : _) → isInKer midhom x → isInIm lhom x)
-- --   → ((x : _) → isInKer rhom x → isInIm midhom x)
-- --   → isEquiv (fst midhom)
-- -- SES→Iso {R = R} {G = G} {H = H} =
-- --   J (λ L _ → UnitGroup ≡ R →
-- --       (lhom : GroupHom L G) (midhom : GroupHom G H)
-- --       (rhom : GroupHom H R) →
-- --       ((x : fst G) → isInKer midhom x → isInIm lhom x) →
-- --       ((x : fst H) → isInKer rhom x → isInIm midhom x) →
-- --       isEquiv (fst midhom))
-- --       ((J (λ R _ → (lhom : GroupHom UnitGroup G) (midhom : GroupHom G H)
-- --                    (rhom : GroupHom H R) →
-- --                    ((x : fst G) → isInKer midhom x → isInIm lhom x) →
-- --                    ((x : _) → isInKer rhom x → isInIm midhom x) →
-- --                    isEquiv (fst midhom))
-- --          main))
-- --   where
-- --   main : (lhom : GroupHom UnitGroup G) (midhom : GroupHom G H)
-- --          (rhom : GroupHom H UnitGroup) →
-- --          ((x : fst G) → isInKer midhom x → isInIm lhom x) →
-- --          ((x : fst H) → isInKer rhom x → isInIm midhom x) →
-- --          isEquiv (fst midhom)
-- --   main lhom midhom rhom lexact rexact =
-- --     BijectionIsoToGroupEquiv {G = G} {H = H}
-- --       bijIso' .fst .snd
-- --     where
-- --     bijIso' : BijectionIso G H
-- --     BijectionIso.fun bijIso' = midhom
-- --     BijectionIso.inj bijIso' x inker =
-- --       pRec (GroupStr.is-set (snd G) _ _)
-- --            (λ s → sym (snd s) ∙ IsGroupHom.pres1 (snd lhom)) (lexact _ inker)
-- --     BijectionIso.surj bijIso' x = rexact x refl

-- -- HopfInvariantPush : (n : ℕ)
-- --              → (f : S₊ (3 +ℕ n +ℕ n) → S₊ (2 +ℕ n))
-- --              → Type _
-- -- HopfInvariantPush n f = Pushout (λ _ → tt) f


-- -- Hopfα : (n : ℕ)
-- --      → (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n))
-- --      → coHom (2 +ℕ n) (HopfInvariantPush n (fst f))
-- -- Hopfα n f = ∣ (λ { (inl x) → 0ₖ _
-- --                 ; (inr x) → ∣ x ∣
-- --                 ; (push a i) → help a (~ i)}) ∣₂
-- --   where
-- --   help : (a : S₊ (3 +ℕ n +ℕ n)) → ∣ fst f a ∣ ≡ 0ₖ (2 +ℕ n)
-- --   help = sphereElim _ (λ _ → isOfHLevelPlus' {n = n} (3 +ℕ n)
-- --          (isOfHLevelPath' (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n)) _ _)) (cong ∣_∣ₕ (snd f))

-- -- Hopfβ : (n : ℕ)
-- --      → (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n))
-- --      → coHom (4 +ℕ (n +ℕ n)) (HopfInvariantPush n (fst f))
-- -- Hopfβ n f = fst (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n)) ∣ ∣_∣ ∣₂

-- -- module _ (n : ℕ) (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n)) where
-- --   module M = MV _ _ _ (λ _ → tt) (fst f)
-- --   ¬lem : (n m : ℕ) → ¬ suc (suc (m +ℕ n)) ≡ suc n
-- --   ¬lem zero zero p = snotz (cong predℕ p)
-- --   ¬lem (suc n) zero p = ¬lem n zero (cong predℕ p)
-- --   ¬lem zero (suc m) p = snotz (cong predℕ p)
-- --   ¬lem (suc n) (suc m) p =
-- --     ¬lem n (suc m) (cong (suc ∘ suc )
-- --       (sym (+-suc m n)) ∙ (cong predℕ p))

-- --   GroupEquiv1 :
-- --     GroupEquiv
-- --       (coHomGr (3 +ℕ n +ℕ n) (fst (S₊∙ (3 +ℕ n +ℕ n))))
-- --       ((coHomGr (suc (3 +ℕ n +ℕ n)) (Pushout (λ _ → tt) (fst f))))
-- --   fst (fst GroupEquiv1) = (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n)) .fst
-- --   snd (fst GroupEquiv1) =
-- --     SES→Iso
-- --       (GroupPath _ _ .fst
-- --         (invGroupEquiv (isContr→≃Unit
-- --           (isOfHLevelΣ 0
-- --             (isOfHLevelRetractFromIso 0 (fst (Hⁿ-Unit≅0 _)) isContrUnit)
-- --             λ _ → isOfHLevelRetractFromIso 0
-- --                (fst (Hⁿ-Sᵐ≅0 _ _ (¬lem n n))) isContrUnit)
-- --                        , makeIsGroupHom λ _ _ → refl)))
-- --       (GroupPath _ _ .fst
-- --         (invGroupEquiv
-- --           (isContr→≃Unit
-- --             (isContrΣ
-- --               (isOfHLevelRetractFromIso 0 (fst (Hⁿ-Unit≅0 _))
-- --                 isContrUnit)
-- --                λ _ → isOfHLevelRetractFromIso 0
-- --                (fst (Hⁿ-Sᵐ≅0 _ _  (¬lem n (suc n)))) isContrUnit)
-- --          , makeIsGroupHom λ _ _ → refl)))
-- --         (M.Δ (3 +ℕ n +ℕ n))
-- --         (M.d (3 +ℕ n +ℕ n))
-- --         (M.i (4 +ℕ n +ℕ n))
-- --         (M.Ker-d⊂Im-Δ _)
-- --         (M.Ker-i⊂Im-d _)
-- --   snd GroupEquiv1 = (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n)) .snd

-- --   Hopfβ-Iso : GroupIso ((coHomGr (suc (3 +ℕ n +ℕ n)) (Pushout (λ _ → tt) (fst f)))) ℤGroup
-- --   Hopfβ-Iso = compGroupIso (GroupEquiv→GroupIso (invGroupEquiv GroupEquiv1)) (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n))))

-- -- h33 : (n : ℕ) → Iso.inv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) 1 ≡ ∣ ∣_∣ ∣₂
-- -- h33 zero = Iso.leftInv (fst (Hⁿ-Sⁿ≅ℤ (suc zero))) _
-- -- h33 (suc n) = (λ i → Iso.inv
-- --     (fst
-- --      (suspensionAx-Sn (suc n) (suc n))) (h33 n i))
-- --      ∙ cong ∣_∣₂ (funExt λ { north → refl
-- --                           ; south → cong ∣_∣ₕ (merid north)
-- --                           ; (merid a i) j → ∣ compPath-filler (merid a) (sym (merid north)) (~ j) i ∣})

-- -- d-β : (n : ℕ) (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n))
-- --   → Iso.fun (fst (Hopfβ-Iso n f)) (Hopfβ n f) ≡ 1
-- -- d-β n f = sym (cong (Iso.fun (fst (Hopfβ-Iso n f))) h) ∙ Iso.rightInv (fst (Hopfβ-Iso n f)) (pos 1)
-- --   where
-- --   h : Iso.inv (fst (Hopfβ-Iso n f)) (pos 1) ≡ Hopfβ n f
-- --   h = (λ i → fst (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n))
-- --                (h33 _ i))
-- --     ∙ cong ∣_∣₂ (funExt (λ { (inl x) → refl
-- --                           ; (inr x) → refl
-- --                           ; (push a i) → refl}))

-- -- module _ (n : ℕ) (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n)) where
-- --   2+n = 2 +ℕ n
-- --   H = HopfInvariantPush n (fst f)

-- --   ff : coHom 2+n H → coHom 2+n (S₊ (suc (suc n)))
-- --   ff = sMap (_∘ inr)

-- --   grHom : IsGroupHom (snd (coHomGr 2+n H)) ff (snd (coHomGr 2+n (S₊ (suc (suc n))))) 
-- --   grHom =
-- --     makeIsGroupHom
-- --       (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
-- --         λ f g → refl)

-- --   h' : (g : (S₊ (suc (suc n)) → coHomK 2+n)) → H → coHomK (2 +ℕ n)
-- --   h' g (inl x) = 0ₖ _
-- --   h' g (inr x) = g x -ₖ g north
-- --   h' g (push a i) = h23 a i
-- --     where
-- --     h23 : (a : S₊ (suc (suc (suc (n +ℕ n))))) → 0ₖ (suc (suc n)) ≡ g (fst f a) -ₖ g north
-- --     h23 = sphereElim _ (λ x → isOfHLevelPlus' {n = n} (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n) _ _))
-- --                        (sym (rCancelₖ _ (g north)) ∙ cong (λ x → g x -ₖ g north) (sym (snd f)))

-- --   ff⁻ : coHom 2+n (S₊ (suc (suc n))) → coHom 2+n H
-- --   ff⁻ = sMap h'

-- --   h23 : (x : _) → ∥ x ≡ 0ₖ (suc (suc n)) ∥
-- --   h23 = coHomK-elim _ (λ _ → isProp→isOfHLevelSuc (suc n) squash) ∣ refl ∣

-- --   h : Iso (coHom (2 +ℕ n) (HopfInvariantPush n (fst f))) (coHom (2 +ℕ n) ((S₊ (suc (suc n)))))
-- --   Iso.fun h = ff
-- --   Iso.inv h = ff⁻
-- --   Iso.rightInv h =
-- --     sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- --       λ g → pRec (squash₂ _ _)
-- --                   (λ p → cong ∣_∣₂ (funExt λ x → cong (g x +ₖ_) (cong (-ₖ_) p) ∙ rUnitₖ _ (g x)))
-- --                   (h23 (g north))
-- --   Iso.leftInv h =
-- --     sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- --           λ g → pRec (squash₂ _ _)
-- --                  (pRec (isPropΠ (λ _ → squash₂ _ _))
-- --                   (λ gn gtt →
-- --                    trRec (isProp→isOfHLevelSuc n (squash₂ _ _))
-- --                      (λ r → cong ∣_∣₂ (funExt λ {
-- --                                    (inl x) → sym gtt
-- --                                  ; (inr x) → (λ i → g (inr x) -ₖ gn i) ∙ rUnitₖ _ (g (inr x))
-- --                                  ; (push a i)
-- --                                    → sphereElim _
-- --                                         {A = λ a → PathP (λ i → h' (λ x → g (inr x)) (push a i) ≡ g (push a i))
-- --                                                        (sym gtt)
-- --                                                        ((λ i → g (inr (fst f a)) -ₖ gn i) ∙ rUnitₖ _ (g (inr (fst f a))))}
-- --                                         (λ _ → isOfHLevelPathP' (suc (suc (suc (n +ℕ n))))
-- --                                                  (isOfHLevelPath (suc (suc (suc (suc (n +ℕ n)))))
-- --                                                   (isOfHLevelPlus' {n = n} (suc (suc (suc (suc n))))
-- --                                                    (isOfHLevelTrunc (suc (suc (suc (suc n)))))) _ _) _ _)
-- --                                         r a i}))
-- --                                 (l g gtt gn))
-- --                         (h23 (g (inr north))))
-- --                       (h23 (g (inl tt)))
-- --     where
-- --     l : (g : HopfInvariantPush n (fst f) → coHomK (suc (suc n)))
-- --      → (gtt : g (inl tt) ≡ 0ₖ (suc (suc n)))
-- --      → (gn : g (inr north) ≡ 0ₖ (suc (suc n)))
-- --      → hLevelTrunc (suc n) (PathP (λ i → h' (λ x → g (inr x)) (push north i) ≡ g (push north i))
-- --              (sym gtt) ((λ i → g (inr (fst f north)) -ₖ gn i) ∙ rUnitₖ _ (g (inr (fst f north)))))
-- --     l g gtt gn = isConnectedPathP _ (isConnectedPath _ (isConnectedKn _) _ _) _ _ .fst


-- --   Hopfα-Iso : GroupIso (coHomGr (2 +ℕ n) (HopfInvariantPush n (fst f))) ℤGroup
-- --   Hopfα-Iso =
-- --     compGroupIso
-- --       (h , grHom)
-- --       (Hⁿ-Sⁿ≅ℤ (suc n))

-- -- Hopfα-Iso-α : (n : ℕ) (f : _)
-- --             → Iso.fun (fst (Hopfα-Iso n f)) (Hopfα n f)
-- --             ≡ 1
-- -- Hopfα-Iso-α n f =
-- --     sym (cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ (suc n)))) (h33 n))
-- --   ∙ Iso.rightInv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) (pos 1)
-- --   where
-- --   hz : Iso.fun (h n f) (Hopfα n f) ≡ ∣ ∣_∣ ∣₂
-- --   hz = refl

-- -- _·₀ₕ_ : ∀ {ℓ} {n : ℕ} {A : Type ℓ} → ℤ → coHom n A → coHom n A
-- -- _·₀ₕ_ {n = n} a = sMap λ f x → a ·₀ f x

-- -- HopfInvariant : (n : ℕ)
-- --              → (f : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
-- --              → Type _
-- -- HopfInvariant n f =
-- --   Σ[ x ∈ ℤ ]
-- --     Hopfα n f ⌣ Hopfα n f
-- --     ≡ (x ·₀ₕ subst (λ x → coHom x (HopfInvariantPush n (fst f)))
-- --                    (λ i → suc (suc (suc (+-suc n n (~ i)))))
-- --                    (Hopfβ n f))

-- -- pres- : (e : GroupHom ℤGroup ℤGroup) → (a : ℤ) → fst e (- a) ≡ - fst e a
-- -- pres- e a = +Comm (fst e (- a)) (pos 0)
-- --            ∙ cong (_+ (fst e (- a))) (sym (l (fst e a)) ∙ +Comm (fst e a) (- fst e a))
-- --           ∙∙ sym (+Assoc _ _ _)
-- --           ∙∙ cong (- (fst e a) +_) (pp ∙ l (fst e a))
-- --   where
-- --   l : (a : ℤ) → a + (- a) ≡ 0
-- --   l (pos zero) = refl
-- --   l (pos (suc zero)) = refl
-- --   l (pos (suc (suc n))) = predℤ+negsuc n (pos (suc (suc n))) ∙ l (pos (suc n))
-- --   l (negsuc zero) = refl
-- --   l (negsuc (suc n)) = (cong sucℤ (sucℤ+pos n (negsuc (suc n)))) ∙ l (negsuc n)

-- --   pp : fst e a + fst e (- a) ≡ fst e a + (- fst e a)
-- --   pp = sym (IsGroupHom.pres· (snd e) a (- a))
-- --     ∙∙ cong (fst e) (l a)
-- --     ∙∙ (IsGroupHom.pres1 (snd e)
-- --       ∙ sym (l _))



-- -- GroupHomPres· : (e : GroupHom ℤGroup ℤGroup) → (a b : ℤ) → fst e (a · b) ≡ a · fst e b
-- -- GroupHomPres· e (pos zero) b = IsGroupHom.pres1 (snd e)
-- -- GroupHomPres· e (pos (suc n)) b =
-- --   IsGroupHom.pres· (snd e) b (pos n · b) ∙ cong (fst e b +_) (GroupHomPres· e (pos n) b)
-- -- GroupHomPres· e (negsuc zero) b = pres- e b
-- -- GroupHomPres· e (negsuc (suc n)) b =
-- --               IsGroupHom.pres· (snd e) (- b) (negsuc n · b)
-- --             ∙ cong₂ _+_ (pres- e b) (GroupHomPres· e (negsuc n) b)

-- -- lUnit·₀ₕ : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → (x : coHom n A) → (pos zero) ·₀ₕ x ≡ 0ₕ _
-- -- lUnit·₀ₕ n = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _) λ _ → refl

-- -- minus≡0- : (x : ℤ) → - x ≡ (0 - x)
-- -- minus≡0- x = sym (GroupStr.lid (snd ℤGroup) (- x))

-- -- GroupHomPres·₀ : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
-- --   (e : GroupHom ℤGroup (coHomGr n A))
-- --   → (a b : ℤ)
-- --   → fst e (a · b)
-- --   ≡ (a ·₀ₕ fst e b) 
-- -- GroupHomPres·₀ n e (pos zero) b = IsGroupHom.pres1 (snd e) ∙ sym (lUnit·₀ₕ n (fst e b))
-- -- GroupHomPres·₀ {A = A} n e (pos (suc a)) b =
-- --   IsGroupHom.pres· (snd e) b (pos a · b)
-- --   ∙ (λ i → fst e b +ₕ GroupHomPres·₀ n e (pos a) b i)
-- --   ∙ s (fst e b)
-- --   where
-- --   s : (x : coHom n A) → x +ₕ (pos a ·₀ₕ x) ≡ pos (suc a) ·₀ₕ x
-- --   s = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _) λ _ → refl
-- -- GroupHomPres·₀ n e (negsuc zero) b =
-- --     (cong (fst e) (sym (GroupStr.lid (snd ℤGroup) (- b)))
-- --   ∙ IsGroupHom.presinv (snd e) b)
-- -- GroupHomPres·₀ {A = A} n e (negsuc (suc a)) b =
-- --      IsGroupHom.pres· (snd e) (- b) (negsuc a · b)
-- --   ∙∙ cong₂ _+ₕ_ ((cong (fst e) (sym (GroupStr.lid (snd ℤGroup) (- b)))
-- --                ∙ IsGroupHom.presinv (snd e) b))
-- --                (GroupHomPres·₀ n e (negsuc a) b)
-- --   ∙∙ helper (fst e b)
-- --   where
-- --   helper : (x : coHom n A) → (-ₕ x) +ₕ (negsuc a ·₀ₕ x) ≡ (negsuc (suc a) ·₀ₕ x)
-- --   helper =
-- --     sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- --           λ f → cong ∣_∣₂ (funExt λ x → commₖ n (-ₖ (f x)) (negsuc a ·₀ f x))

-- -- genH : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
-- --      → (e : GroupIso (coHomGr n A)
-- --                  ℤGroup)
-- --      → Σ[ x ∈ coHom n A ]
-- --           ((y : coHom n A)
-- --             → Σ[ a ∈ ℤ ] a ·₀ₕ x ≡ y)
-- -- genH {A = A} n e = (Iso.inv (fst e) 1)
-- --          , λ y → (Iso.fun (fst e) y)
-- --          , (sym (GroupHomPres·₀ n (_ , snd (invGroupIso e)) (Iso.fun (fst e) y) (pos 1))
-- --          ∙∙ cong (Iso.inv (fst e)) (·Comm (Iso.fun (fst e) y) (pos 1))
-- --          ∙∙ Iso.leftInv (fst e) y)

-- -- -- open import Cubical.Data.Sum
-- -- -- open import Cubical.Relation.Nullary
-- -- -- l2 : (n m : ℕ) → Σ[ a ∈ ℕ ] (negsuc n · pos (suc m)) ≡ negsuc a
-- -- -- l2 n zero = n , ·Comm  (negsuc n) (pos 1)
-- -- -- l2 n (suc m) = h _ _ .fst ,
-- -- --      (·Comm (negsuc n) (pos (suc (suc m)))
-- -- --   ∙∙ cong (negsuc n +_) (·Comm (pos (suc m)) (negsuc n) ∙ (l2 n m .snd))
-- -- --   ∙∙ h _ _ .snd)
-- -- --   where
-- -- --   h : (x y : ℕ) → Σ[ a ∈ ℕ ] negsuc x + negsuc y ≡ negsuc a
-- -- --   h zero zero = 1 , refl
-- -- --   h zero (suc y) = (suc (suc y)) , +Comm (negsuc zero) (negsuc (suc y))
-- -- --   h (suc x) zero = (suc (suc x)) , refl
-- -- --   h (suc x) (suc y) = (h (suc (suc x)) y .fst) , (predℤ+negsuc y (negsuc (suc x)) ∙ snd ((h (suc (suc x))) y))

-- -- -- zz : (n x : ℕ) → Σ[ a ∈ ℕ ] ((pos (suc x)) · pos (suc (suc n)) ≡ pos (suc (suc a)))
-- -- -- zz n zero = n , refl
-- -- -- zz n (suc x) = h _ _ (zz n x)
-- -- --   where
-- -- --   h : (x : ℤ) (n : ℕ) → Σ[ a ∈ ℕ ] (x ≡ pos (suc (suc a)))
-- -- --                 → Σ[ a ∈ ℕ ] pos n + x ≡ pos (suc (suc a))
-- -- --   h x n (a , p) = n +ℕ a
-- -- --     , cong (pos n +_) p ∙ cong sucℤ (sucℤ+pos a (pos n))
-- -- --        ∙ sucℤ+pos a (pos (suc n)) ∙ (sym (pos+ (suc (suc n)) a))

-- -- -- lem22 : (n : ℕ) (x : ℤ) → ¬ pos 1 ≡ x · pos (suc (suc n))
-- -- -- lem22 n (pos zero) p = snotz (injPos p)
-- -- -- lem22 n (pos (suc n₁)) p = snotz (injPos (sym (cong predℤ (snd (zz n n₁))) ∙ sym (cong predℤ p)))
-- -- -- lem22 n (negsuc n₁) p = posNotnegsuc _ _ (p ∙ l2 _ _ .snd)


-- -- -- grr : (e : GroupEquiv ℤGroup ℤGroup) (x : ℤ) → (fst (fst e) 1) ≡ x → abs (fst (fst e) 1) ≡ 1
-- -- -- grr e (pos zero) p =
-- -- --   ⊥-rec (snotz (injPos (sym (retEq (fst e) 1)
-- -- --             ∙∙ (cong (fst (fst (invGroupEquiv e))) p)
-- -- --             ∙∙ IsGroupHom.pres1 (snd (invGroupEquiv e)))))
-- -- -- grr e (pos (suc zero)) p = cong abs p
-- -- -- grr e (pos (suc (suc n))) p = ⊥-rec (lem22 _ _ (h ∙ ·Comm (pos (suc (suc n))) (invEq (fst e) 1)))
-- -- --   where

-- -- --   h : pos 1 ≡ _
-- -- --   h = sym (retEq (fst e) 1)
-- -- --     ∙∙ (cong (fst (fst (invGroupEquiv e))) (p ∙ ·Comm 1 (pos (suc (suc n)))))
-- -- --     ∙∙ GroupHomPres· (_ , snd (invGroupEquiv e)) (pos (suc (suc n))) 1
-- -- -- grr e (negsuc zero) p = cong abs p
-- -- -- grr e (negsuc (suc n)) p = ⊥-rec (lem22 _ _ l33)
-- -- --   where
-- -- --   h : fst (fst e) (negsuc zero) ≡ pos (suc (suc n))
-- -- --   h = pres- (_ , snd e) (pos 1) ∙ cong -_ p

-- -- --   compGroup : GroupEquiv ℤGroup ℤGroup
-- -- --   fst compGroup = isoToEquiv (iso -_ -_ -Involutive -Involutive)
-- -- --   snd compGroup = makeIsGroupHom -Dist+

-- -- --   compHom : GroupEquiv ℤGroup ℤGroup
-- -- --   compHom = compGroupEquiv compGroup e

-- -- --   l32 : fst (fst compHom) (pos 1) ≡ pos (suc (suc n))
-- -- --   l32 = h

-- -- --   l33 : pos 1 ≡ invEq (fst compHom) (pos 1) · pos (suc (suc n))
-- -- --   l33 = sym (retEq (fst compHom) (pos 1))
-- -- --      ∙∙ cong (invEq (fst compHom)) l32
-- -- --      ∙∙ (cong (invEq (fst compHom)) (·Comm (pos 1) (pos (suc (suc n))))
-- -- --        ∙ GroupHomPres· (_ , (snd (invGroupEquiv compHom))) (pos (suc (suc n))) (pos 1)
-- -- --        ∙ ·Comm (pos (suc (suc n))) (invEq (fst compHom) (pos 1)))

-- -- -- abs→⊎ : (x : ℤ) (n : ℕ) → abs x ≡ n → (x ≡ pos n) ⊎ (x ≡ - pos n)
-- -- -- abs→⊎ x n = J (λ n _ → (x ≡ pos n) ⊎ (x ≡ - pos n)) (help x)
-- -- --   where
-- -- --   help : (x : ℤ) → (x ≡ pos (abs x)) ⊎ (x ≡ - pos (abs x))
-- -- --   help (pos n) = inl refl
-- -- --   help (negsuc n) = inr refl

-- -- -- JGroupEquiv : ∀ {ℓ ℓ'} {G : Group ℓ} (P : (H : Group ℓ) → GroupEquiv G H → Type ℓ')
-- -- --             → P G idGroupEquiv
-- -- --             → ∀ {H} e → P H e
-- -- -- JGroupEquiv {G = G} P p {H} e =
-- -- --   transport (λ i → P (GroupPath G H .fst e i)
-- -- --     (transp (λ j → GroupEquiv G (GroupPath G H .fst e (i ∨ ~ j))) i e))
-- -- --       (subst (P G) (sym l) p)
-- -- --   where
-- -- --   l : (transp (λ j → GroupEquiv G (GroupPath G H .fst e (~ j))) i0 e) ≡ idGroupEquiv
-- -- --   l = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
-- -- --        (Σ≡Prop (λ _ → isPropIsEquiv _)
-- -- --          (funExt λ x → (λ i → fst (fst (fst e .snd .equiv-proof
-- -- --                           (transportRefl (fst (fst e) (transportRefl x i)) i))))
-- -- --                          ∙ retEq (fst e) x))

-- -- -- sesIsoPresGen :
-- -- --    ∀ (G : Group ℓ-zero)
-- -- --   → (iso : GroupEquiv ℤGroup G)
-- -- --   → (H : Group ℓ-zero)
-- -- --   → (iso2 : GroupEquiv ℤGroup H)
-- -- --   → (e : fst G)
-- -- --   → invEq (fst iso) e ≡ 1
-- -- --   → (hom : GroupEquiv G H)
-- -- --   → abs (invEq (fst iso2) (fst (fst hom) e)) ≡ 1
-- -- -- sesIsoPresGen G = JGroupEquiv (λ G iso →
-- -- --     (H : Group ℓ-zero)
-- -- --     (iso2 : GroupEquiv ℤGroup H)
-- -- --   → (e : fst G)
-- -- --   → invEq (fst iso) e ≡ 1
-- -- --   → (hom : GroupEquiv G H)
-- -- --   → abs (invEq (fst iso2) (fst (fst hom) e)) ≡ 1)
-- -- --   λ H → JGroupEquiv (λ H iso2 → (e : ℤ) → e ≡ pos 1 →
-- -- --       (hom : GroupEquiv ℤGroup H) →
-- -- --       abs (invEq (fst iso2) (fst (fst hom) e)) ≡ 1)
-- -- --       λ e p hom → cong (abs ∘ (fst (fst hom))) p ∙ autoPres1 hom
-- -- --   where
-- -- --   autoPres1 : (e : GroupEquiv ℤGroup ℤGroup)
-- -- --            → abs (fst (fst e) 1) ≡ 1
-- -- --   autoPres1 e = grr e _ refl

-- -- -- characFunSpaceS¹ : ∀ {ℓ} {A : Type ℓ} →
-- -- --   Iso (S₊ 1 → A) (Σ[ x ∈ A ] x ≡ x)
-- -- -- Iso.fun characFunSpaceS¹ f = f base , cong f loop
-- -- -- Iso.inv characFunSpaceS¹ (x , p) base = x
-- -- -- Iso.inv characFunSpaceS¹ (x , p) (loop i) = p i
-- -- -- Iso.rightInv characFunSpaceS¹ _ = refl
-- -- -- Iso.leftInv characFunSpaceS¹ f = funExt λ { base → refl ; (loop i) → refl}

-- -- -- characFunSpace : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
-- -- --                → Iso (join A B → C)
-- -- --                       (Σ[ f ∈ (A → C) ] Σ[ g ∈ (B → C) ]
-- -- --                         ((a : A) (b : B) → f a ≡ g b))
-- -- -- Iso.fun characFunSpace f = (f ∘ inl) , ((f ∘ inr) , (λ a b → cong f (push a b)))
-- -- -- Iso.inv characFunSpace (f , g , p) (inl x) = f x
-- -- -- Iso.inv characFunSpace (f , g , p) (inr x) = g x
-- -- -- Iso.inv characFunSpace (f , g , p) (push a b i) = p a b i
-- -- -- Iso.rightInv characFunSpace (f , g , p) = refl
-- -- -- Iso.leftInv characFunSpace f =
-- -- --   funExt λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}

-- -- -- coHomS¹-ish : (n : ℕ) → Type _
-- -- -- coHomS¹-ish n = hLevelTrunc 3 (S₊ 1 → coHomK (3 +ℕ n))

-- -- -- fib : (n : ℕ) → coHomS¹-ish n → Type _
-- -- -- fib n x =
-- -- --   trRec {B = TypeOfHLevel ℓ-zero 2} (isOfHLevelTypeOfHLevel 2)
-- -- --         (λ f → ∥ (Σ[ g ∈ (S₊ 3 → coHomK (3 +ℕ n)) ]
-- -- --           ((a : S₊ 1) (b : S₊ 3) → f a ≡ g b)) ∥₂ , squash₂) x .fst

-- -- -- contrFstΣ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
-- -- --           → (e : isContr A)
-- -- --           → Iso (Σ A B) (B (fst e))
-- -- -- Iso.fun (contrFstΣ {B = B} e) (a , b) = subst B (sym (snd e a)) b
-- -- -- Iso.inv (contrFstΣ {B = B} e) b = (fst e) , b
-- -- -- Iso.rightInv (contrFstΣ {B = B} e) b = cong (λ x → subst B x b) h ∙ transportRefl b
-- -- --   where
-- -- --   h : sym (snd e (fst e)) ≡ refl
-- -- --   h = isProp→isSet (isContr→isProp e) _ _ _ _
-- -- -- Iso.leftInv (contrFstΣ {B = B} e) b =
-- -- --   ΣPathP ((snd e (fst b))
-- -- --         , (λ j → transp (λ i → B (snd e (fst b) (~ i ∨ j))) j (snd b)))

-- -- -- Iso1 : (n : ℕ) → Iso (coHom (3 +ℕ n) (join S¹ (S₊ 3))) ∥ Σ (coHomS¹-ish n) (fib n) ∥₂
-- -- -- Iso1 n = compIso (setTruncIso characFunSpace) Iso2
-- -- --   where
-- -- --   Iso2 : Iso _ ∥ Σ (coHomS¹-ish n) (fib n) ∥₂
-- -- --   Iso.fun Iso2 = sMap λ F → ∣ fst F ∣ , ∣ (fst (snd F)) , (snd (snd F)) ∣₂
-- -- --   Iso.inv Iso2 =
-- -- --     sRec squash₂
-- -- --       (uncurry (trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelSuc 2 squash₂)
-- -- --         λ f → sRec squash₂ λ p → ∣ f , p ∣₂))
-- -- --   Iso.rightInv Iso2 =
-- -- --     sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- -- --       (uncurry (trElim (λ _ → isOfHLevelΠ 3 λ _ → isProp→isOfHLevelSuc 2 (squash₂ _ _))
-- -- --         λ f → sElim (λ _ → isOfHLevelPath 2 squash₂ _ _) λ _ → refl ))
-- -- --   Iso.leftInv Iso2 = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _) λ _ → refl

-- -- -- isContrcoHomS¹-ish : (n : ℕ) → isContr (coHomS¹-ish n)
-- -- -- isContrcoHomS¹-ish n = isOfHLevelRetractFromIso 0 (mapCompIso characFunSpaceS¹) isContrEnd
-- -- --   where
-- -- --   isContrEnd : isContr (hLevelTrunc 3 (Σ[ x ∈ coHomK (3 +ℕ n) ] x ≡ x))
-- -- --   fst isContrEnd = ∣ 0ₖ _ , refl ∣
-- -- --   snd isContrEnd =
-- -- --     trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
-- -- --            (uncurry (coHomK-elim _
-- -- --              (λ _ → isOfHLevelΠ (suc (suc (suc n)))
-- -- --                λ _ → isOfHLevelPlus' {n = n} 3 (isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _))
-- -- --                (λ p → (trRec (isOfHLevelPlus' {n = n} 3 (isOfHLevelTrunc 3) _ _)
-- -- --                       (λ p i → ∣ (0ₖ (3 +ℕ n) , p i) ∣)
-- -- --                  (Iso.fun (PathIdTruncIso _)
-- -- --                    (isContr→isProp
-- -- --                      (isConnectedPath _ (isConnectedKn (2 +ℕ n)) (0ₖ _) (0ₖ _)) ∣ refl ∣ ∣ p ∣))))))

-- -- -- Iso2' : (n : ℕ) → Iso (∥ Σ (coHomS¹-ish n) (fib n) ∥₂) (fib n ∣ (λ _ → 0ₖ _) ∣)
-- -- -- Iso2' n = compIso (setTruncIso (contrFstΣ centerChange))
-- -- --                  (setTruncIdempotentIso squash₂)
-- -- --   where
-- -- --   centerChange : isContr (coHomS¹-ish n)
-- -- --   fst centerChange = ∣ (λ _ → 0ₖ _) ∣
-- -- --   snd centerChange y = isContr→isProp (isContrcoHomS¹-ish n) _ _

-- -- -- open import Cubical.Foundations.Equiv.HalfAdjoint
-- -- -- open import Cubical.Relation.Nullary
-- -- -- ll5 : (n : ℕ) → ¬ (n ≡ 2) → isContr (fib n ∣ (λ _ → 0ₖ _) ∣)
-- -- -- ll5 n p =
-- -- --   isOfHLevelRetractFromIso 0
-- -- --       (compIso
-- -- --         (setTruncIso
-- -- --           (compIso (Σ-cong-iso-snd λ f →
-- -- --             (compIso characFunSpaceS¹ (invIso (Σ-cong-iso-fst (iso funExt⁻ funExt (λ _ → refl) λ _ → refl)))))
-- -- --             (compIso ΣΣ (contrFstΣ (isContrSingl _)))))
-- -- --         (compIso (setTruncIso (iso funExt⁻ funExt (λ _ → refl) λ _ → refl))
-- -- --                  (compIso (setTruncIso (codomainIso (congIso (invIso (Iso-Kn-ΩKn+1 _)))))
-- -- --                           ((compIso (invIso (fst (coHom≅coHomΩ _ (S₊ _))))
-- -- --                                     (fst (Hⁿ-Sᵐ≅0 n 2 p)))))))
-- -- --       isContrUnit

-- -- -- record ExactSeqℤ {ℓ : Level} (G : ℤ → Group ℓ) : Type ℓ where
-- -- --   field
-- -- --     maps : ∀ n → GroupHom (G n) (G (sucℤ n))
-- -- --     im⊂ker : ∀ n → ∀ g → isInIm (maps n) g → isInKer (maps (sucℤ n)) g
-- -- --     ker⊂im : ∀ n → ∀ g → isInKer (maps (sucℤ n)) g → isInIm (maps n) g

-- -- -- record ExactSeqℕ {ℓ : Level} (G : ℕ → Group ℓ) : Type ℓ where
-- -- --   field
-- -- --     maps : ∀ n → GroupHom (G n) (G (suc n))
-- -- --     im⊂ker : ∀ n → ∀ g → isInIm (maps n) g → isInKer (maps (suc n)) g
-- -- --     ker⊂im : ∀ n → ∀ g → isInKer (maps (suc n)) g → isInIm (maps n) g


-- -- -- module _ {ℓ : Level} {A : Pointed ℓ} {n : ℕ}
-- -- --   where
-- -- --   funTyp : Type _
-- -- --   funTyp = A →∙ coHomK-ptd n

-- -- --   _++_ : funTyp → funTyp → funTyp
-- -- --   fst (f ++ g) x = fst f x +ₖ fst g x
-- -- --   snd (f ++ g) = cong₂ _+ₖ_ (snd f) (snd g) ∙ rUnitₖ _ (0ₖ _)

-- -- -- addAgree : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (x y : funTyp {A = A} {n = n})
-- -- --          → Path (fst (coHomRedGrDir n A))
-- -- --                  ∣ x ++ y ∣₂
-- -- --                  (∣ x ∣₂ +ₕ∙ ∣ y ∣₂)
-- -- -- addAgree {A = A} zero f g =
-- -- --   cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _) refl)
-- -- -- addAgree {A = A} (suc zero) f g =
-- -- --   cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _) refl)
-- -- -- addAgree {A = A} (suc (suc n)) f g =
-- -- --   cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _) refl)

-- -- -- ss : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Type ℓ''}
-- -- --      → isHomogeneous B
-- -- --      → (x y : (A →∙ B)) (f : C → x ≡ y)
-- -- --      → isEquiv (cong fst ∘ f)
-- -- --      → isEquiv f
-- -- -- ss homb x y f e =
-- -- --   isoToIsEquiv
-- -- --    (iso _
-- -- --         (λ p → invEq (_ , e) (cong fst p))
-- -- --         (λ p → →∙Homogeneous≡Path homb _ _ (secEq (_ , e) (cong fst p)))
-- -- --         (retEq (_ , e)))

-- -- -- Whitehead : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
-- -- --           → (f : A → B)
-- -- --           → isEmbedding f
-- -- --           → (∀ (b : B) → ∃[ a ∈ A ] f a ≡ b)
-- -- --           → isEquiv f
-- -- -- equiv-proof (Whitehead f emb p) b =
-- -- --   pRec isPropIsContr
-- -- --     (λ fib → fib , isEmbedding→hasPropFibers emb b fib)
-- -- --     (p b)

-- -- -- Int-ind : ∀ {ℓ} (P : ℤ → Type ℓ)
-- -- --         → P (pos zero) → P (pos 1)
-- -- --         → P (negsuc zero)
-- -- --         → ((x y : ℤ) → P x → P y → P (x + y)) → (x : ℤ) → P x
-- -- -- Int-ind P z one min ind (pos zero) = z
-- -- -- Int-ind P z one min ind (pos (suc zero)) = one
-- -- -- Int-ind P z one min ind (pos (suc (suc n))) =
-- -- --   ind (pos (suc n)) 1  (Int-ind P z one min ind (pos (suc n))) one
-- -- -- Int-ind P z one min ind (negsuc zero) = min
-- -- -- Int-ind P z one min ind (negsuc (suc n)) =
-- -- --   ind (negsuc n) (negsuc zero) (Int-ind P z one min ind (negsuc n)) min

-- -- -- genFunSpace : (n : ℕ) → S₊∙ n →∙ coHomK-ptd n
-- -- -- fst (genFunSpace zero) false = 1
-- -- -- fst (genFunSpace zero) true = 0
-- -- -- snd (genFunSpace zero) = refl
-- -- -- fst (genFunSpace (suc n)) = ∣_∣
-- -- -- snd (genFunSpace (suc zero)) = refl
-- -- -- snd (genFunSpace (suc (suc n))) = refl

-- -- -- module _ where
-- -- --   open import Cubical.Algebra.Monoid
-- -- --   open import Cubical.Algebra.Semigroup
-- -- --   open GroupStr
-- -- --   open IsGroup
-- -- --   open IsMonoid
-- -- --   open IsSemigroup
-- -- --   πS : (n : ℕ) → Group ℓ-zero
-- -- --   fst (πS n) = S₊∙ n →∙ coHomK-ptd n
-- -- --   1g (snd (πS n)) = (λ _ → 0ₖ n) , refl
-- -- --   GroupStr._·_ (snd (πS n)) =
-- -- --     λ f g → (λ x → fst f x +ₖ fst g x)
-- -- --             , cong₂ _+ₖ_ (snd f) (snd g) ∙ rUnitₖ n (0ₖ n)
-- -- --   inv (snd (πS n)) f = (λ x → -ₖ fst f x) , cong -ₖ_ (snd f) ∙ -0ₖ {n = n}
-- -- --   is-set (isSemigroup (isMonoid (isGroup (snd (πS zero))))) =
-- -- --     isOfHLevelΣ 2 (isSetΠ (λ _ → isSetℤ))
-- -- --       λ _ → isOfHLevelPath 2 isSetℤ _ _
-- -- --   is-set (isSemigroup (isMonoid (isGroup (snd (πS (suc n)))))) = isOfHLevel↑∙' 0 n
-- -- --   IsSemigroup.assoc (isSemigroup (isMonoid (isGroup (snd (πS n))))) x y z =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ w → assocₖ n (fst x w) (fst y w) (fst z w))
-- -- --   fst (identity (isMonoid (isGroup (snd (πS n)))) (f , p)) =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ x → rUnitₖ n (f x))
-- -- --   snd (identity (isMonoid (isGroup (snd (πS n)))) (f , p)) =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ x → lUnitₖ n (f x))
-- -- --   fst (inverse (isGroup (snd (πS n))) (f , p)) =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ x → rCancelₖ n (f x))
-- -- --   snd (inverse (isGroup (snd (πS n))) (f , p)) =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ x → lCancelₖ n (f x))

-- -- --   isSetπS : (n : ℕ) → isSet (S₊∙ n →∙ coHomK-ptd n)
-- -- --   isSetπS = λ n → is-set (snd (πS n))

-- -- -- K : (n : ℕ) → GroupIso (coHomRedGrDir n (S₊∙ n)) (πS n)
-- -- -- fst (K n) = setTruncIdempotentIso (isSetπS n)
-- -- -- snd (K zero) =
-- -- --   makeIsGroupHom
-- -- --     (sElim2 (λ _ _ → isOfHLevelPath 2 (isSetπS 0) _ _)
-- -- --       λ f g → →∙Homogeneous≡ (isHomogeneousKn 0) refl)
-- -- -- snd (K (suc zero)) =
-- -- --     makeIsGroupHom
-- -- --     (sElim2 (λ _ _ → isOfHLevelPath 2 (isSetπS 1) _ _)
-- -- --       λ f g → →∙Homogeneous≡ (isHomogeneousKn 1) refl)
-- -- -- snd (K (suc (suc n))) =
-- -- --     makeIsGroupHom
-- -- --     (sElim2 (λ _ _ → isOfHLevelPath 2 (isSetπS _) _ _)
-- -- --       λ f g → →∙Homogeneous≡ (isHomogeneousKn _) refl)

-- -- -- t : ∀ {ℓ} {A : Pointed ℓ} → Iso ((Bool , true) →∙ A) (typ A)
-- -- -- Iso.fun t f = fst f false
-- -- -- fst (Iso.inv t a) false = a
-- -- -- fst (Iso.inv (t {A = A}) a) true = pt A
-- -- -- snd (Iso.inv t a) = refl
-- -- -- Iso.rightInv t a = refl
-- -- -- Iso.leftInv t (f , p) =
-- -- --   ΣPathP ((funExt (λ { false → refl ; true → sym p})) , λ i j → p (~ i ∨ j))

-- -- -- S1' : (n : ℕ) → GroupIso (πS n) ℤGroup
-- -- -- fst (S1' zero) = t
-- -- -- snd (S1' zero) = makeIsGroupHom λ _ _ → refl
-- -- -- S1' (suc n) =
-- -- --   compGroupIso
-- -- --     (invGroupIso (K (suc n)))
-- -- --     (compGroupIso
-- -- --       (GroupEquiv→GroupIso (coHomGr≅coHomRedGr n (S₊∙ (suc n))))
-- -- --       (Hⁿ-Sⁿ≅ℤ n))

-- -- -- S1 : (n : ℕ) → Iso (S₊∙ (suc n) →∙ coHomK-ptd (suc n)) ℤ
-- -- -- S1 n = compIso (invIso (setTruncIdempotentIso (isOfHLevel↑∙' 0 n)))
-- -- --                (compIso (equivToIso (fst (coHomGr≅coHomRedGr n (S₊∙ (suc n)))))
-- -- --                (fst (Hⁿ-Sⁿ≅ℤ n)))

-- -- -- connFunSpace : (n i : ℕ) → (x y : S₊∙ n →∙ coHomK-ptd (suc i +' n)) → ∥ x ≡ y ∥
-- -- -- connFunSpace n i f g = Iso.fun PathIdTrunc₀Iso (isContr→isProp (lem n) ∣ f ∣₂ ∣ g ∣₂)
-- -- --   where
-- -- --   open import Cubical.Relation.Nullary
-- -- --   natLem : (n i : ℕ) → ¬ (suc (i +ℕ n) ≡ n)
-- -- --   natLem zero i = snotz
-- -- --   natLem (suc n) i p = natLem n i (sym (+-suc i n) ∙ (cong predℕ p))

-- -- --   lem : (n : ℕ) → isContr ∥ (S₊∙ n →∙ coHomK-ptd (suc i +' n)) ∥₂
-- -- --   fst (lem zero) = 0ₕ∙ (suc i)
-- -- --   snd (lem zero) = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- -- --                          λ f → pRec (squash₂ _ _)
-- -- --                                      (λ id → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn (suc i))
-- -- --                                                (funExt λ { false → sym id ; true → sym (snd f)})))
-- -- --                                      (help (f .fst false))
-- -- --     where
-- -- --     help : (x : coHomK (suc i)) → ∥ x ≡ 0ₖ _ ∥
-- -- --     help = coHomK-elim _ (λ _ → isProp→isOfHLevelSuc i squash) ∣ refl ∣
-- -- --   lem (suc n) =
-- -- --     isOfHLevelRetractFromIso 0
-- -- --       (compIso (equivToIso (fst (coHomGr≅coHomRedGr (suc (i +ℕ n)) (S₊∙ (suc n)))))
-- -- --                (fst (Hⁿ-Sᵐ≅0 (suc (i +ℕ n)) n (natLem n i))))
-- -- --       isContrUnit

-- -- -- S1Pres1 : (n : ℕ) → Iso.fun (fst (S1' (suc n))) (∣_∣ , refl) ≡ pos 1
-- -- -- S1Pres1 zero = refl
-- -- -- S1Pres1 (suc n) = cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n))) (lem n) ∙ S1Pres1 n
-- -- --   where
-- -- --   lem : (n : ℕ) → Iso.fun (fst (suspensionAx-Sn n n)) ∣ ∣_∣ ∣₂ ≡ ∣ ∣_∣ ∣₂
-- -- --   lem zero = cong ∣_∣₂ (funExt λ x → transportRefl (∣ x ∣ +ₖ (0ₖ 1)) ∙ rUnitₖ 1 ∣ x ∣)
-- -- --   lem (suc n) = cong ∣_∣₂
-- -- --     (funExt λ x → (λ i → transportRefl ((ΩKn+1→Kn (suc (suc n))
-- -- --        (transp (λ j → 0ₖ (suc (suc (suc n))) ≡ ∣ merid north (~ j ∧ ~ i) ∣) i
-- -- --         (λ z → ∣ compPath-filler (merid (transportRefl (transportRefl x i) i)) (sym (merid north)) i z
-- -- --            ∣)))) i)
-- -- --     ∙ Iso.leftInv (Iso-Kn-ΩKn+1 (suc (suc n))) ∣ x ∣)

-- -- -- S1Pres1← : (n : ℕ) → Iso.inv (fst (S1' (suc n))) (pos 1) ≡ (∣_∣ , refl)
-- -- -- S1Pres1← n = sym (cong (Iso.inv (fst (S1' (suc n)))) (S1Pres1 n)) ∙ Iso.leftInv (fst (S1' (suc n))) (∣_∣ , refl)

-- -- -- IsoFunSpace : (n : ℕ) → Iso (S₊∙ n →∙ coHomK-ptd n) ℤ
-- -- -- IsoFunSpace n = fst (S1' n)

-- -- -- module g-base where
-- -- --   g : (n : ℕ) (i : ℕ) → coHomK i → (S₊∙ n →∙ coHomK-ptd (i +' n))
-- -- --   fst (g n i x) y = x ⌣ₖ (genFunSpace n) .fst y
-- -- --   snd (g n i x) = cong (x ⌣ₖ_) ((genFunSpace n) .snd) ∙ ⌣ₖ-0ₖ i n x

-- -- --   G : (n : ℕ) (i : ℕ) → coHomK i → (S₊∙ n →∙ coHomK-ptd (n +' i))
-- -- --   fst (G n i x) y = (genFunSpace n) .fst y ⌣ₖ x
-- -- --   snd (G n i x) = cong (_⌣ₖ x) ((genFunSpace n) .snd) ∙ 0ₖ-⌣ₖ n i x

-- -- --   eq1 : (n : ℕ) (i : ℕ) → (S₊∙ n →∙ coHomK-ptd (i +' n)) ≃ (S₊∙ n →∙ coHomK-ptd (i +' n))
-- -- --   eq1 n i = isoToEquiv (iso F F FF FF)
-- -- --     where
-- -- --     lem : (i n : ℕ) → (-ₖ^ i · n) (snd (coHomK-ptd (i +' n))) ≡ 0ₖ _
-- -- --     lem zero zero = refl
-- -- --     lem zero (suc zero) = refl
-- -- --     lem zero (suc (suc n)) = refl
-- -- --     lem (suc zero) zero = refl
-- -- --     lem (suc (suc i)) zero = refl
-- -- --     lem (suc i) (suc n) = refl

-- -- --     F : S₊∙ n →∙ coHomK-ptd (i +' n) → S₊∙ n →∙ coHomK-ptd (i +' n)
-- -- --     fst (F f) x = (-ₖ^ i · n) (fst f x)
-- -- --     snd (F f) = cong (-ₖ^ i · n) (snd f) ∙ lem i n

-- -- --     FF : (x : _) → F (F x) ≡ x
-- -- --     FF x =
-- -- --       →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --         (funExt λ y → -ₖ-gen² i n _ _ (fst x y))

-- -- --   rCancel'' : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → sym p ∙∙ refl ∙∙ p ≡ refl
-- -- --   rCancel'' p = (λ j → (λ i → p (~ i ∨ j)) ∙∙ refl ∙∙ λ i → p (i ∨ j)) ∙ sym (rUnit refl)

-- -- --   transpPres0 : ∀ {k m : ℕ} (p : k ≡ m) → subst coHomK p (0ₖ k) ≡ 0ₖ m
-- -- --   transpPres0 {k = k} = J (λ m p → subst coHomK p (0ₖ k) ≡ 0ₖ m) (transportRefl _)

-- -- --   eq2 : (n : ℕ) (i : ℕ) → (S₊∙ n →∙ coHomK-ptd (n +' i)) ≃ (S₊∙ n →∙ coHomK-ptd (i +' n))
-- -- --   eq2 n i =
-- -- --     isoToEquiv (iso (λ f → (λ x → subst coHomK (+'-comm n i) (fst f x)) ,
-- -- --                     cong (subst coHomK (+'-comm n i)) (snd f) ∙ transpPres0 (+'-comm n i))
-- -- --                     (λ f → (λ x → subst coHomK (sym (+'-comm n i)) (fst f x))
-- -- --                           , (cong (subst coHomK (sym (+'-comm n i))) (snd f) ∙ transpPres0 (sym (+'-comm n i))))
-- -- --                     (λ f → →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ x → transportTransport⁻ _ (f .fst x)))
-- -- --                     λ f → →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ x → transportTransport⁻ _ (f .fst x)))

-- -- --   g≡ : (n : ℕ) (i : ℕ) → g n i ≡ λ x → fst (compEquiv (eq2 n i) (eq1 n i)) ((G n i) x)
-- -- --   g≡ n i = funExt (λ f → →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --              (funExt λ y → gradedComm-⌣ₖ _ _ f (genFunSpace n .fst y)))

-- -- --   glIso3-fun : (n m : ℕ) →
-- -- --     (S₊∙ (suc n) →∙ coHomK-ptd (suc m))
-- -- --         → (S₊ n → coHomK m)
-- -- --   glIso3-fun zero m (f , p) false = ΩKn+1→Kn _ (sym p ∙∙ cong f loop ∙∙ p)
-- -- --   glIso3-fun zero m (f , p) true = 0ₖ _
-- -- --   glIso3-fun (suc n) m (f , p) x =
-- -- --     ΩKn+1→Kn _ (sym p ∙∙ cong f (merid x ∙ sym (merid (ptSn _))) ∙∙ p)

-- -- --   glIso3-fun∙ : (n m : ℕ) → (f : _) → glIso3-fun n m f (ptSn _) ≡ 0ₖ m
-- -- --   glIso3-fun∙ zero m = λ _ → refl
-- -- --   glIso3-fun∙ (suc n) m (f , p) =
-- -- --     cong (ΩKn+1→Kn m) (cong (sym p ∙∙_∙∙ p) (cong (cong f) (rCancel (merid (ptSn _)))))
-- -- --      ∙∙ cong (ΩKn+1→Kn m) (rCancel'' p) 
-- -- --      ∙∙ ΩKn+1→Kn-refl m


-- -- --   glIso3-inv : (n m : ℕ) → (S₊∙ n →∙ coHomK-ptd m) → (S₊∙ (suc n) →∙ coHomK-ptd (suc m))
-- -- --   fst (glIso3-inv zero m (f , p)) base = 0ₖ _
-- -- --   fst (glIso3-inv zero m (f , p)) (loop i) = Kn→ΩKn+1 m (f false) i
-- -- --   snd (glIso3-inv zero m (f , p)) = refl
-- -- --   fst (glIso3-inv (suc n) m (f , p)) north = 0ₖ _
-- -- --   fst (glIso3-inv (suc n) m (f , p)) south = 0ₖ _
-- -- --   fst (glIso3-inv (suc n) m (f , p)) (merid a i) = Kn→ΩKn+1 m (f a) i
-- -- --   snd (glIso3-inv (suc n) m (f , p)) = refl

-- -- --   glIso3 : (n m : ℕ) →
-- -- --     Iso (S₊∙ (suc n) →∙ coHomK-ptd (suc m))
-- -- --         (S₊∙ n →∙ coHomK-ptd m)
-- -- --   Iso.fun (glIso3 n m) f = (glIso3-fun n m f) , (glIso3-fun∙ n m f)
-- -- --   Iso.inv (glIso3 n m) = glIso3-inv n m
-- -- --   Iso.rightInv (glIso3 zero m) (f , p) =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --       (funExt λ { false → cong (ΩKn+1→Kn m) (sym (rUnit _)) ∙ Iso.leftInv (Iso-Kn-ΩKn+1 _) (f false)
-- -- --                 ; true → sym p})
-- -- --   Iso.rightInv (glIso3 (suc n) m) (f , p) =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --       (funExt λ x → (λ i → ΩKn+1→Kn m (sym (rUnit (cong-∙ (glIso3-inv (suc n) m (f , p) .fst) (merid x) (sym (merid (ptSn _))) i)) i))
-- -- --       ∙∙ cong (ΩKn+1→Kn m) (cong (Kn→ΩKn+1 m (f x) ∙_) (cong sym (cong (Kn→ΩKn+1 m) p ∙ Kn→ΩKn+10ₖ m)) ∙ sym (rUnit _))
-- -- --       ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 _)  (f x))
-- -- --   Iso.leftInv (glIso3 zero m) (f , p) = →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --     (funExt λ { base → sym p
-- -- --               ; (loop i) j → h j i})
-- -- --     where
-- -- --     h : PathP (λ i → p (~ i) ≡ p (~ i)) (Kn→ΩKn+1 m (ΩKn+1→Kn m (sym p ∙∙ cong f loop ∙∙ p))) (cong f loop)
-- -- --     h = Iso.rightInv (Iso-Kn-ΩKn+1 _) _
-- -- --       ◁ λ i → doubleCompPath-filler (sym p) (cong f loop) p (~ i)
-- -- --   Iso.leftInv (glIso3 (suc n) m) (f , p) =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --      (funExt λ { north → sym p
-- -- --                ; south → sym p ∙ cong f (merid (ptSn _))
-- -- --                ; (merid a i) j → h a j i})
-- -- --     where
-- -- --     h : (a : S₊ (suc n)) → PathP (λ i → p (~ i) ≡ (sym p ∙ cong f (merid (ptSn (suc n)))) i)
-- -- --                                  (Kn→ΩKn+1 m (ΩKn+1→Kn m (sym p ∙∙ cong f (merid a ∙ sym (merid (ptSn _))) ∙∙ p)))
-- -- --                                  (cong f (merid a))
-- -- --     h a = Iso.rightInv (Iso-Kn-ΩKn+1 _) _
-- -- --         ◁ λ i j → hcomp (λ k → λ { (i = i1) → (f (merid a j))
-- -- --                                    ; (j = i0) → p (k ∧ ~ i)
-- -- --                                    ; (j = i1) → compPath-filler' (sym p) (cong f (merid (ptSn _))) k i })
-- -- --                          (f (compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j))

-- -- --   glIsoInvHom : (n m : ℕ) (x y : coHomK n) (z : S₊ (suc m))
-- -- --     → Iso.inv (glIso3 _ _) (G m n (x +ₖ y)) .fst z
-- -- --     ≡ Iso.inv (glIso3 _ _) (G m n x) .fst z
-- -- --     +ₖ Iso.inv (glIso3 _ _) (G m n y) .fst z
-- -- --   glIsoInvHom zero zero x y base = refl
-- -- --   glIsoInvHom (suc n) zero x y base = refl
-- -- --   glIsoInvHom zero zero x y (loop i) j = h j i
-- -- --     where
-- -- --     h : (cong (Iso.inv (glIso3 _ _) (G zero zero (x + y)) .fst) loop)
-- -- --       ≡ cong₂ _+ₖ_ (cong (Iso.inv (glIso3 _ _) (G zero zero x) .fst) loop)
-- -- --                    (cong (Iso.inv (glIso3 _ _) (G zero zero y) .fst) loop)
-- -- --     h = Kn→ΩKn+1-hom 0 x y
-- -- --      ∙ ∙≡+₁ (cong (Iso.inv (glIso3 _ _) (G zero zero x) .fst) loop)
-- -- --             (cong (Iso.inv (glIso3 _ _) (G zero zero y) .fst) loop)
-- -- --   glIsoInvHom (suc n) zero x y (loop i) j = h j i
-- -- --     where
-- -- --     h : Kn→ΩKn+1 (suc n) ((pos (suc zero)) ·₀ (x +ₖ y))
-- -- --       ≡ cong₂ _+ₖ_ (cong (Iso.inv (glIso3 zero (zero +' suc n)) (G zero (suc n) x) .fst) loop)
-- -- --                    (cong (Iso.inv (glIso3 zero (zero +' suc n)) (G zero (suc n) y) .fst) loop)
-- -- --     h = cong (Kn→ΩKn+1 (suc n)) (lUnit⌣ₖ _ (x +ₖ y))
-- -- --      ∙∙ Kn→ΩKn+1-hom (suc n) x y
-- -- --      ∙∙ (λ i → ∙≡+₂ n (Kn→ΩKn+1 (suc n) (lUnit⌣ₖ _ x (~ i)))
-- -- --                        (Kn→ΩKn+1 (suc n) (lUnit⌣ₖ _ y (~ i))) i)
-- -- --   glIsoInvHom zero (suc m) x y north = refl
-- -- --   glIsoInvHom zero (suc m) x y south = refl
-- -- --   glIsoInvHom zero (suc m) x y (merid a i) j = h j i
-- -- --     where
-- -- --     h : Kn→ΩKn+1 (suc m) (_⌣ₖ_ {n = suc m} {m = zero} ∣ a ∣ (x + y))
-- -- --       ≡ cong₂ _+ₖ_ (Kn→ΩKn+1 (suc m) (_⌣ₖ_ {n = suc m} {m = zero} ∣ a ∣ x))
-- -- --                    (Kn→ΩKn+1 (suc m) (_⌣ₖ_ {n = suc m} {m = zero} ∣ a ∣ y))
-- -- --     h = cong (Kn→ΩKn+1 (suc m)) (leftDistr-⌣ₖ (suc m) 0 ∣ a ∣ x y)
-- -- --      ∙∙ Kn→ΩKn+1-hom (suc m) _ _
-- -- --      ∙∙ ∙≡+₂ _ _ _
-- -- --   glIsoInvHom (suc n) (suc m) x y north = refl
-- -- --   glIsoInvHom (suc n) (suc m) x y south = refl
-- -- --   glIsoInvHom (suc n) (suc m) x y (merid a i) j = h j i
-- -- --     where
-- -- --     h : Kn→ΩKn+1 (suc (suc (m +ℕ n))) (_⌣ₖ_ {n = suc m} {m = suc n} ∣ a ∣ (x +ₖ y))
-- -- --       ≡ cong₂ _+ₖ_ (Kn→ΩKn+1 (suc (suc (m +ℕ n))) (_⌣ₖ_ {n = suc m} {m = suc n} ∣ a ∣ x))
-- -- --                    (Kn→ΩKn+1 (suc (suc (m +ℕ n))) (_⌣ₖ_ {n = suc m} {m = suc n} ∣ a ∣ y))
-- -- --     h = cong (Kn→ΩKn+1 (suc (suc (m +ℕ n))))
-- -- --              (leftDistr-⌣ₖ (suc m) (suc n) ∣ a ∣ x y)
-- -- --      ∙∙ Kn→ΩKn+1-hom _ _ _
-- -- --      ∙∙ ∙≡+₂ _ _ _

-- -- --   +'-suc : (n m : ℕ) → suc n +' m ≡ suc (n +' m)
-- -- --   +'-suc zero zero = refl
-- -- --   +'-suc (suc n) zero = refl
-- -- --   +'-suc zero (suc m) = refl
-- -- --   +'-suc (suc n) (suc m) = refl

-- -- --   LEM : (i n : ℕ) (x : coHomK i)
-- -- --     → Path _ (G (suc n) i x)
-- -- --                  (subst (λ x → S₊∙ (suc n) →∙ coHomK-ptd x)
-- -- --                  (sym (+'-suc n i))
-- -- --                  ((Iso.inv (glIso3 n _)) (G n i x)))
-- -- --   LEM zero zero x =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --       (funExt λ z → (λ i → x ·₀ ∣ z ∣) ∙ h x z ∙ sym (transportRefl _))
-- -- --       where
-- -- --       h : (x : ℤ) (z : S¹) → _·₀_ {n = 1} x ∣ z ∣ ≡ fst (Iso.inv (glIso3 0 zero) (G zero zero x)) z
-- -- --       h = Int-ind _ (λ { base → refl ; (loop i) j → Kn→ΩKn+10ₖ zero (~ j) i})
-- -- --                     (λ { base → refl ; (loop i) j → rUnit (cong ∣_∣ₕ (lUnit loop j)) j i})
-- -- --                     (λ { base → refl ; (loop i) j → rUnit (cong ∣_∣ₕ (sym loop)) j i})
-- -- --                     λ x y inx iny z
-- -- --                       → rightDistr-⌣ₖ 0 1 x y ∣ z ∣
-- -- --                       ∙∙ cong₂ _+ₖ_ (inx z) (iny z)
-- -- --                       ∙∙ sym (glIsoInvHom zero zero x y z)
-- -- --   LEM (suc i) zero x =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --       (funExt λ z → h z
-- -- --             ∙ sym (transportRefl
-- -- --                ((Iso.inv (glIso3 zero (suc i)) (G zero (suc i) x)) .fst z)))
-- -- --     where
-- -- --     h : (z : S₊ 1) → _ ≡ Iso.inv (glIso3 zero (suc i)) (G zero (suc i) x) .fst z
-- -- --     h base = refl
-- -- --     h (loop k) j = Kn→ΩKn+1 (suc i) (lUnit⌣ₖ _ x (~ j)) k
-- -- --   LEM zero (suc n) x =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --       (funExt λ z → h x z ∙ λ i → transportRefl (Iso.inv (glIso3 (suc n) (suc n)) (G (suc n) zero x)) (~ i) .fst z)
-- -- --       where
-- -- --       +merid : rUnitₖ (suc (suc n)) ∣ south ∣ ≡ cong ∣_∣ₕ (merid (ptSn _))
-- -- --       +merid = sym (lUnit _)
-- -- --              ∙ cong (cong ∣_∣ₕ)
-- -- --              λ j i → transp (λ _ → S₊ (suc (suc n))) (i ∨ j) (merid (ptSn (suc n)) i)
-- -- --       open import Cubical.Foundations.Path

-- -- --       pp : (a : S₊ (suc n)) → PathP (λ i → ∣ merid a i ∣ₕ ≡ Kn→ΩKn+1 (suc n) (∣ a ∣ +ₖ (0ₖ _)) i)
-- -- --                                      refl (sym (rUnitₖ (suc (suc n)) ∣ south ∣))
-- -- --       pp a = flipSquare ((λ i j → ∣ compPath-filler (merid a) (sym (merid (ptSn _))) i j ∣ₕ )
-- -- --               ▷ cong (Kn→ΩKn+1 (suc n)) (sym (rUnitₖ (suc n) ∣ a ∣ₕ)))
-- -- --             ▷ sym (cong sym +merid)

-- -- --       pp2 : (a : S₊ (suc n)) → (λ i → -ₖ ∣ merid a i ∣)
-- -- --                                ≡ Kn→ΩKn+1 (suc n) (-ₖ ∣ a ∣)
-- -- --       pp2 a = cong (cong ∣_∣ₕ) (sym (symDistr (merid a) (sym (merid (ptSn (suc n))))))
-- -- --             ∙ sym (Kn→ΩKn+1-ₖ (suc n) ∣ a ∣)

-- -- --       h : (x : ℤ) (z : S₊ (suc (suc n)))
-- -- --        → _⌣ₖ_ {n = suc (suc n)} {m = 0} ∣ z ∣ x
-- -- --         ≡ Iso.inv (glIso3 (suc n) (suc n)) (G (suc n) zero x) .fst z
-- -- --       h = Int-ind _
-- -- --             (λ { north → refl ; south → refl ; (merid a i) j → Kn→ΩKn+10ₖ (suc n) (~ j) i})
-- -- --             (λ { north → refl ; south → refl
-- -- --                ; (merid a i) j → hcomp (λ k → λ { (i = i0) → ∣ north ∣
-- -- --                                                   ; (i = i1) → rUnitₖ (suc (suc n)) ∣ south ∣ (~ k)
-- -- --                                                   ; (j = i0) → rUnitₖ (suc (suc n)) ∣ merid a i ∣ (~ k)
-- -- --                                                   ; (j = i1) → pp a i k})
-- -- --                                        ∣ merid a i ∣ₕ})
-- -- --             (λ { north → refl
-- -- --                ; south → refl
-- -- --                ; (merid a i) j → pp2 a j i})
-- -- --             λ x y indx indy z → leftDistr-⌣ₖ _ _ ∣ z ∣ x y
-- -- --                                ∙ cong₂ _+ₖ_ (indx z) (indy z)
-- -- --                                ∙ sym (glIsoInvHom _ _ _ _ _)
-- -- --   LEM (suc i) (suc n) x =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --       (funExt λ z → h z
-- -- --          ∙ λ j → transportRefl ((Iso.inv (glIso3 (suc n) (suc (suc (n +ℕ i))))
-- -- --                      (G (suc n) (suc i) x))) (~ j) .fst z)
-- -- --     where
-- -- --     h : (z : S₊ (suc (suc n))) → _
-- -- --     h north = refl
-- -- --     h south = refl
-- -- --     h (merid a i) = refl

-- -- --   isEquivGzero : (i : ℕ) → isEquiv (G zero i)
-- -- --   isEquivGzero i =
-- -- --     isoToIsEquiv
-- -- --       (iso _ (λ f → fst f false)
-- -- --         (λ {(f , p) → →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --               (funExt λ { false → rUnitₖ _ (f false) ; true → sym p})})
-- -- --         (lUnit⌣ₖ _))

-- -- --   isEquivG : (n i : ℕ) → isEquiv (G n i)
-- -- --   isEquivG zero i =
-- -- --     isoToIsEquiv
-- -- --       (iso _ (λ f → fst f false)
-- -- --         (λ {(f , p) → →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --               (funExt λ { false → rUnitₖ _ (f false) ; true → sym p})})
-- -- --         (lUnit⌣ₖ _))
-- -- --   isEquivG (suc n) i =
-- -- --     subst isEquiv (sym (funExt (LEM i n)))
-- -- --       (compEquiv (compEquiv (G n i , isEquivG n i)
-- -- --         (isoToEquiv (invIso (glIso3 n (n +' i)))))
-- -- --         (pathToEquiv (λ j → S₊∙ (suc n) →∙ coHomK-ptd (+'-suc n i (~ j)))) .snd)


-- -- --   isEquiv-g : (n i : ℕ) → isEquiv (g n i)
-- -- --   isEquiv-g n i =
-- -- --     subst isEquiv (sym (g≡ n i))
-- -- --       (compEquiv (G n i , isEquivG n i) (compEquiv (eq2 n i) (eq1 n i)) .snd)

-- -- -- module _ {ℓ} (B : Pointed ℓ) (Q : typ B → Pointed ℓ-zero)
-- -- --          (conB : (x y : typ B) → ∥ x ≡ y ∥)
-- -- --          (n : ℕ) (Q-is : Iso (typ (Q (pt B))) (S₊ n))
-- -- --          (Q-is-ptd : Iso.fun Q-is (pt (Q (pt B))) ≡ snd (S₊∙ n))
-- -- --          (c : (b : typ B) → (Q b →∙ coHomK-ptd n))
-- -- --          (c-pt : c (pt B) .fst ≡ ((λ x → genFunSpace n .fst (Iso.fun Q-is x)))) where

-- -- --   g : (b : typ B) (i : ℕ) → coHomK i → (Q b →∙ coHomK-ptd (i +' n))
-- -- --   fst (g b i x) y = x ⌣ₖ c b .fst y
-- -- --   snd (g b i x) = cong (x ⌣ₖ_) (c b .snd) ∙ ⌣ₖ-0ₖ i n x

-- -- --   g' : (b : typ B) (i : ℕ) → coHomK i → coHomK i → (Q b →∙ coHomK-ptd (i +' n))
-- -- --   fst (g' b i x y) z = x ⌣ₖ c b .fst z +ₖ y ⌣ₖ c b .fst z
-- -- --   snd (g' b i x y) = cong₂ _+ₖ_ (cong (x ⌣ₖ_) (c b .snd) ∙ ⌣ₖ-0ₖ i n x)
-- -- --                        (cong (y ⌣ₖ_) (c b .snd) ∙ ⌣ₖ-0ₖ i n y) ∙ rUnitₖ _ (0ₖ _)

-- -- --   g-hom : (b : typ B) (i : ℕ) → (x y : coHomK i) → g b i (x +ₖ y) ≡ ((g b i x) ++ (g b i y))
-- -- --   g-hom b i x y = →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ z → rightDistr-⌣ₖ i n x y (c b .fst z))

-- -- --   gPathP' : (i : ℕ) → PathP (λ j → coHomK i → (isoToPath Q-is j , ua-gluePath (isoToEquiv Q-is) (Q-is-ptd) j)
-- -- --                                  →∙ coHomK-ptd (i +' n)) (g (pt B) i) (g-base.g n i)
-- -- --   gPathP' i =
-- -- --     toPathP
-- -- --       (funExt
-- -- --       λ x → →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --           (funExt λ y → (λ i → transportRefl (transportRefl x i ⌣ₖ c (pt B) .fst (Iso.inv Q-is (transportRefl y i))) i)
-- -- --                        ∙ cong (x ⌣ₖ_) (funExt⁻ c-pt (Iso.inv Q-is y) ∙ cong (genFunSpace n .fst) (Iso.rightInv Q-is y))))

-- -- --   g-base : (i : ℕ) → isEquiv (g (pt B) i)
-- -- --   g-base i = transport (λ j → isEquiv (gPathP' i (~ j))) (g-base.isEquiv-g n i)

-- -- --   g-equiv : (b : typ B) (i : ℕ) → isEquiv (g b i)
-- -- --   g-equiv b i =
-- -- --     pRec (isPropIsEquiv _)
-- -- --          (J (λ b _ → isEquiv (g b i))
-- -- --            (g-base i))
-- -- --          (conB (pt B) b)

-- -- -- module _ {ℓ} (B : Pointed ℓ) (Q : typ B → Pointed ℓ-zero)
-- -- --          (conB : (x y : typ B) → ∥ x ≡ y ∥₂)
-- -- --          (n : ℕ) (Q-is : Iso (typ (Q (pt B))) (S₊ n))
-- -- --          (Q-is-ptd : Iso.fun Q-is (pt (Q (pt B))) ≡ snd (S₊∙ n)) where

-- -- --   is-setQ→K : (b : typ B) → isSet (Q b →∙ coHomK-ptd n)
-- -- --   is-setQ→K b =
-- -- --     sRec (isProp→isOfHLevelSuc 1 isPropIsSet)
-- -- --           (J (λ b _ → isSet (Q b →∙ coHomK-ptd n))
-- -- --             (subst isSet (cong (_→∙ coHomK-ptd n)
-- -- --               (ua∙ (isoToEquiv (invIso Q-is)) (cong (Iso.inv Q-is) (sym Q-is-ptd) ∙ Iso.leftInv Q-is _)))
-- -- --               (isOfHLevelRetractFromIso 2 (fst (S1' n)) isSetℤ)))
-- -- --           (conB (pt B) b)


-- -- --   isConnB : isConnected 3 (typ B)
-- -- --   fst isConnB = ∣ pt B ∣
-- -- --   snd isConnB =
-- -- --     trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
-- -- --            λ a → sRec (isOfHLevelTrunc 3 _ _) (cong ∣_∣ₕ) (conB (pt B) a)

-- -- --   isPropPath : isProp (∥ pt B ≡ pt B ∥₂)
-- -- --   isPropPath =
-- -- --     isOfHLevelRetractFromIso 1 setTruncTrunc2Iso
-- -- --       (isContr→isProp (isConnectedPath _ isConnB (pt B) (pt B)))

-- -- --   c* : Σ[ c ∈ ((b : typ B) → (Q b →∙ coHomK-ptd n)) ] 
-- -- --          (c (pt B) .fst ≡ ((λ x → genFunSpace n .fst (Iso.fun Q-is x))))
-- -- --   fst c* b =
-- -- --     sRec (is-setQ→K b)
-- -- --           (J (λ b _ → Q b →∙ coHomK-ptd n)
-- -- --             ((λ x → genFunSpace n .fst (Iso.fun Q-is x))
-- -- --            , cong (genFunSpace n .fst) Q-is-ptd ∙ genFunSpace n .snd)) (conB (pt B) b)
-- -- --   snd c* =
-- -- --     funExt λ x → (λ i → sRec (is-setQ→K (pt B))
-- -- --                   (J (λ b _ → Q b →∙ coHomK-ptd n)
-- -- --                    ((λ x₁ → genFunSpace n .fst (Iso.fun Q-is x₁)) ,
-- -- --                     (λ i → genFunSpace n .fst (Q-is-ptd i)) ∙ genFunSpace n .snd))
-- -- --                   (isPropPath (conB (pt B) (pt B)) ∣ refl ∣₂ i) .fst x)
-- -- --       ∙ (λ i → transportRefl (genFunSpace n .fst (Iso.fun Q-is (transportRefl x i))) i)

-- -- --   p-help : {b : fst B} (p : pt B ≡ b) → (subst (fst ∘ Q) (sym p) (snd (Q b))) ≡ (snd (Q (pt B)))
-- -- --   p-help {b = b} =
-- -- --     J (λ b p → subst (fst ∘ Q) (sym p) (snd (Q b)) ≡ snd (Q (pt B))) (transportRefl _)

-- -- --   cEquiv : (b : fst B) (p : ∥ pt B ≡ b ∥₂)
-- -- --     → (c* .fst b)
-- -- --       ≡ sRec (is-setQ→K b)
-- -- --              (λ pp → (λ qb → genFunSpace n .fst (Iso.fun Q-is (subst (fst ∘ Q) (sym pp) qb)))
-- -- --              , cong (genFunSpace n .fst ∘ Iso.fun Q-is) (p-help pp)
-- -- --              ∙ ((λ i → genFunSpace n .fst (Q-is-ptd i)) ∙ genFunSpace n .snd)) p
-- -- --   cEquiv b =
-- -- --     sElim (λ _ → isOfHLevelPath 2 (is-setQ→K b) _ _)
-- -- --           (J (λ b a → c* .fst b ≡
-- -- --       sRec (is-setQ→K b) (λ pp →
-- -- --          (λ qb →
-- -- --             genFunSpace n .fst (Iso.fun Q-is (subst (fst ∘ Q) (sym pp) qb)))
-- -- --          ,
-- -- --          cong (genFunSpace n .fst ∘ Iso.fun Q-is) (p-help pp) ∙
-- -- --          (λ i → genFunSpace n .fst (Q-is-ptd i)) ∙ genFunSpace n .snd)
-- -- --       ∣ a ∣₂)
-- -- --       ((λ i → sRec (is-setQ→K (pt B))
-- -- --       (J (λ b₁ _ → Q b₁ →∙ coHomK-ptd n)
-- -- --        ((λ x → genFunSpace n .fst (Iso.fun Q-is x)) ,
-- -- --         (λ i → genFunSpace n .fst (Q-is-ptd i)) ∙ genFunSpace n .snd))
-- -- --           (isPropPath (conB (pt B) (pt B)) ∣ refl ∣₂ i))
-- -- --           ∙ →∙Homogeneous≡ (isHomogeneousKn n)
-- -- --             (transportRefl ((λ x → genFunSpace n .fst (Iso.fun Q-is x)))
-- -- --             ∙ funExt λ x → cong (genFunSpace n .fst ∘ Iso.fun Q-is) (sym (transportRefl x)))))

-- -- -- module _ {ℓ ℓ'} (B : Pointed ℓ) (P : typ B → Type ℓ') where
-- -- --   E : Type _
-- -- --   E = Σ (typ B) P

-- -- --   Ẽ : Type _
-- -- --   Ẽ = Pushout {A = E} (λ _ → tt) fst

-- -- --   i : (n : ℕ) → (P-base : Iso (P (pt B)) (S₊ n)) → S₊ (suc n) → Ẽ
-- -- --   i zero P-base base = inr (pt B)
-- -- --   i zero P-base (loop j) = (sym (push (pt B , Iso.inv P-base false))
-- -- --                                ∙ push ((pt B) , Iso.inv P-base true)) j
-- -- --   i (suc n) P-base north = inl tt
-- -- --   i (suc n) P-base south = inr (pt B)
-- -- --   i (suc n) P-base (merid a i₁) = push (pt B , Iso.inv P-base a) i₁

-- -- --   Q : typ B → Pointed ℓ'
-- -- --   Q x = Susp (P x) , north

-- -- --   F : Type _
-- -- --   F = Σ (typ B) λ x → Q x .fst

-- -- --   F̃ : Type _
-- -- --   F̃ = Pushout {A = typ B} {C = F} (λ _ → tt) λ b → b , north

-- -- --   invFE : Ẽ → F̃
-- -- --   invFE (inl x) = inl tt
-- -- --   invFE (inr x) = inr (x , south)
-- -- --   invFE (push (x , a) i₁) = ((push x) ∙ λ i → inr (x , merid a i)) i₁

-- -- --   funFE : F̃ → Ẽ
-- -- --   funFE (inl x) = inl tt
-- -- --   funFE (inr (x , north)) = inl tt
-- -- --   funFE (inr (x , south)) = inr x
-- -- --   funFE (inr (x , merid a i₁)) = push (x , a) i₁
-- -- --   funFE (push a i₁) = inl tt

-- -- --   IsoFE : Iso F̃ Ẽ
-- -- --   Iso.fun IsoFE = funFE
-- -- --   Iso.inv IsoFE = invFE
-- -- --   Iso.rightInv IsoFE (inl x) = refl
-- -- --   Iso.rightInv IsoFE (inr x) = refl
-- -- --   Iso.rightInv IsoFE (push (x , a) i₁) k = h k i₁
-- -- --     where
-- -- --     h : cong funFE (((push x) ∙ λ i → inr (x , merid a i)))
-- -- --       ≡ push (x , a)
-- -- --     h = congFunct funFE (push x) (λ i → inr (x , merid a i))
-- -- --      ∙ sym (lUnit (push (x , a)))
-- -- --   Iso.leftInv IsoFE (inl x) = refl
-- -- --   Iso.leftInv IsoFE (inr (x , north)) = push x
-- -- --   Iso.leftInv IsoFE (inr (x , south)) = refl
-- -- --   Iso.leftInv IsoFE (inr (x , merid a i)) j =
-- -- --     compPath-filler' (push x) (λ i₁ → inr (x , merid a i₁)) (~ j) i
-- -- --   Iso.leftInv IsoFE (push a i₁) k =  push a (i₁ ∧ k)


-- -- --   funDir1 : ∀ {ℓ} {A : Pointed ℓ} → (F̃ , inl tt) →∙ A → (b : typ B) → Q b →∙ A
-- -- --   fst (funDir1 {A = A , a} (f , p) b) north = f (inr (b , north))
-- -- --   fst (funDir1 {A = A , a} (f , p) b) south = f (inr (b , south))
-- -- --   fst (funDir1 {A = A , a} (f , p) b) (merid a₁ i₁) = f (inr (b , merid a₁ i₁))
-- -- --   snd (funDir1 {A = A , a} (f , p) b) = sym (cong f (push b)) ∙ p

-- -- --   funDir2 : ∀ {ℓ} {A : Pointed ℓ} → ((b : typ B) → Q b →∙ A) → (F̃ , inl tt) →∙ A
-- -- --   fst (funDir2 {A = A , a} f) (inl x) = a
-- -- --   fst (funDir2 {A = A , a} f) (inr (x , north)) = f x .fst north
-- -- --   fst (funDir2 {A = A , a} f) (inr (x , south)) = f x .fst south
-- -- --   fst (funDir2 {A = A , a} f) (inr (x , merid a₁ i₁)) = f x .fst (merid a₁ i₁)
-- -- --   fst (funDir2 {A = A , a} f) (push a₁ i₁) = snd (f a₁) (~ i₁)
-- -- --   snd (funDir2 {A = A , a} f) = refl

-- -- --   funDir2-hom : (n : ℕ) → (f g : ((b : typ B) → Q b →∙ coHomK-ptd n))
-- -- --              → funDir2 (λ b → f b ++ g b) ≡ (funDir2 f ++ funDir2 g)
-- -- --   funDir2-hom n f g =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --                   (funExt λ { (inl x) → sym (rUnitₖ _ (0ₖ _))
-- -- --                              ; (inr (x , north)) → refl
-- -- --                              ; (inr (x , south)) → refl
-- -- --                              ; (inr (x , merid a i₁)) → refl
-- -- --                              ; (push a j) i → compPath-filler (cong₂ _+ₖ_ (snd (f a)) (snd (g a)))
-- -- --                                                                (rUnitₖ n (0ₖ n)) (~ i) (~ j)})

-- -- --   funDirSect : ∀ {ℓ} {A : Pointed ℓ} → (x : (b : typ B) → Q b →∙ A) (b : typ B) (q : Q b .fst)
-- -- --                → funDir1 (funDir2 x) b .fst q ≡ x b .fst q
-- -- --   funDirSect f b north = refl
-- -- --   funDirSect f b south = refl
-- -- --   funDirSect f b (merid a i₁) = refl

-- -- --   funDirRetr : ∀ {ℓ} {A : Pointed ℓ} (f : F̃ → typ A) (p : _)
-- -- --     → (x : F̃) → fst (funDir2 {A = A} (funDir1 (f , p))) x ≡ f x
-- -- --   funDirRetr f p (inl x) = sym p
-- -- --   funDirRetr f p (inr (x , north)) = refl
-- -- --   funDirRetr f p (inr (x , south)) = refl
-- -- --   funDirRetr f p (inr (x , merid a i₁)) = refl
-- -- --   funDirRetr f p (push a i₁) j = compPath-filler (sym (cong f (push a))) p (~ j) (~ i₁)

-- -- --   Iso2 : ∀ {ℓ} {A : Pointed ℓ}
-- -- --     → Iso ((F̃ , inl tt) →∙ A)
-- -- --           ((b : typ B) → Q b →∙ A)
-- -- --   Iso.fun (Iso2 {A = A , a}) = funDir1
-- -- --   Iso.inv (Iso2 {A = A , a}) = funDir2
-- -- --   Iso.rightInv (Iso2 {A = A , a}) f =
-- -- --     funExt λ b → ΣPathP (funExt (funDirSect f b)
-- -- --                , sym (rUnit (snd (f b))))
-- -- --   Iso.leftInv (Iso2 {A = A , a}) (f , p) =
-- -- --     ΣPathP ((funExt (funDirRetr f p))
-- -- --          , λ i j → p (~ i ∨ j))

-- -- --   ι : (k : ℕ) → Iso ((b : typ B) → Q b →∙ coHomK-ptd k)
-- -- --                       ((Ẽ , inl tt) →∙ coHomK-ptd k)
-- -- --   ι k = compIso (invIso Iso2) h
-- -- --     where
-- -- --     h : Iso ((F̃ , inl tt) →∙ coHomK-ptd k)
-- -- --              ((Ẽ , inl tt) →∙ coHomK-ptd k)
-- -- --     Iso.fun h G = (λ x → G .fst (Iso.inv IsoFE x))
-- -- --                 , (snd G)
-- -- --     Iso.inv h G = (λ x → G .fst (Iso.fun IsoFE x))
-- -- --                 , (snd G)
-- -- --     Iso.rightInv h G =
-- -- --       →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --         (funExt λ x → cong (G .fst) (Iso.rightInv IsoFE x))
-- -- --     Iso.leftInv h G =
-- -- --       →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --         (funExt λ x → cong (G .fst) (Iso.leftInv IsoFE x))

-- -- --   ι-hom : (k : ℕ) → (f g : ((b : typ B) → Q b →∙ coHomK-ptd k))
-- -- --                    → Iso.fun (ι k) (λ b → f b ++ g b)
-- -- --                    ≡ (Iso.fun (ι k) f ++ Iso.fun (ι k) g)
-- -- --   ι-hom k f g =
-- -- --     →∙Homogeneous≡ (isHomogeneousKn _)
-- -- --         (funExt λ x → funExt⁻ (cong fst (funDir2-hom _ f g)) (invFE x))

-- -- -- codomainIsoDep : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
-- -- --                  → ((a : A) → Iso (B a) (C a))
-- -- --                  → Iso ((a : A) → B a) ((a : A) → C a)
-- -- -- Iso.fun (codomainIsoDep is) f a = Iso.fun (is a) (f a)
-- -- -- Iso.inv (codomainIsoDep is) f a = Iso.inv (is a) (f a)
-- -- -- Iso.rightInv (codomainIsoDep is) f = funExt λ a → Iso.rightInv (is a) (f a)
-- -- -- Iso.leftInv (codomainIsoDep is) f = funExt λ a → Iso.leftInv (is a) (f a)

-- -- -- module Thom {ℓ} (B : Pointed ℓ) (P : typ B → Type ℓ-zero) 
-- -- --          (conB : (x y : typ B) → ∥ x ≡ y ∥)
-- -- --          (n : ℕ) (Q-is : Iso (typ (Q B P (pt B))) (S₊ n))
-- -- --          (Q-is-ptd : Iso.fun Q-is (pt (Q B P (pt B))) ≡ snd (S₊∙ n))
-- -- --          (c : (b : typ B) → (Q B P b →∙ coHomK-ptd n))
-- -- --          (c-pt : c (pt B) .fst ≡ ((λ x → genFunSpace n .fst (Iso.fun Q-is x)))) where

-- -- --   ϕ : (i : ℕ) → GroupEquiv (coHomGr i (typ B))
-- -- --                                 (coHomRedGrDir (i +' n) (Ẽ B P , inl tt))
-- -- --   fst (ϕ i) =
-- -- --     isoToEquiv
-- -- --       (setTruncIso
-- -- --         (compIso
-- -- --           (codomainIsoDep
-- -- --             λ b → equivToIso ((g B (Q B P) conB n Q-is Q-is-ptd c c-pt b i)
-- -- --                  , g-equiv B (Q B P) conB n Q-is Q-is-ptd c c-pt b i))
-- -- --             (ι B P (i +' n))))
-- -- --   snd (ϕ i) =
-- -- --     makeIsGroupHom
-- -- --     (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
-- -- --       λ F G → cong ∣_∣₂ (cong (Iso.fun (ι B P (i +' n)))
-- -- --                                    (funExt (λ a → g-hom B (Q B P) conB n Q-is Q-is-ptd c c-pt a i (F a) (G a)))
-- -- --                                  ∙ ι-hom B P (i +' n) _ _)
-- -- --                        ∙ addAgree (i +' n) _ _)

-- -- -- module Gysin {ℓ} (B : Pointed ℓ) (P : typ B → Type ℓ-zero) 
-- -- --          (conB : (x y : typ B) → ∥ x ≡ y ∥₂)
-- -- --          (n : ℕ) (Q-is : Iso (typ (Q B P (pt B))) (S₊ n))
-- -- --          (Q-is-ptd : Iso.fun Q-is (pt (Q B P (pt B))) ≡ snd (S₊∙ n)) where

-- -- --   0-connB : (x y : typ B) → ∥ x ≡ y ∥
-- -- --   0-connB x y = sRec (isProp→isSet squash) (∥_∥.∣_∣) (conB x y)

-- -- --   c = (c* B (Q B P) conB n Q-is Q-is-ptd .fst)
-- -- --   c-ptd = (c* B (Q B P) conB n Q-is Q-is-ptd .snd)
-- -- --   cEq = cEquiv B (Q B P) conB n Q-is Q-is-ptd

-- -- --   module w = Thom B P 0-connB n Q-is Q-is-ptd c c-ptd

-- -- --   ϕ = w.ϕ

-- -- --   E' = E B P

-- -- --   E'̃ = Ẽ B P

-- -- --   p : E' → typ B
-- -- --   p = fst

-- -- --   e : coHom n (typ B)
-- -- --   e = ∣ (λ b → c b .fst south) ∣₂

-- -- --   ⌣-hom : (i : ℕ) → GroupHom (coHomGr i (typ B)) (coHomGr (i +' n) (typ B))
-- -- --   fst (⌣-hom i) x = x ⌣ e
-- -- --   snd (⌣-hom i) =
-- -- --     makeIsGroupHom λ f g → rightDistr-⌣ _ _ f g e

-- -- --   p-hom : (i : ℕ) → GroupHom (coHomGr i (typ B)) (coHomGr i E')
-- -- --   p-hom i = coHomMorph _ p

-- -- --   E-susp : (i : ℕ) → GroupHom (coHomGr i E') (coHomRedGrDir (suc i) (E'̃ , inl tt))
-- -- --   fst (E-susp i) = sMap λ f → (λ { (inl x) → 0ₖ _
-- -- --                                   ; (inr x) → 0ₖ _
-- -- --                                   ; (push a j) → Kn→ΩKn+1 _ (f a) j}) , refl
-- -- --   snd (E-susp zero) =
-- -- --     makeIsGroupHom (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
-- -- --       λ f g →
-- -- --         cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn 1)
-- -- --           (funExt λ { (inl x) → refl
-- -- --                     ; (inr x) → refl
-- -- --                     ; (push a j) k → (Kn→ΩKn+1-hom zero (f a) (g a)
-- -- --                                    ∙ ∙≡+₁ (Kn→ΩKn+1 _ (f a)) (Kn→ΩKn+1 _ (g a))) k j})))
-- -- --   snd (E-susp (suc i)) =
-- -- --     makeIsGroupHom (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
-- -- --       λ f g →
-- -- --         cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _)
-- -- --           (funExt λ { (inl x) → refl
-- -- --                     ; (inr x) → refl
-- -- --                     ; (push a j) k → (Kn→ΩKn+1-hom _ (f a) (g a)
-- -- --                                    ∙ ∙≡+₂ _ (Kn→ΩKn+1 _ (f a)) (Kn→ΩKn+1 _ (g a))) k j})))

-- -- --   module cofibSeq where
-- -- --     j* : (i : ℕ) → GroupHom (coHomRedGrDir i (E'̃ , (inl tt))) (coHomGr i (typ B))
-- -- --     fst (j* i) = sMap λ f → λ x → fst f (inr x)
-- -- --     snd (j* zero) =
-- -- --       makeIsGroupHom
-- -- --         (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl)
-- -- --     snd (j* (suc zero)) =
-- -- --       makeIsGroupHom
-- -- --         (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl)
-- -- --     snd (j* (suc (suc i₁))) =
-- -- --       makeIsGroupHom
-- -- --         (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl)

-- -- --     Im-j⊂Ker-p : (i : ℕ) (x : _) → isInIm (j* i) x → isInKer (p-hom i) x
-- -- --     Im-j⊂Ker-p i =
-- -- --       sElim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
-- -- --         λ f → pRec (squash₂ _ _)
-- -- --           (uncurry (sElim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
-- -- --             λ g P → subst (isInKer (p-hom i)) P
-- -- --               (cong ∣_∣₂ (funExt λ x → cong (g .fst) (sym (push x)) ∙ g .snd))))

-- -- --     Ker-p⊂Im-j : (i : ℕ) (x : _) → isInKer (p-hom i) x → isInIm (j* i) x
-- -- --     Ker-p⊂Im-j i =
-- -- --       sElim (λ _ → isSetΠ (λ _ → isProp→isSet squash))
-- -- --         λ f ker → pRec squash
-- -- --           (λ id → ∣ ∣ (λ { (inl x) → 0ₖ _
-- -- --                          ; (inr x) → f x
-- -- --                          ; (push a i₁) → funExt⁻ id a (~ i₁)}) , refl ∣₂ , refl ∣)
-- -- --                    (Iso.fun PathIdTrunc₀Iso ker)

-- -- --   Im-p⊂Ker-Susp : (i : ℕ) (x : _) → isInIm (p-hom i) x → isInKer (E-susp i) x
-- -- --   Im-p⊂Ker-Susp i =
-- -- --     sElim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
-- -- --       λ f → pRec (squash₂ _ _)
-- -- --         (uncurry (sElim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
-- -- --           λ g y → subst (isInKer (E-susp i)) y
-- -- --             (cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _)
-- -- --               (funExt λ { (inl x) → refl
-- -- --                         ; (inr x) → sym (Kn→ΩKn+1 _ (g x))
-- -- --                         ; (push a j) k → Kn→ΩKn+1 i (g (fst a)) (~ k ∧ j)})))))
-- -- --   open import Cubical.Foundations.Path
-- -- --   Ker-Susp⊂Im-p : (i : ℕ) (x : _) → isInKer (E-susp i) x → isInIm (p-hom i) x
-- -- --   Ker-Susp⊂Im-p i =
-- -- --     sElim (λ _ → isSetΠ (λ _ → isProp→isSet squash))
-- -- --       λ f ker → pRec squash
-- -- --         (λ id → ∣ ∣ (λ x → ΩKn+1→Kn i (sym (funExt⁻ (cong fst id) (inr x)))) ∣₂
-- -- --                   , cong ∣_∣₂ (funExt (λ { (a , b) →
-- -- --                          cong (ΩKn+1→Kn i) (lUnit _ ∙ cong (_∙ sym (funExt⁻ (λ i₁ → fst (id i₁)) (inr a))) (sym (flipSquare (cong snd id))
-- -- --                        ∙∙ (PathP→compPathR (cong (funExt⁻ (cong fst id)) (push (a , b))))
-- -- --                        ∙∙ assoc _ _ _
-- -- --                         ∙ sym (rUnit _))
-- -- --                         ∙ (sym (assoc _ _ _)
-- -- --                         ∙∙ cong (Kn→ΩKn+1 i (f (a , b)) ∙_) (rCancel _)
-- -- --                         ∙∙ sym (rUnit _)))
-- -- --                         ∙ Iso.leftInv (Iso-Kn-ΩKn+1 _) (f (a , b))})) ∣)
-- -- --         (Iso.fun PathIdTrunc₀Iso ker)

-- -- --   Im-Susp⊂Ker-j : (i : ℕ) (x : _) → isInIm (E-susp i) x → isInKer (cofibSeq.j* (suc i)) x
-- -- --   Im-Susp⊂Ker-j i =
-- -- --     sElim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
-- -- --       λ g → pRec (squash₂ _ _)
-- -- --         (uncurry (sElim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
-- -- --           λ f id → pRec (squash₂ _ _)
-- -- --             (λ P → subst (isInKer (cofibSeq.j* (suc i))) (cong ∣_∣₂ P)
-- -- --               (cong ∣_∣₂ refl))
-- -- --             (Iso.fun PathIdTrunc₀Iso id)))

-- -- --   Ker-j⊂Im-Susp : (i : ℕ) (x : _) → isInKer (cofibSeq.j* (suc i)) x → isInIm (E-susp i) x
-- -- --   Ker-j⊂Im-Susp i =
-- -- --     sElim (λ _ → isSetΠ (λ _ → isProp→isSet squash))
-- -- --       λ f ker
-- -- --        → pRec squash
-- -- --           (λ p → ∣ ∣ (λ x → ΩKn+1→Kn _ (sym (snd f) ∙∙ cong (fst f) (push x) ∙∙ funExt⁻ p (fst x))) ∣₂
-- -- --                   , cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _)
-- -- --                     (funExt (λ { (inl x) → sym (snd f)
-- -- --                                ; (inr x) → sym (funExt⁻ p x) 
-- -- --                                ; (push a j) k → h f p a k j}))) ∣)
-- -- --           (Iso.fun PathIdTrunc₀Iso ker)
-- -- --           where
-- -- --           h : (f : (E'̃ , inl tt) →∙ coHomK-ptd (suc i))
-- -- --            → (p : (fst f ∘ inr) ≡ (λ _ → 0ₖ (suc i)))
-- -- --            → (a : E B P)
-- -- --            → PathP (λ i → snd f (~ i) ≡ p (~ i) (fst a))
-- -- --                    (Kn→ΩKn+1 i (ΩKn+1→Kn i (sym (snd f) ∙∙ cong (fst f) (push a) ∙∙ funExt⁻ p (fst a))))
-- -- --                    (cong (fst f) (push a))
-- -- --           h f p a = Iso.rightInv (Iso-Kn-ΩKn+1 i) _
-- -- --                   ◁ λ i j → doubleCompPath-filler (sym (snd f)) (cong (fst f) (push a)) (funExt⁻ p (fst a)) (~ i) j

-- -- --   ϕ∘j : (i : ℕ) → GroupHom (coHomGr i (typ B)) (coHomGr (i +' n) (typ B))
-- -- --   ϕ∘j i = compGroupHom (fst (fst (ϕ i)) , snd (ϕ i)) (cofibSeq.j* (i +' n))

-- -- --   +'-suc : (i n : ℕ) → (suc i +' n) ≡ suc (i +' n)
-- -- --   +'-suc zero zero = refl
-- -- --   +'-suc (suc i₁) zero = refl
-- -- --   +'-suc zero (suc n) = refl
-- -- --   +'-suc (suc i₁) (suc n) = refl

-- -- --   private
-- -- --     h : ∀ {ℓ ℓ'} {n m : ℕ} (G : ℕ → Group ℓ) (H : Group ℓ') (p : n ≡ m)
-- -- --       → GroupEquiv (G n) H
-- -- --       → GroupEquiv (G m) H
-- -- --     h {n = n} G H =
-- -- --       J (λ m _ → GroupEquiv (G n) H → GroupEquiv (G m) H)
-- -- --         λ p → p

-- -- --     h-ret : ∀ {ℓ ℓ'} {n m : ℕ} (G : ℕ → Group ℓ) (H : Group ℓ')
-- -- --       → (e : GroupEquiv (G n) H)
-- -- --       → (p : n ≡ m)
-- -- --       → (x : G m .fst) → invEq (fst e) (fst (fst (h G H p e)) x) ≡ subst (λ x → G x .fst) (sym p) x
-- -- --     h-ret G H e =
-- -- --       J (λ m p → ((x : G m .fst) → invEq (fst e) (fst (fst (h G H p e)) x) ≡ subst (λ x → G x .fst) (sym p) x))
-- -- --         λ x → cong (invEq (fst e) )
-- -- --               (λ i → transportRefl (transportRefl (fst (fst e) (transportRefl (transportRefl x i) i)) i) i)
-- -- --            ∙∙ retEq (fst e) x
-- -- --            ∙∙ sym (transportRefl _)

-- -- --   isEquivϕ' : (i : ℕ) → GroupEquiv (coHomRedGrDir (suc (i +' n)) (E'̃ , inl tt))
-- -- --                             (coHomGr (suc i) (typ B))
-- -- --   isEquivϕ' i = (h (λ n → coHomRedGrDir n (E'̃ , inl tt)) _ (+'-suc i n)
-- -- --                 (invGroupEquiv (ϕ (suc i))))

-- -- --   ϕ' : (i : ℕ) → GroupHom (coHomRedGrDir (suc (i +' n)) (E'̃ , inl tt))
-- -- --                             (coHomGr (suc i) (typ B))
-- -- --   ϕ' i = fst (fst (isEquivϕ' i)) , snd (isEquivϕ' i)

-- -- --   susp∘ϕ : (i : ℕ) → GroupHom (coHomGr (i +' n) E') (coHomGr (suc i) (typ B))
-- -- --   susp∘ϕ i = compGroupHom (E-susp (i +' n)) (ϕ' i)

-- -- --   Im-ϕ∘j⊂Ker-p : (i : ℕ) (x : _) → isInIm (ϕ∘j i) x → isInKer (p-hom _) x
-- -- --   Im-ϕ∘j⊂Ker-p i x p =
-- -- --     cofibSeq.Im-j⊂Ker-p _ x
-- -- --       (pRec squash (uncurry (λ f p → ∣ fst (fst (ϕ _)) f , p ∣)) p)

-- -- --   Ker-p⊂Im-ϕ∘j : (i : ℕ) (x : _) → isInKer (p-hom _) x → isInIm (ϕ∘j i) x
-- -- --   Ker-p⊂Im-ϕ∘j i x p =
-- -- --     pRec squash (uncurry (λ f p → ∣ (invEq (fst (ϕ _)) f)
-- -- --                                    , (cong (fst (cofibSeq.j* _)) (secEq (fst (ϕ _)) f) ∙ p) ∣))
-- -- --                 (cofibSeq.Ker-p⊂Im-j _ x p)


-- -- --   Im-p⊂KerSusp∘ϕ : (i : ℕ) (x : _) → isInIm (p-hom _) x → isInKer (susp∘ϕ i) x
-- -- --   Im-p⊂KerSusp∘ϕ i x p = cong (fst (ϕ' _)) (Im-p⊂Ker-Susp _ x p) ∙ IsGroupHom.pres1 (snd (ϕ' _))

-- -- --   KerSusp∘ϕ⊂Im-p : (i : ℕ) (x : _) → isInKer (susp∘ϕ i) x → isInIm (p-hom _) x
-- -- --   KerSusp∘ϕ⊂Im-p i x p =
-- -- --     Ker-Susp⊂Im-p _ x (sym (retEq (fst (isEquivϕ' _)) _)
-- -- --                      ∙ (cong (invEq (fst (isEquivϕ' _))) p
-- -- --                      ∙ IsGroupHom.pres1 (snd (invGroupEquiv (isEquivϕ' _)))))

-- -- --   Im-Susp∘ϕ⊂Ker-ϕ∘j : (i : ℕ) → (x : _) → isInIm (susp∘ϕ i) x → isInKer (ϕ∘j (suc i)) x
-- -- --   Im-Susp∘ϕ⊂Ker-ϕ∘j i x =
-- -- --     pRec (squash₂ _ _)
-- -- --       (uncurry λ f → J (λ x p → isInKer (ϕ∘j (suc i)) x)
-- -- --         ((λ i → fst (cofibSeq.j* _) (fst (fst (ϕ _)) (fst (ϕ' _) (fst (E-susp _) f))))
-- -- --              ∙∙ cong (fst (cofibSeq.j* _))
-- -- --                      ((h-ret (λ n → coHomRedGrDir n (E'̃ , inl tt)) _
-- -- --                              (invGroupEquiv (ϕ (suc i))) (+'-suc i n)) (fst (E-susp _) f))
-- -- --              ∙∙ (natTranspLem _ (λ n → fst (cofibSeq.j* n)) (sym (+'-suc i n))
-- -- --              ∙ cong (subst (λ z → coHomGr z (typ B) .fst) (sym (+'-suc i n)))
-- -- --                     (Im-Susp⊂Ker-j _ (fst (E-susp (i +' n)) f) ∣ f , refl ∣)
-- -- --               ∙ tLem i n)))
-- -- --     where
-- -- --     tLem : (i n : ℕ) → subst (λ z → coHomGr z (typ B) .fst) (sym (+'-suc i n))
-- -- --                                (0ₕ _) ≡ 0ₕ _
-- -- --     tLem zero zero = refl
-- -- --     tLem zero (suc n) = refl
-- -- --     tLem (suc i₁) zero = refl
-- -- --     tLem (suc i₁) (suc n) = refl


-- -- --   Ker-ϕ∘j⊂Im-Susp∘ϕ : (i : ℕ) (x : _)
-- -- --     → isInKer (ϕ∘j (suc i)) x → isInIm (susp∘ϕ i) x
-- -- --   Ker-ϕ∘j⊂Im-Susp∘ϕ i x p =
-- -- --     pRec squash
-- -- --       (uncurry (λ f p → ∣ f , cong (fst (fst (isEquivϕ' i))) p ∙ secEq (fst (isEquivϕ' _)) x ∣))
-- -- --       (Ker-j⊂Im-Susp _ (invEq (fst (isEquivϕ' _)) x)
-- -- --         ((cong (cofibSeq.j* (suc (i +' n)) .fst ) lem2
-- -- --         ∙ natTranspLem _ (λ n → cofibSeq.j* n .fst) (+'-suc i n))
-- -- --         ∙∙ cong (transport (λ j → (coHomGr (+'-suc i n j) (typ B) .fst))) p
-- -- --         ∙∙ h2 i n))
-- -- --     where
-- -- --     lem2 : invEq (fst (isEquivϕ' i)) x ≡ transport (λ j → coHomRed (+'-suc i n j) (E'̃ , inl tt)) (fst (fst (ϕ _)) x)
-- -- --     lem2 = cong (transport (λ j → coHomRed (+'-suc i n j) (E'̃ , inl tt)))
-- -- --                 (transportRefl _ ∙ cong (fst (fst (ϕ _)))
-- -- --                   λ i → transportRefl (transportRefl x i) i)

-- -- --     h2 : (i n : ℕ) → transport (λ j → coHomGr (+'-suc i n j) (typ B) .fst)
-- -- --       (GroupStr.1g (coHomGr (suc i +' n) (typ B) .snd)) ≡ 0ₕ _
-- -- --     h2 zero zero = refl
-- -- --     h2 zero (suc n) = refl
-- -- --     h2 (suc i₁) zero = refl
-- -- --     h2 (suc i₁) (suc n) = refl


-- -- --   ϕ∘j≡ : (i : ℕ) → ϕ∘j i ≡ ⌣-hom i
-- -- --   ϕ∘j≡ i =
-- -- --     Σ≡Prop (λ _ → isPropIsGroupHom _ _)
-- -- --            (funExt (sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- -- --            λ _ → refl))

-- -- -- open import Cubical.Experiments.Brunerie
-- -- -- open import Cubical.HITs.Hopf

-- -- -- open import Cubical.HITs.Join

-- -- -- module fibS1 = hopfBase S1-AssocHSpace (sphereElim2 _ (λ _ _ → squash) ∣ refl ∣)

-- -- -- S¹Hopf : S₊ 2 → Type
-- -- -- S¹Hopf = fibS1.Hopf

-- -- -- TotalHopf' : Type _
-- -- -- TotalHopf' = Σ (S₊ 2) S¹Hopf

-- -- -- CP2 : Type _
-- -- -- CP2 = fibS1.megaPush

-- -- -- fibr : CP2 → Type _
-- -- -- fibr = fibS1.P

-- -- -- hopf : join S¹ S¹ → S₊ 2
-- -- -- hopf x = fst (JoinS¹S¹→TotalHopf x)

-- -- -- E* : Type _
-- -- -- E* = fibS1.totalSpaceMegaPush

-- -- -- IsoE' : Iso E* (join S¹ (join S¹ S¹))
-- -- -- IsoE' = fibS1.IsoJoin₁

-- -- -- IsoE2 : (join S¹ (join S¹ S¹)) ≡ join S¹ (S₊ 3)
-- -- -- IsoE2 = cong (join S¹) (sym S³≡joinS¹S¹ ∙ isoToPath IsoS³S3)

-- -- -- IsoTotalHopf' : Iso fibS1.TotalSpaceHopf' (join S¹ S¹)
-- -- -- IsoTotalHopf' = fibS1.joinIso₁

-- -- -- CP' : Type _
-- -- -- CP' = Pushout (λ _ → tt) hopf

-- -- -- conCP2 : (x y : CP2) → ∥ x ≡ y ∥₂
-- -- -- conCP2 x y = sRec2 squash₂ (λ p q → ∣ p ∙ sym q ∣₂) (conCP2' x) (conCP2' y)
-- -- --   where
-- -- --   conCP2' : (x : CP2) → ∥ x ≡ inl tt ∥₂
-- -- --   conCP2' (inl x) = ∣ refl ∣₂
-- -- --   conCP2' (inr x) = sphereElim 1 {A = λ x → ∥ inr x ≡ inl tt ∥₂} (λ _ → squash₂) ∣ sym (push (inl base)) ∣₂ x
-- -- --   conCP2' (push a i₁) = ll a i₁
-- -- --     where
-- -- --     h2 : ∀ {ℓ} {A : fibS1.TotalSpaceHopf' → Type ℓ} → ((a : _) → isProp (A a))
-- -- --         → A (inl base)
-- -- --         → ((a : fibS1.TotalSpaceHopf') → A a) 
-- -- --     h2 {A = A} p b =
-- -- --       PushoutToProp p (sphereElim 0 (λ _ → p _) b)
-- -- --                       (sphereElim 0 (λ _ → p _) (subst A (push (base , base)) b))

-- -- --     ll : (a : fibS1.TotalSpaceHopf') → PathP (λ i → ∥ Path CP2 (push a i) (inl tt) ∥₂) (conCP2' (inl tt)) (conCP2' (inr (fibS1.induced a)))
-- -- --     ll = h2 (λ _ → isOfHLevelPathP' 1 squash₂ _ _) λ j → ∣ (λ i → push (inl base) (~ i ∧ j)) ∣₂

-- -- -- module GysinS1 = Gysin (CP2 , inl tt) fibr conCP2 2 idIso refl

-- -- -- PushoutReplaceBase :
-- -- --   ∀ {ℓ ℓ' ℓ''} {A B : Type ℓ} {C : Type ℓ'} {D : Type ℓ''} {f : A → C} {g : A → D}
-- -- --     (e : B ≃ A) → Pushout (f ∘ fst e) (g ∘ fst e) ≡ Pushout f g
-- -- -- PushoutReplaceBase {f = f} {g = g} =
-- -- --   EquivJ (λ _ e → Pushout (f ∘ fst e) (g ∘ fst e) ≡ Pushout f g)
-- -- --          refl

-- -- -- isContrH³E : isContr (coHom 3 (GysinS1.E'))
-- -- -- isContrH³E =
-- -- --   subst isContr
-- -- --         (sym (isoToPath (compIso (Iso1 0) (Iso2' 0)))
-- -- --        ∙ cong (coHom 3) (sym (isoToPath IsoE' ∙ IsoE2)))
-- -- --     (ll5 0 (snotz ∘ sym))

-- -- -- isContrH⁴E : isContr (coHom 4 (GysinS1.E'))
-- -- -- isContrH⁴E =
-- -- --   subst isContr
-- -- --         (sym (isoToPath (compIso (Iso1 1) (Iso2' 1)))
-- -- --        ∙ cong (coHom 4) (sym (isoToPath IsoE' ∙ IsoE2)))
-- -- --     (ll5 1 λ p → snotz (sym (cong predℕ p)))

-- -- -- genH2 = GysinS1.e

-- -- -- S³→Groupoid : ∀ {ℓ} (P : join S¹ S¹ → Type ℓ)
-- -- --             → ((x : _) → isGroupoid (P x))
-- -- --             → P (inl base)
-- -- --             → (x : _) → P x
-- -- -- S³→Groupoid P grp b =
-- -- --   transport (λ i → (x : (sym (isoToPath S³IsojoinS¹S¹) ∙ isoToPath IsoS³S3) (~ i))
-- -- --                  → P (transp (λ j → (sym (isoToPath S³IsojoinS¹S¹) ∙ isoToPath IsoS³S3) (~ i ∧ ~ j)) i x))
-- -- --             (sphereElim _ (λ _ → grp _) b)

-- -- -- TotalHopf→Gpd : ∀ {ℓ} (P : fibS1.TotalSpaceHopf' → Type ℓ)
-- -- --             → ((x : _) → isGroupoid (P x))
-- -- --             → P (inl base)
-- -- --             → (x : _) → P x
-- -- -- TotalHopf→Gpd P grp b =
-- -- --   transport (λ i → (x : sym (isoToPath IsoTotalHopf') i)
-- -- --                  → P (transp (λ j → isoToPath IsoTotalHopf' (~ i ∧ ~ j)) i x))
-- -- --     (S³→Groupoid _ (λ _ → grp _) b)

-- -- -- TotalHopf→Gpd' : ∀ {ℓ} (P : Σ (S₊ 2) fibS1.Hopf → Type ℓ)
-- -- --             → ((x : _) → isGroupoid (P x))
-- -- --             → P (north , base)
-- -- --             → (x : _) → P x
-- -- -- TotalHopf→Gpd' P grp b =
-- -- --   transport (λ i → (x : ua (_ , fibS1.isEquivTotalSpaceHopf'→TotalSpace) i)
-- -- --           → P (transp (λ j → ua (_ , fibS1.isEquivTotalSpaceHopf'→TotalSpace) (i ∨ j)) i x))
-- -- --           (TotalHopf→Gpd _ (λ _ → grp _) b)

-- -- -- CP2→Groupoid : ∀ {ℓ} {P : CP2 → Type ℓ}
-- -- --                → ((x : _) → is2Groupoid (P x))
-- -- --                → (b : P (inl tt))
-- -- --                → (s2 : ((x : _) → P (inr x)))
-- -- --                → PathP (λ i → P (push (inl base) i)) b (s2 north)
-- -- --                → (x : _) → P x
-- -- -- CP2→Groupoid {P = P} grp b s2 pp (inl x) = b
-- -- -- CP2→Groupoid {P = P} grp b s2 pp (inr x) = s2 x
-- -- -- CP2→Groupoid {P = P} grp b s2 pp (push a i₁) = h23 a i₁
-- -- --   where
-- -- --   h23 : (a : fibS1.TotalSpaceHopf') → PathP (λ i → P (push a i)) b (s2 _) 
-- -- --   h23 = TotalHopf→Gpd _  (λ _ → isOfHLevelPathP' 3 (grp _) _ _) pp

-- -- -- mm : (S₊ 2 → coHomK 2) → (CP2 → coHomK 2)
-- -- -- mm f =  λ { (inl x) → 0ₖ _
-- -- --           ; (inr x) → f x -ₖ f north
-- -- --           ; (push a i) → TotalHopf→Gpd (λ x → 0ₖ 2 ≡ f (fibS1.TotalSpaceHopf'→TotalSpace x .fst) -ₖ f north)
-- -- --                                          (λ _ → isOfHLevelTrunc 4 _ _)
-- -- --                                          (sym (rCancelₖ 2 (f north)))
-- -- --                                          a i}

-- -- -- e-inv : coHomGr 2 (S₊ 2) .fst → coHomGr 2 CP2 .fst
-- -- -- e-inv = sMap mm

-- -- -- cancel : (f : CP2 → coHomK 2) → ∥ mm (f ∘ inr) ≡ f ∥
-- -- -- cancel f =
-- -- --   pRec squash
-- -- --     (λ p → pRec squash
-- -- --                 (λ f → ∣ funExt f ∣)
-- -- --                 (zz2 p))
-- -- --     (h1 (f (inl tt)))
-- -- --   where
-- -- --   h1 : (x : coHomK 2) →  ∥ x ≡ 0ₖ 2 ∥
-- -- --   h1 = coHomK-elim _ (λ _ → isOfHLevelSuc 1 squash) ∣ refl ∣ 

-- -- --   zz2 : (p : f (inl tt) ≡ 0ₖ 2) → ∥ ((x : CP2) → mm (f ∘ inr) x ≡ f x) ∥
-- -- --   zz2 p = trRec squash (λ pp → 
-- -- --     ∣ CP2→Groupoid (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
-- -- --                  (sym p)
-- -- --                  (λ x → (λ i → f (inr x) -ₖ f (push (inl base) (~ i)))
-- -- --                        ∙∙ (λ i → f (inr x) -ₖ p i)
-- -- --                        ∙∙ rUnitₖ 2 (f (inr x)))
-- -- --                  pp ∣)
-- -- --                 l
-- -- --     where
-- -- --     l : hLevelTrunc 1 (PathP ((λ i₁ → mm (f ∘ inr) (push (inl base) i₁) ≡ f (push (inl base) i₁)))
-- -- --               (sym p)
-- -- --               (((λ i₁ → f (inr north) -ₖ f (push (inl base) (~ i₁))) ∙∙
-- -- --                 (λ i₁ → f (inr north) -ₖ p i₁) ∙∙ rUnitₖ 2 (f (inr north)))))
-- -- --     l = isConnectedPathP 1 (isConnectedPath 2 (isConnectedKn 1) _ _) _ _ .fst

-- -- -- e' : GroupIso (coHomGr 2 CP2) (coHomGr 2 (S₊ 2))
-- -- -- Iso.fun (fst e') = sMap (_∘ inr)
-- -- -- Iso.inv (fst e') = e-inv
-- -- -- Iso.rightInv (fst e') =
-- -- --   sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- -- --       λ f → trRec {B = Iso.fun (fst e') (Iso.inv (fst e') ∣ f ∣₂) ≡ ∣ f ∣₂}
-- -- --       (isOfHLevelPath 2 squash₂ _ _)
-- -- --       (λ p → cong ∣_∣₂ (funExt λ x → cong (λ y → (f x) -ₖ y) p ∙ rUnitₖ 2 (f x)))
-- -- --       (Iso.fun (PathIdTruncIso _) (isContr→isProp (isConnectedKn 1) ∣ f north ∣ ∣ 0ₖ 2 ∣))
-- -- -- Iso.leftInv (fst e') =
-- -- --   sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- -- --     λ f → pRec (squash₂ _ _) (cong ∣_∣₂) (cancel f)
-- -- -- snd e' =
-- -- --   makeIsGroupHom
-- -- --     (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ f g → refl)

-- -- -- grrg : GroupIso (coHomGr 2 CP2) ℤGroup
-- -- -- grrg = compGroupIso e' (Hⁿ-Sⁿ≅ℤ 1)

-- -- -- ⌣hom : GroupEquiv (coHomGr 2 CP2) (coHomGr 4 CP2)
-- -- -- fst (fst ⌣hom) = GysinS1.⌣-hom 2 .fst
-- -- -- snd (fst ⌣hom) = subst isEquiv (cong fst (GysinS1.ϕ∘j≡ 2)) h23
-- -- --   where
-- -- --   h23 : isEquiv (GysinS1.ϕ∘j 2 .fst)
-- -- --   h23 =
-- -- --     SES→Iso
-- -- --       (GroupPath _ _ .fst (invGroupEquiv
-- -- --         (isContr→≃Unit isContrH³E
-- -- --         , makeIsGroupHom λ _ _ → refl)))
-- -- --       (GroupPath _ _ .fst (invGroupEquiv
-- -- --         (isContr→≃Unit isContrH⁴E
-- -- --         , makeIsGroupHom λ _ _ → refl)))
-- -- --       (GysinS1.susp∘ϕ 1)
-- -- --       (GysinS1.ϕ∘j 2)
-- -- --       (GysinS1.p-hom 4)
-- -- --       (GysinS1.Ker-ϕ∘j⊂Im-Susp∘ϕ _)
-- -- --       (GysinS1.Ker-p⊂Im-ϕ∘j _)
-- -- -- snd ⌣hom = GysinS1.⌣-hom 2 .snd

-- -- -- isGenerator≃ℤ : ∀ {ℓ} (G : Group ℓ) (g : fst G)
-- -- --                → Type _
-- -- -- isGenerator≃ℤ G g =
-- -- --   ∃[ e ∈ GroupIso G ℤGroup ] abs (Iso.fun (fst e) g) ≡ 1



-- -- -- -- ⌣-pres1 : ∀ {ℓ} (G : Type ℓ) (n : ℕ) → Type _
-- -- -- -- ⌣-pres1 G n =
-- -- -- --   Σ[ x ∈ coHomGr n G .fst ]
-- -- -- --     isGenerator≃ℤ (coHomGr n G) x × isGenerator≃ℤ (coHomGr (n +' n) G) (x ⌣ x)

-- -- -- -- genr : coHom 2 CP2
-- -- -- -- genr = ∣ CP2→Groupoid (λ _ → isOfHLevelTrunc 4)
-- -- -- --                       (0ₖ _)
-- -- -- --                       ∣_∣
-- -- -- --                       refl ∣₂

-- -- -- -- ≡CP2 : (f g : CP2 → coHomK 2) → ∥ f ∘ inr ≡ g ∘ inr ∥ → Path (coHom 2 CP2) ∣ f ∣₂ ∣ g ∣₂
-- -- -- -- ≡CP2 f g = pRec (squash₂ _ _)
-- -- -- --            (λ p → pRec (squash₂ _ _) (λ id → trRec (squash₂ _ _)
-- -- -- --                                           (λ pp → cong ∣_∣₂
-- -- -- --                                             (funExt (CP2→Groupoid (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
-- -- -- --                                                     id
-- -- -- --                                                     (funExt⁻ p)
-- -- -- --                                                     (compPathR→PathP pp))))
-- -- -- --                                               (pp2 (f (inl tt)) (g (inl tt)) id
-- -- -- --                                                 (cong f (push (inl base)) ∙ (funExt⁻ p north) ∙ cong g (sym (push (inl base))))))
-- -- -- --                                           (conn (f (inl tt)) (g (inl tt))))

-- -- -- --   where
-- -- -- --   conn : (x y : coHomK 2) → ∥ x ≡ y ∥
-- -- -- --   conn = coHomK-elim _ (λ _ → isSetΠ λ _ → isOfHLevelSuc 1 squash)
-- -- -- --            (coHomK-elim _ (λ _ → isOfHLevelSuc 1 squash) ∣ refl ∣)

-- -- -- --   pp2 : (x y : coHomK 2) (p q : x ≡ y) → hLevelTrunc 1 (p ≡ q)
-- -- -- --   pp2 x y = λ p q → Iso.fun (PathIdTruncIso _) (isContr→isProp (isConnectedPath _ (isConnectedKn 1) x y) ∣ p ∣ ∣ q ∣)

-- -- -- -- rUnit* : (x : S¹) → x * base ≡ x
-- -- -- -- rUnit* base = refl
-- -- -- -- rUnit* (loop i₁) = refl

-- -- -- -- meridP : (a x : S¹) → Path (Path (coHomK 2) _ _) (cong ∣_∣ₕ (merid (a * x) ∙ sym (merid base)))
-- -- -- --                                                   ((cong ∣_∣ₕ (merid a ∙ sym (merid base))) ∙ (cong ∣_∣ₕ (merid x ∙ sym (merid base))))
-- -- -- -- meridP = wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
-- -- -- --            (λ x → lUnit _ ∙ cong (_∙ cong ∣_∣ₕ (merid x ∙ sym (merid base))) (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
-- -- -- --            (λ x → (λ i → cong ∣_∣ₕ (merid (rUnit* x i) ∙ sym (merid base)))
-- -- -- --                ∙∙ rUnit _
-- -- -- --                ∙∙ cong (cong ∣_∣ₕ (merid x ∙ sym (merid base)) ∙_)
-- -- -- --                        (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
-- -- -- --            (sym (l (cong ∣_∣ₕ (merid base ∙ sym (merid base)))
-- -- -- --                 (cong (cong ∣_∣ₕ) (sym (rCancel (merid base))))))
-- -- -- --   where
-- -- -- --   l : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (P : refl ≡ p)
-- -- -- --     → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P
-- -- -- --   l p = J (λ p P → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P) refl

-- -- -- -- lemmie : (x : S¹) → ptSn 1 ≡ x * (invLooper x)
-- -- -- -- lemmie base = refl
-- -- -- -- lemmie (loop i) j =
-- -- -- --   hcomp (λ r → λ {(i = i0) → base ; (i = i1) → base ; (j = i0) → base})
-- -- -- --         base

-- -- -- -- mmInv : (x : S¹) → Path (Path (coHomK 2) _ _)
-- -- -- --                          (cong ∣_∣ₕ (merid (invLooper x) ∙ sym (merid base)))
-- -- -- --                          (cong ∣_∣ₕ (sym (merid x ∙ sym (merid base))))
-- -- -- -- mmInv x = (lUnit _
-- -- -- --        ∙∙ cong (_∙ cong ∣_∣ₕ (merid (invLooper x) ∙ sym (merid base))) (sym (lCancel (cong ∣_∣ₕ (merid x ∙ sym (merid base))))) ∙∙ sym (assoc _ _ _))
-- -- -- --        ∙∙ cong (sym (cong ∣_∣ₕ (merid x ∙ sym (merid base))) ∙_) hh
-- -- -- --        ∙∙ (assoc _ _ _
-- -- -- --        ∙∙ cong (_∙ (cong ∣_∣ₕ (sym (merid x ∙ sym (merid base))))) (lCancel (cong ∣_∣ₕ (merid x ∙ sym (merid base))))
-- -- -- --        ∙∙ sym (lUnit _))
-- -- -- --   where
-- -- -- --   hh : cong ∣_∣ₕ (merid x ∙ sym (merid base)) ∙ cong ∣_∣ₕ (merid (invLooper x) ∙ sym (merid base))
-- -- -- --      ≡ cong ∣_∣ₕ (merid x ∙ sym (merid base)) ∙ cong ∣_∣ₕ (sym (merid x ∙ sym (merid base)))
-- -- -- --   hh = sym (meridP x (invLooper x)) ∙ ((λ i → cong ∣_∣ₕ (merid (lemmie x (~ i)) ∙ sym (merid base))) ∙ cong (cong ∣_∣ₕ) (rCancel (merid base))) ∙ sym (rCancel _)

-- -- -- -- commS1 : (a x : S¹) → a * x ≡ x * a
-- -- -- -- commS1 = wedgeconFun _ _ (λ _ _ → isGroupoidS¹ _ _)
-- -- -- --          (sym ∘ rUnit*)
-- -- -- --          rUnit*
-- -- -- --          refl

-- -- -- -- s233 : (a x : S¹) → (invEq (fibS1.μ-eq a) x) * a ≡ (invLooper a * x) * a
-- -- -- -- s233 a x = secEq (fibS1.μ-eq a) x ∙∙ cong (_* x) (lemmie a) ∙∙ assocHSpace.μ-assoc S1-AssocHSpace a (invLooper a) x ∙ commS1 _ _

-- -- -- -- ss23 : (a x : S¹) → invEq (fibS1.μ-eq a) x ≡ invLooper a * x
-- -- -- -- ss23 a x = sym (retEq (fibS1.μ-eq a) (invEq (fibS1.μ-eq a) x))
-- -- -- --         ∙∙ cong (invEq (fibS1.μ-eq a)) (s233 a x)
-- -- -- --         ∙∙ retEq (fibS1.μ-eq a) (invLooper a * x)

-- -- -- -- ll : GysinS1.e ≡ genr
-- -- -- -- ll = ≡CP2 _ _ ∣ funExt (λ x → funExt⁻ (cong fst (ll32 x)) south) ∣
-- -- -- --   where
-- -- -- --   kr : (x : Σ (S₊ 2) fibS1.Hopf) → Path (hLevelTrunc 4 _) ∣ fst x ∣ ∣ north ∣
-- -- -- --   kr = uncurry λ { north → λ y → cong ∣_∣ₕ (merid base ∙ sym (merid y))
-- -- -- --                  ; south → λ y → cong ∣_∣ₕ (sym (merid y))
-- -- -- --                  ; (merid a i) → lem a i}
-- -- -- --     where
-- -- -- --     lem : (a : S¹) → PathP (λ i → (y : fibS1.Hopf (merid a i)) → Path (HubAndSpoke (Susp S¹) 3) ∣ merid a i ∣ ∣ north ∣)
-- -- -- --                             (λ y → cong ∣_∣ₕ (merid base ∙ sym (merid y)))
-- -- -- --                             λ y → cong ∣_∣ₕ (sym (merid y))
-- -- -- --     lem a = toPathP (funExt λ x → cong (transport ((λ i₁ → Path (HubAndSpoke (Susp S¹) 3) ∣ merid a i₁ ∣ ∣ north ∣)))
-- -- -- --                                         ((λ i → (λ z → cong ∣_∣ₕ (merid base
-- -- -- --                                                                ∙ sym (merid (transport (λ j → uaInvEquiv (fibS1.μ-eq a) (~ i) j) x))) z))
-- -- -- --                                         ∙ λ i → cong ∣_∣ₕ (merid base
-- -- -- --                                                ∙ sym (merid (transportRefl (invEq (fibS1.μ-eq a) x) i))))
-- -- -- --                                ∙∙ (λ i → transp (λ i₁ → Path (HubAndSpoke (Susp S¹) 3) ∣ merid a (i₁ ∨ i) ∣ ∣ north ∣) i
-- -- -- --                                                  (compPath-filler' (cong ∣_∣ₕ (sym (merid a)))
-- -- -- --                                                    (cong ∣_∣ₕ (merid base ∙ sym (merid (ss23 a x i)))) i))
-- -- -- --                                ∙∙ cong ((cong ∣_∣ₕ) (sym (merid a)) ∙_) (cong (cong ∣_∣ₕ) (cong sym (symDistr (merid base) (sym (merid (invLooper a * x)))))
-- -- -- --                                                                      ∙ cong sym (meridP (invLooper a) x)
-- -- -- --                                                                      ∙ symDistr ((cong ∣_∣ₕ) (merid (invLooper a) ∙ sym (merid base)))
-- -- -- --                                                                                  ((cong ∣_∣ₕ) (merid x ∙ sym (merid base)))
-- -- -- --                                                                      ∙ isCommΩK 2 (sym (λ i₁ → ∣ (merid x ∙ (λ i₂ → merid base (~ i₂))) i₁ ∣))
-- -- -- --                                                                                   (sym (λ i₁ → ∣ (merid (invLooper a) ∙ (λ i₂ → merid base (~ i₂))) i₁ ∣))
-- -- -- --                                                                      ∙ cong₂ _∙_ (cong sym (mmInv a) ∙ cong-∙ ∣_∣ₕ (merid a) (sym (merid base)))
-- -- -- --                                                                                  (cong (cong ∣_∣ₕ) (symDistr (merid x) (sym (merid base))) ∙ cong-∙ ∣_∣ₕ (merid base) (sym (merid x))))
-- -- -- --                                ∙∙ (λ j → (λ i₁ → ∣ merid a (~ i₁ ∨ j) ∣) ∙
-- -- -- --                                           ((λ i₁ → ∣ merid a (i₁ ∨ j) ∣) ∙
-- -- -- --                                            (λ i₁ → ∣ merid base (~ i₁ ∨ j) ∣))
-- -- -- --                                           ∙
-- -- -- --                                           (λ i₁ → ∣ merid base (i₁ ∨ j) ∣) ∙
-- -- -- --                                            (λ i₁ → ∣ merid x (~ i₁) ∣ₕ))
-- -- -- --                                ∙∙ sym (lUnit _)
-- -- -- --                                ∙∙ sym (assoc _ _ _)
-- -- -- --                                ∙∙ (sym (lUnit _) ∙ sym (lUnit _) ∙ sym (lUnit _)))

-- -- -- --   psst : (x : S₊ 2) → Q (CP2 , inl tt) fibr (inr x) →∙ coHomK-ptd 2
-- -- -- --   fst (psst x) north = ∣ north ∣
-- -- -- --   fst (psst x) south = ∣ x ∣
-- -- -- --   fst (psst x) (merid a i₁) = kr (x , a) (~ i₁)
-- -- -- --   snd (psst x) = refl

-- -- -- --   ll32-fst : GysinS1.c (inr north) .fst ≡ psst north .fst
-- -- -- --   ll32-fst = cong fst (GysinS1.cEq (inr north) ∣ push (inl base) ∣₂)
-- -- -- --            ∙ (funExt l)
-- -- -- --     where
-- -- -- --     l : (qb : _) →
-- -- -- --          ∣ (subst (fst ∘ Q (CP2 , inl tt) fibr) (sym (push (inl base))) qb) ∣
-- -- -- --       ≡ psst north .fst qb
-- -- -- --     l north = refl
-- -- -- --     l south = cong ∣_∣ₕ (sym (merid base))
-- -- -- --     l (merid a i) j =
-- -- -- --       hcomp (λ k → λ { (i = i0) → ∣ merid a (~ k ∧ j) ∣
-- -- -- --                       ; (i  = i1) → ∣ merid base (~ j) ∣
-- -- -- --                       ; (j = i0) → ∣ transportRefl (merid a i) (~ k) ∣
-- -- -- --                       ; (j = i1) → ∣ compPath-filler (merid base) (sym (merid a)) k (~ i) ∣ₕ})
-- -- -- --             (hcomp (λ k → λ { (i = i0) → ∣ merid a (j ∨ ~ k) ∣
-- -- -- --                       ; (i  = i1) → ∣ merid base (~ j ∨ ~ k) ∣
-- -- -- --                       ; (j = i0) → ∣ merid a (~ k ∨ i) ∣
-- -- -- --                       ; (j = i1) → ∣ merid base (~ i ∨ ~ k) ∣ₕ})
-- -- -- --                    ∣ south ∣)

-- -- -- --   is-setHepl : (x : S₊ 2) → isSet (Q (CP2 , inl tt) fibr (inr x) →∙ coHomK-ptd 2)
-- -- -- --   is-setHepl = sphereElim _ (λ _ → isProp→isOfHLevelSuc 1 (isPropIsOfHLevel 2))
-- -- -- --                             (isOfHLevel↑∙' 0 1)

-- -- -- --   ll32 : (x : S₊ 2) →  (GysinS1.c (inr x) ≡ psst x)
-- -- -- --   ll32 = sphereElim _ (λ x → isOfHLevelPath 2 (is-setHepl x) _ _)
-- -- -- --          (→∙Homogeneous≡ (isHomogeneousKn _) ll32-fst)

-- -- -- -- isGenerator≃ℤ-e : isGenerator≃ℤ (coHomGr 2 CP2) GysinS1.e
-- -- -- -- isGenerator≃ℤ-e =
-- -- -- --   subst (isGenerator≃ℤ (coHomGr 2 CP2)) (sym ll)
-- -- -- --     ∣ grrg , refl ∣

-- -- -- -- ⌣-pres1-CP2 : ⌣-pres1 CP2 2
-- -- -- -- ⌣-pres1-CP2 =
-- -- -- --     GysinS1.e
-- -- -- --   , (isGenerator≃ℤ-e
-- -- -- --   , ∣ compGroupIso (GroupEquiv→GroupIso (invGroupEquiv ⌣hom)) grrg
-- -- -- --   , {!!} ∣)


-- -- -- -- {-
-- -- -- -- Goal: snd (v' (pt A) (push a i₁)) ≡
-- -- -- --       ua-gluePt (μ-eq (snd a)) i₁ (fst a)
-- -- -- -- ———— Boundary ——————————————————————————————————————————————
-- -- -- -- i₁ = i0 ⊢ HSpace.μₗ e (fst a)
-- -- -- -- i₁ = i1 ⊢ HSpace.μₗ e (HSpace.μ e (fst a) (snd a))
-- -- -- -- -}
    
-- -- -- --   --   help : (x : _) → (v' (pt A)) x ≡ TotalSpaceHopf'→TotalSpace x
-- -- -- --   --   help (inl x) = ΣPathP (refl , HSpace.μₗ e x)
-- -- -- --   --   help (inr x) = ΣPathP (refl , (HSpace.μₗ e x))
-- -- -- --   --   help (push (x , y) i) j =
-- -- -- --   --     comp (λ _ → Σ (Susp (typ A)) Hopf)
-- -- -- --   --          (λ k → λ {(i = i0) → merid y i , HSpace.μₗ e x j
-- -- -- --   --                   ; (i = i1) → merid y i , assocHSpace.μ-assoc-filler e-ass x y j k
-- -- -- --   --                   ; (j = i0) → merid y i , hfill
-- -- -- --   --                                             (λ j → λ { (i = i0) → HSpace.μ e (pt A) x
-- -- -- --   --                                                       ; (i = i1) → assocHSpace.μ-assoc e-ass (pt A) x y j
-- -- -- --   --                                                })
-- -- -- --   --                                             (inS (ua-gluePt (μ-eq y) i (HSpace.μ e (pt A) x)))
-- -- -- --   --                                             k
-- -- -- --   --                   ; (j = i1) → merid y i , ua-gluePt (μ-eq y) i x})
-- -- -- --   --          (merid y i , ua-gluePt (μ-eq y) i (HSpace.μₗ e x j))
-- -- -- --   --     where
-- -- -- --   --     open import Cubical.Foundations.Path

-- -- -- --   --     PPΣ : ∀ {ℓ} {A : Type ℓ} {f : A ≃ A} (p : f ≡ f) → {!!}
-- -- -- --   --     PPΣ = {!!}

-- -- -- --   --     V : PathP (λ i₁ → hcomp
-- -- -- --   --                      (λ { j (i₁ = i0) → HSpace.μ e (pt A) x
-- -- -- --   --                         ; j (i₁ = i1) → assocHSpace.μ-assoc e-ass (pt A) x y j
-- -- -- --   --                         })
-- -- -- --   --                      (ua-gluePt (μ-eq y) i₁ (HSpace.μ e (pt A) x)) ≡
-- -- -- --   --                         ua-gluePt (μ-eq y) i₁ x)
-- -- -- --   --                (HSpace.μₗ e x)
-- -- -- --   --                (HSpace.μₗ e (HSpace.μ e x y)) -- (HSpace.μₗ e (HSpace.μ e (fst a) (snd a)))
-- -- -- --   --     V = transport (λ z → {!PathP (λ i₁ → hfill
-- -- -- --   --                      (λ { j (i₁ = i0) → HSpace.μ e (pt A) x
-- -- -- --   --                         ; j (i₁ = i1) → assocHSpace.μ-assoc e-ass (pt A) x y j
-- -- -- --   --                         })
-- -- -- --   --                      (inS (ua-gluePt (μ-eq y) i₁ (HSpace.μ e (pt A) x))) z ≡ ua-gluePt (μ-eq y) i₁ x)
-- -- -- --   --                                 ? ?!})
-- -- -- --   --                   {!hfill
-- -- -- --   --                      (λ { j (i₁ = i0) → HSpace.μ e (pt A) x
-- -- -- --   --                         ; j (i₁ = i1) → assocHSpace.μ-assoc e-ass (pt A) x y j
-- -- -- --   --                         })
-- -- -- --   --                      (inS (ua-gluePt (μ-eq y) i₁ (HSpace.μ e (pt A) x))) ?!} -- toPathP ({!!} ∙∙ {!!} ∙∙ {!!}) -- toPathP (flipSquare {!!}) -- hcomp {!!} {!!}

-- -- -- --   -- P : Pushout {A = TotalSpaceHopf'} (λ _ → tt) induced → Type _
-- -- -- --   -- P (inl x) = typ A
-- -- -- --   -- P (inr x) = Hopf x
-- -- -- --   -- P (push a i₁) = ua (v a) i₁
