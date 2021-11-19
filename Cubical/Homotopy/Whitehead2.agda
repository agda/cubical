{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Whitehead2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec)
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Homotopy.HopfInvariant.Homomorphism
open import Cubical.Homotopy.Hopf
open import Cubical.Homotopy.HSpace

open import Cubical.HITs.Join
open import Cubical.HITs.Sn
open import Cubical.HITs.Wedge
private
  variable
    ℓ : Level
    A B : Pointed ℓ

open import Cubical.Homotopy.Group.Base
open import Cubical.HITs.SetTruncation renaming (map to sMap ; elim2 to sElim2 ; elim to sElim)
open import Cubical.HITs.PropositionalTruncation renaming (map to pMap ; rec to pRec ; elim to pElim)
open import Cubical.Algebra.Group
open import Cubical.Foundations.Pointed.Homogeneous

Hopfie = S¹Hopf.TotalHopf
Hopfie∙ : Pointed _
Hopfie∙ = Hopfie , (north , base)

open import Cubical.Homotopy.Hopf
open import Cubical.Homotopy.HSpace
open import Cubical.HITs.S1

module S1Hopf =
  Hopf S1-AssocHSpace
       (toPropElim (λ _ → isPropΠ λ _ → squash) isConnectedS¹)

Hopf' : Type _
Hopf' = Σ[ x ∈ S₊ 2 ] S1Hopf.Hopf x

Hopf'∙ : Pointed _
Hopf'∙ = Hopf' , north , base

{-
π₃ A → π₃ Total → π₃ 2

given f : Total → S²
want : ∥ (f : S² → S²) ∥ s.t. (x : S²) → Hopf (f x) 

-}

loop2 : typ ( (Ω^ 2) (S₊∙ 2))
loop2 i j =
  hcomp (λ k → λ { (i = i0) → north
                  ; (i = i1) → north
                  ; (j = i0) → rCancel (merid base) k i
                  ; (j = i1) → rCancel (merid base) k i})
        ((merid (loop j) ∙ sym (merid base)) i)

EHMap : S₊∙ 3 →∙ S₊∙ 2
fst EHMap north = north
fst EHMap south = north
fst EHMap (merid north i) = north
fst EHMap (merid south i) = north
fst EHMap (merid (merid base i₁) i) = north
fst EHMap (merid (merid (loop k) j) i) =
        (sym (rCancel loop2) ∙∙ (EH 0 loop2 (sym loop2)) ∙∙ lCancel loop2) i j k
snd EHMap = refl

Ω3 : typ ((Ω^ 3) (S₊∙ 2))
Ω3 = (sym (rCancel loop2) ∙∙ (EH 0 loop2 (sym loop2)) ∙∙ lCancel loop2)

Ωa→ : S₊ 2 → typ ((Ω^ 4) {!!})
Ωa→ = {!!}

+π₃S2' : S₊ 2 → S₊ 2 → S₊ 2
+π₃S2' north y = north
+π₃S2' south y = north
+π₃S2' (merid base i) y = north
+π₃S2' (merid (loop j) i) north = north
+π₃S2' (merid (loop j) i) south = north
+π₃S2' (merid (loop j) i) (merid base i₁) = north
+π₃S2' (merid (loop j) i) (merid (loop j2) i2) =
 ((sym (rCancel Ω3) ∙∙ EH 1 Ω3 (sym Ω3) ∙∙ lCancel Ω3) i j i2 j2)

cool : {!!}
cool = {!!}

check : S₊ 2 → Type
check = {!!}


+π₃S2 : typ ((Ω^ 3) (S₊∙ 2))
     → typ ((Ω^ 3) (S₊∙ 2))
     → typ ((Ω^ 3) (S₊∙ 2))
+π₃S2 = {!!}

themap : (S₊∙ 3 →∙ S₊∙ 2) → {!!}
themap = {!!}

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure

fiberS¹ : Iso (fiber (fst EHMap) north) (coHomK 1)
Iso.fun fiberS¹ (x , y) = {!fst EHMap x!}
Iso.inv fiberS¹ = trRec {!!} λ { base → north , refl ; (loop i) → north , loop2 i}
Iso.rightInv fiberS¹ = Trunc.elim {!!} {!!}
Iso.leftInv fiberS¹ = {!!}

rr : hLevelTrunc 5 {!!} → TypeOfHLevel _ 5
rr = {!!}

HopfIsh : ∀ {ℓ} {A : Type ℓ} → Iso (Hopf' → A) (Σ[ f ∈ (S₊ 2 → A) ] ((x : S₊ 2) → S1Hopf.Hopf x))
Iso.fun HopfIsh f = (λ x → f (x , {!x!})) , {!!}
Iso.inv HopfIsh f = {!!}
Iso.rightInv HopfIsh = {!!}
Iso.leftInv HopfIsh = {!!}

Code : (x : S₊ 2) → isContr ∥ (S1Hopf.Hopf x → S₊ 2) ∥₂
Code = sphereElim 1 (λ _ → isProp→isSet isPropIsContr)
         (subst isContr (cong ∥_∥₂ (isoToPath (invIso IsoFunSpaceS¹)))
           (∣ north , refl ∣₂
           , Cubical.HITs.SetTruncation.elim
              (λ _ → isSetPathImplicit)
              (uncurry
                (sphereElim 1
                  (λ _ → isSetΠ λ _ → isSetPathImplicit)
                  (λ y → trRec (squash₂ _ _)
                    (λ p → cong ∣_∣₂ λ i → north , p i)
                    (Iso.fun (PathIdTruncIso _)
                      (isContr→isProp (isConnectedPathSⁿ 1 north north) ∣ refl ∣ ∣ y ∣)))))))

Iso1 : Iso ∥ Hopf'∙ →∙ S₊∙ 2 ∥₂ (∥ (S₊∙ 2 →∙ S₊∙ 2) ∥₂)
Iso.fun Iso1 = sMap {!!}
Iso.inv Iso1 = sMap {!λ f →!}
Iso.rightInv Iso1 = {!!}
Iso.leftInv Iso1 = {!!}

-- Σ→∙ : ∀ {ℓ} {A : Pointed ℓ}
--     → Iso (A →∙ Hopfie∙)
--            (Σ[ f ∈ ((fst A) → S₊ 2) ]
--              (Σ[ g ∈ ((a : fst A) → S¹Hopf.HopfSuspS¹ (f a)) ]
--                 Σ[ p ∈ f (pt A) ≡ north ]
--                  PathP (λ i → S¹Hopf.HopfSuspS¹ (p i)) (g (pt A)) base))
-- Σ→∙ = {!!}

-- Σ→∙' : ∀ {ℓ} {A : Pointed ℓ}
--     → Iso (A →∙ Hopfie∙)
--            (Σ[ f ∈ (A →∙ S₊∙ 2) ]
--              (Σ[ g ∈ ((a : fst A) → S¹Hopf.HopfSuspS¹ (fst f a)) ]
--                 (PathP (λ i → S¹Hopf.HopfSuspS¹ (snd f i)) (g (pt A)) base)))
-- Σ→∙' = iso {!!} {!!} {!!} {!!}


-- →fun : ∥ S₊∙ 2 →∙ S₊∙ 2 ∥₂ → ∥ (Hopfie∙ →∙ S₊∙ 2) ∥₂
-- →fun = sMap λ f → fst f ∘ fst , snd f

-- isEquivLem : isEquiv →fun
-- equiv-proof isEquivLem =
--   sElim {!!}
--     λ f → ({!f!} , {!!}) , {!!}

-- Iso3 : Iso (Hopfie∙ →∙ S₊∙ 2)
--            (Σ[ f ∈ (S₊∙ 2 →∙ S₊∙ 2) ]
--              Σ[ g ∈ ((x : S₊ 2) → S¹Hopf.HopfSuspS¹ (fst f x)) ]
--                PathP (λ i → S¹Hopf.HopfSuspS¹ (snd f i)) (g north) base)
-- Iso3 = {!!}
--   where

--   fib = S¹Hopf.HopfSuspS¹

--   contrFst' : {x y : S₊ 2}
--             → (t1 t2 : S¹Hopf.HopfSuspS¹ x)
--             → (s1 s2 : S¹Hopf.HopfSuspS¹ y)
--             → (p q : x ≡ y)
--             → (pp : p ≡ q)
--             → (pp1 : PathP (λ j → S¹Hopf.HopfSuspS¹ (p j)) t1 s1)
--             → (pp2 : PathP (λ j → S¹Hopf.HopfSuspS¹ (q j)) t2 s2)
--             → (pp3 : t1 ≡ t2)
--             → (pp4 : s1 ≡ s2)
--             → isContr ∥ SquareP (λ i j → S¹Hopf.HopfSuspS¹ (pp i j))
--                          pp1
--                          pp2
--                          pp3
--                          pp4 ∥₂
--   contrFst' {x = x} {y = y} t1 t2 s1 s2 p q =
--     J (λ q pp → (pp1 : PathP (λ j → S¹Hopf.HopfSuspS¹ (p j)) t1 s1)
--             → (pp2 : PathP (λ j → S¹Hopf.HopfSuspS¹ (q j)) t2 s2)
--             → (pp3 : t1 ≡ t2)
--             → (pp4 : s1 ≡ s2)
--             → isContr ∥ SquareP (λ i j → S¹Hopf.HopfSuspS¹ (pp i j)) pp1 pp2 pp3 pp4 ∥₂)
--       (postJ x y p t1 t2 s1 s2)
--     where
--     postJ : (x y : S₊ 2)
--             (p : x ≡ y)
--          → (t1 t2 : S¹Hopf.HopfSuspS¹ x)
--          → (s1 s2 : S¹Hopf.HopfSuspS¹ y)
--          → (pp1 : PathP (λ j → S¹Hopf.HopfSuspS¹ (p j)) t1 s1)
--          → (pp2 : PathP (λ j → S¹Hopf.HopfSuspS¹ (p j)) t2 s2)
--          → (pp3 : t1 ≡ t2)
--          → (pp4 : s1 ≡ s2)
--          → isContr ∥ SquareP (λ i j → S¹Hopf.HopfSuspS¹ (p j)) pp1 pp2 pp3 pp4 ∥₂
--     postJ =
--       sphereElim
--         1
--         (λ _ → isSetΠ3
--           λ _ _ _ → isSetΠ3
--             λ _ _ _ → isSetΠ3
--               λ _ _ _ → isSetΠ λ _ → isProp→isSet isPropIsContr)
--         λ y → J (λ y p → (t3 t4 : S¹) (s3 s4 : S¹Hopf.HopfSuspS¹ y)
--       (pp1 : PathP (λ j → S¹Hopf.HopfSuspS¹ (p j)) t3 s3)
--       (pp2 : PathP (λ j → S¹Hopf.HopfSuspS¹ (p j)) t4 s4)
--       (pp3 : t3 ≡ t4) (pp4 : s3 ≡ s4) →
--       isContr
--       ∥ SquareP (λ i j → S¹Hopf.HopfSuspS¹ (p j)) pp1 pp2 pp3 pp4 ∥₂)
--       {!!}

--   contrFst : (x y : S₊ 2)
--              (p : north ≡ x)
--              (gn : fib x)
--              (pp : PathP (λ i → S¹Hopf.HopfSuspS¹ (p i)) base gn)
--              (mer : x ≡ y)
--              (gs : fib y)
--              (mer-l : mer ≡ mer)
--              (ppl : PathP (λ j → S¹Hopf.HopfSuspS¹ (mer j)) gn gs)
--     → isContr ∥ PathP (λ i → PathP (λ j → S¹Hopf.HopfSuspS¹ (mer-l i j)) gn gs) ppl ppl ∥₂
--   contrFst x y =
--     J (λ x p
--     → (gn : fib x)
--              (pp : PathP (λ i → S¹Hopf.HopfSuspS¹ (p i)) base gn)
--              (mer : x ≡ y)
--              (gs : fib y)
--              (mer-l : mer ≡ mer)
--              (ppl : PathP (λ j → S¹Hopf.HopfSuspS¹ (mer j)) gn gs)
--     → isContr ∥ PathP (λ i → PathP (λ j → S¹Hopf.HopfSuspS¹ (mer-l i j)) gn gs) ppl ppl ∥₂)
--       λ gn → J (λ gn _ → (mer : north ≡ y) (gs : fib y) (mer-l : mer ≡ mer)
--       (ppl : PathP (λ j → S¹Hopf.HopfSuspS¹ (mer j)) gn gs) →
--       isContr
--       ∥
--       PathP (λ i → PathP (λ j → S¹Hopf.HopfSuspS¹ (mer-l i j)) gn gs) ppl
--       ppl
--       ∥₂)
--       (J (λ y mer → (gs : fib y) (mer-l : mer ≡ mer)
--       (ppl : PathP (λ j → S¹Hopf.HopfSuspS¹ (mer j)) base gs) →
--       isContr
--       ∥
--       PathP (λ i → PathP (λ j → S¹Hopf.HopfSuspS¹ (mer-l i j)) base gs)
--       ppl ppl
--       ∥₂) λ gs pp
--       → J (λ gs ppl → isContr
--       ∥
--       PathP (λ i → PathP (λ j → S¹Hopf.HopfSuspS¹ (pp i j)) base gs) ppl
--       ppl
--       ∥₂)
--       {!!})

--   testhLevel :
--     Iso ((f : (S₊∙ 2 →∙ S₊∙ 2))
--       → Iso (Σ[ g ∈ ((x : S₊ 2) → S¹Hopf.HopfSuspS¹ (fst f x)) ]
--                PathP (λ i → S¹Hopf.HopfSuspS¹ (snd f i)) (g north) base)
--              (Σ[ gn ∈ fib (fst f north) ]
--                Σ[ gn≡ ∈ PathP (λ i → S¹Hopf.HopfSuspS¹ (snd f i)) gn base ]
--                  Σ[ gs ∈ fib (fst f south) ]
--                    ((a : S₊ 1)
--                    → PathP (λ i → S¹Hopf.HopfSuspS¹  (fst f (merid a i))) gn gs)))
--         {!!}
--   testhLevel = {!!}

-- -- ΣHopf : Iso (Hopfie∙ →∙ Hopfie∙)
-- --             (Σ[ f ∈ Hopfie∙ →∙ (S₊∙ 2) ]
-- --               Σ[ g ∈ ((x : Hopfie) → S¹Hopf.HopfSuspS¹ (fst f x)) ]
-- --                 PathP (λ i → S¹Hopf.HopfSuspS¹ (snd f i)) (g (north , base)) base)
-- -- ΣHopf = {!!}
-- --   where
-- --   gr : (f : Hopfie∙ →∙ (S₊∙ 2)) →
-- --     isContr ∥ (Σ[ g ∈ ((x : Hopfie) → S¹Hopf.HopfSuspS¹ (fst f x)) ]
-- --                 PathP (λ i → S¹Hopf.HopfSuspS¹ (snd f i)) (g (north , base)) base) ∥₂
-- --   gr f = ∣ (λ { (north , y) → {!!}
-- --              ; (south , y) → {!!}
-- --              ; (merid a i , y) → {!!}}) , {!!} ∣₂ , {!!}

-- -- strunc1 : ∀ {ℓ} {A : Pointed ℓ}
-- --         → (x : S₊ 2)
-- --         → (p : north ≡ x)
-- --         → (y : S¹Hopf.HopfSuspS¹ x)
-- --         → isContr (∥ (PathP ((λ i → S¹Hopf.HopfSuspS¹ (p i))) base y) ∥₂ )
-- -- strunc1 {A = A} x =
-- --   J (λ x p → (y : S¹Hopf.HopfSuspS¹ x)
-- --         → isContr (∥ (PathP ((λ i → S¹Hopf.HopfSuspS¹ (p i))) base y) ∥₂ ))
-- --     {!sphere!}

-- -- coolIsoPre : Iso (∥ Hopfie∙ →∙ Hopfie∙ ∥₂)
-- --                  (∥ (Hopfie∙ →∙ S₊∙ 2) ∥₂)
-- -- Iso.fun coolIsoPre = sMap λ f → (fst ∘ fst f) , cong fst (snd f)
-- -- Iso.inv coolIsoPre =
-- --   sMap λ f → {!!} , {!!}
-- -- Iso.rightInv coolIsoPre = {!!}
-- -- Iso.leftInv coolIsoPre = {!!}

-- -- coolIso : Iso (π' 3 (Hopfie , north , base)) (π' 3 (S₊∙ 2))
-- -- coolIso = iso (sMap h) (sMap {!!}) {!!} {!!}
-- --   where
-- --   invie : S₊∙ 3 →∙ S₊∙ 2 → S₊∙ 3 →∙ (Hopfie , north , base)
-- --   fst (invie f) x = fst f x , {!!}
-- --   snd (invie f) = {!refl!}

-- --   h : _ → (_ →∙ _)
-- --   fst (h f) = fst ∘ fst f
-- --   snd (h f) = cong fst (snd f)

-- -- -- →∙Homogeneous≡Path : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'} {f∙ g∙ : A∙ →∙ B∙}
-- -- --   (h : isHomogeneous B∙) → (p q : f∙ ≡ g∙) → cong fst p ≡ cong fst q → p ≡ q
-- -- -- →∙Homogeneous≡Path {A∙ = A∙@(A , a₀)} {B∙@(B , b)} {f∙@(f , f₀)} {g∙@(g , g₀)} h p q r =
-- -- --   transport (λ k
-- -- --       → PathP (λ i
-- -- --         → PathP (λ j → (A , a₀) →∙ newPath-refl p q r i j (~ k))
-- -- --                  (f , f₀) (g , g₀)) p q)
-- -- --       (badPath p q r)
-- -- --   where
-- -- --   newPath : (p q : f∙ ≡ g∙) (r : cong fst p ≡ cong fst q)
-- -- --     → Square (refl {x = b}) refl refl refl
-- -- --   newPath p q r i j =
-- -- --     hcomp (λ k → λ {(i = i0) → cong snd p j k
-- -- --                    ; (i = i1) → cong snd q j k
-- -- --                    ; (j = i0) → f₀ k
-- -- --                    ; (j = i1) → g₀ k})
-- -- --           (r i j a₀)

-- -- --   newPath-refl : (p q : f∙ ≡ g∙) (r : cong fst p ≡ cong fst q)
-- -- --          → PathP (λ i → (PathP (λ j → B∙ ≡ (B , newPath p q r i j))) refl refl) refl refl
-- -- --   newPath-refl p q r i j k =
-- -- --     hcomp (λ w → λ { (i = i0) → lCancel (h b) w k
-- -- --                     ; (i = i1) → lCancel (h b) w k
-- -- --                     ; (j = i0) → lCancel (h b) w k
-- -- --                     ; (j = i1) → lCancel (h b) w k
-- -- --                     ; (k = i0) → lCancel (h b) w k
-- -- --                     ; (k = i1) → B , newPath p q r i j})
-- -- --           ((sym (h b) ∙ h (newPath p q r i j)) k)

-- -- --   badPath : (p q : f∙ ≡ g∙) (r : cong fst p ≡ cong fst q)
-- -- --     → PathP (λ i →
-- -- --         PathP (λ j → A∙ →∙ (B , newPath p q r i j))
-- -- --              (f , f₀) (g , g₀))
-- -- --               p q
-- -- --   fst (badPath p q r i j) = r i j
-- -- --   snd (badPath p q s i j) k =
-- -- --     hcomp (λ r → λ { (i = i0) → snd (p j) (r ∧ k)
-- -- --                     ; (i = i1) → snd (q j) (r ∧ k)
-- -- --                     ; (j = i0) → f₀ (k ∧ r)
-- -- --                     ; (j = i1) → g₀ (k ∧ r)
-- -- --                     ; (k = i0) → s i j a₀})
-- -- --           (s i j a₀)

-- -- -- contrsnd : {!(f : !}
-- -- -- contrsnd = {!!}

-- -- -- π→ : (n : ℕ) → A →∙ B → π' n A → π' n B 
-- -- -- π→ n f = sMap (f ∘∙_)

-- -- -- coef : (n : ℕ) → {!!} → {!!}
-- -- -- coef = {!!}

-- -- -- →isHomogeneousΣ≡ : ∀ {ℓ ℓ'} (C : Pointed ℓ) (B : (typ A) → Type ℓ')
-- -- --   → (b₀ : B (pt A))
-- -- --   → (((x : (typ A)) (b : B x) → isHomogeneous (B x , b)))
-- -- --   → (f : typ C → (Σ (typ A) B))
-- -- --   → (sndf1 sndf2 : f (snd C) ≡ (pt A , b₀))
-- -- --   → cong fst sndf1 ≡ cong fst sndf2
-- -- --   → Path {!!} {!!} {!!}
-- -- -- →isHomogeneousΣ≡ C B b₀ hom f g = {!!}

-- -- -- →∙Σ' : ∀ {ℓ ℓ'} (C : Pointed ℓ) (B : typ A → Type ℓ')
-- -- --     → (b₀ : B (pt A))
-- -- --     → (f : C →∙ A)
-- -- --     → Πᵘ∙ (typ C) (λ x → B (fst f x) , {!!}) .fst
-- -- --     → {!!}
-- -- -- →∙Σ' = {!isHomogeneousPi!}

-- -- -- →∙Σ : ∀ {ℓ ℓ'} (C : Pointed ℓ) (B : (typ A) → Type ℓ')
-- -- --     → (b₀ : B (pt A))
-- -- --     → (f : C →∙ A)
-- -- --     → (g : (x : fst C) → B (fst f x))
-- -- --     → (p : fst f (snd C) ≡ snd A)
-- -- --     → PathP (λ i → B (p i)) (g (snd C)) b₀
-- -- --     → (C →∙ (Σ (typ A) B , pt A , b₀))
-- -- -- fst (fst (→∙Σ C B b₀ f g p pp) x) = fst f x
-- -- -- snd (fst (→∙Σ C B b₀ f g p pp) x) = g x
-- -- -- fst (snd (→∙Σ C B b₀ f g p pp) i) = p i
-- -- -- snd (snd (→∙Σ C B b₀ f g p pp) i) = pp i

-- -- -- theTyp : ∀ {ℓ ℓ'} (C : Pointed ℓ) (B : (typ A) → Type ℓ')
-- -- --     → (b₀ : B (pt A))
-- -- --     → Type _
-- -- -- theTyp {A = A} C B b₀ =
-- -- --   Σ[ f ∈ C →∙ A ]
-- -- --     Σ[ g ∈ ((x : fst C) → B (fst f x)) ]
-- -- --      Σ[ p ∈ (fst f (snd C) ≡ snd A) ]
-- -- --        PathP (λ i → B (p i)) (g (snd C)) b₀

-- -- -- -- isHomogeneousΠ∙

-- -- -- IsoΣ : ∀ {ℓ ℓ'} (C : Pointed ℓ) (B : (typ A) → Type ℓ')
-- -- --     → (b₀ : B (pt A))
-- -- --     → Iso (C →∙ (Σ (typ A) B , pt A , b₀))
-- -- --            (Σ[ f ∈ C →∙ A ]
-- -- --              Π∙ C (λ c → B (fst f c)) (subst B (sym (snd f)) b₀))
-- -- -- Iso.fun (IsoΣ C B b₀) f = ((fst ∘ (fst f)) , (cong fst (snd f)))
-- -- --                        , (snd ∘ (fst f))
-- -- --                        , λ j → transp (λ i → B (fst (snd f (~ i ∧ j))))
-- -- --                                        (~ j)
-- -- --                                        (snd (snd f j))
-- -- -- fst (fst (Iso.inv (IsoΣ C B b₀) (f , g , p)) x) = fst f x
-- -- -- snd (fst (Iso.inv (IsoΣ C B b₀) (f , g , p)) x) = g x
-- -- -- snd (Iso.inv (IsoΣ C B b₀) (f , g , p)) =
-- -- --   ΣPathP ((snd f) , {!!})
-- -- -- Iso.rightInv (IsoΣ C B b₀) = {!!}
-- -- -- Iso.leftInv (IsoΣ C B b₀) = {!!}

-- -- -- theTyp≡hom : ∀ {ℓ ℓ'} (C : Pointed ℓ) (B : (typ A) → Type ℓ')
-- -- --     → (b₀ : B (pt A))
-- -- --     → ((x : (typ A)) (b : B x) → isHomogeneous (B x , b))
-- -- --     → (x y : theTyp C B b₀)
-- -- --     → (p : fst x ≡ fst y)
-- -- --     → (e : (c : fst C)
-- -- --      →  PathP (λ i → B (p i .fst c))
-- -- --               (fst (snd x) c) (fst (snd y) c))
-- -- --     → PathP (λ i → fst (p i) (snd C) ≡ snd A)
-- -- --              (fst (snd (snd x))) (fst (snd (snd y)))
-- -- --     → x ≡ y
-- -- -- theTyp≡hom {A = A} C B b₀ hom x y p q r =
-- -- --   transport
-- -- --     (λ i → {!p!})
-- -- --     {!theTyp C B b₀!}
-- -- --   where
-- -- --   main : PathP (λ i → Σ[ f ∈ (C →∙ A) ] {!!}) x y
-- -- --   main = {!(λ f →
-- -- --    Σ-syntax ((x₁ : fst C) → B (fst f x₁))
-- -- --    (λ g →
-- -- --       Σ-syntax (fst f (snd C) ≡ snd A)
-- -- --       (λ p₁ → PathP (λ i → B (p₁ i)) (g (snd C)) b₀)))!}

-- -- --   newPath : SquareP (λ i j → (B (fst (p i) (pt C)))) {!!} {!!} {!!} {!!}
-- -- --   newPath i j =
-- -- --     hcomp (λ k → λ { (i = i0) → {!snd (snd (snd x)) j!}
-- -- --                     ; (i = i1) → {!snd (snd (snd y)) k!}
-- -- --                     ; (j = i0) → {!!}
-- -- --                     ; (j = i1) → {!!}})
-- -- --           {!!}


-- -- -- πHom→ : (n : ℕ) → A →∙ B → GroupHom (π'Gr n A) (π'Gr n B)
-- -- -- fst (πHom→ n f) = π→ (suc n) f
-- -- -- snd (πHom→ zero f) =
-- -- --   makeIsGroupHom
-- -- --     (sElim2 (λ _ _ → isSetPathImplicit)
-- -- --     λ g h →
-- -- --      cong ∣_∣₂
-- -- --       (ΣPathP ((funExt
-- -- --         (λ { base → snd f
-- -- --           ; (loop i) → {!!}}))
-- -- --              , (sym (lUnit _) ◁ λ i j → snd f (i ∨ j)))))
-- -- -- snd (πHom→ (suc n) f) =
-- -- --   makeIsGroupHom
-- -- --     (sElim2 (λ _ _ → isSetPathImplicit)
-- -- --       λ g h → cong ∣_∣₂
-- -- --         (ΣPathP ((funExt λ { north → snd f
-- -- --                            ; south → snd f
-- -- --                            ; (merid a i) j →
-- -- --                              hcomp (λ k →
-- -- --                                λ {(i = i0) → snd f (j ∧ k)
-- -- --                                 ; (i = i1) → snd f (j ∧ k)
-- -- --                                 ; (j = i0) →
-- -- --                                   cong-∙ (fst f)
-- -- --                                     (sym (snd g) ∙∙ cong (fst g) (σ (S₊∙ (suc n)) a) ∙∙ snd g)
-- -- --                                     (sym (snd h) ∙∙ cong (fst h) (σ (S₊∙ (suc n)) a) ∙∙ snd h)
-- -- --                                   (~ k) i
-- -- --                                 ; (j = i1) →
-- -- --                                    ((sym (compPath-filler (cong (fst f) (snd g)) (snd f) k)
-- -- --                                   ∙∙ cong (fst f) (cong (fst g)
-- -- --                                       (σ (S₊∙ (suc n)) a))
-- -- --                                   ∙∙ compPath-filler (cong (fst f) (snd g)) (snd f) k)
-- -- --                                   ∙ (sym (compPath-filler (cong (fst f) (snd h)) (snd f) k)
-- -- --                                   ∙∙ cong (fst f) (cong (fst h)
-- -- --                                       (σ (S₊∙ (suc n)) a))
-- -- --                                   ∙∙ compPath-filler (cong (fst f) (snd h)) (snd f) k))
-- -- --                                   i})
-- -- --                 ((cong-∙∙ (fst f) (sym (snd g)) (cong (fst g) (σ (S₊∙ (suc n)) a)) (snd g) j
-- -- --                ∙ cong-∙∙ (fst f) (sym (snd h)) (cong (fst h) (σ (S₊∙ (suc n)) a)) (snd h) j) i)})
-- -- --       , (sym (lUnit (snd f)) ◁ λ i j → snd f (i ∨ j)))))

-- -- -- module _ (f : A →∙ B)
-- -- --   where
-- -- --   fib = fiber (fst f) (pt B)

-- -- --   fib∙ : Pointed _
-- -- --   fst fib∙ = fib
-- -- --   snd fib∙ = (pt A) , (snd f)

-- -- --   fib→A : fib∙ →∙ A
-- -- --   fst fib→A = fst
-- -- --   snd fib→A = refl

-- -- --   hom₁ : (n : ℕ) → GroupHom (π'Gr n fib∙) (π'Gr n A)
-- -- --   hom₁ n = πHom→ n fib→A

-- -- --   hom₂ : (n : ℕ) → GroupHom (π'Gr n A) (π'Gr n B)
-- -- --   hom₂ n = πHom→ n f

-- -- --   ∙Π' : (n : ℕ) → (S₊∙ (suc n) →∙ fib∙) → (S₊∙ (suc n) →∙ fib∙)
-- -- --       → S₊∙ (suc n) →∙ fib∙
-- -- --   fst (∙Π' n g h) x =
-- -- --       (pt A)
-- -- --     , snd f ∙ (sym (snd (fst g x)) ∙ fst g x .snd) ∙ (sym (snd (fst h x)) ∙ fst h x .snd)
-- -- --   snd (∙Π' n g h) =
-- -- --     ΣPathP (refl , (cong (snd f ∙_) (cong₂ _∙_ (rCancel (sym (snd (fst g (ptSn _))))) (rCancel (sym (snd (fst h (ptSn _))))) ∙ sym (rUnit refl)) ∙ sym (rUnit (snd f))))

-- -- --   ∙Π'≡∙Π : (n : ℕ) (f g : _) → ∙Π' n f g ≡ ∙Π f g
-- -- --   ∙Π'≡∙Π zero f g =
-- -- --     ΣPathP ((funExt (λ { base → snd (∙Π' zero f g)
-- -- --                        ; (loop i) j → {!snd A!}
-- -- --                                      , {!!}}))
-- -- --           , λ i j → snd (∙Π' zero f g) (i ∨ j))
-- -- --   ∙Π'≡∙Π (suc n) f g = {!!}

-- -- -- --   fun₃ : (n : ℕ) →  S₊∙ (suc (suc n)) →∙ B → S₊∙ (suc n) →∙ fib∙
-- -- -- --   fst (fun₃ n g) x = pt A , (snd f
-- -- -- --       ∙ (sym (snd g) ∙∙ cong (fst g) (σ (S₊∙ (suc n)) x) ∙∙ snd g))
-- -- -- --   snd (fun₃ n g) =
-- -- -- --     ΣPathP (refl , (cong (snd f ∙_) (cong (sym (snd g) ∙∙_∙∙ snd g) (cong (cong (fst g)) (rCancel (merid (ptSn (suc n))))) ∙ ∙∙lCancel (snd g)) ∙ sym (rUnit (snd f))))

-- -- -- --   hom₃ : (n : ℕ) → GroupHom (π'Gr (suc n) B) (π'Gr n fib∙)
-- -- -- --   fst (hom₃ n) = sMap (fun₃ n)
-- -- -- --   snd (hom₃ zero) = {!!}
-- -- -- --   snd (hom₃ (suc n)) =
-- -- -- --     makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
-- -- -- --       λ g h → cong ∣_∣₂
-- -- -- --         (ΣPathP
-- -- -- --           ((funExt λ { north →
-- -- -- --             ΣPathP (refl , cong (snd f ∙_)
-- -- -- --                           (sym (rUnit (λ i₁ → fst (∙Π g h) (σ (S₊∙ (suc (suc n))) north i₁)))
-- -- -- --                        ∙∙ cong-∙ (fst (∙Π g h)) (merid north) (sym (merid north))
-- -- -- --                        ∙∙ rCancel (cong (fst (∙Π g h)) (merid north)))
-- -- -- --                         ∙ sym (rUnit (snd f)))
-- -- -- --                      ; south →
-- -- -- --             ΣPathP (refl , cong (snd f ∙_)
-- -- -- --                           (sym (rUnit (λ i₁ → fst (∙Π g h) (σ (S₊∙ (suc (suc n))) south i₁)))
-- -- -- --                        ∙∙ ((λ j → cong (fst (∙Π g h)) (merid (merid (ptSn (suc n)) (~ j)) ∙ (λ i → merid north (~ i)))) ∙ cong-∙ (fst (∙Π g h)) (merid north) (sym (merid north)))
-- -- -- --                        ∙∙ rCancel (cong (fst (∙Π g h)) (merid north)))
-- -- -- --                         ∙ sym (rUnit (snd f)))
-- -- -- --                      ; (merid a i) j → {!!} , {!!}})
-- -- -- --          , {!!})))


-- -- -- -- --   ker⊂im : (n : ℕ) (x : _) → isInKer (hom₁ n) x → isInIm (hom₃ n) x
-- -- -- -- --   ker⊂im n =
-- -- -- -- --     sElim {!!}
-- -- -- -- --       λ h p →
-- -- -- -- --        pRec squash
-- -- -- -- --          (λ r → ∣ ∣ lem h r ∣₂
-- -- -- -- --                 , {!!} ∣)
-- -- -- -- --         (Iso.fun PathIdTrunc₀Iso p)

-- -- -- -- --     where
-- -- -- -- --     lem : (g : S₊∙ (suc n) →∙ fib∙) → (fib→A ∘∙ g) ≡ 1Π → S₊∙ (suc (suc n)) →∙ B
-- -- -- -- --     fst (lem g r) north = pt B
-- -- -- -- --     fst (lem g r) south = pt B
-- -- -- -- --     fst (lem g r) (merid a i) =
-- -- -- -- --        ((sym (snd f)
-- -- -- -- --       ∙ cong (fst f) (sym (funExt⁻ (cong fst r) a)))
-- -- -- -- --       ∙ snd (fst g a)) i
-- -- -- -- --     snd (lem g r) = refl

-- -- -- -- --     lem₂ : (g : S₊∙ (suc n) →∙ fib∙) (r : (fib→A ∘∙ g) ≡ 1Π) →
-- -- -- -- --          (x : _) → fst (fun₃ _ (lem g r)) x ≡ fst g x
-- -- -- -- --     lem₂ g r x =
-- -- -- -- --       ΣPathP ((sym (funExt⁻ (cong fst r) x))
-- -- -- -- --           , (cong (snd f ∙_) (sym (rUnit (cong (fst (lem g r)) (σ (S₊∙ (suc n)) x )))
-- -- -- -- --           ∙ cong-∙ (fst (lem g r)) (merid x) (sym (merid (ptSn (suc n)))))
-- -- -- -- --           ◁ {!!}))

-- -- -- -- --   im→ker : (n : ℕ) (x : _) → isInIm (hom₃ n) x → isInKer (hom₁ n) x
-- -- -- -- --   im→ker n =
-- -- -- -- --     sElim {!!}
-- -- -- -- --       λ h →
-- -- -- -- --         pRec (squash₂ _ _)
-- -- -- -- --          (uncurry
-- -- -- -- --           (sElim (λ _ → isSetΠ λ _ → isSetPathImplicit)
-- -- -- -- --             λ g p → pRec (isPropIsInKer (hom₁ n) ∣ h ∣₂)
-- -- -- -- --               (J (λ h _ → isInKer (hom₁ n) ∣ h ∣₂)
-- -- -- -- --                 (cong ∣_∣₂ (ΣPathP (funExt (λ _ → refl)
-- -- -- -- --                 , {!!}))))
-- -- -- -- --               (Iso.fun PathIdTrunc₀Iso p)))

-- -- -- -- -- module _ {ℓ} (P : typ A → Pointed ℓ) (e : Iso (typ (P (pt A))) (typ (P (pt A))))
-- -- -- -- --              (e∙ : Iso.inv e (pt (P (pt A))) ≡ pt (P (pt A)))
-- -- -- -- --   where
-- -- -- -- --   B' = (P (pt A))

-- -- -- -- --   e∙' : Iso.fun e (pt (P (pt A))) ≡ pt (P (pt A))
-- -- -- -- --   e∙' = {!!} ∙ {!!}
-- -- -- -- --   TS : Pointed _
-- -- -- -- --   TS = Σ (typ A) (fst ∘ P) , pt A , pt (P (pt A))

-- -- -- -- --   transpPath : (n : ℕ) (f : S₊∙ (suc (suc n)) →∙ TS) → S₊ (suc n) → fst f north ≡ snd TS
-- -- -- -- --   transpPath n f x =
-- -- -- -- --     cong (fst f) (merid x ∙ sym (merid (ptSn _))) ∙ snd f

-- -- -- -- --   ll : (n : ℕ) (f : S₊∙ (suc (suc n)) →∙ TS)
-- -- -- -- --      → S₊ (suc n)
-- -- -- -- --      → (fst ∘ P) (fst (snd TS))
-- -- -- -- --   ll n f x = subst (fst ∘ P) (cong fst (cong (fst f)
-- -- -- -- --                    (merid x ∙ sym (merid (ptSn _))) ∙ snd f))
-- -- -- -- --                      (fst f north .snd)

-- -- -- -- --   transpPath∙ : (n : ℕ) → (f : S₊∙ (suc (suc n)) →∙ TS)
-- -- -- -- --              → transpPath n f (ptSn (suc n)) ≡ snd f
-- -- -- -- --   transpPath∙ n f =
-- -- -- -- --       cong (_∙ snd f) (cong (cong (fst f))
-- -- -- -- --        (rCancel (merid (ptSn (suc n)))))
-- -- -- -- --     ∙ sym (lUnit _)

-- -- -- -- --   B→TS : B' →∙ TS
-- -- -- -- --   fst B→TS x = pt A , x
-- -- -- -- --   snd B→TS = refl

-- -- -- -- --   TS→A : TS →∙ A
-- -- -- -- --   fst TS→A = fst
-- -- -- -- --   snd TS→A = refl

-- -- -- -- --   π↓ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
-- -- -- -- --         (n : ℕ) (f : ((S₊∙ (suc (suc n))) →∙ A)
-- -- -- -- --                      → S₊∙ (suc n) →∙ B)
-- -- -- -- --       → GroupHom (π'Gr (suc n) A) (π'Gr n B)
-- -- -- -- --   fst (π↓ n F) = sMap F
-- -- -- -- --   snd (π↓ zero F) =
-- -- -- -- --     makeIsGroupHom
-- -- -- -- --       (sElim2 (λ _ _ → isSetPathImplicit)
-- -- -- -- --         λ f g → cong ∣_∣₂
-- -- -- -- --           (ΣPathP (funExt (λ { base → snd (F (∙Π f g))
-- -- -- -- --                              ; (loop i) → {!!}})
-- -- -- -- --                  , λ i j → snd (F (∙Π f g)) (i ∨ j))))
-- -- -- -- --   snd (π↓ (suc n) F) = {!!}

-- -- -- -- --   fun→₁ : (n : ℕ) → π' (suc (suc n)) B' → (π' (suc (suc n)) TS)
-- -- -- -- --   fun→₁ n = π→ (suc (suc n)) B→TS

-- -- -- -- --   fun→₁Hom : (n : ℕ) → GroupHom (π'Gr (suc n) B') (π'Gr (suc n) TS)
-- -- -- -- --   fun→₁Hom n = πHom→ (suc n) B→TS

-- -- -- -- --   fun→₂Hom : (n : ℕ) → GroupHom (π'Gr (suc n) TS) (π'Gr (suc n) A)
-- -- -- -- --   fun→₂Hom n = πHom→ (suc n) TS→A

-- -- -- -- --   lem₁ : (n : ℕ) → (f : S₊∙ (suc (suc n)) →∙ A)
-- -- -- -- --     → (x : S₊ (suc n))
-- -- -- -- --     → pt A ≡ pt A
-- -- -- -- --   lem₁ n f x = sym (snd f) ∙∙ cong (fst f) (σ (S₊∙ (suc n)) x) ∙∙ snd f

-- -- -- -- --   lem₁Π∙ : (n : ℕ) → (f g : S₊∙ (suc (suc n)) →∙ A)
-- -- -- -- --                     → (x : S₊ (suc n))
-- -- -- -- --                     → pt A ≡ pt A
-- -- -- -- --   lem₁Π∙ n f g x =
-- -- -- -- --       sym (snd f) ∙∙ cong (fst f) (σ (S₊∙ (suc n)) x) ∙∙ snd f
-- -- -- -- --     ∙ (sym (snd g) ∙∙ cong (fst g) (σ (S₊∙ (suc n)) x) ∙∙ snd g)

-- -- -- -- --   lem₁Π∙∙ : (n : ℕ) → (f g : S₊∙ (suc (suc n)) →∙ A)
-- -- -- -- --     → lem₁Π∙ n f g (ptSn (suc n)) ≡ refl
-- -- -- -- --   lem₁Π∙∙ n f g = {!!}

-- -- -- -- --   lem₁≡ : (n : ℕ) (f g : S₊∙ (suc (suc n)) →∙ A) (x : S₊ (suc n))
-- -- -- -- --                 → lem₁ n (∙Π f g) x ≡ lem₁Π∙ n f g x 
-- -- -- -- --   lem₁≡ = {!!}

-- -- -- -- --   lem₁∙ : (n : ℕ) → (f : S₊∙ (suc (suc n)) →∙ A)
-- -- -- -- --     → lem₁ n f (ptSn (suc n)) ≡ refl
-- -- -- -- --   lem₁∙ n f = cong (sym (snd f) ∙∙_∙∙ snd f) (cong (cong (fst f)) (rCancel _))
-- -- -- -- --           ∙ ∙∙lCancel (snd f)

-- -- -- -- --   fib≡ : Iso (fiber (fst B→TS) ((pt A) , (pt (P (pt A)))))
-- -- -- -- --              (typ (P (pt A)))
-- -- -- -- --   Iso.fun fib≡ x = fst B→TS {!x!} .snd
-- -- -- -- --   Iso.inv fib≡ x = {!!}
-- -- -- -- --   Iso.rightInv fib≡ x = {!!}
-- -- -- -- --   Iso.leftInv fib≡ x = {!!}

-- -- -- -- --   fun→₃Hom-gen : {!!}
-- -- -- -- --   fun→₃Hom-gen = {!!}

-- -- -- -- --   fun→₃Hom : (n : ℕ)
-- -- -- -- --     → GroupHom (π'Gr (suc n) A)
-- -- -- -- --                (π'Gr n B')
-- -- -- -- --   fst (fun→₃Hom n) =
-- -- -- -- --     sMap λ f → (λ x → subst (fst ∘ P) (lem₁ n f x) (pt (P (pt A))))
-- -- -- -- --               , cong (λ x → subst (λ x → fst (P x)) x (pt (P (pt A)))) (lem₁∙ n f)
-- -- -- -- --               ∙ transportRefl (snd B')
-- -- -- -- --   snd (fun→₃Hom zero) =
-- -- -- -- --     makeIsGroupHom
-- -- -- -- --       (sElim2 (λ _ _ → isSetPathImplicit)
-- -- -- -- --         λ f g → cong ∣_∣₂ (ΣPathP ((funExt
-- -- -- -- --           λ { base → cong (λ x → subst (λ x → fst (P x)) x (pt (P (pt A))))
-- -- -- -- --                           (lem₁∙ zero ((∙Π f g) ))
-- -- -- -- --                         ∙ transportRefl (snd B')
-- -- -- -- --            ; (loop i) j → {!!}})
-- -- -- -- --            , λ i j → (cong (λ x → subst (λ x → fst (P x)) x (pt (P (pt A))))
-- -- -- -- --                           (lem₁∙ zero ((∙Π f g) ))
-- -- -- -- --                         ∙ transportRefl (snd B')) (i ∨ j))))
-- -- -- -- --   snd (fun→₃Hom (suc n)) =
-- -- -- -- --     makeIsGroupHom
-- -- -- -- --       (sElim2 (λ _ _ → isSetPathImplicit)
-- -- -- -- --         λ f g
-- -- -- -- --          → cong ∣_∣₂ (ΣPathP ({!!}
-- -- -- -- --                             , {!!})))
-- -- -- -- --   {-
-- -- -- -- --     makeIsGroupHom
-- -- -- -- --       (sElim2 (λ _ _ → isSetPathImplicit)
-- -- -- -- --         λ f g → cong ∣_∣₂ (ΣPathP ((funExt λ x → {!!}) , {!!})))
-- -- -- -- -- -}
-- -- -- -- --   im₁⊂ker₂ : (n : ℕ) (x : _)
-- -- -- -- --            → isInIm (fun→₁Hom n) x
-- -- -- -- --            → isInKer (fun→₂Hom n) x
-- -- -- -- --   im₁⊂ker₂ n =
-- -- -- -- --     sElim (λ _ → isSetΠ λ _ → isSetPathImplicit)
-- -- -- -- --       λ f → pRec (isPropIsInKer _ _)
-- -- -- -- --         (uncurry
-- -- -- -- --           (sElim (λ _ → isSetΠ λ _ → isSetPathImplicit)
-- -- -- -- --             λ g p → pRec (isPropIsInKer (fun→₂Hom n) ∣ f ∣₂)
-- -- -- -- --               (J (λ f _ → isInKer (fun→₂Hom n) ∣ f ∣₂)
-- -- -- -- --                 (cong ∣_∣₂ (ΣPathP (refl
-- -- -- -- --                                 , (sym (rUnit _)
-- -- -- -- --                                  ∙ cong-∙ (fst TS→A) (λ i → pt A , snd g i) refl
-- -- -- -- --                                  ∙ sym (rUnit _))))))
-- -- -- -- --               (Iso.fun PathIdTrunc₀Iso p)))

-- -- -- -- --   ker₂⊂im₁ : (n : ℕ) (x : _)
-- -- -- -- --            → isInKer (fun→₂Hom n) x
-- -- -- -- --            → isInIm (fun→₁Hom n) x
-- -- -- -- --   ker₂⊂im₁ n =
-- -- -- -- --     sElim (λ _ → isSetΠ
-- -- -- -- --             λ _ → isProp→isSet (isPropIsInIm (fun→₁Hom n) _))
-- -- -- -- --       λ f p → pRec (isPropIsInIm (fun→₁Hom n) ∣ f ∣₂)
-- -- -- -- --         (λ q →
-- -- -- -- --           (help (fst ∘ fst f) (sym (cong fst q)) (cong fst (snd f))
-- -- -- -- --                 ((λ i j → snd (q (~ i)) j) ▷ sym (rUnit _))
-- -- -- -- --                 (snd ∘ fst f)
-- -- -- -- --                 λ j → snd (snd f j)))
-- -- -- -- --         (Iso.fun PathIdTrunc₀Iso p)
-- -- -- -- --     where
-- -- -- -- --     help : (f : (a : fst (S₊∙ (suc (suc n)))) → typ A)
-- -- -- -- --          → (p : (λ _ → pt A) ≡ f)
-- -- -- -- --          → (f∙ : f north ≡ pt A)
-- -- -- -- --          → PathP (λ i → p i north ≡ pt A) refl f∙
-- -- -- -- --          → (r : (a : _) → fst (P (f a)))
-- -- -- -- --         → (r∙ : PathP (λ i → fst (P (f∙ i))) (r north) (pt B'))
-- -- -- -- --         → isInIm (fun→₁Hom n) ∣ (λ a → (f a) , (r a)) , ΣPathP (f∙ , r∙) ∣₂
-- -- -- -- --     help f =
-- -- -- -- --       J (λ f p →
-- -- -- -- --         (f∙ : f north ≡ pt A)
-- -- -- -- --          → PathP (λ i → p i north ≡ pt A) refl f∙
-- -- -- -- --          → (r : (a : _) → fst (P (f a)))
-- -- -- -- --         → (r∙ : PathP (λ i → fst (P (f∙ i))) (r north) (pt B'))
-- -- -- -- --         → isInIm (fun→₁Hom n) ∣ (λ a → (f a) , (r a)) , ΣPathP (f∙ , r∙) ∣₂)
-- -- -- -- --         λ f∙ → J (λ f∙ _ → (r : (a : Susp (S₊ (suc n))) → fst (P (pt A)))
-- -- -- -- --       (r∙
-- -- -- -- --        : PathP (λ i → fst (P (f∙ i))) (r (snd (S₊∙ (suc (suc n)))))
-- -- -- -- --          (pt B')) →
-- -- -- -- --       isInIm (fun→₁Hom n) ∣ (λ a → pt A , r a) , (λ i → f∙ i , r∙ i) ∣₂)
-- -- -- -- --       λ r r∙ → ∣ ∣ r , r∙ ∣₂
-- -- -- -- --                , cong ∣_∣₂ (ΣPathP (refl , sym (rUnit _))) ∣

-- -- -- -- --   im₃⊂ker₁ : (n : ℕ) (x : _)
-- -- -- -- --              → isInIm (fun→₃Hom (suc n)) x
-- -- -- -- --              → isInKer (fun→₁Hom n) x
-- -- -- -- --   im₃⊂ker₁ n =
-- -- -- -- --     sElim (λ _ → (isSetΠ (λ _ → isSetPathImplicit)))
-- -- -- -- --       λ f → pRec (isPropIsInKer (fun→₁Hom n) ∣ f ∣₂)
-- -- -- -- --         (uncurry (sElim
-- -- -- -- --           (λ _ → isSetΠ (λ _ → isSetPathImplicit))
-- -- -- -- --           λ g p →
-- -- -- -- --             pRec
-- -- -- -- --               (isPropIsInKer (fun→₁Hom n) ∣ f ∣₂)
-- -- -- -- --               (J (λ f _ → isInKer (fun→₁Hom n) ∣ f ∣₂)
-- -- -- -- --                 (cong ∣_∣₂
-- -- -- -- --                   (ΣPathP
-- -- -- -- --                     (funExt (λ x → ΣPathP (sym (lem₁ (suc n) g x)
-- -- -- -- --                           , λ i →  transp (λ j → fst (P (lem₁ (suc n) g x (j ∧ ~ i)))) i
-- -- -- -- --                                            (pt (P (pt A)))))
-- -- -- -- --                   , {!!}))))
-- -- -- -- --               (Iso.fun PathIdTrunc₀Iso p)))

-- -- -- -- --   ker₁⊂im₃ : (n : ℕ) (x : _)
-- -- -- -- --              → isInKer (fun→₁Hom n) x
-- -- -- -- --              → isInIm (fun→₃Hom (suc n)) x
-- -- -- -- --   ker₁⊂im₃ n =
-- -- -- -- --     sElim (λ _ → isSetΠ λ _ → isProp→isSet (isPropIsInIm _ _))
-- -- -- -- --       λ f p → pRec (isPropIsInIm (fun→₃Hom (suc n)) ∣ f ∣₂)
-- -- -- -- --                 (λ q → ∣ ∣ (λ { north → pt A
-- -- -- -- --                               ; south → pt A
-- -- -- -- --                               ; (merid a i) → cong fst q i a .fst})
-- -- -- -- --                         , refl ∣₂
-- -- -- -- --                        , cong ∣_∣₂ (ΣPathP (funExt
-- -- -- -- --                          (λ { north → {!refl!}
-- -- -- -- --                             ; south → {!!}
-- -- -- -- --                             ; (merid a i) → {!!}}) , {!!})) ∣)
-- -- -- -- --                 (Iso.fun PathIdTrunc₀Iso p)
-- -- -- -- --       where
-- -- -- -- --       help : (f : S₊ (suc (suc n)) → typ A)
-- -- -- -- --         → (q : (λ _ → pt A) ≡ f)
-- -- -- -- --         → (f∙ : f north ≡ pt A)
-- -- -- -- --         → PathP {!!} -- (λ i → q (~ i) north ≡ pt A)
-- -- -- -- --                  (λ _ → pt A)
-- -- -- -- --                  f
-- -- -- -- --         → {!!}
-- -- -- -- --       help = {!!}

-- -- -- -- --   fun→₂ : (n : ℕ) → π' (suc (suc n)) TS → π' (suc (suc n)) A
-- -- -- -- --   fun→₂ n = sMap λ f → (λ x → fst f x .fst)
-- -- -- -- --                        , cong fst (snd f)

-- -- -- -- --   fun→₃ : (n : ℕ) → π' (suc (suc n)) A → π' (suc n) B'
-- -- -- -- --   fun→₃ n =
-- -- -- -- --     sMap λ f → (λ x → Iso.fun e (subst (fst ∘ P)
-- -- -- -- --                            (sym (snd f)
-- -- -- -- --                          ∙∙ cong (fst f) (σ (S₊∙ (suc n)) x)
-- -- -- -- --                          ∙∙ snd f) (snd (P (pt A)))))
-- -- -- -- --              , cong (Iso.fun e)
-- -- -- -- --                 (cong (λ y → subst (λ x → fst (P x)) y (snd (P (pt A))))
-- -- -- -- --                   (cong (sym (snd f) ∙∙_∙∙ snd f)
-- -- -- -- --                     (cong (cong (fst f)) (rCancel (merid (ptSn _))))
-- -- -- -- --                     ∙ ∙∙lCancel (snd f))
-- -- -- -- --                ∙ transportRefl ((snd (P (pt A)))))
-- -- -- -- --               ∙ sym (cong (Iso.fun e) e∙)
-- -- -- -- --               ∙ Iso.rightInv e (snd B')
-- -- -- -- --   fun→₃' : {!!}
-- -- -- -- --   fun→₃' = {!!}

-- -- -- -- -- -- fibreSeq : ∀ {ℓ} → (P : typ A → Pointed ℓ)
-- -- -- -- -- --   → (e : Iso (typ (P (pt A))) (typ B))
-- -- -- -- -- --   → Iso.fun e (pt (P (pt A))) ≡ pt B
-- -- -- -- -- --   → (n : ℕ)
-- -- -- -- -- --   → isContr (π' (suc n) (P (pt A)))
-- -- -- -- -- --   → Iso (π' (suc n) ((Σ (typ A) (fst ∘ P) , pt A , pt (P (pt A)))))
-- -- -- -- -- --          (π' n B)
-- -- -- -- -- -- Iso.fun (fibreSeq P e e∙ n c) =
-- -- -- -- -- --   sMap λ f →
-- -- -- -- -- --     (λ x → Iso.fun e (subst (λ x → typ (P x))
-- -- -- -- -- --                       (cong fst (snd f) ∙ {!(merid x)!})
-- -- -- -- -- --                       (f .fst (ptSn (suc n)) .snd)))
-- -- -- -- -- --                     , {!Iso.fun e (subst (λ x → typ (P x))
-- -- -- -- -- --                       (cong fst (snd f) ∙ {!(merid x)!})
-- -- -- -- -- --                       (f .fst (ptSn (suc n)) .snd))!}
-- -- -- -- -- -- Iso.inv (fibreSeq P e e∙ n c) = {!!}
-- -- -- -- -- -- Iso.rightInv (fibreSeq P e e∙ n c) = {!!}
-- -- -- -- -- -- Iso.leftInv (fibreSeq P e e∙ n c) = {!!}
