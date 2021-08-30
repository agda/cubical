{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.CP2 where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup ; Unit to UnitGroup) hiding (Bool)

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Hopf
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₁ ; map to pMap)
open import Cubical.HITs.Truncation
  renaming (elim to trElim ; rec2 to trRec2 ; rec to trRec)

open import Cubical.Relation.Nullary

open IsGroupHom
open Iso



diag : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (p : x ≡ y) (r : z ≡ w) (q : y ≡ z) (s : x ≡ w) (P : PathP (λ i → p i ≡ r (~ i)) s q)
     → (λ i → P i i) ≡ p ∙ q
diag {x = x} {y = y} {z = z} {w = w} p r q s P i j =
  hcomp (λ k → λ {(i = i0) → P j (j ∧ k)
                 ; (j = i0) → x
                 ; (j = i1) → q k})
        (p j)
  {-
  ———— Boundary ——————————————————————————————————————————————
i = i0 ⊢ P j j
i = i1 ⊢ (p ∙ q) j
j = i0 ⊢ x
j = i1 ⊢ z
  -}


testagain : (g : S₊ 3 → S₊ 2) (p : Σ[ f ∈ (S₊ 2 → coHomK 4) ] ((x : S₊ 3) → f (g x) ≡ 0ₖ 4))
          → (s : (λ x → 0ₖ 4) ≡ fst p)
          → p ≡ ((λ _ → 0ₖ 4) , λ x → funExt⁻ s (g x) ∙ (snd p x))
testagain g (f , k) s = help f s k
  where
  help : (f : (S₊ 2 → coHomK 4)) (s : (λ x → 0ₖ 4) ≡ f) (k : (x : S₊ 3) → f (g x) ≡ 0ₖ 4)
       → Path (Σ[ f ∈ (S₊ 2 → coHomK 4) ] ((x : S₊ 3) → f (g x) ≡ 0ₖ 4)) (f , k)
              (((λ _ → 0ₖ 4) , λ x → funExt⁻ s (g x) ∙ (k x)))
  help f =
    J (λ f s → (k : (x : S₊ 3) → f (g x) ≡ 0ₖ 4)
       → Path (Σ[ f ∈ (S₊ 2 → coHomK 4) ] ((x : S₊ 3) → f (g x) ≡ 0ₖ 4)) (f , k)
              (((λ _ → 0ₖ 4) , λ x → funExt⁻ s (g x) ∙ (k x))))
      λ k → ΣPathP (refl , (funExt (λ x → lUnit (k x))))

open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.SmashProduct

hopfy : ∀ {ℓ} {A : Pointed ℓ}
  → (Ω^ 2) A .fst → (Ω^ 3) A .fst
hopfy α l i =
  hcomp
    (λ m → λ
      { (i = i0) → refl
      ; (i = i1) → λ j → side l m j
      ; (l = i0) → α (i ∧ ~ m)
      ; (l = i1) → α (~ i ∨ m)
      })
    (λ j → top l i j)
  where
  a₀ = α i0 i0

  top : (l i j : I) → _
  top l i j =
    hcomp
      (λ k → λ
        { (i = i0) → a₀
        ; (j = i0) → a₀
        ; (j = i1) → α (~ (i ∧ l)) k
        ; (l = i0) → α i j
        ; (l = i1) → α (~ i) (j ∧ k)
        })
      (α (i ∧ ~ l) j)

  side : (l m j : I) → _
  side l m j =
    hcomp
      (λ k → λ
        { (m = i1) → a₀
        ; (j = i0) → a₀
        ; (j = i1) → α (~ (m ∨ l)) k
        ; (l = i0) → α (~ m) (j ∧ k)
        ; (l = i1) → α m j
        })
      (α (m ∨ ~ l) j)

EH-funct : ∀ {ℓ} (p q : typ ((Ω^ 2) (S₊∙ 2))) → EH 0 (p ∙ q) (sym (p ∙ q)) ≡ {!EH 0 p (sym p)!}
EH-funct = {!!}

zz : (p q r : typ (Ω (S₊∙ 2))) (b : r ≡ r) (t : p ∙ sym p ≡ sym p ∙ p) (l : r ≡ p) (r : r ≡ q) (P : PathP (λ i → {!!} ≡ {!p i!}) {!!} {!!})
        → Path (Square {!!} {!!} {!!} {!!}) (λ i j → P (i ∨ j) i j) {!!}
zz  p q = {!!}

Iso1 : Iso ∥ typ ((Ω^ 3) (S₊∙ 2)) ∥₂ ∥ typ ((Ω^ 2) (S₊∙ 2)) ∥₂
fun Iso1 = {!!}
inv Iso1 = sMap hopfy
rightInv Iso1 = sElim {!!} λ p → cong ∣_∣₂ {!!} -- (l p)
  where
  l : (p : _) → {!!}
  l p k i j =
    hcomp {!λ r → {(i = i0) → ? ; (i = i1) → ? ; (j = i0) → ? ; (j = i1) → ? ; (k = i1) → ? ; (k = i0) → ?}!}
          {!!}
leftInv Iso1 =
  {!k = i0 ⊢ ((λ i₁ → rCancel p (~ i₁)) ∙∙ EH 0 p (p ⁻¹) ∙∙ lCancel p)
         (~ i ∨ j) (~ i ∧ j) j
k = i1 ⊢ p i j
i = i0 ⊢ snd (Ω (S₊∙ 2)) j
i = i1 ⊢ snd (Ω (S₊∙ 2)) j
j = i0 ⊢ snd (S₊∙ 2)
j = i1 ⊢ snd (S₊∙ 2)!}

surf' : typ ((Ω^ 2) (S₊∙ 2))
surf' i j = hcomp (λ k → λ { (i = i0) → north
                            ; (i = i1) → north
                            ; (j = i0) → rCancel (merid base) k i
                            ; (j = i1) → rCancel (merid base) k i})
                  ((merid (loop j) ∙ sym (merid base)) i)

test : ℤ
test = sRec isSetℤ (λ p → Iso.inv (Iso-Kn-ΩKn+1 0) (cong (Iso.inv (Iso-Kn-ΩKn+1 1)) (cong (cong ∣_∣ₕ) p)))
            (Iso.fun Iso1 ∣ hopfy surf' ∣₂)

-- fun1 : ∥ typ ((Ω^ 3) (S₊∙ 2)) ∥₂ → coHom 2 (Smash (S₊∙ 1) (S₊∙ 1))
-- fun1 = {!!}


-- open import Cubical.Data.Bool
-- S¹* : Type
-- S¹* = Susp Bool

-- S³* : Type
-- S³* = Susp (Susp (Susp Bool))

-- open import Cubical.HITs.S3
-- open import Cubical.HITs.Join
-- S¹*S¹→S³ :  join S¹ S¹ → S₊ 2
-- S¹*S¹→S³ (inl x) = north
-- S¹*S¹→S³ (inr x) = north
-- S¹*S¹→S³ (push base b i) = north
-- S¹*S¹→S³ (push (loop j) base i) = north
-- S¹*S¹→S³ (push (loop i) (loop j) k) = (sym (rCancel surf') ∙∙ EH 0 surf' (sym surf') ∙∙ lCancel surf') k i j

-- c : Iso S³* TotalHopf
-- fun c north = north , base
-- fun c south = north , base
-- fun c (merid a i) = h1 a i , S³≡S³ a i
--   where
--   h1 : (a : Susp (Susp Bool)) → Path (S₊ 2) north north
--   h1 north = refl
--   h1 south = refl
--   h1 (merid north i) j = (surf' ∙ sym (surf')) i j
--   h1 (merid south i) j = (sym surf' ∙ surf') i j
--   h1 (merid (merid false k) i) j  = (rCancel surf' ∙ sym (lCancel surf')) k i j 
--   h1 (merid (merid true k) i) j = EH 0 surf' (sym surf') k i j

--   S³≡S³ : (a : Susp (Susp Bool)) → PathP (λ i → HopfSuspS¹ (h1 a i)) base base 
--   S³≡S³ north = refl
--   S³≡S³ south = refl
--   S³≡S³ (merid a i) = {!!} -- help a i
--     where
--     sl : {!(j : I) → !}
--     sl = {!!}
--     l : (j : I) (x : Susp (Susp Bool)) (p : north ≡ x) → Path (PathP {!!} {!!} {!!}) (λ j → transp (λ i₂ → HopfSuspS¹ (h1 (p i₂) j)) i0 base) {!!}
--     l = {!!}
    
--     s : (a : _) → (λ j → transp (λ i₂ → HopfSuspS¹ (h1 (merid a i₂) j)) i0 base) ≡ refl
--     s x = {!!}
--     help : (a : _) → SquareP (λ i j → HopfSuspS¹ (h1 (merid a i) j)) refl refl refl refl
--     help a = toPathP (transportRefl _ ∙ s a)

--   h : (a : S₊ 2) → Path TotalHopf (north , base) (north , base)
--   h a = cong₂ _,_ refl {!!}
--     where
--     help : (a : S₊ 2) → PathP (λ i → Glue S¹ (Border base i)) base base
--     help = {!!}
-- inv c = {!!}
-- rightInv c = {!!}
-- leftInv c = {!!}


-- hej : S₊ 2 → Type₀
-- hej north = S¹
-- hej south = S¹
-- hej (merid a i) = {!!}

-- sauto : S¹ → I → S¹
-- sauto base i = base
-- sauto (loop j) i =
--   hcomp (λ k → λ {(i = i0) → loop (j ∨ k)
--                  ; (i = i1) → base
--                  ; (j = i0) → loop (i ∨ k)
--                  ; (j = i1) → base})
--         (loop (i ∨ j))

-- open import Cubical.HITs.S1 renaming (_·_ to _*_)
-- S₊2→Type : S₊ 2 → Type
-- S₊2→Type north = typ (Ω (S₊∙ 2))
-- S₊2→Type south = typ (Ω (S₊∙ 2))
-- S₊2→Type (merid a i) = l i
--   where
--   h : (a : S¹) → isEquiv λ p → p ∙ merid (sauto a i) ∙ sym (merid base)
--   h = sphereElim 0 (λ _ → isPropIsEquiv _) (subst isEquiv (λ j p → ((cong (p ∙_) (rCancel (merid base))) ∙ sym (rUnit p)) (~ j))
--                    (idEquiv _ .snd))

--   l : typ (Ω (S₊∙ 2)) ≡ typ (Ω (S₊∙ 2))
--   l = ua ((λ p → p ∙ merid (sauto a i) ∙ sym (merid base)) , h a) -- ua (a *_ , (rotIsEquiv a))

-- t2 : hLevelTrunc 3 ((typ ((Ω^ 2) (S₊∙ 2)))) → S¹
-- t2 = {!!}

-- test : ℤ
-- test = Iso.fun (fst (Hⁿ-Sⁿ≅ℤ 1)) ∣ {!!} ∣₂

-- S2-add : hLevelTrunc 5 (S₊ 2) → hLevelTrunc 5 (S₊ 2) → hLevelTrunc 4 (S₊ 2)
-- S2-add = trRec2 {!!} (wedgeconFun 1 1 (λ _ _ → isOfHLevelTrunc {!!}) {!!} {!!} {!!})

-- CP² : Type
-- CP² = Pushout {A = TotalHopf} fst λ _ → tt

-- characFunSpaceCP² : ∀ {ℓ} {A : Type ℓ}
--   → Iso (CP² → A) (Σ[ x ∈ A ] Σ[ f ∈ (S₊ (suc (suc zero)) → A) ]
--          ((y : TotalHopf) → f (fst y) ≡ x))
-- fun characFunSpaceCP² f = (f (inr tt)) , ((f ∘ inl ) , (λ a → cong f (push a)))
-- inv characFunSpaceCP² (a , f , p) (inl x) = f x
-- inv characFunSpaceCP² (a , f , p) (inr x) = a
-- inv characFunSpaceCP² (a , f , p) (push b i) = p b i
-- rightInv characFunSpaceCP² _ = refl
-- leftInv characFunSpaceCP² _ =
--   funExt λ { (inl x) → refl
--            ; (inr x) → refl
--            ; (push a i) → refl}

-- H⁰CP²≅ℤ : GroupIso (coHomGr 0 CP²) ℤGroup
-- H⁰CP²≅ℤ =
--   H⁰-connected (inr tt)
--     (PushoutToProp (λ _ → squash)
--       (sphereElim _ (λ _ → isOfHLevelSuc 1 squash)
--         ∣ sym (push (north , base)) ∣₁)
--     λ _ → ∣ refl ∣₁)

-- module M = MV (S₊ 2) Unit TotalHopf fst (λ _ → tt)

-- H²CP²≅ℤ : GroupIso (coHomGr 2 CP²) ℤGroup
-- H²CP²≅ℤ = compGroupIso (BijectionIso→GroupIso bij)
--             (compGroupIso (invGroupIso trivIso) (Hⁿ-Sⁿ≅ℤ 1))
--   where
--   isContrH¹TotalHopf : isContr (coHom 1 TotalHopf)
--   isContrH¹TotalHopf =
--     isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
--       (isOfHLevelRetractFromIso 0 ((fst (H¹-Sⁿ≅0 1))) isContrUnit)

--   isContrH²TotalHopf : isContr (coHom 2 TotalHopf)
--   isContrH²TotalHopf =
--     isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
--       ((isOfHLevelRetractFromIso 0
--         (fst (Hⁿ-Sᵐ≅0 1 2 λ p → snotz (sym (cong predℕ p)))) isContrUnit))

--   trivIso : GroupIso (coHomGr 2 (Susp S¹)) (×coHomGr 2 (Susp S¹) Unit)
--   fun (fst trivIso) x = x , 0ₕ _
--   inv (fst trivIso) = fst
--   rightInv (fst trivIso) (x , p) =
--     ΣPathP (refl , isContr→isProp (isContrHⁿ-Unit 1) _ _)
--   leftInv (fst trivIso) x = refl
--   snd trivIso = makeIsGroupHom λ _ _ → refl

--   bij : BijectionIso (coHomGr 2 CP²) (×coHomGr 2 (Susp S¹) Unit)
--   BijectionIso.fun bij = M.i 2
--   BijectionIso.inj bij x p =
--     pRec (squash₂ _ _)
--       (uncurry (λ z q
--         → sym q
--         ∙∙ cong (fst (M.d 1)) (isContr→isProp isContrH¹TotalHopf z (0ₕ _))
--         ∙∙ (M.d 1) .snd .pres1))
--       (M.Ker-i⊂Im-d 1 x p)
--     where
--     help : isInIm (M.d 1) x
--     help = M.Ker-i⊂Im-d 1 x p
--   BijectionIso.surj bij y =
--     M.Ker-Δ⊂Im-i 2 y (isContr→isProp isContrH²TotalHopf _ _)

-- H⁴CP²≅ℤ : GroupIso (coHomGr 4 CP²) ℤGroup
-- H⁴CP²≅ℤ = compGroupIso (invGroupIso (BijectionIso→GroupIso bij))
--           (compGroupIso help (Hⁿ-Sⁿ≅ℤ 2))
--   where
--   help : GroupIso (coHomGr 3 TotalHopf) (coHomGr 3 (S₊ 3))
--   help = isoType→isoCohom 3 (invIso IsoS³TotalHopf)

--   bij : BijectionIso (coHomGr 3 TotalHopf) (coHomGr 4 CP²)
--   BijectionIso.fun bij = M.d 3
--   BijectionIso.inj bij x p =
--     pRec (squash₂ _ _)
--          (uncurry (λ z q →
--              sym q
--           ∙∙ cong (M.Δ 3 .fst)
--                 (isOfHLevelΣ 1 (isContr→isProp
--                   (isOfHLevelRetractFromIso 0
--                     (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p))) isContrUnit))
--                 (λ _ → isContr→isProp (isContrHⁿ-Unit 2))
--                 z (0ₕ _ , 0ₕ _))
--           ∙∙ M.Δ 3 .snd .pres1))
--          (M.Ker-d⊂Im-Δ _ x p)
--   BijectionIso.surj bij y =
--     M.Ker-i⊂Im-d 3 y (isOfHLevelΣ 1
--       (isContr→isProp (isOfHLevelRetractFromIso 0
--         (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))) isContrUnit))
--         (λ _ → isContr→isProp (isContrHⁿ-Unit _)) _ _)


-- -- Characterisations of the trivial groups

-- private
--     elim-TotalHopf : (B : TotalHopf → Type)
--       → ((x : _) → isOfHLevel 3 (B x)) → B (north , base)
--       → (x : _) → B x
--     elim-TotalHopf =
--       transport (λ i → (B : isoToPath IsoS³TotalHopf i → Type)
--         → ((x : _) → isOfHLevel 3 (B x))
--           → B (transp (λ j → isoToPath IsoS³TotalHopf (i ∨ ~ j)) i (north , base)) → (x : _) → B x)
--           λ B hLev elim-TotalHopf → sphereElim _ (λ _ → hLev _) elim-TotalHopf

-- H¹-CP²≅0 : GroupIso (coHomGr 1 CP²) UnitGroup
-- H¹-CP²≅0 =
--   contrGroupIsoUnit
--     (isOfHLevelRetractFromIso 0 (setTruncIso characFunSpaceCP²)
--     (isOfHLevelRetractFromIso 0 lem₂ lem₃))
--   where
--   lem₁ : (f : (Susp S¹ → coHomK 1)) → ∥ (λ _ → 0ₖ _) ≡ f ∥
--   lem₁ f = pMap (λ p → p)
--                 (Iso.fun PathIdTrunc₀Iso (isOfHLevelRetractFromIso 1
--                   (fst (Hⁿ-Sᵐ≅0 0 1 (λ p → snotz (sym p)))) isPropUnit (0ₕ _) ∣ f ∣₂))

--   lem₂ : Iso ∥ (Σ[ x ∈ coHomK 1 ] ( Σ[ f ∈ (Susp S¹ → coHomK 1) ] ((y : TotalHopf) → f (fst y) ≡ x))) ∥₂
--              ∥ (Σ[ f ∈ (Susp S¹ → coHomK 1) ] ((y : TotalHopf) → f (fst y) ≡ 0ₖ 1)) ∥₂
--   fun lem₂ = sMap (uncurry λ x → uncurry λ f p → (λ y → (-ₖ x) +ₖ f y) , λ y → cong ((-ₖ x) +ₖ_) (p y) ∙ lCancelₖ _ x)
--   inv lem₂ = sMap λ p → 0ₖ _ , p
--   rightInv lem₂ =
--     sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
--           λ {(f , p) → cong ∣_∣₂ (ΣPathP ((funExt (λ x → lUnitₖ _ (f x)))
--           , (funExt (λ y → sym (rUnit (λ i → (-ₖ 0ₖ 1) +ₖ p y i)))
--            ◁ λ j y i → lUnitₖ _ (p y i) j)))}
--   leftInv lem₂ =
--     sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
--       (uncurry (coHomK-elim _ (λ _ → isPropΠ (λ _ → squash₂ _ _))
--        (uncurry λ f p → cong ∣_∣₂ (ΣPathP (refl , (ΣPathP ((funExt (λ x → lUnitₖ _ (f x)))
--        , ((funExt (λ y → sym (rUnit (λ i → (-ₖ 0ₖ 1) +ₖ p y i)))
--          ◁ λ j y i → lUnitₖ _ (p y i) j)))))))))

--   lem₃ : isContr _
--   fst lem₃ = ∣ (λ _ → 0ₖ 1) , (λ _ → refl) ∣₂
--   snd lem₃ =
--     sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
--       (uncurry λ f → pRec (isPropΠ (λ _ → squash₂ _ _))
--       (J (λ f _ → (y : (y₁ : TotalHopf) → f (fst y₁) ≡ 0ₖ 1) →
--       ∣ (λ _ → 0ₖ 1) , (λ _ _ → 0ₖ 1) ∣₂ ≡ ∣ f , y ∣₂)
--       (λ y → cong ∣_∣₂ (ΣPathP ((funExt (λ z → sym (y (north , base)))) , toPathP (s y)))))
--       (lem₁ f))

--     where
--     s : (y : TotalHopf → 0ₖ 1 ≡ 0ₖ 1)
--      → transport (λ i → (_ : TotalHopf) → y (north , base) (~ i) ≡ ∣ base ∣)
--                   (λ _ _ → 0ₖ 1) ≡ y
--     s y = funExt (elim-TotalHopf _ (λ _ → isOfHLevelPath 3 (isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) _ _)
--                  λ k → transp (λ i → y (north , base) (~ i ∧ ~ k) ≡ ∣ base ∣) k
--                                 λ j → y (north , base) (~ k ∨ j))

-- Hⁿ-CP²≅0-higher : (n : ℕ) → ¬ (n ≡ 1) → GroupIso (coHomGr (3 +ℕ n) CP²) UnitGroup
-- Hⁿ-CP²≅0-higher n p = contrGroupIsoUnit ((0ₕ _) , (λ x → sym (main x)))
--   where
--   h : GroupHom (coHomGr (2 +ℕ n) TotalHopf) (coHomGr (3 +ℕ n) CP²)
--   h = M.d (2 +ℕ n)

--   propᵣ : isProp (fst (×coHomGr (3 +ℕ n) (Susp S¹) Unit))
--   propᵣ =
--     isPropΣ
--       (isOfHLevelRetractFromIso 1
--          (fst (Hⁿ-Sᵐ≅0 (2 +ℕ n) 1 λ p → ⊥-rec (snotz (cong predℕ p)))) isPropUnit)
--       λ _ → isContr→isProp (isContrHⁿ-Unit _)

--   propₗ : isProp (coHom (2 +ℕ n) TotalHopf)
--   propₗ = subst (λ x → isProp (coHom (2 +ℕ n) x)) (isoToPath IsoS³TotalHopf)
--                (isOfHLevelRetractFromIso 1
--                  (fst (Hⁿ-Sᵐ≅0 (suc n) 2 λ q → p (cong predℕ q))) isPropUnit)

--   inIm : (x : coHom (3 +ℕ n) CP²) → isInIm h x
--   inIm x = M.Ker-i⊂Im-d (2 +ℕ n) x (propᵣ _ _)

--   main : (x : coHom (3 +ℕ n) CP²) → x ≡ 0ₕ _
--   main x =
--     pRec (squash₂ _ _)
--       (uncurry (λ f p → sym p ∙∙ cong (h .fst) (propₗ f (0ₕ _)) ∙∙ pres1 (snd h)))
--       (inIm x)

-- -- All trivial groups:
-- Hⁿ-CP²≅0 : (n : ℕ) → ¬ suc n ≡ 2 → ¬ suc n ≡ 4
--        → GroupIso (coHomGr (suc n) CP²) UnitGroup
-- Hⁿ-CP²≅0 zero p q = H¹-CP²≅0
-- Hⁿ-CP²≅0 (suc zero) p q = ⊥-rec (p refl)
-- Hⁿ-CP²≅0 (suc (suc zero)) p q = Hⁿ-CP²≅0-higher 0 λ p → snotz (sym p)
-- Hⁿ-CP²≅0 (suc (suc (suc zero))) p q = ⊥-rec (q refl)
-- Hⁿ-CP²≅0 (suc (suc (suc (suc n)))) p q =
--   Hⁿ-CP²≅0-higher (suc (suc n))
--     λ p → snotz (cong predℕ p)

-- -- Another Brunerie number
-- ℤ→HⁿCP²→ℤ : ℤ → ℤ
-- ℤ→HⁿCP²→ℤ x =
--   Iso.fun (fst H⁴CP²≅ℤ)
--     (Iso.inv (fst H²CP²≅ℤ) x ⌣ Iso.inv (fst H²CP²≅ℤ) x)

-- brunerie2 : ℤ
-- brunerie2 = ℤ→HⁿCP²→ℤ 1

-- {-
-- |brunerie2|≡1 : abs (ℤ→HⁿCP²→ℤ 1) ≡ 1
-- |brunerie2|≡1 = refl
-- -}

-- t : ∀ (a : TotalHopf) → ∣ fst a ∣ ≡ 0ₖ 2
-- t = {!!}

-- one : coHom 2 CP²
-- one = ∣ (λ { (inl x) → ∣ x ∣
--            ; (inr x) → 0ₖ _
--            ; (push a i) → t a i}) ∣₂


-- CP²→CP⁴ : (x : coHom 2 CP²) → coHom 2 CP² → coHom 4 CP²
-- CP²→CP⁴ x f = f ⌣ x

-- zz : Iso.fun (fst H⁴CP²≅ℤ) (CP²→CP⁴ one one) ≡ 1
-- zz = {!pres1!} ∙∙ {!!} ∙∙ {!!}
-- open import Cubical.ZCohomology.Properties
-- CP4→CP2 : (x : coHom 2 CP²) → coHom 4 CP² → coHom 2 CP²
-- CP4→CP2 = sRec2 squash₂
--                  λ e f → ∣ (λ { (inl x) → {!!}
--                               ; (inr x) → {!!}
--                               ; (push a i) → {!!}}) ∣₂


-- CP' : (f : S₊∙ 3 →∙ S₊∙ 2) → Type₀
-- CP' f = Pushout {A = S₊ 3} (fst f) λ _ → tt

-- open import Cubical.Homotopy.Loopspace

-- contrH2 : (f : S₊ 2 → coHomK 4) → ∥ (λ x → 0ₖ 4) ≡ f ∥₂
-- contrH2 = {!!}

-- CP4→CP2'' : (f : S₊∙ 3 →∙ S₊∙ 2) → ∥ (Σ[ g ∈ (S₊ 2 → coHomK 4) ] ((a : S₊ 3) → g (fst f a) ≡ 0ₖ 4)) ∥₂
--                                   → ∥ ((S₊∙ 3 →∙ (Ω (coHomK-ptd 4)))) ∥₂
-- CP4→CP2'' (f , p) =
--   sRec squash₂
--     (uncurry λ g →
--       sRec (isSetΠ (λ _ → squash₂)) (J (λ g _ → (y : (a : Susp (Susp S¹)) → g (f a) ≡ 0ₖ 4)
--               → ∥ ((S₊∙ 3 →∙ (Ω (coHomK-ptd 4)))) ∥₂)
--                 λ p → ∣ (λ a → p a ∙ sym (p north)) , rCancel (p north) ∣₂)
--               (contrH2 g))

-- CP²' = CP' (fst ∘ Iso.fun (IsoS³TotalHopf) , refl)

-- gen0 : CP²' → coHomK 2
-- gen0 = {!!}

-- gen1 : CP²' → coHomK 4
-- gen1 (inl x) = 0ₖ 4
-- gen1 (inr x) = 0ₖ 4
-- gen1 (push a i) = Kn→ΩKn+1 3 ∣ a ∣ i


-- hehehe : S₊ 3 → S₊ 2
-- hehehe north = north
-- hehehe south = north
-- hehehe (merid north i) = north
-- hehehe (merid south i) = north
-- hehehe (merid (merid base i₁) i) = north
-- hehehe (merid (merid (loop k) j) i) =
--   (sym (rCancel surf') ∙∙ EH 0 surf' (sym surf') ∙∙ lCancel surf') i j k

-- wtf : (x : S₊ 2) → Σ[ y ∈ S₊ 3 ] hehehe y ≡ x
-- wtf north = north , refl
-- wtf south = north , merid base
-- wtf (merid base i) = north , λ j → (merid base (i ∧ j))
-- wtf (merid (loop j) i) = sq i j , {!!}
--   where
--   sq : Square {A = S₊ 3} (refl {x = north}) refl refl refl
--   sq i j = hcomp (λ k → λ {(i = i0) → north
--                           ; (i = i1) → merid north (~ k)
--                           ; (j = i0) → merid north (~ k ∧ i)
--                           ; (j = i1) → merid {!!} (i ∧ ~ k)})
--                  (merid (merid (loop j) j) i)


-- -- sl : S₊ 2 → Type
-- -- sl north = S¹
-- -- sl south = S¹
-- -- sl (merid base i) = S¹
-- -- sl (merid (loop j) i) = h i j
-- --   where
-- --   h : Square (refl {x = S¹}) (λ _ → S¹) (λ _ → S¹) λ _ → S¹
-- --   h i j = Glue {!HopfSuspS¹ (merid base i)!}
-- --                λ { (i = i0) → S¹ , {!!}
-- --                  ; (i = i1) → {!!}
-- --                  ; (j = i0) → {!!}
-- --                  ; (j = i1) → {!!}}

-- -- CP7 : Type₀
-- -- CP7 = Pushout hehehe λ _ → tt

-- -- indMap : typ ((Ω^ 4) (coHomK-ptd 4)) → CP7 → coHomK 4
-- -- indMap P (inl x) = 0ₖ 4
-- -- indMap P (inr x) = 0ₖ 4
-- -- indMap P (push north i) = 0ₖ 4
-- -- indMap P (push south i) = 0ₖ 4
-- -- indMap P (push (merid north j) i) = 0ₖ 4
-- -- indMap P (push (merid south j) i) = 0ₖ 4
-- -- indMap P (push (merid (merid base i₁) j) i) = 0ₖ 4
-- -- indMap P (push (merid (merid (loop l) k) j) i) = P i j k l

-- -- ss : Iso ∥ (CP7 → coHomK 4) ∥₂ ∥ (Σ[ x ∈ coHomK 4 ] Σ[ f ∈ (S₊ 2 → coHomK 4) ] ((a : S₊ 3) → f (hehehe a) ≡ x)) ∥₂
-- -- fun ss = sMap λ f → (f (inr tt)) , ((f ∘ inl) , (λ a → cong f (push a)))
-- -- inv ss = sMap λ {(pt , f , p) → λ { (inl x) → f x ; (inr x) → pt ; (push a i) → p a i}}
-- -- rightInv ss = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _) (λ x → refl)
-- -- leftInv ss = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- --                    λ f → cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl})

-- -- ss2 : Iso (∥ (Σ[ x ∈ coHomK 4 ] Σ[ f ∈ (S₊ 2 → coHomK 4) ] ((a : S₊ 3) → f (hehehe a) ≡ x)) ∥₂)
-- --           ∥ (Σ[ f ∈ (S₊ 2 → coHomK 4) ] ((a : S₊ 3) → f (hehehe a) ≡ 0ₖ 4)) ∥₂
-- -- fun ss2 =
-- --   sRec squash₂ (uncurry (coHomK-elim 3 (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelSuc 3 (isOfHLevelSuc 2 squash₂))
-- --        ∣_∣₂))
-- -- inv ss2 = sMap λ p → (0ₖ 4 , p)
-- -- rightInv ss2 = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _) λ _ → refl
-- -- leftInv ss2 =
-- --   sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- --         (uncurry (coHomK-elim 3
-- --           (λ _ → isOfHLevelΠ 4
-- --             λ _ → isOfHLevelPath 4
-- --               (isOfHLevelSuc 3 (isOfHLevelSuc 2 squash₂)) _ _) λ _ → refl))
-- -- open import Cubical.Homotopy.Connected

-- -- truncLem : (f : (S₊ 2 → coHomK 4)) → ∥ (λ x → 0ₖ 4) ≡ f ∥₂
-- -- truncLem f =
-- --   sRec squash₂
-- --        (λ hs → sRec squash₂
-- --          (λ h → sRec squash₂ (λ m-b → sRec squash₂ (λ m-l → ∣ funExt (λ { north → h
-- --                                                    ; south → hs
-- --                                                    ; (merid base i) → m-b i
-- --                                                    ; (merid (loop j) i) k → m-l j i k} ) ∣₂)
-- --                       (final (f north) (f south) h hs (cong f (merid base)) m-b (λ j i → f (merid (loop j) i))))
-- --                       (h-m-b (f north) (f south) h hs (cong f (merid base))))
-- --          (h (f north))) (h (f south))
-- --   where
-- --   h : (x : coHomK 4) → ∥ 0ₖ 4 ≡ x ∥₂
-- --   h = coHomK-elim _ (λ _ → isOfHLevelSuc 3 (isOfHLevelSuc 2 squash₂)) ∣ refl ∣₂

-- --   stupid : isConnected (1 +ℕ 4) (coHomK 4)
-- --   stupid = isConnectedKn 3

-- --   h-m-b : (x y : coHomK 4) → (p : 0ₖ 4 ≡ x) (q : 0ₖ 4 ≡ y) (z : x ≡ y) → ∥ PathP (λ i → 0ₖ 4 ≡ z i) p q ∥₂
-- --   h-m-b x y p q z = trElim {B = λ _ → ∥ PathP (λ i → 0ₖ 4 ≡ z i) p q ∥₂} (λ _ → squash₂) ∣_∣₂
-- --                            (isConnectedPathP 2 {A = λ i → 0ₖ 4 ≡ z i} (isConnectedPath 3 (isConnectedSubtr 4 1 stupid) _ _) p q .fst)

-- --   final : (x y : coHomK 4) → (p : 0ₖ 4 ≡ x) (q : 0ₖ 4 ≡ y) (z : x ≡ y) (w : PathP (λ i → 0ₖ 4 ≡ z i) p q) (r : z ≡ z)
-- --         → ∥ PathP (λ j → PathP (λ i → 0ₖ 4 ≡ r j i) p q) w w ∥₂
-- --   final x y p q z w r =
-- --     trRec {B = ∥ PathP (λ j → PathP (λ i → 0ₖ 4 ≡ r j i) p q) w w ∥₂}
-- --           squash₂
-- --           ∣_∣₂
-- --           (isConnectedPathP 2 {A = (λ j → PathP (λ i → 0ₖ 4 ≡ r j i) p q) }
-- --             (isConnectedPathP 3 (isConnectedPath 4 (isConnectedKn 3) _ _) _ _) w w .fst)

-- -- truncLemHLev : (f : (S₊ 2 → coHomK 4)) → isContr ∥ (λ x → 0ₖ 4) ≡ f ∥₂
-- -- truncLemHLev f =
-- --   isOfHLevelRetractFromIso 0
-- --     (compIso setTruncTrunc2Iso (invIso (PathIdTruncIso 2)))
-- --       (isOfHLevelPath 0 (∣ (λ _ → 0ₖ 4) ∣ , (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ f → sRec (isOfHLevelTrunc 3 _ _) (cong ∣_∣) (truncLem f))) _ _)

-- -- FF : (f : (S₊ 2 → coHomK 4)) → ∥ (λ _ → 0ₖ 4) ≡ f ∥₂ → ((a : S₊ 3) → f (hehehe a) ≡ 0ₖ 4) → ∥ (S₊ 3 → 0ₖ 4 ≡ 0ₖ 4) ∥₂
-- -- FF f = sRec (isSetΠ (λ _ → squash₂)) λ id p →  ∣ (λ x → funExt⁻ id (hehehe x) ∙ (p x)) ∣₂

-- -- sll : (S₊ 3 → 0ₖ 4 ≡ 0ₖ 4) → CP7 → coHomK 4
-- -- sll f (inl x) = 0ₖ 4
-- -- sll f (inr x) = 0ₖ 4
-- -- sll f (push a i) = f a i

-- -- ssl* : ∥ (S₊ 3 → 0ₖ 4 ≡ 0ₖ 4) ∥₂ → ∥ (CP7 → coHomK 4) ∥₂
-- -- ssl* = sMap sll

-- -- ss3 : Iso ∥ (Σ[ f ∈ (S₊ 2 → coHomK 4) ] ((a : S₊ 3) → f (hehehe a) ≡ 0ₖ 4)) ∥₂ ∥ (S₊ 3 → 0ₖ 4 ≡ 0ₖ 4) ∥₂
-- -- fun ss3 = sRec squash₂ (uncurry (λ f → FF f (truncLem f)))
-- -- inv ss3 = sMap λ f → (λ _ → 0ₖ 4) , f
-- -- rightInv ss3 = sElim {!!} λ f → {!λ i → FF (λ _ → 0ₖ 4) (h i) f!} ∙ {!!}
-- --   where
-- --   h : truncLem (λ _ → 0ₖ _) ≡ ∣ refl ∣₂
-- --   h = {!cong ∣_∣₂ ?!}
-- -- leftInv ss3 = {!!}

-- -- s : ∀ (f : CP7 → coHomK 4) → Σ[ P ∈ (S₊∙ 3 →∙ Ω (coHomK-ptd 4)) ]
-- --                               ∣ f ∣₂ ≡ ∣ sll (fst P) ∣₂
-- -- s f = (transport (λ i → Σ[ P ∈ (S₊∙ 3 →∙ Ω (coHomK-ptd 4)) ]
-- --                               Iso.leftInv myIso ∣ f ∣₂ i ≡ ∣ sll (fst P) ∣₂)
-- --                  ((sRec l (λ f → (λ x → f x ∙ sym (f north)) , rCancel (f north)) (Iso.fun myIso ∣ f ∣₂)) ,
-- --                  mainLem (Iso.fun myIso ∣ f ∣₂)))
-- --   where
-- --   myIso : Iso _ _
-- --   myIso = compIso ss (compIso ss2 ss3)

-- --   ll : (f : Susp (Susp S¹) → 0ₖ 4 ≡ 0ₖ 4) → ∥ f north ≡ refl ∥₂
-- --   ll f = trRec squash₂ ∣_∣₂
-- --          (isConnectedPath 2 (isConnectedSubtr 3 1 (isConnectedPathKn 3 (0ₖ 4) (0ₖ 4))) (f north) refl .fst)

-- --   l : isSet (S₊∙ 3 →∙ Ω (coHomK-ptd 4))
-- --   l = subst isSet (λ i → S₊∙ 3 →∙ Kn≃ΩKn+1∙ {n = 3} i)
-- --             (isOfHLevel↑∙' 0 2)

-- --   kaha : (f : _) → inv myIso ∣ f ∣₂ ≡ ∣ sll f ∣₂
-- --   kaha f = cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl})

-- --   mainLem : (f : _) → inv myIso f ≡ 
-- --       ∣ sll (fst (sRec l (λ f₁ → (λ x → f₁ x ∙ (λ i → f₁ north (~ i))) , rCancel (f₁ (snd (S₊∙ 3))))
-- --         f)) ∣₂
-- --   mainLem = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
-- --                   λ f → sRec (isOfHLevelPath 2 squash₂ _ _)
-- --                     (λ p → kaha f ∙ cong ∣_∣₂ (cong sll ((λ i x → rUnit (f x) i) ∙ λ i x → f x ∙ sym (p (~ i)))))
-- --                       (ll f)

-- -- genCP7 : coHom 4 CP7
-- -- genCP7 = ∣ (λ { (inl x) → 0ₖ 4
-- --              ; (inr x) → 0ₖ 4
-- --              ; (push a i) → Kn→ΩKn+1 3 ∣ a ∣ i}) ∣₂

-- -- heheid : (a : _) → ∣ hehehe a ∣ ≡ 0ₖ (suc (suc zero))
-- -- heheid = sphereElim _ (λ _ → isOfHLevelTrunc 4 _ _) refl

-- -- gen2CP7 : coHom 4 CP7
-- -- gen2CP7 = ∣ (λ { (inl x) → _⌣ₖ_ {n = 2} {m = 2} ∣ x ∣ ∣ x ∣
-- --                ; (inr x) → 0ₖ 4
-- --                ; (push a i) → heheid a i ⌣ₖ heheid a i}) ∣₂


-- -- testS : gen2CP7 ≡ genCP7
-- -- testS =
-- --   cong ∣_∣₂
-- --     (funExt λ { (inl north) → refl
-- --               ; (inl south) → refl
-- --               ; (inl (merid a i)) j → h a j i
-- --               ; (inr x) → {!!}
-- --               ; (push a i) → {!!}})
-- --   where
-- --   h : (a : S¹) → cong₂ (_⌣ₖ_ {n = 2} {m = 2}) (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (merid a)) ≡ λ i → 0ₖ 4
-- --   h = {!!}

-- -- gen2 : coHom 2 CP7
-- -- gen2 = ∣ (λ { (inl x) → ∣ x ∣ ; (inr x) → 0ₖ 2 ; (push a i) → heheid a i}) ∣₂

-- -- open import Cubical.HITs.S1 renaming (_·_ to _*_)
-- -- hopfSurj' : (x : S₊ 2) → HopfSuspS¹ x
-- -- hopfSurj' north = base
-- -- hopfSurj' south = base
-- -- hopfSurj' (merid a i) = {!!}
-- --   where
-- --   k : (a : _) → PathP (λ i → Glue S¹ (Border a i)) base base
-- --   k a = toPathP ((λ i → a * base) ∙ {!!})

-- -- -- hopfSurj : (x : S₊ 2) → Σ[ s ∈ S₊ 3 ] fst (JoinS¹S¹→TotalHopf (S³→joinS¹S¹ (inv IsoS³S3 s))) ≡ x
-- -- -- hopfSurj x = (Iso.inv (IsoS³TotalHopf) (x , l x)) , cong fst (Iso.rightInv (IsoS³TotalHopf) (x , l x))

-- -- -- gen2 : (p : (a : S₊ 3) → ∣ fst (JoinS¹S¹→TotalHopf (S³→joinS¹S¹ (inv IsoS³S3 a))) ∣ ≡ 0ₖ 2)
-- -- --                       → CP²' → coHomK 4
-- -- -- gen2 p (inl x) = _⌣ₖ_ {n = 2} {m = 2} ∣ x ∣ ∣ x ∣
-- -- -- gen2 p (inr x) = 0ₖ _
-- -- -- gen2 p (push a i) = p a i ⌣ₖ p a i

-- -- -- gen≡ : (p : _) (a : _) → gen1 a ≡ gen2 p a
-- -- -- gen≡ p (inl x) = (λ i → p (fst (hopfSurj x)) (~ i) ⌣ₖ p (fst (hopfSurj x)) (~ i))
-- -- --                 ∙ λ i → _⌣ₖ_ {n = 2} {m = 2} ∣ hopfSurj x .snd i ∣ ∣ hopfSurj x .snd i ∣
-- -- -- gen≡ p (inr x) = refl
-- -- -- gen≡ p (push a i) = {!!}


-- -- -- -- CP4→CP2''' : (f : S₊∙ 3 →∙ S₊∙ 2) → ∥ (S₊∙ 3 →∙ (Ω (coHomK-ptd 4))) ∥₂ → coHom 2 (CP' f)
-- -- -- -- CP4→CP2''' f = sRec squash₂ λ f → ∣ (λ { (inl x) → ΩKn+1→Kn 2 (cong (ΩKn+1→Kn 3) (h x f))
-- -- -- --                                         ; (inr x) → 0ₖ 2
-- -- -- --                                         ; (push a i) → {!!}}) ∣₂
-- -- -- --   where
-- -- -- --   h : (x : S₊ 2) (f : ((S₊∙ 3 →∙ (Ω (coHomK-ptd 4))))) → typ ((Ω^ 2) (coHomK-ptd 4))
-- -- -- --   h x f i j =
-- -- -- --     hcomp (λ k → λ { (i = i0) → 0ₖ 4
-- -- -- --                     ; (i = i1) → 0ₖ 4
-- -- -- --                     ; (j = i0) → snd f k i
-- -- -- --                     ; (j = i1) → snd f k i})
-- -- -- --           (fst f ((merid x ∙ sym (merid north)) j) i)

-- -- -- -- CP4→CP2' : (f : S₊∙ 3 →∙ S₊∙ 2) (x : coHom 2 (CP' f)) → coHom 4 (CP' f) → coHom 2 (CP' f)
-- -- -- -- CP4→CP2' f =
-- -- -- --   sRec2 squash₂
-- -- -- --     λ e g → ∣ (λ { (inl x) → ΩKn+1→Kn 2 ({!g!} ∙∙ cong (ΩKn+1→Kn 3) {!λ i j → g (push (merid x i)) j!} ∙∙ {!!})
-- -- -- --                  ; (inr x) → {!!}
-- -- -- --                  ; (push a i) → {!!}}) ∣₂
-- -- -- --   where
-- -- -- --   h : (g : CP' f → coHomK 4) → g (inr tt) ≡ 0ₖ _ → g ∘ inl ≡ (λ x → 0ₖ _) → S₊ 2 → typ ((Ω^ 2) (coHomK-ptd 4))
-- -- -- --   h g gpd idf x i j =
-- -- -- --     hcomp (λ k → λ { (i = i0) → rCancelₖ 4 (g (push north j)) k
-- -- -- --                     ; (i = i1) → rCancelₖ 4 (g (push south j)) k
-- -- -- --                     ; (j = i0) → {!idf k ((fst f (merid x i))) -ₖ idf k ((fst f (merid north i)))!} -- idf k ((fst f (merid x i))) -ₖ gpd k
-- -- -- --                     ; (j = i1) → {!!}})
-- -- -- --           (g (push (merid x i) j) -ₖ g (push (merid north i) j))


-- -- contrfstIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → (s : isContr A) → Iso (Σ A B) (B (s .fst))
-- -- fun (contrfstIso {B = B} s) (a , b) = subst B (sym (snd s a)) b
-- -- inv (contrfstIso s) b = (fst s) , b
-- -- rightInv (contrfstIso {B = B} s) b = (λ i → subst B (sym (h i)) b) ∙ transportRefl b
-- --   where
-- --   h : snd s (fst s) ≡ refl
-- --   h = isProp→isSet (isContr→isProp s) _ _ _ _
-- -- leftInv (contrfstIso{B = B} s) (a , b) =
-- --   ΣPathP ((snd s a) , λ i → transp (λ j → B (snd s a (i ∨ ~ j))) i b)

-- -- miniFib : hLevelTrunc 3 (S₊ 2 → coHomK 4) → Type
-- -- miniFib x = trRec {B = TypeOfHLevel ℓ-zero 2} (isOfHLevelTypeOfHLevel 2) (λ f → (∥ ((x : S₊ 3) → f (hehehe x) ≡ 0ₖ 4) ∥₂) , squash₂) x .fst

-- -- l3 : isContr (hLevelTrunc 3 (S₊ 2 → coHomK 4))
-- -- l3 = {!!}

-- -- l7 : {!!}
-- -- l7 = {!!}
