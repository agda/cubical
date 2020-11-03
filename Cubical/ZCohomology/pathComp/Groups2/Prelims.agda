{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.pathComp.Groups2.Prelims where

open import Cubical.ZCohomology.pathComp.Base
open import Cubical.ZCohomology.pathComp.Properties2
open import Cubical.ZCohomology.pathComp.EilenbergIso
open import Cubical.ZCohomology.pathComp.MayerVietoris2

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv

open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; elim2 to trElim2 ; map to trMap ; rec to trRec)
open import Cubical.HITs.SetTruncation renaming (elim to sElim ; map to sMap ; rec to sRec)

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected

open import Cubical.ZCohomology.MayerVietoris2

infixr 33 _⋄_

_⋄_ : _
_⋄_ = compIso


0₀ = 0ₖ 0
0₁ = 0ₖ 1
0₂ = 0ₖ 2
0₃ = 0ₖ 3
0₄ = 0ₖ 4

S¹map : hLevelTrunc 3 S¹ → S¹
S¹map = trRec isGroupoidS¹ (idfun _)

S¹map-id : (x : hLevelTrunc 3 S¹) → Path (hLevelTrunc 3 S¹) ∣ S¹map x ∣ x
S¹map-id = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → refl

S1map : hLevelTrunc 3 (S₊ 1) → (S₊ 1)
S1map = trRec isGroupoidS¹ (idfun _)


{- Proof that (S¹ → ∥ S¹ ∥₁) ≃ S¹ × ℤ. Needed for H¹(S¹)) -}
-- We prove that (S¹ → ∥ S¹ ∥) ≃ S¹ × ℤ. Note that the truncation doesn't really matter, since S¹ is a groupoid.
-- Given a map f : S¹ → S¹, the idea is to send this to (f(base) , winding (f(loop))). For this to be
-- well-typed, we need to translate f(loop) into an element in Ω(S¹,base).

Iso-S¹→S¹-ΩS²×Ω²S² : Iso (S¹ → loopK 1) (Σ[ x ∈ loopK 1 ] x ≡ x)
Iso-S¹→S¹-ΩS²×Ω²S² = IsoFunSpaceS¹

test : Iso (typ (Ω (loopK 1 , refl))) Int
test = congIso (invIso (Iso-Kn-ΩKn+1 1)) ⋄ invIso (Iso-Kn-ΩKn+1 0)

abstract
  testFunct : (p q : typ (Ω (loopK 1 , refl))) → Iso.fun test (p ∙ q) ≡ (Iso.fun test p +ℤ Iso.fun test q)
  testFunct p q = cong (Iso.inv (Iso-Kn-ΩKn+1 0)) (congFunct (Iso.inv (Iso-Kn-ΩKn+1 1)) p q)
                ∙∙ cong winding (congFunct (Iso.fun ((truncIdempotentIso 3 isGroupoidS¹))) (cong (Iso.inv (Iso-Kn-ΩKn+1 1)) p) (cong (Iso.inv (Iso-Kn-ΩKn+1 1)) q)) 
                ∙∙ winding-hom (cong (Iso.fun ((truncIdempotentIso 3 isGroupoidS¹))) (cong (Iso.inv (Iso-Kn-ΩKn+1 1)) p))
                               (cong (Iso.fun ((truncIdempotentIso 3 isGroupoidS¹))) (cong (Iso.inv (Iso-Kn-ΩKn+1 1)) q))

hahah : (n : ℕ) (x : loopK n) → Iso (loopK n) (loopK n)
Iso.fun (hahah n x) y = y ∙ sym x
Iso.inv (hahah n x) y = y ∙ x
Iso.rightInv (hahah n x) y = sym (assoc y x (sym x)) ∙∙ cong (y ∙_) (rCancel x) ∙∙ sym (rUnit y)
Iso.leftInv (hahah n x) y = sym (assoc y (sym x) x) ∙∙ cong (y ∙_) (lCancel x) ∙∙ sym (rUnit y)

hahah2 : (n : ℕ) (x : loopK n) → Iso (x ∙ sym x ≡ x ∙ sym x) (typ (Ω ((loopK n) , refl)))
Iso.fun (hahah2 n x) p = wrapItUp p (rCancel x)
Iso.inv (hahah2 n x) p = wrapItUp p (sym (rCancel x))
Iso.rightInv (hahah2 n x) p = wrapInv p (sym (rCancel x))
Iso.leftInv (hahah2 n x) p = wrapInv p (rCancel x)

maybe2 : (n : ℕ) → (x : loopK n) → Iso (x ≡ x) (typ (Ω ((loopK n) , refl)))
maybe2 n x = congIso (hahah n x) ⋄ hahah2 n x

abstract
  maybe2Funct : (n : ℕ) → (x : loopK n) → (p q : x ≡ x) → Iso.fun (maybe2 n x) (p ∙ q) ≡ Iso.fun (maybe2 n x) p ∙ Iso.fun (maybe2 n x) q
  maybe2Funct n x p q = cong (Iso.fun (hahah2 n x)) (congFunct (Iso.fun (hahah n x)) p q)
                      ∙ wrapFunct (cong (_∙ sym x) p) (cong (_∙ sym x) q) (rCancel x)

nice! : Iso (Σ[ x ∈ loopK 1 ] x ≡ x) (loopK 1 × typ (Ω ((loopK 1) , refl)))
Iso.fun nice! (a , p) = a , (Iso.fun (maybe2 1 a) p)
Iso.inv nice! (a , p) = a , (Iso.inv (maybe2 1 a) p)
Iso.rightInv nice! (a , p) i = a , (Iso.rightInv (maybe2 1 a) p i)
Iso.leftInv nice! (a , p) i = a , (Iso.leftInv (maybe2 1 a) p i)

open import Cubical.Algebra.Group

halfway : GroupIso (coHomGr 1 S¹) (dirProd (auxGr ((loopK 1) , refl)) (auxGr ((coHomK 2) , _))) 
GroupHom.fun (GroupIso.map halfway) =
  sRec (isSet× setTruncIsSet setTruncIsSet)
       λ f → ∣ Iso.fun (IsoFunSpaceS¹ ⋄ nice!) f .snd ∣₂ ,  ∣ Iso.fun (IsoFunSpaceS¹ ⋄ nice!) f .fst ∣₂
GroupHom.isHom (GroupIso.map halfway) =
  coHomPointedElim2 _ base base
    (λ _ _ → isSet× setTruncIsSet setTruncIsSet _ _)
    λ f g fId gId → ΣPathP ((cong ∣_∣₂ (cong (Iso.fun (maybe2 1 (f base ∙ g base))) (cong₂Funct _∙_ (cong f loop) (cong g loop))
                            ∙∙ maybe2Funct 1 (f base ∙ g base) (cong (_∙ g base) (cong f loop)) (cong (f base ∙_) (cong g loop))
                            ∙∙ ((λ i → Iso.fun (maybe2 1 (f base ∙ gId i)) (cong (_∙ gId i) (cong f loop))
                                      ∙ Iso.fun (maybe2 1 (fId i ∙ g base)) (cong (fId i ∙_) (cong g loop)))
                              ∙ λ i → Iso.fun (maybe2 1 (rUnit (f base) (~ i))) (cong (λ x → rUnit x (~ i)) (cong f loop))
                                      ∙ Iso.fun (maybe2 1 (lUnit (g base) (~ i))) (cong (λ x → lUnit x (~ i)) (cong g loop)))))
                           , refl)
GroupIso.inv halfway = uncurry (rec2 setTruncIsSet λ p q → ∣ Iso.inv IsoFunSpaceS¹ (Iso.inv nice! (q , p)) ∣₂ )
GroupIso.rightInv halfway =
  uncurry (elim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
          λ p q → ΣPathP (cong ∣_∣₂ (cong snd (Iso.rightInv (IsoFunSpaceS¹ ⋄ nice!) (q , p)))
                         , cong ∣_∣₂ (cong fst (Iso.rightInv (IsoFunSpaceS¹ ⋄ nice!) (q , p)))))
GroupIso.leftInv halfway =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        λ f → cong ∣_∣₂ (Iso.leftInv (IsoFunSpaceS¹ ⋄ nice!) f)

nice!TOTAL : Iso (S¹ → loopK 1) (loopK 1 × Int)
nice!TOTAL = IsoFunSpaceS¹ ⋄ nice! ⋄ prodIso idIso test


halfway2 : GroupIso (auxGr ((loopK 1) , refl)) intGroup
halfway2 =
  Iso+Hom→GrIso (setTruncIdempotentIso (isOfHLevelTrunc 4 _ _ _ _) ⋄ test)
    (elim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) testFunct)

-- S1→K₁≡S1×Int : Iso ((S₊ 1) → coHomK 1) (coHomK 1 × Int)
-- S1→K₁≡S1×Int = S¹→S¹≡S¹×Int ⋄ prodIso (invIso (truncIdempotentIso 3 (isGroupoidS¹))) idIso
-- module _ (key : Unit') where
--   module P = lockedCohom key
--   private
--     _+K_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
--     _+K_ {n = n} = P.+K n

--     -K_ : {n : ℕ} → coHomK n → coHomK n
--     -K_ {n = n} = P.-K n

--     _-K_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
--     _-K_ {n = n} = P.-Kbin n

--   infixr 55 _+K_
--   infixr 55 -K_
--   infixr 56 _-K_

--   {- Proof that S¹→K2 is isomorphic to K2×K1 (as types). Needed for H²(T²)  -}
--   S1→K2≡K2×K1' : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
--   Iso.fun S1→K2≡K2×K1' f = f base , ΩKn+1→Kn 1 (sym (P.cancelK 2 (f base))
--                                              ∙∙ cong (λ x → (f x) -K f base) loop
--                                              ∙∙ P.cancelK 2 (f base))
--   Iso.inv S1→K2≡K2×K1' = invmap
--     where
--     invmap : (∥ Susp S¹ ∥ 4) × (∥ S¹ ∥ 3) → S¹ → ∥ Susp S¹ ∥ 4
--     invmap (a , b) base = a +K 0₂
--     invmap (a , b) (loop i) = a +K Kn→ΩKn+1 1 b i
--   Iso.rightInv S1→K2≡K2×K1' (a , b) = ΣPathP ((P.rUnitK 2 a)
--                                            , (cong (ΩKn+1→Kn 1) (doubleCompPath-elim' (sym (P.cancelK 2 (a +K 0₂)))
--                                              (λ i → (a +K Kn→ΩKn+1 1 b i) -K (a +K 0₂))
--                                              (P.cancelK 2 (a +K 0₂)))
--                                           ∙∙ cong (ΩKn+1→Kn 1) (congHelper2 (Kn→ΩKn+1 1 b) (λ x → (a +K x) -K (a +K 0₂))
--                                                                (funExt (λ x → sym (cancelHelper a x)))
--                                                                (P.cancelK 2 (a +K 0₂)))
--                                           ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 1) b))

--       module _ where
--       cancelHelper : (a b : coHomK 2) → (a +K b) -K (a +K 0₂) ≡ b
--       cancelHelper a b = cong (λ x → (a +K b) -K x) (P.rUnitK 2 a)
--                        ∙ P.-cancelLK 2 a b

--       congHelper2 : (p : 0₂ ≡ 0₂) (f : coHomK 2 → coHomK 2) (id : (λ x → x) ≡ f) → (q : (f 0₂) ≡ 0₂)
--                   → (sym q) ∙ cong f p ∙ q ≡ p
--       congHelper2 p f = J (λ f _ → (q : (f 0₂) ≡ 0₂) → (sym q) ∙ cong f p ∙ q ≡ p)
--                          λ q → (cong (sym q ∙_) (isCommΩK 2 p _) ∙∙ assoc _ _ _ ∙∙ cong (_∙ p) (lCancel q))
--                               ∙ sym (lUnit p)

--       conghelper3 : (x : coHomK 2) (p : x ≡ x) (f : coHomK 2 → coHomK 2) (id : (λ x → x) ≡ f) (q : f x ≡ x)
--                   → (sym q) ∙ cong f p ∙ q ≡ p
--       conghelper3 x p f = J (λ f _ → (q : (f x) ≡ x) → (sym q) ∙ cong f p ∙ q ≡ p)
--                             λ q → (cong (sym q ∙_) (isCommΩK-based 2 x p _) ∙∙ assoc _ _ _ ∙∙ cong (_∙ p) (lCancel q))
--                                       ∙  sym (lUnit p)
--   Iso.leftInv S1→K2≡K2×K1' a = funExt λ { base → P.rUnitK _ (a base)
--                                        ; (loop i) j → loopcase j i}
--     where
--     loopcase : PathP (λ i → P.rUnitK _ (a base) i ≡ P.rUnitK _ (a base) i)
--                      (cong (a base +K_) (Kn→ΩKn+1 1 (ΩKn+1→Kn 1 ((sym (P.cancelK 2 (a base))
--                            ∙∙ (λ i → a (loop i) -K (a (base)))
--                            ∙∙ P.cancelK 2 (a base))))))
--                      (cong a loop)
--     loopcase i j = hcomp (λ k → λ { (i = i0) → a base +K Kn→ΩKn+1 1 (ΩKn+1→Kn 1 (doubleCompPath-elim'
--                                                                                   (sym (P.cancelK 2 (a base)))
--                                                                                   (λ i₁ → a (loop i₁) -K a base)
--                                                                                   (P.cancelK 2 (a base)) (~ k))) j
--                                   ; (i = i1) → cong a loop j
--                                   ; (j = i0) → P.rUnitK 2 (a base) i
--                                   ; (j = i1) → P.rUnitK 2 (a base) i})
--                          (loopcase2 i j)

--        where

--        stupidAgda : (x : coHomK 2) (p : x ≡ x) (q : 0₂ ≡ x) → Kn→ΩKn+1 1 (ΩKn+1→Kn 1 (q ∙ p ∙ sym q)) ≡ q ∙ p ∙ sym q
--        stupidAgda x p q = Iso.rightInv (Iso-Kn-ΩKn+1 1) (q ∙ p ∙ sym q)

--        pathHelper : (a b : hLevelTrunc 4 (S₊ 2)) → a +K (b -K a) ≡ b
--        pathHelper a b = P.commK 2 a (b -K a) ∙ P.-+cancelK 2 b a

--        pathPHelper : PathP (λ i → pathHelper (a base) (a base) i ≡ pathHelper (a base) (a base) i)
--                            (cong (a base +K_) (λ i₁ → a (loop i₁) -K a base))
--                            λ i → a (loop i)
--        pathPHelper i j = pathHelper (a base) (a (loop j)) i

--        abstract
--          helperFun2 : {A : Type₀} {0A a b : A} (main : 0A ≡ 0A) (start : b ≡ b) (p : a ≡ a) (q : a ≡ b) (r : b ≡ 0A) (Q : a ≡ 0A)
--                       (R : PathP (λ i → Q i ≡ Q i) p main)
--                       → start ≡ sym q ∙ p ∙ q
--                       → isComm∙ (A , 0A)
--                       → sym r ∙ start ∙ r ≡ main
--          helperFun2 main start p q r Q R startId comm =
--              sym r ∙ start ∙ r           ≡[ i ]⟨ sym r ∙ startId i ∙ r ⟩
--              sym r ∙ (sym q ∙ p ∙ q) ∙ r ≡[ i ]⟨ sym r ∙ assoc (sym q) (p ∙ q) r (~ i) ⟩
--              sym r ∙ sym q ∙ (p ∙ q) ∙ r ≡[ i ]⟨ sym r ∙ sym q ∙ assoc p q r (~ i) ⟩
--              sym r ∙ sym q ∙ p ∙ q ∙ r ≡[ i ]⟨ assoc (sym r) (rUnit (sym q) i) (p ∙ lUnit (q ∙ r) i) i ⟩
--              (sym r ∙ sym q ∙ refl) ∙ p ∙ refl ∙ q ∙ r ≡[ i ]⟨ (sym r ∙ sym q ∙ λ j → Q (i ∧ j)) ∙ R i ∙ (λ j → Q ( i ∧ (~ j))) ∙ q ∙ r ⟩
--              (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ q ∙ r ≡[ i ]⟨ (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ symDistr (sym r) (sym q) (~ i) ⟩
--              (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ sym (sym r ∙ sym q) ≡[ i ]⟨ (assoc (sym r) (sym q) Q i) ∙ main ∙ symDistr (sym r ∙ sym q) Q (~ i) ⟩
--              ((sym r ∙ sym q) ∙ Q) ∙ main ∙ sym ((sym r ∙ sym q) ∙ Q)  ≡[ i ]⟨ ((sym r ∙ sym q) ∙ Q) ∙ comm main (sym ((sym r ∙ sym q) ∙ Q)) i ⟩
--              ((sym r ∙ sym q) ∙ Q) ∙ sym ((sym r ∙ sym q) ∙ Q) ∙ main ≡⟨ assoc ((sym r ∙ sym q) ∙ Q) (sym ((sym r ∙ sym q) ∙ Q)) main  ⟩
--              (((sym r ∙ sym q) ∙ Q) ∙ sym ((sym r ∙ sym q) ∙ Q)) ∙ main ≡[ i ]⟨ rCancel (((sym r ∙ sym q) ∙ Q)) i ∙ main ⟩
--              refl ∙ main ≡⟨ sym (lUnit main) ⟩
--              main ∎


--        helper : cong (a base +K_)
--                      (Kn→ΩKn+1 1
--                        (ΩKn+1→Kn 1
--                        (sym (P.cancelK 2 (a base))
--                          ∙ (λ i₁ → a (loop i₁) -K a base)
--                          ∙ P.cancelK 2 (a base))))
--                    ≡ _
--        helper = (λ i → cong (a base +K_) (stupidAgda (a base -K (a base))
--                                                       (λ i₁ → a (loop i₁) -K a base)
--                                                       (sym (P.cancelK 2 (a base))) i))
--              ∙ congFunct₃ (a base +K_) (sym (P.cancelK 2 (a base)))
--                                         (λ i₁ → a (loop i₁) -K a base)
--                                         (P.cancelK 2 (a base))
--          where
--          congFunct₃ : ∀ {A B : Type₀} {a b c d : A} (f : A → B) (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
--                     → cong f (p ∙ q ∙ r) ≡ cong f p ∙ cong f q ∙ cong f r
--          congFunct₃ f p q r = congFunct f p (q ∙ r)
--                             ∙ cong (cong f p ∙_) (congFunct f q r)

--        loopcase2 : PathP (λ i → P.rUnitK _ (a base) i ≡ P.rUnitK _ (a base) i)
--                      (cong (a base +K_) (Kn→ΩKn+1 1 (ΩKn+1→Kn 1 ((sym (P.cancelK 2 (a base))
--                            ∙ (λ i → a (loop i) -K (a (base)))
--                            ∙ P.cancelK 2 (a base))))))
--                      (cong a loop)
--        loopcase2 = compPathL→PathP (helperFun2 (cong a loop)
--                                             _
--                                             _
--                                             (cong (a base +K_) (P.cancelK 2 (a base)))
--                                             _
--                                             _
--                                             pathPHelper
--                                             helper
--                                             (isCommΩK-based 2 (a base)))


-- -- The translation mention above uses the basechange function.

-- ---------- lemmas on the baschange of ΩS¹ ----------

-- --The following lemma is used to prove the basechange2⁻ preserves
-- -- path composition (in a more general sense than what is proved in basechange2⁻-morph)

-- basechange-lemma : ∀ {ℓ} {A : Type ℓ} {a : A} (x y : S¹) (F : a ≡ a → S¹) (f : S¹ → a ≡ a) (g : S¹ → a ≡ a)
--                   → (f base ≡ refl)
--                   → (g base ≡ refl)
--                   → basechange2⁻ (F (f base ∙ g base)) (cong₂ {A = S¹} {B = λ x → S¹} (λ x y → F (f x ∙ g y)) loop loop)
--                    ≡ basechange2⁻ (F (f base)) (cong (λ x → F (f x)) loop) ∙ basechange2⁻ (F (g base)) (cong (λ x → F (g x)) loop)
-- basechange-lemma x y F f g frefl grefl  =
--     ((λ i → basechange2⁻ (F (f base ∙ g base)) (cong₂Funct (λ x y → F (f x ∙ g y)) loop loop i))
--   ∙∙ (λ i → basechange2⁻ (F (f base ∙ g base)) (cong (λ x₁ → F (f x₁ ∙ g base)) loop ∙ cong (λ y₁ → F (f base ∙ g y₁)) loop))
--   ∙∙ basechange2⁻-morph (F (f base ∙ g base)) _ _)
--   ∙∙ (λ j → basechange2⁻ (F (f base ∙ grefl j))
--                         (λ i → F (f (loop i) ∙ grefl j))
--           ∙ basechange2⁻ (F (frefl j ∙ g base))
--                         (λ i → F (frefl j ∙ g (loop i))))
--   ∙∙ ((λ j → basechange2⁻ (F (rUnit (f base) (~ j)))
--                         (λ i → F (rUnit (f (loop i)) (~ j)))
--           ∙ basechange2⁻ (F (lUnit (g base) (~ j)))
--                         (λ i → F (lUnit (g (loop i)) (~ j)))))


-- basechange-lemma2 : (f g : S¹ → hLevelTrunc 3 (S₊ 1)) (F : hLevelTrunc 3 (S₊ 1) → S¹)
--                  → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
--                   ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
--                   ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
-- basechange-lemma2 f g F = coInd (f base) (g base) refl refl
--   where
--   coInd : (x y : hLevelTrunc 3 (S₊ 1))
--                    → f base ≡ x
--                    → g base ≡ y
--                    → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
--                     ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
--                     ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
--   coInd =
--     elim2 (λ _ _ → isGroupoidΠ2 λ _ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isGroupoidS¹ base base)) _ _ )
--           (toPropElim2 (λ _ _ → isPropΠ2 λ _ _ → isGroupoidS¹ _ _ _ _)
--              λ fb gb → basechange-lemma base base (F ∘ ΩKn+1→Kn 1) (Kn→ΩKn+1 1 ∘ f) (Kn→ΩKn+1 1 ∘ g)
--                                           (cong (Kn→ΩKn+1 1) fb ∙ Kn→ΩKn+10ₖ 1)
--                                           (cong (Kn→ΩKn+1 1) gb ∙ Kn→ΩKn+10ₖ 1)
--                        ∙ cong₂ (_∙_) (λ j i → basechange2⁻ (F (Iso.leftInv (Iso-Kn-ΩKn+1 1) (f base) j))
--                                                             (cong (λ x → F (Iso.leftInv (Iso-Kn-ΩKn+1 1) (f x) j)) loop) i)
--                                      λ j i → basechange2⁻ (F (Iso.leftInv (Iso-Kn-ΩKn+1 1) (g base) j))
--                                                               (cong (λ x → F (Iso.leftInv (Iso-Kn-ΩKn+1 1) (g x) j)) loop) i)

-- S1→K2≡K2×K1 : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
-- S1→K2≡K2×K1 = S1→K2≡K2×K1' unlock
