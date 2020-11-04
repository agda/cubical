{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.dirrAdd.Groups.Prelims where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.dirrAdd.Properties
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec)
open import Cubical.HITs.SetTruncation renaming (elim to sElim ; map to sMap ; rec to sRec ; elim2 to sElim2)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint


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

S¹→S¹≡S¹×Int : Iso (S¹ → hLevelTrunc 3 S¹) (S¹ × Int)
Iso.fun S¹→S¹≡S¹×Int f = S¹map (f base)
                 , winding (basechange2⁻ (S¹map (f base)) λ i → S¹map (f (loop i)))
Iso.inv S¹→S¹≡S¹×Int (s , int) base = ∣ s ∣
Iso.inv S¹→S¹≡S¹×Int (s , int) (loop i) = ∣ basechange2 s (intLoop int) i ∣
Iso.rightInv S¹→S¹≡S¹×Int (s , int) = ΣPathP (refl , ((λ i → winding (basechange2-retr s (λ i → intLoop int i) i))
                                                      ∙ windingIntLoop int))
Iso.leftInv S¹→S¹≡S¹×Int f = funExt λ { base → S¹map-id (f base)
                                      ; (loop i) j → helper j i}
  where
  helper : PathP (λ i → S¹map-id (f base) i ≡ S¹map-id (f base) i)
                  (λ i → ∣ basechange2 (S¹map (f base))
                             (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁)))))) i ∣)
                  (cong f loop)
  helper i j =
    hcomp (λ k → λ { (i = i0) → cong ∣_∣ (basechange2 (S¹map (f base))
                                           (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁))))))) j
                    ; (i = i1) → S¹map-id (f (loop j)) k
                    ; (j = i0) → S¹map-id (f base) (i ∧ k)
                    ; (j = i1) → S¹map-id (f base) (i ∧ k)})
          (helper2 i j)
    where
    helper2 : Path (Path (hLevelTrunc 3 _) _ _)
                   (cong ∣_∣ (basechange2 (S¹map (f base))
                                         (intLoop
                                           (winding
                                             (basechange2⁻ (S¹map (f base))
                                                           (λ i₁ → S¹map (f (loop i₁))))))))
                   λ i → ∣ S¹map (f (loop i)) ∣
    helper2 i j =
         ∣ ((cong (basechange2 (S¹map (f base)))
                   (decodeEncode base (basechange2⁻ (S¹map (f base))
                                                    (λ i₁ → S¹map (f (loop i₁)))))
            ∙ basechange2-sect (S¹map (f base))
                               (λ i → S¹map (f (loop i)))) i) j ∣



ΩK₁Iso : (x : coHomK 1) → (x ≡ x) ≃ Int
ΩK₁Iso = trElim (λ _ → isOfHLevel≃ 3 (isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ _ _ → isOfHLevelPath 2 isSetInt _ _)
                λ a → isoToEquiv (help a)
  where
  help : (a : S¹) → Iso (∣ a ∣ ≡ ∣ a ∣) Int
  help a = congIso (truncIdempotentIso 3 isGroupoidS¹)
         ⋄ Iso-basedΩS¹-Int a

private
  helpIso : Iso (Σ-syntax (∥ S¹ ∥ 3) (λ x → x ≡ x)) ((∥ S¹ ∥ 3) × Int)
  Iso.fun helpIso (x , p) = x , fst (ΩK₁Iso x) p 
  Iso.inv helpIso (x , p) = x , invEq (ΩK₁Iso x) p
  Iso.rightInv helpIso (x , p) = ΣPathP (refl , (retEq (ΩK₁Iso x) p))
  Iso.leftInv helpIso (x , p) = ΣPathP (refl , (secEq (ΩK₁Iso x) p))

ΩK₁Iso-hom : (x : coHomK 1) (p q : x ≡ x) → fst (ΩK₁Iso x) (p ∙ q) ≡ (fst (ΩK₁Iso x) p +ℤ fst (ΩK₁Iso x) q)
ΩK₁Iso-hom =
  trElim (λ _ → isGroupoidΠ2 λ _ _ → isOfHLevelPlus {n = 1} 2 (isSetInt _ _)) (toPropElim (λ _ → isPropΠ2 λ _ _ → isSetInt _ _) help)
  where
  help : (p q : ∣ base ∣ ≡ ∣ base ∣) →
      fst (ΩK₁Iso ∣ base ∣) (p ∙ q) ≡
      (fst (ΩK₁Iso ∣ base ∣) p +ℤ fst (ΩK₁Iso ∣ base ∣) q)
  help p q =
    let
    congLem : cong (Iso.fun (truncIdempotentIso 3 isGroupoidS¹)) (p ∙ q)
            ≡ cong (Iso.fun (truncIdempotentIso 3 isGroupoidS¹)) p ∙ cong (Iso.fun (truncIdempotentIso 3 isGroupoidS¹)) q
    congLem = congFunct (Iso.fun (truncIdempotentIso 3 isGroupoidS¹)) p q
    p' = cong (Iso.fun (truncIdempotentIso 3 isGroupoidS¹)) p
    q' = cong (Iso.fun (truncIdempotentIso 3 isGroupoidS¹)) q
    in cong (Iso.fun (Iso-basedΩS¹-Int base)) congLem
     ∙ winding-hom p' q'

S1→K₁≡S1×Int : Iso ((S₊ 1) → coHomK 1) (coHomK 1 × Int)
S1→K₁≡S1×Int = IsoFunSpaceS¹ ⋄ helpIso

open import Cubical.Algebra.Group
H¹S¹→Int : GroupHom (coHomGr 1 (S₊ 1)) intGroup
GroupHom.fun H¹S¹→Int = sRec isSetInt (snd ∘ (Iso.fun S1→K₁≡S1×Int))
GroupHom.isHom H¹S¹→Int =
  coHomPointedElim2 _ base (λ _ _ → isSetInt _ _)
    λ f g fId gId → (λ i → fst (ΩK₁Iso (f base +ₖ g base)) (cong₂Funct (λ x y → f x +ₖ g y) loop loop i))
                   ∙ (ΩK₁Iso-hom (f base +ₖ g base) _ _
                  ∙∙ (λ i → fst (ΩK₁Iso (f base +ₖ gId i)) (cong (λ x → f x +ₖ gId i) loop)
                         +ℤ fst (ΩK₁Iso (fId i +ₖ g base)) (cong (λ x → fId i +ₖ g x) loop))
                  ∙∙ (λ i → fst (ΩK₁Iso (rUnitₖ 1 (f base) i)) (cong (λ x → rUnitₖ 1 (f x) i) loop)
                          +ℤ fst (ΩK₁Iso (lUnitₖ 1 (g base) i)) (cong (λ x → lUnitₖ 1 (g x) i) loop)))
{-
S1→K2≡K2×K1' : GroupIso (coHomGr 2 S¹)
                         (auxGr (coHomK-ptd 2))
S1→K2≡K2×K1' = Iso+Hom→GrIso
  help
  (coHomPointedElim2 1 base (λ _ _ → setTruncIsSet _ _)
    λ f g fId gId
     → cong ∣_∣₂ ((λ i → sym (rCancelₖ 2 (f base +ₖ g base)) ∙∙ cong (λ x → x -[ 2 ]ₖ (f base +ₖ g base)) (cong (λ x → f x +ₖ g x) loop) ∙∙ rCancelₖ 2 (f base +ₖ g base))
              ∙∙ (λ i → doubleCompPath-elim' (sym (rCancelₖ 2 (f base +ₖ g base)))
                                       (cong₂Funct (λ x y → (f x +ₖ g y) -[ 2 ]ₖ (f base +ₖ g base)) loop loop i)
                                       (rCancelₖ 2 (f base +ₖ g base)) i)
              ∙∙ ((λ j → sym (rCancelₖ 2 (f base +ₖ g base)) ∙ ((rUnit (λ i → (f (loop i) +ₖ g base) -ₖ (f base +ₖ g base)) j) ∙ (lUnit (λ i → (f base +ₖ g (loop i)) -ₖ (f base +ₖ g base))) j) ∙ rCancelₖ 2 (f base +ₖ g base))
              ∙∙ (λ j → sym (rCancelₖ 2 (f base +ₖ gId j)) ∙ (((λ i → (f (loop i) +ₖ gId j) -ₖ (f base +ₖ gId j)) ∙ lUnit (λ i → (f base +ₖ gId (j ∧ ~ i)) -ₖ (f base +ₖ gId (j ∧ ~ i))) j) ∙ rUnit (λ i → (fId (j ∧ i) +ₖ g base) -ₖ (fId (j ∧ i) +ₖ g base)) j ∙ λ i → (fId j +ₖ g (loop i)) -ₖ (fId j +ₖ g base)) ∙ rCancelₖ 2 (fId j +ₖ g base))
              ∙∙ ((λ j → sym (rCancelₖ 2 (rUnitₖ 2 (f base) j))
                    ∙ (((λ i → rUnitₖ 2 (f (loop i)) j -ₖ rUnitₖ 2 (f base) j)
                    ∙ (λ i → rUnitₖ 2 (f base) (~ i ∧ j) -ₖ rUnitₖ 2 (f base) (~ i ∧ j))
                    ∙ λ i → (f base +ₖ gId (~ i)) -ₖ (f base +ₖ gId (~ i)))
                ∙ ((λ i → (fId i +ₖ g base) -ₖ (fId i +ₖ g base))
                    ∙ λ i → lUnitₖ 2 (g base) (i ∧ j) -ₖ lUnitₖ 2 (g base) (i ∧ j))
                    ∙ λ i → (lUnitₖ 2 (g (loop i)) j) -ₖ (lUnitₖ 2 (g base) j))
                    ∙ rCancelₖ 2 (lUnitₖ 2 (g base) j))
              ∙∙ (λ j → sym (rCancelₖ 2 (f base))
                    ∙ (((λ i → (f (loop i)) -ₖ (f base))
                    ∙ pathCanc (g base) (f base) (sym gId) (sym fId) .snd j)
                ∙ pathCanc (g base) (f base) (sym gId) (sym fId) .fst j
                    ∙ λ i → (g (loop i)) -ₖ (g base))
                    ∙ rCancelₖ 2 (g base))
              ∙∙ ({!!}
              ∙∙ {!!}
              ∙∙ {!!})))))
  where

  path× : (g-b f-b : ∥ Susp S¹ ∥ 4) (gId : ∣ north ∣ ≡ g-b) (fId : ∣ north ∣ ≡ f-b) → Type₀
  path× g-b f-b gId fId =
      ((λ i → (fId (~ i) +ₖ g-b) -ₖ (fId (~ i) +ₖ g-b)) ∙ (λ i → (lUnitₖ 2 (g-b) i) -ₖ (lUnitₖ 2 (g-b) i))
            ≡ rCancelₖ 2 (f-b +ₖ g-b) ∙ sym (rCancelₖ 2 g-b))
        ×
      ((λ i → rUnitₖ 2 f-b (~ i) -ₖ rUnitₖ 2 f-b (~ i)) ∙ (λ i → (f-b +ₖ gId i) -ₖ (f-b +ₖ gId i))
            ≡ rCancelₖ 2 (f-b) ∙ sym (rCancelₖ 2 (f-b +ₖ g-b)))

  pathCanc : (g-b f-b : ∥ Susp S¹ ∥ 4) (gId : ∣ north ∣ ≡ g-b) (fId : ∣ north ∣ ≡ f-b)
           → path× g-b f-b gId fId
  pathCanc g-b f-b = J (λ g-b gId → (fId : ∣ north ∣ ≡ f-b) → path× g-b f-b gId fId)
                       (J (λ f-b fId → path× ∣ north ∣ f-b refl fId)
                          (sym (rUnit _) ∙ sym (rCancel (rCancelₖ 2 ∣ north ∣))
                         , sym (rUnit _) ∙ sym (rCancel (rCancelₖ 2 ∣ north ∣))))
-}
{-
  pathCanc : (g-b f-b : ∥ Susp S¹ ∥ 4) (gId : ∣ north ∣ ≡ g-b) (fId : ∣ north ∣ ≡ f-b)
           → ? ×
            ((λ i → rUnitₖ 2 f-b (~ i) -ₖ rUnitₖ 2 f-b (~ i)) ∙ (λ i → (f-b +ₖ gId i) -ₖ (f-b +ₖ gId i))
            ≡ rCancelₖ 2 (f-b) ∙ sym (rCancelₖ 2 (f-b +ₖ g-b)))
  pathCanc g-b f-b =  J (λ g-b gId → (fId : ∣ north ∣ ≡ f-b)
                                     → ? × ((λ i → rUnitₖ 2 f-b (~ i) -ₖ rUnitₖ 2 f-b (~ i)) ∙ (λ i → (f-b +ₖ gId i) -ₖ (f-b +ₖ gId i))
                                      ≡ rCancelₖ 2 (f-b) ∙ sym (rCancelₖ 2 (f-b +ₖ g-b))))
                         (J (λ f-b fId → ? × ((λ i → rUnitₖ 2 f-b (~ i) -ₖ rUnitₖ 2 f-b (~ i)) ∙ (λ i → (f-b +ₖ ∣ north ∣) -ₖ (f-b +ₖ ∣ north ∣))
                                      ≡ rCancelₖ 2 (f-b) ∙ sym (rCancelₖ 2 (f-b +ₖ ∣ north ∣))))
                            (? , sym (rUnit _) ∙ sym (rCancel (rCancelₖ 2 ∣ north ∣))))
-}
{-
  help : Iso ∥ (S¹ → coHomK 2) ∥₂ ∥ 0ₖ 2 ≡ 0ₖ 2 ∥₂
  Iso.fun help = sMap λ f → sym (rCancelₖ 2 (f base)) ∙∙ cong (λ x → x -[ 2 ]ₖ f base) (cong f loop) ∙∙ rCancelₖ 2 (f base)
  Iso.inv help = sMap λ p → λ {base → 0ₖ 2 ; (loop i) → p i}
  Iso.rightInv help = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                            λ p → cong ∣_∣₂ ((λ i → transportRefl refl i ∙∙ cong (λ x → x -[ 2 ]ₖ ∣ north ∣) p ∙∙ transportRefl refl i)
                                            ∙∙ sym (rUnit (cong (λ x → x -[ 2 ]ₖ ∣ north ∣) p))
                                            ∙∙ λ j i → rUnitₖ 2 (p i) j)
  Iso.leftInv help =
    coHomPointedElim 1 base (λ _ → setTruncIsSet _ _)
                     λ f fId → cong ∣_∣₂ (funExt λ {base → sym fId
                                                 ; (loop i) j → helper f fId j i})
      where
      helper : (f : _) (fId : _) → PathP (λ j → fId (~ j) ≡ fId (~ j))
                                          (sym (rCancelₖ 2 (f base))
                                            ∙∙ cong (λ x → x -[ 2 ]ₖ f base) (cong f loop)
                                            ∙∙ rCancelₖ 2 (f base))
                                          (cong f loop)
      helper f fId = compPathR→PathP ((λ i → sym (rCancelₖ 2 (f base))
                                            ∙∙ rUnit (cong (λ x → x -[ 2 ]ₖ f base) (cong f loop)) i
                                            ∙∙ rCancelₖ 2 (f base))
                                    ∙∙ (λ i → sym (rCancelₖ 2 (fId i))
                                            ∙∙ (λ j → fId (i ∧ ~ j) -[ 2 ]ₖ (fId i)) ∙∙ cong (λ x → x -[ 2 ]ₖ fId i) (cong f loop) ∙∙ (λ j → fId (i ∧ j) -[ 2 ]ₖ (fId i))
                                            ∙∙ rCancelₖ 2 (fId i))
                                    ∙∙ ((λ i → transportRefl refl i
                                             ∙∙ (λ j → fId (~ j) -[ 2 ]ₖ ∣ north ∣) ∙∙ cong (λ x → x -[ 2 ]ₖ ∣ north ∣) (cong f loop) ∙∙ (λ j → fId j -[ 2 ]ₖ ∣ north ∣)
                                             ∙∙ transportRefl refl i)
                                    ∙∙ sym (rUnit ((λ j → fId (~ j) -[ 2 ]ₖ ∣ north ∣) ∙∙ cong (λ x → x -[ 2 ]ₖ ∣ north ∣) (cong f loop) ∙∙ (λ j → fId j -[ 2 ]ₖ ∣ north ∣)))
                                    ∙∙ ((λ i → (λ j → fId (~ j) +[ 2 ]ₖ -0ₖ i) ∙∙ cong (λ x → x +[ 2 ]ₖ -0ₖ i) (cong f loop) ∙∙ λ j → fId j +[ 2 ]ₖ -0ₖ i)
                                    ∙∙ (λ i → (λ j → rUnitₖ 2 (fId (~ j)) i) ∙∙ cong (λ x → rUnitₖ 2 x i) (cong f loop) ∙∙ λ j → rUnitₖ 2 (fId j) i)
                                    ∙∙ doubleCompPath-elim' _ _ _)))
-}
{-
S1→K2≡K2×K1 : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
Iso.fun S1→K2≡K2×K1 f = (f base) , ΩKn+1→Kn 1 (sym (rCancelₖ 2 (f base)) ∙∙ cong (λ x → (f x) -ₖ f base) loop ∙∙ rCancelₖ 2 (f base))
Iso.inv S1→K2≡K2×K1 (x2 , x1) base = x2
Iso.inv S1→K2≡K2×K1 (x2 , x1) (loop i) = (sym (lUnitₖ 2 x2) ∙∙ cong (λ x → x +ₖ x2) (Kn→ΩKn+1 1 x1) ∙∙ lUnitₖ 2 x2) i
Iso.rightInv S1→K2≡K2×K1 =
  uncurry (trElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPath 4 (isOfHLevel× 4 (isOfHLevelTrunc 4) (isOfHLevelSuc 3 (isOfHLevelTrunc 3))) _ _)
          λ x2 → trElim (λ _ → isOfHLevel× 4 (isOfHLevelTrunc 4) (isOfHLevelSuc 3 (isOfHLevelTrunc 3)) _ _)
          λ x1 → ΣPathP (refl , helper x1 x2))
  where
  helper : (x1 : S¹) (x2 : S₊ 2) →
     ΩKn+1→Kn 1
      ((λ i → retEq (Kₙ≃Kₙ 1 ∣ x2 ∣) ∣ north ∣ (~ i)) ∙∙
       (λ i →
          ((λ i₁ → +ₖ-syntax 2 ∣ north ∣ ∣ x2 ∣) ∙∙
           (λ i₁ → preAdd 0 .fst (ϕ base x1 i₁) x2) ∙∙
           (λ _ → +ₖ-syntax 2 ∣ north ∣ ∣ x2 ∣))
          i
          -ₖ ∣ x2 ∣)
       ∙∙ retEq (Kₙ≃Kₙ 1 ∣ x2 ∣) ∣ north ∣)
      ≡ ∣ x1 ∣
  helper x1 =
    sphereElim _ (λ _ → isOfHLevelTrunc 3 _ _)
       (cong (ΩKn+1→Kn 1) ((λ i → transportRefl refl i ∙∙ ((λ j →
                           (rUnit (λ i₁ → preAdd 0 .fst (ϕ base x1 i₁) north) (~ i)) j -ₖ ∣ north ∣)) ∙∙ transportRefl refl i)
                        ∙∙ (sym (rUnit (cong (λ x → (preAdd 0 .fst x north) -ₖ ∣ north ∣) (ϕ base x1)))) 
                        ∙∙ (λ j i → rUnitₖ 2 (rUnitₖ 2 ∣ ϕ base x1 i ∣ j) j))
    ∙ Iso.leftInv (Iso-Kn-ΩKn+1 1) ∣ x1 ∣)
Iso.leftInv S1→K2≡K2×K1 f = funExt λ {base → refl
                                    ; (loop i) j → {!!}}
  where
  helper : cong (Iso.inv S1→K2≡K2×K1 (Iso.fun S1→K2≡K2×K1 f)) loop ≡ cong f loop
  helper = (λ i j → (sym (lUnitₖ 2 (f base))
                  ∙∙ cong (λ x → x +ₖ (f base)) (Iso.rightInv (Iso-Kn-ΩKn+1 1) ((sym (rCancelₖ 2 (f base))
                                                                               ∙∙ cong (λ x → (f x) -ₖ f base) loop
                                                                               ∙∙ rCancelₖ 2 (f base))) i)
                  ∙∙ lUnitₖ 2 (f base)) j)
        ∙∙ (λ i j → (sym (lUnitₖ 2 (f base))
                  ∙∙ cong-∙∙ (λ x → x +ₖ (f base)) (sym (rCancelₖ 2 (f base))) (cong (λ x → (f x) -ₖ f base) loop) (rCancelₖ 2 (f base)) i
                  ∙∙ lUnitₖ 2 (f base)) j)
        ∙∙ (λ i j → (sym (lUnitₖ 2 (f base))
                  ∙∙ (λ w → rCancelₖ 2 (f base) (~ w) +ₖ f base) ∙∙ rUnit (λ w → (f (loop w) -ₖ f base) +ₖ f base) i ∙∙ (λ w → rCancelₖ 2 (f base) w +ₖ f base)
                  ∙∙ lUnitₖ 2 (f base)) j)
        ∙∙ (λ i j → (sym (lUnitₖ 2 (f base))
                  ∙∙ (λ w → rCancelₖ 2 (f base) (~ w) +ₖ f base)
                  ∙∙ (λ w → assocₖ 2 (f base) (-ₖ f base) (f base) (~ i ∨ ~ w))
                  ∙∙ (rUnit (rUnit (λ w → assocₖ 2 (f (loop w)) (-ₖ f base) (f base) (~ i)) i) i)
                  ∙∙ (λ w → assocₖ 2 (f base) (-ₖ f base) (f base) (~ i ∨ w))
                  ∙∙ (λ w → rCancelₖ 2 (f base) w +ₖ f base)
                  ∙∙ lUnitₖ 2 (f base)) j)
        ∙∙ ((λ i j → (sym (lUnitₖ 2 (f base))
                  ∙∙ (λ w → rCancelₖ 2 (f base) (~ w) +ₖ f base)
                  ∙∙ (sym (assocₖ 2 (f base) (-ₖ f base) (f base)))
                  ∙∙ (λ w → f base +ₖ lCancelₖ 2 (f base) (i ∧ w))
                  ∙∙ refl
                  ∙∙ (λ w → (f (loop w)) +ₖ (lCancelₖ 2 (f base) i))
                  ∙∙ refl
                  ∙∙ (λ w → f base +ₖ lCancelₖ 2 (f base) (i ∧ ~ w))
                  ∙∙ (assocₖ 2 (f base) (-ₖ f base) (f base))
                  ∙∙ (λ w → rCancelₖ 2 (f base) w +ₖ f base)
                  ∙∙ lUnitₖ 2 (f base)) j)
        ∙∙ (λ i j → (sym (lUnitₖ 2 (f base))
                  ∙∙ (λ w → rCancelₖ 2 (f base) (~ w) +ₖ f base)
                  ∙∙ (sym (assocₖ 2 (f base) (-ₖ f base) (f base)))
                  ∙∙ (λ w → f base +ₖ lCancelₖ 2 (f base) w)
                  ∙∙ (λ w → rUnitₖ 2 (f base) (i ∧ w))
                  ∙∙ (λ w → (rUnitₖ 2 (f (loop w)) i))
                  ∙∙ (λ w → rUnitₖ 2 (f base) (i ∧ (~ w)))
                  ∙∙ (λ w → f base +ₖ lCancelₖ 2 (f base) (~ w))
                  ∙∙ (assocₖ 2 (f base) (-ₖ f base) (f base))
                  ∙∙ (λ w → rCancelₖ 2 (f base) w +ₖ f base)
                  ∙∙ lUnitₖ 2 (f base)) j)
        ∙∙ {!!})
-}

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
