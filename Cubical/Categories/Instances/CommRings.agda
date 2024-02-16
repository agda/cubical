{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.CommRings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FiberedProduct
open import Cubical.Algebra.CommRing.Instances.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Limits

open import Cubical.HITs.PropositionalTruncation

open Category hiding (_∘_)
open isUnivalent
open isIso
open Functor
open CommRingStr
open RingHoms
open IsRingHom

private
  variable
    ℓ ℓ' ℓ'' : Level

CommRingsCategory : Category (ℓ-suc ℓ) ℓ
ob CommRingsCategory                     = CommRing _
Hom[_,_] CommRingsCategory               = CommRingHom
id CommRingsCategory {R}                 = idCommRingHom R
_⋆_ CommRingsCategory {R} {S} {T}        = compCommRingHom R S T
⋆IdL CommRingsCategory {R} {S}           = compIdCommRingHom {R = R} {S}
⋆IdR CommRingsCategory {R} {S}           = idCompCommRingHom {R = R} {S}
⋆Assoc CommRingsCategory {R} {S} {T} {U} = compAssocCommRingHom {R = R} {S} {T} {U}
isSetHom CommRingsCategory               = isSetRingHom _ _

ForgetfulCommRing→Set : Functor CommRingsCategory (SET ℓ)
F-ob ForgetfulCommRing→Set R    = R .fst , CommRingStr.is-set (snd R)
F-hom ForgetfulCommRing→Set f x = f .fst x
F-id ForgetfulCommRing→Set      = funExt (λ _ → refl)
F-seq ForgetfulCommRing→Set f g = funExt (λ _ → refl)

open Iso

CommRingIsoIsoCatIso : {R S : CommRing ℓ} → Iso (CommRingIso R S) (CatIso CommRingsCategory R S)
(fun CommRingIsoIsoCatIso e) .fst = (e .fst .fun) , (e .snd)
(fun (CommRingIsoIsoCatIso {R = R} {S}) e) .snd .inv =
    e .fst .inv
  , makeIsRingHom (sym (cong (e .fst .inv) (pres1 (e .snd))) ∙ e .fst .leftInv _)
                  (λ x y → let rem = e .fst .rightInv _
                                  ∙∙ (λ i → S .snd ._+_ (e .fst .rightInv x (~ i)) (e .fst .rightInv y (~ i)))
                                  ∙∙ sym (pres+ (e .snd) _ _)
                            in injCommRingIso {R = R} {S} e _ _ rem)
                  (λ x y → let rem = e .fst .rightInv _
                                  ∙∙ (λ i → S .snd ._·_ (e .fst .rightInv x (~ i)) (e .fst .rightInv y (~ i)))
                                  ∙∙ sym (pres· (e .snd) _ _)
                           in injCommRingIso {R = R} {S} e _ _ rem)
(fun CommRingIsoIsoCatIso e) .snd .sec = RingHom≡ (funExt (e .fst .rightInv))
(fun CommRingIsoIsoCatIso e) .snd .ret = RingHom≡ (funExt (e .fst .leftInv))
fun (fst (inv CommRingIsoIsoCatIso e)) = e .fst .fst
inv (fst (inv CommRingIsoIsoCatIso e)) = e .snd .inv .fst
rightInv (fst (inv CommRingIsoIsoCatIso e)) x i = fst (e .snd .sec i) x
leftInv  (fst (inv CommRingIsoIsoCatIso e)) x i = fst (e .snd .ret i) x
snd (inv CommRingIsoIsoCatIso e) = e .fst .snd
rightInv CommRingIsoIsoCatIso x = CatIso≡ _ _ (RingHom≡ refl)
leftInv (CommRingIsoIsoCatIso {R = R} {S}) x =
  Σ≡Prop (λ x → isPropIsRingHom (CommRingStr→RingStr (R .snd))
                                (x .fun)
                                (CommRingStr→RingStr (S .snd)))
         (Iso≡Set (is-set (snd R)) (is-set (snd S)) _ _ (λ _ → refl) (λ _ → refl))

isUnivalentCommRingsCategory : ∀ {ℓ} → isUnivalent {ℓ = ℓ-suc ℓ} CommRingsCategory
univ isUnivalentCommRingsCategory R S = subst isEquiv (funExt rem) (≡≃CatIso .snd)
  where
  CommRingEquivIso≡ : Iso (CommRingEquiv R S) (R ≡ S)
  CommRingEquivIso≡ = equivToIso (CommRingPath R S)

  ≡≃CatIso : (R ≡ S) ≃ (CatIso CommRingsCategory R S)
  ≡≃CatIso = isoToEquiv (compIso (invIso CommRingEquivIso≡)
                                 (compIso (CommRingEquivIsoCommRingIso R S) CommRingIsoIsoCatIso))

  rem : ∀ p → ≡≃CatIso .fst p ≡ pathToIso p
  rem p = CatIso≡ _ _
    (RingHom≡ (funExt λ x → cong (transport (cong fst p)) (sym (transportRefl x))))

module _ {ℓ : Level} where
  TerminalCommRing : Terminal CommRingsCategory
  fst TerminalCommRing = UnitCommRing {ℓ = ℓ}
  fst (fst (snd TerminalCommRing y)) _ = tt*
  snd (fst (snd TerminalCommRing y)) = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)
  snd (snd TerminalCommRing y) f = RingHom≡ (funExt (λ _ → refl))


open Pullback

{-
   A x_C B -----> A
      |           |
      |           | α
      |           |
      V           V
      B --------> C
            β
-}
PullbackCommRingsCategory : Pullbacks {ℓ-suc ℓ} CommRingsCategory
pbOb (PullbackCommRingsCategory (cospan A C B α β))             = fiberedProduct A B C α β
pbPr₁ (PullbackCommRingsCategory (cospan A C B α β))            = fiberedProductPr₁ A B C α β
pbPr₂ (PullbackCommRingsCategory (cospan A C B α β))            = fiberedProductPr₂ A B C α β
pbCommutes (PullbackCommRingsCategory (cospan A C B α β))       = fiberedProductPr₁₂Commutes A B C α β
univProp (PullbackCommRingsCategory (cospan A C B α β)) {d = D} = fiberedProductUnivProp A B C α β D


-- General limits
module _ {ℓJ ℓJ' : Level} where

  open LimCone
  open Cone

  LimitsCommRingsCategory : Limits {ℓJ} {ℓJ'} (CommRingsCategory {ℓ = ℓ-max ℓJ ℓJ'})
  fst (lim (LimitsCommRingsCategory J D)) =
    lim {J = J} (completeSET J (funcComp ForgetfulCommRing→Set D)) .fst
  0r (snd (lim (LimitsCommRingsCategory J D))) =
    cone (λ v _ → 0r (snd (F-ob D v)))
         (λ e → funExt (λ _ → F-hom D e .snd .pres0))
  1r (snd (lim (LimitsCommRingsCategory J D))) =
    cone (λ v _ → 1r (snd (F-ob D v)))
         (λ e → funExt (λ _ → F-hom D e .snd .pres1))
  _+_ (snd (lim (LimitsCommRingsCategory J D))) x y =
    cone (λ v _ → _+_ (snd (F-ob D v)) _ _)
         ( λ e → funExt (λ _ → F-hom D e .snd .pres+ _ _
         ∙ λ i → _+_ (snd (F-ob D _)) (coneOutCommutes x e i tt*) (coneOutCommutes y e i tt*)))
  _·_ (snd (lim (LimitsCommRingsCategory J D))) x y =
    cone (λ v _ → _·_ (snd (F-ob D v)) _ _)
         ( λ e → funExt (λ _ → F-hom D e .snd .pres· _ _
         ∙ λ i → _·_ (snd (F-ob D _)) (coneOutCommutes x e i tt*) (coneOutCommutes y e i tt*)))
  (- snd (lim (LimitsCommRingsCategory J D))) x =
    cone (λ v _ → -_ (snd (F-ob D v)) _)
         ( λ e → funExt (λ z → F-hom D e .snd .pres- _
         ∙ λ i → -_ (snd (F-ob D _)) (coneOutCommutes x e i tt*)))
  isCommRing (snd (lim (LimitsCommRingsCategory J D))) =
    makeIsCommRing
      (isSetCone (funcComp ForgetfulCommRing→Set D) (Unit* , _))
      (λ _ _ _ → cone≡ (λ v → funExt (λ _ → snd (F-ob D v) .+Assoc _ _ _)))
      (λ _ → cone≡ (λ v → funExt (λ _ → +IdR (snd (F-ob D v)) _)))
      (λ _ → cone≡ (λ v → funExt (λ _ → +InvR (snd (F-ob D v)) _)))
      (λ _ _ → cone≡ (λ v → funExt (λ _ → snd (F-ob D v) .+Comm _ _)))
      (λ _ _ _ → cone≡ (λ v → funExt (λ _ → snd (F-ob D v) .·Assoc _ _ _)))
      (λ _ → cone≡ (λ v → funExt (λ _ → ·IdR (snd (F-ob D v)) _)))
      (λ _ _ _ → cone≡ (λ v → funExt (λ _ → ·DistR+ (snd (F-ob D v)) _ _ _)))
      (λ _ _ → cone≡ (λ v → funExt (λ _ → snd (F-ob D v) .·Comm _ _)))
  fst (coneOut (limCone (LimitsCommRingsCategory J D)) v) =
    coneOut (limCone (completeSET J (funcComp ForgetfulCommRing→Set D))) v
  pres0 (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = refl
  pres1 (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = refl
  pres+ (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = λ _ _ → refl
  pres· (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = λ _ _ → refl
  pres- (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = λ _ → refl
  coneOutCommutes (limCone (LimitsCommRingsCategory J D)) e =
    RingHom≡ (coneOutCommutes (limCone (completeSET J (funcComp ForgetfulCommRing→Set D))) e)
  univProp (LimitsCommRingsCategory J D) c cc =
    uniqueExists
      ( (λ x → limArrow (completeSET J (funcComp ForgetfulCommRing→Set D))
                        (fst c , snd c .is-set)
                        (cone (λ v _ → coneOut cc v .fst x)
                              (λ e → funExt (λ _ → funExt⁻ (cong fst (coneOutCommutes cc e)) x))) x)
      , makeIsRingHom
          (cone≡ (λ v → funExt (λ _ → coneOut cc v .snd .pres1)))
          (λ x y → cone≡ (λ v → funExt (λ _ → coneOut cc v .snd .pres+ _ _)))
          (λ x y → cone≡ (λ v → funExt (λ _ → coneOut cc v .snd .pres· _ _))))
      (λ _ → RingHom≡ refl)
      (isPropIsConeMor cc (limCone (LimitsCommRingsCategory J D)))
      (λ a' x → Σ≡Prop (λ _ → isPropIsRingHom _ _ _)
                       (funExt (λ y → cone≡ λ v → funExt (λ _ → sym (funExt⁻ (cong fst (x v)) y)))))
