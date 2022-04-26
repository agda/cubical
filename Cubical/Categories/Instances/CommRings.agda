{-# OPTIONS --safe #-}
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
open CatIso
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

forgetfulFunctor : Functor CommRingsCategory (SET ℓ)
F-ob forgetfulFunctor R    = R .fst , CommRingStr.is-set (snd R)
F-hom forgetfulFunctor f x = f .fst x
F-id forgetfulFunctor      = funExt (λ _ → refl)
F-seq forgetfulFunctor f g = funExt (λ _ → refl)

open Iso

CommRingIsoIsoCatIso : {R S : CommRing ℓ} → Iso (CommRingIso R S) (CatIso CommRingsCategory R S)
mor (fun CommRingIsoIsoCatIso e) = (e .fst .fun) , (e .snd)
inv (fun (CommRingIsoIsoCatIso {R = R} {S}) e) =
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
sec (fun CommRingIsoIsoCatIso e) = RingHom≡ (funExt (e .fst .rightInv))
ret (fun CommRingIsoIsoCatIso e) = RingHom≡ (funExt (e .fst .leftInv))
fun (fst (inv CommRingIsoIsoCatIso e)) = e .mor .fst
inv (fst (inv CommRingIsoIsoCatIso e)) = e .inv .fst
rightInv (fst (inv CommRingIsoIsoCatIso e)) x i = fst (e .sec i) x
leftInv (fst (inv CommRingIsoIsoCatIso e)) x i = fst (e .ret i) x
snd (inv CommRingIsoIsoCatIso e) = e .mor .snd
rightInv CommRingIsoIsoCatIso x = CatIso≡ _ _ (RingHom≡ refl) (RingHom≡ refl)
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
                 (RingHom≡ (funExt (λ x → cong (transport (λ i → fst (p i))) (sym (transportRefl x)))))
                 (RingHom≡ (funExt (λ x → sym (transportRefl _))))

TerminalCommRing : Terminal {ℓ-suc ℓ-zero} CommRingsCategory
fst TerminalCommRing = UnitCommRing
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

  LimitsCommRingsCategory : Limits {ℓJ} {ℓJ'} CommRingsCategory
  fst (lim (LimitsCommRingsCategory J D)) =
    lim {J = J} (completeSET J (funcComp forgetfulFunctor D)) .fst
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
      (isSetCone (funcComp forgetfulFunctor D) (Unit* , _))
      (λ _ _ _ → cone≡ (λ v → funExt (λ _ → snd (F-ob D v) .+Assoc _ _ _)))
      (λ _ → cone≡ (λ v → funExt (λ _ → +Rid (snd (F-ob D v)) _)))
      (λ _ → cone≡ (λ v → funExt (λ _ → +Rinv (snd (F-ob D v)) _)))
      (λ _ _ → cone≡ (λ v → funExt (λ _ → snd (F-ob D v) .+Comm _ _)))
      (λ _ _ _ → cone≡ (λ v → funExt (λ _ → snd (F-ob D v) .·Assoc _ _ _)))
      (λ _ → cone≡ (λ v → funExt (λ _ → ·Rid (snd (F-ob D v)) _)))
      (λ _ _ _ → cone≡ (λ v → funExt (λ _ → ·Rdist+ (snd (F-ob D v)) _ _ _)))
      (λ _ _ → cone≡ (λ v → funExt (λ _ → snd (F-ob D v) .·Comm _ _)))
  fst (coneOut (limCone (LimitsCommRingsCategory J D)) v) =
    coneOut (limCone (completeSET J (funcComp forgetfulFunctor D))) v
  pres0 (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = refl
  pres1 (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = refl
  pres+ (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = λ _ _ → refl
  pres· (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = λ _ _ → refl
  pres- (snd (coneOut (limCone (LimitsCommRingsCategory J D)) v)) = λ _ → refl
  coneOutCommutes (limCone (LimitsCommRingsCategory J D)) e =
    RingHom≡ (coneOutCommutes (limCone (completeSET J (funcComp forgetfulFunctor D))) e)
  univProp (LimitsCommRingsCategory J D) c cc =
    uniqueExists
      ( (λ x → limArrow (completeSET J (funcComp forgetfulFunctor D))
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
