{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.CommRings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FiberedProduct
open import Cubical.Algebra.CommRing.Instances.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Limits

open Category hiding (_∘_)
open CommRingHoms
open isUnivalent

private
  variable
    ℓ ℓ' : Level

CommRingsCategory : Category (ℓ-suc ℓ) ℓ
ob CommRingsCategory                     = CommRing _
Hom[_,_] CommRingsCategory               = CommRingHom
id CommRingsCategory {R}                 = idCommRingHom R
_⋆_ CommRingsCategory {R} {S} {T}        = compCommRingHom R S T
⋆IdL CommRingsCategory {R} {S}           = compIdCommRingHom {R = R} {S}
⋆IdR CommRingsCategory {R} {S}           = idCompCommRingHom {R = R} {S}
⋆Assoc CommRingsCategory {R} {S} {T} {U} = compAssocCommRingHom {R = R} {S} {T} {U}
isSetHom CommRingsCategory               = isSetRingHom _ _

open CatIso

CatIso≡ : {ℓ ℓ' : Level} {C : Category ℓ ℓ'} {x y : C .ob} (f g : CatIso C x y) → f .mor ≡ g .mor → f .inv ≡ g .inv → f ≡ g
mor (CatIso≡ f g p q i) = p i
inv (CatIso≡ f g p q i) = q i
sec (CatIso≡ {C = C} f g p q i) j =
  isSet→isSet' (isSetHom C) (λ i → seq' C (q i) (p i)) (λ _ → C .id) (sec f) (sec g) j i
ret (CatIso≡ {C = C} f g p q i) j =
  isSet→isSet' (isSetHom C) (λ i → seq' C (p i) (q i)) (λ _ → C .id) (ret f) (ret g) j i

isUnivalentCommRingsCategory : ∀ {ℓ} → isUnivalent {ℓ = ℓ-suc ℓ} CommRingsCategory
univ isUnivalentCommRingsCategory R S = subst isEquiv (funExt blop) (boo .snd)
  where
  foo : Iso (CommRingEquiv R S) (R ≡ S)
  foo = equivToIso (CommRingPath R S)

  open Iso
  open CatIso

  injCommRingIso : (f : CommRingIso R S) → (x y : R .fst) → f .fst .fun x ≡ f .fst .fun y → x ≡ y
  injCommRingIso f x y h = sym (f .fst .leftInv x) ∙∙ cong (f .fst .inv) h ∙∙ f .fst .leftInv y

  bar : Iso (CommRingIso R S) (CatIso CommRingsCategory R S)
  mor (fun bar e) = (e .fst .fun) , (e .snd)
  inv (fun bar e) = e .fst .inv , makeIsRingHom (sym (cong (e .fst .inv) (IsRingHom.pres1 (e .snd))) ∙ e .fst .leftInv _)
                                                (λ x y → injCommRingIso e _ _ (e .fst .rightInv _ ∙ (λ i → S .snd .CommRingStr._+_ (e .fst .rightInv x (~ i)) (e .fst .rightInv y (~ i))) ∙ sym (IsRingHom.pres+ (e .snd) _ _)))
                                                (λ x y → injCommRingIso e _ _ (e .fst .rightInv _ ∙ (λ i → S .snd .CommRingStr._·_ (e .fst .rightInv x (~ i)) (e .fst .rightInv y (~ i))) ∙ sym (IsRingHom.pres· (e .snd) _ _)))
  sec (fun bar e) = RingHom≡ (funExt (e .fst .rightInv))
  ret (fun bar e) = RingHom≡ (funExt (e .fst .leftInv))
  fun (fst (inv bar e)) = e .mor .fst
  inv (fst (inv bar e)) = e .inv .fst
  rightInv (fst (inv bar e)) x i = fst (e .sec i) x
  leftInv (fst (inv bar e)) x i = fst (e .ret i) x
  snd (inv bar e) = e .mor .snd
  rightInv bar x = CatIso≡ _ _ (RingHom≡ refl) (RingHom≡ refl)
  leftInv bar x = Σ≡Prop (λ x → isPropIsRingHom (CommRingStr→RingStr (R .snd)) (x .fun) (CommRingStr→RingStr (S .snd)))
                         (Iso≡Set (CommRingStr.is-set (snd R)) (CommRingStr.is-set (snd S)) _ _ (λ _ → refl) (λ _ → refl))

  boo : (R ≡ S) ≃ (CatIso CommRingsCategory R S)
  boo = isoToEquiv (compIso (invIso foo) (compIso (CommRingEquivIsoCommRingIso R S) bar))

  blop : ∀ p → boo .fst p ≡ pathToIso p
  blop p = CatIso≡ (boo .fst p) (pathToIso p) (RingHom≡ (funExt (λ x → cong (transport (λ i → fst (p i))) (sym (transportRefl x))))) (RingHom≡ (funExt (λ x → sym (transportRefl _))))

TerminalCommRing : Terminal {ℓ-suc ℓ-zero} CommRingsCategory
fst TerminalCommRing                 = UnitCommRing
fst (fst (snd TerminalCommRing y)) _ = tt
snd (fst (snd TerminalCommRing y))   = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)
snd (snd TerminalCommRing y) f       = RingHom≡ (funExt (λ _ → refl))


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

open LimCone
open Cone
open Functor

forgetfulFunctor : Functor CommRingsCategory (SET ℓ)
F-ob forgetfulFunctor R = R .fst , CommRingStr.is-set (snd R)
F-hom forgetfulFunctor f x = f .fst x
F-id forgetfulFunctor = funExt (λ _ → refl)
F-seq forgetfulFunctor f g = funExt (λ _ → refl)

open RingHoms

-- LimitsCommRingsCategory : Limits CommRingsCategory
-- fst (lim (LimitsCommRingsCategory J D)) = lim (completeSET J (funcComp forgetfulFunctor D)) .fst
-- snd (lim (LimitsCommRingsCategory J D)) = {!!}
-- fst (coneOut (limCone (LimitsCommRingsCategory J D)) v) = coneOut (limCone (completeSET J (funcComp forgetfulFunctor D))) v
-- snd (coneOut (limCone (LimitsCommRingsCategory J D)) v) = {!!}
-- coneOutCommutes (limCone (LimitsCommRingsCategory J D)) e = RingHom≡ (coneOutCommutes (limCone (completeSET J (funcComp forgetfulFunctor D))) e)
-- univProp (LimitsCommRingsCategory J D) = {!!}
