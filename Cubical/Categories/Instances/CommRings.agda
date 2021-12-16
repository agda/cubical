{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.CommRings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Pullback

open Category hiding (_∘_)
open CommRingHoms

private
  variable
    ℓ : Level

CommRingsCategory : Category (ℓ-suc ℓ) ℓ
ob CommRingsCategory                     = CommRing _
Hom[_,_] CommRingsCategory               = CommRingHom
id CommRingsCategory {R}                 = idCommRingHom R
_⋆_ CommRingsCategory {R} {S} {T}        = compCommRingHom R S T
⋆IdL CommRingsCategory {R} {S}           = compIdCommRingHom {R = R} {S}
⋆IdR CommRingsCategory {R} {S}           = idCompCommRingHom {R = R} {S}
⋆Assoc CommRingsCategory {R} {S} {T} {U} = compAssocCommRingHom {R = R} {S} {T} {U}
isSetHom CommRingsCategory               = isSetRingHom _ _

TerminalCommRing : Terminal {ℓ-suc ℓ-zero} CommRingsCategory
fst TerminalCommRing = UnitCommRing
fst (fst (snd TerminalCommRing y)) _ = tt
snd (fst (snd TerminalCommRing y)) = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)
snd (snd TerminalCommRing y) f = RingHom≡ (funExt (λ _ → refl))


module FiberedProduct (A B C : CommRing ℓ) (α : CommRingHom A C) (β : CommRingHom B C) where

  private
    module A = CommRingStr (snd A)
    module B = CommRingStr (snd B)

  open CommRingStr
  open CommRingStr (snd A) renaming (0r to 0A ; 1r to 1A ; _+_ to _+A_ ; _·_ to _·A_ ; -_ to -A_)
  open CommRingStr (snd B) renaming (0r to 0B ; 1r to 1B ; _+_ to _+B_ ; _·_ to _·B_ ; -_ to -B_)
  open CommRingStr (snd C) renaming (0r to 0C ; 1r to 1C ; _+_ to _+C_ ; _·_ to _·C_ ; -_ to -C_)
  open IsRingHom (snd α) renaming (pres0 to pres0α ; pres1 to pres1α ; pres+ to pres+α ; pres· to pres·α ; pres- to pres-α)
  open IsRingHom (snd β) renaming (pres0 to pres0β ; pres1 to pres1β ; pres+ to pres+β ; pres· to pres·β ; pres- to pres-β)

  fbT : Type ℓ
  fbT = Σ[ ab ∈ fst A × fst B ] (fst α (fst ab) ≡ fst β (snd ab))

  fbT≡ : {x y : fbT} → fst (fst x) ≡ fst (fst y) → snd (fst x) ≡ snd (fst y) → x ≡ y
  fbT≡ h1 h2 = Σ≡Prop (λ _ → is-set (snd C) _ _) λ i → (h1 i) , (h2 i)

  0fbT : fbT
  0fbT = (0A , 0B) , pres0α ∙ sym pres0β

  1fbT : fbT
  1fbT = (1A , 1B) , pres1α ∙ sym pres1β

  _+fbT_ : fbT → fbT → fbT
  ((a1 , b1) , hab1) +fbT ((a2 , b2) , hab2) =
    (a1 +A a2 , b1 +B b2) , pres+α a1 a2 ∙∙ (λ i → hab1 i +C hab2 i) ∙∙ sym (pres+β b1 b2)

  _·fbT_ : fbT → fbT → fbT
  ((a1 , b1) , hab1) ·fbT ((a2 , b2) , hab2) =
    (a1 ·A a2 , b1 ·B b2) , pres·α a1 a2 ∙∙ (λ i → hab1 i ·C hab2 i) ∙∙ sym (pres·β b1 b2)

  -fbT_ : fbT → fbT
  -fbT ((a , b) , hab) = (-A a , -B b) , pres-α a ∙∙ cong -C_ hab ∙∙ sym (pres-β b)

  fiberedProduct : CommRing ℓ
  fst fiberedProduct = fbT
  0r (snd fiberedProduct) = 0fbT
  1r (snd fiberedProduct) = 1fbT
  _+_ (snd fiberedProduct) = _+fbT_
  _·_ (snd fiberedProduct) = _·fbT_
  -_ (snd fiberedProduct) = -fbT_
  isCommRing (snd fiberedProduct) =
    makeIsCommRing (isSetΣSndProp (isSet× (is-set (snd A)) (is-set (snd B))) λ x → is-set (snd C) _ _)
                   (λ _ _ _ → fbT≡ (A.+Assoc _ _ _) (B.+Assoc _ _ _))
                   (λ _ → fbT≡ (A.+Rid _) (B.+Rid _))
                   (λ _ → fbT≡ (A.+Rinv _) (B.+Rinv _))
                   (λ _ _ → fbT≡ (A.+Comm _ _) (B.+Comm _ _))
                   (λ _ _ _ → fbT≡ (A.·Assoc _ _ _) (B.·Assoc _ _ _))
                   (λ _ → fbT≡ (A.·Rid _) (B.·Rid _))
                   (λ _ _ _ → fbT≡ (A.·Rdist+ _ _ _) (B.·Rdist+ _ _ _))
                   (λ _ _ → fbT≡ (A.·Comm _ _) (B.·Comm _ _))

  fiberedProductPr₁ : CommRingHom fiberedProduct A
  fst fiberedProductPr₁ = fst ∘ fst
  snd fiberedProductPr₁ = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)

  fiberedProductPr₂ : CommRingHom fiberedProduct B
  fst fiberedProductPr₂ = snd ∘ fst
  snd fiberedProductPr₂ = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)

  fiberedProductPr₁₂Commutes : compCommRingHom fiberedProduct A C fiberedProductPr₁ α ≡
                               compCommRingHom fiberedProduct B C fiberedProductPr₂ β
  fiberedProductPr₁₂Commutes = RingHom≡ (funExt (λ x → x .snd))

  open IsRingHom

  fiberedProductUnivProp :
    (D : CommRing ℓ) (h : CommRingHom D A) (k : CommRingHom D B) →
    compCommRingHom D A C h α ≡ compCommRingHom D B C k β →
    ∃![ l ∈ CommRingHom D fiberedProduct ] (h ≡ compCommRingHom D fiberedProduct A l fiberedProductPr₁)
                                         × (k ≡ compCommRingHom D fiberedProduct B l fiberedProductPr₂)
  fiberedProductUnivProp D (h , hh) (k , hk) H =
    uniqueExists f (RingHom≡ refl , RingHom≡ refl)
                 (λ _ → isProp× (isSetRingHom _ _ _ _) (isSetRingHom _ _ _ _))
                 (λ { (g , _) (Hh , Hk) → RingHom≡ (funExt (λ d → fbT≡ (funExt⁻ (cong fst Hh) d)
                                                                       (funExt⁻ (cong fst Hk) d))) })
    where
    f : CommRingHom D fiberedProduct
    fst f d = (h d , k d) , funExt⁻ (cong fst H) d
    snd f = makeIsRingHom (fbT≡ (hh .pres1) (hk .pres1))
                          (λ _ _ → fbT≡ (hh .pres+ _ _) (hk .pres+ _ _))
                          (λ _ _ → fbT≡ (hh .pres· _ _) (hk .pres· _ _))


open FiberedProduct
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
PullbackCommRing : Pullbacks {ℓ-suc ℓ} CommRingsCategory
pbOb (PullbackCommRing (cospan A C B α β)) = fiberedProduct A B C α β
pbPr₁ (PullbackCommRing (cospan A C B α β)) = fiberedProductPr₁ A B C α β
pbPr₂ (PullbackCommRing (cospan A C B α β)) = fiberedProductPr₂ A B C α β
pbCommutes (PullbackCommRing (cospan A C B α β)) = fiberedProductPr₁₂Commutes A B C α β
isPb (PullbackCommRing (cospan A C B α β)) {d = D} = fiberedProductUnivProp A B C α β D
