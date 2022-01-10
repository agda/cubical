{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.CommRings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FiberedProduct
open import Cubical.Algebra.CommRing.Instances.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Pullback

open import Cubical.HITs.PropositionalTruncation

open Category hiding (_∘_)
open CommRingHoms

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

TerminalCommRing : Terminal {ℓ-suc ℓ-zero} CommRingsCategory
fst TerminalCommRing = UnitCommRing
fst (fst (snd TerminalCommRing y)) _ = tt
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
PullbackCommRing : Pullbacks {ℓ-suc ℓ} CommRingsCategory
pbOb (PullbackCommRing (cospan A C B α β)) = fiberedProduct A B C α β
pbPr₁ (PullbackCommRing (cospan A C B α β)) = fiberedProductPr₁ A B C α β
pbPr₂ (PullbackCommRing (cospan A C B α β)) = fiberedProductPr₂ A B C α β
pbCommutes (PullbackCommRing (cospan A C B α β)) = fiberedProductPr₁₂Commutes A B C α β
univProp (PullbackCommRing (cospan A C B α β)) {d = D} = fiberedProductUnivProp A B C α β D


-- techiques for constructing CommRing valued presheaves
-- throuh universal properties
CommRingValPShf : {ℓ : Level} → Category ℓ ℓ' → Category _ _
CommRingValPShf {ℓ = ℓ} C = FUNCTOR (C ^op) (CommRingsCategory {ℓ = ℓ})

module PreSheafFromUniversalProp (C : Category ℓ ℓ') (P : ob C → Type ℓ)
         (𝓕 : Σ (ob C) P → CommRing ℓ)
         (Q : ∀ {x y} → CommRingHom (𝓕 x) (𝓕 y) → Type ℓ'')
         (isPropQ : ∀ {x y} (f : CommRingHom (𝓕 x) (𝓕 y)) → isProp (Q f))
         (Qid : ∀ {x} → Q (idCommRingHom (𝓕 x)))
         (Qcomp : ∀ {x y z} {f : CommRingHom (𝓕 x) (𝓕 y)} {g : CommRingHom (𝓕 y) (𝓕 z)}
                → Q f → Q g → Q (compCommRingHom (𝓕 x) (𝓕 y) (𝓕 z) f g))
         (uniqueQHom : ∀ x y → C [ fst x , fst y ] → ∃![ f ∈ CommRingHom (𝓕 y) (𝓕 x) ] Q f)
         where

 private
  ∥P∥ : ℙ (ob C)
  ∥P∥ x  = ∥ P x ∥ , isPropPropTrunc

  ΣC∥P∥Cat = ΣPropCat C ∥P∥

 open Functor
 universalPShf : Functor (ΣC∥P∥Cat ^op) (CommRingsCategory {ℓ = ℓ})
 F-ob universalPShf = uncurry theMap
  where
  theMap : (x : ob C) → ∥ P x ∥ → CommRing ℓ
  theMap x = recPT→CommRing (curry 𝓕 x)
    (λ p q → 𝓕UniqueEquiv p q .fst .fst)
      λ p q r → cong fst (𝓕UniqueEquiv p r .snd (_ , Qcomp (𝓕UniqueEquiv p q .fst .snd)
                                                            (𝓕UniqueEquiv q r .fst .snd)))
   where
   𝓕UniqueEquiv : (p q : P x)
                 → ∃![ e ∈ CommRingEquiv (𝓕 (x , p)) (𝓕 (x , q)) ] Q (RingEquiv→RingHom e)
   𝓕UniqueEquiv = uniqueCommHom→uniqueCommEquiv (curry 𝓕 x) Q isPropQ Qid Qcomp
                                                     λ p q → uniqueQHom _ _ (id C)

 F-hom universalPShf f = {!uniqueQHom _ _ f .fst!}
  -- where
  -- curriedAndExplicit : (x y : ob C) → ∥ P x ∥ → ∥ P y ∥ →

 F-id universalPShf = {!!}
 F-seq universalPShf = {!!}
