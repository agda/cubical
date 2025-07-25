{-# OPTIONS --lossy-unification #-}

module Cubical.ZCohomology.CohomologyRings.KleinBottle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; discreteℕ ; suc-predℕ ; +-comm)
open import Cubical.Data.Int
open import Cubical.Data.Int.IsEven
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-notationZ

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.KleinBottle

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.Groups.KleinBottle
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso


{- Convention over ℤ[X,Y]
   X : (1,0)
   Y : (0,1)
-}

module Equiv-𝕂²-Properties
  (e₁ : GroupIso ℤGroup (coHomGr 1 KleinBottle))
  (e₂ : GroupIso BoolGroup (coHomGr 2 KleinBottle))
  where


-----------------------------------------------------------------------------
-- Definitions, Import with notations, Partition

  -- Definition
  private
    ℤAG = Ring→AbGroup (CommRing→Ring ℤCR)

  <2Y,Y²,XY,X²> : FinVec ℤ[x,y] 4
  <2Y,Y²,XY,X²> zero  = base (0 ∷ 1 ∷ []) 2
  <2Y,Y²,XY,X²> one   = base (0 ∷ 2 ∷ []) 1
  <2Y,Y²,XY,X²> two   = base (1 ∷ 1 ∷ []) 1
  <2Y,Y²,XY,X²> three = base (2 ∷ 0 ∷ []) 1

  ℤ[X,Y]/<2Y,Y²,XY,X²> : CommRing ℓ-zero
  ℤ[X,Y]/<2Y,Y²,XY,X²> = PolyCommRing-Quotient ℤCR <2Y,Y²,XY,X²>

  ℤ[x,y]/<2y,y²,xy,x²> : Type ℓ-zero
  ℤ[x,y]/<2y,y²,xy,x²> = fst ℤ[X,Y]/<2Y,Y²,XY,X²>

  -- Import with notation
  open IsGroupHom
  open gradedRingProperties

  open GroupStr (snd BoolGroup) using ()
    renaming
    ( 1g        to 0gBool
    ; _·_       to _+Bool_
    ; inv       to -Bool_
    ; ·Assoc    to +BoolAssoc
    ; ·IdL      to +BoolIdL
    ; ·IdR      to +BoolIdR
    ; is-set    to isSetBool   )

  open CommRingStr (snd ℤCR) using ()
    renaming
    ( 0r        to 0ℤ
    ; 1r        to 1ℤ
    ; _+_       to _+ℤ_
    ; -_        to -ℤ_
    ; _·_       to _·ℤ_
    ; +Assoc    to +ℤAssoc
    ; +IdL      to +ℤIdL
    ; +IdR      to +ℤIdR
    ; +Comm     to +ℤComm
    ; ·Assoc    to ·ℤAssoc
    ; ·IdL      to ·ℤIdL
    ; ·IdR      to ·ℤIdR
    ; ·DistR+   to ·ℤDistR+
    ; ·Comm     to ·ℤComm
    ; is-set    to isSetℤ     )

  open RingStr (snd (H*R KleinBottle)) using ()
    renaming
    ( 0r        to 0H*
    ; 1r        to 1H*
    ; _+_       to _+H*_
    ; -_        to -H*_
    ; _·_       to _cup_
    ; +Assoc    to +H*Assoc
    ; +IdL      to +H*IdL
    ; +IdR      to +H*IdR
    ; +Comm     to +H*Comm
    ; ·Assoc    to ·H*Assoc
    ; ·IdL      to ·H*IdL
    ; ·IdR      to ·H*IdR
    ; ·DistR+   to ·H*DistR+
    ; is-set    to isSetH*     )

  open CommRingStr (snd ℤ[X,Y]) using ()
    renaming
    ( 0r        to 0Pℤ
    ; 1r        to 1Pℤ
    ; _+_       to _+Pℤ_
    ; -_        to -Pℤ_
    ; _·_       to _·Pℤ_
    ; +Assoc    to +PℤAssoc
    ; +IdL      to +PℤIdL
    ; +IdR      to +PℤIdR
    ; +Comm     to +PℤComm
    ; ·Assoc    to ·PℤAssoc
    ; ·IdL      to ·PℤIdL
    ; ·IdR      to ·PℤIdR
    ; ·Comm     to ·PℤComm
    ; ·DistR+   to ·PℤDistR+
    ; is-set    to isSetPℤ     )

  open CommRingStr (snd ℤ[X,Y]/<2Y,Y²,XY,X²>) using ()
    renaming
    ( 0r        to 0PℤI
    ; 1r        to 1PℤI
    ; _+_       to _+PℤI_
    ; -_        to -PℤI_
    ; _·_       to _·PℤI_
    ; +Assoc    to +PℤIAssoc
    ; +IdL      to +PℤIIdL
    ; +IdR      to +PℤIIdR
    ; +Comm     to +PℤIComm
    ; ·Assoc    to ·PℤIAssoc
    ; ·IdL      to ·PℤIIdL
    ; ·IdR      to ·PℤIIdR
    ; ·DistR+   to ·PℤIDistR+
    ; is-set    to isSetPℤI     )


  e₀ = invGroupIso H⁰-𝕂²≅ℤ
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)

  ϕ₁ = fun (fst e₁)
  ϕ₁str = snd e₁
  ϕ₁⁻¹ = inv (fst e₁)
  ϕ₁⁻¹str = snd (invGroupIso e₁)
  ϕ₁-sect = rightInv (fst e₁)
  ϕ₁-retr = leftInv (fst e₁)

  ϕ₂ = fun (fst e₂)
  ϕ₂str = snd e₂
  ϕ₂⁻¹ = inv (fst e₂)
  ϕ₂⁻¹str = snd (invGroupIso e₂)
  ϕ₂-sect = rightInv (fst e₂)
  ϕ₂-retr = leftInv (fst e₂)

  module PblComp
    (null-H¹  : (a b : ℤ) → (ϕ₁ a) ⌣  (ϕ₁ b) ≡ 0ₕ 2)
    where

  -----------------------------------------------------------------------------
  -- Direct Sens on ℤ[x,y]

    ψ₂ : ℤ → Bool
    ψ₂ = isEven

    ϕ₂∘ψ₂str : IsGroupHom (snd ℤGroup) (ϕ₂ ∘ ψ₂) (snd (coHomGr 2 KleinBottle))
    ϕ₂∘ψ₂str = isGroupHomComp (ψ₂ , isEven-GroupMorphism) (ϕ₂ , ϕ₂str)

    ℤ[x,y]→H*-𝕂² : ℤ[x,y] → H* KleinBottle
    ℤ[x,y]→H*-𝕂² = DS-Rec-Set.f _ _ _ _ isSetH*
                        0H*
                        ϕ
                        _+H*_
                        +H*Assoc
                        +H*IdR
                        +H*Comm
                        base-neutral-eq
                        base-add-eq
     where
     ϕ : _
     ϕ (zero        ∷ zero        ∷ []) a = base 0 (ϕ₀ a)
     ϕ (zero        ∷ one         ∷ []) a = base 2 ((ϕ₂ ∘ ψ₂) a)
     ϕ (zero        ∷ suc (suc m) ∷ []) a = 0H*
     ϕ (one         ∷ zero        ∷ []) a = base 1 (ϕ₁ a)
     ϕ (one         ∷ suc m       ∷ []) a = 0H*
     ϕ (suc (suc n) ∷ m           ∷ []) a = 0H*

     base-neutral-eq : _
     base-neutral-eq (zero        ∷ zero        ∷ []) = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
     base-neutral-eq (zero        ∷ one         ∷ []) = cong (base 2) (pres1 ϕ₂∘ψ₂str) ∙ base-neutral _
     base-neutral-eq (zero        ∷ suc (suc m) ∷ []) = refl
     base-neutral-eq (one         ∷ zero        ∷ []) = cong (base 1) (pres1 ϕ₁str) ∙ base-neutral _
     base-neutral-eq (one         ∷ suc m       ∷ []) = refl
     base-neutral-eq (suc (suc n) ∷ m           ∷ []) = refl

     base-add-eq : _
     base-add-eq (zero        ∷ zero        ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym (pres· ϕ₀str _ _))
     base-add-eq (zero        ∷ one         ∷ []) a b = base-add _ _ _ ∙ cong (base 2) (sym (pres· ϕ₂∘ψ₂str _ _))
     base-add-eq (zero        ∷ suc (suc m) ∷ []) a b = +H*IdR _
     base-add-eq (one         ∷ zero        ∷ []) a b = base-add _ _ _ ∙ cong (base 1) (sym (pres· ϕ₁str _ _))
     base-add-eq (one         ∷ suc m       ∷ []) a b = +H*IdR _
     base-add-eq (suc (suc n) ∷ m           ∷ []) a b = +H*IdR _

  -----------------------------------------------------------------------------
  -- Morphism on ℤ[x]

    ℤ[x,y]→H*-𝕂²-pres1 : ℤ[x,y]→H*-𝕂² (1Pℤ) ≡ 1H*
    ℤ[x,y]→H*-𝕂²-pres1 = refl

    ℤ[x,y]→H*-𝕂²-pres+ : (x y : ℤ[x,y]) → ℤ[x,y]→H*-𝕂² (x +Pℤ y) ≡ ℤ[x,y]→H*-𝕂² x +H* ℤ[x,y]→H*-𝕂² y
    ℤ[x,y]→H*-𝕂²-pres+ x y = refl

    --           Explanation of the product proof
    --
    --           -------------------------------------------------------
    --           | (0,0) | (0,1) | (0,m+2) | (1,0) | (1,m+1) | (n+2,m) |
    -- -----------------------------------------------------------------
    -- | (0,0)   |   H⁰  |   H⁰  |    0    |   H⁰  |    0    |    0    |
    -- -----------------------------------------------------------------
    -- | (0,1)   |  Sym  |   0₄  |    0    |   0₃  |    0    |    0    |
    -- -----------------------------------------------------------------
    -- | (0,m+2) | ==========================================> triv    |
    -- -----------------------------------------------------------------
    -- | (1,0)   |  Sym  |  Sym  |    0    |   ★  |    0    |    0    |
    -- -----------------------------------------------------------------
    -- | (1,m+1) | ==========================================> triv    |
    -- -----------------------------------------------------------------
    -- | (n+2,m) | ==========================================> triv    |
    -- -----------------------------------------------------------------

    -- ★ : prove that ϕ₁(1) ⌣ ϕ₁(1) ≡ 0

    open pres⌣


    ϕ₀-gen : (n : ℕ) → (f : coHom n KleinBottle) → ϕ₀ (pos 1) ⌣ f ≡ f
    ϕ₀-gen n = ST.elim (λ _ → isProp→isSet (GroupStr.is-set (snd (coHomGr n KleinBottle)) _ _))
                       (λ f → cong ∣_∣₂ (funExt (λ x → rUnitₖ n (f x))))

    -- note that the proof might be simplified by adding a second partition on T
    -- side, though it might complicated a bunch of things
    pres·-int : (n m : ℕ) → (a : ℤ) → (k l : ℕ) → (b : ℤ) →
                   ℤ[x,y]→H*-𝕂² (base (n ∷ m ∷ []) a ·Pℤ base (k ∷ l ∷ []) b)
                ≡ ℤ[x,y]→H*-𝕂² (base (n ∷ m ∷ []) a) cup ℤ[x,y]→H*-𝕂² (base (k ∷ l ∷ []) b)

      -- non trivial case (0,0)
    pres·-int zero zero a zero zero          b = cong (base 0) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₀str _ ϕ₀str (ϕ₀-gen _ _) _ _)
    pres·-int zero zero a zero one           b = cong (base 2) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₂∘ψ₂str _ ϕ₂∘ψ₂str (ϕ₀-gen _ _) _ _)
    pres·-int zero zero a zero (suc (suc l)) b = refl
    pres·-int zero zero a one zero           b = cong (base 1) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₁str _ ϕ₁str (ϕ₀-gen _ _) _ _)
    pres·-int zero zero a one (suc l)        b = refl
    pres·-int zero zero a (suc (suc k)) l    b = refl
      -- non trivial case (0,1)
    pres·-int zero one a zero  zero         b = cong ℤ[x,y]→H*-𝕂² (·PℤComm (base (0 ∷ 1 ∷ []) a) (base (0 ∷ 0 ∷ []) b))
                                                ∙ pres·-int 0 0 b 0 1 a
                                                ∙ gradCommRing KleinBottle _ _ _ _
    pres·-int zero one a zero  one          b = sym (base-neutral 4)
                                                ∙ cong (base 4) (unitGroupEq (Hⁿ⁺³-𝕂²≅0 1) _ _)
    pres·-int zero one a zero (suc (suc l)) b = refl
    pres·-int zero one a one zero           b = sym (base-neutral 3)
                                                ∙ cong (base 3) (unitGroupEq (Hⁿ⁺³-𝕂²≅0 0) _ _)
    pres·-int zero one a one (suc l)        b = refl
    pres·-int zero one a (suc (suc k)) l    b = refl
      -- trivial case (0, m+2)
    pres·-int zero (suc (suc m)) a  zero         l b = refl
    pres·-int zero (suc (suc m)) a  one          l b = refl
    pres·-int zero (suc (suc m)) a (suc (suc k)) l b = refl
      -- non trivial case (1,0)
    pres·-int one zero a zero zero          b = cong ℤ[x,y]→H*-𝕂² (·PℤComm (base (1 ∷ 0 ∷ []) a) (base (0 ∷ 0 ∷ []) b))
                                                ∙ pres·-int 0 0 b 1 0 a
                                                ∙ gradCommRing KleinBottle _ _ _ _
    pres·-int one zero a zero one           b = cong ℤ[x,y]→H*-𝕂² (·PℤComm (base (1 ∷ 0 ∷ []) a) (base (0 ∷ 1 ∷ []) b))
                                                ∙ pres·-int 0 1 b 1 0 a
                                                ∙ gradCommRing KleinBottle _ _ _ _
    pres·-int one zero a zero (suc (suc l)) b = refl
    pres·-int one zero a one zero           b = sym (base-neutral 2)
                                                ∙ cong (base 2) (sym (null-H¹ _ _))
    pres·-int one zero a one (suc l)        b = refl
    pres·-int one zero a (suc (suc k)) l    b = refl
      -- trivial case (1,m+1)
    pres·-int one (suc m) a  zero   l b = refl
    pres·-int one (suc m) a (suc k) l b = refl
      -- trivial case (n+2,m)
    pres·-int (suc (suc n)) m a k l b = refl



    pres·-base-case-vec : (v : Vec ℕ 2) → (a : ℤ) → (v' : Vec ℕ 2) → (b : ℤ) →
                             ℤ[x,y]→H*-𝕂² (base v a ·Pℤ base v' b)
                          ≡ ℤ[x,y]→H*-𝕂² (base v a) cup ℤ[x,y]→H*-𝕂² (base v' b)
    pres·-base-case-vec (n ∷ m ∷ []) a (k ∷ l ∷ []) b = pres·-int n m a k l b

    -- proof of the morphism
    ℤ[x,y]→H*-𝕂²-pres· : (x y : ℤ[x,y]) → ℤ[x,y]→H*-𝕂² (x ·Pℤ y) ≡ ℤ[x,y]→H*-𝕂² x cup ℤ[x,y]→H*-𝕂² y
    ℤ[x,y]→H*-𝕂²-pres· = DS-Ind-Prop.f _ _ _ _
                           (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                           (λ y → refl)
                           base-case
                           λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
      where
      base-case : _
      base-case v a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                             (sym (RingTheory.0RightAnnihilates (H*R KleinBottle) _))
                             (λ v' b → pres·-base-case-vec v a v' b )
                             λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


  -----------------------------------------------------------------------------
  -- Function on ℤ[x]/x + morphism

    -- not a trivial cancel ?
    ℤ[x,y]→H*-𝕂²-cancel : (x : Fin 4) → ℤ[x,y]→H*-𝕂² (<2Y,Y²,XY,X²> x) ≡ 0H*
    ℤ[x,y]→H*-𝕂²-cancel zero = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
    ℤ[x,y]→H*-𝕂²-cancel one = refl
    ℤ[x,y]→H*-𝕂²-cancel two = refl
    ℤ[x,y]→H*-𝕂²-cancel three = refl


    ℤ[X,Y]→H*-𝕂² : RingHom (CommRing→Ring ℤ[X,Y]) (H*R KleinBottle)
    fst ℤ[X,Y]→H*-𝕂² = ℤ[x,y]→H*-𝕂²
    snd ℤ[X,Y]→H*-𝕂² = makeIsRingHom ℤ[x,y]→H*-𝕂²-pres1
                                       ℤ[x,y]→H*-𝕂²-pres+
                                       ℤ[x,y]→H*-𝕂²-pres·

    -- hence not a trivial pres+, yet pres0 still is
    ℤ[X,Y]/<2Y,Y²,XY,X²>→H*R-𝕂² : RingHom (CommRing→Ring ℤ[X,Y]/<2Y,Y²,XY,X²>) (H*R KleinBottle)
    ℤ[X,Y]/<2Y,Y²,XY,X²>→H*R-𝕂² = Quotient-FGideal-CommRing-Ring.inducedHom
                                    ℤ[X,Y] (H*R KleinBottle) ℤ[X,Y]→H*-𝕂²
                                    <2Y,Y²,XY,X²> ℤ[x,y]→H*-𝕂²-cancel

    ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² : ℤ[x,y]/<2y,y²,xy,x²> → H* KleinBottle
    ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² = fst ℤ[X,Y]/<2Y,Y²,XY,X²>→H*R-𝕂²

    ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂²-pres0 : ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² 0PℤI ≡ 0H*
    ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂²-pres0 = refl

    ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂²-pres+ : (x y : ℤ[x,y]/<2y,y²,xy,x²>) →
                                             ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² ( x +PℤI y)
                                          ≡ ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² x +H* ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² y
    ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂²-pres+ x y = IsRingHom.pres+ (snd ℤ[X,Y]/<2Y,Y²,XY,X²>→H*R-𝕂²) x y


  -----------------------------------------------------------------------------
  -- Converse Sens on H* → ℤ[X,Y]

    ψ₂⁻¹ : Bool → ℤ
    ψ₂⁻¹ false = 1
    ψ₂⁻¹ true = 0

    private
    -- Those lemma are requiered because ψ₂⁻¹
    -- is a morphism only under the quotient
      Λ : (x : Bool) → ℤ[x,y]/<2y,y²,xy,x²>
      Λ x = [ (base (0 ∷ 1 ∷ []) (ψ₂⁻¹ x)) ]

      Λ-pres+ : (x y : Bool) → Λ x +PℤI Λ y ≡ Λ (x +Bool y)
      Λ-pres+ false false = cong [_] (base-add _ _ _)
                            ∙ eq/ (base (0 ∷ 1 ∷ []) 2)
                                  (base (0 ∷ 1 ∷ []) 0)
                                  ∣ ((λ {zero → base (0 ∷ 0 ∷ []) 1 ; one → 0Pℤ ; two → 0Pℤ ; three → 0Pℤ}) , helper) ∣₁
              where
              helper : _
              helper = base-add  _ _ _
                       ∙ sym (cong₂ _+Pℤ_ refl (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdL _) ∙ +PℤIdR _)
      Λ-pres+ false true = cong [_] (base-add _ _ _)
      Λ-pres+ true false = cong [_] (base-add _ _ _)
      Λ-pres+ true true = cong [_] (base-add _ _ _)

    ϕ⁻¹ : (k : ℕ) → (a : coHom k KleinBottle) → ℤ[x,y]/<2y,y²,xy,x²>
    ϕ⁻¹ zero a = [ base (0 ∷ 0 ∷ []) (ϕ₀⁻¹ a) ]
    ϕ⁻¹ one a = [ base (1 ∷ 0 ∷ []) (ϕ₁⁻¹ a) ]
    ϕ⁻¹ two a = [ base (0 ∷ 1 ∷ []) ((ψ₂⁻¹ ∘ ϕ₂⁻¹) a) ]
    ϕ⁻¹ (suc (suc (suc k))) a = 0PℤI

    H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> : H* KleinBottle → ℤ[x,y]/<2y,y²,xy,x²>
    H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> = DS-Rec-Set.f _ _ _ _ isSetPℤI
         0PℤI
         ϕ⁻¹
         _+PℤI_
         +PℤIAssoc
         +PℤIIdR
         +PℤIComm
         base-neutral-eq
         base-add-eq
      where

      base-neutral-eq : _
      base-neutral-eq zero = cong [_] (cong (base {AGP = λ _ → snd ℤAG} (0 ∷ 0 ∷ [])) (pres1 ϕ₀⁻¹str)
                                       ∙ (base-neutral _))
      base-neutral-eq one = cong [_] (cong (base {AGP = λ _ → snd ℤAG} (1 ∷ 0 ∷ [])) (pres1 ϕ₁⁻¹str)
                                       ∙ (base-neutral _))
      base-neutral-eq two = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ (pres1 ϕ₂⁻¹str))
                                     ∙ base-neutral _)
      base-neutral-eq (suc (suc (suc k))) = refl

      base-add-eq : _
      base-add-eq zero a b = cong [_] (base-add _ _ _ ∙ cong (base (0 ∷ 0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _)))
      base-add-eq one a b = cong [_] (base-add _ _ _ ∙ cong (base (1 ∷ 0 ∷ [])) (sym (pres· ϕ₁⁻¹str _ _)))
      base-add-eq two a b = Λ-pres+ (ϕ₂⁻¹ a) (ϕ₂⁻¹ b)
                            ∙ cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ (sym (pres· ϕ₂⁻¹str _ _))))
      base-add-eq (suc (suc (suc k))) a b = +PℤIIdR _

    H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²>-pres0 : H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> 0H* ≡ 0PℤI
    H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²>-pres0 = refl

    H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²>-pres+ : (x y : H* KleinBottle) →
                                               H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> (x +H* y)
                                           ≡ (H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> x) +PℤI (H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> y)
    H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²>-pres+ x y = refl



  -----------------------------------------------------------------------------
  -- Section

    ψ₂-sect : (x : Bool) → ψ₂ (ψ₂⁻¹ x) ≡ x
    ψ₂-sect false = refl
    ψ₂-sect true = refl


    e-sect-base : (k : ℕ) → (a : coHom k KleinBottle) →
                  ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² (ϕ⁻¹ k a) ≡ base k a
    e-sect-base zero a = cong (base 0) (ϕ₀-sect a)
    e-sect-base one a = cong (base 1) (ϕ₁-sect a)
    e-sect-base two a = cong (base 2) (cong ϕ₂ (ψ₂-sect _) ∙ ϕ₂-sect a)
    e-sect-base (suc (suc (suc k))) a = sym (base-neutral (suc (suc (suc k))))
                                        ∙ cong (base (suc (suc (suc k)))) (unitGroupEq (Hⁿ⁺³-𝕂²≅0 k) _ _)

    e-sect : (x : H* KleinBottle) → ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² (H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> x) ≡ x
    e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
             refl
             e-sect-base
             λ {U V} ind-U ind-V → ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂²-pres+ _ _ ∙ cong₂ _+H*_ ind-U ind-V



  -----------------------------------------------------------------------------
  -- Retraction

    e-retr-ψ₂-false : (a : ℤ) → (isEven a ≡ false) → Λ (ψ₂ a) ≡ [ base (0 ∷ 1 ∷ []) a ]
    e-retr-ψ₂-false a x = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ x))
                    ∙ eq/ (base (0 ∷ 1 ∷ []) 1) (base (0 ∷ 1 ∷ []) a)
                      ∣ ((λ {zero → base (0 ∷ 0 ∷ []) (-ℤ m) ; one → 0Pℤ ; two → 0Pℤ ; three → 0Pℤ}) , helper) ∣₁
              where
              m = fst (isEvenFalse a x)

              helper : _
              helper = base-add _ _ _
                       ∙ cong (base (0 ∷ 1 ∷ [])) (cong (λ X → 1 +ℤ (-ℤ X)) (snd (isEvenFalse a x))
                                               ∙ cong (λ X → 1 +ℤ X) (-Dist+ _ _)
                                               ∙ +ℤAssoc _ _ _
                                               ∙ +ℤIdL _)
                       ∙ sym (cong₂ _+Pℤ_ (cong (base (0 ∷ 1 ∷ [])) (sym (-DistL· _ _) ∙ cong -ℤ_ (·ℤComm _ _)))
                                          (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdL _)
                             ∙ +PℤIdR _)

    e-retr-ψ₂-true : (a : ℤ) → (isEven a ≡ true) → Λ (ψ₂ a) ≡ [ base (0 ∷ 1 ∷ []) a ]
    e-retr-ψ₂-true a x = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ x))
                    ∙ eq/ (base (0 ∷ 1 ∷ []) 0) (base (0 ∷ 1 ∷ []) a)
                      ∣ ((λ {zero → base (0 ∷ 0 ∷ []) (-ℤ m) ; one → 0Pℤ ; two → 0Pℤ ; three → 0Pℤ}) , helper) ∣₁
              where
              m = fst (isEvenTrue a x)

              helper : _
              helper = base-add _ _ _
                       ∙ cong (base (0 ∷ 1 ∷ [])) (+ℤIdL _ ∙ cong -ℤ_ (snd (isEvenTrue a x)))
                       ∙ sym (cong₂ _+Pℤ_ (cong (base (0 ∷ 1 ∷ [])) (sym (-DistL· _ _) ∙ cong -ℤ_ (·ℤComm _ _)))
                                          (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdL _)
                             ∙ +PℤIdR _)


    e-retr-ψ₂ : (a : ℤ) → ((isEven a ≡ false) ⊎ (isEven a ≡ true)) → Λ (ψ₂ a) ≡ [ base (0 ∷ 1 ∷ []) a ]
    e-retr-ψ₂ a (inl x) = e-retr-ψ₂-false a x
    e-retr-ψ₂ a (inr x) = e-retr-ψ₂-true a x



    e-retr-base : (v : Vec ℕ 2) → (a : ℤ) →
                  H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> (ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² [ base v a ]) ≡ [ base v a ]
    e-retr-base (zero        ∷ zero        ∷ []) a = cong [_] (cong (base (0 ∷ 0 ∷ [])) (ϕ₀-retr a))
    e-retr-base (zero        ∷ one         ∷ []) a = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ (ϕ₂-retr (ψ₂ a))))
                                                      ∙ e-retr-ψ₂ a (dichotomyBoolSym (isEven a))
    e-retr-base (zero        ∷ suc (suc m) ∷ []) a = eq/ _ _ ∣ (v , helper) ∣₁
           where
           v = λ { zero → 0Pℤ ; one → base (0 ∷ m ∷ []) (-ℤ a) ; two → 0Pℤ ; three → 0Pℤ }
           helper : _
           helper = +PℤIdL _ ∙ sym (+PℤIdL _
                    ∙ cong₂ _+Pℤ_ (cong₂ base (cong (λ X → 0 ∷ X ∷ []) (+-comm _ _)) (·ℤIdR _))
                                  (+PℤIdL _ ∙ +PℤIdL _) ∙ +PℤIdR _)
    e-retr-base (one         ∷ zero        ∷ []) a = cong [_] (cong (base (1 ∷ 0 ∷ [])) (ϕ₁-retr a))
    e-retr-base (one         ∷ suc m       ∷ []) a = eq/ _ _ ∣ (v , helper) ∣₁
           where
           v = λ { zero → 0Pℤ ; one → 0Pℤ ; two → base (0 ∷ m ∷ []) (-ℤ a) ; three → 0Pℤ }
           helper : _
           helper = +PℤIdL _ ∙ sym (+PℤIdL _ ∙ +PℤIdL _
                    ∙ cong₂ _+Pℤ_ (cong₂ base (cong (λ X → 1 ∷ X ∷ []) (+-comm _ _)) (·ℤIdR _)) (+PℤIdL _) ∙ +PℤIdR _)
    e-retr-base (suc (suc n) ∷ m           ∷ []) a = eq/ _ _ ∣ (v , helper) ∣₁
           where
           v = λ {zero → 0Pℤ ; one → 0Pℤ ; two → 0Pℤ ; three → base (n ∷ m ∷ []) (-ℤ a) }
           helper : _
           helper = +PℤIdL _ ∙ sym (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdR _
                    ∙ cong₂ base (cong₂ (λ X → λ Y → X ∷ Y ∷ []) (+-comm _ _) (+-comm _ _)) (·ℤIdR _))

    e-retr : (x : ℤ[x,y]/<2y,y²,xy,x²>) → H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²> (ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂² x) ≡ x
    e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
             (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
             refl
             e-retr-base
             λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)



-- Computation of the Cohomology Ring

module _ where

  open Equiv-𝕂²-Properties (invGroupIso H¹-𝕂²≅ℤ) (invGroupIso H²-𝕂²≅Bool)
  open pres⌣trivial
  open PblComp (λ a b → sym (ϕₙ⌣ϕₘ-0 ϕ₁ ϕ₁str ϕ₁ ϕ₁str trivial-cup a b))

  𝕂²-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X,Y]/<2Y,Y²,XY,X²>) (H*R KleinBottle)
  fst 𝕂²-CohomologyRing = isoToEquiv is
    where
    is : Iso ℤ[x,y]/<2y,y²,xy,x²> (H* KleinBottle)
    fun is = ℤ[x,y]/<2y,y²,xy,x²>→H*-𝕂²
    inv is = H*-𝕂²→ℤ[x,y]/<2y,y²,xy,x²>
    rightInv is = e-sect
    leftInv is = e-retr
  snd 𝕂²-CohomologyRing = snd ℤ[X,Y]/<2Y,Y²,XY,X²>→H*R-𝕂²

  CohomologyRing-𝕂² : RingEquiv (H*R KleinBottle) (CommRing→Ring ℤ[X,Y]/<2Y,Y²,XY,X²>)
  CohomologyRing-𝕂² = RingEquivs.invRingEquiv 𝕂²-CohomologyRing
