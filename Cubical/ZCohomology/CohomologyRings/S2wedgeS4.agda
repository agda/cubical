{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.ZCohomology.CohomologyRings.S2wedgeS4 where

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
open import Cubical.Algebra.Group.Instances.Int renaming (ℤGroup to ℤG)
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.RPn.Base

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.Groups.S2wedgeS4
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso


module Equiv-RP2-Properties where

-----------------------------------------------------------------------------
-- Definitions, Import with notations, Partition

  -- Definition
  private
    ℤAG = Ring→AbGroup (CommRing→Ring ℤCR)

  <XY,X²,Y²> : FinVec ℤ[x,y] 3
  <XY,X²,Y²> zero = base (1 ∷ 1 ∷ []) 1
  <XY,X²,Y²> one = base (2 ∷ 0 ∷ []) 1
  <XY,X²,Y²> two = base (0 ∷ 2 ∷ []) 1

  ℤ[X,Y]/<XY,X²,Y²> : CommRing ℓ-zero
  ℤ[X,Y]/<XY,X²,Y²> = PolyCommRing-Quotient ℤCR <XY,X²,Y²>

  ℤ[x,y]/<xy,x²,y²> : Type ℓ-zero
  ℤ[x,y]/<xy,x²,y²> = fst ℤ[X,Y]/<XY,X²,Y²>

  -- Import with notation
  open IsGroupHom
  open gradedRingProperties

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

  open RingStr (snd (H*R S²⋁S⁴)) using ()
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

  open CommRingStr (snd ℤ[X,Y]/<XY,X²,Y²>) using ()
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


  e₀ = invGroupIso H⁰-S²⋁S⁴≅ℤ
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)

  e₂ = invGroupIso H²-S²⋁S⁴≅ℤ
  ϕ₂ = fun (fst e₂)
  ϕ₂str = snd e₂
  ϕ₂⁻¹ = inv (fst e₂)
  ϕ₂⁻¹str = snd (invGroupIso e₂)
  ϕ₂-sect = rightInv (fst e₂)
  ϕ₂-retr = leftInv (fst e₂)

  e₄ = invGroupIso H⁴-S²⋁S⁴≅ℤ
  ϕ₄ = fun (fst e₄)
  ϕ₄str = snd e₄
  ϕ₄⁻¹ = inv (fst e₄)
  ϕ₄⁻¹str = snd (invGroupIso e₄)
  ϕ₄-sect = rightInv (fst e₄)
  ϕ₄-retr = leftInv (fst e₄)

  -- Partition
  data partℕ (k : ℕ) : Type ℓ-zero where
    is0  : (k ≡ 0)            → partℕ k
    is2  : (k ≡ 2)            → partℕ k
    is4  : (k ≡ 4)            → partℕ k
    else : (k ≡ 0 → ⊥)
           × ((k ≡ 2 → ⊥)
              × (k ≡ 4 → ⊥)) → partℕ k

  part : (k : ℕ) → partℕ k
  part k with (discreteℕ k 0)
  ... | yes p = is0 p
  ... | no ¬p with (discreteℕ k 2)
  ... |       yes q = is2 q
  ... |       no ¬q with (discreteℕ k 4)
  ... |             yes r = is4 r
  ... |             no ¬r = else (¬p , (¬q , ¬r))


  part0 : part 0 ≡ is0 refl
  part0 = refl

  part2 : part 2 ≡ is2 refl
  part2 = refl

  part4 : part 4 ≡ is4 refl
  part4 = refl


-----------------------------------------------------------------------------
-- Direct Sens on ℤ[x]

  ℤ[x,y]→H*-S²⋁S⁴ : ℤ[x,y] → H* S²⋁S⁴
  ℤ[x,y]→H*-S²⋁S⁴ = DS-Rec-Set.f _ _ _ _ isSetH*
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
                  ϕ (zero        ∷ one         ∷ []) a = base 4 (ϕ₄ a)
                  ϕ (zero        ∷ suc (suc m) ∷ []) a = 0H*
                  ϕ (one         ∷ zero        ∷ []) a = base 2 (ϕ₂ a)
                  ϕ (one         ∷ suc m       ∷ []) a = 0H*
                  ϕ (suc (suc n) ∷ m           ∷ []) a = 0H*

                  base-neutral-eq : _
                  base-neutral-eq (zero        ∷ zero        ∷ []) = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
                  base-neutral-eq (zero        ∷ one         ∷ []) = cong (base 4) (pres1 ϕ₄str) ∙ base-neutral _
                  base-neutral-eq (zero        ∷ suc (suc m) ∷ []) = refl
                  base-neutral-eq (one         ∷ zero        ∷ []) = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
                  base-neutral-eq (one         ∷ suc m       ∷ []) = refl
                  base-neutral-eq (suc (suc n) ∷ m           ∷ []) = refl

                  base-add-eq : _
                  base-add-eq (zero        ∷ zero        ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym (pres· ϕ₀str _ _))
                  base-add-eq (zero        ∷ one         ∷ []) a b = base-add _ _ _ ∙ cong (base 4) (sym (pres· ϕ₄str _ _))
                  base-add-eq (zero        ∷ suc (suc m) ∷ []) a b = +H*IdR _
                  base-add-eq (one         ∷ zero        ∷ []) a b = base-add _ _ _ ∙ cong (base 2) (sym (pres· ϕ₂str _ _))
                  base-add-eq (one         ∷ suc m       ∷ []) a b = +H*IdR _
                  base-add-eq (suc (suc n) ∷ m           ∷ []) a b = +H*IdR _

-----------------------------------------------------------------------------
-- Morphism on ℤ[x]

  ℤ[x,y]→H*-S²⋁S⁴-pres1Pℤ : ℤ[x,y]→H*-S²⋁S⁴ (1Pℤ) ≡ 1H*
  ℤ[x,y]→H*-S²⋁S⁴-pres1Pℤ = refl

  ℤ[x,y]→H*-S²⋁S⁴-pres+ : (x y : ℤ[x,y]) → ℤ[x,y]→H*-S²⋁S⁴ (x +Pℤ y) ≡ ℤ[x,y]→H*-S²⋁S⁴ x +H* ℤ[x,y]→H*-S²⋁S⁴ y
  ℤ[x,y]→H*-S²⋁S⁴-pres+ x y = refl

  --           Explanation of the product proof
  --
  --           -------------------------------------------------------
  --           | (0,0) | (0,1) | (0,m+2) | (1,0) | (1,m+1) | (n+2,m) |
  -- -----------------------------------------------------------------
  -- | (0,0)   |   H⁰  |   H⁰  |    0    |   H⁰  |    0    |    0    |
  -- -----------------------------------------------------------------
  -- | (0,1)   |  Sym  |   0₈  |    0    |   0₆  |    0    |    0    |
  -- -----------------------------------------------------------------
  -- | (0,m+2) | ==========================================> triv    |
  -- -----------------------------------------------------------------
  -- | (1,0)   |  Sym  |  Sym  |    0    |   ★  |    0    |    0    |
  -- -----------------------------------------------------------------
  -- | (1,m+1) | ==========================================> triv    |
  -- -----------------------------------------------------------------
  -- | (n+2,m) | ==========================================> triv    |
  -- -----------------------------------------------------------------

  -- ★ : prove that ϕ₂(1) ⌣ ϕ₂(1) ≡ 0 => ok because equiv H²(S²) and H⁴(S²) is trivial

  open pres⌣


  ϕ₀-gen : (n : ℕ) → (f : coHom n S²⋁S⁴) → ϕ₀ (pos 1) ⌣ f ≡ f
  ϕ₀-gen n = ST.elim (λ _ → isProp→isSet (GroupStr.is-set (snd (coHomGr n S²⋁S⁴)) _ _))
                     (λ f → cong ∣_∣₂ (funExt (λ x → rUnitₖ n (f x))))

  pres·-int : (n m : ℕ) → (a : ℤ) → (k l : ℕ) → (b : ℤ) →
                 ℤ[x,y]→H*-S²⋁S⁴ (base (n ∷ m ∷ []) a ·Pℤ base (k ∷ l ∷ []) b)
              ≡ ℤ[x,y]→H*-S²⋁S⁴ (base (n ∷ m ∷ []) a) cup ℤ[x,y]→H*-S²⋁S⁴ (base (k ∷ l ∷ []) b)

    -- non trivial case (0,0)
  pres·-int zero zero a zero zero          b = cong (base 0) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₀str _ ϕ₀str (ϕ₀-gen _ _) _ _)
  pres·-int zero zero a zero one           b = cong (base 4) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₄str _ ϕ₄str (ϕ₀-gen _ _) _ _)
  pres·-int zero zero a zero (suc (suc l)) b = refl
  pres·-int zero zero a one zero           b = cong (base 2) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₂str _ ϕ₂str (ϕ₀-gen _ _) _ _)
  pres·-int zero zero a one (suc l)        b = refl
  pres·-int zero zero a (suc (suc k)) l    b = refl
    -- non trivial case (0,1)
  pres·-int zero one a zero  zero         b = cong ℤ[x,y]→H*-S²⋁S⁴ (·PℤComm (base (0 ∷ 1 ∷ []) a) (base (0 ∷ 0 ∷ []) b))
                                              ∙ pres·-int 0 0 b 0 1 a
                                              ∙ gradCommRing S²⋁S⁴ _ _ _ _
  pres·-int zero one a zero  one          b = sym (base-neutral 8)
                                              ∙ cong (base 8) (trivialGroupEq (Hⁿ-S²⋁S⁴≅0 _) _ _)
  pres·-int zero one a zero (suc (suc l)) b = refl
  pres·-int zero one a one zero           b = sym (base-neutral 6)
                                              ∙ cong (base 6) (trivialGroupEq (Hⁿ-S²⋁S⁴≅0 _) _ _)
  pres·-int zero one a one (suc l)        b = refl
  pres·-int zero one a (suc (suc k)) l    b = refl
    -- trivial case (0, m+2)
  pres·-int zero (suc (suc m)) a  zero         l b = refl
  pres·-int zero (suc (suc m)) a  one          l b = refl
  pres·-int zero (suc (suc m)) a (suc (suc k)) l b = refl
    -- non trivial case (1,0)
  pres·-int one zero a zero zero          b = cong ℤ[x,y]→H*-S²⋁S⁴ (·PℤComm (base (1 ∷ 0 ∷ []) a) (base (0 ∷ 0 ∷ []) b))
                                              ∙ pres·-int 0 0 b 1 0 a
                                              ∙ gradCommRing S²⋁S⁴ _ _ _ _
  pres·-int one zero a zero one           b = cong ℤ[x,y]→H*-S²⋁S⁴ (·PℤComm (base (1 ∷ 0 ∷ []) a) (base (0 ∷ 1 ∷ []) b))
                                              ∙ pres·-int 0 1 b 1 0 a
                                              ∙ gradCommRing S²⋁S⁴ _ _ _ _
  pres·-int one zero a zero (suc (suc l)) b = refl
  pres·-int one zero a one zero           b = {!!}
  pres·-int one zero a one (suc l)        b = refl
  pres·-int one zero a (suc (suc k)) l    b = refl
    -- trivial case (1,m+1)
  pres·-int one (suc m) a  zero   l b = refl
  pres·-int one (suc m) a (suc k) l b = refl
    -- trivial case (n+2,m)
  pres·-int (suc (suc n)) m a k l b = refl


  pres·-base-case-vec : (v : Vec ℕ 2) → (a : ℤ) → (v' : Vec ℕ 2) → (b : ℤ) →
                           ℤ[x,y]→H*-S²⋁S⁴ (base v a ·Pℤ base v' b)
                        ≡ ℤ[x,y]→H*-S²⋁S⁴ (base v a) cup ℤ[x,y]→H*-S²⋁S⁴ (base v' b)
  pres·-base-case-vec (n ∷ m ∷ []) a (k ∷ l ∷ []) b = pres·-int n m a k l b

  -- proof of the morphism
  ℤ[x,y]→H*-S²⋁S⁴-pres· : (x y : ℤ[x,y]) → ℤ[x,y]→H*-S²⋁S⁴ (x ·Pℤ y) ≡ ℤ[x,y]→H*-S²⋁S⁴ x cup ℤ[x,y]→H*-S²⋁S⁴ y
  ℤ[x,y]→H*-S²⋁S⁴-pres· = DS-Ind-Prop.f _ _ _ _
                         (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                         (λ y → refl)
                         base-case
                         λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
    where
    base-case : _
    base-case v a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                           (sym (RingTheory.0RightAnnihilates (H*R S²⋁S⁴) _))
                           (λ v' b → pres·-base-case-vec v a v' b )
                           λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


-- -----------------------------------------------------------------------------
-- -- Function on ℤ[x]/x + morphism

--   -- not a trivial cancel
--   ℤ[x]→H*-RP²-cancelX : (x : Fin 2) → ℤ[x]→H*-RP² (<2X,X²> x) ≡ 0H*
--   ℤ[x]→H*-RP²-cancelX zero = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
--   ℤ[x]→H*-RP²-cancelX one = refl

--   ℤ[X]→H*-RP² : RingHom (CommRing→Ring ℤ[X]) (H*R RP²)
--   fst ℤ[X]→H*-RP² = ℤ[x]→H*-RP²
--   snd ℤ[X]→H*-RP² = makeIsRingHom ℤ[x]→H*-RP²-pres1Pℤ ℤ[x]→H*-RP²-pres+ ℤ[x]→H*-RP²-pres·

--   -- hence not a trivial pres+, yet pres0 still is
--   ℤ[X]/<2X,X²>→H*R-RP² : RingHom (CommRing→Ring ℤ[X]/<2X,X²>) (H*R RP²)
--   ℤ[X]/<2X,X²>→H*R-RP² =
--     Quotient-FGideal-CommRing-Ring.inducedHom ℤ[X] (H*R RP²) ℤ[X]→H*-RP² <2X,X²> ℤ[x]→H*-RP²-cancelX

--   ℤ[x]/<2x,x²>→H*-RP² : ℤ[x]/<2x,x²> → H* RP²
--   ℤ[x]/<2x,x²>→H*-RP² = fst ℤ[X]/<2X,X²>→H*R-RP²

--   ℤ[x]/<2x,x²>→H*-RP²-pres0 : ℤ[x]/<2x,x²>→H*-RP² 0PℤI ≡ 0H*
--   ℤ[x]/<2x,x²>→H*-RP²-pres0 = refl

--   ℤ[x]/<2x,x²>→H*-RP²-pres+ : (x y : ℤ[x]/<2x,x²>) → ℤ[x]/<2x,x²>→H*-RP² ( x +PℤI y) ≡ ℤ[x]/<2x,x²>→H*-RP² x +H* ℤ[x]/<2x,x²>→H*-RP² y
--   ℤ[x]/<2x,x²>→H*-RP²-pres+ x y = IsRingHom.pres+ (snd ℤ[X]/<2X,X²>→H*R-RP²) x y


-- -----------------------------------------------------------------------------
-- -- Converse Sens on ℤ[X] + ℤ[x]/x

--   -- Because ϕ⁻¹ are not morphism on there own
--   -- We need to define functions directly from H* to Z[X]/<2X, X³>

--   ψ₂⁻¹ : Bool → ℤ
--   ψ₂⁻¹ false = 1
--   ψ₂⁻¹ true = 0

--   private
--   -- Those lemma are requiered because ψ₂⁻¹
--   -- is a morphism only under the quotient
--     Λ : (x : Bool) → ℤ[x]/<2x,x²>
--     Λ x = [ (base (1 ∷ []) (ψ₂⁻¹ x)) ]

--     Λ-pres+ : (x y : Bool) → Λ x +PℤI Λ y ≡ Λ (x +Bool y)
--     Λ-pres+ false false = cong [_] (base-add _ _ _)
--                           ∙ eq/ (base (1 ∷ []) 2)
--                                 (base (1 ∷ []) 0)
--                                 ∣ ((λ {zero → base (0 ∷ []) 1 ; one → 0Pℤ}) , helper) ∣₁
--             where
--             helper : _
--             helper = base-add _ _ _
--                      ∙ sym (cong (λ X → ((base (1 ∷ []) 2) +Pℤ X)) (+PℤIdR _) ∙ +PℤIdR _)
--     Λ-pres+ false true = cong [_] (base-add _ _ _)
--     Λ-pres+ true false = cong [_] (base-add _ _ _)
--     Λ-pres+ true true = cong [_] (base-add _ _ _)


--   ϕ⁻¹ : (k : ℕ) → (a : coHom k RP²) → (x : partℕ k) → ℤ[x]/<2x,x²>
--   ϕ⁻¹ k a (is0 x) = [ (base (0 ∷ []) (ϕ₀⁻¹ (substG x a))) ]
--   ϕ⁻¹ k a (is2 x) = [ (base (1 ∷ []) ((ψ₂⁻¹ ∘ ϕ₂⁻¹) (substG x a))) ]
--   ϕ⁻¹ k a (else x) = 0PℤI

--   H*-RP²→ℤ[x]/<2x,x²> : H* RP² → ℤ[x]/<2x,x²>
--   H*-RP²→ℤ[x]/<2x,x²> = DS-Rec-Set.f _ _ _ _ isSetPℤI
--                         0PℤI
--                         (λ { k a → ϕ⁻¹ k a (part k)})
--                         _+PℤI_
--                         +PℤIAssoc
--                         +PℤIIdR
--                         +PℤIComm
--                         (λ k → base-neutral-eq k (part k))
--                         λ k a b → base-add-eq k a b (part k)
--        where
--        base-neutral-eq : (k : ℕ) → (x : partℕ k) → ϕ⁻¹ k (0ₕ k) x ≡ 0PℤI
--        base-neutral-eq k (is0 x) = cong [_] (cong (base {AGP = λ _ → snd ℤAG} (0 ∷ []))
--                                                   (cong ϕ₀⁻¹ (subst0g x) ∙ pres1 ϕ₀⁻¹str)
--                                             ∙ (base-neutral _))
--        base-neutral-eq k (is2 x) = cong [_] (cong (base (1 ∷ []))
--                                                   (cong (ψ₂⁻¹ ∘ ϕ₂⁻¹) (subst0g x)
--                                                   ∙ cong ψ₂⁻¹ (pres1 ϕ₂⁻¹str)) -- ψ₂⁻¹ pres1 by refl
--                                             ∙ base-neutral _)
--        base-neutral-eq k (else x) = refl

--        base-add-eq : (k : ℕ) → (a b : coHom k RP²) → (x : partℕ k) →
--                      (ϕ⁻¹ k a x) +PℤI (ϕ⁻¹ k b x) ≡ ϕ⁻¹ k (a +ₕ b) x
--        base-add-eq k a b (is0 x) = cong [_] (base-add _ _ _
--                                             ∙ cong (base (0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _) ∙ cong ϕ₀⁻¹ (subst+ _ _ _)))
--        base-add-eq k a b (is2 x) = Λ-pres+ (ϕ₂⁻¹ (substG x a)) (ϕ₂⁻¹ (substG x b))
--                                    ∙ cong [_] (cong (λ X → base {AGP = λ _ → snd ℤAG} (1 ∷ []) (ψ₂⁻¹ X))
--                                                     ((sym (pres· ϕ₂⁻¹str _ _) ∙ cong ϕ₂⁻¹ (subst+ _ _ _))))
--        base-add-eq k a b (else x) = +PℤIIdR _

--   H*-RP²→ℤ[x]/<2x,x²>-pres0 : H*-RP²→ℤ[x]/<2x,x²> 0H* ≡ 0PℤI
--   H*-RP²→ℤ[x]/<2x,x²>-pres0 = refl

--   H*-RP²→ℤ[x]/<2x,x²>-pres+ : (x y : H* RP²) → H*-RP²→ℤ[x]/<2x,x²> (x +H* y) ≡ (H*-RP²→ℤ[x]/<2x,x²> x) +PℤI (H*-RP²→ℤ[x]/<2x,x²> y)
--   H*-RP²→ℤ[x]/<2x,x²>-pres+ x y = refl



-- -----------------------------------------------------------------------------
-- -- Section

--   ψ₂-sect : (x : Bool) → ψ₂ (ψ₂⁻¹ x) ≡ x
--   ψ₂-sect false = refl
--   ψ₂-sect true = refl

--   e-sect-base : (k : ℕ) → (a : coHom k RP²) → (x : partℕ k) →
--                   ℤ[x]/<2x,x²>→H*-RP² (ϕ⁻¹ k a x) ≡ base k a
--   e-sect-base k a (is0 x) = cong (base 0) (ϕ₀-sect (substG x a))
--                             ∙ sym (constSubstCommSlice _ _ base x a)
--   e-sect-base k a (is2 x) = cong (base 2) (cong ϕ₂ (ψ₂-sect _) ∙ ϕ₂-sect _)
--                             ∙ sym (constSubstCommSlice _ _ base x a)
--   e-sect-base k a (else x) = sym (base-neutral k)
--                              ∙ cong (base k) (trivialGroupEq (Hⁿ-RP²≅0' k (fst x) (snd x)) _ _)

--   e-sect : (x : H* RP²) → ℤ[x]/<2x,x²>→H*-RP² (H*-RP²→ℤ[x]/<2x,x²> x) ≡ x
--   e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
--            refl
--            (λ k a → e-sect-base k a (part k))
--            λ {U V} ind-U ind-V → ℤ[x]/<2x,x²>→H*-RP²-pres+ _ _ ∙ cong₂ _+H*_ ind-U ind-V


-- -----------------------------------------------------------------------------
-- -- Retraction

--   -- could be prove for : k + 2·m
--   -- then call it with 0 and 1
--   e-retr-ψ₂-false : (a : ℤ) → (isEven a ≡ false) → Λ (ψ₂ a) ≡ [ base (1 ∷ []) a ]
--   e-retr-ψ₂-false a x = cong [_] (cong (base (1 ∷ [])) (cong ψ₂⁻¹ x))
--                   ∙ eq/ (base (1 ∷ []) 1) (base (1 ∷ []) a)
--                     ∣ ((λ {zero → base (0 ∷ []) (-ℤ m) ; one → 0Pℤ }) , helper) ∣₁
--             where
--             m = fst (isEvenFalse a x)

--             helper : _
--             helper = base-add _ _ _
--                      ∙ cong (base (1 ∷ [])) (cong (λ X → 1 +ℤ (-ℤ X)) (snd (isEvenFalse a x))
--                                              ∙ cong (λ X → 1 +ℤ X) (-Dist+ _ _)
--                                              ∙ +ℤAssoc _ _ _
--                                              ∙ +ℤIdL _)
--                      ∙ sym (cong (λ X → ((base (0 ∷ []) (-ℤ m)) ·Pℤ base (1 ∷ []) 2) +Pℤ X) (+PℤIdR _)
--                            ∙ +PℤIdR _
--                            ∙ cong (base (1 ∷ [])) (sym (-DistL· _ _) ∙ cong -ℤ_ (·ℤComm _ _)))

--   e-retr-ψ₂-true : (a : ℤ) → (isEven a ≡ true) → Λ (ψ₂ a) ≡ [ base (1 ∷ []) a ]
--   e-retr-ψ₂-true a x = cong [_] (cong (base (1 ∷ [])) (cong ψ₂⁻¹ x))
--                        ∙ eq/ (base (1 ∷ []) 0) (base (1 ∷ []) a)
--                        ∣ ((λ { zero → base (0 ∷ []) (-ℤ m) ; one → 0Pℤ }) , helper) ∣₁
--             where
--             m = fst (isEvenTrue a x)

--             helper : _
--             helper = base-add _ _ _
--                      ∙ cong (base (1 ∷ [])) (+ℤIdL _ ∙ cong -ℤ_ (snd (isEvenTrue a x) ∙ ·ℤComm 2 m))
--                      ∙ sym (cong (λ X → (base (0 ∷ []) (-ℤ m) ·Pℤ base (1 ∷ []) 2) +Pℤ X) (+PℤIdR _)
--                             ∙ +PℤIdR _
--                             ∙ cong (base (1 ∷ [])) (sym (-DistL· _ _)))


--   e-retr-ψ₂ : (a : ℤ) → ((isEven a ≡ false) ⊎ (isEven a ≡ true)) → Λ (ψ₂ a) ≡ [ base (1 ∷ []) a ]
--   e-retr-ψ₂ a (inl x) = e-retr-ψ₂-false a x
--   e-retr-ψ₂ a (inr x) = e-retr-ψ₂-true a x


--   e-retr-base : (k :  ℕ) → (a : ℤ) → H*-RP²→ℤ[x]/<2x,x²> (ℤ[x]/<2x,x²>→H*-RP² [ base (k ∷ []) a ]) ≡ [ base (k ∷ []) a ]
--   e-retr-base zero a = cong [_] (cong (base (zero ∷ []))
--                                 (cong ϕ₀⁻¹ (transportRefl (ϕ₀ a)) ∙ ϕ₀-retr a))
--   e-retr-base one a = cong [_] (cong (base (1 ∷ [])) (cong (ψ₂⁻¹ ∘ ϕ₂⁻¹) (transportRefl _)))
--                       ∙ cong [_] (cong (base (1 ∷ [])) (cong ψ₂⁻¹ (ϕ₂-retr (ψ₂ a))))
--                       ∙ e-retr-ψ₂ a (dichotomyBoolSym (isEven a))
--   e-retr-base (suc (suc k)) a = eq/ 0Pℤ (base ((suc (suc k)) ∷ []) a)
--                                 ∣ ((λ { zero → 0Pℤ ; one → base (k ∷ []) (-ℤ a) }) , helper) ∣₁
--               where
--               helper : _
--               helper = +PℤIdL _
--                        ∙ cong₂ base (cong (λ X → X ∷ []) (sym (+-comm k 2))) (sym (·ℤIdR _))
--                        ∙ sym (+PℤIdL _ ∙ +PℤIdR _ )

--   e-retr : (x : ℤ[x]/<2x,x²>) → H*-RP²→ℤ[x]/<2x,x²> (ℤ[x]/<2x,x²>→H*-RP² x) ≡ x
--   e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
--            (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
--            refl
--            (λ { (k ∷ []) a → e-retr-base k a})
--            λ {U V} ind-U ind-V → cong H*-RP²→ℤ[x]/<2x,x²> (ℤ[x]/<2x,x²>→H*-RP²-pres+ [ U ] [ V ])
--                                   ∙ cong₂ _+PℤI_ ind-U ind-V)


-- -----------------------------------------------------------------------------
-- -- Computation of the Cohomology Ring

-- module _ where

--   open Equiv-RP2-Properties

--   RP²-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X]/<2X,X²>) (H*R RP²)
--   fst RP²-CohomologyRing = isoToEquiv is
--     where
--     is : Iso ℤ[x]/<2x,x²> (H* RP²)
--     fun is = ℤ[x]/<2x,x²>→H*-RP²
--     inv is = H*-RP²→ℤ[x]/<2x,x²>
--     rightInv is = e-sect
--     leftInv is = e-retr
--   snd RP²-CohomologyRing = snd ℤ[X]/<2X,X²>→H*R-RP²

--   CohomologyRing-RP² : RingEquiv (H*R RP²) (CommRing→Ring ℤ[X]/<2X,X²>)
--   CohomologyRing-RP² = RingEquivs.invRingEquiv RP²-CohomologyRing
