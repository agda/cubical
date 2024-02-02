{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Experiments.ZariskiLatticeBasicOpens where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
-- open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties
open import Cubical.Algebra.CommAlgebra.Localisation
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Semilattice

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso
open BinaryRelation
open isEquivRel

private
  variable
    ℓ ℓ' : Level


module Presheaf (A' : CommRing ℓ) where
 open CommRingStr (snd A') renaming (_·_ to _·r_ ; ·Comm to ·r-comm ; ·Assoc to ·rAssoc
                                                 ; ·IdL to ·rLid ; ·IdR to ·rRid)
 open Exponentiation A'
 open CommRingTheory A'
 open InvertingElementsBase A'
 open isMultClosedSubset
 open CommAlgebraStr ⦃...⦄
 private
  A = fst A'

  A[1/_] : A → CommAlgebra A' ℓ
  A[1/ x ] = AlgLoc.S⁻¹RAsCommAlg A' [ x ⁿ|n≥0] (powersFormMultClosedSubset _)

  A[1/_]ˣ : (x : A) → ℙ (fst A[1/ x ])
  A[1/ x ]ˣ = (CommAlgebra→CommRing A[1/ x ]) ˣ


 _≼_ : A → A → Type ℓ
 x ≼ y = ∃[ n ∈ ℕ ] Σ[ z ∈ A ] x ^ n ≡ z ·r y -- rad(x) ⊆ rad(y)

-- ≼ is a pre-order:
 Refl≼ : isRefl _≼_
 Refl≼ x = PT.∣ 1 , 1r , ·r-comm _ _ ∣₁

 Trans≼ : isTrans _≼_
 Trans≼ x y z = map2 Trans≼Σ
  where
  Trans≼Σ : Σ[ n ∈ ℕ ] Σ[ a ∈ A ] x ^ n ≡ a ·r y
          → Σ[ n ∈ ℕ ] Σ[ a ∈ A ] y ^ n ≡ a ·r z
          → Σ[ n ∈ ℕ ] Σ[ a ∈ A ] x ^ n ≡ a ·r z
  Trans≼Σ (n , a , p) (m , b , q) = n ·ℕ m , (a ^ m ·r b) , path
   where
   path : x ^ (n ·ℕ m) ≡ a ^ m ·r b ·r z
   path = x ^ (n ·ℕ m)    ≡⟨ ^-rdist-·ℕ x n m ⟩
          (x ^ n) ^ m     ≡⟨ cong (_^ m) p ⟩
          (a ·r y) ^ m     ≡⟨ ^-ldist-· a y m ⟩
          a ^ m ·r y ^ m   ≡⟨ cong (a ^ m ·r_) q ⟩
          a ^ m ·r (b ·r z) ≡⟨ ·rAssoc _ _ _ ⟩
          a ^ m ·r b ·r z   ∎


 R : A → A → Type ℓ
 R x y = x ≼ y × y ≼ x -- rad(x) ≡ rad(y)

 RequivRel : isEquivRel R
 RequivRel .reflexive x = Refl≼ x , Refl≼ x
 RequivRel .symmetric _ _ Rxy = (Rxy .snd) , (Rxy .fst)
 RequivRel .transitive _ _ _ Rxy Ryz = Trans≼ _ _ _ (Rxy .fst) (Ryz .fst)
                                     , Trans≼ _ _ _  (Ryz .snd) (Rxy .snd)

 RpropValued : isPropValued R
 RpropValued x y = isProp× isPropPropTrunc isPropPropTrunc

 powerIs≽ : (x a : A) → x ∈ [ a ⁿ|n≥0] → a ≼ x
 powerIs≽ x a = map powerIs≽Σ
  where
  powerIs≽Σ : Σ[ n ∈ ℕ ] (x ≡ a ^ n) → Σ[ n ∈ ℕ ] Σ[ z ∈ A ] (a ^ n ≡ z ·r x)
  powerIs≽Σ (n , p) = n , 1r , sym p ∙ sym (·rLid _)

 module ≼ToLoc (x y : A) where
  private
   instance
    _ = snd A[1/ x ]

  lemma : x ≼ y → y ⋆ 1a ∈ A[1/ x ]ˣ -- y/1 ∈ A[1/x]ˣ
  lemma = PT.rec (A[1/ x ]ˣ (y ⋆ 1a) .snd) lemmaΣ
   where
   path1 : (y z : A) → 1r ·r (y ·r 1r ·r z) ·r 1r ≡ z ·r y
   path1 _ _ = solve! A'
   path2 : (xn : A) → xn ≡ 1r ·r 1r ·r (1r ·r 1r ·r xn)
   path2 _ = solve! A'

   lemmaΣ : Σ[ n ∈ ℕ ] Σ[ a ∈ A ] x ^ n ≡ a ·r y → y ⋆ 1a ∈ A[1/ x ]ˣ
   lemmaΣ (n , z , p) = [ z , (x ^ n) ,  PT.∣ n , refl ∣₁ ] -- xⁿ≡zy → y⁻¹ ≡ z/xⁿ
                      , eq/ _ _ ((1r , powersFormMultClosedSubset _ .containsOne)
                      , (path1 _ _ ∙∙ sym p ∙∙ path2 _))

 module ≼PowerToLoc (x y : A) (x≼y : x ≼ y) where
  private
   [yⁿ|n≥0] = [ y ⁿ|n≥0]
   instance
    _ = snd A[1/ x ]
  lemma : ∀ (s : A) → s ∈ [yⁿ|n≥0] → s ⋆ 1a ∈ A[1/ x ]ˣ
  lemma _ s∈[yⁿ|n≥0] = ≼ToLoc.lemma _ _ (Trans≼ _ y _ x≼y (powerIs≽ _ _ s∈[yⁿ|n≥0]))



 𝓞ᴰ : A / R → CommAlgebra A' ℓ
 𝓞ᴰ = rec→Gpd.fun isGroupoidCommAlgebra (λ a → A[1/ a ]) RCoh LocPathProp
    where
    RCoh : ∀ a b → R a b → A[1/ a ] ≡ A[1/ b ]
    RCoh a b (a≼b , b≼a) = fst (isContrS₁⁻¹R≡S₂⁻¹R (≼PowerToLoc.lemma _ _ b≼a)
                                                   (≼PowerToLoc.lemma _ _ a≼b))
     where
     open AlgLocTwoSubsets A' [ a ⁿ|n≥0] (powersFormMultClosedSubset _)
                              [ b ⁿ|n≥0] (powersFormMultClosedSubset _)

    LocPathProp : ∀ a b → isProp (A[1/ a ] ≡ A[1/ b ])
    LocPathProp a b = isPropS₁⁻¹R≡S₂⁻¹R
     where
     open AlgLocTwoSubsets A' [ a ⁿ|n≥0] (powersFormMultClosedSubset _)
                              [ b ⁿ|n≥0] (powersFormMultClosedSubset _)


 -- The quotient A/R corresponds to the basic opens of the Zariski topology.
 -- Multiplication lifts to the quotient and corresponds to intersection
 -- of basic opens, i.e. we get a meet-semilattice with:
 _∧/_ : A / R → A / R → A / R
 _∧/_ = setQuotSymmBinOp (RequivRel .reflexive) (RequivRel .transitive) _·r_
          (λ a b → subst (λ x → R (a ·r b) x) (·r-comm a b) (RequivRel .reflexive (a ·r b))) ·r-lcoh
  where
  ·r-lcoh-≼ : (x y z : A) → x ≼ y → (x ·r z) ≼ (y ·r z)
  ·r-lcoh-≼ x y z = map ·r-lcoh-≼Σ
   where
   path : (x z a y zn : A) →  x ·r z ·r (a ·r y ·r zn) ≡ x ·r zn ·r a ·r (y ·r z)
   path _ _ _ _ _ = solve! A'

   ·r-lcoh-≼Σ : Σ[ n ∈ ℕ ] Σ[ a ∈ A ] x ^ n ≡ a ·r y
              → Σ[ n ∈ ℕ ] Σ[ a ∈ A ] (x ·r z) ^ n ≡ a ·r (y ·r z)
   ·r-lcoh-≼Σ  (n , a , p) = suc n , (x ·r z ^ n ·r a) , (cong (x ·r z ·r_) (^-ldist-· _ _ _)
                                                       ∙∙ cong (λ v → x ·r z ·r (v ·r z ^ n)) p
                                                       ∙∙ path _ _ _ _ _)

  ·r-lcoh : (x y z : A) → R x y → R (x ·r z) (y ·r z)
  ·r-lcoh x y z Rxy = ·r-lcoh-≼ x y z (Rxy .fst) , ·r-lcoh-≼ y x z (Rxy .snd)
{-
 BasicOpens : Semilattice ℓ
 BasicOpens = makeSemilattice [ 1r ] _∧/_ squash/
   (elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → cong [_] (·rAssoc _ _ _))
     (elimProp (λ _ → squash/ _ _) λ _ → cong [_] (·rRid _))
       (elimProp (λ _ → squash/ _ _) λ _ → cong [_] (·rLid _))
         (elimProp2 (λ _ _ → squash/ _ _) λ _ _ → cong [_] (·r-comm _ _))
           (elimProp (λ _ → squash/ _ _) λ a → eq/ _ _ -- R a a²
              (∣ 1 , a , ·rRid _ ∣ , ∣ 2 , 1r , cong (a ·r_) (·rRid a) ∙ sym (·rLid _) ∣))

 -- The induced partial order
 open MeetSemilattice BasicOpens renaming (_≤_ to _≼/_ ; IndPoset to BasicOpensAsPoset)

 -- coincides with our ≼
 ≼/CoincidesWith≼ : ∀ (x y : A) → ([ x ] ≼/ [ y ]) ≡ (x ≼ y)
 ≼/CoincidesWith≼ x y = [ x ] ≼/ [ y ] -- ≡⟨ refl ⟩ [ x ·r y ] ≡ [ x ]
                      ≡⟨ isoToPath (isEquivRel→effectiveIso RpropValued RequivRel _ _) ⟩
                        R (x ·r y) x
                      ≡⟨ isoToPath Σ-swap-Iso ⟩
                        R x (x ·r y)
                      ≡⟨ hPropExt (RpropValued _ _) isPropPropTrunc ·To≼ ≼To· ⟩
                        x ≼ y ∎
  where
  x≼xy→x≼yΣ : Σ[ n ∈ ℕ ] Σ[ z ∈ A ] x ^ n ≡ z ·r (x ·r y)
            → Σ[ n ∈ ℕ ] Σ[ z ∈ A ] x ^ n ≡ z ·r y
  x≼xy→x≼yΣ (n , z , p) =  n , (z ·r x) , p ∙ ·rAssoc _ _ _

  ·To≼ : R x (x ·r y) → x ≼ y
  ·To≼ (x≼xy , _) = PT.map x≼xy→x≼yΣ x≼xy

  x≼y→x≼xyΣ : Σ[ n ∈ ℕ ] Σ[ z ∈ A ] x ^ n ≡ z ·r y
            → Σ[ n ∈ ℕ ] Σ[ z ∈ A ] x ^ n ≡ z ·r (x ·r y)
  x≼y→x≼xyΣ (n , z , p) = suc n , z , cong (x ·r_) p ∙ ·CommAssocl _ _ _

  ≼To· : x ≼ y → R x ( x ·r y)
  ≼To· x≼y = PT.map x≼y→x≼xyΣ x≼y , PT.∣ 1 , y , ·rRid _ ∙ ·r-comm _ _ ∣₁

 open IsPoset
 open PosetStr
 Refl≼/ : isRefl _≼/_
 Refl≼/ = BasicOpensAsPoset .snd .isPoset .is-refl

 Trans≼/ : isTrans _≼/_
 Trans≼/ = BasicOpensAsPoset .snd .isPoset .is-trans

 -- The restrictions:
 ρᴰᴬ : (a b : A) → a ≼ b → isContr (CommAlgebraHom A[1/ b ] A[1/ a ])
 ρᴰᴬ _ b a≼b = A[1/b]HasUniversalProp _ (≼PowerToLoc.lemma _ _ a≼b)
  where
  open AlgLoc A' [ b ⁿ|n≥0] (powersFormMultClosedSubset _)
       renaming (S⁻¹RHasAlgUniversalProp to A[1/b]HasUniversalProp)

 ρᴰᴬId : ∀ (a : A) (r : a ≼ a) → ρᴰᴬ a a r .fst ≡ idAlgHom
 ρᴰᴬId a r = ρᴰᴬ a a r .snd _

 ρᴰᴬComp : ∀ (a b c : A) (l : a ≼ b) (m : b ≼ c)
         → ρᴰᴬ a c (Trans≼ _ _ _ l m) .fst ≡ ρᴰᴬ a b l .fst ∘a ρᴰᴬ b c m .fst
 ρᴰᴬComp a _ c l m = ρᴰᴬ a c (Trans≼ _ _ _ l m) .snd _


 ρᴰ : (x y : A / R) → x ≼/ y → CommAlgebraHom (𝓞ᴰ y) (𝓞ᴰ x)
 ρᴰ = elimContr2 λ _ _ → isContrΠ
                 λ [a]≼/[b] → ρᴰᴬ _ _ (transport (≼/CoincidesWith≼ _ _) [a]≼/[b])

 ρᴰId : ∀ (x : A / R) (r : x ≼/ x) → ρᴰ x x r ≡ idAlgHom
 ρᴰId = SQ.elimProp (λ _ → isPropΠ (λ _ → isSetAlgebraHom _ _ _ _))
                     λ a r → ρᴰᴬId  a (transport (≼/CoincidesWith≼ _ _) r)

 ρᴰComp : ∀ (x y z : A / R) (l : x ≼/ y) (m : y ≼/ z)
        → ρᴰ x z (Trans≼/ _ _ _ l m) ≡ ρᴰ x y l ∘a ρᴰ y z m
 ρᴰComp = SQ.elimProp3 (λ _ _ _ → isPropΠ2 (λ _ _ → isSetAlgebraHom _ _ _ _))
                        λ a b c _ _ → sym (ρᴰᴬ a c _ .snd _) ∙ ρᴰᴬComp a b c _ _
-}
