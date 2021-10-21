{-
  This is mostly for convenience, when working with ideals
  (which are defined for general rings) in a commutative ring.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Functions.Logic

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; tt)
                             renaming ( --zero to ℕzero ; suc to ℕsuc
                                        _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-assoc to +ℕ-assoc ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)

open import Cubical.Data.FinData hiding (rec ; elim)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal renaming (IdealsIn to IdealsInRing)
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

IdealsIn : (R : CommRing ℓ) → Type _
IdealsIn R = IdealsInRing (CommRing→Ring R)

module _ (Ring@(R , str) : CommRing ℓ) where
  open CommRingStr str
  makeIdeal : (I : R → hProp ℓ)
              → (+-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I)
              → (0r-closed : 0r ∈ I)
              → (·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I)
              → IdealsIn (R , str)
  makeIdeal I +-closed 0r-closed ·-closedLeft = I ,
    (record
       { +-closed = +-closed
       ; -closed = λ x∈I → subst-∈ I (useSolver _)
                             (·-closedLeft (- 1r) x∈I)
       ; 0r-closed = 0r-closed
       ; ·-closedLeft = ·-closedLeft
       ; ·-closedRight = λ r x∈I →
                       subst-∈ I
                             (·-comm r _)
                             (·-closedLeft r x∈I)
       })
       where useSolver : (x : R) → - 1r · x ≡ - x
             useSolver = solve Ring


-- better?
module CommIdeal (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R')
 open Sum (CommRing→Ring R')
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')

 record isCommIdeal (I : ℙ R) : Type ℓ where
  constructor
   makeIsCommIdeal
  field
   +Closed : ∀ {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
   contains0 : 0r ∈ I
   ·Closed : ∀ {x : R} (r : R) → x ∈ I → r · x ∈ I

  ·RClosed :  ∀ {x : R} (r : R) → x ∈ I → x · r ∈ I
  ·RClosed r x∈I = subst-∈ I (·-comm _ _) (·Closed r x∈I)

 open isCommIdeal
 isPropIsCommIdeal : (I : ℙ R) → isProp (isCommIdeal I)
 +Closed (isPropIsCommIdeal I ici₁ ici₂ i) x∈I y∈I =
         I _ .snd (ici₁ .+Closed x∈I y∈I) (ici₂ .+Closed x∈I y∈I) i
 contains0 (isPropIsCommIdeal I ici₁ ici₂ i) = I 0r .snd (ici₁ .contains0) (ici₂ .contains0) i
 ·Closed (isPropIsCommIdeal I ici₁ ici₂ i) r x∈I =
         I _ .snd (ici₁ .·Closed r x∈I) (ici₂ .·Closed r x∈I) i

 CommIdeal : Type _
 CommIdeal = Σ[ I ∈ ℙ R ] isCommIdeal I

 CommIdeal≡Char : {I J : CommIdeal} → (I .fst ⊆ J .fst) → (J .fst ⊆ I .fst) → I ≡ J
 CommIdeal≡Char I⊆J J⊆I = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (I⊆J , J⊆I))

 ∑Closed : (I : CommIdeal) {n : ℕ} (V : FinVec R n)
         → (∀ i → V i ∈ fst I) → ∑ V ∈ fst I
 ∑Closed I {n = zero} _ _ = I .snd .contains0
 ∑Closed I {n = suc n} V h = I .snd .+Closed (h zero) (∑Closed I (V ∘ suc) (h ∘ suc))

 0Ideal : CommIdeal
 fst 0Ideal x = (x ≡ 0r) , is-set _ _
 +Closed (snd 0Ideal) x≡0 y≡0 = cong₂ (_+_) x≡0 y≡0 ∙ +Rid _
 contains0 (snd 0Ideal) = refl
 ·Closed (snd 0Ideal) r x≡0 = cong (r ·_) x≡0 ∙ 0RightAnnihilates _

 1Ideal : CommIdeal
 fst 1Ideal x = ⊤
 +Closed (snd 1Ideal) _ _ = lift tt
 contains0 (snd 1Ideal) = lift tt
 ·Closed (snd 1Ideal) _ _ = lift tt

 contains1Is1 : (I : CommIdeal) → 1r ∈ I .fst → I ≡ 1Ideal
 contains1Is1 I 1∈I = CommIdeal≡Char (λ _ _ → lift tt)
   λ x _ → subst-∈ (I .fst) (·Rid _) (I .snd .·Closed x 1∈I) -- x≡x·1 ∈ I

 _+i_ : CommIdeal → CommIdeal → CommIdeal
 fst (I +i J) x =
     (∃[ (y , z) ∈ (R × R) ] ((y ∈ I .fst) × (z ∈ J .fst) × (x ≡ y + z))) --have a record for this?
     , isPropPropTrunc
 +Closed (snd (I +i J)) {x = x₁} {y = x₂} = map2 +ClosedΣ
  where
  +ClosedΣ : Σ[ (y₁ , z₁) ∈ (R × R) ] ((y₁ ∈ I .fst) × (z₁ ∈ J .fst) × (x₁ ≡ y₁ + z₁))
           → Σ[ (y₂ , z₂) ∈ (R × R) ] ((y₂ ∈ I .fst) × (z₂ ∈ J .fst) × (x₂ ≡ y₂ + z₂))
           → Σ[ (y₃ , z₃) ∈ (R × R) ] ((y₃ ∈ I .fst) × (z₃ ∈ J .fst) × (x₁ + x₂ ≡ y₃ + z₃))
  +ClosedΣ ((y₁ , z₁) , y₁∈I , z₁∈J , x₁≡y₁+z₁) ((y₂ , z₂) , y₂∈I , z₂∈J , x₂≡y₂+z₂) =
    (y₁ + y₂ , z₁ + z₂) , +Closed (snd I) y₁∈I y₂∈I , +Closed (snd J) z₁∈J z₂∈J
                      , cong₂ (_+_) x₁≡y₁+z₁ x₂≡y₂+z₂ ∙ +ShufflePairs _ _ _ _
 contains0 (snd (I +i J)) = ∣ (0r , 0r) , contains0 (snd I) , contains0 (snd J) , sym (+Rid _) ∣
 ·Closed (snd (I +i J)) {x = x} r = map ·ClosedΣ
  where
  ·ClosedΣ : Σ[ (y₁ , z₁) ∈ (R × R) ] ((y₁ ∈ I .fst) × (z₁ ∈ J .fst) × (x ≡ y₁ + z₁))
           → Σ[ (y₂ , z₂) ∈ (R × R) ] ((y₂ ∈ I .fst) × (z₂ ∈ J .fst) × (r · x ≡ y₂ + z₂))
  ·ClosedΣ ((y₁ , z₁) , y₁∈I , z₁∈J , x≡y₁+z₁) =
    (r · y₁ , r · z₁) , ·Closed (snd I) r y₁∈I , ·Closed (snd J) r z₁∈J
                     , cong (r ·_) x≡y₁+z₁ ∙ ·Rdist+ _ _ _

 infixl 6 _+i_

 +iComm⊆ : ∀ (I J : CommIdeal) → (I +i J) .fst ⊆ (J +i I) .fst
 +iComm⊆ I J x = map λ ((y , z) , y∈I , z∈J , x≡y+z) → (z , y) , z∈J , y∈I , x≡y+z ∙ +Comm _ _

 +iComm : ∀ (I J : CommIdeal) → I +i J ≡ J +i I
 +iComm I J = CommIdeal≡Char (+iComm⊆ I J)  (+iComm⊆ J I)

 +iLid : ∀ (I : CommIdeal) → 0Ideal +i I ≡ I
 +iLid I = CommIdeal≡Char incl1 incl2
  where
  incl1 : (0Ideal +i I) .fst ⊆ I .fst
  incl1 x = rec (I .fst x .snd) λ ((y , z) , y≡0 , z∈I , x≡y+z)
                                  → subst-∈ (fst I) (sym (x≡y+z ∙∙ cong (_+ z) y≡0 ∙∙ +Lid z)) z∈I

  incl2 : I .fst ⊆ (0Ideal +i I) .fst
  incl2 x x∈I = ∣ (0r , x) , refl , x∈I , sym (+Lid _) ∣

 +iLincl : ∀ (I J : CommIdeal) → I .fst ⊆ (I +i J) .fst
 +iLincl I J x x∈I = ∣ (x , 0r) , x∈I , J .snd .contains0 , sym (+Rid x) ∣

 +iRincl : ∀ (I J : CommIdeal) → J .fst ⊆ (I +i J) .fst
 +iRincl I J x x∈J = ∣ (0r , x) , I .snd .contains0 , x∈J ,  sym (+Lid x) ∣

 +iRespLincl : ∀ (I J K : CommIdeal) → I .fst ⊆ J .fst → (I +i K) .fst ⊆ (J +i K) .fst
 +iRespLincl I J K I⊆J x = map λ ((y , z) , y∈I , z∈K , x≡y+z) → ((y , z) , I⊆J y y∈I , z∈K , x≡y+z)

 +iAssoc : ∀ (I J K : CommIdeal) → I +i (J +i K) ≡ (I +i J) +i K
 +iAssoc I J K = CommIdeal≡Char incl1 incl2
  where
  incl1 : (I +i (J +i K)) .fst ⊆ ((I +i J) +i K) .fst
  incl1 x = elim (λ _ → ((I +i J) +i K) .fst x .snd) (uncurry3
            λ (y , z) y∈I → elim (λ _ → isPropΠ λ _ → ((I +i J) +i K) .fst x .snd)
              λ ((u , v) , u∈J , v∈K , z≡u+v) x≡y+z
                → ∣ (y + u , v) , ∣ _ , y∈I , u∈J , refl ∣ , v∈K
                                 , x≡y+z ∙∙ cong (y +_) z≡u+v ∙∙ +Assoc _ _ _ ∣)
  incl2 : ((I +i J) +i K) .fst ⊆ (I +i (J +i K)) .fst
  incl2 x = elim (λ _ → (I +i (J +i K)) .fst x .snd) (uncurry3
            λ (y , z) → elim (λ _ → isPropΠ2 λ _ _ → (I +i (J +i K)) .fst x .snd)
              λ ((u , v) , u∈I , v∈J , y≡u+v) z∈K x≡y+z
                → ∣ (u , v + z) , u∈I , ∣ _ , v∈J , z∈K , refl ∣
                                       , x≡y+z ∙∙ cong (_+ z) y≡u+v ∙∙ sym (+Assoc _ _ _) ∣)

 +iIdem : ∀ (I : CommIdeal) → I +i I ≡ I
 +iIdem I = CommIdeal≡Char incl1 incl2
  where
  incl1 : (I +i I) .fst ⊆ I .fst
  incl1 x = rec (I .fst x .snd) λ ((y , z) , y∈I , z∈I , x≡y+z)
                                  → subst-∈ (I .fst) (sym x≡y+z) (I .snd .+Closed y∈I z∈I)

  incl2 : I .fst ⊆ (I +i I) .fst
  incl2 x x∈I = ∣ (0r , x) , I .snd .contains0 , x∈I , sym (+Lid _) ∣


 -- where to put this?
 mul++dist : ∀ {n m : ℕ} (α U : FinVec R n) (β V : FinVec R m) (j : Fin (n +ℕ m))
            → ((λ i → α i · U i) ++Fin (λ i → β i · V i)) j ≡ (α ++Fin β) j · (U ++Fin V) j
 mul++dist {n = zero} α U β V j = refl
 mul++dist {n = suc n} α U β V zero = refl
 mul++dist {n = suc n} α U β V (suc j) = mul++dist (α ∘ suc) (U ∘ suc) β V j

 -- define multiplication of ideals
 _·i_ : CommIdeal → CommIdeal → CommIdeal
 fst (I ·i J) x = (∃[ n ∈ ℕ ] Σ[ (α , β) ∈ (FinVec R n × FinVec R n) ]
                   (∀ i → α i ∈ I .fst) × (∀ i → β i ∈ J .fst) × (x ≡ ∑ λ i → α i · β i))
                    , isPropPropTrunc
 +Closed (snd (I ·i J)) = map2
  λ (n , (α , β) , ∀αi∈I , ∀βi∈J , x≡∑αβ) (m , (γ , δ) , ∀γi∈I , ∀δi∈J , y≡∑γδ)
   → n +ℕ m , (α ++Fin γ , β ++Fin δ) , ++FinPres∈ (I .fst) ∀αi∈I ∀γi∈I
                                      , ++FinPres∈ (J .fst) ∀βi∈J ∀δi∈J
    , cong₂ (_+_) x≡∑αβ y≡∑γδ ∙∙ sym (∑Split++ (λ i → α i · β i) (λ i → γ i · δ i))
                              ∙∙ ∑Ext (mul++dist α β γ δ)
 contains0 (snd (I ·i J)) = ∣ 0 , ((λ ()) , (λ ())) , (λ ()) , (λ ()) , refl ∣
 ·Closed (snd (I ·i J)) r = map
  λ (n , (α , β) , ∀αi∈I , ∀βi∈J , x≡∑αβ)
   → n , ((λ i → r · α i) , β) , (λ i → I .snd .·Closed r (∀αi∈I i)) , ∀βi∈J
    , cong (r ·_) x≡∑αβ ∙ ∑Mulrdist r (λ i → α i · β i) ∙ ∑Ext λ i → ·Assoc r (α i) (β i)

 infixl 7 _·i_

 prodInProd : ∀ (I J : CommIdeal) (x y : R) → x ∈ I .fst → y ∈ J .fst → (x · y) ∈ (I ·i J) .fst
 prodInProd _ _ x y x∈I y∈J =
            ∣ 1 , ((λ _ → x) , λ _ → y) , (λ _ → x∈I) , (λ _ → y∈J) , sym (+Rid _) ∣

 -- a non-dep version that works?
 -- ·iElim : {I J : CommIdeal} {P : (x : R) → x ∈ (I ·i J) .fst → Type ℓ}
 --        → (∀ x x∈IJ → isProp (P x x∈IJ))
 --        → (∀ x y x∈I y∈J → P (x · y) (prodInProd I J x y x∈I y∈J))
 --        ---------------------------------------------------------
 --        → ∀ x x∈IJ → P x x∈IJ
 -- ·iElim {I = I} {J = J} {P = P} isPropP h x = elim (isPropP x) λ (_ , (α , β) , α∈I , β∈J , x≡∑αβ)
 --                    → subst (λ x → (x∈IJ : x ∈ (I ·i J) .fst) → P x x∈IJ) (sym x≡∑αβ) {!!} {!!}

 ·iLincl : ∀ (I J : CommIdeal) → (I ·i J) .fst ⊆ I .fst
 ·iLincl I J x = elim (λ _ → I .fst x .snd)
   λ (_ , (α , β) , α∈I , _ , x≡∑αβ) → subst-∈ (I .fst) (sym x≡∑αβ)
                                     (∑Closed I (λ i → α i · β i) λ i → ·RClosed (I .snd) _ (α∈I i))

 ·iComm⊆ : ∀ (I J : CommIdeal) → (I ·i J) .fst ⊆ (J ·i I) .fst
 ·iComm⊆ I J x = map λ (n , (α , β) , ∀αi∈I , ∀βi∈J , x≡∑αβ)
                      → (n , (β , α) , ∀βi∈J , ∀αi∈I , x≡∑αβ ∙ ∑Ext (λ i → ·-comm (α i) (β i)))

 ·iComm : ∀ (I J : CommIdeal) → I ·i J ≡ J ·i I
 ·iComm I J = CommIdeal≡Char (·iComm⊆ I J) (·iComm⊆ J I)

 ·iRid : ∀ (I : CommIdeal) → I ·i 1Ideal ≡ I
 ·iRid I = CommIdeal≡Char (·iLincl I 1Ideal) I1⊆I
  where
  useSolver : ∀ x → x ≡ x · 1r + 0r
  useSolver = solve R'

  I1⊆I : I .fst ⊆ (I ·i 1Ideal) .fst
  I1⊆I x x∈I = ∣ 1 , ((λ _ → x) , λ _ → 1r) , (λ _ → x∈I) , (λ _ → lift tt) , useSolver x ∣

 -- a useful corollary
 ·iRContains1id : ∀ (I J : CommIdeal) → 1r ∈ J .fst → I ·i J ≡ I
 ·iRContains1id I J 1∈J = cong (I ·i_) (contains1Is1 J 1∈J) ∙ ·iRid I

 ·iAssoc : ∀ (I J K : CommIdeal) → I ·i (J ·i K) ≡ (I ·i J) ·i K
 ·iAssoc I J K = CommIdeal≡Char incl1 incl2
  where
  incl1 : (I ·i (J ·i K)) .fst ⊆ ((I ·i J) ·i K) .fst
  incl1 x = rec isPropPropTrunc
          λ (_ , (α , β) , α∈I , β∈JK , x≡∑αβ)
              → subst-∈ (((I ·i J) ·i K) .fst) (sym x≡∑αβ)
                (∑Closed ((I ·i J) ·i K) (λ i → α i · β i)
          λ i → rec isPropPropTrunc
                (λ (_ , (γ , δ) , γ∈J , δ∈K , βi≡∑γδ)
                   → subst-∈ (((I ·i J) ·i K) .fst) -- each αᵢβᵢ ≡...≡ ∑αᵢγⱼδⱼ ∈IJK
                              (sym (cong (α i ·_) βi≡∑γδ ∙∙ ∑Mulrdist (α i) (λ j → γ j · δ j)
                                                         ∙∙ ∑Ext (λ j → ·Assoc (α i) (γ j) (δ j))))
                              (∑Closed ((I ·i J) ·i K) (λ j → α i · γ j · δ j) -- each αᵢγⱼδⱼ∈IJK
                                       λ j → prodInProd (I ·i J) K _ _
                                               (prodInProd I J _ _ (α∈I i) (γ∈J j)) (δ∈K j)))
                (β∈JK i))

  incl2 : ((I ·i J) ·i K) .fst ⊆ (I ·i (J ·i K)) .fst
  incl2 x = rec isPropPropTrunc
          λ (_ , (α , β) , α∈IJ , β∈K , x≡∑αβ)
              → subst-∈ ((I ·i (J ·i K)) .fst) (sym x≡∑αβ)
                (∑Closed (I ·i (J ·i K)) (λ i → α i · β i)
          λ i → rec isPropPropTrunc
                (λ (_ , (γ , δ) , γ∈I , δ∈J , αi≡∑γδ)
                   → subst-∈ ((I ·i (J ·i K)) .fst)
                              (sym (cong (_· β i) αi≡∑γδ ∙∙ ∑Mulldist (β i) (λ j → γ j · δ j)
                                         ∙∙ ∑Ext (λ j → sym (·Assoc (γ j) (δ j) (β i)))))
                              (∑Closed (I ·i (J ·i K)) (λ j → γ j · (δ j · β i))
                                       λ j → prodInProd I (J ·i K) _ _ (γ∈I j)
                                               (prodInProd J K _ _ (δ∈J j) (β∈K i))))
                (α∈IJ i))

 ·iRdist+i : ∀ (I J K : CommIdeal) → I ·i (J +i K) ≡ I ·i J +i I ·i K
 ·iRdist+i I J K = CommIdeal≡Char incl1 incl2
  where
  incl1 : (I ·i (J +i K)) .fst ⊆ (I ·i J +i I ·i K) .fst
  incl1 x = rec isPropPropTrunc
    λ (n , (α , β) , α∈I , β∈J+K , x≡∑αβ) → subst-∈ (((I ·i J) +i (I ·i K)) .fst) (sym x≡∑αβ)
      (∑Closed ((I ·i J) +i (I ·i K)) (λ i → α i · β i) -- each αi·βi ∈ IJ+IK
      λ i → rec isPropPropTrunc
            (λ ((γi , δi) , γi∈J , δi∈K , βi≡γi+δi) →
               ∣ (α i · γi , α i · δi) , prodInProd I J _ _ (α∈I i) γi∈J
                                       , prodInProd I K _ _ (α∈I i) δi∈K
                                       , cong (α i ·_) βi≡γi+δi ∙ ·Rdist+ _ _ _ ∣)
            (β∈J+K i))

  incl2 : ((I ·i J) +i (I ·i K)) .fst ⊆ (I ·i (J +i K)) .fst
  incl2 x = rec isPropPropTrunc λ ((y , z) , y∈IJ , z∈IK , x≡y+z)
          → subst-∈ ((I ·i (J +i K)) .fst) (sym x≡y+z)
              ((I ·i (J +i K)) .snd .+Closed (inclHelperLeft _ y∈IJ) (inclHelperRight _ z∈IK))
   where
   inclHelperLeft : (I ·i J) .fst ⊆ (I ·i (J +i K)) .fst
   inclHelperLeft x' = map (λ (n , (α , β) , α∈I , β∈J , x'≡∑αβ)
                     → n , (α , β) , α∈I , (λ i → +iLincl J K _ (β∈J i)) , x'≡∑αβ)

   inclHelperRight : (I ·i K) .fst ⊆ (I ·i (J +i K)) .fst
   inclHelperRight x' = map (λ (n , (α , β) , α∈I , β∈K , x'≡∑αβ)
                      → n , (α , β) , α∈I , (λ i → +iRincl J K _ (β∈K i)) , x'≡∑αβ)

 -- only one absorption law, i.e. CommIdeal , +i , ·i does not form a dist. lattice
 ·iAbsorb+i : ∀ (I J : CommIdeal) → I +i (I ·i J) ≡ I
 ·iAbsorb+i I J = CommIdeal≡Char incl1 incl2
  where
  incl1 : (I +i (I ·i J)) .fst ⊆ I .fst
  incl1 x = rec (I .fst x .snd) λ ((y , z) , y∈I , z∈IJ , x≡y+z)
          → subst-∈ (I .fst) (sym x≡y+z) (I .snd .+Closed y∈I (·iLincl I J _ z∈IJ))

  incl2 : I .fst ⊆ (I +i (I ·i J)) .fst
  incl2 = +iLincl I (I ·i J)
