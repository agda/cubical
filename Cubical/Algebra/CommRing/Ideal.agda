{-
  This is mostly for convenience, when working with ideals
  (which are defined for general rings) in a commutative ring.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset renaming ( _∈_ to _∈p_ ; _⊆_ to _⊆p_
                                                  ; subst-∈ to subst-∈p )

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
open import Cubical.Algebra.RingSolver.Reflection

private
  variable
    ℓ : Level

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
   +Closed : ∀ {x y : R} → x ∈p I → y ∈p I → (x + y) ∈p I
   contains0 : 0r ∈p I
   ·Closed : ∀ {x : R} (r : R) → x ∈p I → r · x ∈p I

  ·RClosed :  ∀ {x : R} (r : R) → x ∈p I → x · r ∈p I
  ·RClosed r x∈pI = subst-∈p I (·Comm _ _) (·Closed r x∈pI)

 open isCommIdeal
 isPropIsCommIdeal : (I : ℙ R) → isProp (isCommIdeal I)
 +Closed (isPropIsCommIdeal I ici₁ ici₂ i) x∈pI y∈pI =
         I _ .snd (ici₁ .+Closed x∈pI y∈pI) (ici₂ .+Closed x∈pI y∈pI) i
 contains0 (isPropIsCommIdeal I ici₁ ici₂ i) = I 0r .snd (ici₁ .contains0) (ici₂ .contains0) i
 ·Closed (isPropIsCommIdeal I ici₁ ici₂ i) r x∈pI =
         I _ .snd (ici₁ .·Closed r x∈pI) (ici₂ .·Closed r x∈pI) i

 CommIdeal : Type (ℓ-suc ℓ)
 CommIdeal = Σ[ I ∈ ℙ R ] isCommIdeal I

 isSetCommIdeal : isSet CommIdeal
 isSetCommIdeal = isSetΣSndProp isSetℙ isPropIsCommIdeal

 --inclusion and containment of ideals
 _⊆_ : CommIdeal → CommIdeal → Type ℓ
 I ⊆ J = I .fst ⊆p J .fst

 infix 5 _∈_
 _∈_ : R → CommIdeal → Type ℓ
 x ∈ I = x ∈p I .fst

 subst-∈ : (I : CommIdeal) {x y : R} → x ≡ y → x ∈ I → y ∈ I
 subst-∈ I = subst-∈p (I .fst)

 CommIdeal≡Char : {I J : CommIdeal} → I ⊆ J → J ⊆ I → I ≡ J
 CommIdeal≡Char I⊆J J⊆I = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (I⊆J , J⊆I))

 ∑Closed : (I : CommIdeal) {n : ℕ} (V : FinVec R n)
         → (∀ i → V i ∈ I) → ∑ V ∈ I
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

 contains1Is1 : (I : CommIdeal) → 1r ∈ I → I ≡ 1Ideal
 contains1Is1 I 1∈I = CommIdeal≡Char (λ _ _ → lift tt)
   λ x _ → subst-∈ I (·Rid _) (I .snd .·Closed x 1∈I) -- x≡x·1 ∈ I

 _+i_ : CommIdeal → CommIdeal → CommIdeal
 fst (I +i J) x =
     (∃[ (y , z) ∈ (R × R) ] ((y ∈ I) × (z ∈ J) × (x ≡ y + z))) --have a record for this?
     , isPropPropTrunc
 +Closed (snd (I +i J)) {x = x₁} {y = x₂} = map2 +ClosedΣ
  where
  +ClosedΣ : Σ[ (y₁ , z₁) ∈ (R × R) ] ((y₁ ∈ I) × (z₁ ∈ J) × (x₁ ≡ y₁ + z₁))
           → Σ[ (y₂ , z₂) ∈ (R × R) ] ((y₂ ∈ I) × (z₂ ∈ J) × (x₂ ≡ y₂ + z₂))
           → Σ[ (y₃ , z₃) ∈ (R × R) ] ((y₃ ∈ I) × (z₃ ∈ J) × (x₁ + x₂ ≡ y₃ + z₃))
  +ClosedΣ ((y₁ , z₁) , y₁∈I , z₁∈J , x₁≡y₁+z₁) ((y₂ , z₂) , y₂∈I , z₂∈J , x₂≡y₂+z₂) =
    (y₁ + y₂ , z₁ + z₂) , +Closed (snd I) y₁∈I y₂∈I , +Closed (snd J) z₁∈J z₂∈J
                      , cong₂ (_+_) x₁≡y₁+z₁ x₂≡y₂+z₂ ∙ +ShufflePairs _ _ _ _
 contains0 (snd (I +i J)) = ∣ (0r , 0r) , contains0 (snd I) , contains0 (snd J) , sym (+Rid _) ∣
 ·Closed (snd (I +i J)) {x = x} r = map ·ClosedΣ
  where
  ·ClosedΣ : Σ[ (y₁ , z₁) ∈ (R × R) ] ((y₁ ∈ I) × (z₁ ∈ J) × (x ≡ y₁ + z₁))
           → Σ[ (y₂ , z₂) ∈ (R × R) ] ((y₂ ∈ I) × (z₂ ∈ J) × (r · x ≡ y₂ + z₂))
  ·ClosedΣ ((y₁ , z₁) , y₁∈I , z₁∈J , x≡y₁+z₁) =
    (r · y₁ , r · z₁) , ·Closed (snd I) r y₁∈I , ·Closed (snd J) r z₁∈J
                     , cong (r ·_) x≡y₁+z₁ ∙ ·Rdist+ _ _ _

 infixl 6 _+i_

 +iComm⊆ : ∀ (I J : CommIdeal) → (I +i J) ⊆ (J +i I)
 +iComm⊆ I J x = map λ ((y , z) , y∈I , z∈J , x≡y+z) → (z , y) , z∈J , y∈I , x≡y+z ∙ +Comm _ _

 +iComm : ∀ (I J : CommIdeal) → I +i J ≡ J +i I
 +iComm I J = CommIdeal≡Char (+iComm⊆ I J)  (+iComm⊆ J I)

 +iLidLIncl : ∀ (I : CommIdeal) → (0Ideal +i I) ⊆ I
 +iLidLIncl I x = rec (I .fst x .snd) λ ((y , z) , y≡0 , z∈I , x≡y+z)
                                 → subst-∈ I (sym (x≡y+z ∙∙ cong (_+ z) y≡0 ∙∙ +Lid z)) z∈I

 +iLidRIncl : ∀ (I : CommIdeal) → I ⊆ (0Ideal +i I)
 +iLidRIncl I x x∈I = ∣ (0r , x) , refl , x∈I , sym (+Lid _) ∣

 +iLid : ∀ (I : CommIdeal) → 0Ideal +i I ≡ I
 +iLid I = CommIdeal≡Char (+iLidLIncl I) (+iLidRIncl I)

 +iLincl : ∀ (I J : CommIdeal) → I ⊆ (I +i J)
 +iLincl I J x x∈I = ∣ (x , 0r) , x∈I , J .snd .contains0 , sym (+Rid x) ∣

 +iRincl : ∀ (I J : CommIdeal) → J ⊆ (I +i J)
 +iRincl I J x x∈J = ∣ (0r , x) , I .snd .contains0 , x∈J ,  sym (+Lid x) ∣

 +iRespLincl : ∀ (I J K : CommIdeal) → I ⊆ J → (I +i K) ⊆ (J +i K)
 +iRespLincl I J K I⊆J x = map λ ((y , z) , y∈I , z∈K , x≡y+z) → ((y , z) , I⊆J y y∈I , z∈K , x≡y+z)

 +iAssocLIncl : ∀ (I J K : CommIdeal) → (I +i (J +i K)) ⊆ ((I +i J) +i K)
 +iAssocLIncl I J K x = elim (λ _ → ((I +i J) +i K) .fst x .snd) (uncurry3
           λ (y , z) y∈I → elim (λ _ → isPropΠ λ _ → ((I +i J) +i K) .fst x .snd)
             λ ((u , v) , u∈J , v∈K , z≡u+v) x≡y+z
               → ∣ (y + u , v) , ∣ _ , y∈I , u∈J , refl ∣ , v∈K
                                , x≡y+z ∙∙ cong (y +_) z≡u+v ∙∙ +Assoc _ _ _ ∣)

 +iAssocRIncl : ∀ (I J K : CommIdeal) → ((I +i J) +i K) ⊆ (I +i (J +i K))
 +iAssocRIncl I J K x = elim (λ _ → (I +i (J +i K)) .fst x .snd) (uncurry3
           λ (y , z) → elim (λ _ → isPropΠ2 λ _ _ → (I +i (J +i K)) .fst x .snd)
             λ ((u , v) , u∈I , v∈J , y≡u+v) z∈K x≡y+z
               → ∣ (u , v + z) , u∈I , ∣ _ , v∈J , z∈K , refl ∣
                                      , x≡y+z ∙∙ cong (_+ z) y≡u+v ∙∙ sym (+Assoc _ _ _) ∣)

 +iAssoc : ∀ (I J K : CommIdeal) → I +i (J +i K) ≡ (I +i J) +i K
 +iAssoc I J K = CommIdeal≡Char (+iAssocLIncl I J K) (+iAssocRIncl I J K)

 +iIdemLIncl : ∀ (I : CommIdeal) → (I +i I) ⊆ I
 +iIdemLIncl I x = rec (I .fst x .snd) λ ((y , z) , y∈I , z∈I , x≡y+z)
                                 → subst-∈ I (sym x≡y+z) (I .snd .+Closed y∈I z∈I)

 +iIdemRIncl : ∀ (I : CommIdeal) → I ⊆ (I +i I)
 +iIdemRIncl I x x∈I = ∣ (0r , x) , I .snd .contains0 , x∈I , sym (+Lid _) ∣

 +iIdem : ∀ (I : CommIdeal) → I +i I ≡ I
 +iIdem I = CommIdeal≡Char (+iIdemLIncl I) (+iIdemRIncl I)


 -- where to put this?
 mul++dist : ∀ {n m : ℕ} (α U : FinVec R n) (β V : FinVec R m) (j : Fin (n +ℕ m))
            → ((λ i → α i · U i) ++Fin (λ i → β i · V i)) j ≡ (α ++Fin β) j · (U ++Fin V) j
 mul++dist {n = zero} α U β V j = refl
 mul++dist {n = suc n} α U β V zero = refl
 mul++dist {n = suc n} α U β V (suc j) = mul++dist (α ∘ suc) (U ∘ suc) β V j

 -- define multiplication of ideals
 _·i_ : CommIdeal → CommIdeal → CommIdeal
 fst (I ·i J) x = (∃[ n ∈ ℕ ] Σ[ (α , β) ∈ (FinVec R n × FinVec R n) ]
                   (∀ i → α i ∈ I) × (∀ i → β i ∈ J) × (x ≡ ∑ λ i → α i · β i))
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

 prodInProd : ∀ (I J : CommIdeal) (x y : R) → x ∈ I → y ∈ J → (x · y) ∈ (I ·i J)
 prodInProd _ _ x y x∈I y∈J =
            ∣ 1 , ((λ _ → x) , λ _ → y) , (λ _ → x∈I) , (λ _ → y∈J) , sym (+Rid _) ∣

 ·iLincl : ∀ (I J : CommIdeal) → (I ·i J) ⊆ I
 ·iLincl I J x = elim (λ _ → I .fst x .snd)
   λ (_ , (α , β) , α∈I , _ , x≡∑αβ) → subst-∈ I (sym x≡∑αβ)
                                     (∑Closed I (λ i → α i · β i) λ i → ·RClosed (I .snd) _ (α∈I i))

 ·iComm⊆ : ∀ (I J : CommIdeal) → (I ·i J) ⊆ (J ·i I)
 ·iComm⊆ I J x = map λ (n , (α , β) , ∀αi∈I , ∀βi∈J , x≡∑αβ)
                      → (n , (β , α) , ∀βi∈J , ∀αi∈I , x≡∑αβ ∙ ∑Ext (λ i → ·Comm (α i) (β i)))

 ·iComm : ∀ (I J : CommIdeal) → I ·i J ≡ J ·i I
 ·iComm I J = CommIdeal≡Char (·iComm⊆ I J) (·iComm⊆ J I)

 I⊆I1 : ∀ (I : CommIdeal) → I ⊆ (I ·i 1Ideal)
 I⊆I1 I x x∈I = ∣ 1 , ((λ _ → x) , λ _ → 1r) , (λ _ → x∈I) , (λ _ → lift tt) , useSolver x ∣
  where
  useSolver : ∀ x → x ≡ x · 1r + 0r
  useSolver = solve R'

 ·iRid : ∀ (I : CommIdeal) → I ·i 1Ideal ≡ I
 ·iRid I = CommIdeal≡Char (·iLincl I 1Ideal) (I⊆I1 I)

 -- a useful corollary
 ·iRContains1id : ∀ (I J : CommIdeal) → 1r ∈ J → I ·i J ≡ I
 ·iRContains1id I J 1∈J = cong (I ·i_) (contains1Is1 J 1∈J) ∙ ·iRid I

 ·iAssocLIncl : ∀ (I J K : CommIdeal) → (I ·i (J ·i K)) ⊆ ((I ·i J) ·i K)
 ·iAssocLIncl I J K x = rec isPropPropTrunc
         λ (_ , (α , β) , α∈I , β∈JK , x≡∑αβ)
             → subst-∈ ((I ·i J) ·i K) (sym x≡∑αβ)
               (∑Closed ((I ·i J) ·i K) (λ i → α i · β i)
         λ i → rec isPropPropTrunc
               (λ (_ , (γ , δ) , γ∈J , δ∈K , βi≡∑γδ)
                  → subst-∈ ((I ·i J) ·i K) -- each αᵢβᵢ ≡...≡ ∑αᵢγⱼδⱼ ∈IJK
                             (sym (cong (α i ·_) βi≡∑γδ ∙∙ ∑Mulrdist (α i) (λ j → γ j · δ j)
                                                        ∙∙ ∑Ext (λ j → ·Assoc (α i) (γ j) (δ j))))
                             (∑Closed ((I ·i J) ·i K) (λ j → α i · γ j · δ j) -- each αᵢγⱼδⱼ∈IJK
                                      λ j → prodInProd (I ·i J) K _ _
                                              (prodInProd I J _ _ (α∈I i) (γ∈J j)) (δ∈K j)))
               (β∈JK i))

 ·iAssocRIncl : ∀ (I J K : CommIdeal) → ((I ·i J) ·i K) ⊆ (I ·i (J ·i K))
 ·iAssocRIncl I J K x = rec isPropPropTrunc
         λ (_ , (α , β) , α∈IJ , β∈K , x≡∑αβ)
             → subst-∈ (I ·i (J ·i K)) (sym x≡∑αβ)
               (∑Closed (I ·i (J ·i K)) (λ i → α i · β i)
         λ i → rec isPropPropTrunc
               (λ (_ , (γ , δ) , γ∈I , δ∈J , αi≡∑γδ)
                  → subst-∈ (I ·i (J ·i K))
                             (sym (cong (_· β i) αi≡∑γδ ∙∙ ∑Mulldist (β i) (λ j → γ j · δ j)
                                        ∙∙ ∑Ext (λ j → sym (·Assoc (γ j) (δ j) (β i)))))
                             (∑Closed (I ·i (J ·i K)) (λ j → γ j · (δ j · β i))
                                      λ j → prodInProd I (J ·i K) _ _ (γ∈I j)
                                              (prodInProd J K _ _ (δ∈J j) (β∈K i))))
               (α∈IJ i))

 ·iAssoc : ∀ (I J K : CommIdeal) → I ·i (J ·i K) ≡ (I ·i J) ·i K
 ·iAssoc I J K = CommIdeal≡Char (·iAssocLIncl I J K) (·iAssocRIncl I J K)

 ·iRdist+iLIncl : ∀ (I J K : CommIdeal) → (I ·i (J +i K)) ⊆ (I ·i J +i I ·i K)
 ·iRdist+iLIncl I J K x = rec isPropPropTrunc
   λ (n , (α , β) , α∈I , β∈J+K , x≡∑αβ) → subst-∈ ((I ·i J) +i (I ·i K)) (sym x≡∑αβ)
     (∑Closed ((I ·i J) +i (I ·i K)) (λ i → α i · β i) -- each αi·βi ∈ IJ+IK
     λ i → rec isPropPropTrunc
           (λ ((γi , δi) , γi∈J , δi∈K , βi≡γi+δi) →
              ∣ (α i · γi , α i · δi) , prodInProd I J _ _ (α∈I i) γi∈J
                                      , prodInProd I K _ _ (α∈I i) δi∈K
                                      , cong (α i ·_) βi≡γi+δi ∙ ·Rdist+ _ _ _ ∣)
           (β∈J+K i))

 ·iRdist+iRIncl : ∀ (I J K : CommIdeal) → ((I ·i J) +i (I ·i K)) ⊆ (I ·i (J +i K))
 ·iRdist+iRIncl I J K x = rec isPropPropTrunc λ ((y , z) , y∈IJ , z∈IK , x≡y+z)
         → subst-∈ (I ·i (J +i K)) (sym x≡y+z)
             ((I ·i (J +i K)) .snd .+Closed (inclHelperLeft _ y∈IJ) (inclHelperRight _ z∈IK))
  where
  inclHelperLeft : (I ·i J) ⊆ (I ·i (J +i K))
  inclHelperLeft x' = map (λ (n , (α , β) , α∈I , β∈J , x'≡∑αβ)
                    → n , (α , β) , α∈I , (λ i → +iLincl J K _ (β∈J i)) , x'≡∑αβ)

  inclHelperRight : (I ·i K) ⊆ (I ·i (J +i K))
  inclHelperRight x' = map (λ (n , (α , β) , α∈I , β∈K , x'≡∑αβ)
                     → n , (α , β) , α∈I , (λ i → +iRincl J K _ (β∈K i)) , x'≡∑αβ)

 ·iRdist+i : ∀ (I J K : CommIdeal) → I ·i (J +i K) ≡ I ·i J +i I ·i K
 ·iRdist+i I J K = CommIdeal≡Char (·iRdist+iLIncl I J K) (·iRdist+iRIncl I J K)

 -- only one absorption law, i.e. CommIdeal , +i , ·i does not form a dist. lattice
 ·iAbsorb+iLIncl : ∀ (I J : CommIdeal) → (I +i (I ·i J)) ⊆ I
 ·iAbsorb+iLIncl I J x = rec (I .fst x .snd) λ ((y , z) , y∈I , z∈IJ , x≡y+z)
         → subst-∈ I (sym x≡y+z) (I .snd .+Closed y∈I (·iLincl I J _ z∈IJ))

 ·iAbsorb+iRIncl : ∀ (I J : CommIdeal) → I ⊆ (I +i (I ·i J))
 ·iAbsorb+iRIncl I J = +iLincl I (I ·i J)

 ·iAbsorb+i : ∀ (I J : CommIdeal) → I +i (I ·i J) ≡ I
 ·iAbsorb+i I J = CommIdeal≡Char (·iAbsorb+iLIncl I J) (·iAbsorb+iRIncl I J)


IdealsIn : (R : CommRing ℓ) → Type _
IdealsIn R = CommIdeal.CommIdeal R

module _ {R : CommRing ℓ} where
  open CommRingStr (snd R)
  open isIdeal
  open CommIdeal R
  open isCommIdeal
  makeIdeal : (I : fst R → hProp ℓ)
              → (+-closed : {x y : fst R} → x ∈p I → y ∈p I → (x + y) ∈p I)
              → (0r-closed : 0r ∈p I)
              → (·-closedLeft : {x : fst R} → (r : fst R) → x ∈p I → r · x ∈p I)
              → IdealsIn R
  fst (makeIdeal I +-closed 0r-closed ·-closedLeft) = I
  +Closed (snd (makeIdeal I +-closed 0r-closed ·-closedLeft)) = +-closed
  contains0 (snd (makeIdeal I +-closed 0r-closed ·-closedLeft)) = 0r-closed
  ·Closed (snd (makeIdeal I +-closed 0r-closed ·-closedLeft)) = ·-closedLeft


  CommIdeal→Ideal : IdealsIn R → IdealsInRing (CommRing→Ring R)
  fst (CommIdeal→Ideal I) = fst I
  +-closed (snd (CommIdeal→Ideal I)) = +Closed (snd I)
  -closed (snd (CommIdeal→Ideal I)) =  λ x∈pI → subst-∈p (fst I) (useSolver _)
                                                           (·Closed (snd I) (- 1r) x∈pI)
                                         where useSolver : (x : fst R) → - 1r · x ≡ - x
                                               useSolver = solve R
  0r-closed (snd (CommIdeal→Ideal I)) = contains0 (snd I)
  ·-closedLeft (snd (CommIdeal→Ideal I)) = ·Closed (snd I)
  ·-closedRight (snd (CommIdeal→Ideal I)) = λ r x∈pI →
                                             subst-∈p (fst I)
                                                   (·Comm r _)
                                                   (·Closed (snd I) r x∈pI)
