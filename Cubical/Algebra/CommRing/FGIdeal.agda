{-
  Define finitely generated ideals of commutative rings and
  show that they are an ideal.
  Parts of this should be reusable for explicit constructions
  of free modules over a finite set.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.FGIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.FinData
open import Cubical.Data.Nat renaming ( zero to ℕzero ; suc to ℕsuc
                                      ; _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-assoc to +ℕ-assoc ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.Ideal.Sum
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.Quotient
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Matrix
open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' : Level

module _ (Ring@(R , str) : CommRing ℓ) where
  infixr 5 _holds
  _holds : hProp ℓ → Type ℓ
  P holds = fst P
  open CommRingStr str
  open RingTheory (CommRing→Ring Ring)
  open Sum (CommRing→Ring Ring)

  linearCombination : {n : ℕ} → FinVec R n → FinVec R n → R
  linearCombination α V = ∑ (λ i → α i · V i)

  sumDist+ : ∀ {n : ℕ} (α β V : FinVec R n)
           → linearCombination (λ i → α i + β i) V ≡ linearCombination α V + linearCombination β V
  sumDist+ α β V = ∑Ext (λ i → ·DistL+ (α i) (β i) (V i)) ∙ ∑Split (λ i → α i · V i) (λ i → β i · V i)

  dist- : ∀ {n : ℕ} (α V : FinVec R n)
        → linearCombination (λ i → - α i) V ≡ - linearCombination α V
  dist- α V = ∑Ext (λ i → -DistL· (α i) (V i)) ∙ ∑Dist- (λ i → α i · V i)

  dist0 : ∀ {n : ℕ} (V : FinVec R n)
        → linearCombination (replicateFinVec n 0r) V ≡ 0r
  dist0 {n = n} V = ∑Ext (λ i → 0LeftAnnihilates (V i)) ∙ ∑0r n

  isLinearCombination : {n : ℕ} → FinVec R n → R → Type ℓ
  isLinearCombination V x = ∃[ α ∈ FinVec R _ ] x ≡ linearCombination α V

  {- If x and y are linear combinations of l, then (x + y) is
     a linear combination. -}
  isLinearCombination+ : {n : ℕ} {x y : R} (V : FinVec R n)
                         → isLinearCombination V x
                         → isLinearCombination V y
                         → isLinearCombination V (x + y)
  isLinearCombination+ V = PT.map2 λ α β → (λ i → α .fst i + β .fst i)
                                       , cong₂ (_+_) (α .snd) (β .snd) ∙ sym (sumDist+ _ _ V)

  {- If x is a linear combinations of l, then -x is
     a linear combination. -}
  isLinearCombination- : {n : ℕ} {x : R} (V : FinVec R n)
                       → isLinearCombination V x → isLinearCombination V (- x)
  isLinearCombination- V = PT.map λ α → (λ i → - α .fst i) , cong (-_) (α .snd) ∙ sym (dist- _ V)

  {- 0r is the trivial linear Combination -}
  isLinearCombination0 : {n : ℕ} (V : FinVec R n)
                       → isLinearCombination V 0r
  isLinearCombination0 V = ∣ _ , sym (dist0 V) ∣₁

  {- Linear combinations are stable under left multiplication -}
  isLinearCombinationL· : {n : ℕ} (V : FinVec R n) (r : R) {x : R}
                        → isLinearCombination V x → isLinearCombination V (r · x)
  isLinearCombinationL· V r = PT.map λ α → (λ i → r · α .fst i) , cong (r ·_) (α .snd)
                                                            ∙∙ ∑Mulrdist r (λ i → α .fst i · V i)
                                                            ∙∙ ∑Ext λ i → ·Assoc r (α .fst i) (V i)

  generatedIdeal : {n : ℕ} → FinVec R n → IdealsIn Ring
  fst (generatedIdeal V) = λ x → isLinearCombination V x , isPropPropTrunc
  CommIdeal.isCommIdeal.+Closed (snd (generatedIdeal V)) = isLinearCombination+ V
  CommIdeal.isCommIdeal.contains0 (snd (generatedIdeal V)) = isLinearCombination0 V
  CommIdeal.isCommIdeal.·Closed (snd (generatedIdeal V)) = λ r → isLinearCombinationL· V r

-- two lemma for computing linear combination
module _
  (A'@(A , Ar) : CommRing ℓ)
  (B'@(B , Br) : Ring ℓ')
  (f'@(f , fr) : RingHom (CommRing→Ring A') B')
  where

  open CommRingStr Ar using ()
    renaming
    ( 0r        to 0A
    ; 1r        to 1A
    ; _+_       to _+A_
    ; -_        to -A_
    ; _·_       to _·A_ )

  open RingStr Br using ()
    renaming
    ( 0r        to 0B
    ; 1r        to 1B
    ; _+_       to _+B_
    ; -_        to -B_
    ; _·_       to _·B_ )

  open CommRingStr
  open IsRingHom
  open Sum
  open SumMap (CommRing→Ring A') B'

  ∑A = ∑ (CommRing→Ring A')
  ∑B = ∑ B'

  cancelLinearCombination : (n : ℕ) → (a v : FinVec A n) → (fnull : (k : Fin n) → f (v k) ≡ 0B)
                               → f (linearCombination A' a v) ≡ 0B
  cancelLinearCombination n a v fnull = f (∑A (λ i → a i ·A v i))
                                             ≡⟨ ∑Map f' (λ i → a i ·A v i) ⟩
                                        ∑B (λ i → f (a i ·A v i))
                                             ≡⟨ ∑Ext B' (λ i → pres· fr (a i) (v i)) ⟩
                                        ∑B (λ i → (f (a i)) ·B (f (v i)))
                                             ≡⟨ ∑Ext B' (λ i → cong (λ X → f (a i) ·B X) (fnull i)) ⟩
                                        ∑B (λ i → f (a i) ·B 0B)
                                             ≡⟨ ∑Mulr0 B' (λ i → f (a i)) ⟩
                                        0B ∎


module _
  (A'@(A , Astr) : CommRing ℓ)
  where

  Ar : Ring ℓ
  Ar = CommRing→Ring A'

  open CommRingStr Astr
  open RingTheory

  genδ-FinVec-LinearCombi : (n : ℕ) → (k : Fin n) → (a : A) → (v : FinVec A n)
                               → linearCombination A' (genδ-FinVec n (toℕ k) a 0r) v ≡ (a · (v k))
  genδ-FinVec-LinearCombi ℕzero () a v
  genδ-FinVec-LinearCombi (ℕsuc n) zero a v = cong (λ X → a · (v zero) + X) (cong (λ X → foldrFin _+_ 0r X)
                                                    (funExt (λ x → 0LeftAnnihilates Ar (v (suc x)))))
                                               ∙ cong (λ X → (a · v zero) + X) (Sum.∑0r Ar n)
                                               ∙ +IdR _
  genδ-FinVec-LinearCombi (ℕsuc n) (suc k) a v = cong (λ X → X + foldrFin _+_ 0r (λ x → genδ-FinVec n (toℕ k) a 0r x · v (suc x)))
                                                       (0LeftAnnihilates Ar _)
                                                  ∙ +IdL _
                                                  ∙ genδ-FinVec-LinearCombi n k a (λ z → v (suc z))



  genδ-FinVec-ℕLinearCombi : (n k : ℕ) → (infkn : k < n) → (a : A) → (v : FinVec A n)
                           → linearCombination A' (genδ-FinVec n k a 0r) v ≡ (a · (v (fromℕ' n k infkn)))
  genδ-FinVec-ℕLinearCombi ℕzero k infkn a v = ⊥.rec (¬-<-zero infkn)
  genδ-FinVec-ℕLinearCombi (ℕsuc n) ℕzero infkn a v = cong (λ X → a · (v zero) + X) (cong (λ X → foldrFin _+_ 0r X)
                                                       (funExt (λ x → 0LeftAnnihilates Ar (v (suc x)))))

                                                      ∙ cong (λ X → (a · v zero) + X) (Sum.∑0r Ar n)
                                                      ∙ +IdR _
  genδ-FinVec-ℕLinearCombi (ℕsuc n) (ℕsuc k) infkn a v = cong (λ X → X + foldrFin _+_ 0r (λ x → genδ-FinVec n k a 0r x · v (suc x)))
                                                              ((0LeftAnnihilates Ar _))
                                                          ∙ +IdL _
                                                          ∙ genδ-FinVec-ℕLinearCombi n k (pred-≤-pred infkn) a (λ z → v (suc z))



open CommIdeal.isCommIdeal
genIdeal : {n : ℕ} (R : CommRing ℓ) → FinVec (fst R) n → CommIdeal.CommIdeal R
fst (genIdeal R V) x = isLinearCombination R V x , isPropPropTrunc
+Closed (snd (genIdeal R V)) = isLinearCombination+ R V
contains0 (snd (genIdeal R V)) = isLinearCombination0 R V
·Closed (snd (genIdeal R V)) r = isLinearCombinationL· R V r

syntax genIdeal R V = ⟨ V ⟩[ R ]


FGIdealIn : (R : CommRing ℓ) → Type (ℓ-suc ℓ)
FGIdealIn R = Σ[ I ∈ CommIdeal.CommIdeal R ]
                   ∃[ nV ∈ Σ[ n ∈ ℕ ] FinVec (fst R) n ] I ≡ ⟨ nV .snd ⟩[ R ]

-- The lattice laws
module _ (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open CommIdeal R'
 open Sum (CommRing→Ring R')
 open KroneckerDelta (CommRing→Ring R')
 open IdealSum R'
 private
  R = fst R'
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]

 inclOfFGIdeal : {n : ℕ} (V : FinVec R n) (I : CommIdeal)
     → (∀ i → V i ∈ I) → ⟨ V ⟩ ⊆ I
 inclOfFGIdeal V I ∀i→Vi∈I x = PT.elim (λ _ → I .fst x .snd) inclOfFGIdealΣ
  where
  inclOfFGIdealΣ : Σ[ α ∈ FinVec R _ ] x ≡ linearCombination R' α V → x ∈ I
  inclOfFGIdealΣ (α , x≡α·V) = subst-∈ I (sym x≡α·V) (∑Closed I (λ i → α i · V i)
                             λ i → ·Closed (I .snd) _ (∀i→Vi∈I i))

 indInIdeal : ∀ {n : ℕ} (U : FinVec R n) (i : Fin n) → U i ∈ ⟨ U ⟩
 indInIdeal U i = ∣ (δ i) , sym (∑Mul1r _ U i) ∣₁

 sucIncl : ∀ {n : ℕ} (U : FinVec R (ℕsuc n)) → ⟨ U ∘ suc ⟩ ⊆ ⟨ U ⟩
 sucIncl U x = PT.map λ (α , x≡∑αUsuc) → (λ { zero → 0r ; (suc i) → α i }) , x≡∑αUsuc ∙ path _ _
  where
  path : ∀ s u₀ → s ≡ 0r · u₀ + s
  path _ _ = solve! R'

 emptyFGIdeal : ∀ (V : FinVec R 0) → ⟨ V ⟩ ≡ 0Ideal
 emptyFGIdeal V = CommIdeal≡Char (λ _ →  PT.rec (is-set _ _) snd)
                                 (λ _ x≡0 → ∣ (λ ()) , x≡0 ∣₁)

 0FGIdealLIncl : {n : ℕ} → ⟨ replicateFinVec n 0r ⟩ ⊆ 0Ideal
 0FGIdealLIncl x = PT.elim (λ _ → is-set _ _)
         λ (α , x≡∑α0) → subst-∈ 0Ideal (sym x≡∑α0) (∑Closed 0Ideal (λ i → α i · 0r)
         λ i → subst-∈ 0Ideal (sym (0RightAnnihilates _)) refl)

 0FGIdealRIncl : {n : ℕ} → 0Ideal ⊆ ⟨ replicateFinVec n 0r ⟩
 0FGIdealRIncl x x≡0 = subst-∈ ⟨ replicateFinVec _ 0r ⟩ (sym x≡0)
                        (⟨ replicateFinVec _ 0r ⟩ .snd .contains0)

 0FGIdeal : {n : ℕ} → ⟨ replicateFinVec n 0r ⟩ ≡ 0Ideal
 0FGIdeal = CommIdeal≡Char 0FGIdealLIncl 0FGIdealRIncl

 FGIdealAddLemmaLIncl : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                      → ⟨ U ++Fin V ⟩ ⊆ (⟨ U ⟩ +i ⟨ V ⟩)
 FGIdealAddLemmaLIncl {n = ℕzero} U V x x∈⟨V⟩ =
                                  ∣ (0r , x) , ⟨ U ⟩ .snd .contains0 , x∈⟨V⟩ , sym (+IdL x) ∣₁
 FGIdealAddLemmaLIncl {n = ℕsuc n} U V x = PT.rec isPropPropTrunc helperΣ
   where
   helperΣ : Σ[ α ∈ FinVec R _ ] (x ≡ ∑ λ i → α i · (U ++Fin V) i) → x ∈ (⟨ U ⟩ +i ⟨ V ⟩)
   helperΣ (α , p) = subst-∈ (⟨ U ⟩ +i ⟨ V ⟩) (sym p)
                              ((⟨ U ⟩ +i ⟨ V ⟩) .snd .+Closed zeroIncl sumIncl)
    where
    zeroIncl : (α zero · U zero) ∈ (⟨ U ⟩ +i ⟨ V ⟩)
    zeroIncl = +iLincl ⟨ U ⟩ ⟨ V ⟩ (α zero · U zero)
                 (⟨ U ⟩ .snd .·Closed (α zero) (indInIdeal U zero))

    sumIncl : (∑ λ i → (α ∘ suc) i · ((U ∘ suc) ++Fin V) i) ∈ (⟨ U ⟩ +i ⟨ V ⟩)
    sumIncl = let sum = ∑ λ i → (α ∘ suc) i · ((U ∘ suc) ++Fin V) i in
         +iRespLincl ⟨ U ∘ suc ⟩ ⟨ U ⟩ ⟨ V ⟩ (sucIncl U) sum
           (FGIdealAddLemmaLIncl (U ∘ suc) V _ ∣ (α ∘ suc) , refl ∣₁)

 FGIdealAddLemmaRIncl : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                      → (⟨ U ⟩ +i ⟨ V ⟩) ⊆ ⟨ U ++Fin V ⟩
 FGIdealAddLemmaRIncl U V x = PT.rec isPropPropTrunc (uncurry3 helper)
   where
   helperΣ : ((y , z) : R × R)
           → Σ[ α ∈ FinVec R _ ] (y ≡ ∑ λ i → α i · U i)
           → Σ[ β ∈ FinVec R _ ] (z ≡ ∑ λ i → β i · V i)
           → x ≡ y + z
           → x ∈ ⟨ U ++Fin V ⟩
   helperΣ (y , z) (α , y≡∑αU) (β , z≡∑βV) x≡y+z = ∣ (α ++Fin β) , path ∣₁
    where
    path : x ≡ ∑ λ i → (α ++Fin β) i · (U ++Fin V) i
    path = x                                               ≡⟨ x≡y+z ⟩
           y + z                                           ≡⟨ cong₂ (_+_) y≡∑αU z≡∑βV ⟩
           (∑ λ i → α i · U i) + (∑ λ i → β i · V i)       ≡⟨ sym (∑Split++ (λ i → α i · U i) _) ⟩
           (∑ ((λ i → α i · U i) ++Fin (λ i → β i · V i))) ≡⟨ ∑Ext (mul++dist α U β V) ⟩
           (∑ λ i → (α ++Fin β) i · (U ++Fin V) i)         ∎

   helper : ((y , z) : R × R)
          → ∃[ α ∈ FinVec R _ ] (y ≡ ∑ λ i → α i · U i)
          → ∃[ β ∈ FinVec R _ ] (z ≡ ∑ λ i → β i · V i)
          → x ≡ y + z
          → x ∈ ⟨ U ++Fin V ⟩
   helper _ = PT.rec2 (isPropΠ (λ _ → isPropPropTrunc)) (helperΣ _)

 FGIdealAddLemma : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                 → ⟨ U ++Fin V ⟩ ≡ ⟨ U ⟩ +i ⟨ V ⟩
 FGIdealAddLemma U V = CommIdeal≡Char (FGIdealAddLemmaLIncl U V) (FGIdealAddLemmaRIncl U V)


 IdealAddAssoc :  {n m k : ℕ} (U : FinVec R n) (V : FinVec R m) (W : FinVec R k)
               → ⟨ U ++Fin (V ++Fin W) ⟩ ≡  ⟨ (U ++Fin V) ++Fin W ⟩
 IdealAddAssoc {n = n} {m = m} {k = k} U V W =
   let genIdealExpl : (n : ℕ) → FinVec R n → CommIdeal
       genIdealExpl _ V = ⟨ V ⟩
   in  cong₂ genIdealExpl (+ℕ-assoc n m k) (++FinAssoc U V W)

 ++FinComm : ∀ {n m : ℕ} (V : FinVec R n) (W : FinVec R m)
           → ⟨ V ++Fin W ⟩ ≡ ⟨ W ++Fin V ⟩
 ++FinComm V W = FGIdealAddLemma V W ∙∙ +iComm ⟨ V ⟩ ⟨ W ⟩ ∙∙ sym (FGIdealAddLemma W V)

 open ProdFin R'
 prodIn··Ideal : {n m : ℕ} (U : FinVec R n) (V : FinVec R m) (x y : R)
          → (x ∈ ⟨ U ⟩) → (y ∈ ⟨ V ⟩) → (x · y) ∈ ⟨ U ··Fin V ⟩
 prodIn··Ideal {n = n} {m = m} U V x y = PT.map2 Σhelper
  where
  Σhelper : Σ[ α ∈ FinVec R n ] x ≡ linearCombination R' α U
          → Σ[ β ∈ FinVec R m ] y ≡ linearCombination R' β V
          → Σ[ γ ∈ FinVec R (n ·ℕ m) ] (x · y) ≡ linearCombination R' γ (U ··Fin V)
  Σhelper (α , x≡∑αU) (β , y≡∑βV) = α ··Fin β , path
   where
   path : x · y ≡ ∑ λ i → (α ··Fin β) i · (U ··Fin V) i
   path = x · y ≡⟨ cong₂ (_·_) x≡∑αU y≡∑βV ⟩
          (∑ λ i → α i · U i) · (∑ λ i → β i · V i) ≡⟨ ∑Dist··Fin (λ i → α i · U i) _ ⟩
          (∑ λ j → ((λ i → α i · U i) ··Fin (λ i → β i · V i)) j) ≡⟨ ∑Ext (·Dist··Fin α U β V) ⟩
          (∑ λ i → (α ··Fin β) i · (U ··Fin V) i) ∎

 FGIdealMultLemmaLIncl : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                       → ⟨ U ··Fin V ⟩ ⊆ (⟨ U ⟩ ·i ⟨ V ⟩)
 FGIdealMultLemmaLIncl U V x = PT.elim (λ _ → isPropPropTrunc)
   λ (α , x≡∑αUV) → subst-∈ (⟨ U ⟩ ·i ⟨ V ⟩)  (sym x≡∑αUV) --replace x by ∑αᵢⱼUᵢVⱼ
     (∑Closed (⟨ U ⟩ ·i ⟨ V ⟩) (λ i → α i · (U ··Fin V) i) --show that each αᵢ(U··V)ᵢ is in product
       λ i → (⟨ U ⟩ ·i ⟨ V ⟩) .snd .·Closed (α i) --drop the α's
         (flattenElim {P = _∈ (⟨ U ⟩ ·i ⟨ V ⟩)} (toMatrix U V) --show theat UᵢVⱼ is in product
           (λ j k → prodInProd ⟨ U ⟩ ⟨ V ⟩ (U j) (V k) (indInIdeal U j) (indInIdeal V k)) i))

 FGIdealMultLemmaRIncl : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                       → (⟨ U ⟩ ·i ⟨ V ⟩) ⊆ ⟨ U ··Fin V ⟩
 FGIdealMultLemmaRIncl U V x = PT.elim (λ _ → isPropPropTrunc)
   λ (_ , (α , β) , ∀α∈⟨U⟩ , ∀β∈⟨V⟩ , x≡∑αβ) → subst-∈ ⟨ U ··Fin V ⟩ (sym x≡∑αβ)
     (∑Closed ⟨ U ··Fin V ⟩ _ (λ i → prodIn··Ideal U V (α i) (β i) (∀α∈⟨U⟩ i) (∀β∈⟨V⟩ i)))

 FGIdealMultLemma : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                 → ⟨ U ··Fin V ⟩ ≡ ⟨ U ⟩ ·i ⟨ V ⟩
 FGIdealMultLemma U V = CommIdeal≡Char (FGIdealMultLemmaLIncl U V) (FGIdealMultLemmaRIncl U V)




-- A useful lemma for constructing the structure sheaf
module GeneratingPowers (R' : CommRing ℓ) (n : ℕ) where
 open CommRingStr (snd R')
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open Exponentiation R'
 open BinomialThm R'
 open CommIdeal R'

 private
  R = fst R'
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]
  _ⁿ : {m : ℕ} → FinVec R m → FinVec R m
  U ⁿ = λ i → U i ^ n


 lemma : (m : ℕ) (α U : FinVec R (ℕsuc m))
       → (linearCombination R' α U) ^ ((ℕsuc m) ·ℕ n) ∈ ⟨ U ⁿ ⟩
 lemma ℕzero α U = ∣ α ⁿ , path ∣₁
  where
  path : (α zero · U zero + 0r) ^ (n +ℕ 0) ≡ α zero ^ n · U zero ^ n + 0r
  path = (α zero · U zero + 0r) ^ (n +ℕ 0) ≡⟨ cong (_^ (n +ℕ 0)) (+IdR _) ⟩
         (α zero · U zero) ^ (n +ℕ 0)      ≡⟨ cong ((α zero · U zero) ^_) (+-zero n) ⟩
         (α zero · U zero) ^ n              ≡⟨ ^-ldist-· _ _ n ⟩
          α zero ^ n · U zero ^ n           ≡⟨ sym (+IdR _) ⟩
          α zero ^ n · U zero ^ n + 0r ∎

 lemma (ℕsuc m) α U = subst-∈ ⟨ U ⁿ ⟩ (sym (BinomialThm (n +ℕ (ℕsuc m) ·ℕ n) x y)) ∑Binomial∈⟨Uⁿ⟩
  where
  x = α zero · U zero
  y = linearCombination R' (α ∘ suc) (U ∘ suc)

  binomialSummand∈⟨Uⁿ⟩ : ∀ (i : Fin _) → BinomialVec (n +ℕ (ℕsuc m) ·ℕ n) x y i ∈ ⟨ U ⁿ ⟩
  binomialSummand∈⟨Uⁿ⟩ i with ≤-+-split n ((ℕsuc m) ·ℕ n) (toℕ i) (pred-≤-pred (toℕ<n i))
  ... | inl n≤i = subst-∈ ⟨ U ⁿ ⟩ (·CommAssocr _ _ (x ^ (toℕ i)))
                                  (⟨ U ⁿ ⟩ .snd .·Closed _ (xHelper (toℕ i) n≤i))
   where
   xHelper : ∀ k → n ≤ k → x ^ k ∈ ⟨ U ⁿ ⟩
   xHelper k n≤k = subst-∈ ⟨ U ⁿ ⟩ path (⟨ U ⁿ ⟩ .snd .·Closed _ (indInIdeal R' (U ⁿ) zero))
    where
    path : α zero ^ k · U zero ^ (k ∸ n) · U zero ^ n ≡ x ^ k
    path = α zero ^ k · U zero ^ (k ∸ n) · U zero ^ n
         ≡⟨ sym (·Assoc _ _ _) ⟩
           α zero ^ k · (U zero ^ (k ∸ n) · U zero ^ n)
         ≡⟨ cong ((α zero ^ k) ·_) (·-of-^-is-^-of-+ (U zero) (k ∸ n) n) ⟩
           α zero ^ k · U zero ^ ((k ∸ n) +ℕ n)
         ≡⟨ cong (λ l → (α zero ^ k) · (U zero ^ l)) (≤-∸-+-cancel n≤k) ⟩
           α zero ^ k · U zero ^ k
         ≡⟨ sym (^-ldist-· (α zero) (U zero) k) ⟩
           x ^ k ∎

  ... | inr [m+1]n≤n+[m+1]n-i = ⟨ U ⁿ ⟩ .snd .·Closed _ (yHelper (toℕ i) [m+1]n≤n+[m+1]n-i)
   where
   powSucIncl : ⟨ (U ∘ suc) ⁿ ⟩ ⊆ ⟨ U ⁿ ⟩
   powSucIncl = inclOfFGIdeal R' ((U ∘ suc) ⁿ) ⟨ U ⁿ ⟩ (λ i → indInIdeal R' (U ⁿ) (suc i))

   inductiveStep : y ^ ((ℕsuc m) ·ℕ n) ∈ ⟨ U ⁿ ⟩
   inductiveStep = powSucIncl _ (lemma m (α ∘ suc) (U ∘ suc))

   yHelper : ∀ k
           → (ℕsuc m) ·ℕ n ≤ n +ℕ (ℕsuc m) ·ℕ n ∸ k
           → y ^ (n +ℕ (ℕsuc m) ·ℕ n ∸ k) ∈ ⟨ U ⁿ ⟩
   yHelper k [m+1]n≤n+[m+1]n-k = subst-∈ ⟨ U ⁿ ⟩ path (⟨ U ⁿ ⟩ .snd .·Closed _ inductiveStep)
    where
    n+[m+1]n-k = n +ℕ (ℕsuc m) ·ℕ n ∸ k
    [m+1]n = (ℕsuc m) ·ℕ n
    path : y ^ (n+[m+1]n-k ∸ [m+1]n) · y ^ [m+1]n ≡ y ^ n+[m+1]n-k
    path =
      y ^ (n+[m+1]n-k ∸ [m+1]n) · y ^ [m+1]n ≡⟨ ·-of-^-is-^-of-+ y (n+[m+1]n-k ∸ [m+1]n) [m+1]n ⟩
      y ^ ((n+[m+1]n-k ∸ [m+1]n) +ℕ [m+1]n)  ≡⟨ cong (y ^_) (≤-∸-+-cancel [m+1]n≤n+[m+1]n-k) ⟩
      y ^ n+[m+1]n-k ∎

  ∑Binomial∈⟨Uⁿ⟩ : ∑ (BinomialVec (n +ℕ (ℕsuc m) ·ℕ n) x y) ∈ ⟨ U ⁿ ⟩
  ∑Binomial∈⟨Uⁿ⟩ = ∑Closed ⟨ U ⁿ ⟩ _ binomialSummand∈⟨Uⁿ⟩


 thm : ∀ (m : ℕ) (U : FinVec R m) → 1r ∈ ⟨ U ⟩ → 1r ∈ ⟨ U ⁿ ⟩
 thm ℕzero U 1∈⟨U⟩ = 1∈⟨U⟩
 thm (ℕsuc m) U = PT.elim (λ _ → isPropPropTrunc) Σhelper
  where
  Σhelper : Σ[ α ∈ FinVec R (ℕsuc m) ] 1r ≡ linearCombination R' α U
          → 1r ∈ ⟨ U ⁿ ⟩
  Σhelper (α , p) = subst-∈ ⟨ U ⁿ ⟩ path (lemma m α U)
   where
   path : linearCombination R' α U ^ ((ℕsuc m) ·ℕ n) ≡ 1r
   path = linearCombination R' α U ^ ((ℕsuc m) ·ℕ n) ≡⟨ cong (_^ ((ℕsuc m) ·ℕ n)) (sym p) ⟩
          1r ^ ((ℕsuc m) ·ℕ n)                       ≡⟨ 1ⁿ≡1 ((ℕsuc m) ·ℕ n) ⟩
          1r ∎
