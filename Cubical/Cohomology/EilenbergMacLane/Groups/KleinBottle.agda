{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected
open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.IntMod

open import Cubical.HITs.KleinBottle renaming (rec to KleinFun)
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.EilenbergMacLane1 renaming (elimProp to elimPropEM1 ; elimSet to elimSetEM1)
open import Cubical.HITs.Susp
open import Cubical.HITs.RPn

open AbGroupStr

private
  variable
    ℓ ℓ' : Level

-- Elimination principles
module ConnK² {B : Type ℓ'} where
  elim₁ : {A : (KleinBottle → B) → Type ℓ}
    → isConnected 2 B
    → ((x : _) → isProp (A x)) → (b* : B)
    → ((l1 l2 : b* ≡ b*) (sq : Square l2 l2 (sym l1) l1)
                             → A (KleinFun b* l1 l2 sq))
    → (x : _) → A x
  elim₁ {A = A} conB pr b* ind f =
    PT.rec (pr f) (λ {(l1 , l2 , sq , id) → subst A (sym id) (ind _ _ _)})
      (elim₁' f)
    where
    characKleinFun : (f : KleinBottle → B)
      → Σ[ x ∈ B ] Σ[ l1 ∈ x ≡ x ] Σ[ l2 ∈ x ≡ x ]
         Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ KleinFun x l1 l2 sq
    characKleinFun f =
        (f point)
      , ((cong f line1) , ((cong f line2) , (λ i j → f (square i j) )
      , funExt λ { point → refl ; (line1 i) → refl ; (line2 i) → refl
                 ; (square i i₁) → refl}))

    characKleinFun^ : (f : KleinBottle → B) (x y : B) (p : x ≡ y)
      → Σ[ l1 ∈ x ≡ x ] Σ[ l2 ∈ x ≡ x ]
         Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ KleinFun x l1 l2 sq
      → Σ[ l1 ∈ y ≡ y ] Σ[ l2 ∈ y ≡ y ]
         Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ KleinFun y l1 l2 sq
    characKleinFun^ f x = J> λ x → x

    elim₁' : (f : KleinBottle → B)
      → ∃[ l1 ∈ b* ≡ b* ] Σ[ l2 ∈ b* ≡ b* ]
         Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f
        ≡ KleinFun b* l1 l2 sq
    elim₁' f =
      TR.rec squash₁ (λ r → ∣ characKleinFun^ f (f point) b* (sym r)
                               (characKleinFun f .snd) ∣₁)
        (Iso.fun (PathIdTruncIso 1) (isContr→isProp conB _ _))

  elim₂ : {A : (KleinBottle → B) → Type ℓ}
    → isConnected 3 B
    → ((x : _) → isProp (A x))
    → (b : B)
    → ((sq : (Ω^ 2) (B , b) .fst) → A (KleinFun b refl refl sq))
    → (x : _) → A x
  elim₂ {A = A} conB pr b ind f = PT.rec (pr f)
    (λ {(sq , fid) → subst A (sym fid) (ind sq)}) (elim₂' f)
    where
    characKleinFun^ : (f : KleinBottle → B) (x y : B)
         (p : x ≡ y) (l1 : x ≡ x) (l1' : y ≡ y)
      → PathP (λ i → p i ≡ p i) l1 l1'
      → (l2 : x ≡ x) (l2' : y ≡ y)
      → PathP (λ i → p i ≡ p i) l2 l2'
      → Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ KleinFun x l1 l2 sq
      → Σ[ sq ∈ Square l2' l2' (sym l1') l1' ] f ≡ KleinFun y l1' l2' sq
    characKleinFun^ f x = J> λ l1 → J> λ l2 → J> λ r → r

    elim₂' : (f : KleinBottle → B)
      → ∃[ sq ∈ (Ω^ 2) (B , b) .fst ] f ≡ KleinFun b refl refl sq
    elim₂' f =
      TR.rec (isProp→isSet squash₁)
        (λ p → TR.rec squash₁
              (λ pl → TR.rec squash₁
                (λ pr → ∣ characKleinFun^ f _ _
                           (sym p) (cong f line1) refl pl (cong f line2) refl pr
                           ((λ i j → f (square i j))
                           , (funExt (λ { point → refl
                                    ; (line1 i) → refl
                                    ; (line2 i) → refl
                                    ; (square i i₁) → refl}))) ∣₁)
                (isConnectedPathP 1 {A = λ i → p (~ i) ≡ p (~ i)}
           (isConnectedPath 2 conB _ _) (cong f line2) refl .fst))
          (isConnectedPathP 1 {A = λ i → p (~ i) ≡ p (~ i)}
           (isConnectedPath 2 conB _ _) (cong f line1) refl .fst))
        (Iso.fun (PathIdTruncIso 2) (isContr→isProp conB ∣ b ∣ ∣ f point ∣))

------ H⁰(K²,ℤ/2) ------
H⁰[K²,ℤ/2]≅ℤ/2 : AbGroupEquiv (coHomGr 0 ℤ/2 KleinBottle) ℤ/2
H⁰[K²,ℤ/2]≅ℤ/2 =
  H⁰conn (∣ point ∣
    , (TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
               (elimProp (λ _ → isOfHLevelTrunc 2 _ _)
               refl)))
    ℤ/2

------ H¹(K²,ℤ/2) ------
H¹K²→ℤ/2×ℤ/2 : coHom 1 ℤ/2 KleinBottle → fst (dirProdAb ℤ/2 ℤ/2)
H¹K²→ℤ/2×ℤ/2 = ST.rec (is-set (snd (dirProdAb ℤ/2 ℤ/2)))
                   λ f → ΩEM+1→EM-gen _ _ (cong f line1)
                       , ΩEM+1→EM-gen _ _ (cong f line2)

ℤ/2×ℤ/2→H¹K² : fst (dirProdAb ℤ/2 ℤ/2) → coHom 1 ℤ/2 KleinBottle
ℤ/2×ℤ/2→H¹K² (g₁ , g₂) =
  ∣ (λ { point → 0ₖ _
      ; (line1 i) → emloop g₁ i
      ; (line2 i) → emloop g₂ i
      ; (square i j) → main j i}) ∣₂
  where
  sideSq : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → Square p p p p
  sideSq p i j =
    hcomp (λ k → λ {(i = i0) → p (j ∨ ~ k)
                   ; (i = i1) → p (j ∧ k)
                   ; (j = i0) → p (i ∨ ~ k)
                   ; (j = i1) → p (i ∧ k)})
          (p i0)

  q = emloop-1g _ ◁ ((λ i j → emloop 1 i) ▷ sym (emloop-1g _))

  lem : (g₁ g₂ : _)
    → PathP (λ i → Path (EM₁ (ℤGroup/ 2)) (emloop g₂ i) (emloop g₂ i))
             (emloop g₁) (emloop g₁)
  lem  =
    ℤ/2-elim (ℤ/2-elim (sideSq _) q) (ℤ/2-elim (flipSquare q) (sideSq _))

  main : Square {A = EM₁ (ℤGroup/ 2)}
                 (sym (emloop g₁)) (emloop g₁)
                 (emloop g₂) (emloop g₂)
  main = (sym (emloop-inv (ℤGroup/ 2) g₁) ∙ cong emloop (-Const-ℤ/2 g₁))
       ◁ lem g₁ g₂

ℤ/2×ℤ/2→H¹K²→ℤ/2×ℤ/2 : (x : fst (dirProdAb ℤ/2 ℤ/2))
  → H¹K²→ℤ/2×ℤ/2 (ℤ/2×ℤ/2→H¹K² x) ≡ x
ℤ/2×ℤ/2→H¹K²→ℤ/2×ℤ/2 (g₁ , g₂) =
  ΣPathP ((Iso.leftInv (Iso-EM-ΩEM+1 0) g₁)
        , Iso.leftInv (Iso-EM-ΩEM+1 0) g₂)

H¹K²→ℤ/2×ℤ/2→H¹K² : (x : _)
  → ℤ/2×ℤ/2→H¹K² (H¹K²→ℤ/2×ℤ/2 x) ≡ x
H¹K²→ℤ/2×ℤ/2→H¹K² =
  ST.elim (λ _ → isSetPathImplicit)
    (ConnK².elim₁ (isConnectedEM 1) (λ _ → squash₂ _ _) embase
    λ l1 l2 sq → cong ∣_∣₂ (funExt (elimSet (λ _ → hLevelEM _ 1 _ _) refl
      (flipSquare (Iso.rightInv (Iso-EM-ΩEM+1 0) l1))
      (flipSquare (Iso.rightInv (Iso-EM-ΩEM+1 0) l2)))))

ℤ/2×ℤ/2≅H¹[K²,ℤ/2] :
  AbGroupEquiv (dirProdAb ℤ/2 ℤ/2) (coHomGr 1 ℤ/2 KleinBottle)
fst ℤ/2×ℤ/2≅H¹[K²,ℤ/2] = isoToEquiv is
  where
  is : Iso _ _
  Iso.fun is = ℤ/2×ℤ/2→H¹K²
  Iso.inv is = H¹K²→ℤ/2×ℤ/2
  Iso.rightInv is = H¹K²→ℤ/2×ℤ/2→H¹K²
  Iso.leftInv is = ℤ/2×ℤ/2→H¹K²→ℤ/2×ℤ/2
snd ℤ/2×ℤ/2≅H¹[K²,ℤ/2] =
  makeIsGroupHom λ x y → cong ∣_∣₂
    (funExt (elimSet (λ _ → hLevelEM _ 1 _ _) refl
      (flipSquare ((EM→ΩEM+1-hom 0 (fst x) (fst y)
                 ∙ sym (cong₂+₁ (emloop (fst x)) (emloop (fst y))))))
      (flipSquare ((EM→ΩEM+1-hom 0 (snd x) (snd y)
                 ∙ sym (cong₂+₁ (emloop (snd x)) (emloop (snd y))))))))

H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 :
  AbGroupEquiv (coHomGr 1 ℤ/2 KleinBottle) (dirProdAb ℤ/2 ℤ/2)
H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 = invGroupEquiv ℤ/2×ℤ/2≅H¹[K²,ℤ/2]

------ H²(K²,ℤ/2) ------

-- The equivalence Ω²K₂ ≃ ℤ/2 will be needed
Ω²K₂→ℤ/2 : fst ((Ω^ 2) (EM∙ ℤ/2 2)) → fst ℤ/2
Ω²K₂→ℤ/2 = Iso.fun Iso-Ω²K₂-ℤ/2

ℤ/2→Ω²K₂ : fst ℤ/2 → fst ((Ω^ 2) (EM∙ ℤ/2 2))
ℤ/2→Ω²K₂ = Iso.inv Iso-Ω²K₂-ℤ/2

Ω²K₂-based→ℤ/2 : (x : EM ℤ/2 2) (p : refl {x = x} ≡ refl) → fst ℤ/2
Ω²K₂-based→ℤ/2 x p =
  ΩEM+1→EM-gen 0 (ΩEM+1→EM-gen 1 x refl) (cong (ΩEM+1→EM-gen 1 x) p)

-- Contrucing the map H²(K²,ℤ/2) → ℤ/2
H²K²→ℤ/2₁ : (f : KleinBottle → EM ℤ/2 2)
  → (λ j → f (line2 j)) ∙ (λ i → f (line1 i))
   ≡ (λ j → f (line2 j)) ∙ (λ i → f (line1 i))
H²K²→ℤ/2₁ f =
  (λ i → (λ j → f (line2 j))
        ∙ symConst-ℤ/2 2 (f point) (λ i → f (line1 i)) i)
  ∙ isCommΩEM-base 1 _ _ _
  ∙ Square→compPath (λ i j → f (square i j))

H²K²→ℤ/2₂ : {x : EM ℤ/2 2} {p : x ≡ x} (q : p ≡ p) → fst ℤ/2
H²K²→ℤ/2₂ {x = x} {p = p} q =
  Ω²K₂-based→ℤ/2 x (sym (rCancel p) ∙∙ cong (_∙ sym p) q ∙∙ rCancel p)

-- the map gives something nice applied to nice elements
H²K²→ℤ/2-rewrite : (p : Square {A = EM ℤ/2 2} refl refl refl refl)
  → H²K²→ℤ/2₂ (H²K²→ℤ/2₁ (KleinFun (0ₖ 2) refl refl p))
  ≡ ΩEM+1→EM 0 (cong (ΩEM+1→EM 1) p)
H²K²→ℤ/2-rewrite p = cong H²K²→ℤ/2₂ (H²K²→ℤ/2₁-rewrite p)
      ∙ (λ j → H²K²→ℤ/2₂ (λ i → rUnit (p (~ i)) (~ j)))
      ∙ cong (Ω²K₂-based→ℤ/2 _) lem
      ∙ ΩEM+1→EM-sym 0 (cong (ΩEM+1→EM 1) p)
      ∙ -Const-ℤ/2 _
  where
  H²K²→ℤ/2₁-rewrite : (p : Square {A = EM ℤ/2 2} refl refl (sym refl) refl)
    → H²K²→ℤ/2₁ (KleinFun (0ₖ 2) refl refl p)
    ≡ λ i → p (~ i) ∙ refl
  H²K²→ℤ/2₁-rewrite p =
       cong₂ _∙_ (cong (cong (λ x → (λ _ → ∣ north ∣) ∙ x)) symConst-ℤ/2-refl)
                 (cong₂ _∙_ lem (Square→compPathΩ² p))
    ∙∙ sym (lUnit _)
    ∙∙ (sym (lUnit _)
     ∙ cong (cong (λ x → x ∙ refl)) (sym (sym≡flipSquare p)))
    where
    lem : isCommΩEM-base {G = ℤ/2} 1 ∣ north ∣ refl refl ≡ refl
    lem = ∙∙lCancel _

  lem : sym (rCancel refl) ∙∙ (λ i → p (~ i) ∙ refl) ∙∙ rCancel refl
       ≡ λ i j → p (~ i) j
  lem k i =
    hcomp (λ r → λ { (k = i1) → p (~ i)
                    ; (i = i0) → rUnit (refl {x = 0ₖ 2}) (~ r ∧ ~ k)
                    ; (i = i1) → rUnit (refl {x = 0ₖ 2}) (~ r ∧ ~ k)})
           (rUnit (p (~ i)) (~ k))

H²K²→ℤ/2 : coHom 2 ℤ/2 KleinBottle → fst ℤ/2
H²K²→ℤ/2 =
  ST.rec isSetFin
    λ f → H²K²→ℤ/2₂ (H²K²→ℤ/2₁ f)

-- Map in other direction
ℤ/2→H²K² : fst ℤ/2 → coHom 2 ℤ/2 KleinBottle
ℤ/2→H²K² g = ∣ KleinFun (0ₖ 2) refl refl (ℤ/2→Ω²K₂ g) ∣₂

-- Cancellations
H²K²→ℤ/2→H²K² : (f : coHom 2 ℤ/2 KleinBottle) → ℤ/2→H²K² (H²K²→ℤ/2 f) ≡ f
H²K²→ℤ/2→H²K² =
  ST.elim (λ _ → isSetPathImplicit)
    (ConnK².elim₂ (isConnectedEM 2) (λ _ → squash₂ _ _) ∣ north ∣
      λ sq → cong ℤ/2→H²K² (H²K²→ℤ/2-rewrite sq)
            ∙ cong ∣_∣₂ (funExt
              λ { point → refl
                ; (line1 i) → refl
                ; (line2 i) → refl
                ; (square i j) k → Iso.leftInv Iso-Ω²K₂-ℤ/2 sq k i j}))

ℤ/2→H²K²→ℤ/2 : (g : fst ℤ/2) → H²K²→ℤ/2 (ℤ/2→H²K² g) ≡ g
ℤ/2→H²K²→ℤ/2 g =
  H²K²→ℤ/2-rewrite (ℤ/2→Ω²K₂ g) ∙ (Iso.rightInv Iso-Ω²K₂-ℤ/2 g)

KleinFun-triv : ∀ {ℓ} {A : Type ℓ} {a : A} → KleinFun a refl refl refl ≡ λ _ → a
KleinFun-triv =
  funExt λ { point → refl ; (line1 i) → refl ; (line2 i) → refl
          ; (square i i₁) → refl}

KleinFun-trivₕ : {n : ℕ}
  → Path (coHom n ℤ/2 KleinBottle)
      (0ₕ n) (∣ (KleinFun (0ₖ n) refl refl (λ _ _ → 0ₖ n)) ∣₂)
KleinFun-trivₕ = cong ∣_∣₂ (sym KleinFun-triv)

H²K²→ℤ/2-pres0 : H²K²→ℤ/2 (0ₕ _) ≡ 0
H²K²→ℤ/2-pres0 = cong H²K²→ℤ/2 KleinFun-trivₕ
       ∙ H²K²→ℤ/2-rewrite (λ _ _ → ∣ north ∣ₕ)
       ∙ refl

H²[K²,ℤ/2]≅ℤ/2 : AbGroupEquiv (coHomGr 2 ℤ/2 KleinBottle) ℤ/2
fst H²[K²,ℤ/2]≅ℤ/2 = isoToEquiv is
  where
  is : Iso _ _
  Iso.fun is = H²K²→ℤ/2
  Iso.inv is = ℤ/2→H²K²
  Iso.rightInv is = ℤ/2→H²K²→ℤ/2
  Iso.leftInv is = H²K²→ℤ/2→H²K²
snd H²[K²,ℤ/2]≅ℤ/2 =
  Isoℤ/2-morph (fst H²[K²,ℤ/2]≅ℤ/2) (0ₕ 2) (sym H²K²→ℤ/2-pres0) _+ₕ_ (-ₕ_)
    (funExt (ST.elim (λ _ → isSetPathImplicit)
      (λ f → cong ∣_∣₂ (funExt λ x → sym (-ₖConst-ℤ/2 1 (f x))))))
    (AbGroupStr.isAbGroup (coHomGr 2 ℤ/2 KleinBottle .snd))

isContr-HⁿKleinBottle : (n : ℕ) (G : AbGroup ℓ)
  → isContr (coHom (suc (suc (suc n))) G KleinBottle)
fst (isContr-HⁿKleinBottle n G) = ∣ (KleinFun ∣ north ∣ refl refl refl) ∣₂
snd (isContr-HⁿKleinBottle n G) = ST.elim (λ _ → isSetPathImplicit)
         (ConnK².elim₂ (isConnectedSubtr 3 (suc n)
           (subst (λ m → isConnected m (EM G (3 +ℕ n)))
             (cong suc (+-comm 3 n))
             (isConnectedEM (3 +ℕ n)))) (λ _ → squash₂ _ _)
            (0ₖ (3 +ℕ n))
            λ p → TR.rec (squash₂ _ _)
              (λ q → cong ∣_∣₂ (cong (KleinFun ∣ north ∣ refl refl) q))
              (isConnectedPath 1
                (isConnectedPath 2
                  (isConnectedPath 3
                    ((isConnectedSubtr 4 n
                     (subst (λ m → isConnected m (EM G (3 +ℕ n)))
                       (+-comm 4 n)
                       (isConnectedEM (3 +ℕ n))))) _ _) _ _)
                         refl p .fst))


---- With general coefficients

-- H⁰(K²,G)
H⁰[K²,G]≅G : (G : AbGroup ℓ) → AbGroupEquiv (coHomGr 0 G KleinBottle) G
H⁰[K²,G]≅G G = H⁰conn (∣ point ∣
  , (TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
      (elimProp (λ _ → isOfHLevelTrunc 2 _ _) refl))) G

-- H¹(K²,G)
H¹[K²,G]≅G×H¹[RP²,G] : (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr 1 G KleinBottle) (AbDirProd G (coHomGr 1 G RP²))
fst (H¹[K²,G]≅G×H¹[RP²,G] G) = isoToEquiv mainIso
  where
  F→ : (KleinBottle → EM G 1) → (RP² → EM G 1)
  F→ f point = f point
  F→ f (line i) = f (line1 i)
  F→ f (square i j) = help i (~ j)
    where
    help : cong f (sym line1) ≡ cong f line1
    help =
      lUnit (cong f (sym line1))
      ∙ cong (_∙ cong f (sym line1))
          (sym (lCancel _))
     ∙ sym (assoc _ _ _)
     ∙ cong (sym (cong f line2) ∙_) (isCommΩEM-base 0 _ _ _)
     ∙ PathP→compPathL (λ i j → f (square j i))

  F← : (g : fst G) → (RP² → EM G 1) → KleinBottle → EM G 1
  F← g f point = f point
  F← g f (line1 i) = f (line i)
  F← g f (line2 i) = EM→ΩEM+1-gen 0 (f point) g i
  F← g f (square i j) = help j i
    where
    l1 = cong f line
    l2 = EM→ΩEM+1-gen 0 (f point) g

    help : Square (sym l1) l1 l2 l2
    help = compPathL→PathP
      (cong₂ _∙_ refl (isCommΩEM-base 0 _ _ _)
      ∙∙ assoc _ _ _
      ∙∙ cong (_∙ sym l1) (lCancel l2)
      ∙∙ sym (lUnit _)
      ∙∙ sym (cong (cong f) square))

  mainIso : Iso (coHom 1 G KleinBottle) (fst G × coHom 1 G RP²)
  Iso.fun mainIso =
    ST.rec (isSet× (is-set (snd G)) squash₂)
      λ f → (ΩEM+1→EM-gen 0 _ (cong f line2)) , ∣ F→ f ∣₂
  Iso.inv mainIso = uncurry λ g → ST.map (F← g)
  Iso.rightInv mainIso = uncurry λ g
    → ST.elim (λ _ → isOfHLevelPath 2 (isSet× (is-set (snd G)) squash₂) _ _)
               λ f → ΣPathP ((Iso.leftInv (Iso-EM-ΩEM+1-gen 0 (f point)) g)
                            , cong ∣_∣₂ (funExt (elimSetRP² (λ _ → hLevelEM G 1 _ _)
                              refl λ i j → f (line i))))
  Iso.leftInv mainIso = ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt (elimSet (λ _ → hLevelEM G 1 _ _)
      refl
      (λ i j → f (line1 i))
      (flipSquare (Iso.rightInv (Iso-EM-ΩEM+1-gen 0 (f point)) (cong f line2)))))
snd (H¹[K²,G]≅G×H¹[RP²,G] G) =
  makeIsGroupHom (ST.elim2
    (λ _ _ → isOfHLevelPath 2 lem  _ _)
    (ConnK².elim₁ (isConnectedEM 1) (λ _ → isPropΠ λ _ → lem _ _) embase
      λ p1 q1 r1
   → ConnK².elim₁ (isConnectedEM 1) (λ _ → lem _ _) embase
        λ p2 q2 r2 → ΣPathP (cong (ΩEM+1→EM 0) (cong₂+₁ q1 q2)
                            ∙ ΩEM+1→EM-hom 0 q1 q2
        , (cong ∣_∣₂ (funExt (elimSetRP² (λ _ → hLevelEM G 1 _ _)
          refl
          λ i j → (p1 i) +[ 1 ]ₖ (p2 i)))))))
  where
  lem = isSet× (is-set (snd G)) squash₂

H¹[K²,G]≅G×G[2] : (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr 1 G KleinBottle) (AbDirProd G (G [ 2 ]ₜ))
H¹[K²,G]≅G×G[2] G =
  compGroupEquiv (H¹[K²,G]≅G×H¹[RP²,G] G)
    (GroupEquivDirProd idGroupEquiv (H¹[RP²,G]≅G[2] G))

-- H²(K²,G)
private
  H²K²-helperFun₁ : (G : AbGroup ℓ) (n : ℕ)
    → (Σ[ p ∈ Ω (EM∙ G (2 +ℕ n)) .fst ]
              Σ[ q ∈ Ω (EM∙ G (2 +ℕ n)) .fst ] Square (sym p) p q q)
    →  ((Σ[ p ∈ Ω (EM∙ G (2 +ℕ n)) .fst ]
             p ≡ sym p))
  H²K²-helperFun₁ G n (p , q , r) = (p , λ i j
    → hcomp (λ k → λ {(i = i0) → rUnitₖ (suc (suc n)) (p j) k
                      ; (i = i1) → rUnitₖ (suc (suc n)) (p (~ j)) k
                      ; (j = i0) → rCancelₖ (suc (suc n)) (q (~ i)) k
                      ; (j = i1) → rCancelₖ (suc (suc n)) (q (~ i)) k})
            (r (~ i) j -[ suc (suc n) ]ₖ q (~ i) ))

  H²K²-helperIso₁ : (G : AbGroup ℓ) (n : ℕ) →
    Iso ∥ (Σ[ p ∈ Ω (EM∙ G (2 +ℕ n)) .fst ]
              Σ[ q ∈ Ω (EM∙ G (2 +ℕ n)) .fst ] Square (sym p) p q q) ∥₂
        ∥ (Σ[ x ∈ EM G (2 +ℕ n) ] (Σ[ p ∈ Ω (EM G (2 +ℕ n) , x) .fst ]
              Σ[ q ∈ Ω (EM G (2 +ℕ n) , x) .fst ] Square (sym p) p q q)) ∥₂
  Iso.fun (H²K²-helperIso₁ G n) = ST.map (0ₖ _ ,_)
  Iso.inv (H²K²-helperIso₁ G n) = ST.rec squash₂
    (uncurry (EM-raw'-elim G (2 +ℕ n)
      (λ _ → isOfHLevelΠ (3 +ℕ n) λ _ → isOfHLevelPlus' {n = suc n} 2 squash₂)
        (EM-raw'-trivElim G (suc n) (λ _
          → isOfHLevelΠ (2 +ℕ n) λ _ → isOfHLevelPlus' {n = n} 2 squash₂)
          ∣_∣₂)))
  Iso.rightInv (H²K²-helperIso₁ G n) = ST.elim (λ _ → isSetPathImplicit)
    (uncurry (EM-raw'-elim G (2 +ℕ n)
      (λ _ → isOfHLevelΠ (3 +ℕ n)
          λ _ → isOfHLevelPlus' {n = suc (suc n)} 1 (squash₂ _ _))
        (EM-raw'-trivElim G (suc n) (λ _ → isOfHLevelΠ (2 +ℕ n)
          λ _ → isOfHLevelPlus' {n = suc n} 1 (squash₂ _ _))
        λ _ → refl)))
  Iso.leftInv (H²K²-helperIso₁ G n) = ST.elim (λ _ → isSetPathImplicit) λ _ → refl

  H²K²-helperIso₂ : (G : AbGroup ℓ) (n : ℕ) →
    Iso ∥ (Σ[ p ∈ Ω (EM∙ G (2 +ℕ n)) .fst ]
              Σ[ q ∈ Ω (EM∙ G (2 +ℕ n)) .fst ] Square (sym p) p q q) ∥₂
        ∥ ((Σ[ p ∈ Ω (EM∙ G (2 +ℕ n)) .fst ]
             p ≡ sym p)) ∥₂
  Iso.fun (H²K²-helperIso₂ G n) = ST.map (H²K²-helperFun₁ G n)
  Iso.inv (H²K²-helperIso₂ G n) = ST.map (λ p → fst p , refl , sym (snd p))
  Iso.rightInv (H²K²-helperIso₂ G n) = ST.elim (λ _ → isSetPathImplicit) λ {(p , r)
    → TR.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
        (λ { P → cong ∣_∣₂ (main p P r)})
      ((F p .fst))}
    where
    F = isConnectedPath (suc n) (isConnectedPath (suc (suc n))
          (isConnectedEM (suc (suc n))) _ _) refl
    main : (p : Ω (EM∙ G (2 +ℕ n)) .fst) → refl ≡ p
      → (r : p ≡ sym p)
      → H²K²-helperFun₁ G n (p , refl , sym r) ≡ (p , r)
    main = (J> λ r → (ΣPathP (refl , sym (rUnit _)
      ∙ λ i j k → rUnitₖ (suc (suc n)) (r j k) i)))
  Iso.leftInv (H²K²-helperIso₂ G n) = ST.elim (λ _ → isSetPathImplicit)
    (uncurry λ p → TR.rec (isProp→isOfHLevelSuc n (isPropΠ (λ _ → squash₂ _ _ )))
      (λ P → uncurry λ q → TR.rec (isProp→isOfHLevelSuc n (isPropΠ (λ _ → squash₂ _ _ )))
        (λ Q x → cong ∣_∣₂ (main p P q Q x))
        (F q .fst))
      (F p .fst))
    where
    F = isConnectedPath (suc n) (isConnectedPath (suc (suc n))
         (isConnectedEM (suc (suc n))) _ _) refl
    main : (p : _) → refl ≡ p →
        (q : _) → refl ≡ q →
        (x : Square (sym p) p q q) →
        (fst (H²K²-helperFun₁ G n (p , q , x))
        , refl
        , (λ i → snd (H²K²-helperFun₁ G n (p , q , x)) (~ i)))
      ≡ (p , q , x)
    main = J> (J> λ p → ΣPathP (refl , (ΣPathP (refl
      , cong sym (sym (rUnit _))
      ∙ λ i j k → rUnitₖ (suc (suc n)) (p j k) i))))

  Iso-H²⁺ⁿ[K²,G]-H²⁺ⁿ[RP²,G] : (G : AbGroup ℓ) (n : ℕ)
    → Iso (coHom (2 +ℕ n) G KleinBottle)
           (coHom (2 +ℕ n) G RP²)
  Iso-H²⁺ⁿ[K²,G]-H²⁺ⁿ[RP²,G] G n =
    compIso
      (setTruncIso
        (compIso K²FunCharacIso
                 (Σ-cong-iso-snd λ p → Σ-cong-iso-snd λ q
                   → Σ-cong-iso-snd λ r → equivToIso flipSquareEquiv)))
      (compIso (invIso (H²K²-helperIso₁ G n))
      (compIso (H²K²-helperIso₂ G n)
               (compIso (invIso (killFirstCompIsoGen G n))
                 (setTruncIso (invIso RP²FunCharacIso)))))

H²[RP²,G]≅H²[K²,G] : (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr 2 G RP²) (coHomGr 2 G KleinBottle)
fst (H²[RP²,G]≅H²[K²,G] G) = isoToEquiv (invIso (Iso-H²⁺ⁿ[K²,G]-H²⁺ⁿ[RP²,G] G 0))
snd (H²[RP²,G]≅H²[K²,G] G) =
  makeIsGroupHom (ST.elim (λ _ → isSetΠ λ _ → isSetPathImplicit)
    (RP²Conn.elim₂ (isConnectedEM 2)
      (λ _ → isPropΠ λ _ → squash₂ _ _)
      (0ₖ 2)
      λ p → ST.elim (λ _ → isSetPathImplicit)
        (RP²Conn.elim₂ (isConnectedEM 2)
              (λ _ → squash₂ _ _)
              (0ₖ 2) λ q
              → cong ∣_∣₂ (funExt λ { point → refl
                                  ; (line1 i) → refl
                                  ; (line2 i) → refl
                                  ; (square i i₁) → refl}))))

H²⁺ⁿ[K²,G]≅H²⁺ⁿ[RP²,G] : (G : AbGroup ℓ) (n : ℕ)
  → AbGroupEquiv (coHomGr (2 +ℕ n) G KleinBottle)
                  (coHomGr (2 +ℕ n) G RP²)
fst (H²⁺ⁿ[K²,G]≅H²⁺ⁿ[RP²,G] G n) = isoToEquiv (Iso-H²⁺ⁿ[K²,G]-H²⁺ⁿ[RP²,G] G n)
snd (H²⁺ⁿ[K²,G]≅H²⁺ⁿ[RP²,G] G zero) = invGroupEquiv (H²[RP²,G]≅H²[K²,G] G) .snd
snd (H²⁺ⁿ[K²,G]≅H²⁺ⁿ[RP²,G] G (suc n)) =
  makeIsGroupHom λ _ _ → isContr→isProp
    (isOfHLevelRetractFromIso 0 (equivToIso (fst (H³⁺ⁿ[RP²,G]≅0 G n)))
      isContrUnit*) _ _

H²[K²,G]≅G/2 : (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr 2 G KleinBottle)
                  (G /^ 2)
H²[K²,G]≅G/2 G = compGroupEquiv (H²⁺ⁿ[K²,G]≅H²⁺ⁿ[RP²,G] G 0) (H²[RP²,G]≅G/2 G)

H³⁺ⁿ[K²,G]≅0 : (n : ℕ) (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr (3 +ℕ n) G KleinBottle) (trivialAbGroup {ℓ})
H³⁺ⁿ[K²,G]≅0 n G = compGroupEquiv (H²⁺ⁿ[K²,G]≅H²⁺ⁿ[RP²,G] G (suc n)) (H³⁺ⁿ[RP²,G]≅0 G n)
