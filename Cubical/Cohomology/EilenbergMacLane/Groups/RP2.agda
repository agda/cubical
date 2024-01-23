{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.RP2 where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.EilenbergMacLane1 as EM1
open import Cubical.HITs.RPn
open import Cubical.HITs.SetQuotients as SQ

open AbGroupStr

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

module RP²Conn {B : (RP² → A) → Type ℓ} where
  elim₁ :
      isConnected 2 A
    → ((x : _) → isProp (B x))
    → (a* : A)
    → ((l1 : a* ≡ a*) (sq : l1 ≡ sym l1)
         → B (RP²Fun a* l1 sq))
    → (x : _) → B x
  elim₁  conA pr a* ind f =
    TR.rec (pr _)
      (λ p → J (λ a* _ → ((l1 : a* ≡ a*) (sq : l1 ≡ sym l1)
                        → B (RP²Fun a* l1 sq)) → B f)
                (λ ind → subst B (characRP²Fun f) (ind _ _))
                p ind)
      (isConnectedPath 1 conA (f point) a* .fst)

  elim₂ : isConnected 3 A
    → ((x : _) → isProp (B x))
    → (a* : A)
    → ((sq : refl {x = a*} ≡ refl)
         → B (RP²Fun a* refl sq))
    → (x : _) → B x
  elim₂ conA pr a* ind =
    elim₁ (isConnectedSubtr 2 1 conA)
      (λ _ → pr _)
      a*
      (λ l1 → TR.rec (isPropΠ (λ _ → pr _))
        (J (λ l1 _ → (sq : l1 ≡ sym l1) → B (RP²Fun a* l1 sq))
          ind)
        (isConnectedPath 1
          (isConnectedPath 2 conA a* a*) refl l1 .fst))

  elim₃ : isConnected 4 A
    → ((x : _) → isProp (B x))
    → (a* : A)
    → (B λ _ → a*)
    → (x : _) → B x
  elim₃ conA pr a* ind =
    elim₂ (isConnectedSubtr 3 1 conA)
      pr
      a*
      λ sq → TR.rec (pr _)
        (J (λ sq _ → B (RP²Fun a* refl sq))
          (subst B (sym (characRP²Fun (λ _ → a*))) ind))
        (isConnectedPath 1
          (isConnectedPath 2
            (isConnectedPath 3 conA _ _) _ _) refl sq .fst)

--- lemmas
Isoℤ/2-morph : {A : Type} (f : A ≃ fst ℤ/2) (0A : A)
  → 0 ≡ fst f 0A → (_+'_ : A → A → A) (-m : A → A)
  → (λ x → x) ≡ -m
  → (e : IsAbGroup 0A _+'_ -m)
  → IsGroupHom (AbGroup→Group (A , abgroupstr 0A _+'_ (λ x → -m x) e) .snd)
                (fst f) ((ℤGroup/ 2) .snd)
Isoℤ/2-morph =
  EquivJ (λ A f → (0A : A) → 0 ≡ fst f 0A → (_+'_ : A → A → A) (-m : A → A)
  → (λ x → x) ≡ -m
  → (e : IsAbGroup 0A _+'_ -m)
  → IsGroupHom (AbGroup→Group (A , abgroupstr 0A _+'_ (λ x → -m x) e) .snd)
                (fst f) ((ℤGroup/ 2) .snd))
  (J> λ _+'_ → J>
    λ e → makeIsGroupHom (ℤ/2-elim (ℤ/2-elim (IsAbGroup.+IdR e fzero)
      (IsAbGroup.+IdL e 1))
      (ℤ/2-elim (IsAbGroup.+IdR e 1)
        (IsAbGroup.+InvR e 1))))

Iso-Ω²K₂-ℤ/2 : Iso (fst ((Ω^ 2) (EM∙ ℤ/2 2))) (fst ℤ/2)
Iso-Ω²K₂-ℤ/2 =
  compIso (congIso (invIso (Iso-EM-ΩEM+1 {G = ℤ/2} 1)))
    (invIso (Iso-EM-ΩEM+1 {G = ℤ/2} 0))



----- H¹(RP²,ℤ/2) ------
H¹[RP²,ℤ/2]→ℤ/2 : coHom 1 ℤ/2 RP² → fst ℤ/2
H¹[RP²,ℤ/2]→ℤ/2 =
  ST.rec isSetFin
    λ f → ΩEM+1→EM-gen 0 _ (cong f line)

ℤ/2→H¹[RP²,ℤ/2] : fst ℤ/2 → coHom 1 ℤ/2 RP²
ℤ/2→H¹[RP²,ℤ/2] x =
  ∣ (λ { point → embase
      ; (line i) → emloop x i
      ; (square i j) → symConst-ℤ/2 1 embase (emloop x) i j}) ∣₂

ℤ/2→H¹[RP²,ℤ/2]→ℤ/2 : (x : fst ℤ/2)
  → H¹[RP²,ℤ/2]→ℤ/2 (ℤ/2→H¹[RP²,ℤ/2] x) ≡ x
ℤ/2→H¹[RP²,ℤ/2]→ℤ/2 = Iso.leftInv (Iso-EM-ΩEM+1 0)

H¹[RP²,ℤ/2]→ℤ/2→H¹[RP²,ℤ/2]  : (f : coHom 1 ℤ/2 RP²)
  → ℤ/2→H¹[RP²,ℤ/2] (H¹[RP²,ℤ/2]→ℤ/2 f) ≡ f
H¹[RP²,ℤ/2]→ℤ/2→H¹[RP²,ℤ/2] =
  ST.elim
    (λ _ → isSetPathImplicit)
    (RP²Conn.elim₁ (isConnectedEM 1)
      (λ _ → squash₂ _ _)
      embase
      λ l sq → cong ∣_∣₂
        (funExt (elimSetRP² (λ _ → hLevelEM _ 1 _ _)
          refl
          (flipSquare (Iso.rightInv (Iso-EM-ΩEM+1 0) l)))))

H¹[RP²,ℤ/2]≅ℤ/2 : AbGroupEquiv (coHomGr 1 ℤ/2 RP²) ℤ/2
fst H¹[RP²,ℤ/2]≅ℤ/2 = isoToEquiv is
  where
  is : Iso _ _
  Iso.fun is = H¹[RP²,ℤ/2]→ℤ/2
  Iso.inv is = ℤ/2→H¹[RP²,ℤ/2]
  Iso.rightInv is = ℤ/2→H¹[RP²,ℤ/2]→ℤ/2
  Iso.leftInv is = H¹[RP²,ℤ/2]→ℤ/2→H¹[RP²,ℤ/2]
snd H¹[RP²,ℤ/2]≅ℤ/2 =
  isGroupHomInv ((invEquiv (fst H¹[RP²,ℤ/2]≅ℤ/2))
    , makeIsGroupHom λ x y → cong ∣_∣₂
      (funExt (elimSetRP² (λ _ → hLevelEM _ 1 _ _)
                refl
                (flipSquare
                  (emloop-comp _ x y
                  ∙ sym (cong₂+₁ (emloop x) (emloop y)))))))

----- H²(RP²,ℤ/2) ------

H²[RP²,ℤ/2]→ℤ/2 : coHom 2 ℤ/2 RP² → fst ℤ/2
H²[RP²,ℤ/2]→ℤ/2 =
  ST.rec isSetFin
    λ f → ΩEM+1→EM-gen 0 _
      (cong (ΩEM+1→EM-gen 1 _)
      ((cong (cong f) square ∙ symConst-ℤ/2 2 _ (sym (cong f line)))))

ℤ/2→H²[RP²,ℤ/2] : fst ℤ/2 → coHom 2 ℤ/2 RP²
ℤ/2→H²[RP²,ℤ/2] x = ∣ RP²Fun (0ₖ 2) refl (Iso.inv Iso-Ω²K₂-ℤ/2 x) ∣₂

H²[RP²,ℤ/2]→ℤ/2-Id : (p : fst ((Ω^ 2) (EM∙ ℤ/2 2)))
                  → H²[RP²,ℤ/2]→ℤ/2 ∣ RP²Fun (0ₖ 2) refl p ∣₂
                  ≡ Iso.fun Iso-Ω²K₂-ℤ/2 p
H²[RP²,ℤ/2]→ℤ/2-Id q = cong (Iso.fun Iso-Ω²K₂-ℤ/2) lem
  where
  lem : q ∙ symConst-ℤ/2 2 _ refl ≡ q
  lem = (λ i → q ∙ transportRefl refl i)
       ∙ sym (rUnit q)

ℤ/2→H²[RP²,ℤ/2]→ℤ/2 : (x : fst ℤ/2)
  → H²[RP²,ℤ/2]→ℤ/2 (ℤ/2→H²[RP²,ℤ/2] x) ≡ x
ℤ/2→H²[RP²,ℤ/2]→ℤ/2 x =
    H²[RP²,ℤ/2]→ℤ/2-Id (Iso.inv Iso-Ω²K₂-ℤ/2 x)
  ∙ Iso.rightInv Iso-Ω²K₂-ℤ/2 x

H²[RP²,ℤ/2]→ℤ/2→H²[RP²,ℤ/2] : (x : coHom 2 ℤ/2 RP²)
  → ℤ/2→H²[RP²,ℤ/2] (H²[RP²,ℤ/2]→ℤ/2 x) ≡ x
H²[RP²,ℤ/2]→ℤ/2→H²[RP²,ℤ/2] =
  ST.elim (λ _ → isSetPathImplicit)
    (RP²Conn.elim₂
      (isConnectedEM 2)
      (λ _ → squash₂ _ _)
      (0ₖ 2)
      λ sq → cong (ℤ/2→H²[RP²,ℤ/2])
               (H²[RP²,ℤ/2]→ℤ/2-Id sq)
            ∙ cong ∣_∣₂ (cong (RP²Fun (snd (EM∙ ℤ/2 2)) refl)
               (Iso.leftInv Iso-Ω²K₂-ℤ/2 sq)))

H²[RP²,ℤ/2]≅ℤ/2 : AbGroupEquiv (coHomGr 2 ℤ/2 RP²) ℤ/2
fst H²[RP²,ℤ/2]≅ℤ/2 = isoToEquiv is
  where
  is : Iso _ _
  Iso.fun is = H²[RP²,ℤ/2]→ℤ/2
  Iso.inv is = ℤ/2→H²[RP²,ℤ/2]
  Iso.rightInv is = ℤ/2→H²[RP²,ℤ/2]→ℤ/2
  Iso.leftInv is = H²[RP²,ℤ/2]→ℤ/2→H²[RP²,ℤ/2]
snd H²[RP²,ℤ/2]≅ℤ/2 =
  Isoℤ/2-morph (fst H²[RP²,ℤ/2]≅ℤ/2)
    _ (sym (H²[RP²,ℤ/2]→ℤ/2-Id refl)
     ∙ cong (H²[RP²,ℤ/2]→ℤ/2 ∘ ∣_∣₂)
            (characRP²Fun (λ _ → 0ₖ 2)))
       _ _ (funExt (ST.elim (λ _ → isSetPathImplicit)
             λ f → cong ∣_∣₂ (funExt
               λ x → sym (-ₖConst-ℤ/2 1 (f x))))) _


----- Hⁿ(RP²,G), n ≥ 3 -----
H³⁺ⁿ[RP²,G]≅G : (n : ℕ) (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr (3 +ℕ n) G RP²) (trivialAbGroup {ℓ})
fst (H³⁺ⁿ[RP²,G]≅G n G) =
  isoToEquiv (isContr→Iso
    (∣ RP²Fun (0ₖ (3 +ℕ n)) refl refl ∣₂
    , (ST.elim (λ _ → isSetPathImplicit)
       (RP²Conn.elim₃
         (isConnectedSubtr 4 n
           (subst (λ x → isConnected x (EM G (3 +ℕ n)))
             (+-comm 4 n)
             (isConnectedEM (3 +ℕ n))))
         (λ _ → squash₂ _ _)
         (0ₖ (3 +ℕ n))
         (cong ∣_∣₂ (characRP²Fun (λ _ → 0ₖ (3 +ℕ n)))))))
    isContrUnit*)
snd (H³⁺ⁿ[RP²,G]≅G n G) = makeIsGroupHom λ _ _ → refl


---- H¹(RP², G) -----
H⁰[RP²,G]≅G : ∀ {ℓ} (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr 0 G RP²) G
H⁰[RP²,G]≅G G =
  H⁰conn (∣ point ∣ₕ , TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
         (elimPropRP² (λ _ → isOfHLevelTrunc 2 _ _) refl)) G

----- H¹(RP², G) ------
module _ {ℓ : Level} (G : AbGroup ℓ) where
  private
    G[2]path : (x : (G [ 2 ]ₜ) .fst) → _+_ (snd G) (fst x) (fst x) ≡ 0g (snd G)
    G[2]path (x , p) = cong (_+_ (snd G) x) (sym (+IdR (snd G) x)) ∙ p

    G[2]path' : (x : (G [ 2 ]ₜ) .fst)  → fst x ≡ -_ (snd G) (fst x)
    G[2]path' x = (sym (+IdR (snd G) _)
                ∙ cong (_+_ (snd G) (fst x)) (sym (+InvR (snd G) (fst x)))
                ∙ (+Assoc (snd G) _ _ _))
               ∙∙ cong (λ w → _+_ (snd G) w (-_ (snd G) (fst x))) (G[2]path x)
               ∙∙ +IdL (snd G) _

  H¹[RP²,G]→G[2] : coHom 1 G RP² → (G [ 2 ]ₜ) .fst
  H¹[RP²,G]→G[2] =
    ST.rec (is-set (snd (G [ 2 ]ₜ)))
      λ f → ΩEM+1→EM-gen {G = G} 0 (f point) (cong f line)
          , cong (_+_ (snd G) (ΩEM+1→EM-gen 0 (f point) (cong f line)))
              (+IdR (snd G) _)
          ∙ sym (ΩEM+1→EM-gen-hom {G = G} 0 (f point) (cong f line) (cong f line))
          ∙ cong (ΩEM+1→EM-gen 0 (f point))
                 (sym (cong-∙ f line line)
               ∙ cong (cong f) (cong (line ∙_) square ∙ rCancel line) )
          ∙ ΩEM+1→EM-gen-refl 0 (f point)

  G[2]→H¹[RP²,G] : (G [ 2 ]ₜ) .fst → coHom 1 G RP²
  G[2]→H¹[RP²,G] g =
    ∣ (λ { point → embase
        ; (line i) → emloop (fst g) i
        ; (square i j) →
           (cong emloop (G[2]path' g)
          ∙ emloop-inv (AbGroup→Group G) (fst g)) i j }) ∣₂

  private
    G[2]≅H¹[RP²,G] : AbGroupEquiv (G [ 2 ]ₜ) (coHomGr 1 G RP²)
    fst G[2]≅H¹[RP²,G] = isoToEquiv (invIso is)
      where
      is : Iso _ _
      Iso.fun is =  H¹[RP²,G]→G[2]
      Iso.inv is =  G[2]→H¹[RP²,G]
      Iso.rightInv is (g , p) =
        Σ≡Prop (λ _ → is-set (snd G) _ _)
        (Iso.leftInv (Iso-EM-ΩEM+1 0) g)
      Iso.leftInv is = ST.elim (λ _ → isSetPathImplicit)
        (RP²Conn.elim₁ (isConnectedEM 1) (λ _ → squash₂ _ _)
          embase
          λ p q → cong ∣_∣₂
            (funExt (elimSetRP² (λ _ → emsquash _ _)
            refl
            (flipSquare (Iso.rightInv (Iso-EM-ΩEM+1 {G = G} 0) p)))))
    snd G[2]≅H¹[RP²,G] = makeIsGroupHom
      λ x y → cong ∣_∣₂
        (funExt (elimSetRP² (λ _ → emsquash _ _) refl
          (flipSquare
            (EM→ΩEM+1-hom {G = G} 0 (fst x) (fst y)
            ∙ sym (cong₂+₁ (emloop (fst x)) (emloop (fst y)))))))


  H¹[RP²,G]≅G[2] : AbGroupEquiv (coHomGr 1 G RP²) (G [ 2 ]ₜ)
  H¹[RP²,G]≅G[2] = invGroupEquiv G[2]≅H¹[RP²,G]

----- H²(RP², G) ------
module _ (G : AbGroup ℓ) where
  private
    ΩEM+1→EM-sym' : (p : fst (Ω (EM∙ G 2)))
      → ΩEM+1→EM 1 (sym p) ≡ (-ₖ ΩEM+1→EM 1 p)
    ΩEM+1→EM-sym'  p =
      ΩEM+1→EM-sym (suc zero) p
        ∙ (sym (rUnitₖ 1 ((-ₖ ΩEM+1→EM 1 p)))
        ∙∙ cong ((-ₖ ΩEM+1→EM 1 p) +ₖ_) (sym (ΩEM+1→EM-sym (suc zero) refl))
        ∙∙ rUnitₖ 1 ((-ₖ ΩEM+1→EM 1 p)))

    ΩEM+1→EM-sym'-refl : ΩEM+1→EM-sym' refl ≡ refl
    ΩEM+1→EM-sym'-refl =
      (λ i → ΩEM+1→EM-sym (suc zero) refl ∙ rUnit (sym (ΩEM+1→EM-sym (suc zero) refl)) (~ i))
      ∙ rCancel _

    G/2-ord2 : (x : fst (G /^ 2)) → (- snd (G /^ 2)) x ≡ x
    G/2-ord2 = SQ.elimProp (λ _ → SQ.squash/ _ _)
      λ a → eq/ _ _ ∣ snd G .-_ a
                    , cong (snd G ._+_ (snd G .-_ a)) (+IdR (snd G) _) ∣₁

  open EM2 (G /^ 2) G/2-ord2
  killFirstCompIsoGen : (n : ℕ)
    → Iso ∥ (Σ[ x ∈ EM G (2 +ℕ n) ] (Σ[ p ∈ x ≡ x ] p ≡ sym p)) ∥₂
                       ∥ (Σ[ p ∈ Ω (EM∙ G (2 +ℕ n)) .fst ] p ≡ sym p) ∥₂
  Iso.fun (killFirstCompIsoGen n) =
    ST.rec squash₂
      (uncurry (TR.elim (λ _ → isOfHLevelPlus {n = 2 +ℕ n} 2
        (isOfHLevelPlus' {n = n} 2 (isSetΠ λ _ → squash₂)))
        (EM-raw'-trivElim G (suc n)
          (λ _ → isOfHLevelΠ (suc (suc n))
            λ _ → isOfHLevelPlus' {n = n} 2 squash₂) ∣_∣₂)))
  Iso.inv (killFirstCompIsoGen n) = ST.map (0ₖ (2 +ℕ n) ,_)
  Iso.rightInv (killFirstCompIsoGen n) = ST.elim (λ _ → isSetPathImplicit) λ _ → refl
  Iso.leftInv (killFirstCompIsoGen n) = ST.elim (λ _ → isSetPathImplicit)
    (uncurry (TR.elim (λ _ → isProp→isOfHLevelSuc (3 +ℕ n)
                        (isPropΠ (λ _ → squash₂ _ _)))
      (EM-raw'-trivElim G (suc n) (λ _ → isProp→isOfHLevelSuc (suc n)
        (isPropΠ λ _ → squash₂ _ _ ))
        λ _ → refl)))

  H²RP²-Iso₁ : Iso (coHom 2 G RP²) ∥ (Σ[ p ∈ Ω (EM∙ G 2) .fst ] p ≡ sym p) ∥₂
  H²RP²-Iso₁ = compIso (setTruncIso RP²FunCharacIso) (killFirstCompIsoGen 0)

  H²RP²-Iso₂ : Iso ((Σ[ p ∈ Ω (EM∙ G 2) .fst ] p ≡ sym p)) (Σ[ p ∈ EM G 1 ] p ≡ -ₖ p)
  H²RP²-Iso₂ = (Σ-cong-iso (invIso (Iso-EM-ΩEM+1 1))
    λ x → compIso (congIso (invIso (Iso-EM-ΩEM+1 1)))
            (equivToIso (compPathrEquiv (ΩEM+1→EM-sym' x))))

  RP²Fun-pres+ : (p q : (Ω^ 2) (EM∙ G 2) .fst) (x : _)
    → RP²Fun _ _ p x +[ 2 ]ₖ RP²Fun _ _ q x ≡ RP²Fun _ _ (p ∙ q) x
  RP²Fun-pres+ p q point = refl
  RP²Fun-pres+ p q (line i) j = 0ₖ 2
  RP²Fun-pres+ p q (square i j) k =
    hcomp (λ r → λ {(i = i0) → lem3 k j r
                   ; (i = i1) → lem2 k (~ r) j
                   ; (j = i0) → p (i ∨ ~ k) r
                   ; (j = i1) → p (~ i ∧ k) (~ r)
                   ; (k = i0) → cong₂+₂ 0 (p i) (q i) (~ r) j
                   ; (k = i1) → lem1 _ refl p (sym q) r i j})
          ((p i ∙ q i) j)
    where
    lem1 : ∀ {ℓ} {A : Type ℓ} (x : A) (p : x ≡ x) (P Q : refl ≡ p)
      → Cube (λ i j → (P i ∙ Q (~ i)) j) (P ∙ sym Q)
              (λ k → compPath-filler refl p (~ k))
              (λ k → compPath-filler' p refl (~ k))
              (λ i j → P j i) λ i j → P (~ j) (~ i)
    lem1 x = J> λ Q → (λ i j k → lUnit (Q (~ j)) (~ i) k) ▷ lUnit (sym Q)

    lem2 : cong₂+₂ {G = G} 0 refl refl ≡ rUnit refl
    lem2 = sym (rUnit _)

    lem3 : Cube (λ j r → cong₂+₂ {G = G} 0 refl refl (~ r) j)
              (λ j r → compPath-filler (refl {x = 0ₖ 2}) refl (~ r) j)
              (λ k r → p (~ k) r) (λ k r → p k (~ r))
              (λ j i → (rUnit (refl {x = 0ₖ 2}) i1) i)
              (λ _ _ → 0ₖ 2)
    lem3 = (λ i j r → lem2 i (~ r) j)
      ◁ (λ k j r →
        hcomp (λ i → λ {(j = i0) → p (~ k) r
                   ; (j = i1) → p k (~ r)
                   ; (r = i0) → rUnit (λ _ → 0ₖ 2) i j
                   ; (r = i1) → 0ₖ 2
                   ; (k = i0) → rUnit (λ _ → 0ₖ 2) (i ∧ ~ r) j
                   ; (k = i1) → rUnit (λ _ → 0ₖ 2) (i ∧ ~ r) j})
         (((sym≡flipSquare p) ∙ flipSquare≡cong-sym p) j k r))

  H²RP²-Iso₁,₂-charac : (p : (Ω^ 2) (EM∙ G 2) .fst)
    → ST.map (Iso.fun H²RP²-Iso₂) (Iso.fun H²RP²-Iso₁ ∣ RP²Fun _ _ p ∣₂)
     ≡ ∣ embase , (cong (ΩEM+1→EM 1) p) ∣₂
  H²RP²-Iso₁,₂-charac p = cong ∣_∣₂ (ΣPathP (refl
    , (λ i → cong (ΩEM+1→EM {G = G} 1) p ∙ ΩEM+1→EM-sym'-refl i)
     ∙ sym (rUnit (cong (ΩEM+1→EM 1) p))))

  H²RP²-Iso₁,₂+ : (p q : (Ω^ 2) (EM∙ G 2) .fst)
    → ST.map (Iso.fun H²RP²-Iso₂) (Iso.fun H²RP²-Iso₁ (∣ RP²Fun _ _ p ∣₂ +ₕ ∣ RP²Fun _ _ q ∣₂))
    ≡ ∣ embase , cong (ΩEM+1→EM 1) p  ∙ cong (ΩEM+1→EM 1) q ∣₂
  H²RP²-Iso₁,₂+ p q = cong (ST.map (Iso.fun H²RP²-Iso₂) ∘ Iso.fun H²RP²-Iso₁)
    (cong ∣_∣₂ (funExt (RP²Fun-pres+ p q)))
    ∙ H²RP²-Iso₁,₂-charac (p ∙ q)
    ∙ cong ∣_∣₂ (ΣPathP (refl , cong-∙ (ΩEM+1→EM 1) p q))

  H²RP²-Iso₃→ : (p : EM G 1) → (p ≡ -[ 1 ]ₖ p) → fst (G /^ 2)
  H²RP²-Iso₃→ = EM1.elimSet (AbGroup→Group G) (λ _ → isSetΠ λ _ → squash/)
    (λ p → [ ΩEM+1→EM 0 p ])
    λ g → toPathP (funExt λ q
      → cong [_] (transportRefl _
                 ∙ cong (ΩEM+1→EM 0)
                    ((λ j → transp (λ i → Path (EM G 1) (emloop g (~ i ∧ ~ j)) (emloop g (i ∨ j))) j
                       (doubleCompPath-filler (emloop g) q (emloop g) j))
                  ∙ doubleCompPath≡compPath _ _ _
                  ∙ cong (emloop g ∙_) (isCommΩEM {G = G} 0 q (emloop g))
                  ∙ assoc (emloop g) (emloop g) q)
                  ∙ ΩEM+1→EM-hom 0 (emloop g ∙ emloop g) q)
               ∙ eq/ _ _ ∣ g
                       , cong (snd G ._+_ g) (+IdR (snd G) _)
                        ∙ sym (+IdR (snd G) (snd G ._+_ g g))
                        ∙ cong₂ (snd G ._+_)
                            (sym (Iso.leftInv (Iso-EM-ΩEM+1 0) _)
                             ∙ cong (ΩEM+1→EM 0) (emloop-comp _ g g))
                            (sym (+InvR (snd G) (ΩEM+1→EM 0 q)))
                        ∙ +Assoc (snd G) _ _ _ ∣₁)

  H²RP²-Iso₃ : Iso ∥ (Σ[ p ∈ EM G 1 ] p ≡ -ₖ p) ∥₂ (fst (G /^ 2))
  Iso.fun H²RP²-Iso₃ = ST.rec squash/ (uncurry H²RP²-Iso₃→)
  Iso.inv H²RP²-Iso₃ =
    SQ.elim (λ _ → squash₂) (λ a → ∣ embase , emloop a ∣₂)
            λ a b → PT.rec (squash₂ _ _)
              (uncurry λ x y → cong ∣_∣₂ (ΣPathP ((emloop x)
              , compPathL→PathP
                (cong₂ _∙_ (sym (emloop-inv _ x))
                (cong (emloop a ∙_) (sym (emloop-inv _ x))
                ∙ sym (EM→ΩEM+1-hom {G = G} 0 a (AbGroupStr.-_ (snd G) x)))
                ∙ sym (EM→ΩEM+1-hom {G = G} 0 _ _)
                ∙ cong emloop (cong (_+_ (snd G) (AbGroupStr.-_ (snd G) x))
                              (+Comm (snd G) _ _)
                ∙ +Assoc (snd G) _ _ _
                ∙ cong (λ w → _+_ (snd G) w a)
                    (sym (GroupTheory.invDistr (AbGroup→Group G) x x)
                   ∙ cong (AbGroupStr.-_ (snd G))
                     (cong (snd G ._+_ x ) (sym (+IdR (snd G) _)) ∙ y)
                   ∙ GroupTheory.invDistr (AbGroup→Group G) a _
                   ∙ cong (λ w → _+_ (snd G) w (AbGroupStr.-_ (snd G) a))
                          (GroupTheory.invInv (AbGroup→Group G) b))
                ∙ (sym (+Assoc (snd G) _ _ _)
                ∙ cong (_+_ (snd G) b) (+InvL (snd G) a))
                ∙ +IdR (snd G) b)))))
  Iso.rightInv H²RP²-Iso₃ = SQ.elimProp (λ _ → squash/ _ _)
    λ a → cong [_] (Iso.leftInv (Iso-EM-ΩEM+1 0) a)
  Iso.leftInv H²RP²-Iso₃ = ST.elim (λ _ → isSetPathImplicit)
    (uncurry (EM1.elimProp (AbGroup→Group G) (λ _ → isPropΠ λ _ → squash₂ _ _)
      λ p → cong ∣_∣₂ (ΣPathP (refl , (Iso.rightInv (Iso-EM-ΩEM+1 0) p)))))

  H²[RP²,G]≅G/2 : AbGroupEquiv (coHomGr 2 G RP²) (G /^ 2)
  fst H²[RP²,G]≅G/2 = isoToEquiv is
    where
    is : Iso _ _
    is = compIso (compIso H²RP²-Iso₁ (setTruncIso H²RP²-Iso₂)) H²RP²-Iso₃
  snd H²[RP²,G]≅G/2 =
    makeIsGroupHom (ST.elim2 (λ _ _ → isOfHLevelPath 2 squash/ _ _)
      (RP²Conn.elim₂ (isConnectedEM 2) (λ _ → isPropΠ λ _ → squash/ _ _)
        (0ₖ 2) λ p → RP²Conn.elim₂ (isConnectedEM 2) (λ _ → squash/ _ _)
        (0ₖ 2) λ q → cong (Iso.fun H²RP²-Iso₃) (H²RP²-Iso₁,₂+ p q)
                   ∙ cong [_] (ΩEM+1→EM-hom 0 (cong (ΩEM+1→EM 1) p)
                                              (cong (ΩEM+1→EM 1) q))
                   ∙ cong₂ ((G /^ 2) .snd ._+_)
                       (cong (Iso.fun H²RP²-Iso₃) (sym (H²RP²-Iso₁,₂-charac p)))
                       (cong (Iso.fun H²RP²-Iso₃) (sym (H²RP²-Iso₁,₂-charac q)))))

  H³⁺ⁿ[RP²,G]≅0 : (n : ℕ) → AbGroupEquiv (coHomGr (3 +ℕ n) G RP²) (trivialAbGroup {ℓ})
  fst (H³⁺ⁿ[RP²,G]≅0 n) = isContr→≃Unit* (0ₕ _
                        , ST.elim (λ _ → isSetPathImplicit)
                         (RP²Conn.elim₃ (isConnectedSubtr 4 n
                           (subst (λ k → isConnected k (EM G (3 +ℕ n)))
                                  (+-comm 4 n) (isConnectedEM (3 +ℕ n))))
                             (λ _ → squash₂ _ _) (0ₖ _) refl))
  snd (H³⁺ⁿ[RP²,G]≅0 n) = makeIsGroupHom λ _ _ → refl
