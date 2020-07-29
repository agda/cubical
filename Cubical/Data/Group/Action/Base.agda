{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Action.Base where

open import Cubical.Core.Everything
open import Cubical.Data.Group.Base
open import Cubical.Data.Group.Higher
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Homotopy.Loopspace
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma hiding (comp)

private
  variable
    ℓ ℓ' ℓ'' : Level

{-- Group action of a group G on set X with explicit axioms
record ActionType' {ℓ : Level} (G : Group ℓ) (X : Type ℓ) (setStruc : isSet X) : Type ℓ where
  field
    fun : (Group.type G) → X → X
    identity : (x : X) → (fun (isGroup.id (Group.groupStruc G)) x) ≡ x
    compatibility : (g h : Group.type G) → (x : X) → (fun ((isGroup.comp (Group.groupStruc G)) g h) x) ≡ (fun g (fun h x))
--}

{-- The quick way of defining an action of a 1-Group G on some a : A via the functions on BG --}
BAction : (BG : 1BGroup ℓ) {A : Type ℓ'} (a : A) → Type (ℓ-max ℓ ℓ')
BAction BG {A = A} a = BGroup.base BG →∙ (A , a)

{-- The trivial Action of G on a is reflₐ at every point --}
BActionTriv : (BG : 1BGroup ℓ) {A : Type ℓ'} (a : A) → BAction BG a
BActionTriv _ a = (λ _ → a) , refl

{-- a map of G-types from a to b is just a function (z : BG) → α z → α' z --}
BActionHom : {BG : 1BGroup ℓ} {a : Type ℓ'} {b : Type ℓ''} (α : BAction BG a) (α' : BAction BG b) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
BActionHom {BG = BG} (α , _) (α' , _) = (z : typ (BGroup.base BG)) → α z → α' z

{-- invariants / homotopy fixed points --}
BActionInv : {BG : 1BGroup ℓ} {a : Type ℓ'} (α : BAction BG a) → Type (ℓ-max ℓ ℓ')
BActionInv {BG = BG} (α , _) = (z : typ (BGroup.base BG)) → α z

{-- coinvariants / homotopy quotient --}
BActionCoinv : {BG : 1BGroup ℓ} {a : Type ℓ'} (α : BAction BG a) → Type (ℓ-max ℓ ℓ')
BActionCoinv {BG = BG} (α , _) = Σ[ z ∈ typ (BGroup.base BG) ] α z

{-- canonical right action of a group on itself --}
-- BActR : (BG : 1BGroup ℓ) → BAction BG (fst (carrier BG))
-- BActR (bgroup base _ _) = (λ x → (snd base) ≡ x ) , refl

{-- adjoint action of a group on itself --}
-- BActAdj : (BG : 1BGroup ℓ) → BAction BG (fst (carrier BG))
-- BActAdj (bgroup base _ _) = (λ x → {!!}) , {!!}


{-- this can be used to actually compute the action of an element --}
BAct : {BG : 1BGroup ℓ} {A : Pointed ℓ'} (α : BAction BG (snd A)) (g : fst (carrier BG)) → fst (Ω A)
BAct (α , α∙) g = sym α∙ ∙∙ cong α g ∙∙ α∙

{-- if a is a sort we can go on and compute the transformation of a --}
BAct' : {BG : 1BGroup ℓ} {a : Type ℓ'} (α : BAction BG a) (g : fst (carrier BG)) → a → a
BAct' (α , α∙) g x = (pathToEquiv (sym α∙ ∙∙ cong α g ∙∙ α∙)) .fst x


{-- left Group action of a group G on set X with explicit axioms --}
record lAction {ℓ ℓ' : Level} (G : Group ℓ) (X : Group ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor laction
  field
    act : (Group.type G) → (Group.type X) → (Group.type X)
    identity : (x : Group.type X) → (act (isGroup.id (Group.groupStruc G)) x) ≡ x
    coh : (g h : Group.type G) → (x : Group.type X) → (act ((isGroup.comp (Group.groupStruc G)) g  h) x) ≡ act g (act h x)
    hom : (g : Group.type G) → isMorph X X (act g)

module lActionProperties {ℓ ℓ' : Level} (G : Group ℓ) (X : Group ℓ') ((laction act identity coh hom) : lAction G X) where
  -- notation
  1X = isGroup.id (Group.groupStruc X)

  -- identities
  actg1≡1 : (g : Group.type G) → act g 1X ≡ 1X
  actg1≡1 g = morphId {G = X} {H = X} ((λ z → act g z) , hom g)


{-- right Group action of a group G on set X with explicit axioms --}
record rAction {ℓ ℓ' : Level} (G : Group ℓ) (X : Group ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor raction
  field
    act : (Group.type X) → (Group.type G) → (Group.type X)
    identity : (x : Group.type X) → (act x (isGroup.id (Group.groupStruc G))) ≡ x
    coh : (g h : Group.type G) → (x : Group.type X) → (act x ((isGroup.comp (Group.groupStruc G)) g  h)) ≡ act (act x g) h
    hom : (g : Group.type G) → isMorph X X (λ x → act x g)

{- the right adjoint action of a group on itself, (x , g) ↦ (g⁻¹ x) g -}
{-
rActionAdj : {ℓ : Level} (G : Group ℓ) → rAction G G
rActionAdj (group type set (group-struct id inv _∘_ lUnit rUnit assoc lCancel rCancel)) =
  raction
    (λ x g → ((inv g) ∘ x) ∘ g)
    (λ g →
      rUnit (inv id ∘ g) ∙∙
      sym (lUnit (inv id ∘ g)) ∙∙
      sym (assoc id (inv id) g) ∙∙
      cong (λ x → x ∘ g) (rCancel id) ∙∙
      lUnit g)
    (λ g h x →
      (cong (λ z → (z ∘ x) ∘ (g ∘ h)) (invComp {_} {G} g h)) ∙∙
      cong (_∘ (g ∘ h)) (assoc (inv h) (inv g) x) ∙∙
      assoc (inv h) (inv g ∘ x) (g ∘ h) ∙∙
      cong ((inv h) ∘_) (sym (assoc (inv g ∘ x) g h)) ∙∙
      sym (assoc (inv h) ((inv g ∘ x) ∘ g) h))
    λ g x x' →
      cong (λ z → (inv g ∘ (x ∘ z)) ∘ g ) (sym (lUnit x')) ∙∙
      cong (λ z → (inv g ∘ (x ∘ (z ∘ x'))) ∘ g) (sym (rCancel g)) ∙∙
      cong (λ z → (inv g ∘ (x ∘ z)) ∘ g) (assoc g (inv g) x') ∙∙
      cong (λ z → (inv g ∘ z) ∘ g) (sym (assoc x g (inv g ∘ x'))) ∙∙
      cong (_∘ g) (sym (assoc (inv g) (x ∘ g) (inv g ∘ x'))) ∙∙
      assoc (inv g ∘ (x ∘ g)) (inv g ∘ x') g ∙∙
      cong (_∘ ((inv g ∘ x') ∘ g)) (sym (assoc (inv g) x g))
    where
      G = group type set (group-struct id inv _∘_ lUnit rUnit assoc lCancel rCancel)
-}
{-- the left adjoint action of a group on a normal subgroup (g , n) ↦ (g n) g⁻¹ -}
lActionAdjSubgroup : {ℓ ℓ' : Level} (G : Group ℓ) (N : Subgroup ℓ' G) (isNormal : isNormalSubgroup G N) → lAction G (Subgroup→Group N)
lActionAdjSubgroup {ℓ' = ℓ'}
  (group type set (group-struct id inv _∘_ lUnit rUnit assoc lCancel rCancel))
  (subgroup P subId compClosed invClosed)
  isNormal
  = laction
  (λ g n → (g ∘ fst n) ∘ (inv g) , isNormal g n)
  (λ n → ΣPathP (p1 n , isProp→PathP (λ i → snd (P (p1 n i))) (isNormal id n) (snd n)))
  (λ g h n → ΣPathP ((p2 g h n)
    , isProp→PathP
      (λ i → snd (P (p2 g h n i)))
      (isNormal (g ∘ h) n) (isNormal g (((h ∘ fst n) ∘ inv h) , isNormal h n))))
  λ g n n' → ΣPathP (p3 g n n' , isProp→PathP
      (λ i → snd (P (p3 g n n' i)))
      (isNormal g (n ∘N n'))
      (snd ((((g ∘ fst n) ∘ inv g) , isNormal g n) ∘N (((g ∘ fst n') ∘ inv g) , isNormal g n'))))
  where
    G = group type set (group-struct id inv _∘_ lUnit rUnit assoc lCancel rCancel)
    N : Subgroup ℓ' G
    N = subgroup P subId compClosed invClosed
    NGrp = Subgroup→Group N
    typeN = Group.type NGrp
    _∘N_ = isGroup.comp (Group.groupStruc NGrp)
    rUnitN = isGroup.rUnit (Group.groupStruc NGrp)
    idN = isGroup.id (Group.groupStruc NGrp)
    abstract
      p1 = λ (n : typeN) → cong ((id ∘ (fst n)) ∘_) (invId G) ∙∙ rUnit (id ∘ (fst n)) ∙∙ lUnit (fst n)
      p2 = λ (g h : type) (n : typeN) →
        cong (((g ∘ h) ∘ fst n) ∘_) (invComp {_} {G} g h)
        ∙∙ sym (assoc ((g ∘ h) ∘ fst n) (inv h) (inv g))
        ∙∙ cong (_∘ inv g) ((cong (_∘ inv h) (assoc g h (fst n))) ∙ assoc g (h ∘ fst n) (inv h))
      p3' = λ (g : type) (n : typeN) → (sym (rUnit (fst n))) ∙ (cong ((fst n) ∘_) (sym (lCancel g)))
      p3 = λ (g : type) (n n' : typeN) →
        (cong
          (λ z → (g ∘ fst (z ∘N n')) ∘ inv g)
          (ΣPathP
            (p3' g n ,
            isProp→PathP
              (λ i → snd (P (p3' g n i)))
              (snd n)
              (snd (n ∘N (inv g ∘ g , subst (λ x → fst (P x)) (sym (lCancel g)) subId)))))) ∙∙
        cong (λ z → (g ∘ (z ∘ (fst n'))) ∘ inv g) (sym (assoc (fst n) (inv g) g)) ∙∙
        cong (λ z → (g ∘ z) ∘ inv g) (assoc ((fst n) ∘ inv g) g (fst n')) ∙∙
        cong (_∘ inv g) (sym (assoc g (fst n ∘ inv g) (g ∘ fst n'))) ∙∙
        assoc (g ∘ (fst n ∘ inv g)) (g ∘ fst n') (inv g) ∙
        cong (_∘ ((g ∘ fst n') ∘ (inv g))) (sym (assoc g (fst n) (inv g)))

{- this is correct but currently not needed
rAction→lAction : {ℓ : Level} {G : Group ℓ} {H : Group ℓ'}  (α : rAction G H) → lAction G H
rAction→lAction {G = group typeG setG (group-struct idG invG _∘G_ lUnitG rUnitG assocG lCancelG rCancelG)}
  {H = group typeH setH (group-struct idH invH _∘H_ lUnitH rUnitH assocH lCancelH rCancelH)}
  (raction act identity coh hom)
  = laction
    (λ g h → act h (invG g))
    (λ h → cong (act h) (invId G) ∙ (identity h))
    (λ g h x → (cong (act x) (invComp {_} {G} g h)) ∙ coh (invG h) (invG g) x)
    λ g h h' → hom (invG g) h h'
    where
      G = group typeG setG (group-struct idG invG _∘G_ lUnitG rUnitG assocG lCancelG rCancelG)
-}
{--
conj : {ℓ : Level} {A : Type ℓ} {x y : A} (p : x ≡ y) → (sym p) ∙∙ refl ∙∙ p ≡ refl
conj p = {!doubleCompPath-filler (sym p) refl p!}

BAction→Action : {ℓ ℓ' : Level} {BG : 1BGroup ℓ} {BX : 1BGroup ℓ'} (α : BAction BG (fst (carrier BX))) → Action (BGroup→Group BG) (BGroup→Group BX)
BAction→Action α = action (λ g x → (pathToEquiv (BAct α g)) .fst x) (λ x →  (cong (λ a → {!!}) (conj (snd α))) ∙ {!!}) {!!} {!!}
--}
