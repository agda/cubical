{- This file contains a direct proof that the Brunerie number (the
number n s.t. π₄(S³)≅ℤ/nℤ) is 2, not relying on any of the more
advanced constructions in chapters 4-6 in Brunerie's thesis (but still
using chapters 1-3 for the construction). The Brunerie number is defined via

S³ ≃ S¹ * S¹ -ᵂ→ S² ∨ S² -ᶠᵒˡᵈ→ S²

where * denotes the join, ∨ denotes the wedge sum, W is the Whitehead
map (see joinTo⋁ in Cubical.Homotopy.Whitehead) and the final map is
just the folding map. η := ∣ fold ∘ W ∣₀ defines an element of π₃(S²).
The (absolute value) of the Brunerie number is given by the absolute
value of ϕ(η) for any iso π₃(S²)≅ℤ. The reason it's hard to prove
ϕ(η) = ± 2 directly is mainly because the equivalence S³ ≃ S¹ * S¹
complicates things. In this file, we try to work around this problem.

The proof goes as follows.

1. Define π₃*(A) := ∥ S¹ * S¹ →∙ A ∥₀ and define explicitly an
addition on this type. Prove that the equivalence π₃(A) ≃ π₃*(A) is
structure preserving, thereby giving a group structure on π₃*(A) and a
group iso π₃*(A) ≅ π₃(A)

2. Under this iso, η gets mapped to η₁ (by construction) defined by
S¹ * S¹ -ᵂ→ S² ∨ S² -ᶠᵒˡᵈ→ S²
which is much easier to work with.

3. Define a sequence of equivalences
π₃*(S²) ≅ π₃*(S¹ * S¹) ≅ π₃*(S³) ≅ π₃(S³) ≅ ℤ
and trace η₁ in each step, proving that it ends up at -2. It turns out
that that the iso S³ ≃ S¹ * S¹, which has been relatively explicitly
defined in Cubical.HITs.Sphere.Properties, kills off a good deal of
``annoying'' terms on the way, making the proof rather straightforward.

4. Conclude that π₄(S³) ≅ ℤ/2ℤ.

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.QuickProof where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Homotopy.Hopf
open import Cubical.Homotopy.Whitehead using (joinTo⋁)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.HopfInvariant.HopfMap using (hopfMap≡HopfMap')
-- Only imports a simple equality of two constructions of the Hopf map.
open import Cubical.Homotopy.Group.Pi4S3.BrunerieNumber
  using (fold∘W ; coFib-fold∘W∙ ; π₄S³≅π₃coFib-fold∘W∙ ; S³→S²→Pushout→Unit)
-- Only imports definitions/proofs from chapter 1-3 in Brunerie's thesis

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Int
  renaming (ℤ to Z ; _·_ to _·Z_ ; _+_ to _+Z_)

open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Join hiding (joinS¹S¹→S³)
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.SetTruncation
  renaming (rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.Truncation renaming (rec to trRec)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Instances.IntMod

open S¹Hopf
open Iso
open GroupStr

private
  variable
    ℓ : Level
    A B : Pointed ℓ

-- Some abbreviations and simple lemmas
private
  σ₁ = σ (S₊∙ 1)
  σ₂ = σ (S₊∙ 2)

  σ-filler : ∀ {ℓ} {A : Type ℓ} (x y : A) (i j : I) → Susp A
  σ-filler x y i j = compPath-filler (merid x) (sym (merid y)) i j

  to3ConnectedId : {f g : A →∙ B}
    → (isConnected 3 (typ B)) → fst f ≡ fst g → ∣ f ∣₂ ≡ ∣ g ∣₂
  to3ConnectedId {f = f} {g = g} con p =
    trRec (squash₂ _ _)
      (λ q → cong ∣_∣₂ (ΣPathP (p , q)))
      (fst (isConnectedPathP 1 (isConnectedPath 2 con _ _) (snd f) (snd g)))

  connS³ : isConnected 3 (S₊ 3)
  connS³ =
    isConnectedSubtr 3 1 (sphereConnected 3)

  con-joinS¹S¹ : isConnected 3 (join S¹ S¹)
  con-joinS¹S¹ =
    (isConnectedRetractFromIso 3
        (IsoSphereJoin 1 1)
        (isConnectedSubtr 3 1 (sphereConnected 3)))

-- Key goal: prove that the following element of π₃(S²) gets mapped to -2
η : π' 3 (S₊∙ 2)
η = fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ id∙ (S₊∙ 3) ∣₂

{- Step 1. Define an addition on π₃*(A) := ∥ S¹ * S¹ →∙ A ∥₀ -}
-- On the underlying function spaces.
_+join_ : (f g : (join S¹ S¹ , inl base) →∙ A)
       → (join S¹ S¹ , inl base) →∙ A
fst (f +join g) (inl x) = fst f (inl x)
fst (f +join g) (inr x) = fst g (inr x)
fst (f +join g) (push a b i) =
  (cong (fst f) (push a b ∙ sym (push base b))
  ∙∙ snd f ∙ sym (snd g)
  ∙∙ cong (fst g) (push base base ∙∙ sym (push a base) ∙∙ push a b)) i
snd (f +join g) = snd f

-- Homotopy group version
_π₃*+_ : (f g : ∥ (join S¹ S¹ , inl base) →∙ S₊∙ 2 ∥₂)
      → ∥ (join S¹ S¹ , inl base) →∙ S₊∙ 2 ∥₂
_π₃*+_ = sRec2 squash₂ λ x y → ∣ x +join y ∣₂

-- transferring between π₃ and π₃*
-- (homotopy groups defined in terms of S¹ * S¹)
joinify :  S₊∙ 3 →∙ A → (join S¹ S¹ , inl base) →∙ A
fst (joinify f) x = fst f (joinS¹S¹→S³ x)
snd (joinify f) = snd f

disjoin : (join S¹ S¹ , inl base) →∙ A → S₊∙ 3 →∙ A
fst (disjoin f) = λ x → fst f (Iso.inv (IsoSphereJoin 1 1) x)
snd (disjoin f) = snd f


-- joinify is structure preserving
+join≡∙Π : (f g : S₊∙ 3 →∙ A)
         → joinify (∙Π f g)
         ≡ (joinify f +join joinify g)
+join≡∙Π f' g' =
  ΣPathP ((funExt (λ { (inl x) → sym fp
                     ; (inr x) → sym gp ∙ cong g (merid north)
                     ; (push a b i) j → main a b j i}))
        , λ i j → fp (j ∨ ~ i))
  where
  f = fst f'
  g = fst g'

  fp = snd f'
  gp = snd g'

  path-lem : ∀ {ℓ} {A : Type ℓ} {x y z w u : A}
       (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ u)
    → (refl ∙∙ p ∙∙ q) ∙ (r ∙∙ s ∙∙ refl)
     ≡ (p ∙∙ (q ∙ r) ∙∙ s)
  path-lem p q r s =
       cong ((p ∙ q) ∙_) (sym (compPath≡compPath' r s))
    ∙∙ sym (∙assoc p q (r ∙ s))
    ∙∙ cong (p ∙_) (∙assoc q r s)
     ∙ sym (doubleCompPath≡compPath p (q ∙ r) s)

  main-helper : (a b : S¹)
    → Square ((refl ∙∙ cong f (σ₂ (S¹×S¹→S² a b)) ∙∙ fp)
             ∙ (sym gp ∙∙ cong g (σ₂ (S¹×S¹→S² a b)) ∙∙ refl))
             ((cong f (merid (S¹×S¹→S² a b))
             ∙ sym (cong f (merid north)))
               ∙∙ (fp ∙ sym gp)
               ∙∙ cong g (merid (S¹×S¹→S² a b)))
           (λ _ → f north)
           (cong g (merid north))
  main-helper a b =
    path-lem (cong f (σ₂ (S¹×S¹→S² a b)))  fp (sym gp)
             (cong g (σ₂ (S¹×S¹→S² a b)))
          ◁ lem
    where
    lem : PathP (λ i → f north ≡ cong g (merid north) i)
              ((λ i → f (σ₂ (S¹×S¹→S² a b) i))
                    ∙∙ fp ∙ (sym gp) ∙∙
               (cong g (σ₂ (S¹×S¹→S² a b))))
              ((cong f (merid (S¹×S¹→S² a b)) ∙ sym (cong f (merid north)))
               ∙∙ fp ∙ sym gp
               ∙∙ cong g (merid (S¹×S¹→S² a b)))
    lem i j =
      hcomp (λ k → λ { (i = i0) →
                          (cong-∙ f (merid (S¹×S¹→S² a b))
                                    (sym (merid north)) (~ k)
                       ∙∙ fp ∙ sym gp
                       ∙∙ (λ i → g (σ-filler (S¹×S¹→S² a b) north k i))) j
                       ; (i = i1) → ((cong f (merid (S¹×S¹→S² a b))
                                       ∙ sym (cong f (merid north)))
                                     ∙∙ (fp ∙ sym gp)
                                     ∙∙ cong g (merid (S¹×S¹→S² a b))) j
                       ; (j = i0) → f north
                       ; (j = i1) → g (merid north (~ k ∨ i))})
            (((cong f (merid (S¹×S¹→S² a b)) ∙ sym (cong f (merid north)))
            ∙∙ (fp ∙ sym gp)
            ∙∙ cong g (merid (S¹×S¹→S² a b))) j)


  main-helper₂ : (a b : S¹)
    → cong (fst (joinify g')) (push base base ∙∙ sym (push a base) ∙∙ push a b)
    ≡ cong g (merid (S¹×S¹→S² a b))
  main-helper₂ a b = cong-∙∙ (fst (joinify g'))
       (push base base) (sym (push a base)) (push a b)
       ∙ cong (cong g (merid north) ∙∙_∙∙ cong g (merid (S¹×S¹→S² a b)))
              (cong (cong g) (cong sym (cong merid (S¹×S¹→S²rUnit a))))
       ∙  ((λ i → (cong g (λ j → merid north (j ∧ ~ i)))
       ∙∙ (cong g (λ j → merid north (~ j ∧ ~ i)))
       ∙∙ cong g (merid (S¹×S¹→S² a b)))
       ∙ sym (lUnit (cong g (merid (S¹×S¹→S² a b)))))

  main : (a b : S¹)
    → PathP (λ i → fp (~ i) ≡ (sym gp ∙ cong g (merid north)) i)
            ((sym fp ∙∙ cong f (σ₂ (S¹×S¹→S² a b)) ∙∙ fp)
           ∙ (sym gp ∙∙ cong g (σ₂ (S¹×S¹→S² a b)) ∙∙ gp))
            ((cong (fst (joinify f')) (push a b ∙ sym (push base b))
          ∙∙ fp ∙ sym gp
          ∙∙ cong (fst (joinify g'))
              (push base base ∙∙ sym (push a base) ∙∙ push a b)))
  main a b =
    ((λ i j → hcomp (λ k → λ {(i = i0) → (((λ j → fp (~ j ∧ k))
                                          ∙∙ cong f (σ₂ (S¹×S¹→S² a b))
                                          ∙∙ fp)
                                          ∙ (sym gp
                                          ∙∙ cong g (σ₂ (S¹×S¹→S² a b))
                                          ∙∙ λ j → gp (j ∧ k))) j
                              ; (i = i1) → ((cong f (merid (S¹×S¹→S² a b))
                                           ∙ sym (cong f (merid north)))
                                          ∙∙ fp ∙ sym gp
                                          ∙∙ cong g (merid (S¹×S¹→S² a b))) j
                              ; (j = i0) → fp (~ i ∧ k)
                              ; (j = i1) → compPath-filler'
                                           (sym gp) (cong g (merid north)) k i})
                     (main-helper a b i j)))
    ▷ λ i →
      cong-∙ (fst (joinify f')) (push a b) (sym (push base b)) (~ i)
      ∙∙ fp ∙ sym gp
      ∙∙ main-helper₂ a b (~ i)



-- Group structure on π₃*
-- todo: remove connectivity assumption
module _ (A : Pointed ℓ) (con : (isConnected 3 (typ A))) where
  π₃*Iso : Iso (typ (π'Gr 2 A)) ∥ (join S¹ S¹ , inl base) →∙ A ∥₂
  fun π₃*Iso = sMap joinify
  inv π₃*Iso = sMap disjoin
  rightInv π₃*Iso =
    sElim (λ _ → isSetPathImplicit)
      λ f → to3ConnectedId
        con (funExt λ x → cong (fst f) (Iso.leftInv (IsoSphereJoin 1 1) x))
  leftInv π₃*Iso =
    sElim (λ _ → isSetPathImplicit)
      λ f → to3ConnectedId
        con (funExt (λ x → cong (fst f) (Iso.rightInv (IsoSphereJoin 1 1) x)))

  π₃* : Group ℓ
  π₃* = InducedGroup (π'Gr 2 A) (sRec2 squash₂ (λ x y → ∣ x +join y ∣₂))
        (isoToEquiv π₃*Iso)
          (sElim2 (λ _ _ → isSetPathImplicit) (λ f g → cong ∣_∣₂ (+join≡∙Π f g)))

  π₃≅π₃* : GroupEquiv (π'Gr 2 A) π₃*
  π₃≅π₃* =
    InducedGroupEquiv (π'Gr 2 A) (sRec2 squash₂ (λ x y → ∣ x +join y ∣₂))
        (isoToEquiv π₃*Iso)
          (sElim2 (λ _ _ → isSetPathImplicit) (λ f g → cong ∣_∣₂ (+join≡∙Π f g)))

-- Induced homomorphisms (A →∙ B) → (π₃*(A) → π₃*(B))
-- todo: remove connectivity assumptions
module _ (conA : (isConnected 3 (typ A))) (conB : (isConnected 3 (typ B)))
         (f : A →∙ B) where
  postCompπ₃* : GroupHom (π₃* A conA) (π₃* B conB)
  fst postCompπ₃* = sMap (f ∘∙_)
  snd postCompπ₃* =
    makeIsGroupHom
      (sElim2 (λ _ _ → isSetPathImplicit)
        λ h g → to3ConnectedId conB
          (funExt λ { (inl x) → refl
                    ; (inr x) → refl
                    ; (push a b i) j →
           (cong-∙∙ (fst f)
                    (cong (fst h) ((push a b ∙ (sym (push base b)))))
                    (snd h ∙ (sym (snd g)))
                    (cong (fst g) ((push base base
                               ∙∙ (sym (push a base))
                               ∙∙ push a b)))
          ∙ cong (cong (fst f)
                   (cong (fst h) (push a b ∙ (sym (push base b))))
                    ∙∙_∙∙
                   cong (fst f ∘ fst g)
                     ((push base base ∙∙ (sym (push a base)) ∙∙ push a b)))
                 (cong-∙ (fst f) (snd h) (sym (snd g))
                 ∙ λ j → compPath-filler (cong (fst f) (snd h)) (snd f) j
                        ∙ sym (compPath-filler
                               (cong (fst f) (snd g)) (snd f) j))) j i}))

-- Induced iso (A ≃∙ B) → π₃*(A) ≅ π₃*(B)
-- todo: remove connectivity assumptions
module _ (conA : (isConnected 3 (typ A))) (conB : (isConnected 3 (typ B)))
         (f : A ≃∙ B) where
  postCompπ₃*Equiv : GroupEquiv (π₃* A conA) (π₃* B conB)
  fst postCompπ₃*Equiv = isoToEquiv h
    where
    h : Iso (π₃* A conA .fst) (π₃* B conB .fst)
    fun h = fst (postCompπ₃* conA conB (≃∙map f))
    inv h = fst (postCompπ₃* conB conA (≃∙map (invEquiv∙ f)))
    rightInv h =
      sElim (λ _ → isSetPathImplicit)
        λ g → to3ConnectedId conB (funExt λ x → secEq (fst f) (fst g x))
    leftInv h =
      sElim (λ _ → isSetPathImplicit)
        λ g → to3ConnectedId conA (funExt λ x → retEq (fst f) (fst g x))
  snd postCompπ₃*Equiv = snd (postCompπ₃* conA conB (≃∙map f))

-- The relevant groups (in order of the iso π₃(S²) ≅ ℤ)
π₃S² = π'Gr 2 (S₊∙ 2)

π₃*S² = π₃* (S₊∙ 2) (sphereConnected 2)

π₃*joinS¹S¹ = π₃* (join S¹ S¹ , inl base) con-joinS¹S¹

π₃*S³ = π₃* (S₊∙ 3) connS³

π₃S³ = π'Gr 2 (S₊∙ 3)

{- Goal now:  Show that
   (η : π₃(S²))
↦ (η₁ : π₃*(S²))
↦ (η₂ : π₃*(S¹ * S¹))
↦ (η₃ : π₃*(S³))
↦ (η₄ : π₃(S³))
↦ (-2 : ℤ)

for some terms η₁ ... η₄ by a sequence of isomorphisms
π₃(S²) ≅ π₃*(S²) ≅ π₃*(S¹ * S¹) ≅ π₃*(S³) ≅ π₃(S³) ≅ ℤ

Hence, there is an is an iso π₃(S²) ≅ ℤ taking η to
-2, from which we can conclude π₄(S³) ≅ ℤ/2ℤ.
-}

-- Underlying functions of (some of) the ηs
η₁-raw : (join S¹ S¹ , inl base) →∙ S₊∙ 2
fst η₁-raw (inl x) = north
fst η₁-raw (inr x) = north
fst η₁-raw (push a b i) = (σ₁ b ∙ σ₁ a) i
snd η₁-raw = refl

η₂-raw : (join S¹ S¹ , inl base) →∙ (join S¹ S¹ , inl base)
fst η₂-raw (inl x) = inr (invLooper x)
fst η₂-raw (inr x) = inr x
fst η₂-raw (push a b i) =
    (sym (push (b * invLooper a) (invLooper a))
  ∙ push (b * invLooper a) b) i
snd η₂-raw = sym (push base base)

η₃-raw : (join S¹ S¹ , inl base) →∙ S₊∙ 3
fst η₃-raw (inl x) = north
fst η₃-raw (inr x) = north
fst η₃-raw (push a b i) =
  (sym (σ₂ (S¹×S¹→S² a b)) ∙ sym (σ₂ (S¹×S¹→S² a b))) i
snd η₃-raw = refl

-- Homotopy group versions
η₁ : fst π₃*S²
η₁ = ∣ η₁-raw ∣₂

η₂ : fst (π₃*joinS¹S¹)
η₂ = ∣ η₂-raw ∣₂

η₃ : π₃*S³ .fst
η₃ = ∣ η₃-raw ∣₂

η₄ : fst π₃S³
η₄ = ·π' 2 (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂) (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂)


-- π₃S²≅π₃*S²
π₃S²→π₃*S² : GroupEquiv π₃S² π₃*S²
π₃S²→π₃*S² = π₃≅π₃* (S₊∙ 2) (sphereConnected 2)

-- Time for π₃*(S¹ * S¹) ≅ π₃*S².
-- We have this iso already, but slightly differently stated,
-- so the following proof becomes a bit technical.
-- We define it in terms a slight variation of the Hopf map

Hopfσ : join S¹ S¹ → S₊ 2
Hopfσ (inl x) = north
Hopfσ (inr x) = north
Hopfσ (push a b i) = σ₁ (invLooper a * b) i

π₃*joinS¹S¹→π₃*S² : GroupHom π₃*joinS¹S¹ π₃*S²
π₃*joinS¹S¹→π₃*S² =
  postCompπ₃* con-joinS¹S¹ (sphereConnected 2)
    (Hopfσ , refl)

π₃*joinS¹S¹≅π₃*S² : GroupEquiv π₃*joinS¹S¹ π₃*S²
fst (fst π₃*joinS¹S¹≅π₃*S²) = fst π₃*joinS¹S¹→π₃*S²
snd (fst π₃*joinS¹S¹≅π₃*S²) =
  subst isEquiv idLem isEquivπ₃*joinS¹S¹→π₃*S²'
  where
  π₃*joinS¹S¹→π₃*S²' : GroupHom π₃*joinS¹S¹ π₃*S²
  π₃*joinS¹S¹→π₃*S²' =
    postCompπ₃* con-joinS¹S¹ (sphereConnected 2)
      (fst ∘ JoinS¹S¹→TotalHopf , refl)

  isEquivπ₃*joinS¹S¹→π₃*S²' : isEquiv (fst π₃*joinS¹S¹→π₃*S²')
  isEquivπ₃*joinS¹S¹→π₃*S²' =
    transport (λ i → isEquiv (fst (help (~ i))))
      (snd (fst GrEq))
    where
    GrEq = compGroupEquiv (πS³≅πTotalHopf 2) π'₃S²≅π'₃TotalHopf

    help : PathP
        (λ i → GroupHom
                (GroupPath π₃*joinS¹S¹ π₃S³ .fst
                  (compGroupEquiv
                   (invGroupEquiv (π₃≅π₃* (join S¹ S¹ , inl base) con-joinS¹S¹))
                   (π'Iso 2 (isoToEquiv (IsoSphereJoin 1 1) , refl))) i)
                (GroupPath π₃*S² π₃S² .fst
                  (invGroupEquiv (π₃≅π₃* (S₊∙ 2) (sphereConnected 2))) i))
         π₃*joinS¹S¹→π₃*S²'
         (fst (fst GrEq) , snd GrEq)
    help =
      toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt
          λ f → (λ i
           → transportRefl
              ((invGroupEquiv (π₃≅π₃* (S₊∙ 2) (sphereConnected 2))) .fst .fst
                (fst π₃*joinS¹S¹→π₃*S²' (
                  ((fst (fst (π₃≅π₃* (join S¹ S¹ , inl base) con-joinS¹S¹)))
                  (invEq (fst (π'Iso 2 (isoToEquiv (IsoSphereJoin 1 1) , refl)))
                     (transportRefl f i)))))) i)
              ∙ main f))

      where
      main : (f : _) → invEquiv (fst (π₃≅π₃* (S₊∙ 2) (sphereConnected 2))) .fst
        (fst π₃*joinS¹S¹→π₃*S²'
         (invEq
          (invEquiv (fst (π₃≅π₃* (join S¹ S¹ , inl base) con-joinS¹S¹)))
          (invEq (fst (π'Iso 2 (isoToEquiv Iso-joinS¹S¹-S³ , (λ _ → north))))
           f)))
        ≡ fst GrEq .fst f
      main = sElim (λ _ → isSetPathImplicit)
        λ f → to3ConnectedId (sphereConnected 2)
          (funExt λ x
            → (λ i → fst (JoinS¹S¹→TotalHopf (Iso.inv (IsoSphereJoin 1 1)
                              (fst f (Iso.rightInv (IsoSphereJoin 1 1) x i)))))
                    ∙ sym (funExt⁻ (sym (cong fst hopfMap≡HopfMap'))
                                (fst f x)))

  idLem : fst π₃*joinS¹S¹→π₃*S²' ≡ fst π₃*joinS¹S¹→π₃*S²
  idLem =
    funExt (sElim (λ _ → isSetPathImplicit)
           λ f → to3ConnectedId (sphereConnected 2)
      (funExt λ x → lem (fst f x)))
    where
    lem : (x : _) → fst (JoinS¹S¹→TotalHopf x) ≡ Hopfσ x
    lem (inl x) = refl
    lem (inr x) = sym (merid base)
    lem (push a b i) j =
      compPath-filler (merid (invLooper a * b)) (sym (merid base)) j i
snd π₃*joinS¹S¹≅π₃*S² = snd π₃*joinS¹S¹→π₃*S²


-- π₃*(S³) ≅ π₃*(S¹ * S¹)
π₃*S³≅π₃*joinS¹S¹ : GroupEquiv π₃*S³ π₃*joinS¹S¹
π₃*S³≅π₃*joinS¹S¹ =
  postCompπ₃*Equiv
    connS³ con-joinS¹S¹
      (isoToEquiv (invIso (IsoSphereJoin 1 1)) , refl)

-- π₃(S³)≅π₃*(S³)
π₃S³≅π₃*S³ : GroupEquiv π₃S³ π₃*S³
π₃S³≅π₃*S³ = π₃≅π₃* (S₊∙ 3) connS³

η↦η₁ :  fst (fst π₃S²→π₃*S²) η ≡ η₁
η↦η₁ = to3ConnectedId (sphereConnected 2)
         (funExt λ x → (funExt⁻ lem₁ x) ∙ sym (lem₂ x))
  where
  lem₁ : fold∘W ∘ joinS¹S¹→S³ ≡ fold⋁ ∘ (joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1})
  lem₁ = funExt λ x
    → cong (fold⋁ ∘ (joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1}))
      (leftInv (IsoSphereJoin 1 1) x)

  lem₂ : (x : join S¹ S¹) → fst η₁-raw x ≡ (fold⋁ ∘ joinTo⋁) x
  lem₂ (inl x) = refl
  lem₂ (inr x) = refl
  lem₂ (push a b i) j = help j i
    where
    help : (σ₁ b ∙ σ₁ a) ≡ cong (fold⋁ ∘ joinTo⋁) (push a b)
    help = sym (cong-∙∙ fold⋁ (λ j → inr (σ₁ b j))
                        (sym (push tt)) (λ j → inl (σ₁ a j))
             ∙ λ i → (λ j → σ₁ b (j ∧ ~ i))
                   ∙∙ (λ j → σ₁ b (j ∨ ~ i))
                   ∙∙ σ₁ a)

-- We show that η₂ ↦ η₁ (this is easier than η₁ ↦ η₂)
η₂↦η₁ : fst (fst π₃*joinS¹S¹≅π₃*S²) η₂ ≡ η₁
η₂↦η₁ =
  to3ConnectedId (sphereConnected 2)
    (funExt λ { (inl x) → refl
              ; (inr x) → refl
              ; (push a b i) j → main a b j i})
  where
  lem : (a b : S¹)
    → (sym (σ₁ (invLooper (b * invLooper a) * invLooper a)) ≡ σ₁ b)
     × (σ₁ (invLooper (b * invLooper a) * b) ≡ σ₁ a)
  fst (lem a b) =
       cong sym (cong σ₁ (sym (invLooperDistr (b * invLooper a) a))
               ∙ σ-invSphere 0 (b * invLooper a * a))
     ∙ cong σ₁ (sym (assocS¹ b (invLooper a) a)
     ∙ cong (b *_) (commS¹ _ _ ∙ sym (rCancelS¹ a))
     ∙ rUnitS¹ b)
  snd (lem a b) =
    cong σ₁ (cong (_* b) (invLooperDistr b (invLooper a)
           ∙ cong (invLooper b *_) (invSphere² 1 a)
           ∙ commS¹ (invLooper b) a)
           ∙ sym (assocS¹ a (invLooper b) b)
           ∙ cong (a *_) (commS¹ _ _ ∙ sym (rCancelS¹ b))
           ∙ rUnitS¹ a)

  main : (a b : S¹)
    → cong Hopfσ ((sym (push (b * invLooper a) (invLooper a))
                        ∙ push (b * invLooper a) b))
     ≡ σ₁ b ∙ σ₁ a
  main a b =
      cong-∙ Hopfσ (sym (push (b * invLooper a) (invLooper a)))
                          (push (b * invLooper a) b)
    ∙ cong₂ _∙_ (fst (lem a b)) (snd (lem a b))

-- We show that η₂ ↦ η₃
η₂↦η₃ : invEq (fst π₃*S³≅π₃*joinS¹S¹) η₂ ≡ η₃
η₂↦η₃ =
  to3ConnectedId connS³
   (funExt λ x → sym (joinS¹S¹→S³σ≡ (fst η₂-raw x))
                ∙ lem x)
  where
  joinS¹S¹→S³σ : join S¹ S¹ → S₊ 3
  joinS¹S¹→S³σ (inl x) = north
  joinS¹S¹→S³σ (inr x) = north
  joinS¹S¹→S³σ (push a b i) = σ₂ (S¹×S¹→S² a b) i

  joinS¹S¹→S³σ≡ : (x : _) → joinS¹S¹→S³σ x ≡ joinS¹S¹→S³ x
  joinS¹S¹→S³σ≡ (inl x) = refl
  joinS¹S¹→S³σ≡ (inr x) = merid north
  joinS¹S¹→S³σ≡ (push a b i) j =
    compPath-filler (merid (S¹×S¹→S² a b)) (sym (merid north)) (~ j) i

  lem : (x : _) → joinS¹S¹→S³σ (fst η₂-raw x) ≡ fst η₃-raw x
  lem (inl x) = refl
  lem (inr x) = refl
  lem (push a b i) j = main j i
    where
    left-lem : σ₂ (S¹×S¹→S² (b * invLooper a) (invLooper a))
             ≡ σ₂ (S¹×S¹→S² a b)
    left-lem = cong σ₂ (S¹×S¹→S²-Distr b (invLooper a)
             ∙ sym (S¹×S¹→S²-antiComm a b))

    right-lem : σ₂ (S¹×S¹→S² (b * invLooper a) b) ≡ sym (σ₂ (S¹×S¹→S² a b))
    right-lem =
         cong σ₂ ((cong (λ x → S¹×S¹→S² x b) (commS¹ b (invLooper a))
                 ∙ S¹×S¹→S²-Distr (invLooper a) b)
                 ∙∙ S¹×S¹→S²-antiComm (invLooper a) b
                 ∙∙ invSusp∘S¹×S¹→S² b (invLooper a))
      ∙∙ σ-invSphere 1 (S¹×S¹→S² b (invLooper a))
      ∙∙ cong (sym ∘ σ₂) (sym (S¹×S¹→S²-antiComm a b))

    main : cong (joinS¹S¹→S³σ ∘ fst η₂-raw) (push a b)
        ≡ sym (σ₂ (S¹×S¹→S² a b)) ∙ sym (σ₂ (S¹×S¹→S² a b))
    main = cong-∙ joinS¹S¹→S³σ
            (sym (push (b * invLooper a) (invLooper a)))
            (push (b * invLooper a) b)
         ∙ cong₂ _∙_ (cong sym left-lem) right-lem

-- We show that η₄ ↦ η₃ (this is easier than η₃ ↦ η₄)
η₄↦η₃ : fst (fst π₃S³≅π₃*S³) η₄ ≡ η₃
η₄↦η₃ = IsGroupHom.pres· (snd π₃S³≅π₃*S³)
            (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂) (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂)
       ∙ cong₂ _+π₃*_ gen↦η₃/2 gen↦η₃/2
       ∙ η₃/2+η₃/2≡η₃
  where
  _+π₃*_ : fst π₃*S³ → fst π₃*S³ → fst π₃*S³
  _+π₃*_ = GroupStr._·_ (snd π₃*S³)

  η₃-raw/2 : (join S¹ S¹ , inl base) →∙ S₊∙ 3
  fst η₃-raw/2 (inl x) = north
  fst η₃-raw/2 (inr x) = north
  fst η₃-raw/2 (push a b i) = σ₂ (S¹×S¹→S² a b) (~ i)
  snd η₃-raw/2 = refl

  η₃/2 : π₃*S³ .fst
  η₃/2 = ∣ η₃-raw/2 ∣₂

  gen↦η₃/2 : fst (fst π₃S³≅π₃*S³) (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂) ≡ η₃/2
  gen↦η₃/2 =
    to3ConnectedId connS³
      (funExt λ { (inl x) → refl
                ; (inr x) → refl
                ; (push a b i) → refl})

  η₃/2+η₃/2≡η₃ : η₃/2 +π₃* η₃/2 ≡ η₃
  η₃/2+η₃/2≡η₃ =
    to3ConnectedId connS³
      (funExt λ { (inl x) → refl
                ; (inr x) → refl
                ; (push a b i) → λ j → lem a b j i})
    where
    lem : (a b : S¹) → cong (fst (η₃-raw/2 +join η₃-raw/2)) (push a b)
                      ≡ cong (fst η₃-raw) (push a b)
    lem a b = (λ i → cong-∙ (fst η₃-raw/2) (push a b) (sym (push base b)) i
                   ∙∙ rUnit refl (~ i)
                   ∙∙ cong-∙∙ (fst η₃-raw/2)
                        (push base base) (sym (push a base)) (push a b) i)
           ∙∙ (λ i → (sym (σ₂ (S¹×S¹→S² a b)) ∙ rCancel (merid north) i)
                   ∙∙ refl
                   ∙∙ (sym (rCancel (merid north) i)
                   ∙∙ (cong σ₂ (S¹×S¹→S²rUnit a) ∙ rCancel (merid north)) i
                   ∙∙ sym (σ₂ (S¹×S¹→S² a b))))
           ∙∙ ((λ i → rUnit (sym (σ₂ (S¹×S¹→S² a b))) (~ i)
                    ∙∙ refl
                    ∙∙ lUnit (sym (σ₂ (S¹×S¹→S² a b))) (~ i))
             ∙ λ i → (λ j → σ₂ (S¹×S¹→S² a b) (i ∨ ~ j))
                   ∙∙ (λ j → σ₂ (S¹×S¹→S² a b) (i ∧ ~ j))
                   ∙∙ sym (σ₂ (S¹×S¹→S² a b)))

-- Agda is very keen on expanding things, so we make an abstract
-- summary of the main lemmas above
abstract
  π₃S²≅π₃*S²-abs : GroupEquiv π₃S² π₃*S²
  π₃S²≅π₃*S²-abs = π₃S²→π₃*S²

  π₃*S²≅π₃*joinS¹S¹-abs : GroupEquiv π₃*S² π₃*joinS¹S¹
  π₃*S²≅π₃*joinS¹S¹-abs = invGroupEquiv π₃*joinS¹S¹≅π₃*S²

  π₃*joinS¹S¹≅π₃*S³-abs : GroupEquiv π₃*joinS¹S¹ π₃*S³
  π₃*joinS¹S¹≅π₃*S³-abs = invGroupEquiv π₃*S³≅π₃*joinS¹S¹

  π₃*S³≅π₃*S³-abs : GroupEquiv π₃*S³ π₃S³
  π₃*S³≅π₃*S³-abs = invGroupEquiv π₃S³≅π₃*S³

  -- stated in terms of (n : ℕ) to prevent normalisation
  π₃'S³≅ℤ-abs : (n : ℕ) → GroupEquiv (π'Gr n (S₊∙ (suc n))) ℤ
  π₃'S³≅ℤ-abs n = GroupIso→GroupEquiv (πₙ'Sⁿ≅ℤ n)

  η↦η₁-abs : fst (fst π₃S²≅π₃*S²-abs) η ≡ η₁
  η↦η₁-abs = η↦η₁

  η₁↦η₂-abs : fst (fst π₃*S²≅π₃*joinS¹S¹-abs) η₁ ≡ η₂
  η₁↦η₂-abs = cong (fst (fst π₃*S²≅π₃*joinS¹S¹-abs)) (sym η₂↦η₁)
              ∙ secEq (fst π₃*S²≅π₃*joinS¹S¹-abs) η₂

  η₂↦η₃-abs : fst (fst π₃*joinS¹S¹≅π₃*S³-abs) η₂ ≡ η₃
  η₂↦η₃-abs = η₂↦η₃

  η₃↦η₄-abs : fst (fst π₃*S³≅π₃*S³-abs) η₃ ≡ η₄
  η₃↦η₄-abs = cong (invEq (fst π₃S³≅π₃*S³)) (sym η₄↦η₃)
                  ∙ retEq (fst π₃S³≅π₃*S³) η₄

  gen↦1 : (n : ℕ) → fst (fst (π₃'S³≅ℤ-abs n)) ∣ idfun∙ (S₊∙ (suc n)) ∣₂ ≡ 1
  gen↦1 = πₙ'Sⁿ≅ℤ-idfun∙

-- We finally prove that η₄ ↦ -2
abstract
  η₄↦-2 : fst (fst (π₃'S³≅ℤ-abs 2)) η₄ ≡ -2
  η₄↦-2 = speedUp (∣ idfun∙ (S₊∙ 3) ∣₂) (gen↦1 2)
    where
    speedUp : (x : _)
      → fst (fst (π₃'S³≅ℤ-abs (suc (suc zero)))) x ≡ (pos (suc zero))
      → (fst (fst (π₃'S³≅ℤ-abs 2))) (·π' 2 (-π' 2 x) (-π' 2 x)) ≡ -2
    speedUp x p =
        IsGroupHom.pres· (π₃'S³≅ℤ-abs 2 .snd)
              (-π' 2 x) (-π' 2 x)
      ∙ cong (λ x → x +Z x)
        (IsGroupHom.presinv (π₃'S³≅ℤ-abs 2 .snd) x ∙ cong (inv (ℤ .snd)) p)

-- Puting it all together, we get our group iso π₃(S²) ≅ ℤ
π₃'S²≅ℤ : GroupEquiv (π'Gr 2 (S₊∙ 2)) ℤ
π₃'S²≅ℤ =
  compGroupEquiv
    π₃S²≅π₃*S²-abs
    (compGroupEquiv
      π₃*S²≅π₃*joinS¹S¹-abs
      (compGroupEquiv
        π₃*joinS¹S¹≅π₃*S³-abs
        (compGroupEquiv π₃*S³≅π₃*S³-abs
          (π₃'S³≅ℤ-abs 2))))


-- ... which takes η to -2
η↦-2 : fst (fst π₃'S²≅ℤ) η ≡ - 2
η↦-2 =
    cong (fst (fst (π₃'S³≅ℤ-abs 2)))
      (cong (fst π₃*S³≅π₃*S³-abs .fst)
        (cong (fst π₃*joinS¹S¹≅π₃*S³-abs .fst)
          (cong (fst (fst π₃*S²≅π₃*joinS¹S¹-abs))
            η↦η₁-abs
          ∙ η₁↦η₂-abs)
        ∙ η₂↦η₃-abs)
     ∙ η₃↦η₄-abs)
  ∙ η₄↦-2

-- We combine this with the rest of the main conclusions of chapters
-- 1-3 in Brunerie's thesis
BrunerieIso : GroupEquiv (π'Gr 3 (S₊∙ 3)) (ℤ/ 2)
BrunerieIso =
  compGroupEquiv
    (compGroupEquiv π₄S³≅π₃coFib-fold∘W∙
    (invGroupEquiv
      (GroupEquiv-abstractℤ/abs-gen
        (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙)
          (invGroupEquiv (π₃'S³≅ℤ-abs 2))
          (invGroupEquiv π₃'S²≅ℤ)
          (π'∘∙Hom 2 (fold∘W , refl))
          _
          S³→S²→Pushout→Unit 2
            (cong abs (cong (invEq (invEquiv (fst π₃'S²≅ℤ))
                     ∘ sMap (_∘∙_ (fold∘W , refl)))
                      (sym (cong (invEq (fst (π₃'S³≅ℤ-abs 2))) (gen↦1 2))
                    ∙ retEq (fst (π₃'S³≅ℤ-abs 2)) ∣ idfun∙ (S₊∙ 3) ∣₂))
           ∙ cong abs η↦-2))))
           (abstractℤ/≅ℤ 2)
