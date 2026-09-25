{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.FiberOrCofiberSequences.ShortExactSequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.SetTruncation renaming (elim to setElim)

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.PuppeLemma

private
  variable
    ℓ : Level

{-iteratedPuppeUniversalEquiv' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  (pb : typ (Ω B))
  → (Σ[ pa ∈ typ (Ω A) ] sym (snd (FiberSeqIncl F))
      ∙ cong (fst (FiberSeqIncl F)) (sym pa) ∙ snd (FiberSeqIncl F) ≡ pb)
  ≃ (sym (snd (FiberSeqProj F)) ∙ cong (fst (FiberSeqProj F)) (sym pb)
     ∙ snd (FiberSeqProj F) ≡ refl {x = pt C})
iteratedPuppeUniversalEquiv' F =
  transport
  (λ i → (pb : typ (Ω (FiberSeqTotal F)))
   → (Σ[ pa ∈ typ (Ω (FiberSeqFiber F)) ] (twiceIteratedPuppeIncl F i pa) ≡ pb)
   ≃ ((twiceIteratedPuppeProj F i pb) ≡ refl {x = pt (FiberSeqBase F)}))
  (UniversalEquiv (puppe (puppe (puppe F))))-}

ftit1 : {A : Type ℓ} (a : A) → Iso (Σ[ a' ∈ A ] a' ≡ a) (Unit)
Iso.fun (ftit1 a) = λ _ → tt
Iso.inv (ftit1 a) = λ _ → (a , refl)
Iso.sec (ftit1 a) = λ _ → refl
Iso.ret (ftit1 a) = λ p → J (λ a' q → Iso.inv (ftit1 a) (Iso.fun (ftit1 a) (a' , (sym q))) ≡ (a' , (sym q))) refl (sym (snd p))

lUnitIsoLeft : {A : Type ℓ} {a b : A} (p q : a ≡ b)
  → Iso (refl ∙ p ≡ q) (p ≡ q)
lUnitIsoLeft p q = ∙IsoOnLeft (lUnit p)

lUnitIsoRight : {A : Type ℓ} {a b : A} (p q : a ≡ b)
  → Iso (p ≡ q) (p ≡ refl ∙ q)
lUnitIsoRight p q = ∙IsoOnRight (lUnit q)

rUnitIsoLeft : {A : Type ℓ} {a b : A} (p q : a ≡ b)
  → Iso (p ∙ refl ≡ q) (p ≡ q)
rUnitIsoLeft p q = ∙IsoOnLeft (rUnit p)

rUnitIsoRight : {A : Type ℓ} {a b : A} (p q : a ≡ b)
  → Iso (p ≡ q) (p ≡ q ∙ refl)
rUnitIsoRight p q = ∙IsoOnRight (rUnit q)

lCancelIsoLeftLeft : {A : Type ℓ} {a b c : A} (p p' : b ≡ c) (q : a ≡ b)
  → Iso (refl ∙ p ≡ p') ((sym q) ∙ q ∙ p ≡ p')
lCancelIsoLeftLeft p p' q = ∙IsoOnLeft (assoc _ _ _ ∙ cong (_∙ p) (lCancel q))

rCancelIsoLeftLeft : {A : Type ℓ} {a b c : A} (p p' : b ≡ c) (q : b ≡ a)
  → Iso (refl ∙ p ≡ p') (q ∙ (sym q) ∙ p ≡ p')
rCancelIsoLeftLeft p p' q = ∙IsoOnLeft (assoc _ _ _ ∙ cong (_∙ p) (rCancel q))

lCancelIsoRightLeft : {A : Type ℓ} {a b c : A} (p p' : a ≡ b) (q : c ≡ b)
  → Iso (p ∙ refl ≡ p') (p ∙ (sym q) ∙ q ≡ p')
lCancelIsoRightLeft p p' q = ∙IsoOnLeft (cong (p ∙_) (lCancel q))

rCancelIsoRightLeft : {A : Type ℓ} {a b c : A} (p p' : a ≡ b) (q : b ≡ c)
  → Iso (p ∙ refl ≡ p') (p ∙ q ∙ (sym q) ≡ p')
rCancelIsoRightLeft p p' q = ∙IsoOnLeft (cong (p ∙_) (rCancel q))

∙LeftIso : {A : Type ℓ} {a b c : A} (p p' : b ≡ c) (q : a ≡ b)
  → Iso (p ≡ p') (q ∙ p ≡ q ∙ p')
∙LeftIso p p' q = congPathIso (λ _ → isoToEquiv (∙IsoOnLeft q))

∙RightIso : {A : Type ℓ} {a b c : A} (p p' : a ≡ b) (q : b ≡ c)
  → Iso (p ≡ p') (p ∙ q ≡ p' ∙ q)
∙RightIso p p' q = congPathIso (λ _ → isoToEquiv (∙IsoOnRight q))

assocIsoLeft : {A : Type ℓ} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
  (s : a ≡ d) → Iso ((p ∙ q) ∙ r ≡ s) (p ∙ q ∙ r ≡ s)
assocIsoLeft p q r s = ∙IsoOnLeft (assoc p q r)

swapSymLeftIso : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z)
  (r : z ≡ y) → Iso ((sym q) ∙ p ≡ r) (p ≡ q ∙ r)
swapSymLeftIso p q r =
  compIso (∙LeftIso ((sym q) ∙ p) r q)
  (compIso (invIso (lCancelIsoLeftLeft p (q ∙ r) (sym q)))
           (lUnitIsoLeft p (q ∙ r)))

swapSymRightIso : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
  (r : x ≡ z) → Iso (p ∙ sym q ≡ r) (p ≡ r ∙ q)
swapSymRightIso p q r =
  compIso (∙RightIso (p ∙ (sym q)) r q)
  (compIso (assocIsoLeft p (sym q) q (r ∙ q))
  (compIso (invIso (rCancelIsoRightLeft p (r ∙ q) (sym q)))
           (rUnitIsoLeft p (r ∙ q))))

swapSymLeftIso' : {A : Type ℓ} {x y : A} (p : x ≡ y) (q : x ≡ y)
  → Iso (p ≡ q) (refl ≡ (sym p) ∙ q)
swapSymLeftIso' p q =
  invIso
  (compIso symIso
  (compIso (swapSymLeftIso q p refl)
           (invIso (compIso symIso (rUnitIsoRight q p)))))

swapSymRightIso' : {A : Type ℓ} {x y : A} (p : x ≡ y) (q : x ≡ y)
  → Iso (p ≡ q) (p ∙ (sym q) ≡ refl)
swapSymRightIso' p q =
  invIso
  (compIso (swapSymRightIso p q refl)
  (compIso symIso
  (compIso (lUnitIsoLeft q p) symIso)))

conjReflSymIso : {A : Type ℓ} {x y : A} (p : x ≡ x) (q : x ≡ y)
  → Iso ((sym q) ∙ (sym p) ∙ q ≡ refl) ((sym q) ∙ p ∙ q ≡ refl)
conjReflSymIso p q =
  compIso (swapSymLeftIso ((sym p) ∙ q) q refl)
  (compIso symIso
  (compIso (rUnitIsoLeft q ((sym p) ∙ q))
  (compIso symIso
  (compIso (swapSymLeftIso q p q)
  (compIso (swapSymLeftIso' q (p ∙ q)) symIso)))))

Auxiliary≡Iso : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  (pb : typ (Ω B))
  → Iso (sym (snd (FiberSeqProj F)) ∙
          cong (fst (FiberSeqProj F)) (sym pb) ∙
          snd (FiberSeqProj F) ≡ refl)
         (sym (snd (FiberSeqProj F)) ∙
          cong (fst (FiberSeqProj F)) pb ∙
          snd (FiberSeqProj F) ≡ refl)
Auxiliary≡Iso F pb =
  conjReflSymIso
  ( cong (fst (FiberSeqProj F)) pb)
  ( snd (FiberSeqProj F))

sprawl : {B C : Pointed ℓ} (f : B →∙ C) (pa : pt B ≡ pt B)
  → Iso (((sym (snd f)) ∙∙ (cong (fst f) pa) ∙∙ (snd f)) ≡ refl)
         (cong (fst f) pa ≡ refl)
sprawl f pa =
  compIso (equivToIso (transport ρ , isEquivTransport ρ))
  (compIso (swapSymLeftIso (cong (fst f) pa ∙ snd f) (snd f) refl)
  (compIso (swapSymRightIso (cong (fst f) pa) (sym (snd f)) (snd f ∙ refl))
  (equivToIso (transport ρ' , isEquivTransport ρ'))))
  where
    ρ : ((sym (snd f) ∙∙ cong (fst f) pa ∙∙ snd f) ≡ refl)
        ≡ ((sym (snd f) ∙ cong (fst f) pa ∙ snd f) ≡ refl)
    ρ = cong (λ p → p ≡ refl) (doubleCompPath-elim (sym (snd f)) (cong (fst f) pa) (snd f) ∙ (assoc (sym (snd f)) (cong (fst f) pa) (snd f)) ⁻¹)

    ρ' : (cong (fst f) pa ≡ (snd f ∙ refl) ∙ sym (snd f))
         ≡ (cong (fst f) pa ≡ refl)
    ρ' = cong (cong (fst f) pa ≡_)
              (cong (_∙ sym (snd f)) (rUnit _ ⁻¹)
              ∙ rCancel _)


budayeen : {B C : Pointed ℓ} (f : B →∙ C) (pa : pt B ≡ pt B)
  → Iso (((sym (snd f)) ∙∙ (cong (fst f) pa) ∙∙ (snd f)) ≡ refl)
         (PathP (λ i → fst f (pa i) ≡ pt C) (snd f) (snd f))
budayeen {ℓ} {C = C} f pa =
  compIso (equivToIso (transport ρ , (isEquivTransport ρ)))
 (compIso (∙LeftIso (sym (snd f) ∙ (cong (fst f) pa) ∙ snd f) refl
                    (snd f))
 (compIso (∙RightIso (snd f ∙ (sym (snd f) ∙ (cong (fst f) pa) ∙ snd f))
                     (snd f ∙ refl)
                     (sym (snd f)))
 (compIso (equivToIso ((transport ρ') , (isEquivTransport ρ')))
 (compIso (∙LeftIso (cong (fst f) pa) (snd f ∙ sym (snd f))
                    (sym (cong (fst f) pa)))
 (compIso (equivToIso ((transport ρ'') , (isEquivTransport ρ'')))
 (compIso symIso
 (compIso (invIso (swapSymRightIso' (sym (cong (fst f) pa) ∙ snd f) (snd f)))
 (compIso (equivToIso ((transport ρ''') , (isEquivTransport ρ''')))
 (invIso (PathPIsoPath (λ i → fst f (pa i) ≡ pt C) (snd f) (snd f)))))))))))
  where
    ρ : ((sym (snd f) ∙∙ cong (fst f) pa ∙∙ snd f) ≡ refl)
        ≡ ((sym (snd f) ∙ cong (fst f) pa ∙ snd f) ≡ refl)
    ρ = cong (λ p → p ≡ refl) (doubleCompPath-elim (sym (snd f)) (cong (fst f) pa) (snd f) ∙ (assoc (sym (snd f)) (cong (fst f) pa) (snd f)) ⁻¹)

    ρ' : (((snd f ∙ (sym (snd f) ∙ (cong (fst f) pa) ∙ snd f)) ∙ sym (snd f))
          ≡ (snd f ∙ refl) ∙ sym (snd f))
         ≡ (cong (fst f) pa ≡ snd f ∙ sym (snd f))
    ρ' = cong (λ p → (p ≡ (snd f ∙ refl) ∙ sym (snd f)))
              (cong (_∙ sym (snd f)) (assoc (snd f) (sym (snd f)) (cong (fst f) pa ∙ snd f) ∙ cong (_∙ cong (fst f) pa ∙ snd f) (rCancel (snd f)) ∙ lUnit _ ⁻¹)
              ∙ (assoc (cong (fst f) pa) (snd f) (sym (snd f))) ⁻¹
              ∙ cong (cong (fst f) pa ∙_) (rCancel (snd f))
              ∙ rUnit _ ⁻¹)
         ∙ cong (λ p → cong (fst f) pa ≡ p)
                (cong (_∙ sym (snd f)) (rUnit _ ⁻¹))

    ρ'' : ((sym (cong (fst f) pa) ∙ cong (fst f) pa) ≡ sym (cong (fst f) pa)
           ∙ snd f ∙ sym (snd f))
          ≡ (refl ≡ (sym (cong (fst f) pa) ∙ snd f) ∙ sym (snd f))
    ρ'' = cong (_≡ sym (cong (fst f) pa) ∙ snd f ∙ sym (snd f))
               (lCancel (cong (fst f) pa))
          ∙ cong (refl ≡_) (assoc (sym (cong (fst f) pa)) (snd f) (sym (snd f)))

    ρ''' : (sym (cong (fst f) pa) ∙ snd f ≡ snd f)
          ≡ (transport (λ i → fst f (pa i) ≡ pt C) (snd f) ≡ (snd f))
    ρ''' = cong (_≡ snd f) (sym (transportPathLemmaLeft (cong (fst f) pa) (snd f)))

iteratedPuppUniversalEquiv*^ : {B C : Pointed ℓ} (f : B →∙ C)
  → Iso (typ (Ω (fiber∙ f)))
         (Σ[ pa ∈ (typ (Ω B)) ] (PathP (λ i → fst f (pa i) ≡ pt C) (snd f) (snd f)))
iteratedPuppUniversalEquiv*^ f = invIso ΣPathPIsoPathPΣ

iteratedPuppUniversalEquiv*^' : {B C : Pointed ℓ} (f : B →∙ C)
  → Iso (Σ[ pa ∈ (typ (Ω B)) ] (PathP (λ i → fst f (pa i) ≡ pt C) (snd f) (snd f)))
         (Σ[ pa ∈ (typ (Ω B)) ] (sym (snd f) ∙∙ cong (fst f) pa ∙∙ snd f ≡ refl))
iteratedPuppUniversalEquiv*^' f = Σ-cong-iso-snd (λ pa → invIso (budayeen f pa))

iteratedPuppeUniversalEquiv** : {B C : Pointed ℓ} (f : B →∙ C)
    (pb : typ (Ω B))
    → Iso (Σ[ pa ∈ typ (Ω (fiber∙ f)) ] cong fst pa ≡ pb)
           (Σ[ pa ∈ typ (fiber∙ (Ω→ f)) ] fst pa ≡ pb)
iteratedPuppeUniversalEquiv** f pb =
  Σ-cong-iso (compIso (iteratedPuppUniversalEquiv*^ f) (iteratedPuppUniversalEquiv*^' f)) λ pa → idIso

iteratedPuppeUnEquiv : {B C : Pointed ℓ} (f : B →∙ C)
  (pb : typ (Ω B))
  → Iso (Σ[ pa ∈ typ (fiber∙ (Ω→ f)) ] fst pa ≡ pb)
         (Σ[ x ∈ (Σ[ pa ∈ typ (Ω B) ] pa ≡ pb) ]
           (sym (snd f) ∙∙ cong (fst f) (fst x) ∙∙ snd f) ≡ refl)
Iso.fun (iteratedPuppeUnEquiv f pb) ((x , y) , z) = (x , z) , y
Iso.inv (iteratedPuppeUnEquiv f pb) ((x , y) , z) = (x , z) , y
Iso.sec (iteratedPuppeUnEquiv f pb) t = refl
Iso.ret (iteratedPuppeUnEquiv f pb) t = refl

iteratedPuppeUniversalEquiv* : {B C : Pointed ℓ} (f : B →∙ C)
    (pb : typ (Ω B))
    → Iso (Σ[ pa ∈ typ (Ω (fiber∙ f)) ] cong fst pa ≡ pb)
           (cong (fst f) pb ≡ refl)
iteratedPuppeUniversalEquiv* {ℓ} f pb =
  compIso (iteratedPuppeUniversalEquiv** f pb)
  (compIso (iteratedPuppeUnEquiv f pb)
  (compIso (invIso (Σ-cong-iso-fst (invIso (ftit1 pb))))
  (compIso (Σ-cong-iso-snd (λ tt → sprawl f _))
  (equivToIso (ΣUnit (λ a →
                         cong (fst f)
                         (λ i → fst (Iso.fun (invIso (ftit1 pb)) a) i)
                         ≡ refl))))))

iteratedPuppeUniversalEquiv*' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    (pb : typ (Ω B))
   → Iso (Σ[ pa ∈ typ (Ω A) ] sym (snd (FiberSeqIncl F))
      ∙ cong (fst (FiberSeqIncl F)) pa ∙ snd (FiberSeqIncl F) ≡ pb)
          (Σ[ pa ∈ typ (Ω (fiber∙ (FiberSeqProj F))) ]
            (sym (snd (fiberMap∙ (FiberSeqProj F)))
             ∙ cong (fst (fiberMap∙ (FiberSeqProj F))) pa
             ∙ snd (fiberMap∙ (FiberSeqProj F))) ≡ pb)
iteratedPuppeUniversalEquiv*' F pb =
  J (λ PP q → Iso (Σ[ pa ∈ typ (Ω (fst PP)) ]
                    sym (snd (snd PP)) ∙ cong (fst (snd PP)) pa
                                       ∙ snd (snd PP) ≡ pb)
                   (Σ[ pa ∈ typ (Ω (fiber∙ (FiberSeqProj F))) ]
            (sym (snd (fiberMap∙ (FiberSeqProj F)))
             ∙ cong (fst (fiberMap∙ (FiberSeqProj F))) pa
             ∙ snd (fiberMap∙ (FiberSeqProj F))) ≡ pb)) idIso (sym (FiberSeq.eqFib F))

iteratedPuppeUniversalEquiv*'' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    (pb : typ (Ω B))
     → Iso (cong (fst (FiberSeqProj F)) pb ≡ refl)
            (sym (snd (FiberSeqProj F)) ∙ cong (fst (FiberSeqProj F)) pb
             ∙ snd (FiberSeqProj F) ≡ refl)
iteratedPuppeUniversalEquiv*'' F pb =
  compIso (equivToIso (transport ρ , isEquivTransport ρ))
  (compIso symIso
  (compIso (swapSymRightIso (snd (FiberSeqProj F) ∙ refl) (snd (FiberSeqProj F)) (cong (fst (FiberSeqProj F)) pb))
  (compIso (swapSymLeftIso refl (sym (snd (FiberSeqProj F))) (cong (fst (FiberSeqProj F)) pb ∙ snd (FiberSeqProj F))) symIso)))
  where
    ρ : (cong (fst (FiberSeqProj F)) pb ≡ refl)
        ≡ (cong (fst (FiberSeqProj F)) pb ≡ (snd (FiberSeqProj F) ∙ refl) ∙ sym (snd (FiberSeqProj F)))
    ρ = cong (cong (fst (FiberSeqProj F)) pb ≡_)
             (rCancel (snd (FiberSeqProj F)) ⁻¹
             ∙ cong (_∙ sym (snd (FiberSeqProj F))) (rUnit _))

iteratedPuppeUniversalEquiv'' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    (pb : typ (Ω B))
    → Iso ((Σ[ pa ∈ typ (Ω A) ] sym (snd (FiberSeqIncl F))
      ∙ cong (fst (FiberSeqIncl F)) pa ∙ snd (FiberSeqIncl F) ≡ pb))
         (sym (snd (FiberSeqProj F)) ∙ cong (fst (FiberSeqProj F)) pb
     ∙ snd (FiberSeqProj F) ≡ refl {x = pt C})
iteratedPuppeUniversalEquiv'' {B = B} F pb =
   compIso (iteratedPuppeUniversalEquiv*' F pb)
  (compIso (equivToIso (transport ρ , isEquivTransport ρ))
  (compIso (iteratedPuppeUniversalEquiv* (FiberSeqProj F) pb)
           (iteratedPuppeUniversalEquiv*'' F pb)))
  where
    ρ : (Σ[ pa ∈ typ (Ω (fiber∙ (FiberSeqProj F))) ]
            (sym (snd (fiberMap∙ (FiberSeqProj F)))
             ∙ cong (fst (fiberMap∙ (FiberSeqProj F))) pa
             ∙ snd (fiberMap∙ (FiberSeqProj F))) ≡ pb)
        ≡ (Σ[ pa ∈ typ (Ω (fiber∙ (FiberSeqProj F))) ]
            (cong (fst (fiberMap∙ (FiberSeqProj F))) pa ≡ pb))
    ρ = cong (λ (f : (typ (Ω (fiber∙ (FiberSeqProj F))))
                     → typ (Ω B))
                → (Σ[ pa ∈ typ (Ω (fiber∙ (FiberSeqProj F))) ]
                     (f pa ≡ pb)))
             (funExt (λ pa → lUnit _ ⁻¹ ∙ rUnit _ ⁻¹))


iteratedPuppeUniversalEquiv : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    (pb : typ (Ω B))
    → (Σ[ pa ∈ typ (Ω A) ] sym (snd (FiberSeqIncl F))
        ∙ cong (fst (FiberSeqIncl F)) pa ∙ snd (FiberSeqIncl F) ≡ pb)
    ≃ (sym (snd (FiberSeqProj F)) ∙ cong (fst (FiberSeqProj F)) pb
       ∙ snd (FiberSeqProj F) ≡ refl {x = pt C})
iteratedPuppeUniversalEquiv F pb = isoToEquiv (iteratedPuppeUniversalEquiv'' F pb)

FiberSeq→ExactFstRecCase : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → (pa : typ (Ω A))
  → ∥ sym (snd (FiberSeqIncl F)) ∙ cong (fst (FiberSeqIncl F)) pa
       ∙ snd (FiberSeqIncl F) ≡ pb ∥₁
  → isInKer (πHom 0 (FiberSeqProj F)) ∣ pb ∣₂
FiberSeq→ExactFstRecCase F pb pa = propRec
 (isOfHLevelPath' 1 isSetSetTrunc (πFun 0 (FiberSeqProj F) ∣ pb ∣₂) ∣ refl ∣₂)
 λ q → Iso.inv PathIdTrunc₀Iso
 ∣ doubleCompPath-elim' (sym (snd (FiberSeqProj F)))
                       (cong (fst (FiberSeqProj F)) pb)
                       (snd (FiberSeqProj F)) ∙
  equivFun (iteratedPuppeUniversalEquiv F pb) (pa , q) ∣₁

FiberSeq→ExactFstRecCase'' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → (g : typ (πGr 0 A))
  → πFun 0 (FiberSeqIncl F) g ≡ ∣ pb ∣₂
  → isInKer (πHom 0 (FiberSeqProj F)) ∣ pb ∣₂
FiberSeq→ExactFstRecCase'' F pb =
  setElim
  (λ g → isSet→
  (isOfHLevelPath 2 isSetSetTrunc (πFun 0 (FiberSeqProj F) ∣ pb ∣₂) ∣ refl ∣₂))
  λ pa q → FiberSeq→ExactFstRecCase F pb pa
  (Iso.fun PathIdTrunc₀Iso
  (cong ∣_∣₂
  (doubleCompPath-elim' (sym (snd (FiberSeqIncl F)))
                        (cong (fst (FiberSeqIncl F)) pa)
                        (snd (FiberSeqIncl F)) ⁻¹) ∙ q))

FiberSeq→ExactFst : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → Σ[ g ∈ typ (πGr 0 A) ] πFun 0 (FiberSeqIncl F) g ≡ ∣ pb ∣₂
  → isInKer (πHom 0 (FiberSeqProj F)) ∣ pb ∣₂
FiberSeq→ExactFst F pb (g , q) = FiberSeq→ExactFstRecCase'' F pb g q

FiberSeq→ExactSndRecCase : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → ∥ sym (snd (FiberSeqProj F)) ∙ cong (fst (FiberSeqProj F)) pb
     ∙ snd (FiberSeqProj F) ≡ refl {x = pt C} ∥₁
  → isInIm (πHom 0 (FiberSeqIncl F)) ∣ pb ∣₂
FiberSeq→ExactSndRecCase F pb = propRec isPropPropTrunc
  λ q → ∣ ∣ fst (invEq (iteratedPuppeUniversalEquiv F pb) q) ∣₂ ,
          Iso.inv PathIdTrunc₀Iso
          ∣ doubleCompPath-elim' (sym (snd (FiberSeqIncl F)))
                                 (cong (fst (FiberSeqIncl F)) _)
                                 (snd (FiberSeqIncl F)) ∙
           snd (invEq (iteratedPuppeUniversalEquiv F pb) q) ∣₁ ∣₁

FiberSeq→ExactSnd : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → isInKer (πHom 0 (FiberSeqProj F)) ∣ pb ∣₂
  → isInIm (πHom 0 (FiberSeqIncl F)) ∣ pb ∣₂
FiberSeq→ExactSnd F pb q = FiberSeq→ExactSndRecCase F pb
  (Iso.fun PathIdTrunc₀Iso (cong ∣_∣₂ ((doubleCompPath-elim' (sym (snd (FiberSeqProj F))) (cong (fst (FiberSeqProj F)) pb) (snd (FiberSeqProj F))) ⁻¹) ∙ q))


FiberSeq→Exact : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → ((x : ⟨ πGr 0 B ⟩)
  → (isInIm (πHom 0 (FiberSeqIncl F)) x → isInKer (πHom 0 (FiberSeqProj F)) x)
  × (isInKer (πHom 0 (FiberSeqProj F)) x → isInIm (πHom 0 (FiberSeqIncl F)) x))
FiberSeq→Exact {B = B} {C = C} F = setElim
 (λ x → isSet×
 (isSet→ (isOfHLevelPath 2 isSetSetTrunc (πFun 0 (FiberSeqProj F) x) ∣ refl ∣₂))
 (isSet→ (isProp→isSet isPropPropTrunc)))
 λ pb → propRec
 (isOfHLevelPath' 1 isSetSetTrunc (πFun 0 (FiberSeqProj F) ∣ pb ∣₂) ∣ refl ∣₂)
 (FiberSeq→ExactFst F pb) , (FiberSeq→ExactSnd F pb)
