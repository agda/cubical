{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Polynomials.UnivariateList.Poly1-1Poly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec renaming ( [] to <> ; _∷_ to _::_)
open import Cubical.Data.Vec.OperationsNat

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials.UnivariateList.Base renaming (Poly to Poly:)
open import Cubical.Algebra.Polynomials.UnivariateList.Properties
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly

private variable
  ℓ : Level

module Equiv-Poly1-Poly:
  (Acr@(A , Astr) : CommRing ℓ) where

  private
    PA = PolyCommRing Acr 1
    PAstr = snd PA
    PA: = UnivariatePolyList Acr
    PA:str = snd PA:

  open PolyMod Acr using (ElimProp)
  open PolyModTheory Acr
    using ( prod-Xn ; prod-Xn-sum ; prod-Xn-∷ ; prod-Xn-prod)
    renaming
    (prod-Xn-0P to prod-Xn-0P:)

  open CommRingStr
  open RingTheory

-- Notation P, Q, R... for Poly 1
-- x, y, w... for Poly:
-- a,b,c... for A


-----------------------------------------------------------------------------
-- direct

  trad-base : (v : Vec ℕ 1) → A → Poly: Acr
  trad-base (n :: <>) a = prod-Xn n (a ∷ [])

  trad-base-neutral : (v : Vec ℕ 1) → trad-base v (0r Astr) ≡ []
  trad-base-neutral (n :: <>) = cong (prod-Xn n) drop0 ∙ prod-Xn-0P: n

  trad-base-add : (v : Vec ℕ 1) → (a b : A) → _+_ PA:str (trad-base v a) (trad-base v b) ≡ trad-base v (_+_ Astr a b)
  trad-base-add (n :: <>) a b = prod-Xn-sum n (a ∷ []) (b ∷ [])

  Poly1→Poly: : Poly Acr 1 → Poly: Acr
  Poly1→Poly: = DS-Rec-Set.f _ _ _ _ (is-set PA:str)
                 []
                 trad-base
                 (_+_ PA:str)
                 (+Assoc PA:str)
                 (+IdR PA:str)
                 (+Comm PA:str)
                 trad-base-neutral
                 trad-base-add

  Poly1→Poly:-pres+ : (P Q : Poly Acr 1) → Poly1→Poly: (_+_ PAstr P Q) ≡ _+_ PA:str (Poly1→Poly: P) (Poly1→Poly: Q)
  Poly1→Poly:-pres+ P Q = refl



-----------------------------------------------------------------------------
-- converse

  Poly:→Poly1-int : (n : ℕ) → Poly: Acr → Poly Acr 1
  Poly:→Poly1-int n [] = 0r PAstr
  Poly:→Poly1-int n (a ∷ x) = _+_ PAstr (base (n :: <>) a) (Poly:→Poly1-int (suc n) x)
  Poly:→Poly1-int n (drop0 i) = ((cong (λ X → _+_ PAstr X (0r PAstr)) (base-neutral (n :: <>))) ∙ (+IdR PAstr _)) i

  Poly:→Poly1 : Poly: Acr → Poly Acr 1
  Poly:→Poly1 x = Poly:→Poly1-int 0 x

  Poly:→Poly1-int-pres+ : (x y : Poly: Acr) → (n : ℕ) →
                              Poly:→Poly1-int n (_+_ PA:str x y) ≡ _+_ PAstr (Poly:→Poly1-int n x) (Poly:→Poly1-int n y)
  Poly:→Poly1-int-pres+ = ElimProp _
                           (λ y n → cong (Poly:→Poly1-int n) (+IdL PA:str y) ∙ sym (+IdL PAstr _))
                           (λ a x ind-x → ElimProp _
                                           (λ n → sym (+IdR PAstr (Poly:→Poly1-int n (a ∷ x))))
                                           (λ b y ind-y n → sym (+ShufflePairs (CommRing→Ring PA) _ _ _ _
                                                                ∙ cong₂ (_+_ PAstr) (base-add _ _ _) (sym (ind-x y (suc n)))))
                                           (isPropΠ (λ _ → is-set PAstr _ _)))
                           (isPropΠ2 (λ _ _ → is-set PAstr _ _))

  Poly:→Poly1-pres+ : (x y : Poly: Acr) → Poly:→Poly1 (_+_ PA:str x y) ≡ _+_ PAstr (Poly:→Poly1 x) (Poly:→Poly1 y)
  Poly:→Poly1-pres+ x y = Poly:→Poly1-int-pres+ x y 0

-----------------------------------------------------------------------------
-- section

  e-sect-int : (x : Poly: Acr) → (n : ℕ) → Poly1→Poly: (Poly:→Poly1-int n x) ≡ prod-Xn n x
  e-sect-int = ElimProp _
               (λ n → sym (prod-Xn-0P: n))
               (λ a x ind-x n → cong (λ X → _+_ PA:str (prod-Xn n (a ∷ [])) X) (ind-x (suc n))
                                 ∙ prod-Xn-∷ n a x)
               (isPropΠ (λ _ → is-set PA:str _ _))

  e-sect : (x : Poly: Acr) → Poly1→Poly: (Poly:→Poly1 x) ≡ x
  e-sect x = e-sect-int x 0



-----------------------------------------------------------------------------
-- retraction

  idde : (m n : ℕ) → (a : A) → Poly:→Poly1-int n (prod-Xn m (a ∷ [])) ≡ base ((n +n m) :: <>) a
  idde zero n a = +IdR PAstr (base (n :: <>) a)
                  ∙ cong (λ X → base (X :: <>) a) (sym (+-zero n))
  idde (suc m) n a = cong (λ X → _+_ PAstr X (Poly:→Poly1-int (suc n) (prod-Xn m (a ∷ [])))) (base-neutral (n :: <>))
                     ∙ +IdL PAstr (Poly:→Poly1-int (suc n) (prod-Xn m (a ∷ [])))
                     ∙ idde m (suc n) a
                     ∙ cong (λ X → base (X :: <>) a) (sym (+-suc n m))

  idde-v : (v : Vec ℕ 1) → (a : A) → Poly:→Poly1-int 0 (trad-base v a) ≡ base v a
  idde-v (n :: <>) a = (idde n 0 a)


  e-retr : (P : Poly Acr 1) → Poly:→Poly1 (Poly1→Poly: P) ≡ P
  e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
           refl
           (λ v a → idde-v v a)
           λ {P Q} ind-P ind-Q → cong Poly:→Poly1 (Poly1→Poly:-pres+ P Q)
                                 ∙ Poly:→Poly1-pres+ (Poly1→Poly: P) (Poly1→Poly: Q)
                                 ∙ cong₂ (_+_ PAstr) ind-P ind-Q



-----------------------------------------------------------------------------
-- Ring morphism

  Poly1→Poly:-pres1 : Poly1→Poly: (1r PAstr) ≡ 1r PA:str
  Poly1→Poly:-pres1 = refl

  trad-base-prod : (v v' : Vec ℕ 1) → (a a' : A) → trad-base (v +n-vec v') (Astr ._·_ a a') ≡
                                                      _·_ PA:str (trad-base v a) (trad-base v' a')
  trad-base-prod (k :: <>) (l :: <>) a a' = sym ((prod-Xn-prod k l [ a ]  [ a' ]) ∙ cong (λ X → prod-Xn (k +n l) [ X ]) (+IdR Astr _))

  Poly1→Poly:-pres· : (P Q : Poly Acr 1) → Poly1→Poly: (_·_ PAstr P Q) ≡ _·_ PA:str (Poly1→Poly: P) (Poly1→Poly: Q)
  Poly1→Poly:-pres· = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ λ _ → is-set PA:str _ _)
                        (λ Q → refl)
                        (λ v a → DS-Ind-Prop.f _ _ _ _ (λ _ → is-set PA:str _ _)
                                  (sym (0RightAnnihilates (CommRing→Ring PA:) _))
                                  (λ v' a' → trad-base-prod v v' a a')
                                  λ {U V} ind-U ind-V → (cong₂ (_+_ PA:str) ind-U ind-V)
                                                          ∙ sym (·DistR+ PA:str _ _ _))
                        λ {U V} ind-U ind-V Q → (cong₂ (_+_ PA:str) (ind-U Q) (ind-V Q))
                                                 ∙ sym (·DistL+ PA:str _ _ _)



-----------------------------------------------------------------------------
-- Ring Equivalences

module _ (Acr : CommRing ℓ) where

  open Equiv-Poly1-Poly: Acr

  CRE-Poly1-Poly: : CommRingEquiv (PolyCommRing Acr 1) (UnivariatePolyList Acr)
  fst CRE-Poly1-Poly: = isoToEquiv is
    where
    is : Iso _ _
    Iso.fun is = Poly1→Poly:
    Iso.inv is = Poly:→Poly1
    Iso.rightInv is = e-sect
    Iso.leftInv is = e-retr
  snd CRE-Poly1-Poly: = makeIsRingHom
                        Poly1→Poly:-pres1
                        Poly1→Poly:-pres+
                        Poly1→Poly:-pres·
