{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.EquivCarac.Poly1-1Poly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec renaming ( [] to <> ; _∷_ to _::_)
open import Cubical.Data.Vec.OperationsNat

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.Univariate.Base
open import Cubical.Algebra.Polynomials.Univariate.Properties
open import Cubical.Algebra.CommRing.Instances.UnivariatePoly

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly

private variable
  ℓ : Level

module Equiv-Poly1-Poly: (A' : CommRing ℓ) where
  private
    A = fst A'

  open PolyMod A'
    renaming
    ( Poly               to Poly:
    ; isSetPoly          to isSetPoly:
    )

  open PolyModTheory A'
    renaming
    ( 0P                 to 0P:
    ; Poly-              to poly:-
    ; _Poly+_            to _poly:+_
    ; Poly+Lid           to poly:+IdL
    ; Poly+Rid           to poly:+IdR
    ; Poly+Assoc         to poly:+Assoc
    ; Poly+Inverses      to poly:+Inverses
    ; Poly+Comm          to poly:+Comm
    ; _Poly*_            to _poly:*_
    ; 1P                 to 1P:
    ; 0PRightAnnihilates to poly:*AnnihilR
    ; 0PLeftAnnihilates  to poly:*AnnihilL
    ; Poly*Lid           to poly:*IdL
    ; Poly*Rid           to poly:*IdR
    ; Poly*Associative   to poly:*Assoc
    ; Poly*Commutative   to poly:*Comm
    ; prod-Xn-0P         to prod-Xn-0P:
    )

  open Nth-Poly-structure A' 1

-- Notation P, Q, R... for Poly 1
-- x, y, w... for Poly:
-- a,b,c... for A


-----------------------------------------------------------------------------
-- direct

  trad-base : (v : Vec ℕ 1) → A → Poly:
  trad-base (n :: <>) a = prod-Xn n [ a ]

  trad-base-neutral : (v : Vec ℕ 1) → trad-base v 0r ≡ []
  trad-base-neutral (n :: <>) = cong (prod-Xn n) drop0 ∙ prod-Xn-0P: n

  trad-base-add : (v : Vec ℕ 1) → (a b : A) → (trad-base v a) poly:+ (trad-base v b) ≡ trad-base v (a + b)
  trad-base-add (n :: <>) a b = prod-Xn-sum n (a ∷ []) (b ∷ [])

  Poly1→Poly: : Poly A' 1 → Poly:
  Poly1→Poly: = Poly-Rec-Set.f A' 1 Poly: isSetPoly:
                 []
                 trad-base
                 (λ x y → x poly:+ y)
                 poly:+Assoc
                 poly:+IdR
                 poly:+Comm
                 trad-base-neutral
                 trad-base-add

  Poly1→Poly:-pres+ : (P Q : Poly A' 1) → Poly1→Poly: (P poly+ Q) ≡ (Poly1→Poly: P) poly:+ (Poly1→Poly: Q)
  Poly1→Poly:-pres+ P Q = refl



-----------------------------------------------------------------------------
-- converse

  Poly:→Poly1-int : (n : ℕ) → Poly: → Poly A' 1
  Poly:→Poly1-int n [] = 0P
  Poly:→Poly1-int n (a ∷ x) = (base (n :: <>) a) poly+ Poly:→Poly1-int (suc n) x
  Poly:→Poly1-int n (drop0 i) = ((cong (λ X → X poly+ 0P) (base-0P (n :: <>))) ∙ (poly+IdR 0P)) i

  Poly:→Poly1 : Poly: → Poly A' 1
  Poly:→Poly1 x = Poly:→Poly1-int 0 x

  Poly:→Poly1-int-pres+ : (x y : Poly:) → (n : ℕ) → Poly:→Poly1-int n (x poly:+ y) ≡ (Poly:→Poly1-int n x) poly+ (Poly:→Poly1-int n y)
  Poly:→Poly1-int-pres+ = ElimProp.f
                        (λ x → (y : Poly:) → (n : ℕ) → Poly:→Poly1-int n (x poly:+ y) ≡ (Poly:→Poly1-int n x poly+ Poly:→Poly1-int n y))
                        (λ y n → (cong (Poly:→Poly1-int n) (poly:+IdL y)) ∙ (sym (poly+IdL (Poly:→Poly1-int n y))))
                        (λ a x ind-x → ElimProp.f
                                        (λ y → (n : ℕ) → Poly:→Poly1-int n ((a ∷ x) poly:+ y) ≡ (Poly:→Poly1-int n (a ∷ x) poly+ Poly:→Poly1-int n y))
                                        (λ n → sym (poly+IdR (Poly:→Poly1-int n (a ∷ x))))
                                        (λ b y ind-y n → sym (
                                                          (poly-com-adv (base (n :: <>) a) (Poly:→Poly1-int (suc n) x) (base (n :: <>) b) (Poly:→Poly1-int (suc n) y))
                                                          ∙
                                                          (cong₂ _poly+_ (base-poly+ (n :: <>) a b) (sym (ind-x y (suc n))))) )
                                        λ {y} p q i n j → trunc
                                                          (Poly:→Poly1-int n ((a ∷ x) poly:+ y))
                                                          (Poly:→Poly1-int n (a ∷ x) poly+ Poly:→Poly1-int n y)
                                                          (p n) (q n) i j )
                        λ {x} p q i y n j → trunc (Poly:→Poly1-int n (x poly:+ y)) (Poly:→Poly1-int n x poly+ Poly:→Poly1-int n y) (p y n) (q y n) i j

  Poly:→Poly1-pres+ : (x y : Poly:) → Poly:→Poly1 (x poly:+ y) ≡ (Poly:→Poly1 x) poly+ (Poly:→Poly1 y)
  Poly:→Poly1-pres+ x y = Poly:→Poly1-int-pres+ x y 0

-----------------------------------------------------------------------------
-- section

  e-sect-int : (x : Poly:) → (n : ℕ) → Poly1→Poly: (Poly:→Poly1-int n x) ≡ prod-Xn n x
  e-sect-int = ElimProp.f
               (λ z → (n : ℕ) → Poly1→Poly: (Poly:→Poly1-int n z) ≡ prod-Xn n z)
               (λ n → sym (prod-Xn-0P: n))
               (λ a x ind-x n → ((prod-Xn n [ a ] ) poly:+ (Poly1→Poly: (Poly:→Poly1-int (suc n) x)))
                                    ≡⟨ cong (λ X → prod-Xn n [ a ] poly:+ X) (ind-x (suc n)) ⟩
                                 (prod-Xn n (a ∷ []) poly:+ ( 0r ∷ prod-Xn n x))
                                    ≡⟨ prod-Xn-∷ n a x ⟩
                                 prod-Xn n (a ∷ x) ∎)
               (λ {x} p q i n j → isSetPoly: (Poly1→Poly: (Poly:→Poly1-int n x)) (prod-Xn n x) (p n) (q n) i j)

  e-sect : (x : Poly:) → Poly1→Poly: (Poly:→Poly1 x) ≡ x
  e-sect x = e-sect-int x 0



-----------------------------------------------------------------------------
-- retraction

  idde : (m n : ℕ) → (a : A) → Poly:→Poly1-int n (prod-Xn m [ a ]) ≡ base ((n +n m) :: <>) a
  idde zero n a = poly+IdR (base (n :: <>) a) ∙ cong (λ X → base (X :: <>) a) (sym (+-zero n))
  idde (suc m) n a = cong (λ X → X poly+ Poly:→Poly1-int (suc n) (prod-Xn m (a ∷ []))) (base-0P (n :: <>))
                     ∙ poly+IdL (Poly:→Poly1-int (suc n) (prod-Xn m (a ∷ [])))
                     ∙ idde m (suc n) a
                     ∙ cong (λ X → base (X :: <>) a) (sym (+-suc n m))

  idde-v : (v : Vec ℕ 1) → (a : A) → Poly:→Poly1-int 0 (trad-base v a) ≡ base v a
  idde-v (n :: <>) a = (idde n 0 a)


  e-retr : (P : Poly A' 1) → Poly:→Poly1 (Poly1→Poly: P) ≡ P
  e-retr = Poly-Ind-Prop.f A' 1
           (λ P → Poly:→Poly1 (Poly1→Poly: P) ≡ P)
           (λ _ → trunc _ _)
           refl
           (λ v a → idde-v v a)
           λ {P Q} ind-P ind-Q → cong Poly:→Poly1 (Poly1→Poly:-pres+ P Q)
                                 ∙
                                 Poly:→Poly1-pres+ (Poly1→Poly: P) (Poly1→Poly: Q)
                                 ∙
                                 cong₂ _poly+_ ind-P ind-Q



-----------------------------------------------------------------------------
-- Ring morphism

  Poly1→Poly:-pres1 : Poly1→Poly: 1P ≡ 1P:
  Poly1→Poly:-pres1 = refl

  trad-base-prod : (v v' : Vec ℕ 1) → (a a' : A) → trad-base (v +n-vec v') (a · a') ≡
                                                      (trad-base v a poly:* trad-base v' a')
  trad-base-prod (k :: <>) (l :: <>) a a' = sym ((prod-Xn-prod k l  [ a ]  [ a' ]) ∙ cong (λ X → prod-Xn (k +n l) [ X ]) (+Rid (a · a')))

  Poly1→Poly:-pres· : (P Q : Poly A' 1) → Poly1→Poly: (P poly* Q) ≡ (Poly1→Poly: P) poly:* (Poly1→Poly: Q)
  Poly1→Poly:-pres· = Poly-Ind-Prop.f A' 1
                        (λ P → (Q : Poly A' 1) → Poly1→Poly: (P poly* Q) ≡ (Poly1→Poly: P poly:* Poly1→Poly: Q))
                        (λ P p q i Q j → isSetPoly: (Poly1→Poly: (P poly* Q)) (Poly1→Poly: P poly:* Poly1→Poly: Q) (p Q) (q Q) i j)
                        (λ Q → refl)
                        (λ v a → Poly-Ind-Prop.f A' 1
                                  (λ P → Poly1→Poly: (base v a poly* P) ≡ (Poly1→Poly: (base v a) poly:* Poly1→Poly: P))
                                  (λ _ → isSetPoly: _ _)
                                  (sym (poly:*AnnihilL (trad-base v a)))
                                  (λ v' a' → trad-base-prod v v' a a')
                                  λ {U V} ind-U ind-V → (cong₂ _poly:+_ ind-U ind-V)
                                                         ∙ sym (Poly*LDistrPoly+ (Poly1→Poly: (base v a)) (Poly1→Poly: U) (Poly1→Poly: V)))
                        λ {U V} ind-U ind-V Q → (cong₂ _poly:+_ (ind-U Q) (ind-V Q))
                                                 ∙ sym (Poly*RDistrPoly+ (Poly1→Poly: U) (Poly1→Poly: V) (Poly1→Poly: Q))



-- -----------------------------------------------------------------------------
-- -- Ring Equivalences

module _ (A' : CommRing ℓ) where

  open Equiv-Poly1-Poly: A'

  CRE-Poly1-Poly: : CommRingEquiv (PolyCommRing A' 1) (UnivariatePoly A')
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
