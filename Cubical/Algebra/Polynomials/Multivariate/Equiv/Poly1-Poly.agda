{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.Equiv.Poly1-Poly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec renaming ( [] to <> ; _∷_ to _::_)

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
    ; Poly-              to Poly:-
    ; _Poly+_            to _Poly:+_
    ; Poly+Lid           to Poly:+Lid
    ; Poly+Rid           to Poly:+Rid
    ; Poly+Assoc         to Poly:+Assoc
    ; Poly+Inverses      to Poly:+Inverses
    ; Poly+Comm          to Poly:+Comm
    ; _Poly*_            to _Poly:*_
    ; 1P                 to 1P:
    ; 0PRightAnnihilates to 0PRightAnnihilates:
    ; 0PLeftAnnihilates  to 0PLeftAnnihilates:
    ; Poly*Lid           to Poly:*Lid
    ; Poly*Rid           to Poly:*Rid
    ; Poly*Associative   to Poly:*Assoc
    ; Poly*Commutative   to Poly:*Comm
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

  trad-base-add : (v : Vec ℕ 1) → (a b : A) → (trad-base v a) Poly:+ (trad-base v b) ≡ trad-base v (a + b)
  trad-base-add (n :: <>) a b = prod-Xn-sum n (a ∷ []) (b ∷ [])

  Poly1→Poly: : Poly A' 1 → Poly:
  Poly1→Poly: = Poly-Rec-Set.f A' 1 Poly: isSetPoly:
                 []
                 trad-base
                 (λ x y → x Poly:+ y)
                 Poly:+Assoc
                 Poly:+Rid
                 Poly:+Comm
                 trad-base-neutral
                 trad-base-add

  Poly1→Poly:-gmorph : (P Q : Poly A' 1) → Poly1→Poly: (P Poly+ Q) ≡ (Poly1→Poly: P) Poly:+ (Poly1→Poly: Q)
  Poly1→Poly:-gmorph P Q = refl



-----------------------------------------------------------------------------
-- converse

  Poly:→Poly1-int : (n : ℕ) → Poly: → Poly A' 1
  Poly:→Poly1-int n [] = 0P
  Poly:→Poly1-int n (a ∷ x) = (base (n :: <>) a) Poly+ Poly:→Poly1-int (suc n) x
  Poly:→Poly1-int n (drop0 i) = ((cong (λ X → X Poly+ 0P) (base-0P (n :: <>))) ∙ (Poly+-Rid 0P)) i

  Poly:→Poly1 : Poly: → Poly A' 1
  Poly:→Poly1 x = Poly:→Poly1-int 0 x

  Poly:→Poly1-int-gmorph : (x y : Poly:) → (n : ℕ) → Poly:→Poly1-int n (x Poly:+ y) ≡ (Poly:→Poly1-int n x) Poly+ (Poly:→Poly1-int n y)
  Poly:→Poly1-int-gmorph = ElimProp.f
                        (λ x → (y : Poly:) → (n : ℕ) → Poly:→Poly1-int n (x Poly:+ y) ≡ (Poly:→Poly1-int n x Poly+ Poly:→Poly1-int n y))
                        (λ y n → (cong (Poly:→Poly1-int n) (Poly:+Lid y)) ∙ (sym (Poly+-Lid (Poly:→Poly1-int n y))))
                        (λ a x ind-x → ElimProp.f
                                        (λ y → (n : ℕ) → Poly:→Poly1-int n ((a ∷ x) Poly:+ y) ≡ (Poly:→Poly1-int n (a ∷ x) Poly+ Poly:→Poly1-int n y))
                                        (λ n → sym (Poly+-Rid (Poly:→Poly1-int n (a ∷ x))))
                                        (λ b y ind-y n → sym (
                                                          (Poly-com-adv (base (n :: <>) a) (Poly:→Poly1-int (suc n) x) (base (n :: <>) b) (Poly:→Poly1-int (suc n) y))
                                                          ∙
                                                          (cong₂ _Poly+_ (base-Poly+ (n :: <>) a b) (sym (ind-x y (suc n))))) )
                                        λ {y} p q i n j → trunc
                                                          (Poly:→Poly1-int n ((a ∷ x) Poly:+ y))
                                                          (Poly:→Poly1-int n (a ∷ x) Poly+ Poly:→Poly1-int n y)
                                                          (p n) (q n) i j )
                        λ {x} p q i y n j → trunc (Poly:→Poly1-int n (x Poly:+ y)) (Poly:→Poly1-int n x Poly+ Poly:→Poly1-int n y) (p y n) (q y n) i j

  Poly:→Poly1-gmorph : (x y : Poly:) → Poly:→Poly1 (x Poly:+ y) ≡ (Poly:→Poly1 x) Poly+ (Poly:→Poly1 y)
  Poly:→Poly1-gmorph x y = Poly:→Poly1-int-gmorph x y 0

-----------------------------------------------------------------------------
-- section

  e-sect-int : (x : Poly:) → (n : ℕ) → Poly1→Poly: (Poly:→Poly1-int n x) ≡ prod-Xn n x
  e-sect-int = ElimProp.f
               (λ z → (n : ℕ) → Poly1→Poly: (Poly:→Poly1-int n z) ≡ prod-Xn n z)
               (λ n → sym (prod-Xn-0P: n))
               (λ a x ind-x n → ((prod-Xn n [ a ] ) Poly:+ (Poly1→Poly: (Poly:→Poly1-int (suc n) x)))
                                    ≡⟨ cong (λ X → prod-Xn n [ a ] Poly:+ X) (ind-x (suc n)) ⟩
                                 (prod-Xn n (a ∷ []) Poly:+ ( 0r ∷ prod-Xn n x))
                                    ≡⟨ prod-Xn-∷ n a x ⟩
                                 prod-Xn n (a ∷ x) ∎)
               (λ {x} p q i n j → isSetPoly: (Poly1→Poly: (Poly:→Poly1-int n x)) (prod-Xn n x) (p n) (q n) i j)

  e-sect : (x : Poly:) → Poly1→Poly: (Poly:→Poly1 x) ≡ x
  e-sect x = e-sect-int x 0



-----------------------------------------------------------------------------
-- retraction

  idde : (m n : ℕ) → (a : A) → Poly:→Poly1-int n (prod-Xn m [ a ]) ≡ base ((n +n m) :: <>) a
  idde zero n a = Poly+-Rid (base (n :: <>) a) ∙ cong (λ X → base (X :: <>) a) (sym (+-zero n))
  idde (suc m) n a = cong (λ X → X Poly+ Poly:→Poly1-int (suc n) (prod-Xn m (a ∷ []))) (base-0P (n :: <>))
                     ∙ Poly+-Lid (Poly:→Poly1-int (suc n) (prod-Xn m (a ∷ [])))
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
           λ {P Q} ind-P ind-Q → cong Poly:→Poly1 (Poly1→Poly:-gmorph P Q)
                                 ∙
                                 Poly:→Poly1-gmorph (Poly1→Poly: P) (Poly1→Poly: Q)
                                 ∙
                                 cong₂ _Poly+_ ind-P ind-Q



-----------------------------------------------------------------------------
-- Ring morphism

  map-1P : Poly1→Poly: 1P ≡ 1P:
  map-1P = refl

  trad-base-prod : (v v' : Vec ℕ 1) → (a a' : A) → trad-base (v +n-vec v') (a · a') ≡
                                                      (trad-base v a Poly:* trad-base v' a')
  trad-base-prod (k :: <>) (l :: <>) a a' = sym ((prod-Xn-prod k l  [ a ]  [ a' ]) ∙ cong (λ X → prod-Xn (k +n l) [ X ]) (+Rid (a · a')))

  Poly1→Poly:-rmorph : (P Q : Poly A' 1) → Poly1→Poly: (P Poly* Q) ≡ (Poly1→Poly: P) Poly:* (Poly1→Poly: Q)
  Poly1→Poly:-rmorph = Poly-Ind-Prop.f A' 1
                        (λ P → (Q : Poly A' 1) → Poly1→Poly: (P Poly* Q) ≡ (Poly1→Poly: P Poly:* Poly1→Poly: Q))
                        (λ P p q i Q j → isSetPoly: (Poly1→Poly: (P Poly* Q)) (Poly1→Poly: P Poly:* Poly1→Poly: Q) (p Q) (q Q) i j)
                        (λ Q → refl)
                        (λ v a → Poly-Ind-Prop.f A' 1
                                  (λ P → Poly1→Poly: (base v a Poly* P) ≡ (Poly1→Poly: (base v a) Poly:* Poly1→Poly: P))
                                  (λ _ → isSetPoly: _ _)
                                  (sym (0PLeftAnnihilates: (trad-base v a)))
                                  (λ v' a' → trad-base-prod v v' a a')
                                  λ {U V} ind-U ind-V → (cong₂ _Poly:+_ ind-U ind-V)
                                                         ∙ sym (Poly*LDistrPoly+ (Poly1→Poly: (base v a)) (Poly1→Poly: U) (Poly1→Poly: V)))
                        λ {U V} ind-U ind-V Q → (cong₂ _Poly:+_ (ind-U Q) (ind-V Q))
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
  snd CRE-Poly1-Poly: = makeIsRingHom map-1P Poly1→Poly:-gmorph Poly1→Poly:-rmorph
