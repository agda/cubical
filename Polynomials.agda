{-A
Polynomials for Cubical Agda
============================
-}
{-# OPTIONS --cubical --no-import-sorts #-}

module Polynomials where

open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _Nat+_; _·_ to _Nat·_)
--open import Cubical.Data.Int hiding (_+_ ; _·_ ; _-_)

open import Cubical.Algebra.Group hiding (Bool)
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation renaming (map to ∥∥-map)
open import Cubical.Data.Nat.Order

open import Cubical.Functions.Logic

open import Cubical.Data.Bool


-- Obs: jag har senaste versionen av agda/cubical och saker är då lite
-- annorlunda organiserade och vissa saker har bytt namn
open import Cubical.Algebra.CommRing.Instances.BiInvInt
--open import Cubical.Data.Int.MoreInts.BiInvInt hiding (_-_)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

module PolyMod (R' : CommRing ℓ) where
  private
    R = fst R'
  open CommRingStr (snd R') public

  data Poly : Type ℓ where
    []    : Poly
    _∷_  : (a : R) → (p : Poly) → Poly
    drop0 : 0r ∷ [] ≡ []

  infixr 5 _∷_

  --postulate
  --  polyIsSet : isSet Poly

  -- Här skapar vi en modul med en funktion för att eliminera ett
  -- polynom. Genom att anropa Elim.f kan vi undvika att definiera
  -- saker genom mönstermatchning vilket gör saker lättare ibland.

  module Elim (B      : Poly → Type ℓ')                                   -- Familjen av typer som vi vill bevisa
              ([]*    : B [])                                             -- Fallet för []  (dvs basfallet)
              (cons*  : (r : R) (p : Poly) (b : B p) → B (r ∷ p))         -- Fallet för
              (drop0* : PathP (λ i → B (drop0 i)) (cons* 0r [] []*) []*) where

   f : (p : Poly) → B p
   f [] = []*
   f (x ∷ p) = cons* x p (f p)
   f (drop0 i) = drop0* i

  -- Ett användbart specialfall är när B är en familj av
  -- propositioner. Detta kan användas för att bevisa likheter mellan
  -- polynom. Detta fungerar då Poly är ett set (genom polyIsSet
  -- konstruktorn), så likheter mellan Poly's är propositioner. Detta
  -- låter oss undvika att skriva fall för drop0 och polyIsSet när vi
  -- bevisar den här typen av likheter (se Poly-Poly-P=P nedan).

  --given a proposition (as type) ϕ ranging over polynomials
  --usage: ElimProp.f ⌜ϕ⌝ ⌜base⌝ ⌜induction step⌝ ⌜proof that ϕ is a proposition over the domain of polynomials⌝
  module ElimProp (B : Poly → Type ℓ')                                  -- Familjen av typer som vi vill bevisa
                  ([]* : B [])                                          -- Fallet för []  (dvs basfallet)
                  (cons* : (r : R) (p : Poly) (b : B p) → B (r ∷ p))   -- Fallet för _∷_
                  (BProp : {p : Poly} → isProp (B p)) where             -- Antagandet som låter oss bevisa drop0 och polyIsSet en gång för alla

   f : (p : Poly) → B p
   f = Elim.f B []* cons* (toPathP (BProp (transport (λ i → B (drop0 i)) (cons* 0r [] []*)) []*))
              --kanske inte värt nu, men ElimProp kan skrivas för formler med mer än 1 argument - sätter då B med två Poly-argument

  module Rec (B : Type ℓ')
             ([]* : B)
             (cons* : R → B → B)
             (drop0* : cons* 0r []* ≡ []*)
                          (Bset : isSet B) where
    f : Poly → B
    f = Elim.f (λ _ → B) []* (λ r p b → cons* r b) drop0*


  --module RecPoly' ([]* : Poly)
  --               (cons* : R → Poly → Poly)
  --               (drop0* : cons* 0r []* ≡ []*) where
  --  f : Poly → Poly
  -- f p = Rec.f Poly []* cons* drop0* polyIsSet p


  module RecPoly ([]* : Poly) (cons* : R → Poly → Poly) (drop0* : cons* 0r []* ≡ []*) where
    f : Poly → Poly
    f [] = []*
    f (a ∷ p) = cons* a (f p)
    f (drop0 i) = drop0* i



-------------------------------------------------------------------------------------------






--alternativ def
--placera som modul i modulen
  --open import Cubical.Data.Sigma
  --open import Cubical.HITs.PropositionalpolyIsSetation
  --open import Cubical.Data.Nat.Order

  --module PolyMod' (R' : CommRing ℓ) where
    --private                                                                                                                                                                                                                                  --                                      Rₐ = fst R'
    --open CommRingStr (snd R') public


  Poly' : Type ℓ
  Poly' = Σ[ p ∈ (ℕ → R) ] (∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → p m ≡ 0r))

--Kolla in Cubical.Foundations.HLevels, finns lemman för sigma-typer


  isSetPoly' : isSet Poly'
  isSetPoly' = isSetΣSndProp (isSetΠ (λ _ → is-set)) λ _ → squash

  isZero : ℕ → Bool
  isZero zero = true
  isZero (suc n) = false

  Poly→Fun : Poly → (ℕ → R)
  Poly→Fun [] = (λ _ → 0r)
  Poly→Fun (a ∷ p) = (λ n → if isZero n then a else Poly→Fun p (predℕ n))
  Poly→Fun (drop0 i) = foo i
    where
    foo : (λ n → if isZero n then 0r else 0r) ≡ (λ _ → 0r)
    foo i zero = 0r
    foo i (suc n) = 0r

  Poly→Prf : (p : Poly) → ∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → Poly→Fun p m ≡ 0r)
  Poly→Prf = ElimProp.f (λ (p : Poly) → ∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → Poly→Fun p m ≡ 0r))
                        ∣ 0 , (λ _ _ → refl) ∣
                        (λ a p b → ∥∥-map (λ { (n , q) → suc n , λ { zero h → ⊥-rec (¬-<-zero h)
                                                                   ; (suc m) → λ h → q m (predℕ-≤-predℕ h) }}) b)
                        squash

  --  --Poly' = Σ[ p ∈ (ℕ → R) ] (∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → p m ≡ 0r))
  Poly→Poly' : Poly → Poly'
  Poly→Poly' p = (Poly→Fun p) , (Poly→Prf p)

  -- TODO: define the unique polynomial with minimal degree
  Poly'→Poly : Poly' → Poly
  Poly'→Poly (p , ∣ 0 , h ∣) = []
  Poly'→Poly (p , ∣ suc n , h ∣) = p 0 ∷ Poly'→Poly (p ∘ suc , ∣ n , (λ m p → h (suc m) (suc-≤-suc p)) ∣)
  Poly'→Poly (p , squash q r i) = {!!}

  lemmaisSet : (p : Poly) → Poly'→Poly (Poly→Poly' p) ≡ p
  lemmaisSet [] = {!!}
  lemmaisSet (a ∷ p) = {!!}
  lemmaisSet (drop0 i) = {!!}


  isSetPoly : isSet Poly
  isSetPoly = isSetRetract Poly→Poly'
                           Poly'→Poly
                           (λ p → lemmaisSet p)
                           isSetPoly'



   --Poly' = Σ[ p ∈ (ℕ → R) ] (∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → p m ≡ 0r))

--  open import Cubical.Data.Sigma
--  open import Cubical.HITs.PropositionalpolyIsSetation
--  open import Cubical.Data.Nat.Order

--Poly' = Σ[ p ∈ (ℕ → R) ] (∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → p m ≡ 0r))

--Att visa

--  isSet Poly'

--är relativt lätt och är mest en fråga om att kombinera lemman från Cubical.Foundations.HLevels.
--När vi har detta räcker det att använda isSetRetract som säger att om vi har funktioner

--f : Poly -> Poly'
--g : Poly' -> Poly

--som uppfyller
--r : (x : Poly) → g (f x) ≡ x
--då är Poly är det ett set.



--------------------------------------------------------------------------------------------


---- Vi jobbar bara med polynom över heltal (som heter BiInvℤ numera)
---- för tillfället. Vissa saker blir mer komplicerade om man skulle
---- göra dom med en godtycklig kommutativ ring R, så vi kan vänta med
---- att generalisera.

open PolyMod BiInvℤAsCommRing public
open CommRingTheory BiInvℤAsCommRing
open RingTheory (CommRing→Ring BiInvℤAsCommRing)
open GroupTheory (Ring→Group (CommRing→Ring BiInvℤAsCommRing))
--open GroupTheory ()

pattern [_] x = x ∷ []


--OBS ändra här sen
polyIsSet : isSet Poly
polyIsSet = isSetPoly





-------------------------------------------------------------
--Definition
--Identity for Poly+
-------------------------------------------------------------

0P : Poly
0P = []

--Given a polynomial, p, of degree m, and a natural number, n,
--replicatePoly(n,p) returns p +
replicatePoly : (n : ℕ)  → Poly
replicatePoly zero  = 0P
replicatePoly (suc n) = 0r ∷ replicatePoly n


0P=nollor : ∀ (n : ℕ) → replicatePoly n  ≡ 0P
0P=nollor zero = refl
0P=nollor (suc n) = (cong (0r ∷_) (0P=nollor n)) ∙ drop0


--is0_∷_[] : Poly → Cubical.Data.Bool.Bool --hur får jag denna att checka med enbart bool - hide verkar inte funka där uppe.
--is0_∷_[] PolyMod.[] = false
--is0_∷_[] (a PolyMod.∷ p) = {!0r + a = 0r!}
--is0_∷_[] (PolyMod.drop0 i) = {!!}

----return the canonical representation of the polynomial, ie., all zeros dropped.
--canonicalReprPoly : Poly → Poly
--canonicalReprPoly (0r ∷ []) = []
--canonicalReprPoly [] = []
--canonicalReprPoly (a ∷ p) = {!if ((is0r a) ∧ (is[] p)) then [] else  !} --with a = 0r AND p = []  = []  {!!}
--canonicalReprPoly (drop0 i) = {!!}


-------------------------------------------------------------
-- Definition
-- Poly-
-------------------------------------------------------------

Poly- : Poly → Poly
Poly- [] = 0P
Poly- (a ∷ p) = (- a) ∷ Poly- p
Poly- (drop0 i) = drop0 i -- Obs: detta är ett ställe där det blir lite mer omständigt för en godtycklig kommutativ ring R då - 0 inte är exakt samma som 0!


Poly-Poly-P=P : (p : Poly) → Poly- (Poly- p) ≡ p
Poly-Poly-P=P = ElimProp.f (λ x → Poly- (Poly- x) ≡ x)
                           (refl)
                           (λ a p e → cong (_∷ (Poly- (Poly- p))) (-Idempotent a) ∙ cong (a ∷_ ) (e))
                           (polyIsSet _ _)






-------------------------------------------------------------
--Definition
--Poly+
-------------------------------------------------------------

_Poly+_ : Poly → Poly → Poly
p Poly+ [] = p
[] Poly+ (a ∷ q) = a ∷ q
[] Poly+ (drop0 i) = drop0 i
(a ∷ p) Poly+ (b ∷ q) = (a + b) ∷ (p Poly+ q)
(drop0 i) Poly+ (a ∷ q) = foo q i  where
                               foo : ∀ q → (0r + a) ∷ ([] Poly+ q) ≡ a ∷ q
                               foo = ElimProp.f (λ q → (0r + a) ∷ ([] Poly+ q) ≡ a ∷ q)
                                                (λ i → (+Lid a i ∷ []))
                                                (λ r p _ → λ i → +Lid a i ∷ r ∷ p )
                                                (isSetPoly _ _)
(a ∷ p) Poly+ (drop0 i) = +Rid a i ∷ p
(drop0 i) Poly+ (drop0 j) =  isSet→isSet' isSetPoly  (cong ([_] ) (+Rid 0r)) drop0 ((cong ([_] ) (+Lid 0r))) drop0 i j


--[] är nollan
Poly+Lid : ∀ p → ([] Poly+ p ≡ p)
Poly+Lid =  ElimProp.f (λ p → ([] Poly+ p ≡ p) )
                       (refl)
                       (λ r p prf → refl)
                       (λ x y → polyIsSet _ _ x y)





-------------------------------------------------------------
-- Theorem
-- [] is the right identity for Poly+
-------------------------------------------------------------

Poly+Rid : ∀ p → (p Poly+ [] ≡ p)
Poly+Rid = λ p → refl





-------------------------------------------------------------
--Theorem 1
--Poly+ is Associative
-------------------------------------------------------------

Poly+Assoc : ∀ p q r → p Poly+ (q Poly+ r) ≡ (p Poly+ q) Poly+ r
Poly+Assoc =
  ElimProp.f (λ p → (∀ q r → p Poly+ (q Poly+ r) ≡ (p Poly+ q) Poly+ r))
             (λ q r → Poly+Lid (q Poly+ r) ∙ cong (_Poly+ r)  (sym (Poly+Lid q)))
             (λ a p prf → ElimProp.f ((λ q → ∀ r → ((a ∷ p) Poly+ (q Poly+ r)) ≡ (((a ∷ p) Poly+ q) Poly+ r)))
                                     (λ r → cong ((a ∷ p) Poly+_) (Poly+Lid r))
                                     (λ b q prf2 →
                                       ElimProp.f (λ r → ((a ∷ p) Poly+ ((b ∷ q) Poly+ r)) ≡ ((a + b ∷ (p Poly+ q)) Poly+ r))
                                                  refl
                                                  (λ c r prfp → cong ((a + (b + c))∷_) (prf q r) ∙ cong (_∷ ((p Poly+ q) Poly+ r)) (+Assoc a b c))
                                                  (polyIsSet _ _))
                                     λ x y i r → polyIsSet (x r i0) (y r i1) (x r) (y r) i) --FRÅGA: Blir detta verkligen rätt???
             λ x y i q r  → polyIsSet _ _ (x q r) (y q r) i




-------------------------------------------------------------
-- Theorem
-- for any polynomial, p, the additive inverse is given by: Poly- p
-------------------------------------------------------------

Poly+Inverses : ∀ p → p Poly+ (Poly- p) ≡ []
Poly+Inverses = ElimProp.f ( λ p → p Poly+ (Poly- p) ≡ [])
                           refl
                           (λ r p prf → cong (r + - r ∷_ ) prf ∙ cong (_∷ []) (lemma r) ∙ drop0)
                           (polyIsSet _ _) where
                                       lemma : ∀ r → r + - r ≡ 0r
                                       lemma = λ r → +Rinv r





-------------------------------------------------------------
--Theorem 2
--Poly+ is commutative
-------------------------------------------------------------

Poly+Comm : ∀ p q → p Poly+ q ≡ q Poly+ p
Poly+Comm = ElimProp.f (λ p → (∀ q → p Poly+ q ≡ q Poly+ p))
                       (λ q → Poly+Lid q)
                       (λ a p prf → ElimProp.f (λ q → ((a ∷ p) Poly+ q) ≡ (q Poly+ (a ∷ p)) )
                                               refl
                                               (λ b q prf2 → cong (_∷ (p Poly+ q)) (+Comm a b ) ∙ cong ((b + a) ∷_) (prf q))
                                               (polyIsSet _ _)
                       )
                       (λ {p} → isPropΠ (λ q → polyIsSet (p Poly+ q) (q Poly+ p)))


_PolyConst*_ : (fst BiInvℤAsCommRing) → Poly → Poly
r PolyConst* [] = []
r PolyConst* (a ∷ p) = (r · a) ∷ (r PolyConst* p)
r PolyConst* (drop0 i) = foo r i where
                               foo : ∀ r → [ r · 0r ] ≡ []
                               foo =  λ r → [ r · 0r ] ≡⟨ cong (_∷ []) (0RightAnnihilates r) ⟩
                                      [ 0r ] ≡⟨ drop0 ⟩
                                      [] ∎


0rLeftAnnihilatesPoly : ∀ q → 0r PolyConst* q ≡ [ 0r ]
0rLeftAnnihilatesPoly = ElimProp.f (λ q → 0r PolyConst* q ≡ [ 0r ])
                                       (sym drop0)
                                       (λ r p prf → cong ((0r · r) ∷_) prf ∙ cong (_∷ [ 0r ]) (0LeftAnnihilates r) ∙ cong (0r ∷_) drop0 )
                                       λ x y → polyIsSet _ _ x y


PolyConst*Lid : ∀ q → 1r PolyConst* q ≡ q
PolyConst*Lid = ElimProp.f (λ q → 1r PolyConst* q ≡ q ) refl
                                                                   (λ a p prf → cong (_∷ (1r PolyConst* p)) (·Lid a) ∙
                                                                          cong (a ∷_) (prf) )
                                                                   λ x y → polyIsSet _ _ x y





-------------------------------------------------------------
--Definition
--Poly*
-------------------------------------------------------------

_Poly*_ : Poly → Poly → Poly
[] Poly* q = []
(a ∷ p) Poly* q = (a PolyConst* q) Poly+ (0r ∷ (p Poly* q))
(drop0 i) Poly* q = foo q i where
                             foo : ∀ q → (0r PolyConst* q) Poly+ [ 0r ] ≡ []
                             foo = λ q → ((0r PolyConst* q) Poly+ [ 0r ]) ≡⟨ cong ( _Poly+ [ 0r ] ) (0rLeftAnnihilatesPoly q)⟩
                                         ([ 0r ] Poly+ [ 0r ]) ≡⟨ cong (_∷ []) 0Idempotent  ∙ drop0 ⟩
                                         [] ∎





-------------------------------------------------------------
--Definition
--Identity for Poly*
-------------------------------------------------------------

1P : Poly
1P = [ 1r ]


0PRightAnnihilates : ∀ q → 0P Poly* q ≡ 0P
0PRightAnnihilates = ElimProp.f (λ q → 0P Poly* q ≡ 0P)
                                refl
                                (λ r p prf → prf)
                                λ x y → polyIsSet _ _ x y


0PLeftAnnihilates : ∀ p → p Poly* 0P ≡ 0P
0PLeftAnnihilates = ElimProp.f (λ p → p Poly* 0P ≡ 0P )
                               refl
                               (λ r p prf → cong (0r ∷_) prf ∙ drop0)
                               λ x y → polyIsSet _ _ x y



Poly*Lid : ∀ q → 1P Poly* q ≡ q
Poly*Lid = ElimProp.f (λ q → 1P Poly* q ≡ q)
                            drop0
                            (λ r p prf → lemma r p)
                            λ x y → polyIsSet _ _ x y where
                                                  lemma : ∀ r p → 1r · r + 0r ∷ (1r PolyConst* p) ≡ r ∷ p
                                                  lemma = λ r p → 1r · r + 0r ∷ (1r PolyConst* p) ≡⟨ cong (_∷ (1r PolyConst* p) ) (+Rid (1r · r)) ⟩
                                                                  1r · r ∷ (1r PolyConst* p) ≡⟨ cong (_∷ 1r PolyConst* p) (·Lid r) ⟩
                                                                  r ∷ (1r PolyConst* p) ≡⟨ cong (r ∷_) (PolyConst*Lid p) ⟩
                                                                  r ∷ p ∎







XLDistrPoly+ : ∀ p q → (0r ∷ (p Poly+ q)) ≡ ((0r ∷ p) Poly+ (0r ∷ q))
XLDistrPoly+ = ElimProp.f (λ p → ∀ q → (0r ∷ (p Poly+ q)) ≡ ((0r ∷ p) Poly+ (0r ∷ q)) )
                     (λ q → (cong (0r ∷_) (Poly+Lid q)) ∙
                             cong (0r ∷_) (sym (Poly+Lid q)) ∙
                             sym (cong (_∷ [] Poly+ q) (+Lid 0r)))
                             --0r ∷ ((a ∷ p) Poly+ q) ≡ 0r + 0r ∷ ((a ∷ p) Poly+ q)
                      (λ a p prf → ElimProp.f (λ q → 0r ∷ ((a ∷ p) Poly+ q) ≡ ((0r ∷ a ∷ p) Poly+ (0r ∷ q)))
                                              (cong (_∷ a ∷ p ) (sym (+Lid 0r)))
                                              (λ b q prf2 → cong (_∷ a + b ∷ (p Poly+ q)) (sym (+Lid 0r)))
                                              λ x y i → polyIsSet (x i0) (x i1) x y i)
                     λ x y i q → polyIsSet (x q i0) (x q i1) (x q) (y q) i


PolyConst*LDistrPoly+ : ∀ a p q → a PolyConst* (p Poly+ q) ≡ (a PolyConst* p) Poly+ (a PolyConst* q)
PolyConst*LDistrPoly+ = λ a → ElimProp.f (λ p → ∀ q → a PolyConst* (p Poly+ q) ≡ (a PolyConst* p) Poly+ (a PolyConst* q))
                                   (λ q → cong (a PolyConst*_) (Poly+Lid q) ∙
                                          (sym (Poly+Lid (a PolyConst* q))))
                                   (λ b p prf → ElimProp.f (λ q → (a PolyConst* ((b ∷ p) Poly+ q)) ≡ ((a PolyConst* (b ∷ p)) Poly+ (a PolyConst* q)))
                                                           refl
                                                           (λ c q prf2  → cong (_∷ (a PolyConst* (p Poly+ q))) (·Rdist+ a b c) ∙
                                                                          cong (a · b + a · c ∷_) (prf q))
                                                           (polyIsSet _ _)
                                    )
                                   λ x y i q  → polyIsSet (x q i0) (x q i1) (x q) (y q) i




-------------------------------------------------------------
--Theorem
--Poly* left distributes over Poly+
-------------------------------------------------------------

Poly*LDistrPoly+ : ∀ p q r → p Poly* (q Poly+ r) ≡ (p Poly* q) Poly+ (p Poly* r)
Poly*LDistrPoly+ = ElimProp.f (λ p → ∀ q r → p Poly* (q Poly+ r) ≡ (p Poly* q) Poly+ (p Poly* r))
                                   (λ _ _ → refl)
                                   (λ a p prf q r → ((a PolyConst* (q Poly+ r)) Poly+ (0r ∷(p Poly*(q Poly+ r)))) ≡⟨
                                                                                 cong (_Poly+ (0r ∷ (p Poly* (q Poly+ r)))) (PolyConst*LDistrPoly+ a q r)⟩
                                                    (((a PolyConst* q) Poly+ (a PolyConst* r)) Poly+ (0r ∷ (p Poly* (q Poly+ r)))) ≡⟨
                                                                                 cong (((a PolyConst* q) Poly+ (a PolyConst* r)) Poly+_) (cong (0r ∷_) (prf q r)) ⟩
                                                    (((a PolyConst* q) Poly+ (a PolyConst* r)) Poly+ (0r ∷ ((p Poly* q) Poly+ (p Poly* r)))) ≡⟨
                                                                         cong (((a PolyConst* q) Poly+ (a PolyConst* r)) Poly+_) (XLDistrPoly+ (p Poly* q) (p Poly* r)) ⟩
                                                    (((a PolyConst* q) Poly+ (a PolyConst* r)) Poly+ ((0r ∷ (p Poly* q)) Poly+ (0r ∷ (p Poly* r)))) ≡⟨
                                                                     Poly+Assoc ((a PolyConst* q) Poly+ (a PolyConst* r)) (0r ∷ (p Poly* q)) (0r ∷ (p Poly* r)) ⟩
                                                    (((a PolyConst* q) Poly+ (a PolyConst* r)) Poly+ (0r ∷ (p Poly* q))) Poly+ (0r ∷ (p Poly* r)) ≡⟨
                                                                     cong (_Poly+ (0r ∷ (p Poly* r))) (sym (Poly+Assoc (a PolyConst* q)  (a PolyConst* r)  (0r ∷ (p Poly* q))))  ⟩
                                                    (((a PolyConst* q) Poly+ ((a PolyConst* r) Poly+ (0r ∷ (p Poly* q)))) Poly+ (0r ∷ (p Poly* r))) ≡⟨
                                                                cong (_Poly+ (0r ∷ (p Poly* r))) (cong ((a PolyConst* q) Poly+_) (Poly+Comm (a PolyConst* r)(0r ∷ (p Poly* q)))) ⟩
                                                    ( ((a PolyConst* q) Poly+ ((0r ∷ (p Poly* q)) Poly+ (a PolyConst* r))) Poly+ (0r ∷ (p Poly* r)) ) ≡⟨
                                                                cong (_Poly+ (0r ∷ (p Poly* r))) (Poly+Assoc (a PolyConst* q) (0r ∷ (p Poly* q)) (a PolyConst* r)) ⟩
                                                    ((((a PolyConst* q) Poly+ (0r ∷ (p Poly* q))) Poly+ (a PolyConst* r)) Poly+ (0r ∷ (p Poly* r))) ≡⟨
                                                                sym (Poly+Assoc ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q))) ((a PolyConst* r)) ((0r ∷ (p Poly* r)))) ⟩
                                                    ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q))) Poly+ ((a PolyConst* r) Poly+ (0r ∷ (p Poly* r))) ∎
                                   )
                                   (λ x y i q r → polyIsSet _ _ (x q r) (y q r) i)


----------------------------------------------
--Lemmas for the associativity proof of Poly*
----------------------------------------------

PolyConst*rEqualsPoly*[r] : ∀ a p → a PolyConst* p ≡ p Poly* [ a ]
PolyConst*rEqualsPoly*[r] = λ a → ElimProp.f (λ p → a PolyConst* p ≡ p Poly* [ a ])
                              refl
                              (λ r p prf →  a · r ∷ (a PolyConst* p) ≡⟨ cong (a · r ∷_) prf ⟩
                                            a · r ∷ (p Poly* [ a ]) ≡⟨ cong (a · r ∷_) (sym (Poly+Lid (p Poly* [ a ]))) ⟩
                                            a · r ∷ ([] Poly+ (p Poly* [ a ])) ≡⟨ cong (_∷ ([] Poly+ (p Poly* [ a ]))) (PolyMod.·-comm BiInvℤAsCommRing a r) ⟩
                                            r · a ∷ ([] Poly+ (p Poly* [ a ])) ≡⟨ cong (_∷ ([] Poly+ (p Poly* [ a ]))) (sym (+Rid (r · a))) ⟩
                                            r · a + 0r ∷ ([] Poly+ (p Poly* [ a ])) ∎)
                              λ x y i → polyIsSet (x i0) (x i1) x y i




PolyConst*Nested· : ∀ a b p → a PolyConst* (b PolyConst* p) ≡ (a · b) PolyConst* p
PolyConst*Nested· = λ a b → ElimProp.f (λ p → a PolyConst* (b PolyConst* p) ≡ (a · b) PolyConst* p)
                             refl
                             (λ c p prf → cong ((a · (b · c)) ∷_) prf ∙
                                          cong (_∷ ((a · b) PolyConst* p)) (·Assoc a b c))
                             (polyIsSet _ _)




--Kortare bevis?
--Xp*q=X*pq : ∀ p q → (0r ∷ p) Poly* q  ≡ 0r ∷ (p Poly* q)
--Xp*q=X*pq = ElimProp.f (λ p → ∀ q → (0r ∷ p) Poly* q  ≡ 0r ∷ (p Poly* q))
--                     (λ q → cong (_Poly+ [ 0r ]) (0rLeftAnnihilatesPoly q) ∙
--                            cong (_∷ []) (+Lid 0r))
--                     (λ a p prf q → cong (_Poly+ (0r ∷ ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q))))) ((0rLeftAnnihilatesPoly q) ∙
--                                                                                                      drop0)
--                                                                                                     )
--                     λ x y i q → polyIsSet (x q i0) (x q i1) (x q) (y q) i




Xp*q=X*pq : ∀ p q → (0r ∷ p) Poly* q ≡ 0r ∷ (p Poly* q)
Xp*q=X*pq = ElimProp.f (λ p → ∀ q → (0r ∷ p) Poly* q ≡ 0r ∷ (p Poly* q))
                     (λ q → cong (_Poly+ [ 0r ])((cong (_Poly+ []) (0rLeftAnnihilatesPoly q))) ∙
                            cong (_∷ []) (+Lid 0r)
                     )
                     (λ r p b q → cong (_Poly+ (0r ∷ ((r PolyConst* q) Poly+ (0r ∷ (p Poly* q))))) (0rLeftAnnihilatesPoly q) ∙
                                  cong (_∷ ([] Poly+ ((r PolyConst* q) Poly+ (0r ∷ (p Poly* q))))) (+Lid 0r) ∙
                                  cong (0r ∷_) (Poly+Lid ((r PolyConst* q) Poly+ (0r ∷ (p Poly* q)))))
                     λ x y i q → polyIsSet _ _ (x q) (y q) i

PolyConst*AssocPoly* : ∀ a p q → a PolyConst* (p Poly* q) ≡ (a PolyConst* p) Poly* q
PolyConst*AssocPoly* = λ a → ElimProp.f (λ p → ∀ q → a PolyConst* (p Poly* q) ≡ (a PolyConst* p) Poly* q  )
                           (λ q → refl)
                           --(a PolyConst* ((b PolyConst* q) Poly+ (0r ∷ (p Poly* q)))) ≡ (((a · b) PolyConst* q) Poly+ (0r ∷ ((a PolyConst* p) Poly* q)))
                           (λ b p prf q → a PolyConst* ((b PolyConst* q) Poly+ (0r ∷ (p Poly* q)))  ≡⟨
                                                                      PolyConst*LDistrPoly+ a (b PolyConst* q) (0r ∷ (p Poly* q)) ⟩
                                          (a PolyConst* (b PolyConst* q)) Poly+ (a PolyConst* (0r ∷ (p Poly* q))) ≡⟨
                                                                      cong (_Poly+ (a · 0r ∷ (a PolyConst* (p Poly* q)))) (PolyConst*Nested· a b q) ⟩
                                          ((a · b) PolyConst* q) Poly+ (a PolyConst* (0r ∷ (p Poly* q))) ≡⟨
                                                                      cong (((a · b) PolyConst* q) Poly+_) (cong (a · 0r  ∷_) (PolyConst*rEqualsPoly*[r] a (p Poly* q))) ⟩
                                          ((a · b) PolyConst* q) Poly+ (a · 0r ∷ ((p Poly* q) Poly* [ a ])) ≡⟨ --detta funkar ej?
                                                                       cong (((a · b) PolyConst* q) Poly+_) (cong (_∷ ((p Poly* q) Poly* [ a ])) (0RightAnnihilates a))  ⟩
                                          ((a · b) PolyConst* q) Poly+ (0r ∷ ((p Poly* q) Poly* [ a ])) ≡⟨
                                                                      cong (((a · b) PolyConst* q) Poly+_) (cong (0r ∷_) (sym (PolyConst*rEqualsPoly*[r] a (p Poly* q)))) ⟩
                                          ((a · b) PolyConst* q) Poly+ (0r ∷ (a PolyConst* (p Poly* q))) ≡⟨
                                                               cong (((a · b) PolyConst* q) Poly+_) (cong (0r ∷_) (prf q)) ⟩
                                          ((a · b) PolyConst* q) Poly+ (0r ∷ ((a PolyConst* p) Poly* q)) ∎
                           )
                           λ x y i q → polyIsSet (x q i0) (x q i1) (x q) (y q) i




p*Xq=X*pq : ∀ p q → p Poly* (0r ∷  q) ≡ 0r ∷ (p Poly* q)
p*Xq=X*pq = ElimProp.f (λ p → ∀ q → p Poly* (0r ∷  q) ≡ 0r ∷ (p Poly* q))
                            (λ q → sym drop0)
                            --a · 0r + 0r ∷ ((a PolyConst* q) Poly+ (p Poly* (0r ∷ q))) ≡ 0r ∷ ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q)))
                            (λ a p prf q → ((a ∷ p) Poly* (0r ∷ q))  ≡⟨ cong ( a · 0r + 0r ∷_) (cong (((a PolyConst* q)) Poly+_ ) (prf q)) ⟩
                                           a · 0r + 0r ∷ ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q))) ≡⟨ cong (_∷ ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q)))) ((+Rid (a · 0r))) ⟩
                                           a · 0r ∷ ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q))) ≡⟨ cong (_∷ ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q)))) (0RightAnnihilates a) ⟩
                                           0r ∷ ((a PolyConst* q) Poly+ (0r ∷ (p Poly* q))) ∎
                            )                                                              --Vad blir fel här?
                            λ x y i q  → polyIsSet (x q i0) (x q i1) (x q) (y q) i


Xp*q=p*Xq : ∀ p q → (0r ∷ p) Poly* q ≡ p Poly* (0r ∷ q)
Xp*q=p*Xq = ElimProp.f (λ p → ∀ q → (0r ∷ p) Poly* q ≡ p Poly* (0r ∷ q) )
                       (λ q → cong ((0r PolyConst* q) Poly+_) drop0 ∙
                                   0rLeftAnnihilatesPoly q ∙
                                   drop0)
                       (λ a p prf q → ((0r ∷ a ∷ p) Poly* q) ≡⟨ Xp*q=X*pq (a ∷ p) q ⟩
                                      0r ∷ ((a ∷ p) Poly* q) ≡⟨ sym (p*Xq=X*pq (a ∷ p) q) ⟩
                                      ((a ∷ p) Poly* (0r ∷ q)) ∎
                       )
                       λ x y i q → polyIsSet (x q i0) (x q i1) (x q) (y q) i






-------------------------------------------------------------
--Theorem
--Poly* is commutative
-------------------------------------------------------------

Poly*Commutative : ∀ p q → p Poly* q ≡ q Poly* p
Poly*Commutative = ElimProp.f (λ p → ∀ q → p Poly* q ≡ q Poly* p)
                              (λ q → sym (0PLeftAnnihilates q))
                              (λ a p prf q → (a PolyConst* q) Poly+ (0r ∷ (p Poly* q))  ≡⟨
                                                           cong ((a PolyConst* q) Poly+_) (cong (0r ∷_) (prf q)) ⟩
                                             (a PolyConst* q) Poly+ (0r ∷ (q Poly* p)) ≡⟨
                                                           cong ((a PolyConst* q) Poly+_) (sym (Xp*q=X*pq q p)) ⟩
                                             (a PolyConst* q) Poly+ ((0r ∷ q) Poly* p) ≡⟨
                                                           cong ( _Poly+ ((0r PolyConst* p) Poly+ (0r ∷ (q Poly* p)))) (PolyConst*rEqualsPoly*[r] a q) ⟩
                                             (q Poly* [ a ]) Poly+ ((0r ∷ q) Poly* p) ≡⟨ cong ((q Poly* [ a ]) Poly+_) (Xp*q=p*Xq q p) ⟩
                                             (q Poly* [ a ]) Poly+ (q Poly* (0r ∷ p)) ≡⟨ sym (Poly*LDistrPoly+ q [ a ] (0r ∷ p)) ⟩
                                             ((q Poly* ([ a ] Poly+ (0r ∷ p)))) ≡⟨ cong (q Poly*_) (Poly+Comm [ a ] (0r ∷ p)) ⟩
                                             (q Poly* ((0r ∷ p) Poly+ [ a ])) ∎
                              )

                              (λ x y i q → polyIsSet _ _ (x q ) (y q) i)


-------------------------------------------------------------
--Theorem
--1P is the right identity of Poly*
-------------------------------------------------------------

Poly*Rid : ∀ p → p Poly* 1P ≡ p
Poly*Rid = λ p → (Poly*Commutative p 1P ∙ Poly*Lid p)



--Kanske bör ordningen på argumenten vara lite annorlunda
Poly*RDistrPoly+ : ∀ p q r → (p Poly+ q) Poly* r ≡ (p Poly* r) Poly+ (q Poly* r)
Poly*RDistrPoly+ = λ p q r → sym (Poly*Commutative r (p Poly+ q)) ∙
                                       Poly*LDistrPoly+ r p q ∙
                                       cong (_Poly+ (r Poly* q)) (Poly*Commutative r p) ∙
                                       cong ((p Poly* r) Poly+_) (Poly*Commutative r q)





-------------------------------------------------------------
--Theorem
--Poly* is Associative
-------------------------------------------------------------

Poly*Associative : ∀ p q r → p Poly* (q Poly* r) ≡  (p Poly* q) Poly* r
Poly*Associative = ElimProp.f (λ p → ∀ q r → p Poly* (q Poly* r) ≡  (p Poly* q) Poly* r ) --skriv om till eq reasoning
                              (λ _ _ → refl)
                              (λ a p prf q r  → cong (_Poly+ (0r ∷ (p Poly* (q Poly* r)))) (PolyConst*AssocPoly* a q r) ∙
                                                                                           (cong (((a PolyConst* q) Poly* r) Poly+_)
                                                                                               (
                                                                                                 (cong (_∷ (p Poly* (q Poly* r))) (+Lid 0r)) ∙
                                                                                                 (
                                                                                                   cong (0r + 0r ∷_) (
                                                                                                     (sym (Poly+Lid (p Poly* (q Poly* r)))) ∙
                                                                                                     (cong ([] Poly+_) (prf q r)))
                                                                                                 )
                                                                                               ) ∙
                                                                                               cong (((a PolyConst* q) Poly* r) Poly+_)
                                                                                                 (cong (_Poly+ (0r ∷ ((p Poly* q) Poly* r))) (sym (0rLeftAnnihilatesPoly r)))) ∙
                                                                                           (sym (Poly*RDistrPoly+ (a PolyConst* q) (0r ∷ (p Poly* q)) r ))
                              )
                              (λ x y i q r  → polyIsSet _ _ (x q r) (y q r) i)


------------------------------------
-- Theorem
-- PolyMod is a Commutative Ring
------------------------------------

PolyCommRing : CommRing ℓ-zero --Blir vanlig level sen när generaliserat
PolyCommRing = makeCommRing 0P 1P _Poly+_ _Poly*_ Poly- polyIsSet Poly+Assoc Poly+Rid Poly+Inverses Poly+Comm Poly*Associative Poly*Rid Poly*LDistrPoly+ Poly*Commutative

















---------------------------------------------
---------------------------------------------
--Diverse:
---------------------------------------------
---------------------------------------------














--Poly*Rid : ∀ p → p Poly* 1P ≡ p
--Poly*Rid = Poly*CommPoly*Lid
--ElimProp.f (λ p → p Poly* 1P ≡ p)
--                             refl
--                             (λ r p prf → lemma p r prf)
--                             λ x y → polyIsSet _ _ x y where
--                                 lemma : ∀ p r prf → r · 1r + 0r ∷ ([] Poly+ (p Poly* 1P)) ≡ r ∷ p
--                                  lemma = λ p r prf  → r · 1r + 0r ∷ ([] Poly+ (p Poly* 1P)) ≡⟨ cong (_∷ ([] Poly+ (p Poly* 1P))) (+Rid (r ·  1r))  ⟩
--                                                  r · 1r  ∷ ([] Poly+ (p Poly* 1P)) ≡⟨ cong (_∷ ([] Poly+ (p Poly* 1P))) (·Rid r) ⟩
--                                                  r ∷ ([] Poly+ (p Poly* 1P)) ≡⟨ cong (r ∷_) (Poly+Lid (p Poly* 1P) ) ⟩
--                                                  r ∷ (p Poly* 1P) ≡⟨ cong (r ∷_) (prf) ⟩
--                                                  r ∷ p ∎









--OBSOBSOB: \cdot-punkten ·, mult. är inte detsamma som \.-punkten ∙, concat.


--
----ctrl c ctrl x ctrl r restartar agda
----om senare fall är givna innan tidigare kan det bli mystiskt
--


--isRing
    --IsAbGroup
      --isGroup :
          --IsGroup
                --isMonoid
                --inverse
          --comm
    --·IsMonoid
--·-comm


---- Bevisa Poly-Poly-P=P med hjälp av ElimProp.f
----
---- Tips: använd (λ x → Poly- (Poly- x) ≡ x) för B och (polyIsSet _ _) för
---- Bprop. De andra argumenten är typ exakt samma som i beviset vi
---- gjorde idag. Som du ser behöver du inte göra några fall för drop0
---- och polyIsSet då detta löses generiskt genom att vi använder ElimProp.f.
---- Detta är anledningen att vi ofta vill resonera kring HIT på detta sätt.


 -- Ska bevisas med hjälp av Elim.f (Tips: använd toPathP för drop0 och
   -- isProp→isSet för polyIsSet. Se ElimProp för FMSet för inspiration)

--(a ∷ p) Poly+ (drop0 i) = {!!} where
--                        foo : {!!}
--                        foo = {!!}

--0Idempotent : 0r + 0r ≡ 0r
-- 0Idempotent = +Lid 0r

--knep: använd   where-sats:
-- ? where
--      f : ?
--      f = ?
--? \==\< ? \> ? \==\< ? \> ? \==\< ? \> ? \qed
--ctrl c ctrl s


--a ∷ p Poly+ ([])      = a ∷ p
--a ∷ p Poly+ (0r ∷ []) = (a + 0) ∷ (p Poly+ [])
--+Idempotency→0
--(λ a p e → cong (_∷ (Poly- (Poly- p))) (-Idempotent a) ∙ cong (a ∷_ ) (e))
--(a ∷ p) Poly+ (drop0 i) = Rec.f Poly [] _∷_ drop0 polyIsSet (polyIsSet (a ∷ p) (drop0 i) (polyIsSet (a ∷ p) (drop0 i) {!!} {!!} {!!}) {!!} {!!} {!!})
--
--cong (λ x → (x Poly+ q))  drop0 i
---- Låt oss testa så att addition funkar med ett par polynom
--open import Cubical.Data.Int.MoreInts.BiInvInt.Base
--
--one : BiInvℤ
--one = suc zero
--
--p1 : Poly
--p1 = one ∷ []
--
--p11 : Poly
--p11 = one ∷ one ∷ []
--
---- För att göra beräkningar testa med:
---- C-c C-n p1 Poly+ p1
---- C-c C-n p11 Poly+ p11
--
--
----  module Rec' {ℓ'} {B : Type ℓ'}
----              (BType : isSet B)
----              ([]* : B)
----              (cons* : R → B → B)
----              (drop0* : cons* 0r []* ≡ []*) where
----    f : Poly → B
----   f = Elim.f (λ _ → B) []* (λ r p b → cons* r b) drop0* ( λ _ → BType)
--
----  module Rec (B : Type ℓ')
----             ([]* : B)
----             (cons* : R → B → B)
----             (drop0* : cons* 0r []* ≡ []*)
----             (Bset : isSet B) where
----    f : Poly → B
----    f = Elim.f (λ _ → B) []* (λ r p b → cons* r b ) drop0* λ _ → Bset
--
--
--
--
---- Det är inte helt uppenbart hur fallen med drop0 och polyIsSet ska
---- lösas. Jag skulle gissa att vi vill lägga in något i stil med:
----
---- module Rec (B : Type ℓ')
----            ([]* : B)
----            (cons* : R → B → B)
----            (drop0* : cons* 0r []* ≡ []*)
----            (Bset : isSet B) where
----  f : Poly → B
----  f = Elim.f ? ? ? ? ?
----
---- Kanske samma för binära funktioner...
--


--annan def för Poly+
--_Poly+_ : Poly → Poly → Poly
--p Poly+ [] = p
--[] Poly+ (a ∷ q) = a ∷ q
--[] Poly+ (drop0 i) = drop0 i
--(a ∷ p) Poly+ (b ∷ q) = (a + b) ∷ (p Poly+ q)
--(drop0 i) Poly+ (a ∷ q) = foo q i  where
--                               foo : ∀ q → (0r + a) ∷ ([] Poly+ q) ≡ a ∷ q
--                               foo = ElimProp.f (λ q → (0r + a) ∷ ([] Poly+ q) ≡ a ∷ q)
--                                                (λ i → (+Lid a i ∷ []))
--                                                (λ r p _ → λ i → +Lid a i ∷ r ∷ p )
--                                                (polyIsSet _ _)
--(a ∷ p) Poly+ (drop0 i) = +Rid a i ∷ p
--(drop0 i) Poly+ (drop0 j) =  isSet→isSet' polyIsSet  (cong ([_] ) (+Rid 0r)) drop0 ((cong ([_] ) (+Lid 0r))) drop0 i j


--Poly*Rid : ∀ p → p Poly* 1P ≡ p
--Poly*Rid = λ p → {!Poly*Commutative (Poly*Lid p)!}
--a *: ((b +: pX) + q)
--((b +: pX) + q) * [a]           --prf : (a PolyConst* (p Poly+ q)) ≡ ((a PolyConst* p) Poly+ (a PolyConst* q))
--((b +: pX) * [a] + q * [a]
--(a *: (b +: pX)) + (a *: q)



 --a *: (q + r) + (p * (q + r)) X
                                   --    PolyConst*LDistrPoly+
                                   --(a *: q) + (a *: r) + (p * (q + r)) X
                                   --                               induktion(prf)
                                   --(a *: q) + (a *: r) + ((p * q) + (p * r)) X
                                   --                              lemm6'
                                   --(a *: q) + (a *: r) + ((p * q) X + (p * r) X)
                                   -- kasta om           +Assoc
                                   --((a *: q) + (a *: r) + (p * q) X) + (p * r) X
                                   -- kasta om            +Comm
                                   -- --((a *: q) + ((p * q) X + (a *: r))) + (p * r) X
                                   --             +assoc
                                   --(((a *: q) + (p * q) X) + (a *: r)) + (p * r) X
                                   -- kasta om                 +Assoc
                                   --((a *: q ) + (p * q) X) + ((a *: r) + (p * r) X)





--a *: ((b *: q) + (p * q)X )
--          PolyConst*Distr
--(a *: (b *: q)) + (a *: (p * q)X))
--   PolyConst*Nested·
--(a · b *: q) + (a *: (p * q)X))
--                      PolyConst*rEqualsPoly*[r]
--(a · b *: q) + ((p * q)X) * [a] )
--                     sym Xp*q=X*pq
--(a · b *: q) + ((p * q) * [a])X )
--                    sym PolyConst*rEqualsPoly*[r]
--(a·b *: q) + (a *: (p * q))X
--                   prf
--(a·b *: q) + ((a *: p) * q)X


                                              --a *: (q * r) + (p * (q * r)) * X
                                                --PolyConst*AssocPoly*            --Xp*q=X*pq
                                              --(a *: q) * r + (p * (q * r) * X)
                                              --(a *: q) * r + (p * (q * r) * X)
                                              --((a *: q) * r + ((p * q) * X)  * r)
                                                      --lemma3'
                                              --((a *: q) + (p * q) * X) * r




--      (a *: q) + (p * q) X
--                   prf
--      (a *: q) + (q * p) X
--                   Xp*q=X*pq
--      (a *: q) + (q X * p)
--         PolyConst*rEqualsPoly*[r]
--      (q * [ a ]) + (q X * p)
--                   Xp*q=p*Xq
--      (q * [a]) + (q * pX)                         --prf : (q₁ : Poly) → (p Poly* q₁) ≡ (q₁ Poly* p)
--           *LeftDistr
--      q * ([a] + p X)
--          +Comm
--      q * (p X + [a])


--PolyConst*LDistrPoly+ : ∀ a p q → a PolyConst* (p Poly+ q) ≡ (a PolyConst* p) Poly+ (a PolyConst* q)
--PolyConst*LDistrPoly+ = λ a → ElimProp.f (λ p → ∀ q → a PolyConst* (p Poly+ q) ≡ (a PolyConst* p) Poly+ (a PolyConst* q))
--                           (λ q → cong (a PolyConst*_) (Poly+Lid q) ∙ sym (Poly+Lid (a PolyConst* q)))
--                           --(a PolyConst* ((b ∷ p) Poly+ q)) ≡ ((a · b ∷ (a PolyConst* p)) Poly+ (a PolyConst* q))
--                           (λ b p prf → ElimProp.f (λ q → (a PolyConst* ((b ∷ p) Poly+ q)) ≡ ((a PolyConst* (b ∷ p)) Poly+ (a PolyConst* q)))
--                                                   refl
--                                                   (λ c r prf2 → cong (_∷ (a PolyConst* (p Poly+ r))) (·Rdist+ a b c) ∙
--                                                                 cong (a · b + a · c ∷_) (prf r))
--                                                   λ x y i → polyIsSet (x i0) (x i1) x y i)
--                          λ x y i q → polyIsSet (x q i0) (x q i1) (x q) (y q) i
