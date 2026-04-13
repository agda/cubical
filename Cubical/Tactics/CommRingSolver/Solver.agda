module Cubical.Tactics.CommRingSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ;suc;zero)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ using (zero-≤)
open import Cubical.Data.Vec as Vec
open import Cubical.Data.Sigma
import Cubical.Data.Prod as ×
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.NatPlusOne
open import Cubical.Data.List as L hiding (drop)
open import Cubical.Data.List.Dependent
open import Cubical.Data.Bool as 𝟚 hiding (_≟_)
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary

open import Cubical.Reflection.Sugar


open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolver.RawAlgebra hiding (⟨_⟩)
open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Tactics.CommRingSolver.RawRing hiding (⟨_⟩)
open import Cubical.Tactics.CommRingSolver.EvalHom
open import Cubical.Tactics.CommRingSolver.Config
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Data.FinData

open import Agda.Builtin.String


module SansReflection (crs : CommRingSolverConfig) where

 open CommRingSolverConfig crs

 open HomomorphismProperties R  R` (snd commAlg)

 mb≟ : ∀ x y → Maybe (x ≡ y)
 mb≟ x y = mbDiscreteScalars <* x <* y >>= decToMaybe

 infix 9 _^'_

 _^'_ : ⟨ R` ⟩ → ℕ → ⟨ R` ⟩
 f ^' zero = 1r`
 f ^' suc zero = f
 f ^' n@(suc (suc _)) = (f ^ n)

 ^'≡^ : ∀ x k → x ^' k ≡  x ^ k
 ^'≡^ x zero = refl
 ^'≡^ x (suc zero) = sym (R`.·IdR _)
 ^'≡^ x (suc (suc k)) = refl


 -- module EvalPoly where
 --  open Sum (CommRing→Ring R')

 _^''_ : ⟨ R` ⟩ → ℕ → Maybe ⟨ R` ⟩
 x ^'' zero = nothing
 x ^'' suc zero = just x
 x ^'' suc n = just (x ^' (suc n) )


 ^''suc : ∀ v m → v ^'' suc m ≡ just (v ^ (suc m))
 ^''suc v zero = cong just (sym (R`.·IdR v))
 ^''suc v (suc m) = refl


 ^''-suc : ∀ m v → v ^' suc m ≡ v ^' m ·` v
 ^''-suc zero v = sym (R`.·IdL _)
 ^''-suc one v = cong (v ·`_) (R`.·IdR _)
 ^''-suc (suc (suc m)) v = R`.·Comm _ _

 _mb·`mb_ : Maybe ⟨ R` ⟩ → Maybe ⟨ R` ⟩ → Maybe ⟨ R` ⟩
 nothing mb·`mb x₁ = x₁
 just x mb·`mb y = just (Mb.rec x (x ·`_) y)


 ^''-+ : ∀ {x} e f → (x ^'' (e ℕ.+ f)) ≡ ((x ^'' e) mb·`mb (x ^'' f))
 ^''-+ zero f = refl
 ^''-+ one zero = refl
 ^''-+ {x} one one = cong (λ x' → just (x ·` (x'))) (R`.·IdR _)
 ^''-+ one (suc (suc f)) = refl
 ^''-+ {x} (suc (suc e)) zero =
   cong (λ e → just (x ·` (x ·` x ^ e))) (ℕ.+-zero e)
 ^''-+ {x} (suc (suc e)) one = cong just
   (sym (·-of-^-is-^-of-+ x (suc (suc e)) 1) ∙
    cong₂ _·`_ refl (R`.·IdR _))
 ^''-+ {x} (suc (suc e)) (suc (suc f)) = cong just
   (sym (·-of-^-is-^-of-+ x (suc (suc e)) (suc (suc f))))


 mb·`mbIdR : ∀ x → x mb·`mb nothing ≡ x
 mb·`mbIdR nothing = refl
 mb·`mbIdR (just x) = refl

 Monomial : ℕ → Type
 Monomial n = Vec ℕ n

 evMonomial : ∀ {n} → Monomial n → Vec ⟨ R` ⟩ n → Maybe ⟨ R` ⟩
 evMonomial {n = 0} _ _ = nothing
 evMonomial {n = 1} (m ∷ _) (v ∷ _) = v ^'' m
 evMonomial {n = suc (suc _)} (m ∷ xs) (v ∷ vs) = (evMonomial xs vs) mb·`mb (v ^'' m)

 evMonomial∷ : ∀ {n} m ms v vs → evMonomial {suc n} (m ∷ ms) (v ∷ vs) ≡
                                   ((evMonomial ms vs) mb·`mb (v ^'' m))
 evMonomial∷ m [] v [] = refl
 evMonomial∷ m (x ∷ ms) v (x₁ ∷ vs) = refl

 PolynomialTerm : ℕ → Type ℓ
 PolynomialTerm n = Bool × (Maybe ⟨ R ⟩) × Monomial n

 fromJust-def-scalar : ∀ k → fromJust-def 1r` (map-Maybe scalar` k)
      ≡ scalar` (fromJust-def 1r k)
 fromJust-def-scalar nothing = sym pres1
 fromJust-def-scalar (just x) = refl

 -[_] : Bool → ⟨ R ⟩ → ⟨ R ⟩
 -[ false ] = -_
 -[ true ] = idfun _


 -`[_] : Bool → ⟨ R` ⟩ → ⟨ R` ⟩
 -`[ false ] = -`_
 -`[ true ] = idfun _

 -`[not] : ∀ b x → -` (-`[ b ] x) ≡ -`[ not b ] x
 -`[not] false x = R`.-Idempotent x
 -`[not] true x = refl

 -`[_]distR+ : ∀ b x y → -`[ b ] (x +` y) ≡ -`[ b ] x +` -`[ b ] y
 -`[ false ]distR+ x y = sym (R`.-Dist _ _)
 -`[ true ]distR+ x y = refl

 -`[_]· : ∀ b x y → (-`[ b ] x) ·` y ≡ -`[ b ] (x ·` y)
 -`[ false ]· x y = R`.-DistL· _ _
 -`[ true ]· x y = refl

 -`[]-fromJust-def-scalar : ∀ b k →
     -`[ b ] (fromJust-def 1r` (map-Maybe scalar` k))
      ≡
      scalar` (-[ b ] (fromJust-def 1r k))
 -`[]-fromJust-def-scalar false k = cong (-`_) (fromJust-def-scalar k) ∙ sym (pres- _)
 -`[]-fromJust-def-scalar true k = fromJust-def-scalar k

 _mb·`_ : Maybe ⟨ R` ⟩ → ⟨ R` ⟩ → ⟨ R` ⟩
 nothing mb·` y = y
 just x mb·` y = x ·` y

 -`[_]0 : ∀ b → -`[ b ] 0r` ≡ 0r`
 -`[ false ]0 =  R`.0Selfinverse
 -`[ true ]0 = refl

 -`[_]-flip≡ : ∀ b x y → -`[ b ] x ≡ y → x ≡ -`[ b ] y
 -`[ false ]-flip≡ x y p = sym (R`.-Idempotent x) ∙ cong -`_ p
 -`[ true ]-flip≡ x y p = p

 evPolynomialTerm' : ∀ {n} → ((Maybe ⟨ R ⟩) × Monomial n) → Vec ⟨ R` ⟩ n → ⟨ R` ⟩
 evPolynomialTerm' (mbK , m) xs =  (Mb.fromJust-def 1r`
   (map-Maybe scalar` mbK mb·`mb evMonomial m xs))


 evPolynomialTerm : ∀ {n} → PolynomialTerm n → Vec ⟨ R` ⟩ n → ⟨ R` ⟩
 evPolynomialTerm (b , mbK , m) xs = -`[ b ] (evPolynomialTerm' ( mbK , m) xs)


 Polynomial : ℕ → Type ℓ
 Polynomial n = List (PolynomialTerm n)

 evPolynomial :  ∀ {n} → Polynomial n → Vec ⟨ R` ⟩ n → ⟨ R` ⟩
 evPolynomial [] vs = 0r`
 evPolynomial P[ x ] vs = evPolynomialTerm x vs
 evPolynomial ((false , x@(mbK , m)) ∷ xs@(_ ∷ _)) vs =
  evPolynomial xs vs -` evPolynomialTerm' x vs
 evPolynomial ((true , x@(mbK , m)) ∷ xs@(_ ∷ _)) vs =
  evPolynomial xs vs +` evPolynomialTerm' x vs

 instance
  EvalInVecRPolynomial : EvalInVecR Polynomial
  EvalInVecRPolynomial .EvalInVecR.evalInVecR = evPolynomial


 Poly·X : ∀ {n} → Polynomial (suc n) → Polynomial (suc n)
 Poly·X {n} = L.map (map-snd (map-snd λ { (x ∷ xs) → suc x ∷ xs  }))

 Poly↑ : ∀ {n} → Polynomial n → Polynomial (suc n)
 Poly↑ {n} = L.map (map-snd (map-snd (zero ∷_)))

 evPolynomial∷ : ∀ {n} t p vs → evPolynomial {n = n} (t ∷ p) vs
                         ≡ evPolynomial p vs +` evPolynomialTerm t vs
 evPolynomial∷ t [] vs = sym (R`.+IdL _)
 evPolynomial∷ (false , _) (x ∷ p) vs = refl
 evPolynomial∷ (true , _) (x ∷ p) vs = refl

 evPolynomial++ : ∀ {n} p₀ p₁ vs → evPolynomial {n = n} (p₀ L.++ p₁) vs
                         ≡ evPolynomial p₁ vs +` evPolynomial p₀ vs
 evPolynomial++ [] p₁ vs = sym (R`.+IdR _)
 evPolynomial++ (x ∷ p₀) p₁ vs =
      evPolynomial∷ x (p₀ L.++ p₁) vs
   ∙∙ cong (_+` _) (evPolynomial++ p₀ p₁ vs)
      ∙ sym (R`.+Assoc _ _ _)
   ∙∙ cong (evPolynomial p₁ vs +`_) (sym (evPolynomial∷ x p₀ vs)  )

 evMonomial·X : ∀ n m ms v vs → evMonomial {suc n} (suc m ∷ ms) (v ∷ vs)
                             ≡ (evMonomial {suc n} (m ∷ ms) (v ∷ vs) mb·`mb just v)
 evMonomial·X n m ms v vs =
      evMonomial∷ (suc m) ms v vs
      ∙∙ hlp (evMonomial ms vs) m
   ∙∙ cong (_mb·`mb just v) (sym (evMonomial∷ m ms v vs))
  where



   hlp : ∀ u m → (u mb·`mb (v ^'' suc m)) ≡
      ((u mb·`mb (v ^'' m)) mb·`mb just v)
   hlp nothing zero = refl
   hlp nothing one = cong just (cong (v ·`_) (R`.·IdR _))
   hlp nothing (suc (suc m)) = cong just (R`.·Comm _ _)
   hlp (just x) zero = refl
   hlp (just x) one = cong just
     (cong (x ·`_) (cong (v ·`_) (R`.·IdR _)) ∙ R`.·Assoc _ _ _ )
   hlp (just x) (suc (suc m)) = cong just
     (cong (x ·`_) (R`.·Comm _ _) ∙ R`.·Assoc _ _ _)


 evPolynomial·X : ∀ {n} p v vs →
      evPolynomial (Poly·X {n} p) (v ∷ vs) ≡
      evPolynomial p (v ∷ vs) ·` v
 evPolynomial·X [] v vs = sym (R`.0LeftAnnihilates _)
 evPolynomial·X {n} (x@(b , k , m ∷ ms) ∷ p) v vs =
      evPolynomial∷ _ (Poly·X p) (v ∷ vs)
    ∙∙ cong₂ _+`_
        (evPolynomial·X p v vs)
        (cong -`[ b ] (
                (cong (λ u → fromJust-def 1r` ((map-Maybe scalar` k) mb·`mb u))
                 (evMonomial·X n m ms v vs) ∙
                  hlp (evMonomial (m ∷ ms) (v ∷ vs)) (map-Maybe scalar` k))
             ∙ sym (∘fromJust-def (_·` v) 1r`
              ((map-Maybe scalar` k) mb·`mb evMonomial (m ∷ ms) (v ∷ vs))))
           ∙ sym (-`[ b ]· _ _))
    ∙∙ sym (R`.·DistL+ _ _ v)
      ∙ cong (_·` v) (sym (evPolynomial∷ _ p _))
  where
  hlp : ∀ u k → fromJust-def 1r` (k mb·`mb (u mb·`mb just v))
              ≡ fromJust-def (1r` ·` v) (map-Maybe (_·` v) (k mb·`mb u))
  hlp nothing nothing = sym (R`.·IdL _)
  hlp nothing (just x) = refl
  hlp (just x) nothing = refl
  hlp (just x) (just x₁) = R`.·Assoc _ _ _

 evPolynomial↑ : ∀ {n} p v vs →
                    evPolynomial (Poly↑ p) (v ∷ vs) ≡
                     evPolynomial {n = n} p (vs)
 evPolynomial↑ [] v vs = refl
 evPolynomial↑ (x ∷ p) v vs =
       evPolynomial∷ _ (Poly↑ p) (v ∷ vs)
    ∙∙ cong₂ _+`_ (evPolynomial↑ p v vs)
        (cong (-`[ x .fst ] ∘ fromJust-def 1r` ∘ (map-Maybe scalar` (x .snd .fst)) mb·`mb_)
          (   evMonomial∷ _ _ v vs
           ∙ mb·`mbIdR _))
    ∙∙ sym (evPolynomial∷ _ p vs)


 -- sign multiplication: false = “negated”, true = “unchanged”
 _⊙_ : Bool → Bool → Bool
 true  ⊙ b = b
 false ⊙ true  = false
 false ⊙ false = true

 -- Maybe-coefficient multiplication, with `nothing` = implicit 1
 _mb·mb_ : Maybe ⟨ R ⟩ → Maybe ⟨ R ⟩ → Maybe ⟨ R ⟩
 nothing mb·mb y = y
 just x  mb·mb y = just (Mb.rec x (x ·_) y)

 -- Monomial multiplication = add exponents pointwise
 mon· : ∀ {n} → Monomial n → Monomial n → Monomial n
 mon· [] [] = []
 mon· (e ∷ es) (f ∷ fs) = (ℕ._+_ e f) ∷ mon· es fs


 PolynomialTerm'· : ∀ {n} → (Maybe ⟨ R ⟩) × Monomial n → (Maybe ⟨ R ⟩) × Monomial n → (Maybe ⟨ R ⟩) × Monomial n
 PolynomialTerm'· {n} (k₁ , m₁) (k₂ , m₂) =
   ( k₁ mb·mb k₂
   , mon· m₁ m₂
   )


 PolynomialTerm· : ∀ {n} → PolynomialTerm n → PolynomialTerm n → PolynomialTerm n
 PolynomialTerm· {n} (b₁ , a₁) (b₂ , a₂) =
   ( b₁ ⊙ b₂ , PolynomialTerm'· a₁ a₂
   )


 -- sign action respects multiplication
 -`[]-⊙ : ∀ b₁ b₂ x y →
   -`[ b₁ ⊙ b₂ ] (x ·` y) ≡ (-`[ b₁ ] x) ·` (-`[ b₂ ] y)
 -`[]-⊙ true true x y = refl
 -`[]-⊙ true false x y = sym (R`.-DistR· x y)
 -`[]-⊙ false true x y = sym (R`.-DistL· x y)
 -`[]-⊙ false false x y =  sym (R`.-Dist· x y)



 map-Maybe-mb·mb : ∀ k₁ k₂ →
   map-Maybe scalar` (k₁ mb·mb k₂)
   ≡ (map-Maybe scalar` k₁) mb·`mb (map-Maybe scalar` k₂)
 map-Maybe-mb·mb nothing k₂ = refl
 map-Maybe-mb·mb (just x) nothing = refl
 map-Maybe-mb·mb (just x) (just y) =
   cong just (pres· x y)


 fromJust-def-mb·`mb :
   ∀ a b →
   fromJust-def 1r` (a mb·`mb b)
   ≡ fromJust-def 1r` a ·` fromJust-def 1r` b
 fromJust-def-mb·`mb nothing nothing =
   sym (R`.·IdR _)
 fromJust-def-mb·`mb nothing (just y) =
   sym (R`.·IdL _)
 fromJust-def-mb·`mb (just x) nothing =
   sym (R`.·IdR _)
 fromJust-def-mb·`mb (just x) (just y) = refl

 mb·`mb-comm : ∀ x y → x mb·`mb y ≡ y mb·`mb x
 mb·`mb-comm nothing nothing = refl
 mb·`mb-comm nothing (just y) = refl
 mb·`mb-comm (just x) nothing = refl
 mb·`mb-comm (just x) (just y) =
   cong just (R`.·Comm x y)

 mb·`mb-assoc : ∀ x y z → (x mb·`mb y) mb·`mb z ≡ x mb·`mb (y mb·`mb z)
 mb·`mb-assoc nothing y z = refl
 mb·`mb-assoc (just x) nothing z = refl
 mb·`mb-assoc (just x) (just y) nothing = refl
 mb·`mb-assoc (just x) (just y) (just z) =
   cong just (sym (R`.·Assoc x y z))

 evMonomial-mon· : ∀ {n} (m₁ m₂ : Monomial n) (xs : Vec ⟨ R` ⟩ n) →
   evMonomial (mon· m₁ m₂) xs ≡ evMonomial m₁ xs mb·`mb evMonomial m₂ xs
 evMonomial-mon· {n = 0} [] [] _ = refl
 evMonomial-mon· {n = 1} (e ∷ []) (f ∷ []) (x ∷ []) = ^''-+ e f
 evMonomial-mon· {n = suc (suc n)} (e ∷ es) (f ∷ fs) (x ∷ xs) =
   let z = evMonomial-mon· es fs xs
   in cong₂ (_mb·`mb_) z (^''-+ e f)
      ∙∙ mb·`mb-assoc (evMonomial es xs) _ _
      ∙∙ cong ((evMonomial es xs) mb·`mb_) (sym (mb·`mb-assoc (evMonomial fs xs) (x ^'' e) (x ^'' f))
         ∙∙ cong (_mb·`mb (x ^'' f)) (mb·`mb-comm (evMonomial fs xs) (x ^'' e))
         ∙∙ (mb·`mb-assoc (x ^'' e) (evMonomial fs xs) (x ^'' f)))
      ∙ sym (mb·`mb-assoc (evMonomial es xs) _ _)

 PolynomialTerm'·-sound : ∀ {n} t₁ t₂ → (xs : Vec ⟨ R` ⟩ n) →
   evPolynomialTerm' {n} (PolynomialTerm'· t₁ t₂) xs
   ≡ evPolynomialTerm' t₁ xs ·` evPolynomialTerm' t₂ xs
 PolynomialTerm'·-sound (k₁ , m₁) (k₂ , m₂) xs =
  (fromJust-def-mb·`mb (map-Maybe scalar` (k₁ mb·mb k₂)) (evMonomial (mon· m₁ m₂) xs))
        ∙∙  cong₂ _·`_
               (cong (fromJust-def 1r`) (map-Maybe-mb·mb k₁ k₂)
               ∙ fromJust-def-mb·`mb (map-Maybe scalar` k₁) (map-Maybe scalar` k₂) )
               (cong (fromJust-def 1r`) (evMonomial-mon· m₁ m₂ xs)
                ∙ fromJust-def-mb·`mb (evMonomial m₁ xs) _)
           ∙ R`.·CommAssocSwap _ _ _ _
        ∙∙ cong₂ _·`_
          (sym (fromJust-def-mb·`mb (map-Maybe scalar` k₁) (evMonomial m₁ xs)))
          (sym (fromJust-def-mb·`mb (map-Maybe scalar` k₂) (evMonomial m₂ xs)))

 PolynomialTerm·-sound : ∀ {n} (t₁ t₂ : PolynomialTerm n) (xs : Vec ⟨ R` ⟩ n) →
   evPolynomialTerm (PolynomialTerm· t₁ t₂) xs
   ≡ evPolynomialTerm t₁ xs ·` evPolynomialTerm t₂ xs
 PolynomialTerm·-sound (b₁ , a₁) (b₂ , a₂) xs =
     cong (-`[ b₁ ⊙ b₂ ]) (PolynomialTerm'·-sound a₁ a₂ xs)
     ∙ -`[]-⊙ b₁ b₂ _ _

 RExpr : (n : ℕ) → Type _
 RExpr = Expr RRng ⟨ R` ⟩

 normalize : {n : ℕ} → RExpr n → IteratedHornerForms n
 normalize {n = n} (K r) = Constant n r
 normalize {n = n} (∣ k) = Variable n k
 normalize (x +' y) =
   (normalize x) +ₕ (normalize y)
 normalize (x ·' y) =
   (normalize x) ·ₕ (normalize y)
 normalize (-' x) =  -ₕ (normalize x)

 evalConstant : ∀ n r xs → eval (Constant n r) xs ≡ scalar` r
 evalConstant zero r [] = refl
 evalConstant (suc n) r (x ∷ xs) =
   R`.+IdL' _ _ (R`.0LeftAnnihilates _)
      ∙ evalConstant n r xs

 isEqualToNormalform :
      {n : ℕ} (e : RExpr n) (xs : Vec (fst R`) n)
    → eval (normalize e) xs ≡ ⟦ e ⟧ xs


 isEqualToNormalform {n = n} (K r) xs = evalConstant n r xs

 isEqualToNormalform (∣ zero) (x ∷ xs) =
   eval 1ₕ (x ∷ xs) ·` x +` eval 0ₕ xs   ≡⟨ cong (λ u → u ·` x +` eval 0ₕ xs)
                                             (Eval1ₕ (x ∷ xs)) ⟩
   1r` ·` x +` eval 0ₕ xs                 ≡⟨ cong (λ u → 1r`  ·` x +` u ) (Eval0H xs) ⟩
   1r` ·` x +` 0r`                        ≡⟨ R`.+IdR _ ⟩
   1r` ·` x                             ≡⟨ R`.·IdL _ ⟩
   x ∎
 isEqualToNormalform {n = suc n} (∣ (suc k)) (x ∷ xs) =
     eval 0ₕ (x ∷ xs) ·` x +` eval (Variable n k) xs ≡⟨ cong (λ u → u ·` x +` eval (Variable n k) xs)
                                                             (Eval0H (x ∷ xs)) ⟩
     0r` ·` x +` eval (Variable n k) xs              ≡⟨ cong (λ u → u +` eval (Variable n k) xs)
                                                             (R`.0LeftAnnihilates _) ⟩
     0r` +` eval (Variable n k) xs                  ≡⟨ R`.+IdL _ ⟩
     eval (Variable n k) xs                       ≡⟨ isEqualToNormalform (∣ k) xs ⟩
     ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

 isEqualToNormalform (-' e) [] =
   eval (-ₕ (normalize e)) []  ≡⟨ -EvalDist (normalize e) [] ⟩
   -` eval (normalize e) []    ≡⟨ cong -`_ (isEqualToNormalform e [] ) ⟩
   -` ⟦ e ⟧ [] ∎
 isEqualToNormalform (-' e) (x ∷ xs) =
   eval (-ₕ (normalize e)) (x ∷ xs) ≡⟨ -EvalDist (normalize e) (x ∷ xs) ⟩
   -` eval (normalize e) (x ∷ xs)    ≡⟨ cong -`_ (isEqualToNormalform e (x ∷ xs) ) ⟩
   -` ⟦ e ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e +' e₁) [] =
       eval (normalize e +ₕ normalize e₁) []
     ≡⟨ +Homeval (normalize e) _ [] ⟩
       eval (normalize e) []
       +` eval (normalize e₁) []
     ≡⟨ cong (λ u → u +` eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ []
       +` eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] +` u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] +` ⟦ e₁ ⟧ [] ∎
 isEqualToNormalform (e +' e₁) (x ∷ xs) =
       eval (normalize e +ₕ normalize e₁) (x ∷ xs)
     ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) +` eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u +` eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +` eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) +` u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +` ⟦ e₁ ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e ·' e₁) [] =
       eval (normalize e ·ₕ normalize e₁) []
     ≡⟨ ·Homeval (normalize e) _ [] ⟩
       eval (normalize e) [] ·` eval (normalize e₁) []
     ≡⟨ cong (λ u → u ·` eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ [] ·` eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] ·` u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] ·` ⟦ e₁ ⟧ [] ∎

 isEqualToNormalform (e ·' e₁) (x ∷ xs) =
       eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
     ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) ·` eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u ·` eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·` eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) ·` u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·` ⟦ e₁ ⟧ (x ∷ xs) ∎


 [_]ᵗʸ : ∀ {ℓ} → List (Type ℓ) → Type (ℓ-suc ℓ)
 [_]ᵗʸ = ListP (idfun _)

 ×[_]ᵗʸ : ∀ {ℓ} → List (Type ℓ) → Type ℓ
 ×[_]ᵗʸ = RepListP (idfun _)


 [X]? : ∀ {ℓ'} → Type ℓ'  → Type (ℓ-max (ℓ-suc ℓ) ℓ')
 [X]? A = (Σ (List (Type ℓ)) (λ XS → (([ XS ]ᵗʸ → A) ×
               (ListP (λ X → Discrete ⟨ R ⟩ → Maybe X) XS))))

 ×-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → [X]? A → [X]? A' → [X]? (A × A')
 ×-[X]? (XS , f , d) (XS' , f' , d') =
   XS L.++ XS' , (map-× f f') ∘S splitP {xs = XS} {XS'} , (d ++P d')

 map-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → (A → A')
           → [X]? A → [X]? A'
 map-[X]? f = map-snd (map-fst (f ∘S_))


 IHR?0 : ∀ {n} → ∀ (e : IteratedHornerForms n) →
           [X]?  (e ≑ 0ₕ)
 IHR?0 (const x) =
    ([ x ≡ 0r ]) , (λ { (p ∷ []) [] → cong scalar` p} )
    , ((λ _≟_ → decRec just (λ _ → nothing) (x ≟ 0r)) ∷ [])
 IHR?0 0H = [] , (λ _ xs → Eval0H xs) , []
 IHR?0 (e ·X+ e₁) =
   map-[X]?
     (λ (f , f') → λ {(v ∷ vs) →
      cong₂ R`._+_
           (R`.0LeftAnnihilates'  _ _  (f (v ∷ vs)))
           (f' vs) ∙ R`.+IdR' _ _ (Eval0H vs) })
     (×-[X]? (IHR?0 e) (IHR?0 e₁))

 -- formIHR?0 : ∀ {n} P (Q : IteratedHornerForms n)  →
 --              [ fst (IHR?0 (P ·X+ Q)) ]ᵗʸ →
 --              [ fst (IHR?0 P) ]ᵗʸ
 -- formIHR?0 = {!!}

 IHR? : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) →
     [X]? (e₁ ≑ e₂)
 IHR? (const x) (const x') = [ x ≡ x' ] , (( λ { (p ∷ []) [] → cong scalar` p }) ,
   (λ _≟_ → decToMaybe (x ≟ x')) ∷ [])
 IHR? 0H e = map-[X]?
  (λ f → λ { (v ∷ vs) → sym   (f (v ∷ vs)) }) (IHR?0 e)
 IHR? e 0H =
    map-[X]?
  (λ f → λ { (v ∷ vs) → (f (v ∷ vs)) }) (IHR?0 e)
 IHR? (e ·X+ e₁) (e' ·X+ e₁') =
  map-[X]?
    ((λ (f , f') → λ {(v ∷ vs) →
       cong₂ R`._+_ (cong (_·` v)  (f (v ∷ vs))) (f' vs)}))
    (×-[X]? (IHR? e e') (IHR? e₁ e₁'))





 IHR?-refl : ∀ {n} → ∀ (e : IteratedHornerForms n) → [ fst (IHR? e e) ]ᵗʸ
 IHR?-refl (const x) = refl ∷ []
 IHR?-refl 0H = []
 IHR?-refl (e ·X+ e₁) = IHR?-refl e ++P IHR?-refl e₁



 solve :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 solve e₁ e₂ xs z =
   ⟦ e₁ ⟧ xs               ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
   eval (normalize e₁) xs ≡⟨ (fst (snd (IHR? (normalize e₁) (normalize e₂))) z xs) ⟩
   eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
   ⟦ e₂ ⟧ xs ∎

 solveByDec :
   (n : ℕ) (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
        ⁇→ (⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs)
 solveByDec _ e₁ e₂ xs = ⁇λ solve e₁ e₂ xs

 IsConstPossiblyNonNull : ∀ {n} → IteratedHornerForms n → Type (ℓ-suc ℓ)
 IsConstPossiblyNonNull (const x) = Unit*
 IsConstPossiblyNonNull 0H = ⊥*
 IsConstPossiblyNonNull (P ·X+ Q) = [ fst (IHR?0 P)  ]ᵗʸ × IsConstPossiblyNonNull Q

 IsConstPossiblyNonNull→ev : ∀ {n} e → IsConstPossiblyNonNull {n} e → Σ[ a ∈ ⟨ R ⟩ ] (∀ xs → eval e xs ≡ scalar` a )
 IsConstPossiblyNonNull→ev (const a) _ = a , λ { [] → refl }
 IsConstPossiblyNonNull→ev (P ·X+ Q) (u , v) =
  let (a , p) = IsConstPossiblyNonNull→ev Q v
  in a , λ { (x ∷ xs) → R`.+IdL' _ _
    (R`.0LeftAnnihilates'  _ _ (fst (snd (IHR?0 P)) u (x ∷ xs)))
     ∙ p xs }

 --
 FreeOfVar : ∀ {n} → IteratedHornerForms n → Fin n → Type (ℓ-suc ℓ)
 FreeOfVar 0H _ = Unit*
 FreeOfVar (P ·X+ Q) zero = [ fst (IHR?0 P)  ]ᵗʸ
 FreeOfVar (P ·X+ Q) (suc k) = FreeOfVar P (suc k) × FreeOfVar Q k

 FreeOfVar→ev : ∀ {n} P k → FreeOfVar {suc n} P k
    → Σ[ P' ∈ IteratedHornerForms n ] (∀ xs → eval P xs ≡ eval P' (Vec.drop k xs) )
 FreeOfVar→ev 0H k _ = 0ₕ , λ xs → sym (Eval0H (Vec.drop k xs))

 FreeOfVar→ev (P ·X+ Q) zero u = Q ,
   λ { (x ∷ xs) → R`.+IdL' _ _ (R`.0LeftAnnihilates' _ _
     ((fst (snd (IHR?0 P)) u (x ∷ xs)))) }
 FreeOfVar→ev {suc n} (P HornerForms.·X+ Q) (suc k) (p , q) =
   let (P' , p') = FreeOfVar→ev P (suc k) p
       (Q' , q') = FreeOfVar→ev Q k q
   in (P' ·X+ Q') , λ { (x ∷ xs) →
     cong₂ _+`_ (cong (_·` x) (p' (x ∷ xs))) (q' xs) }


 HeadVarOnlyInPow : ∀ {n} → IteratedHornerForms (suc n) → ℕ → Type (ℓ-suc ℓ)
 HeadVarOnlyInPow h zero = FreeOfVar h zero
 HeadVarOnlyInPow 0H (suc k) = ⊥*
 HeadVarOnlyInPow (P HornerForms.·X+ Q) (suc k) =
    HeadVarOnlyInPow P k × [ fst (IHR?0 Q)  ]ᵗʸ



 record Elimination {n : ℕ}
          (P : IteratedHornerForms (suc n))
          (iX : Fin (suc n)) (k : ℕ₊₁) : Type (ℓ-max ℓ` ℓ) where

  field
   S Q : IteratedHornerForms n
   S·xᵏ+Q≡P : ∀ xs →
       (eval S (drop iX xs) ·` (lookup iX xs ^ ℕ₊₁→ℕ k)) +` eval Q (drop iX xs)
          ≡ eval P xs

 IsolatedPowerHeadVar : ∀ {n} → IteratedHornerForms (suc n) → ℕ → Type (ℓ-suc ℓ)
 IsolatedPowerHeadVar 0H _ = ⊥*
 IsolatedPowerHeadVar (P ·X+ Q) m = HeadVarOnlyInPow P m

 HeadVarOnlyInPow→ev : ∀ {n} P m → HeadVarOnlyInPow {n} P m →
    Σ[ P' ∈ IteratedHornerForms n ]
      (∀ x xs → eval P' xs ·` x ^ m ≡ eval P (x ∷ xs) )
 HeadVarOnlyInPow→ev P zero v =
   map-snd (λ u x xs → R`.·IdR _ ∙ sym (u (x ∷ xs))) (FreeOfVar→ev _ _ v)
 HeadVarOnlyInPow→ev (P ·X+ Q) (suc m) (u , v) =
   map-snd (λ w x xs →
           (cong₂ _·`_ refl (R`.·Comm _ _)
         ∙∙ R`.·Assoc _ _ _
         ∙∙ cong (_·` x) (w x xs))
      ∙ sym (R`.+IdR' _ _ (fst (snd (IHR?0 Q)) v xs ∙ Eval0H xs)))
     (HeadVarOnlyInPow→ev P m u)


 toElimination : ∀ {n} P m → (IsolatedPowerHeadVar P m) → Elimination {n} P zero (1+ m)
 toElimination (P ·X+ Q) k hvm =
   let (S , eqtion) = HeadVarOnlyInPow→ev P k hvm
   in record { S = S
             ; Q = Q
             ; S·xᵏ+Q≡P = λ { (x ∷ xs) →
                    cong₂ _+`_
                      ( cong₂ _·`_ refl (R`.·Comm _ _)
                          ∙∙  R`.·Assoc _ _ _
                          ∙∙ cong (_·` x) (eqtion x xs))
                      refl } }


 IsolatedPowerVar : ∀ {n} → IteratedHornerForms n → Fin n → ℕ → Type (ℓ-suc ℓ)
 IsolatedPowerVar {suc n} 0H _ _ = ⊥*
 IsolatedPowerVar {suc n} (P ·X+ Q) zero m =
   HeadVarOnlyInPow P m
 IsolatedPowerVar {suc n} (P ·X+ Q) (suc k) m =
   IsolatedPowerVar P (suc k) m × IsolatedPowerVar Q k m


 -- IsolatedPowerVar→ev : ∀ {n} P → ∀ k m →  IsolatedPowerVar {suc n} P k m
 --    → Elimination P k (1+ m)
 -- IsolatedPowerVar→ev {n} P@(_ ·X+ _) zero = toElimination P
 -- IsolatedPowerVar→ev {suc n} (P ·X+ R) (suc k) m (p , r) =
 --   let RE = (IsolatedPowerVar→ev {n} R k m r)
 --       PE = (IsolatedPowerVar→ev {suc n} P (suc k) m p)
 --   in record { S = PE .S ·X+ RE .S ; Q = PE .Q ·X+ RE .Q ;
 --        S·xᵏ+Q≡P = λ {(x ∷ xs) b v →
 --           cong (_+` b) (((R`.·DistL+ _ _ _ ∙ cong₂ _+`_
 --             ( sym (R`.·Assoc _ _ _)
 --              ∙∙ cong₂ _·`_ refl (R`.·Comm _ _) ∙∙ (R`.·Assoc _ _ _) ) refl)
 --              ∙ sym (R`.+IdR` _ _ (R`.+InvR _)))
 --             ∙ R`.+ShufflePairs _ _ _ _)
 --            ∙ sym (R`.+Assoc _ _ _) ∙
 --            cong₂ _+`_ (sym (R`.·DistL+ _ _ _)
 --              ∙ cong (_·` x) (PE .a·xᵏ≡p (x ∷ xs) _
 --              refl))
 --             ((  sym (R`.+Assoc _ _ _)
 --               ∙ cong₂ _+`_ refl
 --                 (R`.+Comm _ _))
 --              ∙ RE .a·xᵏ≡p xs (b -` (eval P (x ∷ xs) ·` x))
 --               (sym (R`.plusMinus _ _)
 --                ∙ cong (_-` (eval P (x ∷ xs) ·` x)) (R`.+Comm _ _ ∙ v))) } }
 --   where open Elimination


 trivialCD : ∀ a b → CommonDenom a b
 trivialCD a b = (a , (b , 1r)) , sym (·IdR _) , sym (·IdR _)

 PoorFactor : ∀ {n} → (P : IteratedHornerForms n) → Type (ℓ-max ℓ ℓ`)

 PoorFactor {n} P = Σ[ a ∈ Maybe ⟨ R ⟩ ] Σ[ m ∈ Monomial n ]
                        Σ[ P' ∈ IteratedHornerForms n ]
                         (∀ xs → just (eval P xs) ≡
                             (      (map-Maybe scalar` a
                             mb·`mb (evMonomial m xs))
                             mb·`mb (just (eval P' xs))))

 1PolynomialTerm : ∀ {n} → PolynomialTerm n
 1PolynomialTerm = (true , (nothing , replicate zero))

 1PolynomialTerm? : ∀ {n} x → Dec (x ≡ 1PolynomialTerm {n})
 1PolynomialTerm? (true , nothing , xs) =
   mapDec (cong (λ xs → true , nothing , xs))
          (_∘ cong (snd ∘ snd))
     (VecPath.discreteA→discreteVecA ℕ.discreteℕ _ xs (replicate zero))
 1PolynomialTerm? (false , _ , _) = no (false≢true ∘ cong fst)
 1PolynomialTerm? (_ , just x , _) = no (¬just≡nothing ∘ cong (fst ∘ snd))

 ev1PolynomialTerm : ∀ {n} xs → evPolynomialTerm (1PolynomialTerm {n}) xs ≡ 1r`
 ev1PolynomialTerm [] = refl
 ev1PolynomialTerm (x ∷ xs) =

  cong (fromJust-def 1r`) (evMonomial∷ zero (replicate zero) x xs)
    ∙∙ fromJust-def-mb·`mb (evMonomial (replicate zero) xs) nothing
    ∙∙ R`.·IdL' _ _ (ev1PolynomialTerm xs)

 ev[PolynomialTerm·Polynomial] :  ∀ {n} mm P xs →
      (evPolynomialTerm mm xs ·` evPolynomial P xs)
    ≡ evPolynomial (L.map (PolynomialTerm· {n} mm) P) xs
 ev[PolynomialTerm·Polynomial] mm [] xs = R‵.0RightAnnihilates _
 ev[PolynomialTerm·Polynomial] mm (x ∷ P) xs =
   cong (evPolynomialTerm mm xs ·`_) (evPolynomial∷ x P xs)
    ∙∙ R`.·DistR+ _ _ _
    ∙∙ (cong₂ _+`_ (ev[PolynomialTerm·Polynomial] mm P xs)
       (sym (PolynomialTerm·-sound mm x xs) )
      ∙ sym (evPolynomial∷ _ (L.map (PolynomialTerm· mm) P) xs))

 module PolyUtils where


  mbNeg‽ : (x : ⟨ R ⟩) → Maybe (Σ[ -x ∈ ⟨ R ⟩ ] - -x ≡ x)
  mbNeg‽ x = do y ← mbNeg?Scalar ; y x

  PolynomialTermNormalize : ∀ {n} mm → Σ[ mm' ∈ _ ] ∀ xs →
       evPolynomialTerm {n} mm xs ≡ evPolynomialTerm {n} mm' xs
  PolynomialTermNormalize mm@(b , nothing , mms) = mm , λ _ → refl
  PolynomialTermNormalize mm@(b , just k , mms) =
    Mb.rec (mm , λ _ → refl)
      (λ (-k , p) → (not b , just -k , mms) ,
         λ xs → sym (R`.-Idempotent _)
           ∙∙ cong -`_ (-`[not] b  _)
           ∙∙ (R`.-IsMult-1 _
            ∙∙ R`.·Comm _ _
            ∙∙ (-`[ not b ]· _ _
              ∙ cong (-`[ not b ])
               (cong₂ _·`_ (fromJust-def-mb·`mb (map-Maybe scalar` (just k)) (evMonomial mms xs)) refl
                 ∙∙ R`.·Comm _ _ ∙ sym (R`.-IsMult-1 _)
                    ∙ sym (R`.-DistL· _ _)
                      ∙ cong₂ _·`_ ((λ i → pres- (p (~ i)) (~ i))
                         ∙ cong scalar` (-Idempotent -k)) refl
                 ∙∙ sym (fromJust-def-mb·`mb (map-Maybe scalar` (just -k)) (evMonomial mms xs))) )))
      (mbNeg‽ k)


  PolynomialTerm+hlp'' : ∀ {n} b k k' mn xs →
    evPolynomialTerm {n} (b , k , mn) xs +`
      evPolynomialTerm (b , k' , mn) xs
      ≡
      evPolynomialTerm
      (b , just (fromJust-def 1r k + fromJust-def 1r k') , mn) xs
  PolynomialTerm+hlp'' b k k' mn xs = sym (-`[ b ]distR+ _ _) ∙
    cong (-`[ b ]) (
        cong₂ _+`_ (fromJust-def-mb·`mb (map-Maybe scalar` k) (evMonomial mn xs))
                   (fromJust-def-mb·`mb (map-Maybe scalar` k') (evMonomial mn xs))
      ∙∙ sym (R`.·DistL+ _ _ _)
      ∙∙ (cong (_·` fromJust-def 1r` (evMonomial mn xs))
        (cong₂ _+`_ (fromJust-def-scalar k) (fromJust-def-scalar k')
         ∙ sym (pres+ _ _))
        ∙ sym (fromJust-def-mb·`mb (map-Maybe scalar`
          (just (fromJust-def 1r k + fromJust-def 1r k'))) (evMonomial mn xs))))

  PolynomialTerm+hlp' : ∀ {n} → ∀ b k b' k' mn →
     Maybe ((Σ[ (b'' , k'') ∈ _ × _ ]
       (∀ xs → evPolynomialTerm {n} (b , k , mn) xs +` evPolynomialTerm {n} (b' , k' , mn) xs
            ≡ evPolynomialTerm {n} (b'' , k'' , mn) xs)) ⊎
      (∀ xs → evPolynomialTerm {n} (b , k , mn) xs +` evPolynomialTerm {n} (b' , k' , mn) xs ≡ 0r`))
  PolynomialTerm+hlp' false k false k' mn = just (inl ((false ,
   just (Mb.fromJust-def 1r k + Mb.fromJust-def 1r k')) , PolynomialTerm+hlp'' false k k' mn))
  PolynomialTerm+hlp' false nothing true nothing mn = just (inr λ _ → R`.+InvL _)
  PolynomialTerm+hlp' false nothing true (just x) mn = nothing
  PolynomialTerm+hlp' false (just x) true nothing mn = nothing
  PolynomialTerm+hlp' false (just x) true (just x₁) mn = nothing
  PolynomialTerm+hlp' true nothing false nothing mn = just (inr λ _ → R`.+InvR _)
  PolynomialTerm+hlp' true nothing false (just x) mn = nothing
  PolynomialTerm+hlp' true (just x) false nothing mn = nothing
  PolynomialTerm+hlp' true (just x) false (just x₁) mn = nothing
  PolynomialTerm+hlp' true k true k' mn =
   just (inl ((true , (just (Mb.fromJust-def 1r k + Mb.fromJust-def 1r k'))) ,
   PolynomialTerm+hlp'' true k k' mn))

  PolynomialTerm+hlp''' : ∀ {n} → ∀ b k b' k' mn → Σ[ (b'' , k'') ∈ _ × _ ]
       (∀ xs → evPolynomialTerm {n} (b , k , mn) xs +` evPolynomialTerm {n} (b' , k' , mn) xs
            ≡ evPolynomialTerm {n} (b'' , k'' , mn) xs)
  PolynomialTerm+hlp''' b k b' k' mn =
    let k'' = -[ b ] (Mb.fromJust-def 1r k) + -[ b' ] (Mb.fromJust-def 1r k')
    in (true , just k'') ,
       λ xs → cong₂ _+`_ (cong (-`[ b ])
              (fromJust-def-mb·`mb (map-Maybe scalar` k) (evMonomial mn xs))
               ∙ sym (-`[ b ]· _ _) ∙ cong₂ _·`_ (-`[]-fromJust-def-scalar b k) refl)
              (cong (-`[ b' ]) (fromJust-def-mb·`mb (map-Maybe scalar` k') (evMonomial mn xs))
               ∙ sym (-`[ b' ]· _ _) ∙ cong₂ _·`_ (-`[]-fromJust-def-scalar b' k') refl)
              ∙∙ sym (R`.·DistL+ _ _ _)
               ∙∙ (cong₂ _·`_ (sym (pres+ _ _)) refl
                ∙ sym (fromJust-def-mb·`mb
                             (map-Maybe scalar` (just k''))
                             (evMonomial mn xs)))

  PolynomialTerm+hlp : ∀ {n} → ∀ b k b' k' mn →
      ((Σ[ (b'' , k'') ∈ _ × _ ]
       (∀ xs → evPolynomialTerm {n} (b , k , mn) xs +` evPolynomialTerm {n} (b' , k' , mn) xs
            ≡ evPolynomialTerm {n} (b'' , k'' , mn) xs)) ⊎
      (∀ xs → evPolynomialTerm {n} (b , k , mn) xs +` evPolynomialTerm {n} (b' , k' , mn) xs ≡ 0r`))
  PolynomialTerm+hlp b k b' k' mn =
    ⊎.map (idfun _)
          -- (λ ((b'' , k'') , q) →
          -- {!let z = PolynomialTermNormalize (b'' , k''a!})
          (idfun _) $
    fromJust-def (inl (PolynomialTerm+hlp''' b k b' k' mn))
      (Mb.rec (PolynomialTerm+hlp' b k b' k' mn) (λ _≟_ →
        decRec
          (λ p → just $ inr λ xs →
             cong₂ _+`_ (cong (-`[ b ])
              (fromJust-def-mb·`mb (map-Maybe scalar` k) (evMonomial mn xs))
               ∙ sym (-`[ b ]· _ _))
              (cong (-`[ b' ]) (fromJust-def-mb·`mb (map-Maybe scalar` k') (evMonomial mn xs))
               ∙ sym (-`[ b' ]· _ _))
              ∙∙ sym (R`.·DistL+ _ _ _)
               ∙∙ R`.0LeftAnnihilates' _ _
                (((cong₂ _+`_ (-`[]-fromJust-def-scalar b k) (-`[]-fromJust-def-scalar b' k')
                   ∙ sym (pres+ _ _))
                 ∙ cong scalar` p) ∙ pres0))
          (λ _ → nothing)
         ((-[ b ] (Mb.fromJust-def 1r k) + -[ b' ] (Mb.fromJust-def 1r k')) ≟ 0r) ) mbDiscreteScalars)


  Term+Polynomial : ∀ {n} → (mm : PolynomialTerm n) (P : Polynomial n) →
         Σ[ mm+P ∈ Polynomial n ]
          (∀ xs → evPolynomial mm+P xs ≡
            (evPolynomialTerm mm xs +` evPolynomial P xs))
  Term+Polynomial mm [] = [ mm ] , λ _ → sym (R`.+IdR _)
  Term+Polynomial mm@(b , k , mn) (mm'@(b' , k' , mn') ∷ P) =
    decRec (λ mn≡mn' →
              ⊎.rec
                (λ ((b'' , k'') , u) → (b'' , k'' , mn) ∷ P ,
                   λ xs → evPolynomial∷ (b'' , k'' , mn) P xs  ∙
                     R`.+Comm _ _ ∙ cong₂ _+`_ (sym (u xs) ∙
                       cong₂ _+`_ refl ((cong
                      (λ mn →  evPolynomialTerm (b' , k' , mn) xs)
                       mn≡mn'))) refl
                      ∙∙ sym (R`.+Assoc _ _ _)
                    ∙∙ cong₂ _+`_ refl (R`.+Comm _ _ ∙ sym (evPolynomial∷ mm' P xs)))
                (λ u → P , λ xs →
                    sym (R`.+IdL' _ _
                     (cong₂ _+`_ refl (cong
                      (λ mn →  evPolynomialTerm (b' , k' , mn) xs)
                       (sym mn≡mn')) ∙ u xs))
                      ∙∙ sym (R`.+Assoc _ _ _)
           ∙∙ cong₂ _+`_ refl (R`.+Comm _ _ ∙ sym (evPolynomial∷ mm' P xs)))
                (PolynomialTerm+hlp b k b' k' mn)
                )
       (λ _ →
         let mm+P , u = Term+Polynomial mm P
         in mm' ∷ mm+P , λ xs →
               evPolynomial∷ mm' mm+P xs
           ∙∙  cong₂ _+`_ (u xs) refl
             ∙  sym (R`.+Assoc _ _ _)
           ∙∙ cong₂ _+`_ refl (sym (evPolynomial∷ mm' P xs)))
      (VecPath.discreteA→discreteVecA ℕ.discreteℕ _ mn mn')

  Polynomial+ : ∀ {n} → (P Q : Polynomial n) →
         Σ[ P+Q ∈ Polynomial n ]
          (∀ xs → evPolynomial P+Q xs ≡
            (evPolynomial P xs +` evPolynomial Q xs))
  Polynomial+ [] Q = Q , λ xs → sym (R`.+IdL _)
  Polynomial+ (mm ∷ P) Q =
   let P+Q , v = Polynomial+ P Q
   in map-snd (λ u xs → u xs ∙∙ cong (evPolynomialTerm mm xs +`_) (v xs)
           ∙∙ (R`.+Assoc _ _ _ ∙
             cong₂ _+`_ (R`.+Comm _ _ ∙ sym (evPolynomial∷ mm P xs)) refl ))
       (Term+Polynomial mm P+Q)


  Polynomial· : ∀ {n} → (P Q : Polynomial n) →
         Σ[ P·Q ∈ Polynomial n ]
          (∀ xs → evPolynomial P·Q xs ≡
            (evPolynomial P xs ·` evPolynomial Q xs))
  Polynomial· [] Q = [] , λ _ → sym (R`.0LeftAnnihilates _)
  Polynomial· (mm ∷ P) Q =
   let P·Q , v = Polynomial· P Q
   in map-snd (λ u xs → u xs ∙∙
             cong₂ (_+`_) (v xs) (sym (ev[PolynomialTerm·Polynomial] mm Q xs))
             ∙∙ sym (R`.·DistL+ _ _ _) ∙
              cong₂ _·`_ (sym (evPolynomial∷ mm P xs)) refl)
        (Polynomial+ P·Q (L.map (PolynomialTerm· mm) Q))


 module CommonMonomial (commonDenom : ∀ a b → CommonDenom a b) where

  commonDenomPow : ∀ a b → Σ[ (a' , b' , c ) ∈ _ × _ × _ ]
                     (∀ x → x ^'' a ≡ ((x ^'' a') mb·`mb (x ^'' c)))
                      ×
                     (∀ x → x ^'' b ≡ ((x ^'' b') mb·`mb (x ^'' c)))
  commonDenomPow a b =
   let a' = a ℕ.∸ ℕ.min a b
       b' = b ℕ.∸ ℕ.min a b
       c = ℕ.min a b
   in (a' , b' , c)
       , (λ x → cong (x ^''_) (sym (ℕ.≤-∸-+-cancel {c} {a} (ℕ.min-≤-left {a} {b}))) ∙ ^''-+ {x} a' c)
       , (λ x → cong (x ^''_) (sym (ℕ.≤-∸-+-cancel {c} {b} (ℕ.min-≤-right {a} {b}))) ∙ ^''-+ {x} b' c)


  toMbKnown1 : ∀ x → Σ[ x' ∈ Maybe _ ] Mb.fromJust-def 1r x' ≡ x
  toMbKnown1 x = Mb.rec (just x , refl) (λ 1=x → nothing , 1=x) (mb≟ 1r x)


  commonDenomPolynomialTerm' : ∀ n a b →
            Σ[ (a' , b' , c ) ∈ _ × _ × _ ]
                (∀ xs → (evPolynomialTerm' {n} a xs ≡
                          evPolynomialTerm' {n} a' xs ·` evPolynomialTerm' {n} c xs))
                 ×
                (∀ xs → (evPolynomialTerm' {n} b xs ≡
                          evPolynomialTerm' {n} b' xs ·` evPolynomialTerm' {n} c xs))
  commonDenomPolynomialTerm' zero (nothing , []) (nothing , []) =
    ((nothing , []) , (nothing , []) , (nothing , [])) ,
     (λ _ → sym (R`.·IdR _)) , λ _ → sym (R`.·IdR _)
  commonDenomPolynomialTerm' zero (nothing , []) (just x , []) =
    ((nothing , []) , (just x , []) , (nothing , [])) ,
     (λ _ → sym (R`.·IdR _)) , λ _ → sym (R`.·IdR _)
  commonDenomPolynomialTerm' zero (just x , []) (nothing , []) =
    ((just x , []) , (nothing , []) , (nothing , [])) ,
     (λ _ → sym (R`.·IdR _)) , λ _ → sym (R`.·IdR _)
  commonDenomPolynomialTerm' zero (just x₀ , []) (just x₁ , []) =
    let (x₀' , x₁' , y) , p , q = commonDenom x₀ x₁
    in ((just x₀' , []) , (just x₁' , []) , (just y , []))
         , (λ xs → cong scalar` p ∙ (λ i → pres· x₀' y i) ∙
                  cong (evPolynomialTerm' (just x₀' , []) xs ·`_)
                     (sym (fromJust-def-scalar (just y)) ∙
                      cong (fromJust-def (CommRingStr.1r (snd (fst commAlg))))
                        (sym (mb·`mbIdR
                         (map-Maybe (fst (snd commAlg)) (just y))))))
           , (λ xs → cong scalar` q ∙ (λ i → pres· x₁' y i) ∙
                  cong (evPolynomialTerm' (just x₁' , []) xs ·`_)
                     (sym (fromJust-def-scalar (just y)) ∙
                      cong (fromJust-def (CommRingStr.1r (snd (fst commAlg))))
                        (sym (mb·`mbIdR
                         (map-Maybe (fst (snd commAlg)) (just y))))))

  commonDenomPolynomialTerm' (suc n) (k₀ , x₀ ∷ ms₀) (k₁ , x₁ ∷ ms₁) =
   let ((k₀' , ms₀') , (k₁' , ms₁') , (k₂' , ms₂')) , p , q =
         commonDenomPolynomialTerm' n (k₀ , ms₀) (k₁ , ms₁)
       (x₀' , x₁' , y) , u , v = commonDenomPow x₀ x₁
   in ((k₀' , x₀' ∷ ms₀') , (k₁' , x₁' ∷ ms₁') , (k₂' , y ∷ ms₂'))
        , (λ { (x ∷ xs) →
                (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₀) (evMonomial∷ x₀ ms₀ x xs i) i)
                ∙∙ cong (fromJust-def 1r` (map-Maybe scalar` k₀) ·`_)
                     (fromJust-def-mb·`mb (evMonomial ms₀ xs) (x ^'' x₀))
                ∙∙ R`.·Assoc _ _ _
              ∙∙ cong₂ _·`_
                   (   sym (fromJust-def-mb·`mb (map-Maybe scalar` k₀) (evMonomial ms₀ xs))
                    ∙∙ p xs
                    ∙∙ cong₂ _·`_
                          (fromJust-def-mb·`mb (map-Maybe scalar` k₀') (evMonomial ms₀' xs))
                          (fromJust-def-mb·`mb (map-Maybe scalar` k₂') (evMonomial ms₂' xs)))
                   (cong (fromJust-def 1r`) (u x)
                    ∙ fromJust-def-mb·`mb (x ^'' x₀') _ )
                ∙ R`.·CommAssocSwap _ _ _ _
              ∙∙ cong₂ _·`_
                  (sym (R`.·Assoc _ _ _)
                   ∙∙ cong (fromJust-def 1r` (map-Maybe scalar` k₀') ·`_)
                     (sym (fromJust-def-mb·`mb (evMonomial ms₀' xs) (x ^'' x₀')))
                    ∙∙
                   (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₀')
                           (evMonomial∷ x₀' ms₀' x xs (~ i)) (~ i)))
                  (sym (R`.·Assoc _ _ _)
                   ∙ cong (fromJust-def 1r` (map-Maybe scalar` k₂') ·`_)
                     (sym (fromJust-def-mb·`mb (evMonomial ms₂' xs) (x ^'' y))) ∙
                   (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₂')
                         (evMonomial∷ y ms₂' x xs (~ i)) (~ i)))})
        , (λ { (x ∷ xs) →
                (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₁) (evMonomial∷ x₁ ms₁ x xs i) i)
                ∙∙ cong (fromJust-def 1r` (map-Maybe scalar` k₁) ·`_)
                     (fromJust-def-mb·`mb (evMonomial ms₁ xs) (x ^'' x₁))
                ∙∙ R`.·Assoc _ _ _
              ∙∙ cong₂ _·`_
                   (   sym (fromJust-def-mb·`mb (map-Maybe scalar` k₁) (evMonomial ms₁ xs))
                    ∙∙ q xs
                    ∙∙ cong₂ _·`_
                          (fromJust-def-mb·`mb (map-Maybe scalar` k₁') (evMonomial ms₁' xs))
                          (fromJust-def-mb·`mb (map-Maybe scalar` k₂') (evMonomial ms₂' xs)))
                   (cong (fromJust-def 1r`) (v x)
                    ∙ fromJust-def-mb·`mb (x ^'' x₁') _ )
                ∙ R`.·CommAssocSwap _ _ _ _
              ∙∙ cong₂ _·`_
                  (sym (R`.·Assoc _ _ _)
                   ∙∙ cong (fromJust-def 1r` (map-Maybe scalar` k₁') ·`_)
                     (sym (fromJust-def-mb·`mb (evMonomial ms₁' xs) (x ^'' x₁')))
                    ∙∙
                   (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₁')
                           (evMonomial∷ x₁' ms₁' x xs (~ i)) (~ i)))
                  (sym (R`.·Assoc _ _ _)
                   ∙ cong (fromJust-def 1r` (map-Maybe scalar` k₂') ·`_)
                     (sym (fromJust-def-mb·`mb (evMonomial ms₂' xs) (x ^'' y))) ∙
                   (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₂')
                         (evMonomial∷ y ms₂' x xs (~ i)) (~ i)))})

  commonDenomPolynomialTerm : ∀ n a b →
            Σ[ (a' , b' , c ) ∈ _ × _ × _ ]
                (∀ xs → (evPolynomialTerm {n} a xs ≡
                          evPolynomialTerm {n} a' xs ·` evPolynomialTerm {n} c xs))
                 ×
                (∀ xs → (evPolynomialTerm {n} b xs ≡
                          evPolynomialTerm {n} b' xs ·` evPolynomialTerm {n} c xs))
  commonDenomPolynomialTerm n (false , a₀) (false , a₁) =
    let (a₀' , a₁' , c) , p , q =
           commonDenomPolynomialTerm' n a₀ a₁
    in ((true , a₀') , (true , a₁') , false , c)
        , (λ xs → cong -`_ (p xs) ∙ sym (R`.-DistR· _ _))
        , (λ xs → cong -`_ (q xs) ∙ sym (R`.-DistR· _ _))
  commonDenomPolynomialTerm n (b₀ , a₀) (b₁ , a₁) =
    let (a₀' , a₁' , c) , p , q =
           commonDenomPolynomialTerm' n a₀ a₁
    in ((b₀ , a₀') , (b₁ , a₁') , true , c)
        , (λ xs → cong -`[ b₀ ] (p xs) ∙ sym (-`[ b₀ ]· _ _))
        , (λ xs → cong -`[ b₁ ] (q xs) ∙ sym (-`[ b₁ ]· _ _))

  polynomialNeg  : ∀ {n} → Polynomial n → Polynomial n
  polynomialNeg = L.map (map-fst not)

  ev[polynomialNeg] :  ∀ {n} P xs →
       -` (evPolynomial {n} P xs)
     ≡ evPolynomial (polynomialNeg P) xs
  ev[polynomialNeg] [] xs = R`.0Selfinverse
  ev[polynomialNeg] (x ∷ P) xs =
    cong -`_ (evPolynomial∷ x P xs)
      ∙∙ sym (R`.-Dist _ _)
      ∙∙ (cong₂ _+`_ (ev[polynomialNeg] P xs)
          (-`[not] (fst x) _)
        ∙ sym (evPolynomial∷ _ (polynomialNeg P) xs))


  factorOutMonomial : ∀ {n} (P : Polynomial n) →
                         Σ[ (mm , P') ∈ PolynomialTerm n × Polynomial n ]
                            (∀ xs → evPolynomial P xs ≡ (evPolynomialTerm mm xs ·` evPolynomial P' xs))
  factorOutMonomial [] = (1PolynomialTerm , []) ,
    λ xs → sym (R`.0RightAnnihilates _)
  factorOutMonomial (mm ∷ []) = (mm , [ 1PolynomialTerm ]) ,
    λ xs → sym (R`.·IdR' _ _ (ev1PolynomialTerm xs))
  factorOutMonomial (x ∷ ms) =
    let (mm , P') , u = factorOutMonomial ms
        (x' , mm' , c) , p , q =
           commonDenomPolynomialTerm _ x mm
        P'' = L.map (PolynomialTerm· mm') P'
    in (c , x' ∷ P'') ,
         λ xs  → evPolynomial∷ x ms xs
          ∙∙ cong₂ _+`_
              (u xs ∙ cong (_·` evPolynomial P' xs) (q xs ∙ R`.·Comm _ _)
                ∙∙ sym (R`.·Assoc _ _ _)
                ∙∙ cong (evPolynomialTerm c xs ·`_)
                     (ev[PolynomialTerm·Polynomial] mm' P' xs))
              (p xs ∙ R`.·Comm _ _)
            ∙ sym (R`.·DistR+ _ _ _)
          ∙∙ cong ( evPolynomialTerm c xs ·`_) (sym (evPolynomial∷ x' P'' xs))


 nicefyPolyTm×Poly : ∀ n → (mm : PolynomialTerm n) (P : Polynomial n) →
                        Σ[ (mm' , P') ∈ Maybe (PolynomialTerm n) × Maybe (Polynomial n) ]
                          ((∀ x xs → ((map-Maybe (flip evPolynomialTerm xs) mm'
                             mb·`mb map-Maybe (flip evPolynomial xs) P')
                             mb·` x) ≡ ((evPolynomialTerm mm xs ·` evPolynomial P xs)
                                ·` x) )) ×
                                (∀ xs → (fromJust-def 1r` (map-Maybe (flip evPolynomialTerm xs) mm'
                             mb·`mb map-Maybe (flip evPolynomial xs) P'))
                              ≡ ((evPolynomialTerm mm xs ·` evPolynomial P xs)))

 nicefyPolyTm×Poly n mm P = w (1PolynomialTerm? mm) (ww P)
  where
   ww : ∀ P → Dec (P ≡ [ 1PolynomialTerm {n} ])
   ww [] = no ¬nil≡cons
   ww P[ x ] = mapDec (cong (_∷ [])) (_∘ cong (flip (L.lookupAlways mm) ℕ.zero) ) (1PolynomialTerm? x)
   ww (x ∷ x₁ ∷ P) = no (ℕ.snotz ∘ cong (ℕ.predℕ ∘ L.length))

   w : Dec (mm ≡ 1PolynomialTerm) → Dec (P ≡ [ 1PolynomialTerm ]) → _
   w (yes p) (yes p₁) = (nothing , nothing) ,
     ((λ x xs → sym (R`.·IdL' _ _ (R`.·IdL' _ _
      (cong (flip evPolynomialTerm xs) p
        ∙ ev1PolynomialTerm xs) ∙
         cong (flip evPolynomial xs) (p₁)
           ∙ ev1PolynomialTerm xs))) ,
      λ xs → sym (R`.·IdL' _ _
      (cong (flip evPolynomialTerm xs) p
        ∙ ev1PolynomialTerm xs) ∙
         cong (flip evPolynomial xs) (p₁)
           ∙ ev1PolynomialTerm xs) )
   w (yes p) (no ¬p) = (nothing , just P) ,
     (λ x xs → cong (_·` x) (sym (R`.·IdL' _ _
      (cong (flip evPolynomialTerm xs) p
        ∙ ev1PolynomialTerm xs)))) , λ xs →
          sym (R`.·IdL' _ _
      (cong (flip evPolynomialTerm xs) p
        ∙ ev1PolynomialTerm xs))
   w (no ¬p) (yes p) = (just mm , nothing) , (λ x xs →
     cong (_·` x)
       (sym (R`.·IdR' _ _ (cong (flip evPolynomial xs) p
        ∙ ev1PolynomialTerm xs)))) ,
        λ xs → (sym (R`.·IdR' _ _ (cong (flip evPolynomial xs) p
        ∙ ev1PolynomialTerm xs)))
   w (no ¬p) (no ¬p₁) = (just mm , just P) , (λ _ _ → refl) , λ _ → refl

 Horner→Poly' : Maybe (Discrete ⟨ R ⟩)
                  → ∀ {n} → (h : IteratedHornerForms n)
                     → Σ (Polynomial n) λ pf → ∀ xs → evPolynomial pf xs ≡ eval h xs
 Horner→Poly' nothing (const x) = [ true , (just x) , [] ] , λ {[] → refl}
 Horner→Poly' (just _≟_) (const x) =
    hlp (x ≟ 0r) (x ≟ 1r) (Mb.rec nothing (_$ x) mbNeg?Scalar) (x ≟ (- 1r))
  where
  hlp : Dec _ →  Dec _ → Maybe _ → Dec _ → _
  hlp (yes x≡0) _ _ _ = [] , λ {[] → sym (pres0) ∙ cong scalar` (sym x≡0) }
  hlp _ (yes x≡1) _ x₁ =
    [ true , nothing , [] ] , λ {[] → sym (pres1) ∙ cong scalar` (sym x≡1)}
  hlp _ (no ¬p) _ (yes x≡-1) =
    [ false , nothing , [] ] , λ {[] → sym (pres- 1r
      ∙ cong -`_ pres1) ∙ cong scalar` (sym x≡-1)}
  hlp _ (no ¬p) (just (-x , p)) _ = [ false , (just -x) , [] ] ,
    λ { [] → sym (pres- -x) ∙
            cong scalar` p}
  hlp _ (no ¬p) _ (no ¬p₁) = [ true , (just x) , [] ] , λ {[] → refl}

 Horner→Poly' _  0H = [] , λ _ → refl
 Horner→Poly' mbD (h₀ ·X+ h₁) =
  let p₀ , q₀ = Horner→Poly' mbD h₀
      p₁ , q₁ = Horner→Poly' mbD h₁
  in Poly·X p₀ L.++ Poly↑ p₁ , λ { vvs@(v ∷ vs) →
          evPolynomial++ (Poly·X p₀) (Poly↑ p₁) vvs
       ∙ R`.+Comm _ _ ∙ cong₂ _+`_
          (evPolynomial·X p₀ v vs ∙ cong (_·` v) (q₀ (v ∷ vs)))
          (evPolynomial↑ p₁ v vs ∙ q₁ vs)}

 Horner→Poly : ∀ {n} → (h : IteratedHornerForms n)
                     → Σ (Polynomial n) λ pf → ∀ xs → evPolynomial pf xs ≡ eval h xs
 Horner→Poly = Horner→Poly' mbDiscreteScalars


 module Decidable {requireDiscreteScalar : IsJust mbDiscreteScalars}
                  where


  _≟_ : Discrete ⟨ R ⟩
  _≟_ = fromIsJust requireDiscreteScalar

  prettyCoeffTerm : ∀ {n} → (pt : PolynomialTerm n) →
    Σ[ pt' ∈ _ ] ((∀ xs →
     ((evPolynomialTerm pt xs ≡ evPolynomialTerm pt' xs)))
     )
  prettyCoeffTerm (b , mbK , mm) =
   let (b' , mbK') , p = w b mbK
   in (b' , mbK' , mm) , (λ xs →
       cong -`[ b ] (fromJust-def-mb·`mb (map-Maybe scalar` mbK) _)
          ∙ sym (-`[ b ]· _ _) ∙∙
         cong₂ _·`_ p refl
         ∙∙ (-`[ b' ]· (Mb.fromJust-def 1r`
               (map-Maybe scalar` mbK')) _
           ∙ cong -`[ b' ]
             (sym (fromJust-def-mb·`mb (map-Maybe scalar` mbK')
               (evMonomial mm xs)) )))

   where
    w : ∀ (b : Bool) (mbK : Maybe ⟨ R ⟩) →
       Σ[ (b' , mbK') ∈ _ × _ ] ((
        ((-`[ b ] (Mb.fromJust-def 1r`
               (map-Maybe scalar` mbK))
           ≡ -`[ b' ] (Mb.fromJust-def 1r`
                   (map-Maybe scalar` mbK'))))))
    w b nothing = (b , nothing) , refl
    w b (just x) with x ≟ 1r | x ≟ (- 1r) | mbNeg?Scalar <* x
    ... | yes p | _ | _ = (b , nothing) ,
     cong -`[ b ] (cong scalar` p ∙ pres1)
    w false (just x) | _ | yes p | _ = (true , nothing) ,
      (sym (pres- _) ∙∙ cong scalar` (cong -_ p ∙ -Idempotent _ ) ∙∙ pres1 )
    w true (just x) | _ | yes p | _ = (false , nothing) ,
      cong scalar` p ∙∙ pres- _ ∙∙ cong -`_ pres1
    w false (just x) | _ | _ | just (just (-x , p)) = (true , just -x ) ,
       cong (-`_ ∘ scalar`) (sym p) ∙ sym (pres- _) ∙ cong scalar` (-Idempotent _)
    w true (just x) | _ | _ | just (just (-x , p)) = (false , just -x ) ,
      cong scalar` (sym p) ∙ pres- _
    ... | _ | _ | _ = (b , just x) , refl



  prettyCoeff : ∀ {n} → (P : Polynomial n) →
    Σ[ P' ∈ _ ] (∀ xs → evPolynomial P xs ≡ evPolynomial P' xs )
  prettyCoeff [] = [] , λ _ → refl
  prettyCoeff (x ∷ P) =
   let P' , p = prettyCoeff P
       x' , q = prettyCoeffTerm x
   in x' ∷ P' , λ xs → evPolynomial∷ x P xs
      ∙ cong₂ _+`_ (p xs) (q xs) ∙ sym (evPolynomial∷ x' P' xs)

  commonDenom : ∀ a b → CommonDenom a b
  commonDenom = fromJust-def trivialCD mbCommonDenom

  open CommonMonomial commonDenom
  open PolyUtils
  -- poorFactor : ∀ {n} P → PoorFactor {n} P
  -- poorFactor P = {!P!}


  -- Horner→PolyFCD : ∀ {n}
  --                    → (h : IteratedHornerForms n)
  --                    → Σ (Polynomial n) λ pf → ∀ xs → evPolynomial pf xs ≡ eval h xs
  -- Horner→PolyFCD = {!!}


  HF-Maybe-prfₕ : {n : ℕ} (e₁ e₂ : IteratedHornerForms n)
                   → Maybe [ fst (IHR? e₁ e₂) ]ᵗʸ
  HF-Maybe-prfₕ e₁ e₂ =
   sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR? e₁ e₂))))


  HF-Maybe-prf : (n : ℕ) (e₁ e₂ : RExpr n)
                   → Maybe [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
  HF-Maybe-prf _ e₁ e₂ = HF-Maybe-prfₕ (normalize e₁) (normalize e₂)

  mbIsConstPossiblyNonNull : {n : ℕ}
        → (e : IteratedHornerForms n)
        → Maybe (IsConstPossiblyNonNull e)
  mbIsConstPossiblyNonNull (const _) = just _
  mbIsConstPossiblyNonNull 0H = nothing
  mbIsConstPossiblyNonNull (P ·X+ Q) =
    ⦇ (sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 P)))))
    , (mbIsConstPossiblyNonNull Q) ⦈

  mbFreeOfVar : ∀ {n} P k → Maybe (FreeOfVar {n} P k)
  mbFreeOfVar 0H k = just _
  mbFreeOfVar (P ·X+ Q) zero =
   sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 P))))
  mbFreeOfVar (P ·X+ Q) (suc k) =
    ⦇ (mbFreeOfVar P (suc k)) , (mbFreeOfVar Q k) ⦈


  mbHeadVarOnlyInPow : {n : ℕ}
        → (P : IteratedHornerForms (suc n))
        → Maybe (Σ _ (HeadVarOnlyInPow P))
  mbHeadVarOnlyInPow 0H = just (0 , _)
  mbHeadVarOnlyInPow P+Q@(P ·X+ Q) =
   Mb.rec (do
      v ← sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 Q))))
      (m , u) ← mbHeadVarOnlyInPow P
      pure (suc m , u , v))
     (just ∘ (0 ,_))
     (mbFreeOfVar P+Q zero)


  mbIsolatedPowerVarHead : ∀ {n} P → Maybe (Σ _ (IsolatedPowerHeadVar {n} P))
  mbIsolatedPowerVarHead {n} 0H = nothing
  mbIsolatedPowerVarHead {n} (P ·X+ P₁) = mbHeadVarOnlyInPow P

  -- is broken, TODO : fix it
  -- mbIsolatedPowerVar : ∀ {n} P k → Maybe (Σ _ (IsolatedPowerVar {n} P k))
  -- mbIsolatedPowerVar 0H k = nothing
  -- mbIsolatedPowerVar (P ·X+ Q) zero = mbHeadVarOnlyInPow P
  -- mbIsolatedPowerVar (P ·X+ Q) (suc k) = do
  --      (m , u) ← mbIsolatedPowerVar P (suc k)
  --      (m' , u') ← mbIsolatedPowerVar Q k
  --      decRec
  --        (λ m≡m' →
  --          just (m , u , subst (IsolatedPowerVar Q k) (sym m≡m') u'))
  --         (λ _ → nothing)
  --        (ℕ.discreteℕ m m')

  normalizeIHF' : ∀ {n} → (e : IteratedHornerForms n) → ((e ≑ 0ₕ) ⊎ Σ _ (e ≑_ ))
  normalizeIHF'  (const x) =
     decRec (λ x≡0 → inl λ xs i → eval (HornerForms.const (x≡0 i)) xs)
      (λ _ → inr (HornerForms.const x , λ _ → refl)) (x ≟ 0r)
  normalizeIHF' 0H = inl λ _ → refl
  normalizeIHF' e@(e₀ ·X+ e₁) = h (normalizeIHF' e₀) (normalizeIHF' e₁)
    where
    h : ((e₀ ≑ 0ₕ) ⊎ Σ _ (e₀ ≑_ )) → ((e₁ ≑ 0ₕ) ⊎ Σ _ (e₁ ≑_ )) → ((e ≑ 0ₕ) ⊎ Σ _ (e ≑_ ))
    h (inl x₀) (inl x₁) = inl λ { (v ∷ vs) →
       cong₂ R`._+_
           (R`.0LeftAnnihilates'  _ _  (x₀ (v ∷ vs)))
           (x₁ vs) ∙ R`.+IdR' _ _ (Eval0H vs) }
    h x₀ x₁ =
      let (u₀ , y₀) = ⊎.rec (0ₕ ,_) (idfun _) x₀
          (u₁ , y₁) = ⊎.rec (0ₕ ,_) (idfun _) x₁
      in inr (u₀ ·X+ u₁ , λ { (v ∷ vs) i → y₀ (v ∷ vs) i ·` v +` y₁ vs i })


  normalizeIHF : ∀ {n} → (e : IteratedHornerForms n) → Σ _ (e ≑_ )
  normalizeIHF = ⊎.rec (0ₕ ,_) (idfun _) ∘ normalizeIHF'


  eval' : {n : ℕ} (P : IteratedHornerForms n)
         → (xs : Vec ⟨ R` ⟩ n) → Σ ⟨ R` ⟩ (_≡ eval P xs )
  eval' (const x) xs = _ , refl
  eval' 0H xs = _ , refl
  eval' P@(e₀ ·X+ e₁) vvs@(v ∷ vs) =
    h (normalizeIHF' e₀) (normalizeIHF' e₁)
   where


    ₕ·` : Σ ⟨ R` ⟩ (_≡ fst (eval' e₀ vvs) ·` v )
    ₕ·` with HF-Maybe-prfₕ e₀ (1ₕ) | HF-Maybe-prfₕ e₀ (-ₕ 1ₕ)
    ... | nothing | nothing = _ , refl
    ... | just x | _ = v , sym (R`.·IdL' _ _
       ((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (1ₕ))) x vvs) ∙∙
        Eval1ₕ vvs))
    ... | _ | just x = -` v , sym (R`.·IdL' _ _
       (cong -`_ (((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (-ₕ 1ₕ))) x vvs) ∙∙
          (-EvalDist 1ₕ vvs ∙ cong -`_ (Eval1ₕ vvs))))
        ∙ R`.-Idempotent _))
     ∙ R`.-Dist· _ _




    h : ((e₀ ≑ 0ₕ) ⊎ Σ _ (e₀ ≑_ )) → ((e₁ ≑ 0ₕ) ⊎ Σ _ (e₁ ≑_ )) → Σ ⟨ R` ⟩ (_≡ eval P vvs )
    h (inl x₀) (inl x₁) =  0r` ,
            sym (R`.0LeftAnnihilates'  _ _  (x₀ vvs))
        ∙ sym (R`.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
    h x₀@(inr _) (inl x₁) =  _ ,
      snd ₕ·` ∙ cong (_·` v) (snd (eval' e₀ vvs))
        ∙ sym (R`.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
    h (inl x₁) (inr x) = _ , snd (eval' e₁ vs) ∙ sym (R`.+IdL' _ _
       (R`.0LeftAnnihilates'  _ _  (x₁ vvs)))
    h (inr x₁) (inr x) = _ , cong₂ _+`_
      (snd ₕ·` ∙ cong (_·` v) (snd (eval' e₀ vvs)))
      (snd (eval' e₁ vs))


  normalizeByDec :
    (n : ℕ) (e : RExpr n) (xs : Vec (fst R`) n)
    →  Σ _ (⟦ e ⟧ xs ≡_)
  normalizeByDec n e xs =
    let (P , =P) = Horner→Poly (fst (normalizeIHF (normalize e)))
        ((Smm , Sp) , P=) =  factorOutMonomial P
        (Sp' , =Sp') = prettyCoeff Sp
        ((Smm* , Sp'*) , (_ , Smm*·Sp'*) ) = nicefyPolyTm×Poly n Smm Sp'
    in _ ,
              sym (isEqualToNormalform e xs)
           ∙∙ snd (normalizeIHF (normalize e)) xs
           ∙∙ sym (=P xs)
             ∙∙ P= xs
             ∙∙ cong₂ _·`_ refl (=Sp' xs)
              ∙ sym (Smm*·Sp'* xs)

  tryElimForHead : {n : ℕ} (e₁ e₂ : RExpr (suc n)) →
    Maybe (Σ _ _)
  tryElimForHead e₁ e₂ =
     do let (ihf , v) = normalizeIHF (normalize (e₁ +' -' e₂))
        (m , u) ← mbIsolatedPowerVarHead ihf
        just (1+ m , toElimination ihf m u)

  record PreElim {n} (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n)) : Type (ℓ-max ℓ ℓ`) where
   field
     Smm : PolynomialTerm n
     Sp : Polynomial n
     Qmm : PolynomialTerm n
     Qp : Polynomial n
     m : ℕ
     ep : evPolynomialTerm Smm (drop zero xs) ·`
           evPolynomial Sp (drop zero xs)
          ·` lookup zero xs ^' suc m
          ≡
          evPolynomialTerm Qmm (drop zero xs) ·`
          evPolynomial Qp (drop zero xs)


   solveForHead' : (Σ ((fst R`) × (fst R`)) λ (lhs , rhs) → lhs ≡ rhs)
   solveForHead' =
         let (_ , (niceS , _)) = nicefyPolyTm×Poly _ Smm Sp
             ((Qmm' , Qp') , (_ , niceQ)) = nicefyPolyTm×Poly _ Qmm Qp
         in (_
               , niceS _ (drop zero xs) ∙ ep ∙ sym (niceQ (drop zero xs)))


  preElimHead : {n : ℕ} (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n))
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs →
     Maybe (PreElim e₁ e₂ xs)
  preElimHead e₁ e₂ xss@(x ∷ xs) e₁≡e₂ = do
         let (ihf , v) = normalizeIHF (normalize (e₁ +' -' e₂))
         (m , u) ← mbIsolatedPowerVarHead ihf
         let p = toElimination ihf m u
             (ihfS , eqS) = normalizeIHF (S p)
             (polyS , polyS=) = Horner→Poly ihfS
             (ihfQ , eqQ) = normalizeIHF (-ₕ (Q p))
             (polyQ , polyQ=) = Horner→Poly ihfQ
             ((Smm , Sp) , SeqCFM) =  factorOutMonomial polyS
             ((Qmm , Qp) , QeqCFM) =  factorOutMonomial polyQ
             p =          cong₂ _+`_ (cong₂ _·`_ (polyS= xs
                         ∙ sym (eqS xs))
                     (^'≡^ x (suc m)))
                    (cong -`_ (polyQ= xs ∙
                     sym (eqQ xs) ∙ -EvalDist (Q p) _) ∙
                      R`.-Idempotent _)
                     ∙∙ S·xᵏ+Q≡P p xss  ∙∙
                    sym (v xss) ∙ isEqualToNormalform (e₁ +' -' e₂) xss
                      ∙ R`.+InvR' _ _ e₁≡e₂
         just (record { Smm = Smm ; Sp = Sp ; Qmm = Qmm ; Qp = Qp ; m = m ;
               ep = cong (_·` x ^' suc m) (sym (SeqCFM xs))
              ∙∙  (R`.equalByDifference _ _ p)
              ∙∙ QeqCFM xs })
    where open Elimination

  solveForHead : (n : ℕ) (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n))
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs → Maybe (Σ ((fst R`) × (fst R`)) λ (lhs , rhs) → lhs ≡ rhs)
  solveForHead _ e₁ e₂ xs p = map-Maybe PreElim.solveForHead' (preElimHead e₁ e₂ xs p)

  module SolveIntegalDomains
             (·`lCancel : ∀ c m n → c ·` m ≡ c ·` n → (c ≡ 0r` → ⊥) → m ≡ n)
             (notZeroRing : 1r` ≡ 0r` → ⊥)
            where

    intDom` = fst R`.·lCancel≃integralDomain ·`lCancel

    fromJust-def≡0 : ∀ x → fromJust-def 1r` x ≡ 0r` → x ≡ just 0r`
    fromJust-def≡0 nothing p = ⊥.rec (notZeroRing p)
    fromJust-def≡0 (just x) = cong just

    PolyTerm≡0-Cases : ∀ {n} mm xs → Σ[ ys ∈ List (Type ℓ`) ]
       ([ ys ]ᵗʸ → (evMonomial {n} mm xs ≡ just 0r` → ⊥))

    PolyTerm≡0-Cases [] xs = [] , λ _ → ¬nothing≡just
    PolyTerm≡0-Cases (zero ∷ mm) (x ∷ xs) =
       map-snd ((λ {a} x₁ x₂ p  →
                   let z = sym (mb·`mbIdR _)
                              ∙∙ sym (evMonomial∷ zero mm x xs)
                              ∙∙ p
                    in x₁ x₂ z))
        (PolyTerm≡0-Cases mm xs)
    PolyTerm≡0-Cases (suc m ∷ mm) (x ∷ xs) =
       let ys , u = PolyTerm≡0-Cases mm xs
       in (x ≡ 0r` → ⊥) ∷ ys ,
            λ { (x≢0 ∷ v) p →
               let z =    cong₂ _·`_ (cong (fromJust-def 1r`) (sym (^''suc x m))) refl ∙ R`.·Comm _ _
                       ∙∙ sym (fromJust-def-mb·`mb (evMonomial mm xs) (x ^'' suc m))
                       ∙∙ cong (fromJust-def 1r`) (sym (evMonomial∷ (suc m) mm x xs) ∙ p)

                   w = intDom` (x ^ (suc m)) (fromJust-def 1r` (evMonomial mm xs))
                         z
                          (IntegralDomain.x≢0→x^sn≢0 intDom` x m x≢0)
               in u v (fromJust-def≡0 _ w) }

    PolyTerm·Poly≡0-Cases : ∀ {n} mm P xs
     → Maybe (Σ[ ys ∈ List (Type ℓ`) ]
       ((evPolynomialTerm mm xs ·` evPolynomial {n} P xs ≡ 0r`) →  [ ys ]ᵗʸ →
         evPolynomial {n} P xs ≡ 0r`))
    PolyTerm·Poly≡0-Cases mmm@(b , nothing , mm) P xs =
          let u , v = PolyTerm≡0-Cases mm xs
          in just (u , λ p ys → intDom` (evPolynomialTerm mmm xs) _
               p (v ys ∘S (fromJust-def≡0 _) ∘S _∙ -`[ b ]0 ∘S -`[ b ]-flip≡ _ _))



    PolyTerm·Poly≡0-Cases mmm@(b , just k , mm) P xs =
      decRec (λ _ → nothing)
        (λ ¬k≡0 →
          let u , v = PolyTerm≡0-Cases mm xs
          in Mb.rec
              (just (_ ∷ u , λ p → λ {(y ∷ ys) →
                intDom` (evPolynomialTerm mmm xs) _
               p (v ys ∘S (fromJust-def≡0 _) ∘S flip (intDom` _ _) (y)
                 ∘S sym (fromJust-def-mb·`mb (just (scalar` k)) (evMonomial mm xs))
                   ∙∙_∙∙ -`[ b ]0 ∘S  -`[ b ]-flip≡ _ _)}))
              (λ ≢0r→≢0r` →
              just (u , λ p ys → intDom` (evPolynomialTerm mmm xs) _
               p (v ys ∘S (fromJust-def≡0 _) ∘S flip (intDom` _ _) (≢0r→≢0r` _ ¬k≡0)
                 ∘S sym (fromJust-def-mb·`mb (just (scalar` k)) (evMonomial mm xs))
                   ∙∙_∙∙ -`[ b ]0 ∘S  -`[ b ]-flip≡ _ _)))
                   mb≢0r→≢0r`) (k ≟ 0r)

  eliminateHead : (n : ℕ) (e₁ e₂ e'₁ e'₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n))
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs → ⟦ e'₁ ⟧ xs ≡ ⟦ e'₂ ⟧ xs →
      String ⊎ (Σ[ (xs , lhs) ∈ List (Type ℓ`) × (fst R`) ] ([ xs ]ᵗʸ → lhs ≡ 0r`))
  eliminateHead _ e₁ e₂ e'₁ e'₂ xxs@(x ∷ xs) e₁≡e₂ e'₁≡e'₂ = do
    pe ← maybeToSum "unable to elim from first eq" (preElimHead e₁ e₂ xxs e₁≡e₂)
    pe' ← maybeToSum "unable to elim from snd eq" (preElimHead e'₁ e'₂ xxs e'₁≡e'₂)
    let (peSmm* , pe'Smm* , c) , peSmm*·c≡peSmm , pe'Smm*·c≡pe'Smm
             = commonDenomPolynomialTerm _ (pe .Smm) (pe' .Smm)
    maybeToSum "unimplemented - solved var extractend with different powers"
      (decToMaybe (ℕ.discreteℕ (pe .m) (pe' .m)) >>=
      λ m≡m' →  do
         let pe'Sp·peQp = Polynomial· (pe' .Sp) (pe .Qp)
             peSp·pe'Qp = Polynomial· (pe .Sp) (pe' .Qp)
             polyLHS = (L.map (PolynomialTerm· (PolynomialTerm· pe'Smm* (pe .Qmm)))
                    (fst pe'Sp·peQp))
             polyRHS = (L.map (PolynomialTerm· (PolynomialTerm· peSmm* (pe' .Qmm)))
                      (fst peSp·pe'Qp))
             polyDiff = Polynomial+ polyLHS (polynomialNeg polyRHS)
             ((Smm , Sp) , SeqCFM) =  factorOutMonomial (fst polyDiff)
             pp : evPolynomial polyLHS xs
                    ≡
                    evPolynomial polyRHS xs
             pp = sym (ev[PolynomialTerm·Polynomial]
                    (PolynomialTerm· pe'Smm* (pe .Qmm)) (fst pe'Sp·peQp) xs)
                ∙ cong₂ (_·`_) (PolynomialTerm·-sound pe'Smm* (pe .Qmm) xs)
                  (snd pe'Sp·peQp xs)
                 ∙∙ R`.·CommAssocSwap _ _ _ _
                 ∙∙ (cong₂ (_·`_) (R`.·Comm _ _) (sym (pe .ep) ∙
                  cong₂ _·`_ (cong₂ _·`_ (peSmm*·c≡peSmm xs) refl) refl)
                ∙∙ R`.·Assoc _ _ _ ∙∙
                  cong₂ _·`_ ( (sym (R`.·Assoc _ _ _)
                     ∙ cong₂ _·`_ refl
                        (   cong₂ _·`_ refl
                          (sym (R`.·Assoc _ _ _) ∙∙ R`.·Comm _ _ ∙∙ sym (R`.·Assoc _ _ _))
                         ∙∙ R`.·Assoc _ _ _
                         ∙∙ R`.·Comm _ _))
                    ∙∙ R`.·Comm _ _ -- (R`.·Assoc _ _ _)
                    ∙∙ sym (R`.·Assoc _ _ _))
                    (cong ((x ^'_) ∘ suc) m≡m')
                  ∙∙ sym (R`.·Assoc _ _ _)
                ∙∙ cong₂ (_·`_) (R`.·Comm _ _)
                  (cong₂ _·`_ (cong₂ _·`_ (sym (pe'Smm*·c≡pe'Smm xs)) refl) refl
                 ∙ pe' .ep )) ∙∙ R`.·CommAssocSwap _ _ _ _
                  ∙∙ cong₂ (_·`_) (sym (PolynomialTerm·-sound peSmm* (pe' .Qmm) xs))
                  (sym (snd peSp·pe'Qp xs))
                  ∙ (ev[PolynomialTerm·Polynomial]
                    (PolynomialTerm· peSmm* (pe' .Qmm)) (fst peSp·pe'Qp) xs)
             pp' =
                   sym (SeqCFM xs)
                ∙  snd polyDiff xs
                ∙∙ cong₂ _+`_ refl (sym (ev[polynomialNeg] polyRHS xs))
                ∙∙ R`.differenceByEqual _ _ pp
         zzz ← pure {A = ℕ} 3

         (do pt-cases ← (λ (a , y) → ((a , evPolynomial Sp xs) , y pp')) <$>_
                  <$> ((PolyTerm·Poly≡0-Cases <$> mb·`lCancel <*> mbNotZeroRing) <*'
                                _ <* Smm <* Sp <* xs)

             pt-cases) <|> pure (([] , _) , λ _ → pp'))


   where
    open PreElim
    open SolveIntegalDomains
  -- pickEliminations : {n : ℕ} (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n)) →
  --   Vec (Maybe ℕ) (suc n)
  -- pickEliminations e₁ e₂ xs =
  --   let (ihf , u) = normalizeIHF (normalize (e₁ +' -' e₂))
  --   in tabulate (λ k →
  --         map-Maybe (fst) (mbIsolatedPowerVar ihf k))


  solveByDifference :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
     → fst (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs) ≡ 0r`
     → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solveByDifference e₁ e₂ xs ev=0 =
      R`.equalByDifference _ _ $
         cong₂ _+`_ (sym (isEqualToNormalform e₁ xs))
          (cong -`_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
          ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
            snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs ∙
             sym (snd (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs)) ∙ ev=0


  solveByDifference' :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
     → evPolynomial (Horner→Poly
      (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) . fst) xs
       ≡ 0r` → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solveByDifference' e₁ e₂ xs ev=0 =
      R`.equalByDifference _ _ $
         cong₂ _+`_ (sym (isEqualToNormalform e₁ xs))
          (cong -`_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
          ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
              (snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs)
             ∙ sym ((Horner→Poly
              (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) . snd) xs) ∙ ev=0



--

 -- congSolve :
 --   {n : ℕ} (e₁ e₂ : RExpr n) → ∀ {xs xs' : Vec (fst R`) n} → xs ≡ xs'
 --   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs'
 -- congSolve e₁ e₂ {xs} {xs'} p z =
 --   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 --   eval (normalize e₁) xs ≡⟨
 --    cong₂ eval (fst (snd (IHR? (normalize e₁) (normalize e₂))) z) p ⟩
 --   eval (normalize e₂) xs' ≡⟨ isEqualToNormalform e₂ xs' ⟩
 --   ⟦ e₂ ⟧ xs' ∎

 -- solveByPath :
 --   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
 --   → eval (normalize e₁) xs ≡ eval (normalize e₂) xs → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 -- solveByPath e₁ e₂ xs p =
 --    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 --    eval (normalize e₁) xs ≡⟨ p ⟩
 --    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
 --    ⟦ e₂ ⟧ xs ∎
