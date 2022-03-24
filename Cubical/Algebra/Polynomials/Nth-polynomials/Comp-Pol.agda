{-# OPTIONS --safe #-}
module Cubical.Algebra.Polynomials.Nth-polynomials.Comp-Pol where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials.Polynomials

open import Cubical.Algebra.Polynomials.Nth-polynomials.Base
open import Cubical.Algebra.Polynomials.Nth-polynomials.CommRing-Structure

private variable
  l l' : Level

module Compo-Pol-nm (A' : CommRing l) (n m : ℕ) where
  private
    A = fst A'
  open CommRingStr (snd A')

  module M   = PolyHIT A'
  module Mr  = Nth-Pol-CommRing A' m
  module N+M  = PolyHIT A'
  module N+Mr = Nth-Pol-CommRing A' (n +n m)
  module N∘M = PolyHIT (Mr.nth-Pol-CommRing)
  module N∘Mr  = Nth-Pol-CommRing Mr.nth-Pol-CommRing n 



-----------------------------------------------------------------------------
-- Some lemma for the traduction

  sep-vec : (k l : ℕ) → Vec ℕ (k +n l) → (Vec ℕ k) ×  (Vec ℕ l )
  sep-vec zero l v = [] , v
  sep-vec (suc k) l (x ∷ v) = (x ∷ fst (sep-vec k l v)) , (snd (sep-vec k l v))

  sep-vec-fst : (k l : ℕ) → (v : Vec ℕ k) → (v' : Vec ℕ l) → fst (sep-vec k l (v ++ v')) ≡ v
  sep-vec-fst zero l [] v' = refl
  sep-vec-fst (suc k) l (x ∷ v) v' = cong (λ X → x ∷ X) (sep-vec-fst k l v v')

  sep-vec-snd : (k l : ℕ) → (v : Vec ℕ k) → (v' : Vec ℕ l) → snd (sep-vec k l (v ++ v')) ≡ v'
  sep-vec-snd zero l [] v' = refl
  sep-vec-snd (suc k) l (x ∷ v) v' = sep-vec-snd k l v v'

  sep-vec-id : (k l : ℕ) → (v : Vec ℕ (k +n l)) → fst (sep-vec k l v) ++ snd (sep-vec k l v) ≡ v
  sep-vec-id zero l v = refl
  sep-vec-id (suc k) l (x ∷ v) = cong (λ X → x ∷ X) (sep-vec-id k l v)

  rep-concat : (k l : ℕ) → {B : Type l'} → (b : B) → replicate {_} {k} {B} b ++ replicate {_} {l} {B} b ≡ replicate {_} {k +n l} {B} b
  rep-concat zero l b = refl
  rep-concat (suc k) l b = cong (λ X → b ∷ X) (rep-concat k l b)

  +n-vec-concat : (k l : ℕ) → (v w : Vec ℕ k) → (v' w' : Vec ℕ l) → (v Mr.+n-vec w) ++ (v' Mr.+n-vec w') ≡ (v ++ v') Mr.+n-vec (w ++ w')
  +n-vec-concat zero l [] [] v' w' = refl
  +n-vec-concat (suc k) l (x ∷ v) (y ∷ w) v' w' = cong (λ X → x +n y ∷ X) (+n-vec-concat k l v w v' w')

-----------------------------------------------------------------------------
-- direct sens

  N∘M→N+M-b : (v : Vec ℕ n) → N+M.Poly m → N+M.Poly (n +n m)
  N∘M→N+M-b v = N+M.Poly-Rec-Set.f m (N+M.Poly (n +n m)) N+M.trunc
                N+M.0P
                (λ v' a → N+M.base (v ++ v') a)
                N+M._Poly+_
                N+M.Poly+-assoc
                N+M.Poly+-Rid
                N+M.Poly+-comm
                (λ v' → N+M.base-0P (v ++ v'))
                (λ v' a b → N+M.base-Poly+ (v ++ v') a b)

  N∘M→N+M : N∘M.Poly n → N+M.Poly (n +n m)
  N∘M→N+M = N∘M.Poly-Rec-Set.f n (N+M.Poly (n +n m)) N+M.trunc
           N+M.0P
           N∘M→N+M-b
           N+M._Poly+_
           N+M.Poly+-assoc
           N+M.Poly+-Rid
           N+M.Poly+-comm
           (λ _ → refl)
           (λ v a b → refl)


-----------------------------------------------------------------------------
-- Converse sens

  N+M→N∘M : N+M.Poly (n +n m) → N∘M.Poly n
  N+M→N∘M = N+M.Poly-Rec-Set.f (n +n m) (N∘M.Poly n) N∘M.trunc
            N∘M.0P
            (λ v a → let v , v'  = sep-vec n m v in
                      N∘M.base v (M.base v' a))
            N∘M._Poly+_
            N∘M.Poly+-assoc
            N∘M.Poly+-Rid
            N∘M.Poly+-comm
            (λ v → (cong (N∘M.base (fst (sep-vec n m v))) (M.base-0P (snd (sep-vec n m v)))) ∙ (N∘M.base-0P (fst (sep-vec n m v))))
            λ v a b → N∘M.base-Poly+ (fst (sep-vec n m v)) (M.base (snd (sep-vec n m v)) a) (M.base (snd (sep-vec n m v)) b)
                       ∙ cong (N∘M.base (fst (sep-vec n m v))) (M.base-Poly+ (snd (sep-vec n m v)) a b)


-----------------------------------------------------------------------------
-- Section 
  
  e-sect : (P : N∘M.Poly n) → N+M→N∘M (N∘M→N+M P) ≡ P
  e-sect = N∘M.Poly-Ind-Prop.f n
           (λ P → N+M→N∘M (N∘M→N+M P) ≡ P)
           (λ _ → N∘M.trunc _ _)
           refl
           (λ v → M.Poly-Ind-Prop.f m
                   (λ P → N+M→N∘M (N∘M→N+M (N∘M.base v P)) ≡ N∘M.base v P)
                   (λ _ → N∘M.trunc _ _)
                   (sym (N∘M.base-0P v))
                   (λ v' a → cong₂ N∘M.base (sep-vec-fst n m v v') (cong (λ X → M.base X a) (sep-vec-snd n m v v')))
                   (λ {U V} ind-U ind-V → (cong₂ N∘M._Poly+_ ind-U ind-V) ∙ (N∘M.base-Poly+ v U V)))
           (λ {U V} ind-U ind-V → cong₂ N∘M._Poly+_ ind-U ind-V )


-----------------------------------------------------------------------------
-- Retraction

  e_retr : (P : N+M.Poly (n +n m)) → N∘M→N+M (N+M→N∘M P) ≡ P
  e_retr = N+M.Poly-Ind-Prop.f (n +n m)
           (λ P → N∘M→N+M (N+M→N∘M P) ≡ P)
           (λ _ → N+M.trunc _ _)
           refl
           (λ v a → cong (λ X → N+M.base X a) (sep-vec-id n m v))
           (λ {U V} ind-U ind-V → cong₂ N+M._Poly+_ ind-U ind-V)


-----------------------------------------------------------------------------
-- Morphism of ring

  map-0P : N∘M→N+M (N∘M.0P) ≡ N+M.0P
  map-0P = refl

  N∘M→N+M-gmorph : (P Q : N∘M.Poly n) → N∘M→N+M ( P N∘M.Poly+ Q) ≡ N∘M→N+M P N+M.Poly+ N∘M→N+M Q
  N∘M→N+M-gmorph = λ P Q → refl

  map-1P : N∘M→N+M (N∘Mr.1P) ≡ N+Mr.1P
  map-1P = cong (λ X → N+M.base X 1r) (rep-concat n m 0 )

  N∘M→N+M-rmorph : (P Q : N∘M.Poly n) → N∘M→N+M ( P N∘Mr.Poly* Q) ≡ N∘M→N+M P N+Mr.Poly* N∘M→N+M Q
  N∘M→N+M-rmorph =
    -- Ind P
    N∘M.Poly-Ind-Prop.f n
    (λ P → (Q : N∘M.Poly n) → N∘M→N+M (P N∘Mr.Poly* Q) ≡ (N∘M→N+M P N+Mr.Poly* N∘M→N+M Q))
    (λ P p q i Q j → N+M.trunc _ _ (p Q) (q Q) i j)
    (λ Q → refl)
    (λ v → -- Ind Base P
           M.Poly-Ind-Prop.f m 
           (λ P → (Q : N∘M.Poly n) → N∘M→N+M (N∘M.base v P N∘Mr.Poly* Q) ≡ (N∘M→N+M (N∘M.base v P) N+Mr.Poly* N∘M→N+M Q))
           (λ P p q i Q j → N+M.trunc _ _ (p Q) (q Q) i j)
           (λ Q → cong (λ X → N∘M→N+M (X N∘Mr.Poly* Q)) (N∘M.base-0P v)) 
           (λ v' a → -- Ind Q
                      N∘M.Poly-Ind-Prop.f n
                      (λ Q → N∘M→N+M (N∘M.base v (M.base v' a) N∘Mr.Poly* Q) ≡ (N∘M→N+M (N∘M.base v (M.base v' a)) N+Mr.Poly* N∘M→N+M Q))
                      (λ _ → N+M.trunc _ _)
                      (sym (N+Mr.0PRightAnnihilatesPoly (N∘M→N+M (N∘M.base v (M.base v' a)))))
                      (λ w → -- Ind base Q
                              M.Poly-Ind-Prop.f m
                              _
                              (λ _ → N+M.trunc _ _)
                              (sym (N+Mr.0PRightAnnihilatesPoly (N∘M→N+M (N∘M.base v (M.base v' a)))))
                              (λ w' b → cong (λ X → N+M.base X (a · b)) (+n-vec-concat n m v w v' w'))
                              λ {U V} ind-U ind-V → cong (λ X → N∘M→N+M (N∘M.base v (M.base v' a) N∘Mr.Poly* X)) (sym (N∘M.base-Poly+ w U V))
                                                     ∙ cong₂ (N+M._Poly+_ ) ind-U ind-V
                                                     ∙ sym (cong (λ X → N∘M→N+M (N∘M.base v (M.base v' a)) N+Mr.Poly* N∘M→N+M X) (N∘M.base-Poly+ w U V)) )
                              -- End Ind base Q
                      λ {U V} ind-U ind-V → cong₂ N+M._Poly+_ ind-U ind-V)
                      -- End Ind Q
           λ {U V} ind-U ind-V Q → cong (λ X → N∘M→N+M (X N∘Mr.Poly* Q)) (sym (N∘M.base-Poly+ v U V))
                                    ∙ cong₂ N+M._Poly+_ (ind-U Q) (ind-V Q)
                                    ∙ sym (cong (λ X → (N∘M→N+M X) N+Mr.Poly* (N∘M→N+M Q)) (sym (N∘M.base-Poly+ v U V)) ))
           -- End Ind base P
     λ {U V} ind-U ind-V Q → cong₂ N+M._Poly+_ (ind-U Q) (ind-V Q)
     -- End Ind P
