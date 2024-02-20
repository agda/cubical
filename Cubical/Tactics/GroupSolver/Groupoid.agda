{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.Groupoid where


open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe as Mb


open import Cubical.HITs.Interval

open import Cubical.Relation.Nullary

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.GroupSolver.Reflection
open import Cubical.Tactics.Reflection
open import Agda.Builtin.String


private
  variable
    ℓ ℓ' : Level

   


module _ {A : Type ℓ} (_≟_ : Discrete A) where

 fa : ℕ → (xs ys : List A) → Maybe (Σ _ λ k → xs ≡ rotN k ys)
 fa zero _ _ = nothing
 fa (suc k) xs ys =
   decRec (just ∘ ((length xs ∸ k) ,_))
    (λ _ → fa k xs ys) (discreteList _≟_ xs (rotN (length xs ∸ k) ys) )

 findAligment : (xs ys : List A) → Maybe (Σ _ λ k → xs ≡ rotN k ys)  
 findAligment xs ys = fa (suc (length xs)) xs ys


module _ {A : Type ℓ} where
 data PathCase : {a₀ a₁ : A} → a₀ ≡ a₁ → Type ℓ where
  reflCase : ∀ {x} → PathCase (refl {x = x})
  compCase : ∀ {x y z w} → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
             →  PathCase (p ∙∙ q ∙∙ r)


module PT {A : Type ℓ} (_∼_ : A → A → Type ℓ') (∼refl : ∀ {x} → x ∼ x)
         (_∼∙_ : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z)
         (_∼∙∙_∼∙∙_ : ∀ {x y z w} → x ∼ y → y ∼ z → z ∼ w → x ∼ w)
         (∼doubleCompPath-elim : ∀ {x y z w} → 
           (p : x ∼ y) → (q : y ∼ z) → (r : z ∼ w) → (p ∼∙∙ q ∼∙∙ r) ≡ (p ∼∙ q) ∼∙ r)
         (∼assoc : ∀ {x y z w} → (p : x ∼ y) (q : y ∼ z) (r : z ∼ w) → p ∼∙ (q ∼∙ r) ≡ (p ∼∙ q) ∼∙ r)
         where



 data IsPathTrm : {a₀ a₁ : A} → a₀ ∼ a₁ → Type (ℓ-max ℓ ℓ') where
  isReflTrm : ∀ {x} → IsPathTrm (∼refl {x = x})
  isAtomTrm : ∀ {x y} → (p : x ∼ y) → IsPathTrm p
  isCompTrm : ∀ {x y z w : _} → {p : x ∼ y} {q : y ∼ z} {r : z ∼ w}
   → IsPathTrm p → IsPathTrm q → IsPathTrm r → IsPathTrm (p ∼∙∙ q ∼∙∙ r)




 data IsPathTrmReg : {a₀ a₁ : A} → a₀ ∼ a₁ → Type (ℓ-max ℓ ℓ') where
  isReflTrmReg : ∀ {x} → IsPathTrmReg (∼refl {x = x})
  isAtomTrmReg : ∀ {x y} → (p : x ∼ y) → IsPathTrmReg p
  isCompTrmReg : ∀ {x y z : _} → {p : x ∼ y} {q : y ∼ z}
   → IsPathTrmReg p → IsPathTrmReg q → IsPathTrmReg (p ∼∙ q)

 data IsPathTrmDeas : {a₀ a₁ : A} → a₀ ∼ a₁ → Type (ℓ-max ℓ ℓ') where
  nilTrmDeasRefl : ∀ {x} → IsPathTrmDeas (∼refl {x = x})
  consTrmDeas : ∀ {x y z : _} → {p : x ∼ y} → IsPathTrmDeas p → (q : y ∼ z) → IsPathTrmDeas (p ∼∙ q)
  
 data IsPathTrmInvol : (a₀ a₁ : A) → Type (ℓ-max ℓ ℓ') where
  nilTrmInvolRefl : ∀ {x} → IsPathTrmInvol x x
  consTrmInvol : ∀ {x y z : _}  →
   IsPathTrmInvol x y → (q : y ∼ z) → IsPathTrmInvol x z
  involTrmInvol : ∀ {x y z : _} → IsPathTrmInvol x y → (q : y ∼ z) →
    IsPathTrmInvol x y


 module show (showA : {a₀ a₁ : A} → (p : a₀ ∼ a₁) → String) where
  showIPT : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrm p → String
  showIPT isReflTrm = "refl"
  showIPT (isAtomTrm x) = showA x
  showIPT (isCompTrm isReflTrm x₁ x₂) =
        "(" <> showIPT x₁ <> "∙" <> showIPT x₂ <> ")"
  showIPT (isCompTrm x x₁ isReflTrm) =
         "(" <> showIPT x <> "∙'" <> showIPT x₁ <> ")"
  showIPT (isCompTrm x x₁ x₂) =
        "(" <> showIPT x <> "∙∙" <> showIPT x₁ <> "∙∙" <> showIPT x₂ <> ")"
  
  showIPTD : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrmDeas p → String
  
  showIPTD nilTrmDeasRefl = "refl"
  showIPTD (consTrmDeas x q) = showIPTD x <> "∙" <> showA q

  showIPTI : {a₀ a₁ : A} → IsPathTrmInvol a₀ a₁ → String
  showIPTI nilTrmInvolRefl = "refl"
  showIPTI (consTrmInvol x q) = showIPTI x <> "∙" <> showA q
  showIPTI (involTrmInvol x q) = showIPTI x <> "∙⟦" <> showA q <> "∙" <> showA q  <> "⁻¹⟧"

 
 depthIsPathTrmDeas : ∀ {a₀ a₁ : A} → ∀ {p : a₀ ∼ a₁}
                          → IsPathTrmDeas p → ℕ 
 depthIsPathTrmDeas nilTrmDeasRefl = zero
 depthIsPathTrmDeas (consTrmDeas x q) = suc (depthIsPathTrmDeas x)

 hasRedexes : ∀ {a₀ a₁} → IsPathTrmInvol a₀ a₁ → Bool 
 hasRedexes nilTrmInvolRefl = false
 hasRedexes (consTrmInvol x q) = hasRedexes x
 hasRedexes (involTrmInvol x q) = true

 Deas→Invol : ∀ {a₀ a₁ : A} → ∀ {p} → IsPathTrmDeas {a₀ = a₀} {a₁ = a₁} p → IsPathTrmInvol a₀ a₁ 
 Deas→Invol nilTrmDeasRefl = nilTrmInvolRefl
 Deas→Invol (consTrmDeas x q) = consTrmInvol (Deas→Invol x) q

 IsPathTrmDeas∙ : ∀ {x y z : _} → {p : x ∼ y} {q : y ∼ z} →
   IsPathTrmDeas p → IsPathTrmDeas q → Σ _ λ p∙q → IsPathTrmDeas {x} {z} p∙q
 IsPathTrmDeas∙ p' nilTrmDeasRefl = _ , p'
 IsPathTrmDeas∙ nilTrmDeasRefl q'@(consTrmDeas _ _) = _ , q'
 IsPathTrmDeas∙ p' (consTrmDeas q' q'') =
   let (_ , u) = IsPathTrmDeas∙ p' q'
   in _ , consTrmDeas u q''


 Invol→Deas↓ : ∀ {a₀ a₁ : A} → IsPathTrmInvol a₀ a₁ → Σ _ $ IsPathTrmDeas {a₀ = a₀} {a₁ = a₁}
 -- Invol→Deas↓ (nilTrmInvol p) = _ , iptd' (nilTrmDeas p)
 -- Invol→Deas↓ (nilInvolTrmInvol p) = _ , nilTrmDeasRefl
 Invol→Deas↓ nilTrmInvolRefl = _ , nilTrmDeasRefl 
 Invol→Deas↓ (consTrmInvol x q) =
   IsPathTrmDeas∙ (snd (Invol→Deas↓ x)) (consTrmDeas nilTrmDeasRefl q)
 Invol→Deas↓ (involTrmInvol x q) = Invol→Deas↓ x

 ⟦_⟧r : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrm p → (Σ _ λ r → (IsPathTrmReg r × (p ≡ r)))  
 ⟦ isReflTrm ⟧r = ∼refl , isReflTrmReg , refl
 ⟦ isAtomTrm p ⟧r = p , isAtomTrmReg _ , refl
 ⟦ isCompTrm {p = p} {q = q} {r = r} p' q' r' ⟧r =
   let (_ , pR , p=) = ⟦ p' ⟧r ; (_ , qR , q=) = ⟦ q' ⟧r ; (_ , rR , r=) = ⟦ r' ⟧r
   in _ , isCompTrmReg (isCompTrmReg pR qR) rR ,
            λ i → ∼doubleCompPath-elim (p= i) (q= i) (r= i) i


 ⟦_⟧da : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrmReg p → (Σ _ λ r → (IsPathTrmDeas r))  
 ⟦ isReflTrmReg ⟧da = _ , nilTrmDeasRefl
 ⟦ isAtomTrmReg p ⟧da = _ ,  consTrmDeas nilTrmDeasRefl p
 ⟦ isCompTrmReg p' q' ⟧da =
   let (_ , qD) = ⟦ q' ⟧da
       (_ , pD) = ⟦ p' ⟧da
       (_ , p∙qD) = IsPathTrmDeas∙ pD qD
   in _ , p∙qD 

 ⟦_⟧da∘r : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrm p → (Σ _ IsPathTrmDeas)
 ⟦ x ⟧da∘r =  ⟦ fst (snd (⟦ x ⟧r)) ⟧da
 module PT≡ (∼rUnit : ∀ {x y} → (p : x ∼ y) → p ≡ p ∼∙ ∼refl)
            (∼lUnit : ∀ {x y} → (p : x ∼ y) → p ≡  ∼refl ∼∙ p) where

  IsPathTrmDeas∙≡ : ∀ {x y z : _} → {p : x ∼ y} {q : y ∼ z} →
    (p' : IsPathTrmDeas p) → (q' : IsPathTrmDeas q) →
      (fst (IsPathTrmDeas∙ p' q') ≡ (p ∼∙ q))
  IsPathTrmDeas∙≡ _ nilTrmDeasRefl = ∼rUnit _
  IsPathTrmDeas∙≡ nilTrmDeasRefl (consTrmDeas p q) = ∼lUnit _
  IsPathTrmDeas∙≡ (consTrmDeas p q) (consTrmDeas p' q') =
    cong (_∼∙ q')  ( (IsPathTrmDeas∙≡ (consTrmDeas p q) p')) ∙
      sym (∼assoc _ _ _)
 
  ⟦_⟧da≡ : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → (p' : IsPathTrmReg p) →
           fst ⟦ p' ⟧da ≡ p
  ⟦ isReflTrmReg ⟧da≡ = refl
  ⟦ isAtomTrmReg _ ⟧da≡ = sym (∼lUnit _)
  ⟦ isCompTrmReg p' q' ⟧da≡ = 
     IsPathTrmDeas∙≡ (snd ⟦ p' ⟧da) (snd ⟦ q' ⟧da) ∙ cong₂ _∼∙_ ⟦ p' ⟧da≡ ⟦ q' ⟧da≡ 
  
  daSingl : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → (q : IsPathTrm p) → p ≡ fst ⟦ fst (snd ⟦ q ⟧r) ⟧da
  daSingl x = let (_ , x' , x=) = ⟦ x ⟧r in x= ∙ sym (⟦ x' ⟧da≡)



module _ {A : Type ℓ} where

 open PT {A = A} _≡_ refl _∙_ _∙∙_∙∙_ doubleCompPath-elim assoc public
 open PT≡ rUnit lUnit public



 ⟦_,_⟧ti : {a₀ a₁ : A} → IsPathTrmInvol a₀ a₁ → Interval → a₀ ≡ a₁
 ⟦ nilTrmInvolRefl , _ ⟧ti = refl
 ⟦ consTrmInvol x q , 𝓲 ⟧ti = ⟦ x , 𝓲 ⟧ti ∙ q 
 ⟦ involTrmInvol x q , zero ⟧ti = (⟦ x , zero ⟧ti ∙ q) ∙ sym q
 ⟦ involTrmInvol x q , one ⟧ti = ⟦ x , one ⟧ti
 ⟦ involTrmInvol x q , seg j ⟧ti i =
   hcomp (λ k → λ { (j = i1) → ⟦ x , one ⟧ti i
                  ; (i = i1) → q (~ k ∧ ~ j)
                  ; (i = i0) → ⟦ x , seg j ⟧ti i0
                  }) (compPath-filler ⟦ x , seg j ⟧ti q (~ j) i)

 ⟦_⟧ti≡ : {a₀ a₁ : A} → (x : IsPathTrmInvol a₀ a₁) → ⟦ x , zero ⟧ti ≡ ⟦ x , one ⟧ti
 ⟦_⟧ti≡ x i = ⟦ x , (seg i) ⟧ti 



module _ (A : Type ℓ) (a : A) where
 module PTG = PT {A = Unit} (λ _ _ → A)
                  (a)
                  (λ _ _ → a)
                  (λ _ _ _ → a)
                  (λ _ _ _ → refl)
                  (λ _ _ _ → refl)
                  -- (R.def (quote refl) [])
                  -- (λ x y z → R.def (quote _∙∙_∙∙_) (x v∷ y v∷ z v∷ []))

module PTrm = PTG R.Term R.unknown 

module Pℕ = PTG (Bool × ℕ) (true , 0) 

module PℕS = Pℕ.show (λ (b , i) → let v = mkNiceVar i in if b then v else (v <> "⁻¹"))


module _ (f : (Bool × ℕ) → R.Term) where
 mapPTG : Pℕ.IsPathTrmInvol _ _ → PTrm.IsPathTrmInvol _ _
 -- mapPTG (PT.nilTrmInvol x) = PT.nilTrmInvol (f x)
 -- mapPTG (PT.nilInvolTrmInvol p) = PT.nilInvolTrmInvol (f p)
 mapPTG PT.nilTrmInvolRefl = PT.nilTrmInvolRefl 
 mapPTG (PT.consTrmInvol x q) = PT.consTrmInvol (mapPTG x) (f q)
 mapPTG (PT.involTrmInvol x q) = PT.involTrmInvol (mapPTG x) (f q)


-- ℕDeas'→ℕInvol : ∀ {p} → Pℕ.IsPathTrmDeas' p → Pℕ.IsPathTrmInvol _ _

IsRedex? : ∀ x x' → Dec (Path (Bool × ℕ) x (not (fst x') , snd x'))
IsRedex? _ _ = discreteΣ 𝟚._≟_ (λ _ → discreteℕ) _ _

ℕDeas→ℕInvol : ∀ {p} → Pℕ.IsPathTrmDeas p → Pℕ.IsPathTrmInvol _ _

consInvolℕ : ∀ {p} → Pℕ.IsPathTrmDeas p → (Bool × ℕ) → Pℕ.IsPathTrmInvol _ _ 
consInvolℕ PT.nilTrmDeasRefl x = PT.consTrmInvol PT.nilTrmInvolRefl x
consInvolℕ q'@(PT.consTrmDeas x q) x₁ =
    decRec (λ _ → Pℕ.involTrmInvol (ℕDeas→ℕInvol x) q)
              (λ _ → Pℕ.consTrmInvol (ℕDeas→ℕInvol q') x₁) (IsRedex? q x₁ )



ℕDeas→ℕInvol PT.nilTrmDeasRefl = PT.nilTrmInvolRefl
ℕDeas→ℕInvol (PT.consTrmDeas p' q') = consInvolℕ p' q'
-- ℕDeas'→ℕInvol x

module tryPathE where

 try≡ : ℕ → R.Term → R.TC (Σ _ PTrm.IsPathTrm)


 tryRefl : R.Term → R.TC (Σ _ PTrm.IsPathTrm)
 tryRefl t = do
       _ ← R.noConstraints $ R.checkType
             (R.con (quote reflCase) [])
             (R.def (quote PathCase) ([ varg t ]))
       R.returnTC (_ , PTrm.isReflTrm)

 tryComp : ℕ → R.Term → R.TC (Σ _ PTrm.IsPathTrm)
 tryComp zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryComp (suc k) t = do
       tm ← R.noConstraints $ R.checkType
             (R.con (quote compCase) (R.unknown v∷ R.unknown v∷ [ varg R.unknown ]))
             (R.def (quote PathCase) ([ varg t ]))
       (t1 , t2 , t3) ← h tm
       (_ , t1') ← try≡ k t1
       (_ , t2') ← try≡ k t2
       (_ , t3') ← try≡ k t3
       R.returnTC (_ , PTrm.isCompTrm t1' t2' t3')

  where

  h : R.Term → R.TC (R.Term × R.Term × R.Term)
  h (R.con (quote compCase) l) = match3Vargs l
  h _ = R.typeError [ (R.strErr "tryCompFail-h") ]


 atom : R.Term → R.TC (Σ _ PTrm.IsPathTrm)
 atom x = R.returnTC (_ , PTrm.isAtomTrm x)


 try≡ zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 try≡ (suc k) t =
   R.catchTC
    (tryRefl t)
    (R.catchTC (tryComp k t) (atom t))

lamWrap' : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
lamWrap' p i = p i


lamWrap : R.Term → R.Term
lamWrap t = R.def (quote lamWrap') (t v∷ [])

unLam : R.Term → R.TC R.Term
unLam (R.lam _ (R.abs _ t)) = R.returnTC t
unLam t = R.typeError ((R.strErr "unLam-fail") ∷ [ R.termErr t  ])

appendIfUniqe : R.Term → List R.Term →   R.TC (List R.Term)
appendIfUniqe x [] = R.returnTC [ x ]
appendIfUniqe x xs@(x₁ ∷ xs') = do
 x' ← R.checkType x (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>=
          λ u → R.catchTC (unLam u) (R.typeError [ R.strErr "aiu x'" ])
 x₁' ← R.checkType x₁ (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 sym[x₁'] ← R.checkType (R.def (quote sym) [ varg x₁ ]) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 R.catchTC (R.extendContext "i" (varg (R.def (quote I) [])) $
                ( R.noConstraints $ R.unify (x') (x₁') >> R.returnTC xs))
    (
      R.catchTC
     (R.extendContext "i" (varg (R.def (quote I) [])) $
                ( R.noConstraints $ R.unify (x') sym[x₁'] >> R.returnTC xs))
        (appendIfUniqe x xs' >>= (R.returnTC ∘ (x₁ ∷_))  )
        )

comparePathTerms : R.Term → R.Term → R.TC (Maybe Bool)
comparePathTerms x x₁ = do
 x' ← R.withNormalisation true $ R.checkType (lamWrap x) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>=
         λ u → R.catchTC (unLam u) (R.typeError [ R.strErr "cpt x'" ])
 x₁' ← R.withNormalisation true $ R.checkType (lamWrap x₁) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>=
         λ u → R.catchTC (unLam u) (R.typeError (R.strErr "cpt x₁'" ∷ R.termErr x ∷ [ R.termErr x₁ ]))
 sym[x₁'] ← R.checkType (R.def (quote sym) [ varg x₁ ]) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 R.catchTC (R.extendContext "i" (varg (R.def (quote I) [])) $
                ( R.noConstraints $ R.unify (x') (x₁') >> R.returnTC (just true)))
    (
      R.catchTC
     (R.extendContext "i" (varg (R.def (quote I) [])) $
                ( R.noConstraints $ R.unify (x') sym[x₁'] >> R.returnTC (just false)))
        (R.returnTC nothing)
        )

concatUniq : List R.Term → List R.Term →  R.TC (List R.Term)
concatUniq [] = R.returnTC
concatUniq (x ∷ x₂) x₁  = appendIfUniqe x x₁ >>= concatUniq x₂

indexOfAlways : R.Term → List R.Term →   R.TC ((List R.Term) × (Bool × ℕ))
indexOfAlways t [] = R.returnTC ([ t ] , (true , 0))
indexOfAlways t xs@(x ∷ xs') =
  comparePathTerms t x >>=
   Mb.rec ((λ (l , (b , k) ) → (x ∷ l) , (b , (suc k))) <$> indexOfAlways t xs' )
          (λ b → R.returnTC (xs , (b , 0)))

unMapAtoms : List R.Term → ∀ {p} → PTrm.IsPathTrm p →
     (R.TC ((List R.Term) × (Σ _ Pℕ.IsPathTrm)))
unMapAtoms l PT.isReflTrm = R.returnTC (l , _ , Pℕ.isReflTrm)
unMapAtoms l (PT.isAtomTrm x) =
  do (l' , y) ← indexOfAlways x l
     R.returnTC (l' , _ , Pℕ.isAtomTrm y)
unMapAtoms l (PT.isCompTrm e e₁ e₂) =
  do (l' , _ , e') ← unMapAtoms l e
     (l'' , _ , e₁') ← unMapAtoms l' e₁
     (l''' , _ , e₂') ← unMapAtoms l'' e₂
     (R.returnTC (l''' , _ , Pℕ.isCompTrm e' e₁' e₂'))


unquotePathTrm : ∀ {p} → PTrm.IsPathTrm p → R.Term
unquotePathTrm PT.isReflTrm = R.con (quote (isReflTrm)) []
unquotePathTrm (PT.isAtomTrm p) = R.con (quote isAtomTrm) (p v∷ [])
unquotePathTrm (PT.isCompTrm x x₁ x₂) = 
 let x' = unquotePathTrm x
     x₁' = unquotePathTrm x₁
     x₂' = unquotePathTrm x₂
 in R.con (quote isCompTrm) (x' v∷ x₁' v∷ x₂' v∷ [])

module _ (l : List R.Term) where
  lk : (Bool × ℕ) → R.Term
  lk (b , n) = if b then z else (R.def (quote sym) (z v∷ [])) 
    where
    z = lookupWithDefault R.unknown l n



  mkTrmsInvol' :  ∀ {p} → ℕ → Pℕ.IsPathTrmDeas p → List (Pℕ.IsPathTrmInvol _ _)
  mkTrmsInvol' zero _ = []
  mkTrmsInvol' (suc k) u =
    let pi = ℕDeas→ℕInvol u
    in if (Pℕ.hasRedexes pi) then (pi ∷ mkTrmsInvol' k (snd (Pℕ.Invol→Deas↓ pi))) else []

  mkTrmsInvol* : ∀ {p} → Pℕ.IsPathTrmDeas p → List (Pℕ.IsPathTrmInvol _ _)
  mkTrmsInvol* x = mkTrmsInvol' (Pℕ.depthIsPathTrmDeas x) x

  unquoteTrmInvol : PTrm.IsPathTrmInvol tt tt → R.Term
  -- unquoteTrmInvol (PT.nilTrmInvol p) = R.con (quote nilTrmInvol) (p v∷ [])
  -- unquoteTrmInvol (PT.nilInvolTrmInvol p) = R.con (quote nilInvolTrmInvol) (p v∷ [])
  unquoteTrmInvol PT.nilTrmInvolRefl = R.con (quote nilTrmInvolRefl) []
  unquoteTrmInvol (PT.consTrmInvol x q) =
    R.con (quote consTrmInvol) (unquoteTrmInvol x v∷ q v∷ [])
  unquoteTrmInvol (PT.involTrmInvol x q) =
   R.con (quote involTrmInvol) (unquoteTrmInvol x v∷ q v∷ [])

  mkTrmsInvol :  ∀ {p} → Pℕ.IsPathTrmDeas p → List (R.Term)
  mkTrmsInvol x = Li.map ((λ y → R.def (quote ⟦_⟧ti≡) (y v∷ []))
    ∘ unquoteTrmInvol ∘ mapPTG lk) $ mkTrmsInvol* x

  foldPathCompTerm : List R.Term → R.Term
  foldPathCompTerm [] = R.def (quote refl) []
  foldPathCompTerm (x ∷ []) = x
  foldPathCompTerm (x ∷ xs@(_ ∷ _)) = R.def (quote _∙_) (x v∷ foldPathCompTerm xs v∷ [])
  
  mkTrmInvol :  ∀ {p} → Pℕ.IsPathTrmDeas p → (List (Pℕ.IsPathTrmInvol _ _) × R.Term)
  mkTrmInvol x = ( mkTrmsInvol* x) , foldPathCompTerm (mkTrmsInvol x) 


groupoidSolverTerm : Bool → R.Term → R.TC (R.Term × List R.ErrorPart)
groupoidSolverTerm debugFlag  hole = do
 
 (t0 , t1) ← R.inferType hole >>= wait-for-type >>= (get-boundary ) >>= Mb.rec
     (R.typeError [ R.strErr "unable to get boundary" ])
     (λ x → R.returnTC x)
 
 (r0 , r0') ← tryPathE.try≡ 100 t0
 (r1 , r1') ← tryPathE.try≡ 100 t1
 

 (aL' , (_ , e0)) ← unMapAtoms [] r0'
 (aL , (_ , e1)) ← unMapAtoms aL' r1'
 let (_ , e0deas) =  (Pℕ.⟦ e0 ⟧da∘r)
 let (_ , e1deas) =  (Pℕ.⟦ e1 ⟧da∘r)  

 let dbgInfo =   (R.strErr "LHS: ") ∷ (R.termErr $ t0)
               ∷ (R.strErr "\n")
               ∷ (R.strErr "RHS: ") ∷ (R.termErr $ t1)
               ∷ (R.strErr "\n")
               ∷ (R.strErr "LHS: ") ∷ (R.strErr $ PℕS.showIPT (e0))
               ∷ (R.strErr "\n")
               ∷ (R.strErr "RHS: ") ∷ (R.strErr $ PℕS.showIPT (e1))
               ∷ (R.strErr "\n")
               ∷ (R.strErr "LHS: ") ∷ (R.strErr $ PℕS.showIPTD (e0deas))
               ∷ (R.strErr "\n")
               ∷ (R.strErr "RHS: ") ∷ (R.strErr $ PℕS.showIPTD (e1deas))
               ∷ (R.strErr "\n")
               ∷ (R.strErr "LHS: ") ∷ (R.strErr $ PℕS.showIPTI (ℕDeas→ℕInvol e0deas))
               ∷ (R.strErr "\n")
               ∷ (R.strErr "RHS: ") ∷ (R.strErr $ PℕS.showIPTI (ℕDeas→ℕInvol e1deas))
               -- ∷ (R.strErr "\n") ∷ (R.termErr ((mkTrmInvol aL e0deas)))             
               ∷ (R.strErr "\n")
               ∷ ((niceAtomList 0 aL))
 -- R.typeError dbgInfo

 let (_ , iP0) = mkTrmInvol aL e0deas
     (eqs1 , iP1) = mkTrmInvol aL e1deas

 let dbgInfo = dbgInfo ++ ((R.strErr "\n") ∷  niceEqsList eqs1)


 let pa0 = R.def (quote _∙_)
              (R.def (quote daSingl) ((unquotePathTrm r0') v∷ [])
               v∷ iP0 v∷ [] )
     pa1 = R.def (quote _∙_)
              (R.def (quote daSingl) ((unquotePathTrm r1') v∷ [])
               v∷ iP1 v∷ [] )
 let final =  (R.def (quote _∙∙_∙∙_)
            (pa0
             v∷ R.def (quote refl) []
             v∷ R.def (quote sym) (pa1 v∷ []) v∷ [] ))

 -- finalTy0 ← R.inferType pa0 >>= R.normalise
 -- finalTy1 ← R.inferType pa1 >>= R.normalise
 -- finalTy ← R.inferType final
 -- let dbgInfo = dbgInfo
 --       ++ ((R.strErr "\n fTy0 : ") ∷ R.termErr finalTy0 ∷ [])
 --       ++ ((R.strErr "\n fTy1 : ") ∷ R.termErr finalTy1 ∷ [])
 --       -- ++ ((R.strErr "\n fTy : ") ∷ R.termErr finalTy ∷ [])
 -- -- R.typeError dbgInfo
 R.returnTC (final , dbgInfo)  

 where
 niceAtomList : ℕ → List (R.Term) → List R.ErrorPart
 niceAtomList _ [] = []
 niceAtomList k (x ∷ xs) =
   (R.strErr (mkNiceVar k  <> " = ") ∷ R.termErr x ∷ [ R.strErr "\n" ]) ++ niceAtomList (suc k) xs

 niceEq : ℕ → Pℕ.IsPathTrmInvol _ _ → List R.ErrorPart
 niceEq k x = R.strErr (primShowNat k <> " : ")
            ∷ R.strErr (PℕS.showIPTI x)
            ∷ [ R.strErr "\n" ]
 
 niceEqsList' : ℕ → List (Pℕ.IsPathTrmInvol _ _) → List R.ErrorPart
 niceEqsList' k [] = []
 niceEqsList' k (x ∷ xs) =
  niceEq k x ++ niceEqsList' (suc k) xs 

 niceEqsList = niceEqsList' 0

groupoidSolverMain : Bool → R.Term → R.TC Unit
groupoidSolverMain debugFlag  hole = do
  ty ← R.withNormalisation true $  R.inferType hole >>= wait-for-type
  hole' ← R.withNormalisation true $ R.checkType hole ty
  (solution , msg) ← groupoidSolverTerm debugFlag hole'
  R.catchTC
   (R.unify hole solution)
   (R.typeError msg)

squareSolverMain : Bool → R.Term → R.TC Unit
squareSolverMain debugFlag  hole = do
  ty ← R.inferType hole >>= wait-for-type
  hole' ← R.checkType (R.def (quote compPathR→PathP∙∙) (R.unknown v∷ [])) ty >>= extractMeta
  
  -- R.typeError [ R.termErr tm' ] 
  (solution , msg) ← groupoidSolverTerm debugFlag  hole'
  R.catchTC
   (R.unify hole' solution)
   (R.typeError msg)

  R.catchTC
   (R.unify hole (R.def (quote compPathR→PathP∙∙) (hole' v∷ [])))
   (R.typeError [ R.strErr "xxx" ] )
 where
  extractMeta : R.Term → R.TC R.Term
  extractMeta (R.def _ tl) = matchVarg tl
  extractMeta t =
   R.typeError (R.strErr "extractMetaFail :" ∷ [ R.termErr t ])
  
macro
 solveGroupoidDebug : R.Term → R.TC Unit
 solveGroupoidDebug = groupoidSolverMain true

 solveSquareDebug : R.Term → R.TC Unit
 solveSquareDebug = squareSolverMain false

 solveGroupoid : R.Term → R.TC Unit
 solveGroupoid = groupoidSolverMain true

 solveSquare : R.Term → R.TC Unit
 solveSquare = squareSolverMain false



module Examples (A : Type ℓ) (x y z w : A) (p p' : x ≡ y) (q : y ≡ z) (q' : z ≡ y) (r : w ≡ z) where

  pA pB pC : x ≡ w
  pA = (p ∙∙ refl ∙∙ q) ∙ sym r
  pB = (p ∙ (q ∙ sym (sym r ∙  r) ∙ sym q) ∙∙ q ∙∙ refl) ∙∙ sym r ∙∙ refl
  pC = refl ∙∙ p' ∙ q ∙ sym q ∙ sym p' ∙∙ p ∙∙ q ∙∙ sym q ∙ q ∙ sym r 

  pA=pB : pA ≡ pB
  pA=pB = solveGroupoidDebug

  pB=pC : pB ≡ pC
  pB=pC = solveGroupoidDebug

  pA=pC : pA ≡ pC
  pA=pC = solveGroupoidDebug

  pA=pB∙pB=pC-≡-pA=pC : pA=pB ∙ pB=pC ≡ pA=pC
  pA=pB∙pB=pC-≡-pA=pC = midCancel _ _ _

  
  sqTest : Square p (sym r ∙ refl) (p ∙ q) (q ∙ sym r)
  sqTest = solveSquareDebug    

module _ {A : Type ℓ} where
 compSq' :   {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁} {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
             {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} {a₀₀' a₀₁' : A} {a₀₋' : a₀₀' ≡ a₀₁'}
             {a₁₀' a₁₁' : A} {a₁₋' : a₁₀' ≡ a₁₁'} {a₋₀' : a₀₀' ≡ a₁₀'} {a₋₁' : a₀₁' ≡ a₁₁'}
         → Square a₀₋ a₁₋ a₋₀ a₋₁
         → (t : a₀₀ ≡ a₀₀')
         → (a₁₋ ⁻¹ ∙∙ a₋₀ ⁻¹ ∙∙ t ∙∙ a₋₀' ∙∙ a₁₋') ≡ (a₋₁ ⁻¹ ∙∙ a₀₋ ⁻¹ ∙∙ t ∙∙ a₀₋' ∙∙ a₋₁')
         → Square a₀₋' a₁₋' a₋₀' a₋₁'
 compSq' {a₀₋' = a₀₋'} {a₁₋' = a₁₋'} {a₋₀' = a₋₀'}  {a₋₁' =  a₋₁'} s t c i j =
  hcomp
    (λ k → λ {  (i = i0) → doubleCompPath-filler (sym (s i0)) t a₀₋' j k
              ; (i = i1) → doubleCompPath-filler (sym (s  i1))
                             ((λ i → s (~ i) i0) ∙∙ t ∙∙  a₋₀')  a₁₋' j k
              ; (j = i0) → doubleCompPath-filler (λ i → s (~ i) i0) t a₋₀' i k
              ; (j = i1) → compPathR→PathP∙∙ c (~ i) k
              }) (s i j)

open import Cubical.Algebra.Group



module EM₁-Example (G : Group ℓ) (a b c : fst G) where
  open GroupStr (snd G)

  data EM₁ : Type ℓ where
      embase : EM₁
      emloop : ⟨ G ⟩ → embase ≡ embase
      emcomp : (g h : ⟨ G ⟩ ) → PathP (λ j → embase ≡ emloop h j) (emloop g) (emloop (g · h))

  double-emcomp :  Square {A = EM₁}
                    (emloop b) (emloop ((a · b) · c))
                    (sym (emloop a)) (emloop c)

  double-emcomp =
    compSq'
      (emcomp a b ∙v emcomp (a · b) c)
      (emloop a)
      solveGroupoidDebug

