{-# OPTIONS --type-in-type #-}  -- yes, I will let you cheat in this exercise
{-# OPTIONS --allow-unsolved-metas #-}  -- allows import, unfinished

------------------------------------------------------------------------------
-- Dependencies
------------------------------------------------------------------------------

open import CS410-Prelude
open import CS410-Categories
open import Ex1

data oneArrow : One -> One -> Set where
  id1 : oneArrow <> <>

onei : {o : One} -> oneArrow o o
onei {<>} = id1

onecomp : ∀ {o o' o'' : One} → oneArrow o o' → oneArrow o' o'' → oneArrow o o''
onecomp id1 id1 = id1

oneleft : ∀ {S T} (f : oneArrow S T) → onecomp onei f == f
oneleft id1 = refl id1

oneright : ∀ {S T} (f : oneArrow S T) → onecomp f onei == f
oneright id1 = refl id1

oneacc : ∀ {Q R S T} (f : oneArrow Q R) (g : oneArrow R S) (h : oneArrow S T) → onecomp (onecomp f g) h == onecomp f (onecomp g h)
oneacc id1 id1 id1 = refl id1

OneCat : Category
Category.Obj OneCat = One
Category._~>_ OneCat = oneArrow
Category.id~> OneCat = onei
Category._>~>_ OneCat = onecomp
Category.law-id~>>~> OneCat = oneleft
Category.law->~>id~> OneCat = oneright
Category.law->~>>~> OneCat = oneacc

data twoArrow : Two -> Two -> Set where
  idt : twoArrow tt tt
  idf : twoArrow ff ff
  tf : twoArrow tt ff

twoId : ∀ {T} → twoArrow T T
twoId {tt} = idt
twoId {ff} = idf

twoTrans : ∀ {R S T : Two} → twoArrow R S → twoArrow S T → twoArrow R T
twoTrans idt idt = idt
twoTrans idt tf = tf
twoTrans idf idf = idf
twoTrans tf idf = tf

twoLeft : ∀ {S T : Two} (f : twoArrow S T) → twoTrans twoId f == f
twoLeft idt = refl idt
twoLeft idf = refl idf
twoLeft tf = refl tf

twoRight : ∀ {S T : Two} (f : twoArrow S T) → twoTrans f twoId == f
twoRight idt = refl idt
twoRight idf = refl idf
twoRight tf = refl tf

twoAssoc :  ∀ {Q R S T : Two} (f : twoArrow Q R) (g : twoArrow R S) (h : twoArrow S T) → twoTrans (twoTrans f g) h == twoTrans f (twoTrans g h)
twoAssoc idt idt idt = refl idt
twoAssoc idt idt tf = refl tf
twoAssoc idt tf idf = refl tf
twoAssoc idf idf idf = refl idf
twoAssoc tf idf idf = refl tf

TwoCat : Category
TwoCat = record
  { Obj          = Two
  ; _~>_         = twoArrow
  -- Now, assemble the rest of the components.
  ; id~>         = twoId
  ; _>~>_        = twoTrans
  ; law-id~>>~>  = twoLeft
  ; law->~>id~>  = twoRight
  ; law->~>>~>   = twoAssoc
  }

lp : {A B : Set} {a a1 : A} {b b1 : B} → a == a1 → b == b1 → pair a b == pair a1 b1
lp {A} {B} {a} {b = b} (refl _) (refl _) = refl (pair a b)

ProdCat : Category → Category → Category
ProdCat record { Obj = o ; _~>_ = a ; id~> = i ; _>~>_ = c ; law-id~>>~> = l1 ; law->~>id~> = l2 ; law->~>>~> = l3 } record { Obj = o1 ; _~>_ = a1 ; id~> = i1 ; _>~>_ = c1 ; law-id~>>~> = l21 ; law->~>id~> = l22 ; law->~>>~> = l23 } =
  record
    { Obj          = o × o1
    ; _~>_         = λ x y → help x y
    ; id~>         = help1
    ; _>~>_        = help2
    ; law-id~>>~>  = help3
    ; law->~>id~>  = help4
    ; law->~>>~>   = help5
  }
  where
    help : (x y : o × o1) → Set
    help (pair x x1) (pair y y1) = (a x y) × (a1 x1 y1)
    help1 : {T : o × o1} → help T T
    help1 {pair x y} = pair i i1
    help2 : {R S T : o × o1} → help R S → help S T → help R T
    help2 {pair r1 r2} {pair s1 s2} {pair t1 t2} (pair x x1) (pair y y1) = pair (c x y) (c1 x1 y1)
    help3 : {S T : o × o1} (f : help S T) → help2 help1 f == f
    help3 {pair s s1} {pair t t1} (pair x y) = lp (l1 x) (l21 y)
    help4 : {S T : o × o1} (f : help S T) → help2 f help1 == f
    help4 {pair s s1} {pair t t1} (pair x y) = lp (l2 x) (l22 y)
    help5 : {Q R S T : o × o1} (f : help Q R) (g : help R S) (h : help S T)
      → help2 (help2 f g) h == help2 f (help2 g h)
    help5 {pair x x₁} {pair x₂ x₃} {pair x₄ x₅} {pair x₆ x₇} (pair x₈ x₉) (pair x₁₀ x₁₁) (pair x₁₂ x₁₃) = lp (l3 x₈ x₁₀ x₁₂) (l23 x₉ x₁₁ x₁₃)



-- injective : Set₁
-- injective = {A B : Set} {x y : A} (f : A → B) → f x == f y → x == y

isinj : (A B : Set) → (A → B) → Set
isinj A B f = (x y : A) → f x == f y → x == y

isinj' : (A B : Set) → (A → B) → Set
isinj' A B f = (x y : A) → (x == y → Zero) → (f x == f y → Zero )

ismon : (A B : Set) → (A → B) → Set
ismon A B f = {C : Set} (g h : C → A) → (f << g) == (f << h) → g == h

inj->mon : (A B : Set) → (f : A → B) → isinj A B f → ismon A B f
inj->mon A B f injf g h p = extensionality (λ x → injf (g x) (h x) (p =$= refl x))

inj->inj' : {A B : Set} → (f : A → B) → isinj A B f → isinj' A B f
inj->inj' {A} {B} f inj a1 a2 np pf = np (inj a1 a2 pf)

mon->inj : (A B : Set) → (f : A → B) →  ismon A B f → isinj A B f 
mon->inj A B f mon a1 a2 p = mon g h (extensionality λ x → p) =$= refl <>
  where
    C : One
    C = <>
    g : One → A
    g x = a1
    h : One → A
    h x = a2

isepi : (A B : Set) → (A → B) → Set
isepi A B f = {C : Set} (g h : B → C) → (_>>_ f g) == (_>>_ f h) → g == h

isiso : (A B : Set) → (A → B) → Set
isiso A B f = Sg (B → A) λ g → ((f << g) == id) × (((g << f) == id)) 

iso->epi : (A B : Set) → (f : A → B) → isiso A B f → isepi A B f 
iso->epi A B f (g , pair gf=i fg=i) h k hfkf = extensionality l3
  where
    l3 : (x : B) → h x == k x 
    l3 b = h b
           =[ cong h (sym (gf=i =$ b)) >=
           h (f (g b))
           =[ hfkf =$ g b >=
           (k (f (g b)))
           =[ cong k (gf=i =$ b ) >=
             k b [QED]

-- using extensionality
-- iso->mon : (B C : Set) → (m : B → C) → isiso B C m → ismon B C m
-- iso->mon B C m (e , pair em=i me=i) {A} x y eq = extensionality l3
--   where
--     l3 : (a : A) → x a == y a 
--     l3 a = x a
--            =[ sym (me=i =$ (x a)) >=
--            e (m (x a))
--            =[ cong e (eq =$ a) >=
--            (e (m (y a)))
--            =[ me=i =$ (y a)  >=
--            y a [QED]

-- mirroring awodey's proof
iso->mon : (B C : Set) → (m : B → C) → isiso B C m → ismon B C m
iso->mon B C m (e , pair me=i em=i) {A} x y eq =
           x
           =[ sym (em=i =$''' x) >=
           (e << m) << x 
           =[ cong (λ x → e << x) eq >=
           (e << m) << y
           =[ em=i =$''' y >=
           y [QED]
           -- stupid, ditto =[ subst (λ _ → ((λ z → e (m z)) << y) == ((λ z → z) << y) ) (refl x) (em=i =$''' y) >=

iso->monXepi : (A B : Set) → (f : A → B) → isiso A B f → isepi A B f × ismon A B f
iso->monXepi = λ A B f x → pair (iso->epi A B f x) (iso->mon A B f x) 


module INIT {C : Category} where
  open Category C

  id!l : {S : Obj}  → (id' : S ~> S ) -> ({T : Obj} (f : S ~> T) → (id' >~> f) == f) → id' == id~> {S}
  id!l {S} id's f =
    id's
    =[ sym (law->~>id~> id's)  >=
    id's >~> id~>
    =[ f {S} id~> >=
    id~> [QED]

  id!r : {T : Obj}  → (id' : T ~> T ) -> ({S : Obj} (f : S ~> T) → (f >~> id') == f) → id' == id~> {T}
  id!r {S} id's f =
    id's
    =[ sym (law-id~>>~> id's)  >=
    id~> >~> id's
    =[ f {S} id~> >=
    id~> [QED]

  isisoC : (A B : Obj) → (A ~> B) → Set
  isisoC A B f = Sg (B ~> A) λ g → ((f >~> g) == id~>) × (((g >~> f) == id~>)) 

  idiso : (A : Obj) → isisoC A A (id~> {A} )
  fst (idiso A) = id~>
  snd (idiso A) = pair (law-id~>>~> id~>) (law-id~>>~> id~>)

  initial : Obj → Set
  initial z = (X : Obj) → Sg (z ~> X) λ f → (f' : (z ~> X)) → (f == f')

  initial' : Obj → ((X : Obj) → Set)
  initial' z X =  Sg (z ~> X) λ f → (f' : (z ~> X)) → (f == f')

  -- cleaner, but less natural
  initialId' : (A : Obj) → initial' A A → (i : A ~> A) → i == id~> {A}
  initialId' A (i' , ui') i = i
                              =[ sym (ui' i) >=
                              i'
                              =[ ui' id~> >=
                              id~> [QED]

  initialId : (A : Obj) → initial A → (i : A ~> A) → i == id~> {A}
  initialId A x i = i
                    =[ sym (sxA i) >=
                    fst (x A)
                    =[ sxA id~> >=
                    id~> [QED]
    where
      xA : Sg (A ~> A) (λ f → (f' : A ~> A) → f == f')
      xA = x A
      fxA : A ~> A
      fxA = fst xA
      sxA : (f' : A ~> A) → fst (x A) == f'
      sxA = snd xA

  initial! : (z : Obj) (z' : Obj) → initial z → initial z' → Sg  (z ~> z') λ u → isisoC z z' u -- × ((u' : z ~> z') → u == u') 
  initial!  z z' ui vi = fuv , fvu , pair (initialId z ui (fst (ui z') >~> fst (vi z))) (initialId z' vi (fst (vi z) >~> fst (ui z')))
    where
      uv : Sg (z ~> z') (λ f → (f' : z ~> z') → f == f')
      uv = ui z'
      fuv : z ~> z'
      fuv = fst uv
      suv : (f' : z ~> z') → fst (ui z') == f'
      suv = snd uv
      vu : Sg (z' ~> z) (λ f → (f' : z' ~> z) → f == f')
      vu = vi z
      fvu : z' ~> z
      fvu = fst vu
      svu : (f' : z' ~> z) → fst (vi z) == f'
      svu = snd vu


  final : Obj → Set
  final o = (X : Obj) → Sg (X ~> o) λ f → (f' : (X ~> o)) → (f == f')

  -- prodDiagram : Obj →  Obj → Obj → Set
  -- prodDiagram P A B = (P ~> A) × (P ~> B)

  prodDiagram : Obj → Obj → Set
  prodDiagram A B = Sg Obj λ P → (P ~> A) × (P ~> B)

  prodUMP : {A B : Obj} → prodDiagram A B → Set
  prodUMP {A} {B} (P , pair pa pb) = ((X , pair xa xb) : prodDiagram A B) → Sg (X ~> P) λ u →  (( u >~> pa) == xa) × (( u >~> pb) == xb) × {!()!}

    -- ———— Error —————————————————————————————————————————————————
    -- /home/wmacmil/agda2020/CS410-17/exercises/CatProps.agda:281,39-55
    -- Expected record pattern
    -- when checking the let binding X , pair xa xb = .patternInTele0



  record Product (c : Category) : Set where
    field
      P : Obj
      -- p1p2 : {A B : Obj} → (P ~> A) × (P ~> B)
      -- Pp1p2 : {A B : Obj} → prodDiagram A B
      Pp1p2 : {A B : Obj} → prodDiagram A B
      Pprod : {A B : Obj} → fst (Pp1p2 {A} {B}) == P
      -- ump : {A B X : Obj} → prodDiagram X A B → Sg {!!} {!!} 



    
    

  -- -- initial! : (z : Obj) (z' : Obj) → initial z z' → initial z' z → Sg  (z ~> z') λ u → Sg (z' ~> z) λ v → isisoC z z' u -- × isisoC z' z v
  -- -- initial! z z' (u , u!) (v , v!) = u , v , {!!}

  -- initial! : (z : Obj) (z' : Obj) → initial z z' → initial z' z → Sg  (z ~> z') λ u → isisoC z z' u -- × ((u' : z ~> z') → u == u') 
  -- initial!  z z' (u , u!) (v , v!) = u , v , pair {!!} {!!} -- λ u' → u! u'
  --   where
  --     lt : (u >~> v) == id~>
  --     lt = id!r (u >~> v) {!!}
  --     lu! : {!!}
  --     lu! = u! {!id~> {}!}


-- inj'->inj : {A B : Set} → (f : A → B) → isinj' A B f → isinj A B f
-- inj'->inj f inj' a1 a2 pf = {!!}

-- inj'->inj : {A B : Set} → (f : A → B) → isinj' A B f → isinj A B f → Zero
-- inj'->inj f inj' a1 = {!!}

module MONO {C : Category} where
  open Category C

  ismono : (A B : Obj) → ( _~>_ A B) → Set
  ismono A B f = {C : Obj} (g h : _~>_ C A) → (_>~>_ g f) == (_>~>_ h f) → g == h
  
  -- isepi : (A B : Obj) → ( _~>_ A B) → Set
  -- isepi A B f = {C : Obj} (g h : _~>_ B C) → (_>~>_ f g) == (_>~>_ f h) → g == h

  -- isiso : (A B : Obj) → ( _~>_ A B) → Set

module MSet where
  open MONO {SET}

  a : Category
  a = SET

  inj->mono : (A B : Category.Obj a) → (f : Category._~>_ a A B) → isinj A B f → ismono A B f
  inj->mono A B f injf g h p = extensionality (λ x → injf (g x) (h x) (p =$= refl x))

  -- doesn't seem proveable constructively
  -- inj'->mono : (A B : Category.Obj a) → (f : Category._~>_ a A B) → isinj' A B f → ismono A B f
  -- inj'->mono A B f injf' g h x = {!!}

  mono->inj : (A B : Category.Obj a) → (f : Category._~>_ a A B) →  ismono A B f → isinj A B f 
  mono->inj A B f mon a1 a2 p = mon g h (extensionality λ x → p) =$= refl <>
    where
      C : One
      C = <>
      g : One → A
      g x = a1
      h : One → A
      h x = a2
      ll : (x : One) → f (g x) == f (h x)
      ll x = p

  mono->inj' : (A B : Category.Obj a) → (f : Category._~>_ a A B) →  ismono A B f → isinj' A B f 
  -- mono->inj A B f fmon a1 a2 p pf = p (l5 llll)
  mono->inj' A B f fmon a1 a2 p pf = p ((fmon g h (extensionality λ x → pf)) =$= refl <>)
    where
      C : One
      C = <>
      g : One → A
      g x = a1
      h : One → A
      h x = a2
      ll : (x : One) → f (g x) == f (h x)
      ll <> = pf
      lll : Category._>~>_ a g f == Category._>~>_ a h f 
      lll = extensionality ll
      llll : (λ x → a1) == (λ x → a2)
      llll = fmon g h lll
      l5 : (λ  (x : One) → a1) == (λ (x : One) → a2) → a1 == a2
      l5 x = x =$= refl <>
      
