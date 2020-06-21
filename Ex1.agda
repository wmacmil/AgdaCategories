{-# OPTIONS --allow-unsolved-metas #-}


------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CS410 2017/18 Exercise 1  VECTORS AND FRIENDS (worth 25%)
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- NOTE (19/9/17) This file is currently incomplete: more will arrive on
-- GitHub.

-- MARK SCHEME (transcribed from paper): the (m) numbers add up to slightly
-- more than 25, so should be taken as the maximum number of marks losable on
-- the exercise. In fact, I did mark it negatively, but mostly because it was
-- done so well (with Agda's help) that it was easier to find the errors.


------------------------------------------------------------------------------
-- Dependencies
------------------------------------------------------------------------------

open import CS410-Prelude
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)

------------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------------

data Vec (X : Set) : Nat -> Set where  -- like lists, but length-indexed
  []   :                              Vec X zero
  _,-_ : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
infixr 4 _,-_   -- the "cons" operator associates to the right

-- I like to use the asymmetric ,- to remind myself that the element is to
-- the left and the rest of the list is to the right.

-- Vectors are useful when there are important length-related safety
-- properties.


------------------------------------------------------------------------------
-- Heads and Tails
------------------------------------------------------------------------------

-- We can rule out nasty head and tail errors by insisting on nonemptiness!

--??--1.1-(2)-----------------------------------------------------------------

vHead : {X : Set}{n : Nat} -> Vec X (suc n) -> X
vHead (x ,- xs) = x

vTail : {X : Set}{n : Nat} -> Vec X (suc n) -> Vec X n
vTail (x ,- xs) = xs

vHeadTailFact :  {X : Set}{n : Nat}(xs : Vec X (suc n)) ->
                 (vHead xs ,- vTail xs) == xs
vHeadTailFact (x ,- xs) = refl (x ,- xs)

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Concatenation and its Inverse
------------------------------------------------------------------------------

--??--1.2-(2)-----------------------------------------------------------------

_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n)
[] +V xs = xs
(x ,- xs) +V [] = x ,- xs +V []
(x ,- xs) +V x₁ ,- ys = x ,- xs +V x₁ ,- ys
-- (x ,- xs) +V x₁ ,- ys = {!x ,- xs +V x₁ ,- ys!}

-- (x ,- xs) +V s = {!!}
-- [] +V [] = []
-- [] +V x ,- ys = x ,- ys
-- (x ,- xs) +V [] = x ,- xs +V []
infixr 4 _+V_

vChop : {X : Set}(m : Nat){n : Nat} -> Vec X (m +N n) -> Vec X m * Vec X n
vChop zero (x ,- xs) = [] , x ,- xs
vChop zero [] = [] , []
vChop {X }  (suc m) {n} (x ,- xs) = (x ,- fst recCall) , snd recCall 
  where
    recCall : Sg (Vec X m) (λ _ → Vec X n)
    recCall = vChop m xs

lemma11 : {X : Set} (n : Nat) (xs : Vec X n) → fst (vChop n (xs +V [])) == xs
lemma11 zero [] = refl []
lemma11 (suc n) (x ,- xs) rewrite lemma11 n xs = refl (x ,- xs)

lemma1 : {X : Set} (n n' : Nat) (xs : Vec X n) (ys : Vec X n' )→ fst (vChop n (xs +V ys)) == xs
lemma1 zero zero [] [] = refl []
lemma1 zero (suc n') [] (x ,- ys) = refl []
lemma1 (suc n) zero (x ,- xs) [] rewrite lemma11 n xs = refl (x ,- xs)
lemma1 (suc n) (suc n') (x ,- xs) (y ,- ys) rewrite lemma1 n (suc n') xs (y ,- ys) = refl (x ,- xs)

lemma22 : {X : Set} (n : Nat) (xs : Vec X n) → snd (vChop n (xs +V [])) == [] 
lemma22 zero [] = refl []
lemma22 (suc n) (x ,- xs) = lemma22 n xs

lemma2 : {X : Set} (n n' : Nat) (xs : Vec X n) (ys : Vec X n' )→ snd (vChop n (xs +V ys)) == ys 
lemma2 n zero xs [] rewrite lemma22 n xs = refl []
lemma2 .0 (suc n') [] (y ,- ys) = refl (y ,- ys)
lemma2 (suc n) (suc n') (x ,- xs) (y ,- ys) rewrite lemma2 n (suc n') xs (y ,- ys) = refl (y ,- ys)

vChopAppendFact : {X : Set}{m n : Nat}(xs : Vec X m)(ys : Vec X n) ->
                  vChop m (xs +V ys) == (xs , ys)
vChopAppendFact [] [] = refl ([] , [])
vChopAppendFact [] (x ,- ys) = refl ([] , x ,- ys)
vChopAppendFact {X} {suc m} {n} (x ,- xs) [] rewrite lemma11 m xs | lemma22 m xs = refl ((x ,- xs) , [])
vChopAppendFact {m = suc m} {n = suc n} (x ,- xs) (y ,- ys) rewrite lemma1 m (suc n) xs (y ,- ys) | lemma2 m (suc n) xs (y ,- ys) = refl ((x ,- xs) , y ,- ys)

vChopAppendFact' : {X : Set}(m n : Nat)(xs : Vec X m)(ys : Vec X n) ->
                  vChop m (xs +V ys) == (xs , ys)
vChopAppendFact' zero zero [] [] = refl ([] , [])
vChopAppendFact' zero (suc n) [] (x ,- ys) = refl ([] , x ,- ys)
vChopAppendFact' (suc m) zero (x ,- xs) [] rewrite lemma11 m xs | lemma22 m xs = refl ((x ,- xs) , [])
vChopAppendFact' (suc m) (suc n) (x ,- xs) (y ,- ys) rewrite lemma1 m (suc n) xs (y ,- ys) | lemma2 m (suc n) xs (y ,- ys) = refl ((x ,- xs) , y ,- ys)


--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Map, take I
------------------------------------------------------------------------------

-- Implement the higher-order function that takes an operation on
-- elements and does it to each element of a vector. Use recursion
-- on the vector.
-- Note that the type tells you the size remains the same.

-- Show that if the elementwise function "does nothing", neither does
-- its vMap. "map of identity is identity"

-- Show that two vMaps in a row can be collapsed to just one, or
-- "composition of maps is map of compositions"

--??--1.3-(2)-----------------------------------------------------------------

vMap : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vMap f [] = []
vMap f (x ,- xs) = f x ,- vMap f xs


-- _=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
-- f == f' -> x == x' -> f x == f' x'

vMapIdFact : {X : Set}{f : X -> X}(feq : (x : X) -> f x == x) ->
             {n : Nat}(xs : Vec X n) -> vMap f xs == xs
vMapIdFact feq [] = refl []
vMapIdFact {f = f} feq (x ,- xs) = (f x ,- vMap f xs) =[ (cong (λ x₁ → x₁ ,- vMap f xs ) (feq x)) >= cong (λ x₁ → x ,- x₁) (vMapIdFact feq xs)

vMapCpFact : {X Y Z : Set}{f : Y -> Z}{g : X -> Y}{h : X -> Z}
               (heq : (x : X) -> f (g x) == h x) ->
             {n : Nat}(xs : Vec X n) ->
               vMap f (vMap g xs) == vMap h xs
vMapCpFact heq [] = refl []
vMapCpFact {h = h} heq (x ,- xs) rewrite heq x = cong (λ x₁ → h x ,- x₁) (vMapCpFact heq xs)


--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- vMap and +V
------------------------------------------------------------------------------

-- Show that if you've got two vectors of Xs and a function from X to Y,
-- and you want to concatenate and map, it doesn't matter which you do
-- first.

--??--1.4-(1)-----------------------------------------------------------------

-- vAssoc : ∀ {X} (n n' : Nat) (x : X) (xs : Vec X n) (xs' : Vec X n') → ((x ,- xs) +V xs') == (x ,- (xs +V xs'))
vAssoc : ∀ {X} (n n' : Nat) (x : X) (xs : Vec X n) (xs' : Vec X n') → ((x ,- xs) +V xs') == (x ,- (xs +V xs'))
vAssoc zero .0 x [] [] = refl (x ,- [])
vAssoc zero .(suc _) x [] (x₁ ,- xs') = refl (x ,- x₁ ,- xs')
vAssoc (suc n) .0 x (x1 ,- xs) [] = refl (x ,- x1 ,- xs +V [])
vAssoc (suc n) .(suc _) x (x1 ,- xs) (x₁ ,- xs') = refl (x ,- x1 ,- xs +V x₁ ,- xs')
-- vAssoc (suc n) n' x (x1 ,- xs) xs' = cong (λ x₁ → {!(x ,- x₁)!}) (vAssoc n n' x1 xs xs')
-- rewrite (vAssoc n n' x1 xs xs') = {!xs'!}
-- vAssoc n n' x [] xs' = {!!}
-- vAssoc n n' x (x₁ ,- xs) xs' = {!cong ? (vAssoc x₁ xs xs')!}

vMap+VFact : {X Y : Set}(f : X -> Y) ->
             {m n : Nat}(xs : Vec X m)(xs' : Vec X n) ->
             vMap f (xs +V xs') == (vMap f xs +V vMap f xs')
vMap+VFact f [] xs' = refl (vMap f xs')
-- vMap+VFact {m = m} (n = n) f (x ,- xs) xs' rewrite vAssoc m n x xs xs' = {!!}
vMap+VFact f {m = (suc m)} {n = n} (x ,- xs) xs' rewrite vAssoc m n x xs xs' | vMap+VFact f xs xs' | vAssoc m n (f x) (vMap f xs) (vMap f xs') = refl (f x ,- vMap f xs +V vMap f xs')

--??--------------------------------------------------------------------------

-- Think about what you could prove, relating vMap with vHead, vTail, vChop...
-- Now google "Philip Wadler" "Theorems for Free"


------------------------------------------------------------------------------
-- Applicative Structure (giving mapping and zipping cheaply)
------------------------------------------------------------------------------

--??--1.5-(2)-----------------------------------------------------------------

-- HINT: you will need to override the default invisibility of n to do this.
vPure : {X : Set} -> X -> {n : Nat} -> Vec X n
vPure x {zero} = []
vPure x {suc n} = x ,- vPure x

_$V_ : {X Y : Set}{n : Nat} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
[] $V [] = []
f ,- fs $V x ,- xs = f x ,- (fs $V xs)
infixl 3 _$V_  -- "Application associates to the left,
               --  rather as we all did in the sixties." (Roger Hindley)

-- Pattern matching and recursion are forbidden for the next two tasks.

-- implement vMap again, but as a one-liner
vec : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vec f xs = vp $V xs
  where vp = vPure f

-- implement the operation which pairs up corresponding elements
vZip : {X Y : Set}{n : Nat} -> Vec X n -> Vec Y n -> Vec (X * Y) n
vZip [] [] = []
vZip (x ,- xs) (y ,- ys) = (x , y) ,- vZip xs ys 

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Applicative Laws
------------------------------------------------------------------------------

-- According to "Applicative programming with effects" by
--   Conor McBride and Ross Paterson
-- some laws should hold for applicative functors.
-- Check that this is the case.

--??--1.6-(2)-----------------------------------------------------------------

vIdentity : {X : Set}{f : X -> X}(feq : (x : X) -> f x == x) ->
            {n : Nat}(xs : Vec X n) -> (vPure f $V xs) == xs
vIdentity feq [] = refl []
vIdentity feq (x ,- xs) rewrite feq x = cong (λ x₁ → x ,- x₁) (vIdentity feq xs)

vHomomorphism : {X Y : Set}(f : X -> Y)(x : X) ->
                {n : Nat} -> (vPure f $V vPure x) == vPure (f x) {n}
vHomomorphism f x {zero} = refl []
-- vHomomorphism f x {suc n} rewrite vHomomorphism f x {n} = refl (f x ,- vPure (f x))
vHomomorphism f x {suc n} = cong (λ x₁ → f x ,- x₁) (vHomomorphism f x {n})

vInterchange : {X Y : Set}{n : Nat}(fs : Vec (X -> Y) n)(x : X) ->
               (fs $V vPure x) == (vPure (_$ x) $V fs)
vInterchange [] x = refl []
vInterchange (f ,- fs) x = cong (λ x₁ → (f x) ,- x₁) (vInterchange fs x)

vComposition : {X Y Z : Set}{n : Nat}
               (fs : Vec (Y -> Z) n)(gs : Vec (X -> Y) n)(xs : Vec X n) ->
               (vPure _<<_ $V fs $V gs $V xs) == (fs $V (gs $V xs))
vComposition [] [] [] = refl []
vComposition (f ,- fs) (g ,- gs) (x ,- xs)  = cong (λ x₁ → (f << g $ x) ,- x₁) (vComposition fs gs xs)

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Order-Preserving Embeddings (also known in the business as "thinnings")
------------------------------------------------------------------------------

-- What have these to do with Pascal's Triangle?

data _<=_ : Nat -> Nat -> Set where
  oz :                          zero  <= zero
  os : {n m : Nat} -> n <= m -> suc n <= suc m
  o' : {n m : Nat} -> n <= m ->     n <= suc m

-- Find all the values in each of the following <= types.
-- This is a good opportunity to learn to use C-c C-a with the -l option
--   (a.k.a. "google the type" without "I feel lucky")
-- The -s n option also helps.

--??--1.7-(1)-----------------------------------------------------------------

all0<=4 : Vec (0 <= 4) 1
all0<=4 = o' (o' (o' (o' oz))) ,- []

v0n : (n : Nat) → (0 <= n) 
v0n zero = oz
v0n (suc n) = o' (v0n n)

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  -- whats the difference here?
  -- Just : (x : A) → Maybe A
  Just : A → Maybe A

v1n : (n : Nat) → Maybe (1 <= n) 
v1n zero = Nothing
v1n (suc n) = Just (os (v0n n))

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsucc : {n : Nat} -> Fin n -> Fin (suc n)

-- v1nF : (n : Nat) → (n >= 1) → (1 <= n) 
-- v1nF (suc n) <> = os (v0n n)

v1nF : (n : Nat) → {a : n >= 1} → (1 <= n) 
v1nF (suc n) = os (v0n n)

v1nm : (n m : Nat) → {a : n >= m} → {b : m >= 1} → {c : n >= 1} → (1 <= n) 
v1nm (suc zero) (suc zero)  = os oz
v1nm (suc (suc n)) (suc zero)  = v1nF (suc (suc n)) 
v1nm (suc (suc n)) (suc (suc m)) {a = x} = o' (v1nm (suc n) (suc m) {x})

-- vMap : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n

-- oneToN : {X : Set} (n : Nat) → Vec X n
oneToN : (n : Nat) → Vec Nat n
oneToN zero = []
oneToN (suc n) = suc n ,- oneToN n 
-- oneToN (suc n) =  {!(oneToN n) +V (suc n ,- [])!} -- (oneToN n) +V (suc n ,- [])

all1<=n : (n : Nat) → Vec (1 <= n) n
all1<=n n = vMap (λ x → v1nm n x) (oneToN n) 

data _**_ (A B : Set) : Set where
  _,,_ : A → B → A ** B

-- -- oneToN : {X : Set} (n : Nat) → Vec X n
-- oneToN : (n : Nat) → Vec (Nat ** ) n
-- oneToN zero = []
-- oneToN (suc n) = suc n ,- oneToN n 

-- all1<=n : (n : Nat) → {a : n >= 1} → Vec (1 <= n) n
-- all1<=n n {a = a} = vMap (λ x → v1nm n x {c = a}) (oneToN n) 


-- v1nF : (n : Nat) → Fin n → (1 <= n) 
-- v1nF zero ()
-- v1nF (suc zero) fzero = o' {!!}
-- v1nF (suc (suc n)) fzero = {!!}
-- v1nF (suc n) (fsucc x) = {!!}

-- v1nChoose 

-- -- so could we construct a data type of numbers greater than n
-- data Nat> (n : Nat) : Set where
--   nN : (n : Nat) → Nat> n
--   nN : 


all1<=4 : Vec (1 <= 4) 4
all1<=4 = os (o' (o' (o' oz))) ,- (o' (os ( o' (o' oz )))) ,- (o' (o' (os (o' oz))) ,- o' (o' (o' (os oz))) ,- [])

-- all1<=4' : Vec (1 <= 4) 4
-- all1<=4' = {!!}

all2<=4 : Vec (2 <= 4) 6
all2<=4 = (os (os (o' (o' oz)))) ,- ((o' (os (os (o' oz)))) ,- os (o' (os (o' oz))) ,- os (o' (o' (os oz))) ,- (o' (o' (os (os oz)))) ,- (o' (os (o' (os oz)))) ,- [])

       
all3<=4 : Vec (3 <= 4) 4
all3<=4 = (os (os (os (o' oz)))) ,- (os (os (o' (os oz))) ,-
                                       os (o' (os (os oz))) ,- o' (os (os (os oz))) ,- [])

all4<=4 : Vec (4 <= 4) 1
all4<=4 = os (os (os (os oz))) ,- []

-- Prove the following. A massive case analysis "rant" is fine.

no5<=4 : 5 <= 4 -> Zero
no5<=4 (os (os (os (os ()))))
no5<=4 (os (os (os (o' ()))))
no5<=4 (os (os (o' (os ()))))
no5<=4 (os (os (o' (o' ()))))
no5<=4 (os (o' (os (os ()))))
no5<=4 (os (o' (os (o' ()))))
no5<=4 (os (o' (o' (os ()))))
no5<=4 (os (o' (o' (o' ()))))
no5<=4 (o' (os (os (os ()))))
no5<=4 (o' (os (os (o' ()))))
no5<=4 (o' (os (o' (os ()))))
no5<=4 (o' (os (o' (o' ()))))
no5<=4 (o' (o' (os (os ()))))
no5<=4 (o' (o' (os (o' ()))))
no5<=4 (o' (o' (o' (os ()))))
no5<=4 (o' (o' (o' (o' ()))))

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Order-Preserving Embeddings Select From Vectors
------------------------------------------------------------------------------

-- Use n <= m to encode the choice of n elements from an m-Vector.
-- The os constructor tells you to take the next element of the vector;
-- the o' constructor tells you to omit the next element of the vector.

--??--1.8-(2)-----------------------------------------------------------------

_<?=_ : {X : Set}{n m : Nat} -> n <= m -> Vec X m
                     -> Vec X n
oz <?= xs = xs
os th <?= (x ,- xs) = x ,- th <?= xs
o' th <?= (x ,- xs) = th <?= xs

-- it shouldn't matter whether you map then select or select then map

vMap<?=Fact : {X Y : Set}(f : X -> Y)
              {n m : Nat}(th : n <= m)(xs : Vec X m) ->
              vMap f (th <?= xs) == (th <?= vMap f xs)
vMap<?=Fact f oz [] = refl []
vMap<?=Fact f (os th) (x ,- xs) rewrite vMap<?=Fact f th xs = refl (f x ,- (th <?= vMap f xs))
-- vMap<?=Fact f (os th) (x ,- xs) = cong (λ x₁ → (f x) ,- x₁) (vMap<?=Fact f  th xs)
vMap<?=Fact f (o' th) (x ,- xs) = vMap<?=Fact f th xs

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Our Favourite Thinnings
------------------------------------------------------------------------------

-- Construct the identity thinning and the empty thinning.

--??--1.9-(1)-----------------------------------------------------------------

oi : {n : Nat} -> n <= n
oi {zero} = oz
oi {suc n} = os oi

oe : {n : Nat} -> 0 <= n
oe {zero} = oz
oe {suc n} = o' oe

--??--------------------------------------------------------------------------


-- Show that all empty thinnings are equal to yours.

--??--1.10-(1)----------------------------------------------------------------

oeUnique : {n : Nat}(th : 0 <= n) -> th == oe
oeUnique oz = refl oz
oeUnique (o' i) = cong o' (oeUnique i)

--??--------------------------------------------------------------------------


-- Show that there are no thinnings of form big <= small  (TRICKY)
-- Then show that all the identity thinnings are equal to yours.
-- Note that you can try the second even if you haven't finished the first.
-- HINT: you WILL need to expose the invisible numbers.
-- HINT: check CS410-Prelude for a reminder of >=

--??--1.11-(3)----------------------------------------------------------------

⊥-elim : ∀ {A : Set} → Zero → A
⊥-elim = λ ()

-- (trans->= m n (suc m))

lemma : forall (y : Nat) → y  >= suc y → Zero
lemma (suc y) x = lemma y x

lemma' : forall (n m : Nat) → n <= m → m >= n
lemma' .0 .0 oz = <>
lemma' (suc n) (suc m) (os x) = lemma' n m x
lemma' n (suc m) (o' x) = trans->= (suc m) m n (suc->= m) (lemma' n m x)

oTooBig : {n m : Nat} -> n >= m -> suc n <= m -> Zero
oTooBig {n} {(suc m)} n>=m (os th) = ⊥-elim (lemma m (trans->= m n (suc m) (lemma' n m th) n>=m))
oTooBig {n} {(suc m)} n>=m (o' th) = ⊥-elim (lemma m (trans->= m n (suc m) (trans->= m (suc n) n opp (suc->= n)) n>=m))
  where 
    opp = lemma' (suc n) m th

oiUnique : {n : Nat}(th : n <= n) -> th == oi
oiUnique oz = refl oz
oiUnique (os th) rewrite oiUnique th = refl (os oi)
oiUnique {m} (o' th) = ⊥-elim (lemma m (lemma' (suc m) m (os th)))

--??--------------------------------------------------------------------------

-- Show that the identity thinning selects the whole vector

--??--1.12-(1)----------------------------------------------------------------

id-<?= : {X : Set}{n : Nat}(xs : Vec X n) -> (oi <?= xs) == xs
id-<?= [] = refl []
id-<?= (x ,- xs) rewrite id-<?= xs = refl (x ,- xs)

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Composition of Thinnings
------------------------------------------------------------------------------

-- Define the composition of thinnings and show that selecting by a
-- composite thinning is like selecting then selecting again.
-- A small bonus applies to minimizing the length of the proof.
-- To collect the bonus, you will need to think carefully about
-- how to make the composition as *lazy* as possible.

--??--1.13-(3)----------------------------------------------------------------

-- lemma' : forall (n m : Nat) → n <= m → m >= n

lemma'' : forall (n m : Nat) →  m >= n → n <= m 
lemma'' zero zero x = oz
lemma'' zero (suc m) x = o' (lemma'' zero m <>)
lemma'' (suc n) (suc m) x = os (lemma'' n m x)

_o>>_ : {p n m : Nat} -> p <= n -> n <= m -> p <= m
th o>> oz = th
os th o>> os ph = os (th o>> ph)
o' th o>> os ph = o' (th o>> ph)
th o>> o' ph = o' (th o>> ph)

cp-<?= : {p n m : Nat}(th : p <= n)(th' : n <= m) ->
  {X : Set}(xs : Vec X m) ->
  ((th o>> th') <?= xs) == (th <?= (th' <?= xs))
cp-<?= th oz [] = refl (th <?= [])
cp-<?= (os th) (os th') (x ,- xs) rewrite cp-<?= th th' xs = refl (x ,- (th <?= (th' <?= xs)))
cp-<?= (o' th) (os th') (x ,- xs) rewrite cp-<?= th th' xs = refl (th <?= (th' <?= xs))
cp-<?= th (o' th') (x ,- xs) = cp-<?= th th' xs

------------------------------------------------------------------------------
-- Thinning Dominoes
------------------------------------------------------------------------------

--??--1.14-(3)----------------------------------------------------------------

idThen-o>> : {n m : Nat}(th : n <= m) -> (oi o>> th) == th
idThen-o>> oz = refl oz
idThen-o>> (os th) rewrite idThen-o>> th = refl (os th)
idThen-o>> (o' th) rewrite idThen-o>> th = refl (o' th)

idAfter-o>> : {n m : Nat}(th : n <= m) -> (th o>> oi) == th
idAfter-o>> oz = refl oz
idAfter-o>> (os th) rewrite idAfter-o>> th = refl (os th)
idAfter-o>> (o' th) rewrite idAfter-o>> th = refl (o' th)

assoc-o>> : {q p n m : Nat}(th0 : q <= p)(th1 : p <= n)(th2 : n <= m) ->
  ((th0 o>> th1) o>> th2) == (th0 o>> (th1 o>> th2))
assoc-o>> oz th1 th2 rewrite idThen-o>> th1 | idThen-o>> (th1 o>> th2)= refl (th1 o>> th2)
assoc-o>> (os th0) th1 (o' th2) rewrite assoc-o>> (os th0) th1 th2 = refl (o' (os th0 o>> (th1 o>> th2)))
assoc-o>> (os th0) (os th1) (os th2) rewrite assoc-o>> th0 th1 th2 = refl (os (th0 o>> (th1 o>> th2)))
assoc-o>> (os th0) (o' th1) (os th2) rewrite assoc-o>> (os th0) th1 th2 = refl (o' (os th0 o>> (th1 o>> th2)))
assoc-o>> (o' th0) th1 (o' th2) rewrite assoc-o>> (o' th0) th1 th2 = refl (o' (o' th0 o>> (th1 o>> th2)))
assoc-o>> (o' th0) (os th1) (os th2) rewrite assoc-o>> (th0) th1 th2 = refl (o' (th0 o>> (th1 o>> th2)))
assoc-o>> (o' th0) (o' th1) (os th2) rewrite assoc-o>> (o' th0) th1 th2 = refl (o' (o' th0 o>> (th1 o>> th2)))


ref< : {n : Nat} → n <= n
ref< {zero} = oz
ref< {suc n} = os ref<

-- _o>>_ : {p n m : Nat} -> p <= n -> n <= m -> p <= m

-- leWrong : {n : Nat} → suc n <= n → Zero
-- leWrong (os x) = {!!}
-- leWrong (o' x) = {!!}

leWrong : {n : Nat} → suc n <= n → Zero
-- leWrong {suc n} (os x) = leWrong x
leWrong {suc n} (os x) = leWrong x
leWrong {suc n} (o' x) = leWrong (fdsa o>> x)
  where
    fdsa : suc n <= suc (suc n)
    fdsa = os (o' (ref< {n}))

revSuc : {n : Nat} → suc n <= suc n → n <= n
revSuc (os x) = x
revSuc (o' x) = ⊥-elim (leWrong x)

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- -- Vectors as Arrays
-- ------------------------------------------------------------------------------

-- -- We can use 1 <= n as the type of bounded indices into a vector and do
-- -- a kind of "array projection". First we select a 1-element vector from
-- -- the n-element vector, then we take its head to get the element out.


-- -- order preserving embedding
-- -- _<?=_ : {X : Set}{n m : Nat} -> n <= m -> Vec X m
-- -- -> Vec X n

-- -- Your (TRICKY) mission is to reverse the process, tabulating a function
-- -- from indices as a vector. Then show that these operations are inverses.

-- --??--1.15-(3)----------------------------------------------------------------

-- -- all1<=n : (n : Nat) → Vec (1 <= n) n

-- -- foldr : {X : Set} {n : Nat} → Vec X n → ()
-- foldrV : {X Y : Set} {n : Nat} → (X -> Y -> Y) -> Y -> Vec X n -> Y
-- foldrV f y0 [] = y0
-- foldrV f y0 (x ,- xs) = f x (foldrV f y0 xs)

-- foldlV : {X Y : Set} {n : Nat} → (X -> Y -> Y) -> Y -> Vec X n -> Y
-- foldlV f y0 [] = y0
-- foldlV f y0 (x ,- xs) = foldlV f acc xs
--   where
--     acc = f x y0 

-- flip : {A B C : Set} → (A -> B -> C) -> B -> A -> C
-- flip f b a = f a b

-- -- reverse : {A : Set} → {n : Nat} → Vec A n → Vec A n
-- -- reverse = foldlV (flip ?) ? 

-- lengthL : {X : Set} → List X → Nat
-- lengthL [] = 0
-- lengthL (x ,- xs) = 1 +N (lengthL xs)

-- lemmaSuc : {n m : Nat} → suc n == suc m → n == m 
-- lemmaSuc {n} (refl .(suc n)) = refl n

-- list2V : {X : Set} (n : Nat) (l : List X) → (n == (lengthL l)) → Vec X n
-- list2V zero [] p = []
-- list2V (suc n) (x ,- ls) p = x ,- list2V n ls (lemmaSuc p) 

-- lT = list2V 3 (4 ,- 5 ,- 6 ,- []) (refl 3)

-- lReverse : {X : Set} → List X → List X
-- lReverse xs = lHelp xs []
--   where
--     lHelp : {X : Set} → List X → List X → List X
--     lHelp [] acc = acc
--     lHelp (x ,- xs) acc = lHelp xs (x ,- acc)

-- l+ : {X : Set} → List X → List X → List X
-- l+ [] ys = ys
-- l+ (x ,- xs) ys = x ,- l+ xs ys

-- lReverse' : {X : Set} → List X → List X
-- lReverse' [] = []
-- lReverse' (x ,- xs) = l+ (lReverse' xs) (x ,- [])

-- ltt = lReverse (4 ,- 5 ,- 6 ,- [])
-- ltt' = lReverse' (4 ,- 5 ,- 6 ,- [])

-- v2L : {X : Set} {n : Nat} → Vec X n → List X
-- v2L [] = []
-- v2L (x ,- l) = x ,- v2L l

-- lemmaSuc' : {n m : Nat} → n == m → suc n == suc m
-- -- lemmaSuc' (refl x) = refl (suc x)
-- lemmaSuc' x = cong suc x

-- lengthHomo : {X : Set} (xs ys : List X) → (lengthL (l+ xs ys)) == ((lengthL xs) +N (lengthL ys))
-- lengthHomo [] ys = refl (lengthL ys)
-- lengthHomo (x ,- xs) ys = lemmaSuc' (lengthHomo xs ys)

-- postulate
--   +-comm : (m n : Nat) → (m +N n) == (n +N m)

-- revLem : {X : Set} {n : Nat} → (xs : Vec X n) → n == lengthL (lReverse' (v2L xs))
-- revLem [] = refl zero
-- -- revLem (x ,- xs) = subst {!!} (lengthHomo (lReverse' (v2L xs)) (x ,- [])) {!!}
-- -- almost
-- -- revLem {X} {n} (x ,- xs) = {!subst (λ x → n == x) (lengthHomo (lReverse' (v2L xs)) (x ,- [])) ?!}
-- -- revLem {X} {n} (x ,- xs) = {!subst (λ x → n == x) (lengthHomo (lReverse' (v2L xs)) (x ,- [])) ?!}
-- -- revLem {X} {n} (x ,- xs) = n =[ subst (λ x → n == x) (lengthHomo (lReverse' (v2L xs)) (x ,- [])) {!!} >= {!!}
-- revLem {X} {n} (x ,- xs) = sym (lengthL (l+ (lReverse' (v2L xs)) (x ,- []))
--                               =[ ((lengthHomo (lReverse' (v2L xs)) (x ,- []))) >= {!subst (List _) (+-comm _ 1)!})



-- -- revLem {X} {n} (x ,- xs) = sym (lengthL (l+ (lReverse' (v2L xs)) (x ,- []))
-- -- =[ ((lengthHomo (lReverse' (v2L xs)) (x ,- []))) >= {!!})

-- -- revLem [] = refl zero
-- -- revLem (x ,- xs) = cong suc (revLem xs)

-- -- vReverse : {X : Set} (n : Nat) → Vec X n → Vec X n
-- -- vReverse n xs = list2V n (lReverse (v2L xs)) (revLem xs) 
-- -- -- vReverse .0 [] = []
-- -- -- vReverse (suc n) (x ,- xs) = x ,- list2V n (lReverse (v2L xs)) {!!}



-- vReverse : {X : Set} {n : Nat} → Vec X n → Vec X n
-- vReverse [] = []
-- vReverse (x ,- x₁) = subst (Vec _) (+-comm _ 1) $ (vReverse x₁) +V (x ,- [])

-- rtest = vReverse (3 ,- 4 ,- [])


-- foldl : ∀  {A : Set} (B : Nat → Set) {m} →
--   (∀ {n} → B n → A → B (suc n)) →
--   B zero →
--   Vec A m → B m
-- foldl b f n [] = n
-- foldl b f n (x ,- xs) = foldl (λ a → b (suc a)) f (f n x) xs
-- -- foldl b _⊕_ n ε       = {!n!}
-- -- foldl b _⊕_ n (x ,- xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs


-- reverse : ∀ {A} {n} → Vec A n → Vec A n
-- reverse {A = A} = foldl (Vec A) (λ rev x → x ,- rev) []

-- rtest' = reverse (3 ,- 4 ,- [])

-- -- reverse : {A : Set} → {n : ℕ} → Vec A n → Vec A n
-- -- reverse {A} = foldl (Vec A) (flip _►_) ε

-- -- vReverse [] acc = {!!}
-- -- vReverse (x ,- xs) acc = vReverse {!xs!} {!!}

-- -- vReverse : {X : Set} {n : Nat} (m : Nat) → Vec X n → Vec X m → Vec X n
-- -- vReverse m [] acc = {!!}
-- -- vReverse m (x ,- xs) acc = {!!}

-- -- vReverse m [] x₁ = x₁
-- -- vReverse m (x ,- xs) acc = {!vReverse xs (x ,- acc)!}
-- -- vReverse xs = foldlV (λ x y → {!!}) {![]!} {!!}
-- -- vReverse [] = []
-- -- vReverse (x ,- x₁) = {!(vReverse x₁) +V (x ,- [])!}


-- f10 : 1 <= 2 -> Two
-- f10 (os (o' oz)) = ff
-- f10 (o' (os oz)) = tt

-- f11 : 1 <= 2 -> Two
-- f11 (os (o' oz)) = tt
-- f11 (o' (os oz)) = tt

-- f1 : (1 <= 2 -> Two) → Vec Two 2
-- f1 x = x (os (o' oz)) ,- x (o' (os oz)) ,- []


-- all1<=4' : Vec (1 <= 4) 4
-- all1<=4' = os (o' (o' (o' oz))) ,- (o' (o' (os (o' oz))) ,- (o' (os ( o' (o' oz )))) ,- o' (o' (o' (os oz))) ,- [])

-- -- HINT: composition of functions
-- vTabulate : {n : Nat}{X : Set} -> (1 <= n -> X) -> Vec X n
-- -- vTabulate {n} f = vMap f (all1<=n n)
-- vTabulate {n} f = reverse (vMap f (all1<=n n))
-- -- vTabulate {zero} f = []
-- -- vTabulate {suc n} f = (f {!!}) ,- vTabulate (λ z → f (o' z))

-- vProject : {n : Nat}{X : Set} -> Vec X n -> 1 <= n -> X
-- vProject xs i = vHead (i <?= xs)

-- -- works? = vProject all1<=4' (o' (os ( o' (o' oz ))))
-- -- works? = vProject all1<=4' (os (o' (o' (o' oz))) )

-- as = vTabulate (vProject (3 ,- 4 ,- 7 ,- 6 ,- []))
-- -- asdffdsa : vTabulate (vProject (3 ,- 4 ,- [])) == (3 ,- 4 ,- [])

-- vTabulateProjections' : {n : Nat}{X : Set}(x : Vec X 1) ->
--   vTabulate (vProject x) == x
-- vTabulateProjections' (x ,- []) = refl (x ,- [])

-- tabProjHom :  {n : Nat}{X : Set}(x : X)(xs : Vec X n) ->
--    vTabulate (vProject (x ,- xs)) == (vTabulate (vProject (x ,- [])) +V vTabulate (vProject (xs)))
-- tabProjHom x [] rewrite vTabulateProjections' (x ,- []) = refl (x ,- [])
-- tabProjHom x (x₁ ,- xs) rewrite tabProjHom x xs | vTabulateProjections' (x ,- [])  = {!!}

-- -- _<?=_ : {X : Set}{n m : Nat} -> n <= m -> Vec X m
-- -- -> Vec X n
-- -- oz <?= xs = xs
-- -- os th <?= (x ,- xs) = x ,- th <?= xs
-- -- o' th <?= (x ,- xs) = th <?= xs

-- -- This should be easy if vTabulate is correct.
-- vTabulateProjections : {n : Nat}{X : Set}(xs : Vec X n) ->
--                        vTabulate (vProject xs) == xs
-- vTabulateProjections [] = refl []
-- vTabulateProjections (x ,- xs) = {!refl!}
-- -- vTabulateProjections [] = refl []
-- -- vTabulateProjections (x ,- xs) = {!!}

-- -- HINT: oeUnique
-- vProjectFromTable : {n : Nat}{X : Set}(f : 1 <= n -> X)(i : 1 <= n) ->
--                     vProject (vTabulate f) i == f i
-- vProjectFromTable f i = {!!}

-- --??--------------------------------------------------------------------------
