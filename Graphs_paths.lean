structure Graph(V: Type) (E: Type) where
  null : E
  init : E → V
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e: E, bar e ≠ e
  
variable {V: Type}{E: Type}[DecidableEq V][DecidableEq E]

@[inline] def term{V: Type}{E: Type}(graph: Graph V E): E → V :=
  fun e => graph.init (graph.bar e)

inductive EdgePath{V: Type}{E: Type}(graph: Graph V E): V → V → Type where
  | single : (x: V) → EdgePath graph v v
  | cons : {x y z : V} → (e : E) → graph.init e = x → term graph e = y →  
        EdgePath graph y z → EdgePath graph x z

def length{V: Type}{E: Type}{graph: Graph V E}{x y: V}: EdgePath graph x y → Nat
  | EdgePath.single x => 0
  | EdgePath.cons  _ _ _ path => length path + 1 

open EdgePath

theorem lemma2 {G : Graph V E} {x y : V}{h3 :  Prop} : (x = y) → (h3 : (single x) = single y ):=
by 
intro h
exact congrArg (fun x => single x) h

/-theorem lemma2  {V : Type} {E : Type} (G : Graph V E) {x y z : V} (p : EdgePath G x z) (h : x = y) : EdgePath G y z :=
match h with
| rfl => p

def follow {V : Type} {E : Type} (G : Graph V E) (x y : V) (p : EdgePath G x y) : V :=
match p with
| single x => x
| cons ex h1 h2 exy => term G ex


def forward {V : Type} {E : Type} {G : Graph V E} {x y : V} (p : EdgePath G x y) :  EdgePath G _ y :=
match p with
| cons ex h1 h2 exy => --have h : (follow G x _ p) = term G ex := sorry 
                         exy 
| single x => sorry


def next {V : Type} {E : Type} {G : Graph V E} {x y : V}: EdgePath G x y → E
| single x => G.null
| cons ex h1 h2 exy => ex-/

-- concatenates two edgepaths 
def multiply {V : Type} {E : Type} {G : Graph V E} {x y z : V}: (EdgePath G x y) → (EdgePath G y z) → (EdgePath G x z) 
| single x , single y => single x 
|  single x , cons ey h1 h2 eyz => cons ey h1 h2 eyz
| cons ex h1 h2 exy , single y => cons ex h1 h2 exy
| cons ex h1 h2 exy , cons ey h3 h4 eyz => cons ex h1 h2 (multiply exy (cons ey h3 h4 eyz))

--proves that the endpoint of the reverse of an edge is the start point of the edge
theorem lemma1 {V : Type} {E : Type} {G : Graph V E} {x : V}{e : E}: G.init e = x → (term G (G.bar e) = x) :=
by
intro h
have h1 : G.bar (G.bar e) = e := congr G.barInv (Eq.refl e) 
have h2 : G.init (G.bar (G.bar e)) = G.init e := congrArg G.init h1 
apply Eq.trans h2 h

-- reverses an edgepath
def inverse {V : Type} {E : Type} {G : Graph V E} {x y : V}: (EdgePath G x y) → (EdgePath G y x)
| single x => single x 
| cons ex h1 h2 exy => multiply (inverse exy) (cons (G.bar (ex)) h2 (lemma1 h1) (single x)) 

-- redu
def reducePath {G : Graph V E} {x y : V} : EdgePath G x y→ EdgePath G x y
| single x => single x
| cons ex h1 h2 (single y) => cons ex h1 h2 (single y)
| cons ex h1 h2 (cons ey h3 h4 (eyz)) => 
    if c : x = term G ey then
      if ey = G.bar (ey) then
      Eq.symm (Eq.trans c h4) ▸ eyz
      else
      cons ex h1 h2 (cons ey h3 h4 (reducePath eyz))
    else
    cons ex h1 h2 (cons ey h3 h4 (reducePath eyz))


inductive homotopy {G : Graph V E} : EdgePath G x y → EdgePath G x y → Type where
| consht : (x : V) → homotopy (single x) (single x)
| cancel : (ex : E) → {w x y : V} → (p : EdgePath G x y) → 
           (h : x = G.init ex) → { h1 : term G ex = w} → 
           homotopy p (cons ex (Eq.symm h) h1 (cons (G.bar (ex)) h1 (lemma1 (Eq.symm h)) p))
| mult : {x y z : V} → {p q : EdgePath G y z} →
         homotopy p q → (ex : E) →(h1 : y = term G ex) → { h : x = G.init ex} → 
         homotopy (cons ex (Eq.symm h) (Eq.symm h1) p) (cons ex (Eq.symm h) (Eq.symm h1) q)

theorem homotopymult {G : Graph V E} {x y z : V} {p1 p2 : EdgePath G y z} {q : EdgePath G x y} (h :homotopy p1 p2):
         (homotopy (multiply q p1) (multiply q p2)) :=
    EdgePath.casesOn (motive :=  fun (x y : V) (q : EdgePath G x y) => 
                                {z : V} → {p1 p2 : EdgePath G y z} → {q : EdgePath G x y} → 
                                (h : homotopy p1 p2) →  homotopy (multiply q p1) (multiply q p2)) q
(
  by
  intro a b c p q r h1 
  have h2 : (multiply r p) = p := by

  rfl
)
(

)
#check @EdgePath.casesOn

