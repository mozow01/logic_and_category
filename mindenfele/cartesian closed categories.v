Context {CC : Category}.

Class CartClosed := {

(* terminal *)

  Top_obj : Obj;

  Top_mor : forall {x}, x → Top_obj;
 
  unique_top : forall {x} (f : x → Top_obj), f = Top_mor;

(* szorzat *)

  Prod_obj : Obj -> Obj -> Obj;

  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;

  First {x y} : (Prod_obj x y) → x;
  Second {x y} : (Prod_obj x y) → y;

  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (First ∘ (Prod_mor f g) = f) /\ (Second ∘ (Prod_mor f g) = g);
  
  unique_prod : forall {x y z} (f : x → y) (g : x → z) (h : x → Prod_obj y
z),
    ((First ∘ h) = f) /\ ((Second ∘ h) = g) -> h = Prod_mor f g;

(* exponenciális *)

  Exp_obj : Obj -> Obj -> Obj;

  Exp_mor : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;

  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
    Exp_mor ∘ (Prod_mor (Compose (Lam g) First) (Compose (Id y) Second)) = g;
  
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Exp_mor ∘ (Prod_mor (Compose h First) (Compose (Id y) Second))) = h
}.

(* 

  lemmácska TODO: forall x y z (g : x × y -> z), g = eval ∘ (h × id y) -> Lam g = h

ez ekv. unique_exp-pel.

*)


Notation "⊤" := (Top_obj) (at level 40, no
associativity) : type_scope.

Notation "'〈' x ',' y '〉'" := (Prod_mor x y) (at level 40, no
associativity) : type_scope.

Notation "x × y" := (Prod_obj x y) (at level 40, left associativity) :
type_scope. 

Notation "x 'e↑' y" := (Exp_obj x y) (at level 80, right associativity) :
type_scope. 

Notation "f '⊠' g" := (Prod_mor (Compose f First) (Compose g Second)) (at level 40, left associativity) :
type_scope.
