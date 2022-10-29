## The definition of Category in the Monoid Hell (aka categotry with morphism equality)

````coq
(*The definition of Category in the Monoid Hell (aka categotry with morphism equality) *)

(* generic parameterized typeclass, no implementations for any field *)
Class Category := cat_mk {
  Obj : Type; (* type of objects, might be Type or Set for the categories Set or Hask*)

  uHom := Type : Type; (* type of morphisms, defaults to "Type", but might be more restricted - defaults to Type, might be overridden *)

  Hom : Obj -> Obj -> uHom; (* morphism constructor function *)

  Id : forall x, Hom x x; (* Id x := Hom x x*)

  Dom {x y} (f: Hom x y) := x; (* domain operator on morhpisms *)

  CoDom {x y} (f: Hom x y) := y; (* codomain operator on morhisms *)

  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z); (* morhism compose operator *)

  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop; (* equality for two morphisms *)

  (* the prev. equality operator must satisfy these equalities *)
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;

  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h 
         -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;


  (* category laws: associativity of composition, composition of identities, composition preserves identity from both sides *)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);

  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f ;

  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f ;

  eq_1 : forall {x y z} (f: Hom y z) (g h : Hom x y), EqMor g h ->
        EqMor (Compose f g) (Compose f h);
  eq_2 : forall {x y z} (f: Hom x y) (g h : Hom y z), EqMor g h ->
        EqMor (Compose g f) (Compose h f);

}.
````
