(*The definition of Category in the Monoid Hell (aka categotry with morphism equiality) *)

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
Print EqMor.


Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

(* Programmer's composition - might need to refine the level & associativity *)
Notation "g >> f" := (Compose f g) (at level 39, right associativity) : type_scope.

Notation "f ≡ g" := (EqMor f g) (at level 40, left associativity) :
type_scope.

Context {C : Category}.


(* dependent data type - Endofunctor of a category *)
Class EndoFunctor {C : Category} := {

EF_obj : @Obj C -> @Obj C;

EF_mor : forall {x y}, (Hom x y) -> (Hom (EF_obj x) (EF_obj y));

(* functor laws *)
EF_keeps_id : forall {x}, EF_mor (Id x) = Id (EF_obj x);
EF_comp_ax : forall {x y z : @Obj C} {f g},
      @EF_mor x z (f ∘ g) = (@EF_mor y z f) ∘ (@EF_mor x y g)
}.


(* F-algebra is a dependent type on a Category C and it's endofunctor F, and then defined by an object an a morphism (actually the morphism's domain must be the given object *)
Class F_algebra {C : Category} (F : @EndoFunctor C) := {

Carr_F_alg : @Obj C;

Mor_F_alg : Hom ((@EF_obj C F) Carr_F_alg) Carr_F_alg
}.


(* now this is a part I can't grasp yet *)
Ltac Kitten :=
  repeat match goal with
           | [ H : ?P |- ?P ] => exact H
           | [ |- (?P ∘ (Id ?Q)) ≡ ?P  ] => apply id_1
           | [ |- ((Id ?Q) ∘ ?P) ≡ ?P  ] => apply id_2
           | [ |- ?P ≡ ?P  ] => apply Eq_ref
           | [ H : ?P ≡ ?Q |- ?Q ≡ ?P ] => apply Eq_sim
           | [ |- (?P ∘ ?Q) ≡ (?P ∘ ?R) ] => apply eq_1
           | [ |- ( ?Q ∘ ?P ) ≡ (?R ∘ ?P) ] => apply eq_1
         end.


Definition object_is_carrier {C: Category} (F: @EndoFunctor C) := fun (x:@Obj C) => Hom (@EF_obj C F x) x.

Definition F_algebras_Obj {C : Category} (F : @EndoFunctor C) := (@sigT (@Obj C) (@object_is_carrier C F ) ) : Type.
(*
Given object & endofunctor, the set of F-algebras defined by these is the set of (X, a) pairs whose X is an object in C (so first type of pair os Object type in C) and a is a morhphism F X -> X. The sets are not restrictive, afaik only the types must be equal, so if you have a morphism NOT IN C, you could still consider it as an F_algebras_obj.
*)


Definition F_algebras_Hom {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) (y : F_algebras_Obj F) 
:= (sig (fun (f : @Hom C (projT1 x) (projT1 y) ) =>  ((projT2 y) ∘ (EF_mor f )) ≡ (f ∘ (projT2 x) ) )).
Print projT1.
(* morphisms between two f-algebras are mophisms between the carries that also satisfy the law of the square commuting, so a: F A -> A and b: F B -> B morphisms and associated F-algebras, the morphism x: A->B of C is also a morphism between the F-algebras if F x: F A -> F B and F x >> b = a >> x

projT1 -> Dom of morphism
projT2 -> the morphism itself

this could be rewritten so it's easier to understand, maybe with pattern matching
*)

Definition F_algebras_EqMor {C : Category} (F : @EndoFunctor C) (x y : F_algebras_Obj F) (f g : F_algebras_Hom F x y) := (proj1_sig f) ≡ (proj1_sig g).
(* two morphisms between two f-algebras are equal if the underlying morphisms in C equal *)

(* Nem elég megmondani hogy Id ilyen, be is kell biznyítani *)
Definition F_algebras_Id {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) : @F_algebras_Hom C F x x. (* := @existT (@Obj C) (@object_is_carrier C F) (projT1 x) (Hom (projT1 x) (projT1 x)).*)
  unfold F_algebras_Hom.
  set (Carrier:=projT1 x) in *; set (Morphism := projT2 x) in *.
  (* Id of Carrier defines such a morphism for F-algebras *)
  exists (@Id C Carrier).

  rewrite EF_keeps_id.
  apply Eq_trans with (Morphism).
  apply id_1.
  apply Eq_sim; apply id_2.
Defined.


(* this could be rewritten as an exist valued function, but would still need the proof so this looks a bit cleaner *)


(* 
Composistion of two morphisms between F-algebras. Must exists, as the underlying morphisms in C can also compose, so we have to proove this
*)
Definition F_algebras_Comp {C : Category} (F : @EndoFunctor C) (x y z : F_algebras_Obj F)
(h : F_algebras_Hom F y z ) (k : F_algebras_Hom F x y ) : F_algebras_Hom F x z.
  unfold F_algebras_Hom.

  (*
  Aliasok:
  H: homomorfizmus 1 (Y->Z)
  K: homomorfizmus 2 (X->Y)
  XMorph, YMorph, ZMorph: X,Y,Z F-algebrát definiáló morfizmus F*->*

  HProof, KProof: H és K homomorfizmusságát bizonyító tény.
  *)


  set (H:= proj1_sig h); set(K := proj1_sig k); set (ZMorph := projT2 z); set (XMorph:= projT2 x); set (YMorph := projT2 y).
  exists (H ∘ K).
  set (HProof := proj2_sig h); set (KProof := proj2_sig k).
  rewrite EF_comp_ax.


  (* bal oldali zárójel felbontása *)
  apply Eq_sim.
  apply Eq_trans with (g:=ZMorph ∘ EF_mor (H) ∘ EF_mor (K)).
  2: apply Eq_sim; apply assoc.
  apply Eq_sim.


  (* H homomorphism -> F(H)>>Z = (y>>H) csere *)
  apply Eq_sim.
  (*
  replace (EF_mor H >> ZMorph) with (YMorph >> H).
  2: apply Eq_sim; apply HProof.

  ez szerintem szebb lenne, de sajnos nem működik a felülírt ≡ operátorral :(
  *)
  apply Eq_trans with (g:=(H ∘ YMorph ∘ EF_mor (K))).
  2: apply Eq_sim; apply eq_2; apply HProof.

  (* két végén H van, csak előtte nem az *)

  (* bal oldal újrazárójelezése *)
  apply Eq_trans with (g:=(H ∘ (K ∘ XMorph))).
  apply Eq_sim; apply assoc.

  (* jobb oldal újrazárójelezése *)
  apply Eq_trans with (g:=((H ∘ (YMorph ∘ EF_mor (K))))).
  2 : apply assoc.

  (* H eltávolítása *)
  apply eq_1.

  (* K homomorfizmus *)
  apply Eq_sim.
  exact KProof.
Defined.

Theorem F_algebras_form_a_Category {C : Category} (F : @EndoFunctor C) : Category.
Proof.
  apply (cat_mk (@F_algebras_Obj C F) (@F_algebras_Hom C F) (@F_algebras_Id C F) (@F_algebras_Comp C F) (@F_algebras_EqMor C F)).

  (* (x->y) = (x->y) *)
  intros.
  apply Eq_ref.

  (* f=g; g=h -> f=h *)
  intros. 
  unfold F_algebras_EqMor in *.
  apply Eq_trans with (g0:=proj1_sig g).
  exact H.
  exact H0.

  (* f=g -> g=f *)
  intros.
  unfold F_algebras_EqMor in *.
  apply Eq_sim.
  exact H.

  (* f>>(g>>h)=(f>>g)>>h *)
  intros.
  unfold F_algebras_EqMor.
  unfold F_algebras_Hom in f, g, h.
  apply assoc.

  (* id_1: id>>f = f *)
  intros.
  unfold F_algebras_EqMor.
  apply id_1.

  (* id_2: f>>id = f *)
  intros.
  unfold F_algebras_EqMor.
  apply id_2.

  (* g=h -> f>>g = f>>h *)
  intros.
  unfold F_algebras_EqMor.
  apply eq_1.
  unfold F_algebras_EqMor in H.
  exact H.

  (* g=h -> g>>f = h>>f *)
  intros.
  unfold F_algebras_EqMor.
  apply eq_2.
  unfold F_algebras_EqMor in H.
  exact H.
Qed.
