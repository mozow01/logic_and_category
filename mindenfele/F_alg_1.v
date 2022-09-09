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

Require Import Coq.Setoids.Setoid.
Add Parametric Relation {C : Category} {A B: Obj} : (Hom A B) (EqMor)
  reflexivity proved by (Eq_ref)
  symmetry proved by (Eq_sim)
  transitivity proved by (Eq_trans)
  as eq_set_rel.


(* dependent data type - Endofunctor of a category *)
Class EndoFunctor {C : Category} := {

EF_obj : @Obj C -> @Obj C;

EF_mor : forall {x y}, (Hom x y) -> (Hom (EF_obj x) (EF_obj y));

(* functor laws *)
EF_keeps_id : forall {x}, EF_mor (Id x) = Id (EF_obj x);
EF_comp_ax : forall {x y z : @Obj C} {f g},
      @EF_mor x z (f ∘ g) = (@EF_mor y z f) ∘ (@EF_mor x y g);
EF_proper: forall {x y: @Obj C} (f g: x→y), f≡g -> EF_mor f ≡ EF_mor g
}.



Add Parametric Morphism {C: Category} {F: @EndoFunctor C} {A B: @Obj C} {f: Hom A B} : (@EF_mor C F A B)
  with signature (EqMor) ==> (EqMor) as ef_keeps_equality.
Proof.
intros.
exact (EF_proper x y H).
Qed.

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


Definition is_homomorphism {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) (y : F_algebras_Obj F) 
 :=  (fun (f : @Hom C (projT1 x) (projT1 y) ) =>  ((projT2 y) ∘ (EF_mor f )) ≡ (f ∘ (projT2 x) ) ).
Definition F_algebras_Hom {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) (y : F_algebras_Obj F) 
:= (sig (is_homomorphism F x y)).
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
  unfold is_homomorphism.
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
  unfold is_homomorphism.
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

#[refine]
Instance falg_cat `(C : Category, F : @EndoFunctor C) : Category := {
  Obj:= @F_algebras_Obj C F;
  Hom:= @F_algebras_Hom C F;
  Id := @F_algebras_Id C F;
  Compose:= @F_algebras_Comp C F;
  EqMor:=@F_algebras_EqMor C F;
}.
Proof.

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
Defined.

Definition mapped_f_algebra {C: Category} (F: @EndoFunctor C) (alg: F_algebras_Obj F): F_algebras_Obj F.
Proof.
set (X := projT1 alg) in *.
set (morphism := projT2 alg).
set (FX := EF_obj X).
set (FFX := EF_obj FX).
set (Fm := EF_mor morphism).
unfold F_algebras_Obj.
exists (FX).
unfold object_is_carrier.
exact Fm.
Defined.

Definition is_isomorphism {C: Category} {A B: @Obj C} (mor: Hom A B) : Prop := exists mor2, mor>>mor2 ≡ Id A /\ mor2>>mor ≡ Id B.

Class InitCat {C: Category} := {
(* initial *)

 Initial_obj : @Obj C;

 Initial_mor : forall {x: @Obj C},  Initial_obj → x;

  unique_initial : forall {x: @Obj C} (f : Initial_obj → x), f ≡ Initial_mor
}.
Check Initial_obj.

Definition underlying_morphism {C: Category} (F: @EndoFunctor C) {A B} (mor: @F_algebras_Hom C F A B) : Hom (projT1 A) (projT1 B):= proj1_sig mor.


Theorem invert_means_iso {C: Category} {A B: @Obj C} (i: Hom A B) (j: Hom B A) (P1: (i>>j≡Id A)) (P2: (j>>i≡Id B)): is_isomorphism i.
unfold is_isomorphism.
exists j.
split.
exact P1.
exact P2.
Qed. 

Theorem projection_eq {C: Category} (F: @EndoFunctor C) (A B: F_algebras_Obj F) (f g : F_algebras_Hom F A B) (P: F_algebras_EqMor F A B f g) : proj1_sig f ≡ proj1_sig g.
auto.
Defined.

Theorem Lambek {C : Category} (F : @EndoFunctor C) (initob: @InitCat (falg_cat C F)) : is_isomorphism (projT2 (@Initial_obj (falg_cat C F) initob)).
set (cat_of_fs := (falg_cat C F)).
set (initial_algebra:=(@Initial_obj (falg_cat C F) initob)).
set (i:=projT1 initial_algebra).
set (j:=projT2 initial_algebra) in *. 
set (other_obj := mapped_f_algebra F initial_algebra).
set (m := @Initial_mor cat_of_fs initob other_obj).
set (m' := underlying_morphism F m).
set (Fi:= EF_obj i).
set (FFi:= EF_obj Fi).
set (Fm' := EF_mor m').
set (Fj := projT2 other_obj).

(* 2 ablakos diagram comutes *)
assert (D_COMMUTES :j>>(m'>>j) ≡ (Fm'>>Fj)>>j).
apply Eq_sim.
apply Eq_trans with (g:=(j>>m')>>j).
apply eq_1.
exact (proj2_sig m).
apply assoc.

set (complex_id := m'>>j).

(* need to create a homomorphism from complex_id_homo as it's now proven to be one *)

(* proove that m'>>j is a homomorphism *)
assert (COMPOSITE_IS_HOMOMORPHISM : j ∘ (EF_mor complex_id ) ≡ (complex_id ∘ j)).
apply Eq_sim.
unfold complex_id.
rewrite EF_comp_ax.
exact D_COMMUTES.

(* now with the proof we can create the object *)
set (that_homo := exist (is_homomorphism F initial_algebra initial_algebra) complex_id COMPOSITE_IS_HOMOMORPHISM).


(* now need to show that that_homo is also equiv to idi *)

(* we use the fact that the algebra is initial to proove that the two homomorphisms equal *)
set (initial_morphism :=(@Initial_mor cat_of_fs initob initial_algebra)).
assert (that_homo ≡ Id initial_algebra).
apply Eq_trans with (g:=initial_morphism).
apply unique_initial.
apply Eq_sim.
apply unique_initial.

(* but that also implies that the underlying morphisms also equal *)
assert (l_id_1 : m'>>j≡Id i).
auto.

(* now do the opposite - show that j>>m' ≡ Id Fi *)
(* we need to proove that it' s a hom as well *)
assert (l_id_2 : j>>m' ≡  Id Fi  ).
symmetry.
apply Eq_trans with (g:=EF_mor (Id i)).
apply Eq_sim.
replace (EF_mor (Id i)) with (Id Fi).
apply Eq_ref.
symmetry.
apply EF_keeps_id.
apply Eq_trans with (g:=EF_mor (m'>>j) ).
apply Eq_sim.
apply EF_proper.
exact l_id_1.
rewrite EF_comp_ax.
exact (proj2_sig m).

fold m.
exact (invert_means_iso j m' l_id_2 l_id_1).
Qed.

