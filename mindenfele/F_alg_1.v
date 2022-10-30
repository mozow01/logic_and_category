(*The definition of Category in the Setoid Hell (aka categotry with morphism equiality) *)

Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom; (* morphism constructor *)
  Id : forall x, Hom x x; (* Id x := Hom x x *)
  Dom {x y} (f: Hom x y) := x; (* domain operator *)
  CoDom {x y} (f: Hom x y) := y; (* codomain operator *)
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z); (* morhism compose operator *)
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;


  (* equivalence relation properties *)
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

Notation "f ≡ g" := (EqMor f g) (at level 40, left associativity) :
type_scope.

Context {C : Category}.

(*
Setoid hell help: hint to Coq that this Eq_mor is an equivalence relation, so built-in commands can use it as such
*)

Require Import Coq.Setoids.Setoid.
Add Parametric Relation {C : Category} {A B: Obj} : (Hom A B) (EqMor)
  reflexivity proved by (Eq_ref)
  symmetry proved by (Eq_sim)
  transitivity proved by (Eq_trans)
  as eq_set_rel.




(* dependent data type - Endofunctor of a category *)
Class EndoFunctor {C : Category} := {
  EF_obj : @Obj C -> @Obj C; (* object->object map *)
  EF_mor : forall {x y}, (Hom x y) -> (Hom (EF_obj x) (EF_obj y)); (* morphism->morphism map *)

  (* functor laws *)
  EF_keeps_id : forall {x}, EF_mor (Id x) = Id (EF_obj x);
  EF_comp_ax : forall {x y z : @Obj C} {f g},
        @EF_mor x z (f ∘ g) = (@EF_mor y z f) ∘ (@EF_mor x y g);
  EF_proper: forall {x y: @Obj C} (f g: x→y), f≡g -> EF_mor f ≡ EF_mor g
  (* proper: morphism mapping is proper, i.e. it preservers equivalence *)
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
           | [ H : ?P ≡ ?Q |- ?Q ≡ ?P ] => symmetry
           | [ |- (?P ∘ ?Q) ≡ (?P ∘ ?R) ] => apply eq_1
           | [ |- ( ?Q ∘ ?P ) ≡ (?R ∘ ?P) ] => apply eq_1
         end.


Definition constructor_morphism {C: Category} (F: @EndoFunctor C) := fun (x:@Obj C) => Hom (@EF_obj C F x) x.
Definition F_algebras_Obj {C : Category} (F : @EndoFunctor C) := (@sigT (@Obj C) (@constructor_morphism C F ) ) : Type.
(*
Given object & endofunctor, the set of F-algebras defined by these is the set of (X, a) pairs whose X is an object in C (so first type of pair os Object type in C) and a is a morhphism F X -> X. The sets are not restrictive, afaik only the types must be equal, so if you have a morphism NOT IN C, you could still consider it as an F_algebras_obj.
*)


Definition is_homomorphism {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) (y : F_algebras_Obj F) 
 :=  (fun (f : @Hom C (projT1 x) (projT1 y) ) =>  ((projT2 y) ∘ (EF_mor f )) ≡ (f ∘ (projT2 x) ) ).
Definition F_algebras_Hom {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) (y : F_algebras_Obj F) 
:= (sig (is_homomorphism F x y)).
(*
morphisms between two f-algebras are mophisms between the carries that also satisfy the law of the square commuting, so a: F A -> A and b: F B -> B morphisms and associated F-algebras, the morphism x: A->B of C is also a morphism between the F-algebras if F x: F A -> F B and b ∘ F x = x ∘ a
*)


Definition F_algebras_EqMor {C : Category} (F : @EndoFunctor C) (x y : F_algebras_Obj F) (f g : F_algebras_Hom F x y) := (proj1_sig f) ≡ (proj1_sig g).
(* two morphisms between two f-algebras are equal if the underlying morphisms in C equal *)


(* construct ID morphism *)
Definition F_algebras_Id {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) : @F_algebras_Hom C F x x. (* := @existT (@Obj C) (@constructor_morphism C F) (projT1 x) (Hom (projT1 x) (projT1 x)).*)
  unfold F_algebras_Hom.
  set (Carrier:=projT1 x) in *; set (Morphism := projT2 x) in *.
  (* Id of Carrier defines such a morphism for F-algebras *)
  exists (@Id C Carrier).
  unfold is_homomorphism.
  rewrite EF_keeps_id.
  transitivity (Morphism).
  apply id_1.
  symmetry; apply id_2.
Defined.


(* 
Composistion of two morphisms between F-algebras. Must exists, as the underlying morphisms in C can also compose, so we have to proove this
*)
Definition F_algebras_Comp {C : Category} (F : @EndoFunctor C) (x y z : F_algebras_Obj F)
(h : F_algebras_Hom F y z ) (k : F_algebras_Hom F x y ) : F_algebras_Hom F x z.
  unfold F_algebras_Hom.

  (*
  Aliases:
  H: homomorphism 1 (Y->Z)
  K: homomorphism 2 (X->Y)
  XMorph, YMorph, ZMorph: constructors of X,Y,Z F-algebras 
  HProof, KProof: proofs of H and K being homomorphisms
  *)


  set (H:= proj1_sig h); set(K := proj1_sig k); set (ZMorph := projT2 z); set (XMorph:= projT2 x); set (YMorph := projT2 y).
  exists (H ∘ K).
  set (HProof := proj2_sig h); set (KProof := proj2_sig k).
  unfold is_homomorphism.
  rewrite EF_comp_ax.

  (* Zmorph ∘ (FH ∘ FK) -> ZMorph ∘ FH ∘ FK *)
  symmetry.
  transitivity (ZMorph ∘ EF_mor (H) ∘ EF_mor (K)).
  2: symmetry; apply assoc.
  symmetry.


  (* H is a homomorphism -> swap F(H)>>Z = (y>>H) *)
  symmetry.
  transitivity (H ∘ YMorph ∘ EF_mor (K)).
  2: symmetry; apply eq_2; apply HProof.


  (* H∘(...a)≡H∘(...b) -> (...a)≡(...b) *)
  (* left side *)
  transitivity (H ∘ (K ∘ XMorph)).
  symmetry; apply assoc.

  (* right side *)
  transitivity (H ∘ (YMorph ∘ EF_mor (K))).
  2 : apply assoc.

  (* remove H *)
  apply eq_1.

  (* K is a homomrphism *)
  symmetry.
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
  unfold F_algebras_EqMor.
  reflexivity.

  (* f=g; g=h -> f=h *)
  intros. 
  unfold F_algebras_EqMor in *.
  transitivity (proj1_sig g).
  exact H.
  exact H0.

  (* f=g -> g=f *)
  intros.
  unfold F_algebras_EqMor in *.
  symmetry.
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
unfold constructor_morphism.
exact Fm.
Defined.

Definition is_isomorphism {C: Category} {A B: @Obj C} (mor: Hom A B) : Prop := exists mor2, mor2 ∘ mor ≡ Id A /\ mor ∘ mor2 ≡ Id B.

Class InitCat {C: Category} := {
(* initial *)

 Initial_obj : @Obj C;

 Initial_mor : forall {x: @Obj C},  Initial_obj → x;

  unique_initial : forall {x: @Obj C} (f : Initial_obj → x), f ≡ Initial_mor
}.

Definition underlying_morphism {C: Category} (F: @EndoFunctor C) {A B} (mor: @F_algebras_Hom C F A B) : Hom (projT1 A) (projT1 B):= proj1_sig mor.


Theorem invert_means_iso {C: Category} {A B: @Obj C} (i: Hom A B) (j: Hom B A) (P1: (j∘i≡Id A)) (P2: (i∘j≡Id B)): is_isomorphism i.
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
set (carr:=projT1 initial_algebra).
set (constr:=projT2 initial_algebra) in *. 
set (other_obj := mapped_f_algebra F initial_algebra).
set (m := @Initial_mor cat_of_fs initob other_obj).
set (m' := underlying_morphism F m).
set (Fcarr:= EF_obj carr).
set (FFcarr:= EF_obj Fcarr).
set (Fm' := EF_mor m').
set (Fconstr := projT2 other_obj).

assert (M_IS_HOMO :(constr∘m')∘constr ≡ (constr∘(Fconstr∘Fm'))).
symmetry.
transitivity (constr∘(m'∘constr)).
apply eq_1.
exact (proj2_sig m).
apply assoc.

set (comp_id' := constr∘m').

(* need to create a homomorphism from complex_id_homo as it's now proven to be one *)

(* proove that m'>>j is a homomorphism *)
assert (COMPOSITE_IS_HOMOMORPHISM : constr ∘ (EF_mor comp_id' ) ≡ (comp_id' ∘ constr)).
symmetry.
unfold comp_id'.
rewrite EF_comp_ax.
exact M_IS_HOMO.

(* now with the proof we can create the object *)
set (comp_id := exist (is_homomorphism F initial_algebra initial_algebra) comp_id' COMPOSITE_IS_HOMOMORPHISM).


(* now need to show that that_homo is also equiv to id *)

(* we use the fact that the algebra is initial to proove that the two homomorphisms equal *)
set (initial_morphism :=(@Initial_mor cat_of_fs initob initial_algebra)).
assert (comp_id ≡ Id initial_algebra).
transitivity (initial_morphism).
apply unique_initial.
symmetry.
apply unique_initial.

(* but that also implies that the underlying morphisms also equal *)
assert (l_id_1 : constr∘m'≡Id carr).
auto.

(* now do the opposite - show that j>>m' ≡ Id Fi *)
(* we need to proove that it' s a hom as well *)
assert (l_id_2 : m'∘constr ≡  Id Fcarr  ).
symmetry.
transitivity (EF_mor (Id carr)).
symmetry.
replace (EF_mor (Id carr)) with (Id Fcarr).
reflexivity.
symmetry.
apply EF_keeps_id.
transitivity (EF_mor (constr∘m') ).
symmetry.
apply EF_proper.
exact l_id_1.
rewrite EF_comp_ax.
exact (proj2_sig m).

fold m.
exact (invert_means_iso constr m' l_id_2 l_id_1).
Qed.
