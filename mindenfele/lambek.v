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

  eq: forall {x y z} (f g: Hom y z) (h i : Hom x y), EqMor f g /\ EqMor h i ->
        EqMor (Compose f h) (Compose g i);
}.
Print EqMor.


Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Notation "f ≡ g" := (EqMor f g) (at level 40, left associativity) :
type_scope.

(* Context {C : Category}.*)
(*
Setoid hell help: hint to Coq that this Eq_mor is an equivalence relation, so built-in commands can use it as such
*)

Require Import Coq.Setoids.Setoid.
Add Parametric Relation {C : Category} {A B: Obj} : (Hom A B) (EqMor)
  reflexivity proved by (Eq_ref)
  symmetry proved by (Eq_sim)
  transitivity proved by (Eq_trans)
  as eq_set_rel.

Add Parametric Morphism {C: Category} {a b c: @Obj C} : (@Compose C a b c)
  with signature (EqMor) ==> (EqMor) ==> (EqMor) as compose_keeps_equality.
Proof.
intros.
apply eq.
split.
exact H.
exact H0.
Qed.


Lemma eq_1 : forall {C: Category} {x y z} (f: Hom y z) (g h : Hom x y), EqMor g h ->
EqMor (Compose f g) (Compose f h).
Proof.
intros.
apply eq.
split.
reflexivity.
exact H.
Qed.

Lemma eq_2 : forall {C: Category} {x y z} (f: Hom x y) (g h : Hom y z), EqMor g h ->
        EqMor (Compose g f) (Compose h f).
Proof.
intros.
apply eq.
split.
exact H.
reflexivity.
Qed.


(* dependent data type - Endofunctor of a category *)
Class EndoFunctor {C : Category} := ef_mk {
  EF_obj : @Obj C -> @Obj C; (* object->object map *)
  EF_mor : forall {x y}, (Hom x y) -> (Hom (EF_obj x) (EF_obj y)); (* morphism->morphism map *)

  (* functor laws *)
  EF_keeps_id : forall {x}, EF_mor (Id x) ≡ Id (EF_obj x);
  EF_comp_ax : forall {x y z : @Obj C} {f g},
        @EF_mor x z (f ∘ g) ≡ ((@EF_mor y z f) ∘ (@EF_mor x y g));
  EF_proper: forall {x y: @Obj C} (f g: x→y), f≡g -> EF_mor f ≡ EF_mor g
  (* proper: morphism mapping is proper, i.e. it preservers equivalence *)
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
  fold Carrier.
  setoid_replace (@EF_mor C F Carrier Carrier (Id Carrier)) with (Id (EF_obj Carrier)).
  transitivity (Morphism).
  apply id_1.
  symmetry; apply id_2.
  apply EF_keeps_id.

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
  2: apply eq_2 with (g:=H∘YMorph) (h:=ZMorph ∘ EF_mor H); symmetry; apply HProof.


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
  
  intros.
  unfold F_algebras_EqMor.
  compute.
  unfold F_algebras_Comp.

  setoid_replace (proj1_sig f ∘ proj1_sig h) with (proj1_sig g ∘ proj1_sig i).
  reflexivity.
  apply eq.
  split.
  all: apply H.
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
symmetry.
symmetry.
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
setoid_replace (Id Fcarr) with (EF_mor (Id carr)).
symmetry.
transitivity (EF_mor (constr∘m')).
apply EF_proper.
symmetry.
auto.
rewrite EF_comp_ax.
exact (proj2_sig m).
symmetry.
apply EF_keeps_id.

fold m.
exact (invert_means_iso constr m' l_id_2 l_id_1).
Qed.


Class TermCat {C: Category} := {
 Terminal_obj : @Obj C;
 Terminal_mor : forall {x: @Obj C},  x → Terminal_obj;
 unique_terminal : forall {x: @Obj C} (f : x → Terminal_obj), f ≡ Terminal_mor
}.

Class CoProd {C: Category} := {
  Sum_obj : Obj -> Obj -> Obj;

  Sum_mor : forall {x1 x2 z} (f:x1 → z) (g:x2 → z), (Sum_obj x1 x2) → z;

  in_1 {x y} : x→(Sum_obj x y);
  in_2 {x y} : y→(Sum_obj x y);

  sum_ax : forall {x1 x2 z} (f1 : x1 → z) (f2 : x2 → z), 
    ((Sum_mor f1 f2) ∘ in_1 ≡ f1) /\ ((Sum_mor f1 f2) ∘ in_2 ≡ f2);
    
  sum_eq : forall {x1 x2 z} (g : Sum_obj x1 x2 → z),
    Sum_mor (g ∘ in_1) (g ∘in_2) ≡ g;

  sum_proper : forall {x1 x2 z} {h j: x2→z} (f g: x1→z), f≡g /\ h≡j -> Sum_mor f h ≡ Sum_mor g j;
}.



Class NatCat {C: Category} (TC: TermCat) := {
  N: Obj;
  N0 :  Terminal_obj → N;
  NS : N→N;
  nat_mor: forall (M: Obj) (z: Terminal_obj→M) (f: M→M), N→M;
  nat_mor_ax: forall (M: Obj) (z: Terminal_obj→M) (f: M→M), (nat_mor M z f)∘N0≡z /\ f ∘ (nat_mor M z f) ≡ ((nat_mor M z f) ∘ NS);
  nat_mor_uniq : forall (M: Obj) (z: Terminal_obj→M) (f: M→M) (g: N→M), g≡nat_mor M z f
}.

Add Parametric Morphism {C: Category} {CC: CoProd} {A B AB: @Obj C} : (@Sum_mor C CC A B AB)
  with signature (EqMor) ==> (EqMor) ==> (EqMor) as sum_mor_keeps_eq.
Proof.
intros.
apply sum_proper.
split.
exact H.
exact H0.
Qed.

#[refine]
Instance NatFunctor {C: Category} (CC: CoProd) (TC: TermCat) : EndoFunctor := {
  EF_obj := fun x => Sum_obj Terminal_obj x;
  EF_mor := fun {X Y} (f: X→Y) => Sum_mor (in_1) (in_2 ∘ f);
}.
Proof.
(* keeps id *)
intros.
rewrite id_1.
setoid_replace (@in_1 C CC Terminal_obj x) with ((Id (Sum_obj Terminal_obj x)) ∘ in_1).
2: symmetry; apply id_2.
setoid_replace (@in_2 C CC Terminal_obj x) with ((Id (Sum_obj Terminal_obj x)) ∘ in_2).
2: symmetry; apply id_2.
apply sum_eq.

(* keeps composition *)
intros.
(* second projection is in_2 ∘ f ∘ g *)
assert (((Sum_mor in_1 (@in_2 C CC Terminal_obj z ∘ f))∘(Sum_mor in_1 (in_2 ∘ g))) ∘ in_2 ≡ (in_2 ∘ f ∘ g)).
symmetry.
transitivity ((Sum_mor in_1 (@in_2 C CC Terminal_obj z ∘ f))∘((Sum_mor in_1 (in_2 ∘ g)) ∘ in_2)).
2: apply assoc.
transitivity ((Sum_mor in_1 (@in_2 C CC Terminal_obj z ∘ f))∘in_2∘g).
transitivity (@in_2 C CC Terminal_obj z ∘f∘g).
2: symmetry; apply eq_2; apply sum_ax.
reflexivity.
transitivity ((Sum_mor in_1 (@in_2 C CC Terminal_obj z ∘ f))∘(in_2∘g)).
symmetry; apply assoc.
symmetry.
apply eq_1.
apply sum_ax.
(* first projection is in_1 *)
assert (((Sum_mor in_1 (@in_2 C CC Terminal_obj z ∘ f))∘(Sum_mor in_1 (in_2 ∘ g))) ∘ in_1 ≡ in_1).
symmetry.
transitivity ((Sum_mor in_1 (@in_2 C CC Terminal_obj z ∘ f))∘((Sum_mor in_1 (in_2 ∘ g)) ∘ in_1)).
transitivity ((Sum_mor in_1 (@in_2 C CC Terminal_obj z ∘ f))∘in_1).
2: symmetry; apply eq_1; apply sum_ax.
symmetry; apply sum_ax.
apply assoc.
(* it's equal to it's first and second projection's sum morphism *)
set (ugly := ((Sum_mor in_1 (@in_2 C CC Terminal_obj z ∘ f))∘((Sum_mor in_1 (in_2 ∘ g))))).
fold ugly in H.
fold ugly in H0.
transitivity (Sum_mor (ugly ∘ in_1) ((ugly ∘ in_2))).
2: apply sum_eq.
(* since we know them, just replace *)
setoid_replace (ugly ∘ in_1) with (@in_1 C CC Terminal_obj z).
2: apply H0.
setoid_replace (ugly ∘ in_2) with (@in_2 C CC Terminal_obj z ∘ (f ∘ g)).
reflexivity. (*goal is proved, rest is just proof of valid replace*)
setoid_replace ((@in_2 C CC Terminal_obj z) ∘ (f ∘ g)) with ((@in_2 C CC Terminal_obj z) ∘ f∘g).
apply H.
apply assoc.


(* proper *)
intros.
setoid_replace (f) with (g).
reflexivity.
exact H.
Defined.

Lemma ComponentwiseEqual {Cat: Category} {CC: CoProd} {A B C} (f1 f2: A→B) (g1 g2: C→B) : f1≡f2/\g1≡g2 -> Sum_mor f1 g1 ≡ Sum_mor f2 g2.
Proof.
intros.
setoid_replace f1 with f2.
setoid_replace g1 with g2.
reflexivity.
all: apply H.
Qed.


Lemma ComponentwiseEqual2 {Cat: Category} {CC: CoProd} {X1 X2 S} (f1: X1→S) (f2: X2→S) (g: Sum_obj X1 X2→S) : f1≡(g∘in_1)/\f2≡(g∘in_2) -> Sum_mor f1 f2 ≡ g.
Proof.
intros.
setoid_replace f1 with (g∘in_1).
setoid_replace f2 with (g∘in_2).
apply sum_eq.
all: apply H.
Qed.

Lemma proj1_sig_eq {cat: Category} {F: EndoFunctor} {X Y : F_algebras_Obj F} {A B: F_algebras_Hom F X Y} : proj1_sig A ≡ proj1_sig B -> F_algebras_EqMor F X Y A B.
Proof.
auto.
Qed.

#[refine]
Instance InitNat (C: Category) (TC: @TermCat C) (NC: @NatCat C TC) (CC: @CoProd C) : @InitCat (falg_cat C (NatFunctor CC TC)) := {
(* initial *)

}.
Proof.
  (* initial Nat Object *)
  exists (@N C TC NC).  
  (* we need the constructor morphism! *)
  exact (Sum_mor N0 NS).
  set (Nat := (existT (constructor_morphism (NatFunctor CC TC)) N (Sum_mor N0 NS))).
  set (NatMor := projT2 Nat).
  set (NatObj := projT1 Nat).  
  (* now we need a morphism from this to every other nat-like *)
  intros.
  set (ConstrX := projT2 x).
  set (CarrX := projT1 x).
  set (NatNatMor := nat_mor (CarrX) (ConstrX ∘ in_1) (ConstrX ∘ in_2)).
  (* Nat says we have a morphism, but needs the morphisms of this nat-like, but they are in a combined form in it's constructo *)
  exists (NatNatMor).
  (* need to prove that it's a homo *)
  unfold is_homomorphism.
  fold NatMor ConstrX.
  transitivity (ConstrX ∘ (Sum_mor (@in_1 C CC Terminal_obj CarrX) (in_2 ∘ NatNatMor))).
  apply eq_1.
  reflexivity.
  setoid_replace NatMor with (Sum_mor N0 NS).
  2: reflexivity.
  set (z:= ConstrX ∘ in_1).
  set (f:= ConstrX ∘ in_2).
  setoid_replace ConstrX with (Sum_mor z f).
  2: symmetry; apply sum_eq.
  set (leftSide := Sum_mor z f ∘ Sum_mor in_1 (in_2 ∘ NatNatMor)). 
  transitivity (Sum_mor (leftSide∘in_1) (leftSide∘in_2)).
  symmetry; apply sum_eq.
  setoid_replace (leftSide∘in_1) with (z).
  setoid_replace (leftSide∘in_2) with (f∘NatNatMor).
  transitivity (Sum_mor (NatNatMor∘N0) (NatNatMor ∘ NS)).
  apply ComponentwiseEqual.
  split.
  symmetry;apply nat_mor_ax.
  apply nat_mor_ax.
  apply ComponentwiseEqual2.
  split.
  transitivity (NatNatMor ∘ (Sum_mor N0 NS ∘ in_1)).
  apply eq_1.
  symmetry.
  apply sum_ax.
  apply assoc.
  transitivity (NatNatMor ∘ (Sum_mor N0 NS ∘ in_2)).
  apply eq_1.
  symmetry.
  apply sum_ax.
  apply assoc.

  (*
    proove Sum_mor z f ∘ Sum_mor in_1 (in_2 ∘ NatNatMor) ∘ in_2 ≡ (f ∘ NatNatMor) 
    Just always reduct with in_2 til finished - takes a few associativities
  *)
  unfold leftSide.
  transitivity (Sum_mor z f ∘ (Sum_mor in_1 (in_2 ∘ NatNatMor) ∘ in_2)).
  symmetry; apply assoc.
  transitivity (Sum_mor z f ∘ (in_2 ∘ NatNatMor)).
  apply eq_1; apply sum_ax.
  transitivity (Sum_mor z f ∘ in_2 ∘ NatNatMor).
  apply assoc.
  apply eq_2.
  apply sum_ax.

  (* 
    proove Sum_mor z f ∘ Sum_mor in_1 (in_2 ∘ NatNatMor) ∘ in_1 ≡ z
    similar to before
  *)
  unfold leftSide.
  transitivity (Sum_mor z f ∘ (Sum_mor in_1 (in_2 ∘ NatNatMor) ∘ in_1)).
  symmetry; apply assoc.
  transitivity (Sum_mor z f ∘ in_1).
  apply eq_1; apply sum_ax.
  apply sum_ax.

  (* uniqness - our morphism is the only one *)
  intros.
  apply (@proj1_sig_eq C (NatFunctor CC TC)).
  apply (nat_mor_uniq (projT1 x) (projT2 x ∘ in_1) (projT2 x ∘ in_2)).
  (* saw that crazy wall-of-text after intros? Took me some time to decipher what it means...*)
Defined.


Definition NatIsVeryCool (C: Category) (TC: @TermCat C) (NC: @NatCat C TC) (CC: @CoProd C) := @Lambek C (NatFunctor CC TC) (InitNat C TC NC CC).
Print NatIsVeryCool.
