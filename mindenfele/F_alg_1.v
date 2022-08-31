(*The definition of Category in the Monoid Hell (aka categotry with morphism equiality) *)

Class Category := cat_mk {
  Obj : Type;

  uHom := Type : Type;

  Hom : Obj -> Obj -> uHom;

  Id : forall x, Hom x x;

  Dom {x y} (f: Hom x y) := x;

  CoDom {x y} (f: Hom x y) := y;

  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;

  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;

  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h 
         -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;

  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);

  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f ;

  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f ;

  eq_1 : forall {x y z} (f: Hom y z) (g h : Hom x y), EqMor g h ->
        EqMor (Compose f g) (Compose f h);
  eq_2 : forall {x y z} (f: Hom x y) (g h : Hom y z), EqMor g h ->
        EqMor (Compose g f) (Compose h f);

}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Notation "f ≡ g" := (EqMor f g) (at level 40, left associativity) :
type_scope.

Context {C : Category}.


Class EndoFunctor {C : Category} := {

EF_obj : @Obj C -> @Obj C;

EF_mor : forall {x y}, (Hom x y) -> (Hom (EF_obj x) (EF_obj y));

EF_id_ax : forall {x}, EF_mor (Id x) = Id (EF_obj x);

EF_comp_ax : forall {x y z : @Obj C} {f g},
      @EF_mor x z (f ∘ g) = (@EF_mor y z f) ∘ (@EF_mor x y g)
}.

Class F_algebra {C : Category} (F : @EndoFunctor C) := {

Carr_F_alg : @Obj C;

Mor_F_alg : Hom ((@EF_obj C F) Carr_F_alg) Carr_F_alg
}.



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

Definition F_algebras_Obj {C : Category} (F : @EndoFunctor C) := (@sigT (@Obj C) (fun (x:@Obj C) => Hom (@EF_obj C F x) x) ) : Type.

Definition F_algebras_Hom {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) (y : F_algebras_Obj F) 
:= (sig (fun (f : @Hom C (projT1 x) (projT1 y) ) =>  ((projT2 y) ∘ (EF_mor f )) ≡ (f ∘ (projT2 x) ) )).

Definition F_algebras_EqMor {C : Category} (F : @EndoFunctor C) (x y : F_algebras_Obj F) (f g : F_algebras_Hom F x y) := (proj1_sig f) ≡ (proj1_sig g).


Definition F_algebras_Id {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) : @F_algebras_Hom C F x x.
unfold F_algebras_Hom.
exists (@Id C (projT1 x)).
rewrite EF_id_ax.
assert (H: (projT2 x ∘ Id (EF_obj (projT1 x))) ≡ projT2 x).
Kitten.
(*apply id_1.*)
assert (H1: (projT2 x ) ≡ (projT2 x ∘ Id (EF_obj (projT1 x)))).
Kitten.
(*apply Eq_sim.
exact H.*)
Kitten.
apply Eq_trans with (g:=(projT2 x)).
2 : {
assert (K: ((Id (projT1 x) ∘ projT2 x) ≡ projT2 x)).
all: Kitten. }
apply Eq_trans with (g:=(projT2 x)).
2 : { Kitten. }
Kitten.
Defined.

Definition F_algebras_Comp {C : Category} (F : @EndoFunctor C) (x y z : F_algebras_Obj F)
(h : F_algebras_Hom F y z ) (k : F_algebras_Hom F x y ) : F_algebras_Hom F x z.
unfold F_algebras_Hom.
unfold F_algebras_Hom in h, k.
exists ((proj1_sig h) ∘ (proj1_sig k)).
assert (H : (projT2 z ∘ EF_mor (proj1_sig h)) ≡ ((proj1_sig h) ∘ projT2 y)).
exact (proj2_sig h).
assert (K : (projT2 y ∘ EF_mor (proj1_sig k)) ≡ ((proj1_sig k) ∘ projT2 x)).
exact (proj2_sig k).
rewrite EF_comp_ax.
assert (L : (projT2 z ∘ (EF_mor (proj1_sig h) ∘ EF_mor (proj1_sig k))
) ≡ ((projT2 z ∘ EF_mor (proj1_sig h) ∘ EF_mor (proj1_sig k)))).
apply assoc.
apply Eq_sim.
apply Eq_trans with (g:=projT2 z ∘ EF_mor (proj1_sig h) ∘ EF_mor (proj1_sig k)).
2 : {
Kitten. }
apply Eq_sim.
assert (M1 : (projT2 z ∘ EF_mor (proj1_sig h) ∘ EF_mor (proj1_sig k) ) ≡ ((proj1_sig h ∘ projT2 y) ∘ EF_mor (proj1_sig k))).
apply eq_2 with (g:=projT2 z ∘ EF_mor (proj1_sig h)) (h:= proj1_sig h ∘ projT2 y) (f:=EF_mor (proj1_sig k)).
auto.
apply Eq_sim. 
apply Eq_trans with (g:=(proj1_sig h ∘ projT2 y ∘ EF_mor (proj1_sig k))).
2: {
Kitten. }
assert (M2 : (projT2 y ∘ EF_mor (proj1_sig k)) ≡ (proj1_sig k ∘ projT2 x)).
exact (proj2_sig k).
assert (L1 : (proj1_sig h ∘ projT2 y ∘ EF_mor (proj1_sig k))
 ≡ (proj1_sig h ∘ (projT2 y ∘ EF_mor (proj1_sig k)))).
apply Eq_sim.
apply assoc.
apply Eq_trans with (g:=((proj1_sig h ∘ (projT2 y ∘ EF_mor (proj1_sig k))))).
2 : { 
apply Eq_sim.
apply L1. }
assert (L2 : (proj1_sig h ∘ proj1_sig k ∘ projT2 x)
 ≡ (proj1_sig h ∘ (proj1_sig k ∘ projT2 x))).
apply Eq_sim.
apply assoc.
apply Eq_trans with (g:=(proj1_sig h ∘ (proj1_sig k ∘ projT2 x))).
2: {
Kitten. }
auto.
Defined.


Theorem F_algebras_form_a_Cat {C : Category} (F : @EndoFunctor C) : Category.
Proof.
apply (cat_mk (@F_algebras_Obj C F) (@F_algebras_Hom C F) (@F_algebras_Id C F) (@F_algebras_Comp C F) (@F_algebras_EqMor C F) ).
intros.
apply Eq_ref.
intros. 
unfold F_algebras_EqMor.
unfold F_algebras_EqMor in H, H0.
apply Eq_trans with (g:=proj1_sig g).
all: auto.
intros.
unfold F_algebras_EqMor.
unfold F_algebras_EqMor in H.
apply Eq_sim.
auto.
intros.
unfold F_algebras_EqMor.
unfold F_algebras_Hom in f, g, h.
apply assoc.
intros.
unfold F_algebras_EqMor.
apply id_1.
intros.
unfold F_algebras_EqMor.
apply id_2.
intros.
unfold F_algebras_EqMor.
apply eq_1.
unfold F_algebras_EqMor in H.
auto.
intros.
unfold F_algebras_EqMor.
apply eq_2.
unfold F_algebras_EqMor in H.
auto.
Qed.