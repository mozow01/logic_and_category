Class Category := cat_mk {
  uHom := Type : Type;
  Obj : Type;
  Hom : Obj -> Obj -> uHom; 
  Id : forall x, Hom x x; 
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z); 

  (* equivalence *)
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;

  (* equivalence properties *)
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h 
         -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;

  (* associativity, identity*)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f;
  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f;
  
  (* congruence *)
  eq: forall {x y z} (f g: Hom y z) (h i : Hom x y), EqMor f g /\ EqMor h i ->
        EqMor (Compose f h) (Compose g i);
}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Notation "f ≡ g" := (EqMor f g) (at level 40, left associativity) :
type_scope.

Require Import List Arith Peano Lia.
Import ListNotations.


Inductive Typ : Set :=
  | Arr : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm.

Definition Cntxt := list Typ.

Definition CntxExt (A : Typ) Γ  := A :: Γ.

Infix "▷" := CntxExt (at level 20, right associativity).


Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | STT_hypO : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | STT_hypS :
      forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | STT_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Arr A B)
  | STT_app :
      forall Γ t s A B,
      Tyty Γ t (Arr A B) -> Tyty Γ s A -> Tyty Γ (app t s) B.

Notation "G '⊢' t '[:]' A" := (Tyty G t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Fixpoint lift_aux (n : nat) (t : Trm) (k : nat) {struct t} : Trm :=
   match t with
     | hyp i => match (le_gt_dec k i) with
                  | left _ => (* k <= i *) hyp (i + n)
                  | right _ => (* k > i *) hyp i
                end
     | app M N => app (lift_aux n M k) (lift_aux n N k)
     | lam A M => lam A (lift_aux n M (S k))
   end.

Lemma liftappaux (n : nat) (M N : Trm) (k : nat) : lift_aux n (app M N) k = app (lift_aux n M k) (lift_aux n N k).
Proof.
simpl; auto.
Defined.

Definition lift t n := lift_aux n t 0.

Lemma liftapp (n : nat) (M N : Trm) : lift (app M N) n  = app (lift M n) (lift N n).
Proof.
simpl; auto.
Defined.

Lemma lifthypS (n : nat) (i : nat) : lift (hyp i) n = hyp (i + n).
Proof.
induction i.
compute. auto.
unfold lift.
simpl. auto.
Defined.

Lemma weakening_hyp : forall Γ A B n, Tyty Γ (hyp n) B -> Tyty (A :: Γ) (lift (hyp n) 1) B.
Proof.
  intros Γ A B i H.
  assert (Hlift: lift (hyp i) 1 = hyp (S i)).
    { unfold lift. simpl. destruct (le_gt_dec 0 i).
      - rewrite Nat.add_1_r. reflexivity.
      - exfalso. lia.
    }
  rewrite Hlift.
  apply STT_hypS; auto.
Defined.

Lemma liftlam_aux (n : nat) (k : nat) (A : Typ) (M : Trm) : lift_aux n (lam A M) k = lam A (lift_aux n M (S k)).
Proof.
simpl; auto.
Defined.

Lemma switch : forall (A B C : Typ) (Γ : Cntxt)  (t : Trm), (A :: B :: Γ ⊢ lift_aux 1 t 0 [:] C) -> (B :: A :: Γ ⊢ lift_aux 1 t 1 [:] C).
Proof.
intros.
induction t.
inversion H.
simpl in H.
Admitted.

Lemma weakening : forall t, forall Γ B, Tyty Γ t B -> forall A, Tyty (A :: Γ) (lift t 1) B.
Proof.
   induction t.
   1: { intros. apply weakening_hyp.
        auto. }
   2: { intros. inversion H. rewrite liftapp.
        assert (K1: A :: Γ ⊢ (lift t1 1) [:] Arr A0 B).
        apply IHt1. auto.
        assert (K2: A :: Γ ⊢ (lift t2 1) [:] A0).
        apply IHt2. auto.
        apply STT_app with (A:=A0) (B:=B).
        all: auto. }
   intros.
   unfold lift.
   unfold lift in IHt.
   rewrite liftlam_aux.
   rename t into A0.
   inversion H.
   apply STT_lam.
   assert (K:
      A :: A0 :: Γ ⊢ lift_aux 1 t0 0 [:] B0).
   intros.
   apply IHt.
   auto.
(*itt kell a switch:
K : A :: A0 :: Γ ⊢ lift_aux 1 t0 0 [:] B0
______________________________________(1/1)
A0 :: A :: Γ ⊢ lift_aux 1 t0 1 [:] B0
*)
    



(* Lemma weakening : forall Γ t, forall B, Tyty Γ t B -> forall A, Tyty (A :: Γ) (lift t 1) B.
Proof.
   intros Γ t.
   induction t.
   1: { intros. apply weakening_hyp.
        auto. }
   2: { intros. inversion H. rewrite liftapp.
        assert (K1: A :: Γ ⊢ (lift t1 1) [:] Arr A0 B).
        apply IHt1. auto.
        assert (K2: A :: Γ ⊢ (lift t2 1) [:] A0).
        apply IHt2. auto.
        apply STT_app with (A:=A0) (B:=B).
        all: auto. }
   intros.
   unfold lift.
   rewrite liftlam_aux. 
   apply STT_lam.
*)


 

Definition Obj_STT := Typ.

Definition Hom_STT (x y : Obj_STT) := { t : Trm | ⊢ t [:] (Arr x y)}.

Lemma Id_STT (x : Obj_STT) : { t : Trm | ⊢ t [:] (Arr x x)}.
Proof.
exists (lam x (hyp 0)).
apply STT_lam.
apply STT_hypO.
Defined.

(* (fun (A B C : Prop)(p : A->B)(q : B->C)(H : A) => q (p H)): A->C *)

Lemma Compose_STT (x y z : Obj_STT) : (Hom_STT y z) -> (Hom_STT x y) -> (Hom_STT x z).
Proof.
intros.
unfold Hom_STT in H, H0.
unfold Hom_STT.
elim H.
intros.
elim H0.
intros.
assert (K1 : [ x ] ⊢ (hyp 0) [:] x).
apply STT_hypO.
apply STT_weak with (A:=x) (B:=Arr x y) ( Γ:= nil ) in p0.
assert (K2 : [ x ] ⊢ app (weak x1) (hyp 0) [:] y).
apply STT_app with (A:=x) (B:=y).
all: auto.
assert (K3 : [x] ⊢ weak x0 [:] Arr y z).
apply STT_weak with (A:=x) (B:=Arr y z) ( Γ:= nil ).
auto.
assert (K4 : [x] ⊢ app (weak x0) (app (weak x1) (hyp 0)) [:] z).
apply STT_app with (A:=y) (B:=z) (Γ:=[ x ]).
all: auto.
assert (K5 : ⊢ lam x (app (weak x0) (app (weak x1) (hyp 0))) [:] Arr x z).
apply STT_lam.
auto.
exists (lam x (app (weak x0) (app (weak x1) (hyp 0)))).
clear H H0 p p0 K1 K2 K3 K4.
auto.
Show Proof.
Defined.


Definition EqMor_STT {x y : Obj_STT} (f g : Hom_STT x y) := ((proj1_sig f) = (proj1_sig g)).

Lemma EqMor_STT_ref : forall {x y} (f : Hom_STT x y), EqMor_STT f f.
Proof.
intros.
unfold EqMor_STT.
reflexivity.
Defined.

Lemma EqMor_STT_sim : forall {x y} (f g : Hom_STT x y), EqMor_STT f g -> EqMor_STT g f.
Proof.
intros.
unfold EqMor_STT.
unfold EqMor_STT in H.
congruence.
Defined.

Lemma EqMor_STT_trans : forall {x y} (f g h : Hom_STT x y), EqMor_STT f g -> EqMor_STT g h 
         -> EqMor_STT f h.
Proof.
intros.
unfold EqMor_STT.
unfold EqMor_STT in H, H0.
congruence.
Defined.

Lemma assoc_STT :  forall x y z w (f : (Hom_STT z w)) (g:(Hom_STT y z)) (h:(Hom_STT x y)),
        EqMor_STT (Compose_STT x z w f (Compose_STT x y z g h) ) (Compose_STT x y w (Compose_STT y z w f g) h).
Proof.
intros.
unfold EqMor_STT.
simpl.




