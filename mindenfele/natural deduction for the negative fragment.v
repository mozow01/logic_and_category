Require Import List.

Inductive Typ : Set :=
  | Top : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | top : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.

Definition  Cntxt := list Typ.

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | ND_top_intro : forall G, Tyty G top Top
  | ND_hypO : forall G A, Tyty (A :: G) (hyp 0) A
  | ND_hypS :
      forall G A B I,
      Tyty G (hyp I) A -> Tyty (B :: G) (hyp (S I)) A
  | ND_lam :
      forall G t A B,
      Tyty (A :: G) t B -> Tyty G (lam A t) (Imp A B)
  | ND_app :
      forall G t s A B,
      Tyty G t (Imp A B) -> Tyty G s B -> Tyty G (app t s) B
  | ND_cnj :
      forall G t s A B,
      Tyty G t A -> Tyty G s B -> Tyty G (cnj t s) (Cnj A B)
  | ND_proj_1 :
      forall G t A B,
      Tyty G t (Cnj A B) -> Tyty G (proj_1 t) A
  | ND_proj_2 :
      forall G t A B,
      Tyty G t (Cnj A B) -> Tyty G (proj_2 t) B.

Notation "G '⊢' t '[:]' A" := (Tyty G t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.


Lemma problem_1 : forall A B, exists t, ⊢ t [:] (Imp A (Imp B A)).
Proof.
  intros.
  exists (lam A (lam B (hyp 1))).
  apply ND_lam.
  apply ND_lam.
  apply ND_hypS.
  apply ND_hypO.
  Show Proof.
Qed.
