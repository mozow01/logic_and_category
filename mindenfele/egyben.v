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

Class Category := {
  Obj :> Type;

  uHom := Type : Type;

  Hom : Obj -> Obj -> uHom;

  Id : forall x, Hom x x;

  Dom {x y} (f: Hom x y) := x;

  CoDom {x y} (f: Hom x y) := y;

  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);

  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;

  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;

}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "g ∘ f" := (Compose g f) (at level 40, left associativity) :
type_scope.

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

Context {CCC : CartClosed}.

Structure VAL : Type := makeVAL 
  { V :> Typ -> Obj;
    VAL_top : V Top = Top_obj;
    VAL_imp : forall {A B}, V (Imp A B) = Exp_obj (V B) (V A);
    VAL_Cnj : forall {A B}, V (Cnj A B) = Prod_obj (V A) (V B);
  }.

Fixpoint VAL_Cntxt (v : VAL) (G : list Typ) := 
  match G with 
    | nil => Top_obj
    | A :: G' => Prod_obj (v A) (VAL_Cntxt v G') 
  end.

Notation "'[[' G ']]_C' v" := (VAL_Cntxt v G) (at level 40, no associativity) :
type_scope.

Theorem soundness : forall v G A, (exists t, G ⊢ t [:] A) -> 
                           inhabited( ([[ G ]]_C v) → (v A) ).
Proof.
  intros v G A H.
  elim H.
  intros.
  induction H0.
  - apply inhabits.
  rewrite VAL_top.
  exact (Top_mor).
  - apply inhabits.
  exact (@First (CCC) (v A) ([[ G ]]_C v) ).
  - 
  assert (H1 : (exists t : Trm, G ⊢ t [:] A)).
  exists (hyp I). exact H0.
  apply IHTyty in H1.
  apply inhabited_ind with (P := inhabited ([[B :: G ]]_C v → v A)) in H1.
  auto.
  intros.
  apply inhabits.
    exact (Compose X (@Second CCC (v B) ([[ G ]]_C v))). TODO

  




