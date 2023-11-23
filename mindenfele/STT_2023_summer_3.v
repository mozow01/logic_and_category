(*STT nyelve implicit változókkal*)

Require Import List.
Require Import Arith.

(*Típusok nyelve*)

Inductive Typ : Set :=
  | Iota : Typ
  | Arrow : Typ -> Typ -> Typ.

Notation "'ι'" := Iota (at level 20).
Infix "→" := Arrow (at level 20, right associativity).

(*Változók: nameless dummies :)

Nincsenek explicit változók, csak indexek, amik azt mondják meg, hogy a kontextus hanyadik eleme az illető implicit 'változó'. *)

(*A kontextusok típusok listái, a művelet a kontextuskibővítés (balról hozzáfűzünk a kistához egy új elemet)*)

Definition Cntxt := list Typ.

Definition CntxExt (A : Typ) Γ  := A :: Γ.

Infix "▷" := CntxExt (at level 20, right associativity).

(* Külön vannak kifejezések (terminusok, termek)*)

Inductive Trm : Set :=
  | ind : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm.

Notation "x '$' y" := (app x y) (at level 20).

(* Mivel itt bizonyításokról, levezetsekről van szó (és ez szemléletesebb is), ezért an n-edik 
változót 

ind n 

jelöli. Ez viszont nem egy abszolút sorszám, hanem egy relatív.
A Γ = A_0::A_1::A_2::...::nil kontextusban ind 0 pl. az lista első elemére, 
az A_0 típusúváltozóra mutat. Ha Γ bővül egy elemmel, 
a sorrendek eltolódnak 1-gyel. 

lam-nál meg kell jelölni, hogy milyen típusú termet absztrahál, azaz lam egy Typ -> Trm -> Trm típusú lesz.

app problémamentes
*)

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | ND_ind0 : forall Γ A, Tyty (A :: Γ) (ind 0) A
  | ND_indS :
      forall Γ A B i,
      Tyty Γ (ind i) A -> Tyty (B :: Γ) (ind (S i)) A
  | ND_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Arrow A B)
  | ND_app :
      forall Γ t s A B,
      Tyty Γ t (Arrow A B) -> Tyty Γ s A -> Tyty Γ (app t s) B.

Notation "G '⊢' t '[:]' A" := (Tyty G t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Lemma First_typeability_rule_for_snd_term : forall (Γ : Cntxt) (A B : Typ), 
A :: B :: Γ ⊢ (ind 1) [:] B.
Proof.
intros.
apply (ND_indS).
apply (ND_ind0).
Qed.

Example First_typeability_rule_1 : forall (A B C : Typ), 
A :: C :: B :: A :: nil ⊢ (ind 1) [:] C.
Proof.
intros.
apply First_typeability_rule_for_snd_term.
Qed.

Theorem Chain_rule : forall (A B C : Typ), exists (P : Trm), 
A → B :: B → C :: nil ⊢ P [:] A → C.
Proof.
intros.
exists (lam A (app (ind 2) ((app (ind 1) (ind 0)) ))).
apply (ND_lam).
apply ND_app with (A:=B) (B:=C).
apply ND_indS.
apply ND_indS.
apply ND_ind0.
apply ND_app with (A:=A) (B:=B).
apply ND_indS.
apply ND_ind0.
apply ND_ind0.
Qed.




(*De Bruijn term
https://en.wikipedia.org/wiki/De_Bruijn_index
http://alexandria.tue.nl/repository/freearticles/597619.pdf

λ10 megfelel: λx.yx ( y: A -> B |- lambda (x:A). yx : A -> B )

                    zw  x
                     \ /    konkrét szintaxisfa
                      yx
                      |
                    λx.yx        zw

                    y   x
                     \ /     absztrakt szintaxisfa
                      $
                      |
                      λx.      λx.yx  
                 

                    1   0
                     \ /     de Bruijn kód
                      $
                      |
                      λ        
                 -----------
                      |
                      λ         0. szabad változó (y)

                                1.




λ02 megfelel: λx.xz (abban az értelenben, hogy y rejtve van)


                    0   2
                     \ /  
                      $
                      |
                      λ
                 -----------
                      |
                      λ         0. szabad változó (y)
                      |
                      λ         1. szabad változó (z)

λλ02 megfelel: λy.λx.xz


                    0   2
                     \ /  
                      $
                      |
                      λ
                      |
                      λ         
-----------------------------------------------
                      |
                      λ         0. szabad változó (z)


λ1(λ1(3λ13)) megfelel: λx.v(λy.x(wλz.(yv)))

(szokás szerint az applikáció jele $)

                  1   3.
                   \ /
                    $
                    |
                3.. λ
                 \ /
              1   $
               \ /
                $
                |
            1.  λ
             \ /
              $
              |
              λ
----------------------- (ezután már nem a term, hanem a lezártja jön, ezek a szabad változókat "kötik")
              |
              λ.              0. szabad vált.
              |
              λ..             1. szabad vált.

A fában tettem, egy .-ot a 0. szabad változó szerepléseihez, ..-ot az 
1. indexű sz. v.-hoz.

Egy levelet,  amin az n természetes szám van, az a lambda közi, 
amelyikhez pontosan n lambdán át vezet keresztül az út. 

*)

(*A levezethetőség definíciójában a 

https://github.com/coq-contribs/prfx/

munkát követjük. Ebben hyp n tényleg az n-edik DeBruijn index.
 *)







(*Helyettesítés (de Bruijn definíciója)

Adott termek egy sorozata (érdemes "visszafelé felsorolni őket")

s = (..., t_2, t_1, t_0)

és egy szingli term: P. Ekkor

"Sub P n s" (P[...n/s_n...]) 

rekurzívan lesz értelmezve és úgy mondjuk ki, hogy 

"az a term, amit úgy kapunk, hogy a P term n-edik változójába 
az s sorozat n-edik elemét helyettesítjük"

Levelek:

   ha az n-edik szabad változóba akarunk behelyettesíteni,
   akkor a termsorozat n. elemét olvassuk ki:
    (t_0, t_1, t_2, ...)
                ↑
              ind 1
              
(Az applikációkba való helyettesítés problémamentes kompozicionálisan helyettesítendők.)

A lambdák viszont a indexelését elrontják:

                     2..
                      \ /
                       $
                       |
                       λ ←
----------------------------------
                       |
                       λ.
                       |
                       λ..
                       
Itt az 1-essel indexelt szabad változó szereplését 2 jelöli, mert a λ 
felfelé való mozgási irányát nézve bevitt a kontextusba 0-val indexelve 
egy újabb szabad változót és ezzel eltolta (SHIFT) a változók sorozatát. 

Amire még figyelni kell, hogy abban a termben, amit helyettesítünk
szerepelhetnek szabad változók. Ezeknek szintjét minden egyes lambdán való
keresztülhaladáskor (felfelé halad a rekurzió), növelni kell pontosan eggyel, hogy
megmaradjanak szabad változóknak (LIFT). Ezt fejezik ki az alábbi definíciók. 
                       
                       
tehát  "[t]lam t' = lam SHIFT[LIFT t]t' "

Ez utóbbiak beprogramozásához mutatis mutandis ezt követjük:

http://www.cs.ru.nl/~Adam.Koprowski/papers/stlc-draft-06.pdf

*)

(* Ez a rekurzív megadású függvény a t term k-adik szabad változójától kezdve az összes szabad változójának szintjét emeli meg n-nel: (ind m) -> ind (m+n); k-adik úgy értendő, hogy az "első a nulladik" és hogy a k-adik változóra mutat egy levél, ha éppen hyp k van a levélen, miközben minden λ-n való áthaladáskor a változó indexe nő (pl. a 0. szabad változó indexe az első λ-n való áthaladáskor már 1 lesz.)  *)
 

Fixpoint lift_aux (n : nat) (t : Trm) (k : nat) {struct t} : Trm :=
   match t with
     | ind i => match (le_gt_dec k i) with
                  | left _ => (* k <= i *) ind (i + n)
                  | right _ => (* k > i *) ind i
                end
     | app M N => app (lift_aux n M k) (lift_aux n N k)
     | lam A M => lam A (lift_aux n M (S k))
   end.

(* A következő függvény az összes szabad változót lifteli n-nel *)

Definition lift P n := lift_aux n P 0.


Eval compute in lift (lam Iota (app (ind 0) (ind 1))) 1. 

Eval compute in lift (lam Iota (lam Iota (app (ind 0) (ind 1)))) 2.

Eval compute in lift (app (ind 0) (lam Iota (app (ind 0) (ind 1)))) 2.

(* Az alábbi függvény egy termsorozat minden elemét lifteli (azaz a benne
 szereplő szabad változók indexét emeli eggyel.) *)

Definition lift_seq (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => lift (s 0) 1
     | S m => lift (s (S m)) 1
  end.
  
(* Eltolja a termsorozatot 1-gyel és az első helyre berakja a ind 0-t. *)

Definition shift_seq (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => ind 0
     | S m => (s m)
  end.

(* A t term n-edik szabad változója helyére az s sorozat n. elemét helyettesíti *)

Fixpoint subst_aux (t : Trm) (n : nat) (s : nat -> Trm) {struct t} : Trm :=
  match t with
    | ind i => match (Nat.eq_dec n i)  with 
                 | left _ => s n
                 | right _ => ind i
               end
    | app M N => app (subst_aux M n s) (subst_aux N n s)
    | lam A M => lam A (subst_aux M (S n) (shift_seq ( lift_seq s)))
  end.
  
(* Ugyenez 0-val. *)
  
Definition subst P s := subst_aux P 0 s.

(* Ugyanez, azzal a sorozattal, amikor a 0. elem Q, a többi irreleváns *)

Definition subs P Q := subst_aux P 0 (fun k : nat => 
match k with | 0 => Q | S _ => ind 0 end).

Definition s1 (n : nat) : Trm :=
  match n with
    | 0 => app (ind 0) (ind 0)
    | S 0 => app (app (ind 0) (ind 0)) (ind 0) (* (ind 1 $ ind 1) $ ind 1 *)
    | S (S 0) => app (app (ind 0) (ind 0)) (app (ind 0) (ind 0))
    | S (S (S _)) => ind 0
  end.
  

Eval compute in subst (lam Iota (app (ind 2) (ind 1))) s1.

(*
      1  1
   2   *
     *
     λ
λ.2(11)
     *)

Eval compute in subs (lam Iota (app (ind 2) (ind 1))) (app (ind 0) (ind 0)).

Eval compute in subst_aux (lam Iota (app (ind 2) (ind 1))) 1 s1.


Eval compute in subst_aux (lam Iota (lam Iota (app (ind 0) (ind 2)))) 0 s1.

Eval compute in subs (lam Iota (lam Iota (app (ind 0) (ind 3)))) (app (ind 1) (ind 1)).

Eval compute in subs (lam Iota (lam Iota (app (ind 0) (ind 4)))) 
(lam Iota ( lam Iota (((app (ind 2) (ind 2)))))).

Inductive DefEqu : Cntxt -> Trm -> Trm -> Typ -> Prop := 
  | DefEqu_refl : forall Γ t A, Tyty Γ t A -> DefEqu Γ t t A
  | DefEqu_simm : forall Γ t s A, DefEqu Γ t s A -> DefEqu Γ s t A
  | DefEqu_tran : forall Γ t s r A, DefEqu Γ t s A -> DefEqu Γ s r A -> DefEqu Γ t r A
  | DefEqu_beta : forall Γ t s A B, Tyty (A :: Γ) t B ->  Tyty Γ s B -> DefEqu Γ (app (lam A t) s) (subs t s) B
  | DefEqu_eta : forall Γ f A B, Tyty  Γ f (A → B) -> DefEqu Γ (lam A (app f (ind 0)) ) f B.

(*

Parameter r : Trm.

Eval compute in (subst_aux (ind 1) 0 ((fun k : nat => 
match k with | 0 => r | S _ => ind 0 end))).

*)

(*seq_head (P : Trm) az a termsorozat, aminek az első eleme P, a többi az irreleváns ind 0.*)

Definition seq_head (P : Trm) := ((fun k : nat => 
match k with | 0 => P | S _ => ind 0 end)).

(*subs_lift_plus_one (t r : Trm) az a helyettesítés, amit úgy
 kapunk, hogy r-et a t term 1-gyel indexelt, tehát második
 szabad változójába helyettesítünk. r de Bruijn számai persze
 liftelődnek eggyel, mert . Erre a függvényre azért van
 szükség, mert a lambdán áthaladva a kontextus bővül eggyel és
 így nem az első, hanem a második szabad változóba kell
 behelyettesíteni.*)

Definition subs_lift_plus_one (t r : Trm) := subst_aux t (S 0) (shift_seq (lift_seq (seq_head r))).

Definition subs_lift_plus_one' (t r : Trm) := subst_aux t (S 0) ( (lift_seq (seq_head r))).

Theorem Sub_prop_1 : forall r, (subs (ind 0) r) = r.
Proof.
intros.
compute.
auto.
Defined.

Theorem Sub_prop_2 : forall r n, (subs (ind (S n)) r) = ind (S n).
Proof.
intros.
compute.
auto.
Defined.

Theorem Sub_prop_3 : forall r t s, (subs (app t s) r) = (app (subs t r) (subs s r)).
Proof.
intros.
induction t.
all: auto.
Defined.

Theorem Sub_prop_4 : forall r t A, subs (lam A t) r = lam A (subs_lift_plus_one t r).
Proof.
intros.
induction t.
all: auto.
Defined.













