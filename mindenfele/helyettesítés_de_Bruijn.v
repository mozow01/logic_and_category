
Require Import List.
Require Import Arith.


Inductive Typ : Set :=
  | Top : Typ
  | Imp : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm.
  
(* Mivel itt bizonyításokról van szó (és ez szemléletesebb is), ezért an n-edik 
változót 

hyp n 

jelöli. Ez viszont nem egy abszolút sorszám, hanem egy relatív.
A Γ = A_0::A_1::A_2::...::nil kontextusban hyp 0 pl. az lista első elemére, 
az A_0 típusúváltozóra mutat. Ha Γ bővül egy elemmel, 
a sorrendek eltolódnak 1-gyel. 

lam-nál meg kell jelölni, hogy milyen típusú termet absztrahál, azaz lam 
Typ -> Trm -> Trm típusú lesz a Trm -> Trm helyett.

app problémamentes
*)
  
  
(*De Bruijn term
https://en.wikipedia.org/wiki/De_Bruijn_index
http://alexandria.tue.nl/repository/freearticles/597619.pdf

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
 
Definition Cntxt := list Typ.

Definition CntxExt (A : Typ) Γ  := A :: Γ.

Infix "▷" := CntxExt (at level 20, right associativity).


Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | ND_hypO : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | ND_hypS :
      forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | ND_lam :
      forall Γ t A B,
      Tyty (A ▷ Γ) t B -> Tyty Γ (lam A t) (Imp A B)
  | ND_app :
      forall Γ t s A B,
      Tyty Γ t (Imp A B) -> Tyty Γ s A -> Tyty Γ (app t s) B.

Notation "G '⊢' t '[:]' A" := (Tyty G t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

(*Helyettesítés (de Bruijn definíciója)

Adott termek egy sorozata (érdemes "visszafelé felsorolni őket")

s = (..., t_2, t_1, t_0)

és egy szingli term: P. Ekkor

"Sub P n s" 

rekurzívan lesz értelmezve és úgy mondjuk ki, hogy 

"az a term, amit úgy kapunk, hogy a P term n-edik változójába 
az s sorozat n-edik elemét helyettesítjük"

Levelek:

   ha az n-edik szabad változóba akarunk behelyettesíteni,
   akkor a termsorozat n. elemét olvassuk ki:
    (..., t_2, t_1, t_0)
                ↑
              hyp 1
              
Az applikációk kompozicionálisan helyettesítendők.

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
                       
Itt az 1-essel indexelt változó szereplését már 2 jelöli, mert az λ 
felfelé való mozgási irányt nézve bevitt a kontextusba 0-val indexelve 
egy újabb szabad változót és ezzel eltolta (SHIFT) a változók sorozatát. 

Amire még figyelni kell, hogy abban a termben, amit helyettesítünk
szerepelhetnek szabad változók. Ezeknek szintjét minden egyes lambdán való
keresztülhaladáskor (felfelé halad a rekurzió), növelki kell eggyel, hogy
megmaradjanak szabad változóknak (LIFT). Ezt fejezik ki az alábbi definíciók. 
                       
                       
tehát  "[t]lam t' = lam SHIFT[LIFT t]t' "

Ez utóbbiak beprogramozásához mutatis mutandis ezt követjük:

http://www.cs.ru.nl/~Adam.Koprowski/papers/stlc-draft-06.pdf

*)

(* Ez a rekurzív megadású függvény a t term k-adik szabad változójának 
szintjét emeli meg n-nel: (hyp m) -> hyp (m+n); k-adik úgy értendő,
hogy az "első a nulladik" és hogy a k-adik változóra mutat egy levél,
ha éppen hyp k van a levélen, miközben minden λ-n való áthaladáskor a változó 
indexe nő (pl. a 0. szabad változó indexe az első λ-n való áthaladáskor
már 1 lesz.)  *)
 

Fixpoint lift_aux (n : nat) (t : Trm) (k : nat) {struct t} : Trm :=
   match t with
     | hyp i => match (le_gt_dec k i) with
                  | left _ => (* k <= i *) hyp (i + n)
                  | right _ => (* k > i *) hyp i
                end
     | app M N => app (lift_aux n M k) (lift_aux n N k)
     | lam A M => lam A (lift_aux n M (S k))
   end.

(* A következő függvény az első, azaz 0-val indexelt szabad változót lifteli *)

Definition lift P n := lift_aux n P 0.


Eval compute in lift (lam Top (app (hyp 0) (hyp 1))) 1. 


Eval compute in lift (lam Top (lam Top (app (hyp 0) (hyp 1)))) 2.

Print Nat.eq_dec.

(* Az alábbi függvény egy termsorozat minden elemét lifteli (azaz a benne
 szereplő szabad változók indexét emeli eggyel.) *)

Definition lift_subst (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => lift (s 0) 1
     | S m => lift (s m) 1
  end.
  
(* Eltolja a termsorozatot 1-gyel és az első helyre berakja a hyp 0-t. *)

Definition shift_subst (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => hyp 0
     | S m => (s m)
  end.

(* A t term n-edik szabad változója helyére az s sorozat n. elemét helyettesíti *)

Fixpoint subst_aux (t : Trm) (n : nat) (s : nat -> Trm) {struct t} : Trm :=
  match t with
    | hyp i => match (Nat.eq_dec n i)  with 
                 | left _ => s (S n)
                 | right _ => hyp i
               end
    | app M N => app (subst_aux M n s) (subst_aux N n s)
    | lam A M => lam A (subst_aux M (S n) ( shift_subst (lift_subst s)))
  end.
  
(* Ugyenez 0-val. *)
  
Definition subst P s := subst_aux P 0 s.

(* Ugyanez, azzal a sorozattal, amikor a 0. elem Q, a többi irreleváns *)

Definition substi P Q := subst_aux P 0 (fun k : nat => 
match k with | 0 => Q | S _ => hyp 0 end).

Definition s1 (n : nat) : Trm :=
  match n with
    | 0 => app (hyp 0) (hyp 0)
    | S 0 => app (app (hyp 0) (hyp 0)) (hyp 0)
    | S (S 0) => app (app (hyp 0) (hyp 0)) (app (hyp 0) (hyp 0))
    | S (S (S _)) => hyp 0
  end.
  

Eval compute in subst (lam Top (app (hyp 2) (hyp 1))) s1.

Eval compute in subst_aux (lam Top (lam Top (app (hyp 0) (hyp 3)))) 1 s1.

