



Lemma problem_cont : forall (v: VAL) G A, 
(v A) × ([[ G ]]_C v) = [[ A :: G ]]_C v.
Proof.
  intros.
  all: simpl; auto.
Defined.
