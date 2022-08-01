Class STT_ALG := STT_ALG_mk {

(*Category of contexts (where substitutors are the morphisms)*)

  Con : Set;
  Sub : Con -> Con -> Set;
  comp : forall {Γ Δ Ξ : Con}, Sub Δ Γ -> Sub Ξ Δ -> Sub Ξ Γ; 
  id : forall {Γ : Con}, Sub Γ Γ;

  ass : forall {Γ Δ Ξ Ψ : Con} {ξ : Sub Ψ Ξ} {δ : Sub Ξ Δ} {γ : Sub Δ Γ},

        comp (comp γ δ) ξ = comp γ (comp δ ξ);

  idl : forall {Γ : Con} {γ : Sub Γ Γ}, 

        comp id γ = γ;

  idr : forall {Γ : Con} {γ : Sub Γ Γ}, 
    
        comp γ id = γ;

(*Empty context as a terminal object*)

  Ζ : Con;
  ε : forall {Γ : Con}, Sub Γ Ζ;

  Zη : forall {Γ : Con} {γ : Sub Γ Ζ}, 

        γ = ε;

(*Types as a functor from Con to Set where substitutions are the morphisms *)

  Typ  : Con -> Set;
  subT : forall {Γ Δ : Con}, Typ Γ -> Sub Δ Γ -> Typ Δ;

  subTcomp : forall  {Γ Δ Ξ : Con} {A : Typ Γ} {δ : Sub Ξ Δ} {γ : Sub Δ Γ}, 

        subT A (comp γ δ) = subT (subT A γ) δ;

  subTid : forall  {Γ : Con} {A : Typ Γ}, 

        subT A id = A;

(*Proofs *)

  Pf   : forall (Γ:Con), Typ Γ -> Set;
  subP : forall {Γ Δ : Con} {A : Typ Γ}, Pf Γ A -> forall (γ : Sub Δ Γ), Pf Δ (subT A γ);
  extT : forall (Γ:Con), Typ Γ -> Con;
(*

  
| _,_ : (γ:Sub Δ Γ) → Pf Δ (A[γ]) → Sub Δ (Γ▹A)
  hypSub   : forall {Γ : Con} {A : Typ Γ}, Sub (extT Γ A) A;
  zeroHyp  : forall {Γ : Con} {A : Typ Γ}, Pf  (extT Γ A) (subT A hypSub);


| ▹β  : p∘(γ,a) = γ
| ▹η  : (p∘γa,q[γa]) = γa
*)
}.