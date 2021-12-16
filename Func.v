Require Export Ops.
Require Import ProofIrrelevance.



Module Func.



    Record func {T T' : finType} (A : {set T}) (B : {set T'}) : Type := Pack {
        sort :> {set  T * T'};
        axiom : [forall u, u ∈ sort ==> (u.1 ∈ A) && (u.2 ∈ B)]
    }.


End Func.

Notation func := Func.func.
Notation graph := (Func.sort _ _ ).
Notation "A → B" := (func A B)(at level 30).
Notation mkFunc := (Func.Pack _ _ _ _).
Coercion Func.sort : func >-> set_of.


Definition func_mixinb {T T' : finType} (A : {set T}) (B : {set T'}) (G : {set T * T'}) :=
    [forall u, u ∈ G ==> (u.1 ∈ A) && (u.2 ∈ B)].

Definition func_mixinp {T T' : finType} (A : {set T}) (B : {set T'}) (G : {set T * T'}) :=
    forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B.

Theorem func_mixin_elim  {T T' : finType} {A : {set T}} {B : {set T'}} {G : {set T * T'}} :
        [forall u, u ∈ G ==> (u.1 ∈ A) && (u.2 ∈ B)] -> 
        forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B .
Proof.
    move /forallP => H u Hu; move : H.
    move /(_ u) /implyP /(_ Hu) /andP => //.
Qed.

Theorem func_mixin_intro  {T T' : finType} {A : {set T}} {B : {set T'}} {G : {set T * T'}} :
        (forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B)  ->
        [forall u, u ∈ G ==> (u.1 ∈ A) && (u.2 ∈ B)].        
Proof.
    move => H.
    apply /forallP => u.
    apply /implyP => Hu.
    apply /andP; apply H => //.
Qed.    



Theorem func_mixinP  {T T' : finType} (A : {set T}) (B : {set T'}) (G : {set T * T'}) :
    reflect 
        (forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B) 
        ([forall u, u ∈ G ==> (u.1 ∈ A) && (u.2 ∈ B)]).
Proof.
    apply (iffP idP).
    +   apply func_mixin_elim.
    +   apply func_mixin_intro.
Qed.    


      




Section funcCanonical.

    Context {T T' : finType} (A : {set T}) (B : {set T'}).

    

    Canonical func_subType := Eval hnf in [subType for (Func.sort A B)].

    Definition func_eqMixin := Eval hnf in [eqMixin of (A →  B) by <:].
    Canonical func_eqType := Eval hnf in EqType (A → B) func_eqMixin.

    Definition func_choiceMixin := [choiceMixin of (A → B) by <:].
    Canonical func_choiceType := Eval hnf in ChoiceType (A → B) func_choiceMixin.

    Definition func_countMixin := [countMixin of (A → B) by <:].
    Canonical func_countType := Eval hnf in CountType (A → B) func_countMixin.

    Canonical func_subCountType := Eval hnf in [subCountType of (A → B)].

    Definition func_finMixin := [finMixin of (A → B) by <:].
    Canonical func_finType := Eval hnf in FinType (A → B) func_finMixin.

    Canonical func_subFinType := Eval hnf in [subFinType of (A → B)].

End funcCanonical.












Theorem in_graph {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B)  (u : T * T') :
    u ∈ graph Γ ->  u.1 ∈ A  /\ u.2 ∈ B.
Proof.
    destruct Γ => /= H.
    move /forallP /(_ u) /implyP /(_ H) /andP : axiom => //.
Qed.    





Definition image {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) (a : T):=
    [set b | (a, b) ∈ graph Γ].

Lemma imageP {T T' : finType} {A : {set T}} {B : {set T'}} {Γ : A → B} {a : T} {b : T'}:
    reflect ((a,b) ∈ graph Γ) (b ∈ image Γ a).
Proof.
    apply (iffP idP); rewrite in_set => //.
Qed.    


Definition preimage {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) (b : T') :=
    [set a | (a,b) ∈ graph Γ ].

Lemma preimageP {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) a b :
    reflect ((a,b) ∈ graph Γ) (a ∈ preimage Γ b).
Proof.
    apply (iffP idP); rewrite in_set => //.
Qed.    

Definition domain {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    [set a | [exists b, (a,b) ∈ graph Γ]].

Lemma domainP {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) a :
    reflect (exists b, (a,b) ∈ graph Γ) (a ∈ domain Γ).
Proof.
    apply (iffP idP); rewrite in_set.
    +   move /existsP => [b Hb]; exists b => //.
    +   move => [b Hb]; apply /existsP; exists b => //.
Qed.    



Definition range {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    [set b | [exists a, (a,b) ∈ graph Γ]].

Lemma rangeP {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) b:
    reflect (exists a, (a,b) ∈ graph Γ) (b ∈ range Γ).
Proof.
    apply (iffP idP); rewrite in_set.    
    +   move /existsP => //.
    +   move => [a Ha]; apply /existsP; exists a => //.
Qed.    


Definition inv_set {T T' : finType} (G : {set T * T'}) : {set T' * T}:=
    [set u | (u.2,u.1) ∈ G].

Lemma inv_setP {T T' : finType} {G : {set T * T'}} u :
    reflect ((u.2, u.1) ∈ G) (u ∈ inv_set G).
Proof.
    apply (iffP idP); rewrite in_set => //.
Qed.





Lemma invH {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :
    func_mixinb B A (inv_set (graph Γ)).
Proof.
    apply /forallP => u; destruct u as [a b].
    apply /implyP.
    move /inv_setP /in_graph => /= [Ha Hb].
    apply /andP => //=.
Qed.    


Definition inv {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    mkFunc (inv_set (graph Γ)) (invH Γ).

  



(* 3.1 *)  
Lemma image_graph : forall {T T' : finType} {A : {set T}} {B : {set T'}} {Γ : A → B} {a : T}, 
    a ∈ A -> image Γ a = [set b | (a,b) ∈ graph Γ].
Proof.
    move => T T' A B Γ a Ha.
    apply extension; apply /subsetP => x; rewrite !in_set => //.
Qed.

Lemma func_extension (T T' : finType) (A : {set T}) (B : {set T'}) (Γ Γ': A → B) :
    graph Γ = graph Γ' -> Γ = Γ'.
Proof.
    move => H; induction Γ, Γ'.
    simpl in H; subst sort0.
    move : (proof_irrelevance _ axiom axiom0) -> => //.
Qed.






(* 定理１ *)
Theorem uniex_graph : forall {T T' : finType} {A : {set T}} {B : {set T'}},
    forall G : {set T * T'}, G ⊂ (setX A B) -> exists ! Γ : A → B, G = graph Γ.
Proof.
    move => T T' A B G HG.
    move /subsetP : HG => HG.
    have H : forall u, (u ∈ G) -> (u.1 ∈ A) /\ (u.2 ∈ B).
        move => u uG.
        move : (HG u uG).
        destruct u as [a b].
        move /setXP => //=.
    move /func_mixinP : H => H.
    pose Γ := mkFunc G H.
    exists Γ; split => //= Γ' H'.
    apply func_extension; rewrite -H' => //=.
Qed.   


Section Inv.


Variable (T T' : finType) (A : {set T}) (B : {set T'}) (Γ : A → B).

Lemma graph_inv :
    graph (inv Γ) = inv_set (graph Γ).
Proof. done. Qed.

Lemma image_inv :
    forall b, b ∈ B -> image (inv Γ) b = preimage Γ b.
Proof.
    move => b Hb; apply extension; apply /subsetP => a. 
    +   move /imageP /inv_setP => /= H.
        apply /preimageP => //.
    +   move /preimageP => H; apply /imageP /inv_setP => //.  
Qed.    



(* 3.2 *)
Lemma in_inv :
    forall a b,  a ∈ image (inv Γ) b = b ∈ (image Γ a).
Proof.
    move => a b. 
    rewrite !in_set => //.
Qed.

(* 3.3 *)

Lemma dom_inv :
    domain (inv Γ) = range Γ.
Proof.
    apply extension; apply /subsetP => x; rewrite !in_set => 
        /existsP [y Hy]; apply /existsP; exists y ; move : Hy; 
        rewrite graph_inv in_set => //=.
Qed.

Lemma rang_inv :
    range (inv Γ) = domain Γ.
Proof.
    apply extension; apply /subsetP => x; rewrite !in_set => 
        /existsP [y Hy]; apply /existsP; exists y; move : Hy;
        rewrite graph_inv in_set => //=.
Qed.

(* 3.4 *)
Lemma invK :
    inv  (inv Γ) = Γ.
Proof.
    apply func_extension => /=.
    apply extension; apply /subsetP => x;
    rewrite !in_set -surjective_pairing => //=.

Qed.

End Inv.
