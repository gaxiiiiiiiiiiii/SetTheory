Require Export Ops.
Require Import ProofIrrelevance.





Module Func.

Definition mixin {T T' : finType} (A : {set T}) (B : {set T'}) (G : {set T * T'}):=
     forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B.   

Record func {T T' : finType} (A : {set T}) (B : {set T'}) : Type := Pack {
    G :> {set  T * T'};
    axiom : forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B
}.

End Func.

Notation func := Func.func.
Notation graph := (Func.G _ _ ).
Notation "A → B" := (func A B)(at level 30).
Notation mkFunc := (Func.Pack _ _ _ _).



(* Definition map_eq   {T T' : finType} (A : {set T}) (B : {set T'}) : rel (A → B) :=
    fun f f' => Func.G A B f == Func.G A B f'.

Axiom map_eqAxiom : forall {T T' : finType} (A : {set T}) (B : {set T'}),
    @Equality.axiom (A → B)(map_eq A B).

Definition map_eqMixin {T T' : finType} (A : {set T}) (B : {set T'}) := 
    Equality.Mixin (map_eqAxiom A B).

Canonical map_eqType {T T' : finType} (A : {set T}) (B : {set T'}) := 
    EqType (A → B) (map_eqMixin A B). *)



Theorem in_graph {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B)  (u : T * T') :
    u ∈ graph Γ ->  u.1 ∈ A  /\ u.2 ∈ B.
Proof.
    destruct Γ => /= H.
    apply axiom => //.
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


Definition inv_set {T T' : finType} (G : {set T * T'}) :=
    [set u | (u.2,u.1) ∈ G].

Lemma inv_setP {T T' : finType} {G : {set T * T'}} u :
    reflect ((u.2, u.1) ∈ G) (u ∈ inv_set G).
Proof.
    apply (iffP idP); rewrite in_set => //.
Qed.    



Lemma invH {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :
    forall u, u ∈ inv_set (graph Γ) -> u.1 ∈ B /\ u.2 ∈ A.
Proof.
    move => u; rewrite in_set.
    induction Γ; move /axiom => [Ha Hb] //.
Qed.

Definition inv {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    mkFunc (inv_set (graph Γ)) (invH Γ).

  



Theorem func_extension {T T' : finType} {A : {set T}} {B : {set T'}} (Γ Γ' : A → B) :
    graph Γ = graph Γ' -> Γ = Γ'.    
Proof.
    move => H; induction Γ, Γ'.
    simpl in H; subst G0.
    move : (proof_irrelevance _ axiom axiom0) -> => //.
Qed.




(* Axiom func_extension :
    forall {T T' : finType} {A : {set T}} {B : {set T'}} (Γ Γ' : A → B),
    (forall a, a ∈ A -> image Γ a = image Γ' a) -> Γ = Γ'.
Proof. *)
  




 

(* 3.1 *)  
Lemma image_graph_ : forall {T T' : finType} {A : {set T}} {B : {set T'}} {Γ : A → B} {a : T}, 
    a ∈ A -> image Γ a = [set b | (a,b) ∈ graph Γ].
Proof.
    move => T T' A B Γ a Ha.
    apply extension; apply /subsetP => x; rewrite !in_set => //.
Qed.

Lemma graph_inj : forall (T T' : finType) (A : {set T}) (B : {set T'}) (Γ Γ': A → B),
    graph Γ = graph Γ' -> Γ = Γ'.
Proof.
    move => T T' A B Γ Γ'.
    move /setP /subset_eqP /andP; case => H1 H2.
    apply func_extension.
    apply extension; apply /subsetP => b Hb.
    +   move /subsetP : H1; apply => //.
    +   move /subsetP : H2; apply => //.
Qed.  






(* 定理１ *)
Theorem uniex_graph : forall {T T' : finType} {A : {set T}} {B : {set T'}},
    forall G : {set T * T'}, G ⊂ (setX A B) -> exists ! Γ : A → B, G = graph Γ.
Proof.
    move => T T' A B G HG.
    move /subsetP : HG => HG.
    have H : forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B. 
        move => u; move /HG. 
        rewrite [u]surjective_pairing => /=; move /setXP => //.
    pose Γ := mkFunc G H.
    exists Γ; split => //= Γ' H'.
    apply graph_inj; rewrite -H' => //=.
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
    apply graph_inj => /=.
    apply extension; apply /subsetP => x;
    rewrite !in_set -surjective_pairing => //=.

Qed.

End Inv.
