Require Export Ops.


Definition corr {T T' : finType} (A : {set T}) (B : {set T'}) :=
    {Γ : {set prod_finType T T'} | forall u, u ∈ Γ -> u.1 ∈ A /\ u.2 ∈ B}.

Notation "A → B" := (corr A B) (at level 30).

Definition graph {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    let : exist Γ' _ := Γ in Γ'.


Theorem in_corr {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) u :
    u ∈ graph Γ ->  u.1 ∈ A  /\ u.2 ∈ B.
Proof.
    destruct Γ => /= H.
    apply a => //.
Qed.    





Definition image {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) (a : T):=
    [set b | (a, b) ∈ graph Γ].


Definition rev_corr {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    [set u | (u.2, u.1) ∈ graph Γ ].

Definition preimage {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) (b : T') :=
    [set a | (a,b) ∈ graph Γ ].

Definition domain {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    [set a | [exists b, (a,b) ∈ graph Γ]].

Definition range {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    [set b | [exists a, (a,b) ∈ graph Γ]].

Definition inv  {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) : B → A.
Proof.
    exists [set u | (u.2,u.1) ∈ graph Γ] => u.
    rewrite in_set; destruct Γ => /=.
    move /a; case => /= HA HB; split => //.
Qed.    






Axiom graph_extension :
    forall {T T' : finType} {A : {set T}} {B : {set T'}} (Γ Γ' : A → B),
    (forall a, a ∈ A -> image Γ a = image Γ' a) -> Γ = Γ'.



(* 3.1 *)    
Lemma corr_image : forall (T T' : finType) (A : {set T}) (B : {set T'}) (Γ : A → B),
    forall a, a ∈ A -> image Γ a = [set b | (a,b) ∈ graph Γ].
Proof.
    move => T T' A B Γ a Ha.
    apply extension; apply /subsetP => x; rewrite !in_set => //.
Qed.

Lemma graph_inj : forall (T T' : finType) (A : {set T}) (B : {set T'}) (Γ Γ': A → B),
    graph Γ = graph Γ' -> Γ = Γ'.
Proof.
    move => T T' A B Γ Γ'.
    move /setP /subset_eqP /andP; case => H1 H2.
    apply graph_extension => a Ha.
    apply extension; apply /subsetP => b Hb.
    +   suff : (a,b) ∈ graph Γ'.
            rewrite in_set => //=.
        move /subsetP : H1; apply; rewrite in_set in Hb => //.
    +   suff : (a,b) ∈ graph Γ.
            rewrite in_set => //.
        move /subsetP : H2; apply; rewrite in_set in Hb => //.
Qed.        




(* 定理１ *)
Theorem uniex_graph : forall (T T' : finType) (A : {set T}) (B : {set T'}),
    forall G : {set prod_finType T T'}, G ⊂ (setX A B) -> exists ! Γ : A → B, G = graph Γ.
Proof.
    move => T T' A B G HG.
    move /subsetP : HG => HG.
    have H : forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B. 
        move => u; move /HG. 
        rewrite [u]surjective_pairing => /=; move /setXP => //.
    pose Γ := @exist {set prod_finType T T'} (fun g => forall u, u ∈ g -> u.1 ∈ A /\ u.2 ∈ B) G H.
    exists Γ; split => //= Γ' H'.
    apply graph_inj; rewrite -H' => //=.
Qed.   


Section rev.
Print image.

Variable (T T' : finType) (A : {set T}) (B : {set T'}) (Γ : A → B) .

Lemma corr_inv :
    forall a b, a ∈ A -> b ∈ B -> b ∈ (image Γ a) <-> a ∈ image (inv Γ) b.
Proof.
    move => a b Ha Hb; rewrite !in_set => //.
    destruct Γ => /=.
    rewrite /inv.
Qed.

Lemma dom_rev :
    domain (rev Γ) = range Γ.
Proof.
    apply extension; apply /subsetP; [move => a | move =>b]; 
    rewrite !in_set; move /existsP => [x Hx]; 
        apply /existsP; exists x; move : Hx; rewrite !in_set => /=. rewrite -surjective_pairing.
    +   rewrite in_set in Hx.


