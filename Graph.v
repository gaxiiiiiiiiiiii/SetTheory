Require Export Ops.



Module Corr.

Record corr {T T' : finType} (A : {set T}) (B : {set T'}) : Type := Pack {
    G :> {set prod_finType T T'};
    axiom : forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B
}.

End Corr.

Notation corr := Corr.corr.
Notation graph := (Corr.G _ _ ).
Notation "A → B" := (corr A B)(at level 30).
Notation mkCorr := (Corr.Pack _ _ _ _).






Theorem in_corr {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B)  (u : prod_finType T T') :
    u ∈ graph Γ ->  u.1 ∈ A  /\ u.2 ∈ B.
Proof.
    destruct Γ => /= H.
    apply axiom => //.
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




Definition invg {T T' : finType} (G : {set prod_finType T T'}) :=
    [set u | (u.2,u.1) ∈ G].


Definition invType  {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :=
    {Γ' : B → A | graph Γ' = invg (graph Γ)}.

Definition inv_graph 
    {T T' : finType} {A : {set T}} {B : {set T'}} {Γ : A → B} (Γ' : invType Γ) :=
    let : exist a _ := Γ' in a.

Coercion inv_graph : invType >-> corr.

Definition inv  {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) : invType Γ.
Proof.
    destruct Γ => /=.
    have axiom' : forall u, u ∈ (invg G) -> u.1 ∈ B /\ u.2 ∈ A.
        move => u; rewrite in_set; move /axiom => /=.
        move => [HA HB]; split => //.
    pose Γ' := mkCorr (invg G) axiom'.
    exists Γ' => //=.
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
    pose Γ := mkCorr G H.
    exists Γ; split => //= Γ' H'.
    apply graph_inj; rewrite -H' => //=.
Qed.   


Section Inv.


Variable (T T' : finType) (A : {set T}) (B : {set T'}) (Γ : A → B).



Lemma corr_inv :
    forall a b, a ∈ A -> b ∈ B -> b ∈ (image Γ a) <-> a ∈ image (inv Γ) b.
Proof.
    move => a b Ha Hb. 
    rewrite !in_set => //.
    destruct (inv Γ), Γ => /=.
    rewrite e => /=; rewrite in_set => //=.
Qed.

Lemma dom_rev :
    domain (inv Γ) = range Γ.
Proof.
    apply extension; apply /subsetP => x; rewrite !in_set => 
        /existsP [y Hy]; apply /existsP; exists y; move : Hy;
        induction (inv Γ) as [Γ' axiom] => /=; rewrite axiom;
        rewrite in_set => //=.
Qed.




    

