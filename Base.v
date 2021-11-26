
From mathcomp Require Export all_ssreflect.
Require Export Classical.

Notation "∅" := set0.
Notation "x ∈ X" := (x \in X)(at level 50). 
Notation "A ∩ B" := (setI A B)(at level 40).
Notation "A ∪ B" := (setU A B)(at level 40).
Notation "A ⊂ B" := (A \subset B)(at level 30).
Notation "A // B" := (setD A B)(at level 40).
Notation "¬ A" := (setC A)(at level 40).
Notation "pow[ A ]" := (powerset A).
Notation "⊓ X" := (\bigcap_(x in X) x) (at level 30).
Notation "⊔ X" := (\bigcup_(x in X) x) (at level 30).

Lemma bigUP {T : finType} (x : T) (X : {set {set T}}) :
    reflect (exists Y : {set T}, x ∈ Y /\ Y ∈ X)(x ∈ ⊔ X).
Proof.
    apply (iffP idP).
    +   move /bigcupP => [i iX xi]; exists i => //.
    +   move => [Y [xY YX]].
        apply /bigcupP; exists Y => //.
Qed. 

Lemma bigIP {T : finType} (x : T) (X : {set {set T}}) :
    reflect (forall Y : {set T}, Y ∈ X -> x ∈ Y) (x ∈ ⊓ X).
Proof.
    apply (iffP idP).
    +   move /bigcapP => H Y YX; apply H => //.
    +   move => H; apply /bigcapP => Y YX; apply H => //.
Qed.




Lemma extension {T : finType} (A B : {set T}) :
    A ⊂ B -> B ⊂ A -> A = B.
Proof.
    move => AB BA; apply /setP /subset_eqP /andP => //.    
Qed.

