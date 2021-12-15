Require Export Comp.
Require Export Classical.



Theorem inverseP {P b} :
    reflect P b -> reflect (~ P) (~~ b).
Proof.
    destruct b => /= H.
    +   apply (iffP idP).
        -   move => F; inversion F.
        -   move => F.
            suff T : P.
                case (F T).
            apply /H => //.
    +   apply (iffP idP) => //.
        move => _  /H HP.
        inversion HP.
Qed.        




Theorem set0_dec {T : finType}(X : {set T}) :
    {X = ∅} + {X <> ∅}.
Proof.
    remember (X == ∅).
    induction b; [left|right]; symmetry in Heqb.
    +   move /eqP : Heqb => //.
    +   move => F; subst X.
        rewrite eq_refl in Heqb; inversion Heqb.
Qed.   

Section Bigop.
Context {T T' : finType} {AA : {set {set T}}} {B : {set T}}.

Notation "\bigcup A" := (\bigcup_(a in A) a)(at level 50).
Notation "\bigcap A" := (\bigcap_(a in A) a)(at level 50).


Theorem setBUI :
    (\bigcup AA) ∩ B = \bigcup_(A in AA) (A ∩ B).
Proof.
    apply extension; apply /subsetP => x.
    +   move /setIP => [/bigcupP [A AAA xA] xB].
        apply /bigcupP; exists A => //.
        apply /setIP => //.
    +   move /bigcupP => [A AAA /setIP [xA] xB].
        apply /setIP; split => //.
        apply /bigcupP; exists A=> //.
Qed.


     

Theorem setBIU :
    (\bigcap AA) ∪ B = \bigcap_(A in AA) (A ∪ B).
Proof.
    apply extension; apply /subsetP => x.        
    +   move /setUP => [/bigcapP H|xB]; apply /bigcapP => A HA; 
            apply /setUP; [left|right] => //.
        apply H => //.
    +   move /bigcapP => H.
        apply /setUP.
        case (set0_dec AA) => H0; [left|].
        -   subst AA.
            apply /bigcapP => i F.
            move : ((in_set0 i)).
            rewrite F => //.
        -   move /eqP /set0Pn  : H0 => [A HA].
            remember (x ∈ B).
            destruct b; symmetry in Heqb; [right|left] => // .
            apply /bigcapP => A' HA'.
            move : (H A' HA'); move /setUP; case => [xA | xB] => //.
            rewrite Heqb in xB; inversion xB.
Qed.               


Theorem setBUC :
    ¬ (\bigcup AA) = \bigcap_(A in AA) (¬ A).
Proof.
    apply extension; apply /subsetP => a.
    +   move /setCP => H.        
        apply /bigcapP => A HA.
        apply /setCP => aA.
        apply H; apply /bigcupP; exists A => //.
    +   move /bigcapP => H.
        apply /setCP => /bigcupP [A HA aA].
        move /H /setCP : HA; apply => //.
Qed.


Lemma setBC0 x :
    x ∈ (\bigcap (∅ : {set {set T}})).
Proof.
    apply /bigcapP => f F.
    move : (in_set0 f); rewrite F => //.
Qed.    



Theorem setBIC :
    ¬ (\bigcap AA) = \bigcup_(A in AA) (¬ A).
Proof.
    apply extension; apply /subsetP => a.
    +   move /setCP => F.
        apply /bigcupP.
        suff : exists A, A ∈ AA /\ a ∈ ¬ A.
            move => [A' [l r]]; exists A' => //.
        apply not_all_not_ex => f; apply F.
        apply /bigcapP => A HA.
        move : (f A).
        case /not_and_or => H.
        -   case (H HA).
        -   move /setCP : H.
            rewrite Unnamed_thm5 => //.
    +   move /bigcupP => [A HAA /setCP HA].
        apply /setCP => /bigcapP F.
        apply HA; apply  F => //.
Qed.   


End Bigop.



Section bigimage.

Context {T T' : finType} .
Variable (A : {set T}) (P : {set {set T}}) (B : {set T'}) (Q : {set {set T'}}) (f : A ⟶ B).
Hypotheses HP : P ⊂ powerset A.
Hypotheses HQ : Q ⊂ powerset B.


Theorem imageBU :
    Image f (⊔ P) =  \bigcup_(Pi in P) (Image f Pi).
Proof.
    apply extension; apply /subsetP => x.
    +   move /ImageP => [X [HX Him]].
        move /bigcupP : HX => [XX hXX XXX ].
        apply /bigcupP.
        exists XX => //.
        apply /ImageP.
        exists X => //.
    +   move /bigcupP => [XX HXX Him].
        move /ImageP : Him => [X [HX fX]].
        apply /ImageP.
        exists X; split => //.
        apply /bigcupP; exists XX => //.
Qed.  


Theorem imageBI :
    Image f (⊓ P) ⊂ \bigcap_(Pi in P) (Image f Pi).
Proof.
    apply /subsetP => b.
    move /ImageP => [a [Ha fa]].
    move /bigcapP : Ha => Ha.
    (* move /imageP : fa => fa. *)
    apply /bigcapP => X HX.
    apply /ImageP.
    exists a; split => //.
    apply Ha => //.
Qed.

Theorem preimageBU :
    Preimage f (⊔ Q) =  \bigcup_(Qi in Q) (Preimage f Qi).
Proof.
    apply extension; apply /subsetP => a.
    +   move /PreimageP => [b [fa Hb]].
        move /bigcupP : Hb => [Y YQ bY].
        apply /bigcupP.
        exists Y => //.
        apply /PreimageP.
        exists b => //.
    +   move /bigcupP => [Y YQ fb].
        move /PreimageP : fb => [b [fa bY]].
        apply /PreimageP.
        exists b; split => //.
        apply /bigcupP.
        exists Y => //.
Qed.



Theorem preimageBI :
    Q <> ∅ -> Preimage f (⊓ Q) = \bigcap_(Qi in Q) (Preimage f Qi).
Proof.
    move => H0.
    apply extension; apply /subsetP => a.
    +   move /PreimageP => [b [fa Hb]].
        move /bigcapP : Hb => Hb.
        apply /bigcapP => Y HY.
        apply /PreimageP.
        exists b; split => //.
        apply Hb => //.
    +   move /bigcapP => H.
        apply /PreimageP.
        move /eqP /set0Pn : H0 => [Y YQ].
        move : (H Y YQ).
        move /PreimageP => [b [fa bY]].
        exists b; split => //.
        apply /bigcapP => Y' Y'Q.
        move : (H Y' Y'Q).
        move /PreimageP => [b' [fa' b'Y']].
        suff : b = b'.
            by move ->.
        apply (Map.theorem fa fa').
Qed.    
    

End bigimage.








            