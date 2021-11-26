Require Export Base.




Section operations.



Variable T : finType.
Variables A B C : {set T}.

(*2.1*)
Lemma cup_def :
    A ∪ B = [set x | (x ∈ A) || (x ∈ B)].
Proof.
    auto.
Qed.

(*2.2*)
Lemma sub_cup_l :
    A ⊂ (A ∪ B).
Proof.
    apply subsetUl.
Qed.

Lemma sub_cup_r :
    B ⊂ (A ∪ B).
Proof.    
    apply subsetUr.
Qed.

(*2.3*)
Lemma subsub__Usub :
    A ⊂ C -> B ⊂ C -> (A ∪ B) ⊂ C.
Proof.
    move => AC AB; apply /subUsetP => //=.
Qed.    


(*2.4*)
Lemma setU_self :
    A ∪ A = A.
Proof.
    apply extension; apply /subsetP => x H.
    +   case /setUP : H => //.
    +   apply /setUP; left => //.
Qed.

(*2.5*)
Lemma cup_comm :
    A ∪ B = B ∪ A.
Proof.
    apply setUC.
Qed.

(*2.6*)
Lemma cup_assoc :
    (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof.
    apply extension; apply /subsetP => x H; 
        apply /setUP; case /setUP : H => H;
        try (case /setUP : H => H).
    +   left => //.
    +   right; apply /setUP; left => //.
    +   right; apply /setUP; right => //.
    +   left; apply /setUP; left => //.
    +   left; apply /setUP; right => //.
    +   right => //.
Restart.
    by rewrite -setUA.
Qed.

(*2.7*)
Lemma sub__setU :
    A ⊂ B <-> A ∪ B = B.
Proof.
    split => H. 
    +   move /subsetP : H => H.
        apply extension; apply /subsetP => x Hx.
        -   case /setUP : Hx => H0 => //.
            apply H => //.
        -   apply /setUP; right => //.
    +   rewrite -H.
        apply subsetUl.
Qed.

(*2.8*)
Lemma sub__UsubU :
    A ⊂ B -> (A ∪ C) ⊂ (B ∪ C).
Proof.
    move /subsetP => H.
    apply /subsetP => x Hx.
    case /setUP : Hx => H0; apply /setUP; [left|right] => //.
    by apply H.
Qed.    

(*2.9*)
Lemma empty_cup :
    ∅ ∪ A = A.
Proof.
    apply set0U.
Qed.

(*2.10*)
Goal (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C).
apply setIUl. Qed.

Goal (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C).
apply setUIl. Qed.


(*2.11*)
Goal (A ∪ B) ∩ A = A.
apply setUK. Qed.

Goal (A ∩ B) ∪ A = A.
apply setIK. Qed.

(*2.12*)
Goal A ∩ (¬ A) = ∅.
Proof.
    apply setICr.
Restart.
    apply extension; apply /subsetP => x H.
    +   case /setIP : H => H /setCP F => //.
    +   rewrite in_set0 in H.
        inversion H.
Qed.        


Goal A ∪ (¬ A) = setT.
Proof.
    apply setUCr.
Restart.
    apply extension; apply /subsetP => x H.
    +   apply in_setT.
    +   apply /setUP.
        remember (x ∈ A) as Hx.
        destruct Hx; [left => //|right].
        apply /setCP => F.
        rewrite F in HeqHx => //.
Qed.  

(*2.13*)
Goal ¬ (¬ A) = A.
Proof.
    apply extension; apply /subsetP => x;
    rewrite 2!in_setC; rewrite Bool.negb_involutive => //.
Qed.

(*2.14*)
Goal  ¬ ∅ = [set: T].
Proof.
    apply setC0.
Restart.
    apply extension; apply /subsetP => x Hx.
    +   apply in_setT.
    +   rewrite in_setC.
        rewrite in_set0 => //.
Qed.

Goal ¬ [set : T] = ∅.
Proof.
    apply setCT.
Restart.
    apply extension; apply /subsetP => x Hx.
    +   rewrite in_setC in Hx.
        rewrite in_setT in Hx.
        inversion Hx.
    +   rewrite in_set0 in Hx.
        inversion Hx.
Qed.


(*2.15*)
Goal A ⊂ B -> (¬ B) ⊂ (¬ A).
Proof.
    move => /subsetP H.
    apply /subsetP => x /setCP Hb.
    apply /setCP => F.
    contradict Hb; apply H => //.
Qed.


(*2.16*)

Goal ¬ (A ∪ B) = (¬ A) ∩ (¬ B).
Proof.
    apply setCU.
Restart.
    apply extension; apply /subsetP => x Hx.
    +   move /setCP : Hx => Hx.
        apply /setIP; split; apply /setCP => F; 
        apply Hx; apply /setUP; [left|right] => //.
    +   move /setIP : Hx => [/setCP nHa /setCP nHb].
        apply /setCP; case /setUP => [Ha|Hb] => //.
Qed.



Goal ¬ (A ∩ B) = (¬ A) ∪ (¬ B).
    apply setCI.
Restart.
    apply extension; apply /subsetP => x Hx.
    +   apply /setUP.
        rewrite in_setC in Hx.
        move /setIP : Hx => Hx. (* H : ~~ b に対しても    、bP : reflect P b　が使える *)
        case : (not_and_or _ _ Hx) => H ;
        [left|right]; apply /setCP => //.
    +   apply /setCP => /setIP [Ha Hb].
        move /setUP : Hx => [/setCP nHa |/ setCP nHb] => //.
Qed.

Goal A ⊂ B -> (¬ B) ⊂ (¬ A).
Proof.
    move => /subsetP H.
    apply /subsetP => x /setCP nHB.
    apply /setCP => HA.
    apply nHB; apply H => //.
Qed.

Variable me : T.

Goal forall someone, someone ∈ ¬ [set me] -> someone <> me.
Proof.
    move => someone /setCP H /eqP F.
    apply H; rewrite in_set1 => //.
Qed. 

End operations.


(* 2.17 *)
Section bigop1.
Variable (T : finType) (A C : {set T}) (U : {set {set T}}).


Goal A ∈ U -> A ⊂ (⊔ U).
Proof.
    move => AU; apply /subsetP => x xA; apply /bigUP; exists A => //.
Qed.

Goal A ∈ U -> ⊓ U ⊂ A.
Proof.
    move => AU; apply /subsetP => x /bigIP H; apply H => //.
Qed.

End bigop1.

Section bigop2.

Variable (T : finType) (C : {set T}) (U : {set {set T}}).

Goal (forall A, A ∈ U -> A ⊂ C) -> ⊔ U ⊂ C.
Proof.
    move => H; apply /subsetP => x /bigUP [Y [xY YU]].
    move : (H Y YU); move /subsetP; apply => //.
Qed.


Goal (forall A, A ∈ U -> C ⊂ A) -> C ⊂ ⊓ U.
Proof.
    move => H; apply /subsetP => x xC; apply /bigIP => Y YU.
    move : (H Y YU); move /subsetP; apply => //.
Qed.

End bigop2.



        
        


















    



        



