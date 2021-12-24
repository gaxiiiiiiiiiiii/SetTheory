Require Export Func.



Module Map.


    Record map {T T' : finType} (A : {set T}) (B : {set T'}) : Type := Pack {
        sort :> A → B;
        axiom : [forall a, (a ∈ A) ==> [exists b, image sort a == [set b]]]
    }.
    
    

End Map.

Notation map := Map.map.
Notation "A ⟶ B" := (map A B)(at level 30).
Notation mkMap := (Map.Pack _ _ _ _).
Coercion Map.sort : map >-> func.

Definition map_mixinb {T T' : finType} (A : {set T}) (B : {set T'}) (Γ : A → B) :=
    [forall a, (a ∈ A) ==> [exists b, image Γ a == [set b]]].

Definition map_mixinp {T T' : finType} (A : {set T}) (B : {set T'}) (Γ : A → B) :=
    forall a, (a ∈ A) -> exists b, image Γ a = [set b].

Theorem map_mixin_elim {T T' : finType} {A : {set T}} {B : {set T'}} {Γ : A → B} :
        [forall a, (a ∈ A) ==> [exists b, image Γ a == [set b]]] ->
        forall a, (a ∈ A) -> exists b, image Γ a = [set b].
Proof. 
    move /forallP => H a Ha; move : H.
    move /(_ a) /implyP /(_ Ha) /existsP => [b Hb].
    exists b; apply /eqP => //.
Qed. 

Theorem map_mixin_intro {T T' : finType} {A : {set T}} {B : {set T'}} {Γ : A → B} :
        (forall a, (a ∈ A) -> exists b, image Γ a = [set b]) ->
        [forall a, (a ∈ A) ==> [exists b, image Γ a == [set b]]].
Proof.
    move => H. 
    apply /forallP => a; apply /implyP => Ha.
    move : (H a Ha) => [b Hb].
    apply /existsP; exists b; apply /eqP => //.
Qed.    


Theorem map_mixinP {T T' : finType} {A : {set T}} {B : {set T'}} (Γ : A → B) :
    reflect 
        (forall a, (a ∈ A) -> exists b, image Γ a = [set b]) 
        ([forall a, (a ∈ A) ==> [exists b, image Γ a == [set b]]]).
Proof.
    apply (iffP idP).
    +   apply map_mixin_elim.
    +   apply map_mixin_intro.
Qed.

      

                


Theorem map_theorem {T T' : finType} {A : {set T}} {B : {set T'}} (f  : map A B) a b b':
    b ∈ image f a -> b' ∈ image f a -> b = b'.
Proof.
    move => /= H H'.
    have Ha : a ∈ A.
        move /imageP : H.
        induction f, sort => /=.
        clear H'.
        move : (func_mixin_elim axiom0) => H1.
        move /H1 => [Ha _] => //.
    induction f.
    move : H H' => /=.
    move /map_mixinP : axiom.
    move /(_ a Ha); case => b0 ->.
    repeat (move /set1P ->) => //.
Qed.


Section mapCanonical.

    Context {T T' : finType} (A : {set T}) (B : {set T'}).

    Canonical map_subType := Eval hnf in [subType for (Map.sort A B)].

    Definition map_eqMixin := Eval hnf in [eqMixin of (A ⟶  B) by <:].
    Canonical map_eqType := Eval hnf in EqType (A ⟶ B) map_eqMixin.

    Definition map_choiceMixin := [choiceMixin of (A ⟶ B) by <:].
    Canonical map_choiceType := Eval hnf in ChoiceType (A ⟶ B) map_choiceMixin.

    Definition map_countMixin := [countMixin of (A ⟶ B) by <:].
    Canonical map_countType := Eval hnf in CountType (A ⟶ B) map_countMixin.

    Canonical map_subCountType := Eval hnf in [subCountType of (A ⟶ B)].

    Definition map_finMixin := [finMixin of (A ⟶ B) by <:].
    Canonical map_finType := Eval hnf in FinType (A ⟶ B) map_finMixin.

    Canonical map_subFinType := Eval hnf in [subFinType of (A ⟶ B)].

End mapCanonical.














Theorem map_extension {T T' : finType} {A : {set T}} {B : {set T'}} (f f' : A ⟶ B) :
    graph f = graph f' -> f = f'.
Proof.
    move /func_extension.
    induction f, f' => /= ff; subst sort0.
    move : (proof_irrelevance _ axiom axiom0) -> => //.
Qed.        



(* 定理２ *)

Section map.

Variable (T T' : finType) (A : {set T}) (B : {set T'}).



Lemma domain_map (f : A ⟶ B) :
    domain f = A.
Proof.
    destruct f as [Γ Hf].
    destruct Γ as [G HG] => /=.
    (* move /map_mixinP : Hf => Hf => //. *)
    (* move /func_mixinP : HG. => HG. *)
    apply extension; apply /subsetP => a; rewrite in_set => /=.
    +   move /existsP => [b Hab].
        clear Hf.        
        move /func_mixinP /(_ _ Hab) : HG => [Ha _] //=.
    +   move => aA.
        move /map_mixinP /(_ a aA): Hf => [b Hb].
        apply /existsP; exists b.
        suff : b ∈ image (mkFunc G HG) a.
            move /imageP => //.
        rewrite Hb; apply /set1P => //.
Qed.        




Lemma map_graph : forall G : {set T * T'}, G ⊂ setX A B ->
    (exists f : A ⟶ B, G = graph f) <-> 
    (forall a, a ∈ A -> exists ! b, (a,b) ∈ G).
Proof.
    move => G HG.
    split => H.
    +   move : H => [f H].
        induction f as [Γ Hf].
        rewrite H => //= a Ha.
        simpl in H.
        move /map_mixinP /(_ a Ha) : Hf => [b Hb].
        exists b; repeat split. 
        -   suff : b ∈ image Γ a.
                move /imageP => //.
            rewrite Hb; apply /set1P => //.
        -   move => b' /=. 
            move /imageP; rewrite Hb; move /set1P => //=.
    +   have Hc : forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B.
            move /subsetP : HG => HG.
            move => u /HG; rewrite in_set; move /andP => //.
        move /func_mixinP : Hc => Hc.
        pose Γ := mkFunc G Hc.
        have Hm : forall a, a ∈ A -> exists b, image Γ a = [set b].
            move => a /H => Hb.
            induction Hb as [b Hb].
            induction Hb as [Hb unib].
            exists b.
            move /subsetP : HG => HG.
            move : (HG _ Hb); rewrite in_set => /=; move /andP => [aA bB].
            apply extension; apply /subsetP => b'; rewrite in_set.
            -   move /unib ->; apply /set1P => //.
            -   move /eqP ->; apply /imageP => //.
        move /map_mixinP : Hm => Hm.
        exists (mkMap Γ Hm) => //=.
Qed.        

End map.


Definition Image {T T' : finType} {A : {set T}} {B : {set T'}} (f : A → B) (P : {set T}):=
    [set b | [exists a, (a ∈ P) && (b ∈ image f a)]].

Definition Preimage {T T' : finType} {A : {set T}} {B : {set T'}} (f : A → B) (Q : {set T'}) :=
    [set a | [exists b, (b ∈ image f a) && (b ∈ Q)]].

Lemma ImageP {T T' : finType} {A : {set T}} {B : {set T'}} (f : A → B) (P : {set T}) b :
    reflect (exists a, (a ∈ P) /\ (b ∈ image f a)) (b ∈ Image f P).
Proof.
    apply (iffP idP); rewrite in_set.
    +   move /existsP => [a /andP H]; exists a => //.
    +   move => [a H]; apply /existsP; exists a; apply /andP => //.
Qed. 

Lemma PreimageP {T T' : finType} {A : {set T}} {B : {set T'}} (f : A → B) (Q : {set T'}) a :
    reflect (exists b, (b ∈ image f a) /\ (b ∈ Q)) (a ∈ Preimage f Q).
Proof.
    apply (iffP idP); rewrite !in_set => //.
    +   move /existsP => [b /andP Hb]; exists b => //.
    +   move => [b Hb]; apply /existsP; exists b; apply /andP => //.
Qed.    



Section Image.

Variable (T T' : finType) (A P P1 P2 P3 : {set T}) (B Q Q1 Q2 Q3 : {set T'}) (f : A ⟶ B).
Hypotheses PA : P ⊂ A.
Hypotheses PA1 : P1 ⊂ A.
Hypotheses PA2 : P2 ⊂ A.
Hypotheses PA3 : P3 ⊂ A.
Hypotheses QB : Q ⊂ B.
Hypotheses QB1 : Q1 ⊂ B.
Hypotheses QB2 : Q2 ⊂ B.
Hypotheses QB3 : Q3 ⊂ B.

Lemma imageSub : P1 ⊂ P2 -> Image f P1 ⊂ Image f P2.
Proof.
    move => /subsetP H; apply /subsetP => b; rewrite !in_set.
    move => /existsP [a /andP [Hap Hb1]].
    apply H in Hap.
    apply /existsP; exists a; apply /andP => //.
Qed.

Lemma imageU : Image f (P1 ∪ P2) = Image f P1 ∪ Image f P2.
Proof.
    apply extension; apply /subsetP => b; rewrite !in_set.
    +   move => /existsP [a /andP [/setUP [H1 |H2] Hb]]; 
        apply /orP; [left|right]; apply /existsP; exists a; apply /andP => //.
    +   move /orP; case; move /existsP => [a /andP [Ha fa]];
        apply /existsP; exists a; apply /andP; split => //;
        apply /setUP; [left|right] => //.
Qed.

Lemma imageI : Image f (P1 ∩ P2) ⊂ (Image f P1 ∩ Image f P2).
Proof.
    apply /subsetP => b; rewrite !in_set;
    move /existsP => [a /andP [/setIP [HP1 HP2] fa]];
    apply /andP; split; apply /existsP; exists a; apply /andP => //.
Qed.


Lemma ImageD : (Image f A // Image f P) ⊂ Image f (A // P).
Proof.
    apply /subsetP => b; rewrite !in_set.
    move => /andP [F /existsP [a /andP [Ha fa]]]; move : F.
    rewrite negb_exists; move /forallP => H.

    move : (H a); rewrite negb_and; move /orP; case => F.
    +   apply /existsP; exists a; apply /andP; split => //.
        apply /setDP => //.
    +   rewrite fa in F; inversion F.
Qed.    


Lemma preimageSub : 
    Q1 ⊂ Q2 -> Preimage f Q1 ⊂ Preimage f Q2.
Proof.
    move => /subsetP H; apply /subsetP => a.
    move /PreimageP => [b [fa Hb]].
    apply /PreimageP; exists b; split => //.
    apply H => //.
Qed.




Lemma preimageU :
    Preimage f (Q1 ∪ Q2) = Preimage f Q1 ∪ Preimage f Q2.
Proof.
    apply extension; apply /subsetP => a.
    +   move /PreimageP => [b [fa /setUP [H1 | H2]]];
        apply /setUP; [left|right]; apply /PreimageP; exists b => //.
    +   move /setUP; case; move  /PreimageP => [b [fa Hb]];
        apply /PreimageP; exists b; split => //; apply /setUP; [left|right] => //.
Qed.        


Lemma preimageI :
    Preimage f (Q1 ∩ Q2) = Preimage f Q1 ∩ Preimage f Q2.
Proof.
    apply extension; apply /subsetP => a.
    +   move /PreimageP => [b [fa /setIP [H1 H2]]].
        apply /setIP; split; apply /PreimageP; exists b => //.
    +   move /setIP =>  [/PreimageP [b1 [fa1 H1]] /PreimageP [b2 [fa2 H2]]].
        destruct f as [Γ axiom].
        destruct Γ as [G axiom0] => /=.
        have : (a,b1) ∈ G.
            move /imageP in fa1 => //.
        have Hm : func_mixinp A B G.
            apply /func_mixinP => //.
        move /Hm => /= [aA bB].
        have Hf : map_mixinp A B (mkFunc G axiom0).
            apply /map_mixinP => //.
        move : (Hf a aA) => [b Hb].
        rewrite Hb in fa1.
        rewrite Hb in fa2.
        move /set1P in fa1; move /set1P in fa2; subst b1 b2.
        apply /PreimageP; exists b; split.
        +   rewrite Hb; apply /set1P => //.
        +   apply /setIP => //.
Qed.

Lemma preimageD :
    Preimage f (B // Q) = A // Preimage f Q.
Proof.
    apply extension; apply /subsetP => a.
    +   move /PreimageP => [b [fa /setDP [HB HQ]]].
        destruct f as [Γ axiom].
        destruct Γ as [G axiom0].
        move /imageP in fa => /=.
        have Hf : func_mixinp A B G. 
            apply /func_mixinP => //.
        move : (Hf _ fa) => /= [aA bB].
        apply /setDP; split => //.
        apply /negP; move =>  /PreimageP [b' [Hb' F]].
        move /imageP in fa.
        simpl in fa.
        move /map_mixinP /(_ _ aA): axiom => [b'' Hb''].
        move : Hb'; rewrite Hb''; move /set1P => bb; subst b''.
        move : fa => /=; rewrite Hb''; move /set1P => bb; subst b'.
        move /negP : HQ => H.
        case (H F).
    +   move /setDP => [aA /negP F].
        apply /PreimageP.
        destruct f as [Γ axiom].
        destruct Γ as [G axiom0] => /=.
        have Hm : map_mixinp A B (mkFunc G axiom0).
            apply /map_mixinP => //.
        move : (Hm a aA) => [b Hb].
        exists b; split => /=.
        -   rewrite Hb; apply /set1P => //.
        -   apply /setDP.
            have : b ∈ image (mkFunc G axiom0) a.
                rewrite Hb; apply /set1P => //.
            move /imageP => /=.
            have Hf : func_mixinp A B G by (apply /func_mixinP => //).
            move /Hf => /= [_ bB].
            split => //.
            apply /negP => bQ.
            apply F; apply /PreimageP.
            exists b => /=; split => //.
            rewrite Hb; apply /set1P => //.
Qed.

Lemma imageK :
    P ⊂ Preimage f (Image f P).
Proof.
    apply /subsetP => a => aP.
    induction f.
    move /subsetP : PA => H.
    move : (H a aP) => /=.
    move /map_mixinP : axiom => axiom.
    move  /axiom => [b Hb].
    apply /PreimageP; exists b => /=.
    split.
    +   rewrite Hb; apply /set1P => //.
    +   apply /ImageP; exists a; split => //.
        rewrite Hb; apply /set1P => //.
Qed.

Lemma preimageK :
    Image f (Preimage f Q) ⊂ Q.
Proof.
    apply /subsetP => b.
    move /ImageP => [a [ /PreimageP [b' [fa' bQ]] fa]].
    destruct f as [Γ axiom].
    destruct Γ as [G axiom0] => /=.
    move : fa fa' => /=.
    move => /imageP /= HG /imageP /= HG'.
    move /map_mixinP : axiom => axiom.
    have Hf: func_mixinp A B G by (apply /func_mixinP => //).
    move : (Hf _ HG) => /= [aA bB].
    move : (axiom a aA) => [b'' H].
    (* move : Hb''. *)
    (* rewrite ImageP => //= H. *)
    have bb : b ∈ [set b''].
        rewrite -H; apply /imageP => //.
    have bb' : b' ∈ [set b''].
        rewrite -H in_set => //.
    move : bb; move /set1P ->.
    move : bb'; move /set1P <- => //.
Qed.

End Image.


Definition surj {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :=
    range f = B.

Definition inj {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :=
    forall a a', a ∈ A -> a' ∈ A -> image f a = image f a' -> a = a'.

Definition bij {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :=
    surj f /\ inj f.




Theorem inv_bij_ {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :
    (forall b, b ∈ B -> exists a, image (inv f) b = [set a]) <-> bij f.
Proof.
    split => H.
    +   split.
        -   rewrite /surj.
            apply extension; apply /subsetP => b; rewrite in_set.
            *   move /existsP => [a Ha]; move : Ha.
                destruct f as [Γ axiom].
                destruct Γ as [G axiom0].
                have Hf : func_mixinp A B G by (apply /func_mixinP => //).
                move /Hf => /=; case => //.
            *   move /H => [a Ha].
                apply /existsP; exists a.
                have : a ∈ image (inv f) b.
                    rewrite Ha; apply /set1P => //.
                rewrite in_inv //.
                move /imageP => //.
        -   move => a1 a2 Ha1 Ha2 Ha.
            destruct f as [Γ axiom].
            destruct Γ as [G axiom0].
            simpl in Ha; simpl in H.
            have Hm : map_mixinp A B (mkFunc G axiom0) by (apply /map_mixinP => //).
            move : (Hm a1 Ha1) => [b1 Hb1].
            move : (Hm a2 Ha2) => [b2 Hb2].
            rewrite Hb1 Hb2 in Ha.
            have : b1 ∈ [set b2].
                rewrite -Ha; apply /set1P => //.
            move /set1P => bb; subst b2 => {Ha}.
            have : b1 ∈ image (mkFunc G axiom0) a1.
                rewrite Hb1; apply /set1P => //.
            move /imageP => /=.
            have Hf : func_mixinp A B G by (apply /func_mixinP => //).
            move /Hf => /=; case => _.
            move /H => [a Ha]; move.
            have : b1 ∈ [set b1] by apply /set1P => //.
            rewrite -Hb1 -in_inv Ha; move /set1P ->.
            have : b1 ∈ [set b1] by apply /set1P => //.
            rewrite -Hb2 -in_inv Ha; move /set1P ->.
            done.
    +   move : H; case; rewrite /surj /inj => Hi Hs b bB.
        rewrite -Hi in bB.
        move /rangeP : bB => [a Hab].
        exists a; apply extension; apply /subsetP => a'; rewrite in_inv.
        -   move /imageP => Hab'.
            move : (in_graph _ _ Hab') => /= [Ha' _].
            move : (in_graph _ _ Hab) => /= [Ha Hb].
            suff : a = a'.
                move ->; apply /set1P => //.
            apply Hs => //.
            induction f => /=.
            move /imageP : Hab; move /imageP : Hab' => /=.
            have Hm : map_mixinp A B sort by (apply /map_mixinP => //).            
            move : (Hm _ Ha); case => b0 ->.
            move : (Hm _ Ha'); case => b0' ->.
            move /set1P ->; move /set1P -> => //.
        +   move /set1P ->; apply /imageP => //.
Qed.

Theorem inv_bij {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :
    (exists H f', f' = mkMap (inv f) H) <-> bij f.
Proof.
    split.
    +   move => [H HH]. 
        rewrite -inv_bij_ => //.
        apply /map_mixinP => //.
    +   rewrite -inv_bij_ => H.
        move /map_mixinP : H => H.
        pose f' := mkMap (inv f) H.
        exists H, f' => //.
Qed.        

Theorem bij_inv {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :
    bij f -> exists H, bij (mkMap (inv f) H).
Proof.
    move  => H.
    inversion H; move : H.
    rewrite -inv_bij.
    move => [H [f' Hf]].
    have H_ : map_mixinp B A (inv f) by (apply /map_mixinP => //).
    exists H; split.
    +   rewrite /surj rang_inv domain_map => //.
    +   rewrite /inj=> /= b b' bB b'B Hb.
        move : (H_ _ bB) => [a Ha].
        move : (H_ _ b'B) => [a' Ha'].
        rewrite Ha Ha' in Hb.
        have : a' ∈ [set a].
            rewrite Hb; apply /set1P => //.
        move /set1P => aa; subst a' => {Hb}.
        have : a ∈ image (inv f) b.
            rewrite Ha; apply /set1P => //.
        rewrite in_inv; move /imageP => Hab.
        have : a ∈ image (inv f) b'.
            rewrite Ha'; apply /set1P => //.
        rewrite in_inv; move /imageP => Hab'.
        destruct f as [Γ axiom].
        destruct Γ as [G axiom0].
        have axiom0_ : func_mixinp A B G by (apply /func_mixinP => //).
        have axiom_ : map_mixinp A B (mkFunc G axiom0) by (apply /map_mixinP => //).
        move : (axiom0_ _ Hab)=> /=. case => aA _.
        move : Hab Hab'=> /= Hab Hab'.
        move : (axiom_ _ aA) => /= [b0 Hb0].
        have : b = b0.
            apply /set1P; rewrite -Hb0; apply /imageP => //.
        have : b' = b0.
            apply /set1P; rewrite -Hb0; apply /imageP => //.
        move ->; move -> => //.
Qed. 