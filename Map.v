Require Export Func.

Print SubType.

(* Definition map_pred {T T' : finType} (A : {set T}) (B : {set T'}) u :=
    [forall a, a ∈ A ==> 
        [exists b, (b ∈ B) && ((a,b) == u) && 
            [forall b', (b' ∈ B) && ((a,b') == u) ==> (b == b')]
        ]
    ].



Definition map_set_ {T T' : finType} (A : {set T}) (B : {set T'}) :=
    [set u : T * T' | map_pred A B u].

Search "sub" "Type".    


Lemma map_setP_ {T T' : finType} (A : {set T}) (B : {set T'}) u :
    reflect (forall a, a ∈ A -> exists! b, b ∈ B /\ (a,b) = u ) (u ∈ (map_set_ A B)).
Proof.
    apply (iffP idP); rewrite in_set.
    +   move /forallP => H a Ha.
        move : (H a) => {H}; move /implyP => H.
        move : (H Ha) => {H}; move /existsP => 
            [b /andP [/andP [Hb /eqP Hu] /forallP Huni ]]; subst u.
        exists b; repeat split => //.
        move => b' [Hb' Hab]; apply /eqP; move : (Huni b'); 
        move /implyP; apply; apply /andP; split => //; apply /eqP => //.
    +   move => H.
        apply /forallP => a; apply /implyP => Ha; apply /existsP.
        move : (H a Ha) => [b [[Hb Hu] Huni]].
        exists b; apply /andP; split.
        -   apply /andP; split => //; apply /eqP => //.
        -   apply /forallP => b'; apply /implyP => /andP [Hb' Hu'].
            apply /eqP; apply Huni; split => //; apply /eqP => //.
Qed.

Definition map_set {T T' : finType} (A : {set T}) (B : {set T'}) := 
    map_set_ A B ∩ setX A B.

Definition map {T T' : finType} (A : {set T}) (B : {set T'}) :=
    mkFunc (map_set A B) (mixinIX A B (map_set_ A B)).

Notation "A ⟶ B" := (map A B) (at level 30). *)



        


Module Map.

Record map {T T' : finType} (A : {set T}) (B : {set T'}) : Type := Pack {
    Γ :> A → B;
    axiom : forall a, a ∈ A -> exists b, image Γ a = [set b]
}.

End Map.

Notation map := Map.map.
Coercion Map.Γ : map >-> func.
Notation "A ⟶ B" := (map A B)(at level 30).
Notation mkMap := (Map.Pack _ _ _ _).



(* 定理２ *)

Section map.

Variable (T T' : finType) (A : {set T}) (B : {set T'}).




Lemma domain_map (f : A ⟶ B) :
    domain f = A.
Proof.
    destruct f as [Γ Hf].
    destruct Γ as [G HG].
    apply extension; apply /subsetP => a; rewrite in_set => /=.
    +   move /existsP => [b Hab].
        move /HG : Hab; case => //=.
    +   move => aA.
        move : (Hf a aA) => /= [b Hb].
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
        rewrite H => // a Ha.
        move : (Hf a Ha) => [b Hb].
        exists b; repeat split. 
        -   suff : b ∈ image Γ a.
                move /imageP => //.
            rewrite Hb; apply /set1P => //.
        -   move => b' /=. 
            move /imageP; rewrite Hb; move /set1P => //=.
    +   have Hc : forall u, u ∈ G -> u.1 ∈ A /\ u.2 ∈ B.
            move /subsetP : HG => HG.
            move => u /HG; rewrite in_set; move /andP => //.
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
        destruct f.
        destruct Γ.
        have : (a,b1) ∈ G.
            move /imageP in fa1 => //.
        move /axiom0 => /= [aA bB].
        move : (axiom a aA) => [b Hb].
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
        destruct f.
        destruct Γ.
        move /imageP in fa.
        move : (axiom0 _ fa) => /= [aA bB].
        apply /setDP; split => //.
        apply /negP; move =>  /PreimageP [b' [Hb' F]].
        move /imageP in fa.
        move : (axiom _ aA) => [b'' Hb''].
        move : Hb'; rewrite Hb''; move /set1P => bb; subst b''.
        move : fa => /=; rewrite Hb''; move /set1P => bb; subst b'.
        move /negP : HQ => H.
        case (H F).
    +   move /setDP => [aA /negP F].
        apply /PreimageP.
        destruct f, Γ.
        move : (axiom a aA) => [b Hb].
        exists b; split => /=.
        -   rewrite Hb; apply /set1P => //.
        -   apply /setDP.
            have : b ∈ image (mkFunc G axiom0) a.
                rewrite Hb; apply /set1P => //.
            move /imageP => /=.
            move /axiom0 => /= [_ bB].
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
    move : (H a aP).
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
    induction f, Γ.
    move : fa fa' => /=.
    move => /imageP HG /imageP HG'.
    move : (axiom0 _ HG) => /= [aA bB].
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
                induction f, Γ => /=.
                move /axiom0 => /=; case => //.
            *   move /H => [a Ha].
                apply /existsP; exists a.
                have : a ∈ image (inv f) b.
                    rewrite Ha; apply /set1P => //.
                rewrite in_inv //.
                move /imageP => //.
        -   move => a1 a2 Ha1 Ha2 Ha.
            induction f, Γ.
            simpl in Ha; simpl in H.
            move : (axiom a1 Ha1) => [b1 Hb1].
            move : (axiom a2 Ha2) => [b2 Hb2].
            rewrite Hb1 Hb2 in Ha.
            have : b1 ∈ [set b2].
                rewrite -Ha; apply /set1P => //.
            move /set1P => bb; subst b2 => {Ha}.
            have : b1 ∈ image (mkFunc G axiom0) a1.
                rewrite Hb1; apply /set1P => //.
            move /imageP => /=; move /axiom0 => /=; case => _.
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
            move : (axiom _ Ha); case => b0 ->.
            move : (axiom _ Ha'); case => b0' ->.
            move /set1P ->; move /set1P -> => //.
        +   move /set1P ->; apply /imageP => //.
Qed.

Theorem inv_bij {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :
    (exists H f', f' = mkMap (inv f) H) <-> bij f.
Proof.
    split.
    +   move => [H _]; rewrite -inv_bij_ => //.
    +   rewrite -inv_bij_ => H.
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
    exists H; split.
    +   rewrite /surj rang_inv domain_map => //.
    +   rewrite /inj=> /= b b' bB b'B Hb.
        move : (H _ bB) => [a Ha].
        move : (H _ b'B) => [a' Ha'].
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
        induction f, Γ.
        move : (axiom0 _ Hab)=> /=. case => aA _.
        move : Hab Hab'=> /= Hab Hab'.
        move : (axiom _ aA) => /= [b0 Hb0].
        have : b = b0.
            apply /set1P; rewrite -Hb0; apply /imageP => //.
        have : b' = b0.
            apply /set1P; rewrite -Hb0; apply /imageP => //.
        move ->; move -> => //.
Qed. 






Definition comp_set  {T1 T2 T3 : finType} (G : {set T2 * T3}) (F : {set T1 * T2}) :=
    [set u | [ exists b, ((u.1, b) ∈ F) && ((b,u.2) ∈ G) ]].


Lemma comp_setP  {T1 T2 T3 : finType} (G : {set T2 * T3}) (F : {set T1 * T2}) u :
    reflect ( exists b, ((u.1, b) ∈ F) /\ ((b,u.2) ∈ G)) (u ∈ comp_set G F).
Proof.
    apply (iffP idP); rewrite in_set.
    +   move /existsP => [b /andP Hb]; exists b => //.
    +   move => [b Hb]; apply /existsP; exists b; apply /andP => //.
Qed.

Lemma compcH {T1 T2 T3 : finType} {A : {set T1}} {B : {set T2}} {C : {set T3}} 
    (g : B → C) (f : A → B) : let gf := comp_set (graph g) (graph f) in
    forall u, u ∈ gf -> u.1 ∈ A /\ u.2 ∈ C.
Proof.    
    move => gf u /comp_setP; case => b; case => //.
    induction f as [f_ Hf], g as [g_ Hg] => /=.
    move /Hf => /= [Ha Hb].
    move /Hg => /= [_ Hc].
    done.
Qed.

Definition compc {T1 T2 T3 : finType} {A : {set T1}} {B : {set T2}} {C : {set T3}} 
    (g : B → C) (f : A → B) : A → C := mkFunc (comp_set (graph g) (graph f)) (compcH g f).


Lemma compH {T1 T2 T3 : finType} {A : {set T1}} {B : {set T2}} {C : {set T3}} 
    (g : B ⟶ C) (f : A ⟶ B) : 
    forall a, a ∈ A -> exists b, image (compc g f) a = [set b].
Proof.
    induction f as [Γf Hf], g as [Γg Hg].
    induction Γf as [Gf HGf], Γg as [Gg HGg].
    move => a /=.
    move /Hf => [b Hb].
    have : (a,b) ∈ graph (mkFunc Gf HGf).
        apply /imageP; rewrite Hb; apply /set1P => //.
    move /HGf; case => _ /=.
    move /Hg => [c Hc].
    have : (b,c) ∈ graph (mkFunc Gg HGg).
        apply /imageP; rewrite Hc; apply /set1P => //.
    move /HGg => /= [bB cC].
    exists c.
    apply extension; apply /subsetP => c'. move /imageP => /=.
    +   move /comp_setP => /= [b' [Hb' Hc']].
        have bb : b' = b.
            apply /set1P; rewrite -Hb; apply /imageP => //=.
        subst b'.
        have cc : c' = c.
            apply /set1P; rewrite -Hc. apply /imageP => //.
        subst c'.
        apply /set1P => //.
    +   move /set1P ->.
        apply /imageP => /=.
        apply /comp_setP; exists b => /=; split.
        -   suff : b ∈ image (mkFunc Gf HGf) a.
                apply /imageP => //.
            rewrite Hb; apply /set1P => //.
        -   suff : c ∈ image (mkFunc Gg HGg) b.
                apply /imageP => //.
            rewrite Hc; apply /set1P => //.
Qed.            

Definition comp   {T1 T2 T3 : finType} {A : {set T1}} {B : {set T2}} {C : {set T3}} 
    (g : B ⟶ C) (f : A ⟶ B) := mkMap (compc g f) (compH g f).

Notation "g ○ f" := (comp g f) (at level 30).

Lemma image_comp {T1 T2 T3 : finType} {A : {set T1}} {B : {set T2}} {C : {set T3}} 
    (g : B ⟶ C) (f : A ⟶ B) : 
    forall a, a ∈ A -> image (g ○ f) a = Image g (image f a).
Proof.
    move => a ha.
    apply extension; apply /subsetP => c.
    +   move /imageP /comp_setP => /= [b [Hab Hbc]].
        apply /ImageP. exists b; split; apply /imageP => //.
    +   move /ImageP => [b [Hab Hbc]].
        apply /imageP; apply /comp_setP; exists b; split; apply /imageP => //.
Qed.

Section comp.
Variable (T1 T2 T3 : finType) (A : {set T1}) (B : {set T2}) (C : {set T3}).
Variable (f : A ⟶ B) (g : B ⟶ C).

Theorem inj_comp :
    inj f -> inj g -> inj (g ○ f).
Proof.
    move => Hf Hg a a' Ha Ha' H. 

    remember (g ○ f) as h.
    rewrite /comp /compc in Heqh.



    induction h as [Γh Hh].
    move : (Hh a Ha) => [c0 ha].
    move : (Hh a' Ha') => [c0' ha'].
    move : H => /=; rewrite ha ha' => cc'.
    have cc : c0' = c0.
        apply /set1P; rewrite cc'; apply /set1P => //.
    subst c0' => {cc'}.
    inversion Heqh => {Heqh}.


    have: c0 ∈ image Γh a.
        rewrite ha; apply /set1P => //.
    have : c0 ∈ image Γh a'.
        rewrite ha'; apply /set1P => //.
    rewrite H0.
    (* rewrite !ImageP => /=. *)
    move /imageP /comp_setP => /= [b0' [fa' gb0']].
    move /imageP /comp_setP => /= [b0 [fa gb]].
    

    
    move : (Hf a a' Ha Ha').
    apply.
    induction f => /=.
    move : Ha'; move /axiom => [b' fb'].
    move : Ha;  move /axiom => [b fb].
    rewrite fb fb'.
    suff : b = b'.
        move -> => //.
        
    
    induction Γ as [G HG].
    have : (a,b) ∈ graph (mkFunc G HG).
        apply /imageP; rewrite fb; apply /set1P => //.
    have : (a',b') ∈ graph (mkFunc G HG).
        apply /imageP; rewrite fb'; apply /set1P => //.
    move /HG => /= [Ha' Hb'].
    move /HG => /= [Ha Hb].
    apply Hg => //.

    induction g.
    move : Hb; move /axiom0. move  => [c Hc].
    move : Hb'; move /axiom0 => [c' Hc'].
    rewrite Hc Hc'.
    suff : c = c'.
        move -> => //.


    have : b0 ∈  image (mkFunc G HG) a.
        apply /imageP => //. 
    rewrite fb; move /set1P => bb; subst b0.
    inversion gb.
    move : gb; move /imageP; rewrite Hc; move /set1P <-.
    
    have : b0' ∈  image (mkFunc G HG) a'.
        apply /imageP => //.
    rewrite fb'; move /set1P => bb; subst b0'.    
    move : gb0'; move /imageP; rewrite Hc' ; move /set1P <-.

    done.
Qed.
    


    
    

    
    
    
    
    
    
    
    
    



    


