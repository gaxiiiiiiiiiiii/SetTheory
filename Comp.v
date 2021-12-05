Require Export Map.

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
Variable (T1 T2 T3 T4: finType).
Variable (A : {set T1}) (B : {set T2}) (C : {set T3}) (D : {set T4}).
Variable (f : A ⟶ B) (g : B ⟶ C) (i : C ⟶ D).

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
Theorem surj_comp :
    surj f -> surj g -> surj (g ○ f).
Proof.
    rewrite /surj => Hf Hg.
    rewrite /comp /compc => /=.
    apply extension; apply /subsetP => c.
    +   move /rangeP; case => a /=.
        move /comp_setP => /= [b [Hab Hbc]].
        rewrite -Hg; apply /rangeP; exists b => //.
    +   move => Hc.
        apply /rangeP => /=.
        rewrite -Hg in Hc; move : Hc.
        move /rangeP => [b Hbc_].
        inversion Hbc_ as [Hbc]; move : Hbc_.
        induction g, Γ => /=.
        move /axiom0 => /= [Hb _].
        rewrite -Hf in Hb; move : Hb.
        move /rangeP => [a Hab].
        exists a; apply /comp_setP; exists b => //.
Qed.

Theorem bij_comp :
    bij f -> bij g -> bij (g ○ f).
Proof.
    move => [Hfs Hfi] [Hgs Hgi]; split.
    +   apply surj_comp => //.
    +   apply inj_comp => //.
Qed.  



Theorem comp_assoc :
    i ○ (g ○ f) = (i ○ g) ○ f.
Proof.
    apply map_extension.
    apply extension; apply /subsetP => //= u; induction u as [a d];
    move /comp_setP => /= [x [l r]]; apply /comp_setP.
    +   move /comp_setP : l =>  /= [b [Hf Hg]].
        exists b; split => //.
        apply /comp_setP; exists x; split => //.
    +   move /comp_setP : r => /= [c [Hg Hi]].
        exists c; split => //=.
        apply /comp_setP; exists x; split => //.
Qed.

End comp.

Section Id.

Context {T : finType} (A : {set T}).

Definition id_set := [set u in setX A A| u.1 == u.2 ].

Theorem id_setP u:
    reflect (u ∈ setX A A /\ u.1 = u.2) (u ∈ id_set).
Proof.
    move : u => [a b]; apply (iffP idP); rewrite in_set => /=.
    +   move /andP => [Ha /eqP ab] => //.
    +   move => [/andP [aA _] Hab]; subst b.
        rewrite in_set; apply /andP; split => //=.
        apply /setXP => //.
Qed.



Definition id_func_mixin : 
    Func.mixin A A (id_set).
Proof.
    move => [a1 a2]; rewrite in_set; move /andP => /= [/setXP [H1 H2] _] => //.
Qed.    

Definition id_func := mkFunc (id_set) (id_func_mixin).

Theorem id_map_mixin : Map.mixin id_func.
Proof.
    move => a Ha; exists a; rewrite image_graph => //=.
    apply extension; apply /subsetP => x; rewrite in_set.
    +   move /id_setP => /= [_ Hax]; subst x.
        apply /set1P => //.
    +   move /set1P ->; rewrite in_set; apply /andP; split => //.
        apply /setXP => //.
Qed.

Definition id := mkMap id_func id_map_mixin.

End Id.


Section IdComp.
Context {T T' : finType} {A : {set T}} {B : {set T'}}.
Variable (f : A ⟶ B).

Theorem comp_idl :
    f ○ (id A) = f.
Proof.
    apply map_extension; apply extension; apply /subsetP => u /=; induction u as [a b].
    +   move /comp_setP => /= [x [/id_setP /= [_ ax] H]]; subst x => //.
    +   induction f, Γ => /= H.
        move : (axiom0 _ H) => /= [aA _].
        apply /comp_setP => /=.
        exists a; split => //.
        apply /id_setP; split => //.
        apply /setXP => //.
Qed.

Theorem comp_idr :
    (id B) ○ f = f.
Proof.
    apply map_extension; apply extension; apply /subsetP => u /=; induction u as [a b].
    +   move /comp_setP => /=.
        move => [x [H /id_setP /= [_ xb]]].
        subst x => //.
    +   induction f, Γ => /= H.
        move : (axiom0 _ H) => /= [_ bB].
        apply /comp_setP => /=.
        exists b; split => //.
        apply /id_setP; split => //.
        apply /setXP => //.
Qed.

End IdComp.

Section Inv.

Context {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B).
Hypotheses Hbi : bij f.

Theorem inv_map_mixin :
    Map.mixin (inv f).
Proof.
    rewrite  /Map.mixin.
    move : Hbi => [surjf injf].
    move /bij_inv : Hbi => [H' Hf'] => //.
Qed.    
  
Definition Inv  :=    
    mkMap (inv f) inv_map_mixin.

Theorem compKl :
    Inv ○ f = id A.
Proof.
    move : Hbi; rewrite /bij /inj /surj; move => [Hs Hi].
    move /bij_inv : Hbi => [axiom' [ Hs' Hi']].
    apply map_extension; apply extension; apply /subsetP => u /=; induction u as [a a'].
    +   induction f => /=.
        move /comp_setP => /= [b [Hf /inv_setP /= Hf']].
        move : (in_graph _ _ Hf) => /= [Ha Hb].
        move : (in_graph _ _ Hf') => /= [Ha' _].
        move : (axiom _ Ha) => [b0 ima].
        move : (axiom _ Ha') => [b0' ima'].
        move /imageP : Hf; rewrite ima; move /set1P => bb; subst b0.
        move /imageP : Hf'; rewrite ima'; move /set1P => bb; subst b0'.
        suff : a = a'.
            move ->; apply /id_setP; split => //.
            apply /setXP => //.
        apply Hi => //=.        
        rewrite ima ima' => //.        
    +   move /id_setP => /= [/setXP [Ha _] aa]; subst a'.
        rewrite -Hs' in Ha.
        move /rangeP : Ha => /= [b /inv_setP /= Hab].
        apply /comp_setP => /=.
        exists b; split => //.
        apply /inv_setP => //.
Qed.  

Theorem compkr :
    f ○ Inv = id B.
Proof.
    move : Hbi; rewrite /bij /inj /surj; move => [Hs Hi].
    move /bij_inv : Hbi => [axiom' [ Hs' Hi']].
     apply map_extension; apply extension; apply /subsetP => u /=; induction u as [b b'].
    +   induction f => /=.
        move /comp_setP => /= [a [/inv_setP /= Hf Hf']].
        move : (in_graph _ _ Hf) => /= [Ha Hb].
        move : (in_graph _ _ Hf') => /= [_ Hb'].
        move : (axiom' _ Hb) => /= [a0 imb].
        move : (axiom' _ Hb') => /= [a0' imb'].
        move /imageP : Hf; rewrite -in_inv imb; move /set1P => aa; subst a0.
        move /imageP : Hf' ; rewrite -in_inv imb'; move /set1P => aa; subst a0'.
        suff : b = b'.
            move ->; apply /id_setP; split => //.
            apply /setXP => //.
        apply Hi' => //=.        
        rewrite imb imb' => //.        
    +   move /id_setP => /= [/setXP [Hb _] bb]; subst b'.
        rewrite -Hs in Hb.
        move /rangeP : Hb => /= [a  Hab].
        apply /comp_setP => /=.
        exists a; split => //.
        apply /inv_setP => //.
Qed.        

End Inv.

Section restrict.
Context {T T' : finType} {A A' : {set T}} {B : {set T'}} (f : A ⟶ B).
Hypotheses AA : A' ⊂ A.

Definition restrict_set (G : {set T * T'})  :=
    [set u in G  | u.1 ∈ A'].


Theorem restrict_func_axiom  (G : {set T * T'}) :
    G ⊂ setX A B -> Func.mixin A' B (restrict_set G).
Proof.
    move => GAB [a b].
    rewrite in_set.
    move /andP => /= [uG Ha].
    move /subsetP : GAB => H.
    move /H /setXP : uG => [_ Hb] => //.
Qed.

Definition restrict_func (G : {set T * T'})(H : G ⊂ setX A B) :=
    mkFunc (restrict_set G) (restrict_func_axiom G H).

Theorem graph_sub :
    graph f ⊂ setX A B.
Proof.
    apply /subsetP => u; induction u as [a b].
    move /in_graph => [Ha Hb].
    apply /setXP => //.
Qed.    



Theorem restrict_map_axiom :
    Map.mixin (restrict_func (graph f) graph_sub).
Proof.
    move : graph_sub. 
    induction f => graph_sub.
    move => a Ha'.
    have Ha : a ∈ A.
        move /subsetP : AA => HA.
        apply HA => //.
    move : (axiom a Ha) => [b ima].
    exists b => /=.
    apply extension; apply /subsetP => b'.
    +   move /imageP => /=.
        rewrite in_set.
        move /andP => /= [/imageP Hab _].
        rewrite -ima => //.
    +   move /set1P ->.
        apply /imageP => /=.
        rewrite in_set; apply /andP; split => //.
        apply /imageP.
        rewrite ima; apply /set1P => //.
Qed.

Definition restrict :=
        mkMap (restrict_func (graph f) graph_sub) restrict_map_axiom.

End restrict.










