Section Inv.

Context {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B).
Hypotheses Hbi : bij f.

Theorem inv_map_mixin :
    map_mixinp (range f) A  (inv f).
Proof.
    inductionM f Gf Hfm domA imA F Hf_ Hf.
    split.
    +   setE b.
        -   move /domainP => [a].
            rewrite in_set => /=.
            move /Hf; case => //=.
        -   move => Hb.
            apply /domainP.
    move : Hbi => [surjf injf].
    move /bij_inv : Hbi => [H' Hf'] => //.
    apply /map_mixinP => //.
Qed.    
  
Definition Inv  :=    
    mkMap (inv f) (map_mixin_intro inv_map_mixin).

Theorem compKl :
    Inv ○ f = id A.
Proof.
    move : Hbi; rewrite /bij /inj /surj; move => [Hs Hi].
    move /bij_inv : Hbi => [axiom' [ Hs' Hi']].
    apply map_extension; apply extension; apply /subsetP => u /=; induction u as [a a'].
    +   induction f as [Γ axiom_].
        move : (map_mixin_elim axiom_) => axiom.
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
    move /bij_inv : Hbi => [axiom'_ [ Hs' Hi']].
    move : (map_mixin_elim axiom'_) => axiom'.
    apply map_extension; apply extension; apply /subsetP => u /=; induction u as [b b'].
    +   induction f as [Γ axiom_].
        move : (map_mixin_elim axiom_) => axiom.
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