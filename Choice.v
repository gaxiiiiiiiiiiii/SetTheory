Require Export Bigop.


Definition nprod {L T : finType} {I : {set L}} {X : {set {set T}}} (g : I ⟶ X) :=
    [set f : I ⟶ ⊔ X | [forall i , (i ∈ I) ==> image f i ⊂ ⊔ image g i]].

Axiom choicep : forall {L T : finType} {I : {set L}} {X : {set {set T}}} (g : I ⟶ X),
    (forall i, i ∈ I -> image g i <> [set ∅]) -> nprod g <> ∅.

Theorem choice {T : finType} (X : {set {set T}}) :
   X <> ∅ -> ~ ∅ ∈ X -> (exists f : X ⟶ ⊔ X, forall x, x ∈ X -> image f x ⊂ x).
Proof.
    move /eqP /set0Pn => [x hx] H0.
    suff : exists f, f ∈ nprod (id X).
        move => [f].
        rewrite in_set => Hf.
        exists f.
        move => y Hy.
        move /forallP /(_ y) /implyP /(_ Hy) /subsetP in Hf.
        apply /subsetP => i.
        move /Hf /bigcupP => [y_ Hy_ iy]; move : Hy_.
        move /imageP => /=.
        rewrite in_set.
        move /andP => /= [_ /eqP] -> //.
    apply /set0Pn /eqP.
    apply  choicep.
    move => i Hi F.
    apply H0.
    suff : i = ∅.
        move <- => //.
    apply /set1P.
    rewrite -F.
    apply /imageP => /=.
    rewrite in_set.
    apply /andP; split => //.
    apply /setXP => //.
Qed.  






Theorem surj_invr {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :
    surj f <-> exists g : B ⟶ A, f ○ g = id B.
Proof.             
    split; rewrite /surj => /=.
    +   move => H.
        pose AA := 
            [set A : {set T} | [exists b, (b ∈ B) && (A == image (inv f) b)]].        
        induction f as [Γ Hm_] => /=.
        induction Γ as [G Hf_] => /=.
        move : (map_mixin_elim Hm_) => Hm.
        move : (func_mixin_elim Hf_) => Hf.
        pose f := mkMap (mkFunc G Hf_) Hm_.
        simpl in AA.        
        have HAA : ⊔ AA  = A.
            apply extension; apply /subsetP => a.
            -   move /bigcupP => [A_].
                rewrite in_set.
                move /existsP => [b /andP[Hb /eqP]] ->.
                rewrite in_inv.
                move /imageP => /=.
                move /Hf => /= [Ha _]; apply Ha.
            -   move /Hm => [b fa].
                have : b ∈ image (mkFunc G Hf_) a.
                    rewrite fa; apply /set1P => //.
                move /imageP /Hf => /= [_ Hb].
                apply /bigcupP.
                exists (image (inv (mkFunc G Hf_)) b).
                *   rewrite in_set.
                    apply /existsP; exists b.
                    apply /andP => //.
                *   rewrite in_inv.
                    rewrite fa; apply /set1P => //.
        pose G' :=
            [set u in setX B AA | u.2 == image (inv (mkFunc G Hf_)) u.1].
        have fHG'_ : func_mixinb B AA G'.
            apply /forallP => u.
            apply /implyP; rewrite in_set.
            destruct u as [a b] => /=.
            move /andP => [HG _].
            move /setXP /andP : HG => //.
        pose fG' := mkFunc G' fHG'_.
        have mHG'_ : map_mixinb B AA fG'.
            apply /forallP => b.
            apply /implyP => Hb.
            apply /existsP.
            exists (image (inv (mkFunc G Hf_)) b).
            apply /eqP; apply extension; apply /subsetP => a.
            -   move /imageP; rewrite in_set => /=. 
                move /andP => [_ /eqP] ->; apply /set1P => //.
            -   move /set1P ->; apply /imageP; rewrite in_set => /=.
                apply /andP; split => //.
                apply /setXP; split => //.
                rewrite in_set; apply /existsP; exists b.
                apply /andP => //.
        pose g' := mkMap fG' mHG'_.
        move : (map_mixin_elim mHG'_ ) => mHG'.
        move : (func_mixin_elim fHG'_) => fHG'.
        have : nprod g' <> ∅.
            apply choicep => b Hb F.
            have : ∅ ∈ image g' b.
                rewrite F; apply /set1P => //.
            move /imageP => /=.
            rewrite in_set => /=; move /andP => [_ /eqP H1].
            rewrite -H in Hb.
            move /rangeP : Hb => [a].
            move /imageP.
            rewrite -in_inv => /=.
            rewrite -H1 in_set0 => //.
        move /eqP /set0Pn => [g Hg ].
        pose ids := [set u in setX (⊔ AA) A | u.1 == u.2 ].
        have  idfH : func_mixinb (⊔ AA) A ids.
            apply /forallP => u.
            induction u as [x y].
            apply /implyP; rewrite in_set.
            move /andP => /= [/setXP /andP Hxy _] //.
        pose idf := mkFunc ids idfH.
        have idmH : map_mixinb (⊔ AA) A idf.
            apply /forallP => a.
            apply /implyP.
            move /bigcupP => [A_ HA_ Ha].
            rewrite in_set in HA_.
            move /existsP : HA_ => [b /andP [Hb /eqP HA_]].
            rewrite HA_ in_inv in Ha.
            move /imageP : Ha => /= Hab.
            move : (Hf _ Hab) => /= [aA bB].
            apply /existsP; exists a.
            apply /eqP; apply extension; apply /subsetP => a_.
            -   move /imageP.
                rewrite in_set => /=.
                move /andP => [_ /eqP ->].
                apply /set1P => //.
            -   move /set1P ->.
                apply /imageP; rewrite in_set => //.
                apply /andP; split => //.
                apply /setXP; split => //.
                apply /bigcupP.
                exists (image (inv (mkFunc G Hf_)) b).
                *   rewrite in_set.
                    apply /existsP; exists b; apply /andP => //.
                    rewrite in_inv; apply /imageP => //=.
        pose idm := mkMap idf idmH.
        exists (idm ○ g).
        rewrite in_set in Hg.
        move /forallP : Hg => Hg.
        apply map_extension => /=.
        apply extension; apply /subsetP => u; induction u as [b b']; rewrite !in_set => /=.
        -   move /existsP => [a /andP [Hba Hab']].
            rewrite in_set in Hba.
            move /existsP : Hba => /= [a' /andP [Hba' Haa]].
            rewrite in_set in Haa.
            move /andP : Haa => /= [_ /eqP aa]; subst a'.
            induction g as [h Hhm_ ].
            induction h as [F HFf_].
            move : (map_mixin_elim Hhm_) => Hhm.
            move : (func_mixin_elim HFf_) => HFf.
            simpl in Hba'.
            move : (HFf _ Hba') => /= [Hb _].
            move : (Hf _ Hab') => /= [_ Hb'].
            apply /andP; split => //.
            apply /andP; split => //.
            move : Hg; move /(_ b).
            move /implyP /(_ Hb) /subsetP => /= Hg.
            have : a ∈ image (mkFunc F HFf_) b.
                apply /imageP => //=.
            move /Hg /bigcupP => [A_ HA_].
            move /imageP : HA_ => /=.
            rewrite in_set; move /andP => /= [_ /eqP] ->.
            rewrite in_inv; move /imageP => /= Hab.
            apply /eqP.
            apply (map_theorem f a b b'); apply /imageP => //=.
        -   move /andP => [/andP [Hb _] /eqP bb]; subst b'.
            move : Hg; move /(_ b) /implyP /(_ Hb) /subsetP => Hg.
            induction g => /=.
            move : (map_mixin_elim axiom).
            move /(_ b Hb) => [a gba].
            have gb : a ∈ image sort b.
                rewrite gba; apply /set1P => //.
            move : (Hg _ gb ); move /bigcupP => [A_].
            move /imageP.
            rewrite in_set => /= /andP [_ /eqP] ->.
            rewrite in_inv; move /imageP => /= Hab.
            apply /existsP; exists a; apply /andP; split => //.
            rewrite in_set => /=.
            apply /existsP; exists a; apply /andP; split.
            *   apply /imageP => //.
            *   rewrite in_set => /=; apply /andP; split => //.
                move : (Hf _ Hab) => /= [Ha _].
                apply /setXP; split => //.
                apply /bigcupP.
                exists (image (inv f) b).
                +   rewrite in_set.
                    apply /existsP; exists b; apply /andP; split => //.
                +   rewrite in_inv; apply /imageP => //=.
    +   move => [g Hg].
        apply extension; apply /subsetP => b.
        move /rangeP => [a Hab].
        induction f as [F Hfm_].
        induction F as [Γ Hff_].
        move : (func_mixin_elim Hff_).
        move /(_ _ Hab) => /= [_] //.
    +   move => Hb.
        have : (b, b) ∈ id B.
            rewrite in_set; apply /andP; split => //.
            apply /setXP; split => //.
        rewrite -Hg.
        rewrite in_set => /=.
        move /existsP => [a /andP [_ Hab]].
        apply /rangeP; exists a => //.
Qed.   

Theorem inj_invl {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B) :
    inj f <-> exists g : B ⟶ A, g ○ f = id A.
Proof.
    induction f as [Gf Hfm_].
    induction Gf as [F Hff_].
    move : (func_mixin_elim Hff_) => Hff.
    move : (map_mixin_elim Hfm_) => Hfm.
    split; rewrite /inj; first last.
    +   move => [g Hg] a a' Ha Ha' H.
        induction g as [Gg Hgm_].
        induction Gg as [G Hgf_].
        move : (func_mixin_elim Hgf_) => Hgf.
        move : (map_mixin_elim Hgm_) => Hgm.  
        simpl.
        
        have : (a,a) ∈ id A.
            rewrite in_set; apply /andP; split => //.
            apply /setXP => //.
        rewrite -Hg in_set => /=.
        move /existsP => [b /andP [abF baG]].

        have : (a',a') ∈ id A.
            rewrite in_set; apply /andP; split => //.
            apply /setXP => //.
        rewrite -Hg in_set => /=.
        move /existsP => [b' /andP [abF' baG']].

        move : (Hfm _ Ha) => [b0 Hb0].
        move : (Hfm _ Ha') => [b0' Hb0'].
        rewrite H in Hb0.
        rewrite Hb0' in Hb0.
        have bb : b0 = b0'.
            apply /set1P; rewrite Hb0; apply /set1P => //.
        subst b0'; clear Hb0.

        have bb : b = b0.
            apply /set1P; rewrite -Hb0'; rewrite -H; apply /imageP => //.
        subst b0.
        have bb : b' = b.
            apply /set1P; rewrite -Hb0'; apply /imageP => //.
        subst b'.

        apply (map_theorem (mkMap (mkFunc G Hgf_) Hgm_) b a a');
        apply /imageP => //.
    
    +   move => /= H.
        pose f := mkMap (mkFunc F Hff_) Hfm_.
        pose G' := [set u | (u.2, u.1) ∈ f].
        have Hgf : func_mixinb (range f) A G'.
            apply /forallP => u; induction u as [b a].
            apply /implyP; rewrite in_set => /= Hab.
            move : (Hff _ Hab) => /= [Ha Hb].
            apply /andP; split => //.
            apply /rangeP; exists a => //.
        pose Gg' := mkFunc G' Hgf.
        have Hgm : map_mixinb (range f) A Gg'.
            apply /forallP => b.
            apply /implyP.
            move /rangeP => [a Hab].
            apply /existsP; exists a.
            apply /eqP; setE a_.
            +   pose f'b := preimage f b.
                move /imageP.
                rewrite in_set => /= Hab_.
                apply /set1P.
                apply H.
                move : (Hff _ Hab_); case => //=.
                move : (Hff _ Hab); case => //.
                
        

        have : (a,a) ∈ id A.
            rewrite in_set; apply /andP; split => //.
            apply /setXP => //.



