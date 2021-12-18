Require Export Bigop.



Section Choice.

Context {L T : finType} {I : {set L}} {A : {set {set T}}} (g : I ⟶ A).

Definition choiceb (f : I ⟶ ⊔ A) := 
    (range g == A) && [forall i, i ∈ I ==> image f i ⊂ ⊔ image g i].

Definition nprod :=
    [set f : I ⟶ ⊔ A | choiceb f].

Definition choicep (f : I ⟶ ⊔ A) := 
    range g = A /\ forall i, i ∈ I -> image f i ⊂ ⊔ image g i.

Theorem choice_intro (f : I ⟶ ⊔ A) :
    choicep f -> choiceb f.
Proof. 
    move => [/eqP Ha H].
    apply /andP; split => //.
    apply /forallP => i.
    apply /implyP => Hi.
    apply H => //.
Qed.

Theorem choice_elim (f : I ⟶ ⊔ A) :
    choiceb f -> choicep f.
Proof.
    move /andP => [/eqP Ha H]; split => //.
    move => i Hi; move : H.
    move /forallP /(_ i) /implyP /(_ Hi) => //.
Qed.

Theorem choiceP (f : I ⟶ ⊔ A) :
    reflect (choicep f) (choiceb f).
Proof.
    apply (iffP idP).
    +   apply choice_elim.
    +   apply choice_intro.
Qed.

Axiom choice :
    (forall i, i ∈ I -> image g i <> [set ∅]) -> nprod <> ∅.



Axiom hoge : forall  {T T' : finType} {A : {set T}} {B B' : {set T'}} (f : A ⟶ B), 
    B = B' -> exists g : A ⟶ B', graph f = graph g.


End Choice.

Theorem extension_mapType {T T' : finType} (A : {set T}) {B B' : {set T'}} :
    B = B' -> A ⟶ B = A ⟶ B'.
Proof.
    move => H.
    apply f_equal => //.
Qed.

Definition extension_mapRange {T T' : finType} (A : {set T}) {B B' : {set T'}} 
    (H : B = B') : A ⟶ B -> A ⟶ B'.
Proof.
    rewrite (extension_mapType A H) => //.
Qed.








        


Context {T T' : finType} {A : {set T}} {B : {set T'}} (f : A ⟶ B).

Theorem surj_inv :
    surj f <-> exists g : B ⟶ A, f ○ g = id B.
Proof.
    split; rewrite /surj.
    +   move => H.
        pose g' := inv f.
        pose AA : {set {set T}}:= 
            [set Ab :  {set T} | [exists b, (b ∈ B) && (Ab == image g' b)]]. 
        have HA : ⊔ AA = A.
            apply extension; apply /subsetP => a.
            -   move /bigcupP => [A' HAA Ha].
                rewrite in_set in HAA.
                move /existsP : HAA => [b /andP [Hb /eqP gb]].
                move : Ha; subst A'.
                rewrite /g' in_inv.
                move /imageP.
                induction f as [f Hf].
                induction f as [G HG] => /=.
                move : (func_mixin_elim HG) => HG_.
                move /HG_ => /= [Ha _] //.
            -   move => Ha.
                induction f as [Γ Hf_].
                induction Γ as [G HG_].
                move : (map_mixin_elim Hf_) => Hf.
                move : (func_mixin_elim HG_) => HG.
                move : (Hf a Ha) => [b Hb].
                pose A' := image g' b.
                apply /bigcupP.
                have : b ∈ image (mkFunc G HG_) a.
                    rewrite Hb; apply /set1P => //.
                move /imageP => /= Hab.
                exists A'.
                *   rewrite in_set.
                    apply /existsP; exists b.
                    apply /andP; split => //.
                    move : (HG _ Hab) => [_ bB] => //.
                *   rewrite /A'.
                    apply /imageP.
                    rewrite /g' => /=.
                    apply /inv_setP => //=.                          
        pose G := 
            [set u in setX B AA|  (u.1 ∈ B) && (u.2 == image g' (u.1))].
        have HG : func_mixinp B AA G.
            move => u.
            rewrite in_set.
            move /andP => [_ /andP [Hb Ha]].
            split => //.
            rewrite in_set.
            apply /existsP; exists u.1; apply /andP => //.
        pose Γ := mkFunc G (func_mixin_intro HG).
        have HΓ : map_mixinp B AA Γ.
            move => b Hb.
            exists (image g' b).
            apply extension; apply /subsetP => A'.
            -   move /imageP => /=.
                rewrite in_set; move /andP => /= [_ /andP[_ ]].
                move /eqP ->; apply /set1P => //.
            -   move /set1P ->.
                apply /imageP => /=.
                rewrite in_set => /=.
                apply /andP; split.
                *   apply /setXP; split => //.
                    rewrite in_set.
                    apply /existsP; exists b; apply /andP; split => //; apply /eqP => //.
                *   apply /andP; split => //; apply /eqP => //.
        pose g_ := mkMap Γ (map_mixin_intro HΓ).
        have : nprod g_ <> ∅.
            apply choice.
            move => b Hb F.
            have : ∅ ∈ image g_ b.
                rewrite F; apply /set1P => //.
            move /imageP => /=.
            rewrite in_set.
            move /andP => /= [H1 /andP [_ /eqP H0]].
            move : Hb.
            rewrite -H.
            move /rangeP => [a Hab].
            have : a ∈ image g' b.
                apply /imageP => /=.
                apply /inv_setP => //=.
            rewrite -H0 (in_set0 a) => F0.
            inversion F0.
        
        move /eqP /set0Pn => [g'' ].        
        rewrite in_set.
        move /choiceP => [Hl Hr].
        move : (hoge g'' HA) => /= [g Hg].
        induction g'' as [Γ'' axiom''_].
        induction Γ'' as [G'' axiom0''_].
        move : (map_mixin_elim axiom''_) => axiom''.
        move : (func_mixin_elim axiom0''_) => axiom0''.
        exists g.
        apply map_extension => /=.
        apply extension; apply /subsetP => u.
        -   move /comp_setP => /= [a [ga fa2]].
            move : ga; rewrite -Hg => /= ga.
            move : (axiom0'' _ ga) => /= [].
            move /Hr => /= H1.
            rewrite HA => Ha.
            have : a ∈ ⊔ image Γ u.1.
                move /subsetP : H1.
                apply.
                apply /imageP => //=.
            move /bigcupP => [X HX aX].
            move : HX.
            move /imageP.
            rewrite /Γ => /=.
            rewrite in_set.
            move /andP => /= [_ /andP] [u1B /eqP gu1].
            move : aX; rewrite gu1.
            rewrite /g'.
            rewrite in_inv => fa1.
            move : fa2.
            move /imageP => fa2.
            move : (map_theorem f a u.1 u.2 fa1 fa2) => uu.
            rewrite in_set.
            apply /andP; split.
            rewrite (surjective_pairing u).
            apply /setXP.
            rewrite -uu; split => //.
            apply /eqP => //.
        -   rewrite in_set.
            move /andP; rewrite (surjective_pairing u).
            move => [/setXP [uB _] /eqP /= uu].
            rewrite in_set => /=.
            induction g as [Γ' axiom'_].
            move : (map_mixin_elim axiom'_).
            move /(_ _ uB) => [a Ha].
            apply /existsP; exists a.
            apply /andP; split => /=.
            *   apply /imageP; rewrite Ha; apply /set1P => //.
            *   rewrite -uu.
                induction Γ' as [G'].
                simpl in Hg.
                have : a ∈ image (mkFunc G' axiom) u.1.
                    rewrite Ha; apply /set1P => //.                
                simpl in Hr.
                move /(_ _ uB ) /subsetP /(_ a) in Hr.
                move /imageP => /=; rewrite -Hg => gu.
                have : a ∈ ⊔ image Γ u.1.
                    apply Hr.
                    apply /imageP => //=.
                move /bigcupP => [A'].
                move /imageP => /=.
                rewrite in_set.
                move /andP => /= [_ /andP[_ ]].
                move /eqP ->.
                rewrite in_inv.
                move /imageP => //.
    +   move => [g H].
        apply extension; apply /subsetP => b.
        -   induction f as [Γ].
            induction Γ as [G].
            move /rangeP => [a Hab].            
            move : (func_mixin_elim axiom0).
            move /(_ _ Hab) => [] //=.
        -   move => Hb.
            have : (b,b) ∈ id B.
                rewrite in_set => /=.
                apply /andP; split =>  //.
                apply /setXP => //.
            rewrite -H in_set => /=.
            move /existsP => [a /andP [_ fa]].
            apply /rangeP; exists a => //.

Restart. 
    split; rewrite /surj.
    +   move => H.
        pose g' := inv f.
        pose AA : {set {set T}}:= 
            [set Ab :  {set T} | [exists b, (b ∈ B) && (Ab == image g' b)]]. 
        have HA : ⊔ AA = A.
            apply extension; apply /subsetP => a.
            -   move /bigcupP => [A' HAA Ha].
                rewrite in_set in HAA.
                move /existsP : HAA => [b /andP [Hb /eqP gb]].
                move : Ha; subst A'.
                rewrite /g' in_inv.
                move /imageP.
                induction f as [f Hf].
                induction f as [G HG] => /=.
                move : (func_mixin_elim HG) => HG_.
                move /HG_ => /= [Ha _] //.
            -   move => Ha.
                induction f as [Γ Hf_].
                induction Γ as [G HG_].
                move : (map_mixin_elim Hf_) => Hf.
                move : (func_mixin_elim HG_) => HG.
                move : (Hf a Ha) => [b Hb].
                pose A' := image g' b.
                apply /bigcupP.
                have : b ∈ image (mkFunc G HG_) a.
                    rewrite Hb; apply /set1P => //.
                move /imageP => /= Hab.
                exists A'.
                *   rewrite in_set.
                    apply /existsP; exists b.
                    apply /andP; split => //.
                    move : (HG _ Hab) => [_ bB] => //.
                *   rewrite /A'.
                    apply /imageP.
                    rewrite /g' => /=.
                    apply /inv_setP => //=.                          
        pose G := 
            [set u in setX B AA|  (u.1 ∈ B) && (u.2 == image g' (u.1))].
        have HG : func_mixinp B AA G.
            move => u.
            rewrite in_set.
            move /andP => [_ /andP [Hb Ha]].
            split => //.
            rewrite in_set.
            apply /existsP; exists u.1; apply /andP => //.
        pose Γ := mkFunc G (func_mixin_intro HG).
        have HΓ : map_mixinp B AA Γ.
            move => b Hb.
            exists (image g' b).
            apply extension; apply /subsetP => A'.
            -   move /imageP => /=.
                rewrite in_set; move /andP => /= [_ /andP[_ ]].
                move /eqP ->; apply /set1P => //.
            -   move /set1P ->.
                apply /imageP => /=.
                rewrite in_set => /=.
                apply /andP; split.
                *   apply /setXP; split => //.
                    rewrite in_set.
                    apply /existsP; exists b; apply /andP; split => //; apply /eqP => //.
                *   apply /andP; split => //; apply /eqP => //.
        pose g_ := mkMap Γ (map_mixin_intro HΓ).
        have : nprod g_ <> ∅.
            apply choice.
            move => b Hb F.
            have : ∅ ∈ image g_ b.
                rewrite F; apply /set1P => //.
            move /imageP => /=.
            rewrite in_set.
            move /andP => /= [H1 /andP [_ /eqP H0]].
            move : Hb.
            rewrite -H.
            move /rangeP => [a Hab].
            have : a ∈ image g' b.
                apply /imageP => /=.
                apply /inv_setP => //=.
            rewrite -H0 (in_set0 a) => F0.
            inversion F0.
        
        move /eqP /set0Pn => [g0].
        exists g.

Qed.            
            









        