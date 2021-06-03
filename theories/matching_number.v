From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries digraph mgraph sgraph set_tac connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition matchingb (G : sgraph) :=
  [pred M : {set {set G}} |
   (M \subset E(G))  &&
   [forall e1,
       [forall e2,
           (e1 \in M)
             ==> (e2 \in M)
             ==> [forall x : G, (x \in e1) ==> (x \in e2) ==> (e1 == e2)]]]].
Arguments matchingb : clear implicits.
Lemma matchingP (G : sgraph) (M : {set {set G}}) :
  reflect (matching M) (matchingb G M).
Proof.
apply: (iffP idP).
- case/andP=> /subsetP ? H; split=> //.
  move=> e1 e2 e1M e2M x xe1 xe2.
    by move: H=> /forallP /(_ e1) /forallP /(_ e2) /implyP /(_ e1M) /implyP /(_ e2M)
                  /forallP /(_ x) /implyP /(_ xe1) /implyP /(_ xe2) /eqP.
- case=> /subsetP ? H.
  apply/andP; split=> //.
  apply/forallP=> e1; apply/forallP=> e2.
  apply/implyP=> /(H e1 e2) H0; apply/implyP=> /H0 H1.
  apply/forallP=> x.
  apply/implyP=> /H1 H2; apply/implyP=> /H2 H3.
  by apply/eqP.
Qed.
Definition nmatch G := \max_(S in matchingb G) #| S |.

Definition induced_matchingb (G : sgraph) :=
  [pred M : {set {set G}} |
   (M \subset E(G))  &&
   [forall e1,
       [forall e2,
           (e1 \in M)
             ==> (e2 \in M)
             ==> (e1 != e2)
             ==>
             [forall e3,
                 (e3 \in M)
                   ==>
                   (e1 :&: e3 == set0) ||
                   (e2 :&: e3 == set0) ]]]].
Arguments induced_matchingb : clear implicits.
Definition induced_matching (G : sgraph) (M : {set {set G}}) :=
  {subset M <= E(G)} /\
  forall e1 e2,
    e1 \in M -> e2 \in M -> e1 <> e2 ->
                       forall e3, e3 \in M ->
                                         (e1 :&: e3 = set0 \/ e2 :&: e3 = set0).
Lemma induced_matchingP (G : sgraph) (M : {set {set G}}) :
  reflect (induced_matching M) (induced_matchingb G M).
Proof.
apply: (iffP idP).
- case/andP=> /subsetP ? H; split=> //.
  move=> e1 e2 e1M e2M /eqP e12 e3 e3M.
  by move: H=> /forallP /(_ e1) /forallP /(_ e2) /implyP /(_ e1M) /implyP /(_ e2M)
                /implyP /(_ e12) /forallP /(_ e3) /implyP /(_ e3M) /orP [] /eqP ->;
                [left | right].
- case=> /subsetP ? H.
  apply/andP; split=> //.
  apply/forallP=> e1.
  apply/forallP=> e2.
  apply/implyP=> e1M.
  apply/implyP=> e2M.
  apply/implyP=> /eqP e12.
  apply/forallP=> e3.
  apply/implyP=> e3M.
  by case: (H e1 e2 e1M e2M e12 e3 e3M)=> /eqP ->.
Qed.

Definition nindmatch G := \max_(S in induced_matchingb G) #| S |.

Definition is_maximal_matching (G : sgraph) :=
  [pred M : {set {set G}} |
   (M \in matchingb G) &&
   [forall N : {set {set G}}, (M \proper N) ==> (N \notin matchingb G)]].
Definition maximal_matchingb (G : sgraph) :=
  [set M | is_maximal_matching G M].

Definition nminmatch (G : sgraph) :=
  \big[minn/0]_(M <- enum (maximal_matchingb G)) #|M|.
(*
Fail Definition nminmatch' (G : sgraph) :=
  foldr (fun M n => minn #|M| n)
        0 (enum (maximal_matchingb G)).

Definition idM (G : sgraph) (M : {set {set G}}) := M.
Definition nminmatch' (G : sgraph) :=
  foldr (fun M n => minn #|idM M| n)
        0 (enum (maximal_matchingb G)).
*)

(* Hibi-Higashitani-Kimura-O'keefe inequalities *)
Lemma HHKO_1 G : nindmatch G <= nminmatch G.
Abort.

Lemma eq_mem_pred (A : Type) (P Q : pred A) : P =1 Q <-> P =i Q.
Proof. by rewrite /eq_mem /in_mem /=. Qed.

Lemma HHKO_2 G : nminmatch G <= nmatch G.
Proof.
case/boolP: (pred0b (matchingb G)).
- move/pred0P=> H.
  rewrite /nminmatch /maximal_matchingb /is_maximal_matching /nmatch /=.
  rewrite (big_pred0 _ _ _ _ H).
  rewrite big_seq big_pred0 ?leqnn //.
  move=> i.
  move/eq_mem_pred: H.
  by rewrite mem_enum inE => ->.
- case/pred0Pn => z. 
  rewrite -(in_collective z (expose_simpl_pred _)) /= => zmG.
  rewrite /nminmatch /nmatch /=.
  have H: {subset maximal_matchingb G <= matchingb G} 
    by move=> M; rewrite inE /is_maximal_matching=> /andP [].
  have [Max [MmG]]: exists Max,
      Max \in matchingb G /\
              \big[minn/0]_(M <- enum (maximal_matchingb G)) #|M| <= #|Max|.
  + rewrite big_seq.
    apply big_ind.                                
    * by exists z; split; [rewrite zmG | apply leq0n].
    * move=> x y.
      case=> x0 [] ? xx0 [] ? [] ? ?.
      exists x0; split=> //; move: xx0; apply leq_trans; apply geq_minl.
    * move=> M; rewrite mem_enum inE=> /andP [] ? ?.
      by exists M; split; last by apply leqnn.
  + move/leq_trans; apply.
    by apply/leq_bigmax_cond.
Qed.

Lemma matching_disjoint (G : sgraph) (M N : {set {set G}}) :
  matching M -> matching N ->
  (\bigcup_(e in M) e) :&: (\bigcup_(e in N) e) = set0 ->
  matching (M :|: N).
Proof.
case=> HM0 HM1 [] HN0 HN1.
rewrite big_distrr /=; under eq_bigr do rewrite big_distrl /=.
move=> H.
split; first by move=> x; rewrite inE=> /orP; case=> [/HM0 | /HN0].
move=> m n.
rewrite !inE=> /orP [] Hm /orP [] Hn x.
- exact (HM1 m n Hm Hn x).
- move=> xm xn; exfalso; suff: false by done.
  move/eqP: H; rewrite -subset0=> /subsetP /(_ x); rewrite inE; apply.
  apply/bigcupP; exists n=> //.
  apply/bigcupP; exists m=> //.
  by rewrite inE.
- move=> xm xn; exfalso; suff: false by done.
  move/eqP: H; rewrite -subset0=> /subsetP /(_ x); rewrite inE; apply.
  apply/bigcupP; exists m=> //.
  apply/bigcupP; exists n=> //.
  by rewrite inE.
- exact (HN1 m n Hm Hn x).
Qed.

Lemma matching_pushout' (G : sgraph) (M N : {set {set G}}) :
  matching M -> matching N ->
  (forall e, e \in M -> matching (e |: N)) ->
  matching (M :|: N).

Lemma matching_pushout (G : sgraph) (M N : {set {set G}}) :
  matching M -> matching N ->
  matching (M :&: N)-> matching (M :|: N).
Proof.
TODO

move=> HM HN HMN.
apply (matching_setU HM HN).
rewrite setIC big_distrr /=.
apply big_ind.
- done.
- by move=> ? ? /eqP ? /eqP ?; apply/eqP; rewrite setU_eq0; apply/andP; split.
- move=> x xM /=.
  case: (HMN x xM)=> HN0 HN1.
  apply big_ind.
  + by rewrite set0I.
  + move=> y z <-.
    rewrite setIUl=> <-.
    by rewrite setUid.
  + move=> y yN.
    

   big_distrr.
; [done | move=> *; apply setU0 |].

apply disjoint_setI0.


have-> : \bigcup_(e in N) e = N.
rewrite big_distrr /=.
apply/eqP; rewrite -subset0; apply/subsetP=> x; rewrite inE.

Lemma HHKO_3_aux1 G M :
  forall e, e \in E(G) -> 
                  M \in maximal_matchingb G ->
                        exists e', (e' \in M) && (setI e e' != set0).
Proof.
move=> e eEG MmG.
apply/existsP; move: MmG; apply contraLR=> /existsPn.
have H: (forall x : set_of_finType G, ~~ ((x \in M) && (e :&: x != set0))) ->
        forall x : set_of_finType G, (x \in M  -> e :&: x == set0)
          by move=> H x; move: (H x); rewrite negb_and -implybE negbK => /implyP.
move/H=> {H} H.
rewrite inE /is_maximal_matching /= negb_and -implybE.
apply/implyP=> H0.
apply/forallPn=> /=.  
exists (e |: M).
rewrite negb_imply.
apply/andP; split.
- apply properUr.
  apply/negP; rewrite sub1set=> H1.
  move: (H e)=> /(_ H1).
  rewrite setIid.
  case/edgesP: eEG=> x [] y [] -> _.
  by rewrite -cards_eq0 cards2.
- rewrite negbK.
Abort.

Lemma HHKO_3_aux2 G M :
  M \in maximal_matchingb G ->
        exists f : {set G} -> G,
          forall e, e \in E(G) -> f e \in \bigcup_(e in M) e.
Abort.


Lemma HHKO_3 G : nmatch G <= (nminmatch G).*2.
Abort.

move=> G.
set q := nminmatch G.
have: exists S, @is_maximal_matching G S /\ #| S | = q by admit.
case=> S [] H0 H1.
Abort.
