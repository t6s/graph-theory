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

Definition strongly_disjoint (G : sgraph) (M N : {set {set G}}) :=
  (\bigcup_(e in M) e) :&: (\bigcup_(e in N) e) == set0.

Lemma strongly_disjointP (G : sgraph) (M N : {set {set G}}):
  reflect
    (\bigcup_(i in N) \bigcup_(j in M) (j :&: i) = set0)
    (strongly_disjoint M N).
Proof.
suff-> : strongly_disjoint M N = 
         (\bigcup_(i in N) \bigcup_(j in M) (j :&: i) == set0) by apply: eqP.
by rewrite /strongly_disjoint big_distrr /=; under eq_bigr do rewrite big_distrl /=.
Qed.

Lemma strongly_disjointPn (G : sgraph) (M N : {set {set G}}):
  reflect
    (exists i, exists j, i \in M /\ j \in N /\ i :&: j <> set0)
    (~~ (strongly_disjoint M N)).
Proof.
apply: (iffP idP).
- move/strongly_disjointP.
  move/eqP=> H.
  suff: [exists i, [exists j, (i \in M) && (j \in N) && (i :&: j != set0)]]
    by case/existsP=> [] i /existsP [] j /andP [] /andP [] ? ? /eqP ?; exists i, j.
  move: H; apply: contraLR=> H.
  rewrite negbK big1 ?eqxx // => j jN.
  rewrite big1 ?eqxx // => i iM.
  move:H => /existsPn /(_ i) /existsPn /(_ j) /nandP [];
   last by rewrite negbK=> /eqP.
  by case/nandP; rewrite ?iM ?jN.
- case=> i [] j [] iM [] jN /eqP /set0Pn [] x.
  rewrite inE=> /andP [] xi xj.
  rewrite /strongly_disjoint.
  apply/set0Pn; exists x; rewrite inE.
  by apply/andP; split; apply/bigcupP; [exists i | exists j].
Qed.  

Lemma matching_disjoint_nodes (G : sgraph) (M N : {set {set G}}) :
  matching M -> matching N ->
  strongly_disjoint M N ->
  matching (M :|: N).
Proof.
case=> HM0 HM1 [] HN0 HN1 /strongly_disjointP H.
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

Lemma matching_set1U (G : sgraph) (M N : {set {set G}}) :
  matching M -> matching N ->
  (forall e, e \in M -> matching (e |: N)) ->
  matching (M :|: N).
Proof.
case=> /subsetP MEG mM [] /subsetP NEG mN meN.
split; first by apply/subsetP; rewrite subUset.
move=> e e' eMN e'MN x.
case/boolP: (e \in M); case/boolP: (e' \in M).
- by move=> ? ?; apply mM.
- rewrite -in_setC=> /(conj e'MN) /setIP.
  rewrite -setDE setDUl setDv set0U=> /(subsetP (subsetDl N M)) eN.
  by case/meN=> _; apply; [apply: setU11 | apply: setU1r].
- case/meN=> _ ee.
  rewrite -in_setC=> /(conj eMN) /setIP.
  rewrite -setDE setDUl setDv set0U=> /(subsetP (subsetDl N M)) e'N.
  by apply ee; [apply: setU1r | apply: setU11].
- rewrite -in_setC=> /(conj e'MN) /setIP.
  rewrite -setDE setDUl setDv set0U=> /(subsetP (subsetDl N M)) e'N.
  rewrite -in_setC=> /(conj eMN) /setIP.
  rewrite -setDE setDUl setDv set0U=> /(subsetP (subsetDl N M)) eN.
  by apply: mN.
Qed.

(* ???????
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
*)


Lemma HHKO_3_aux1 G M e :
  e \in E(G) -> 
        M \in maximal_matchingb G ->
              exists e', (e' \in M) && (setI e e' != set0).
Proof.
move=> eEG MmG.
case/boolP: (strongly_disjoint [set e] M); last first.
  case/strongly_disjointPn=> j [] i.
  rewrite inE=> -[] /eqP -> [] iM ei.
  by exists i; apply/andP; split=> //; apply/eqP.
move/strongly_disjointP=> disj.  
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
  rewrite inE; apply/andP; split;
    first by apply/subUsetP; split;
      [rewrite sub1set | case/matchingP: H0=> /subsetP].
  apply/forallP=> e1.
  apply/forallP=> e2.
  rewrite !inE.
  apply/implyP=> /orP [/eqP -> | e1M];
  apply/implyP=> /orP [/eqP -> | e2M];
  apply/forallP=> x;
  apply/implyP=> xe1;
  apply/implyP=> xe2.
  + by rewrite eqxx.
  + move/eqP: disj; apply/contraLR=> e1e2.
    apply/set0Pn; exists x.
    apply/bigcupP; exists e2=> //.
    apply/bigcupP; exists e; first by rewrite inE.
    by rewrite inE.
  + move/eqP: disj; apply/contraLR=> e1e2.
    apply/set0Pn; exists x.
    apply/bigcupP; exists e1=> //.
    apply/bigcupP; exists e; first by rewrite inE.
    by rewrite inE.
  + by case/matchingP: H0=> /subsetP MEG /(_ e1 e2 e1M e2M x xe1 xe2) /eqP.
Qed.

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
