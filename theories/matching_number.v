From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries digraph mgraph sgraph set_tac connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition matchingb (G : sgraph) : pred {set {set G}} :=
  fun M => 
    (M \subset E(G))  &&
    [forall e1,
        [forall e2,
            (e1 \in M)
              ==> (e2 \in M)
              ==> [forall x : G, (x \in e1) ==> (x \in e2) ==> (e1 == e2)]]].
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

Definition induced_matchingb (G : sgraph) : pred {set {set G}} :=
  fun M => 
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
                    (e2 :&: e3 == set0) ]]].
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

Definition is_maximal_matching (G : sgraph) : pred {set {set G}} :=
  fun M =>
    (M \in matchingb G) &&
    [forall N : {set {set G}}, (M \proper N) ==> (N \notin matchingb G)].
Definition maximal_matchingb (G : sgraph) : {set {set {set G}}} :=
  [set M | is_maximal_matching M].

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
Lemma HHKO_2 G : nminmatch G <= nmatch G.
Proof.
case/boolP: (pred0b (matchingb G)).
- move/pred0P=> H.
  rewrite /nminmatch /maximal_matchingb /is_maximal_matching /nmatch /=.
  rewrite [in X in _ <= X]big_pred0; last by move=> i; rewrite /= /in_mem /= H.
  rewrite big_seq /= big_pred0 ? leqnn //.
  have-> : [set M in matchingb G | [forall N: {set {set G}},
                                                  (M \proper N) ==>
                                                  (N \notin matchingb G)]] = set0
    by apply eq_finset=> i; rewrite/in_mem/= H /=.
  move=> i.
  by rewrite enum_set0.
- case/pred0Pn => z mGz.
  rewrite /nminmatch /nmatch /=.
  have H: {subset maximal_matchingb G <= matchingb G} 
    by move=> M; rewrite inE /is_maximal_matching=> /andP [].
  have [Max [MmG]]: exists Max,
      Max \in matchingb G /\
              \big[minn/0]_(M <- enum (maximal_matchingb G)) #|M| <= #|Max|.
  + rewrite big_seq.
    apply big_ind.                                
    * exists z.
        by rewrite /in_mem /=; split; [apply mGz | apply leq0n].
    * move=> x y.
      case=> x0 [] ? xx0 [] ? [] ? ?.
      exists x0; split=> //; move: xx0; apply leq_trans; apply geq_minl.
    * move=> M; rewrite mem_enum inE=> /andP [] ? ?.
      by exists M; split; last by apply leqnn.
  + move/leq_trans; apply.
    by apply/leq_bigmax_cond.
Qed.
Lemma HHKO_3 G : nmatch G <= (nminmatch G).*2.
Proof.
move=> G.
set q := nminmatch G.
have: exists S, @is_maximal_matching G S /\ #| S | = q by admit.
case=> S [] H0 H1.
Abort.
