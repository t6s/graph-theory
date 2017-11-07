From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Checkpoints *)

Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types (x y z : G) (U : {set G}).

  Let avoids z x y (p : seq G) := upath x y p && (z \notin x::p).
  Definition avoidable z x y := [exists n : 'I_#|G|, exists p : n.-tuple G, avoids z x y p].

  Definition cp x y := locked [set z | ~~ avoidable z x y].

  Lemma cpPn {z x y} : reflect (exists2 p, upath x y p & z \notin x::p) (z \notin cp x y).
  Proof.
    rewrite /cp -lock inE negbK. apply: (iffP existsP) => [[n] /exists_inP|[p]].
    - case => p ? ?. by exists p.
    - case/andP => U S I.
      have size_p : size p < #|G|.
      { by rewrite -[(size p).+1]/(size (x::p)) -(card_uniqP U) max_card. }
      exists (Ordinal size_p). by apply/exists_inP; exists (in_tuple p).
  Qed.

  Lemma cpNI z x y p : spath x y p -> z \notin x::p -> z \notin cp x y.
  Proof.
    case/andP. case/shortenP => p' ? ? sub_p ? E. apply/cpPn. exists p' => //.
    apply: contraNN E. rewrite !inE. case: (_ == _) => //=. exact: sub_p.
  Qed.
  
  Definition checkpoint x y z := forall p, spath x y p -> z \in x :: p.

  Lemma cpP {x y z} : reflect (checkpoint x y z) (z \in cp x y).
  Proof.
    apply: introP.
    - move => H p pth_p. apply: contraTT H. exact: cpNI.
    - case/cpPn => p /upathW pth_p mem_p /(_ p pth_p). by rewrite (negbTE mem_p).
  Qed.

  (** wrapped versions of the checkpoint/path lemmas *)
  
  Lemma cpP' x y z : reflect (forall p : Path x y, z \in p) (z \in cp x y).
  Proof. 
    apply: (iffP cpP) => [H p|H p Hp]. 
    + rewrite in_collective nodesE. apply: H. exact: valP. 
    + move: (H (Sub p Hp)). by rewrite in_collective nodesE. 
  Qed.
  Arguments cpP' [x y z].

  Lemma cpPn' x y z : reflect (exists2 p : Path x y, irred p & z \notin p) (z \notin cp x y).
  Proof. 
    apply: (iffP cpPn) => [[p /andP [I Hp] N]|[p U N]]. 
    + exists (Sub p Hp); by rewrite /irred ?in_collective nodesE. 
    + rewrite /irred ?in_collective nodesE in U N.
      exists (val p) => //. apply/andP. split => //. exact: valP. 
  Qed.

  Lemma cpNI' x y (p : Path x y) z : z \notin p -> z \notin cp x y.
  Proof. by apply: contraNN => /cpP'. Qed.

  Hypothesis G_conn : forall x y:G, connect sedge x y.

  Lemma cp_sym x y : cp x y = cp y x.
  Proof.
    wlog suff S : x y / cp x y \subset cp y x. 
    { apply/eqP. by rewrite eqEsubset !S. }
    apply/subsetP => z /cpP H. apply/cpP => p p_pth. 
    rewrite (srev_nodes p_pth). apply: H. exact: spath_rev.
  Qed.

  Lemma mem_cpl x y : x \in cp x y.
  Proof. apply/cpP => p. by rewrite mem_head. Qed.

  Lemma subcp x y : [set x;y] \subset cp x y.
  Proof. by rewrite subUset !sub1set {2}cp_sym !mem_cpl. Qed.

  Lemma cpxx x : cp x x = [set x].
  Proof. 
    apply/setP => z; rewrite !inE. 
    apply/idP/idP; last by move/eqP ->; rewrite mem_cpl.
    move/cpP/(_ [::] (spathxx _)). by rewrite inE.
  Qed.

  Lemma cp_triangle z {x y} : cp x y \subset cp x z :|: cp z y.
  Proof.
    apply/subsetP => u /cpP' => A. apply: contraT. 
    rewrite !inE negb_or => /andP[/cpPn' [p1 _ up1]] /cpPn' [p2 _ up2]. 
    move: (A (pcat p1 p2)). by rewrite mem_pcat (negbTE up1) (negbTE up2).
  Qed.
  
  Lemma cpN_cat a x z y : a \notin cp x z -> a \notin cp z y -> a \notin cp x y.
  Proof. 
    move => /negbTE A /negbTE B. apply/negP. move/(subsetP (cp_triangle z)). 
    by rewrite !inE A B.
  Qed.

  Lemma cp_mid (z x y t : G) : t != z -> z \in cp x y ->
   exists (p1 : Path z x) (p2 : Path z y), t \notin p1 \/ t \notin p2.
  Proof. 
    move => tNz cp_z.
    case/uPathP : (G_conn x y) => p irr_p.
    move/cpP'/(_ p) : cp_z. case/(isplitP irr_p) => p1 p2 A B C.
    exists (prev p1). exists p2. rewrite mem_prev. apply/orP. 
    case E : (t \in p1) => //=. 
    by rewrite mem_path !inE (negbTE tNz) (disjointFr C E).
  Qed.

  (** ** CP Closure Operator *)

  Definition CP (U : {set G}) := \bigcup_(xy in setX U U) cp xy.1 xy.2.
  
  Unset Printing Implicit Defensive.
  
  Lemma CP_extensive (U : {set G}) : {subset U <= CP U}.
  Proof.
    move => x inU. apply/bigcupP; exists (x,x); by rewrite ?inE /= ?inU // cpxx inE.
  Qed.

  Lemma CP_mono (U U' : {set G}) : U \subset U' -> CP U \subset CP U'.
  Proof. 
    move/subsetP => A. apply/bigcupsP => [[x y] /setXP [/A Hx /A Hy] /=].
    apply/subsetP => z Hz. apply/bigcupP; exists (x,y) => //. exact/setXP.
  Qed.
  
  Lemma CP_closed U x y : 
    x \in CP U -> y \in CP U -> cp x y \subset CP U.
  Proof.
    case/bigcupP => [[x1 x2] /= /setXP [x1U x2U] x_cp]. 
    case/bigcupP => [[y1 y2] /= /setXP [y1U y2U] y_cp]. 
    apply/subsetP => t t_cp. 
    case (boolP (t == y)) => [/eqP-> //|T2].
    { apply/bigcupP. exists (y1,y2); by [exact/setXP|]. }
    case (boolP (t == x)) => [/eqP-> //|T1].
    { apply/bigcupP. exists (x1,x2); by [exact/setXP|]. }
    move: (cp_mid T1 x_cp) => [p1] [p2] H.
    wlog P1 : x1 x2 p1 p2 x1U x2U x_cp H / t \notin p1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ p1 p2) => //; tauto.
      - rewrite cp_sym in x_cp. apply : (W _ _ p2 p1) => //; tauto. }
    move: (cp_mid T2 y_cp) => [q1] [q2] H.
    wlog P2 : y1 y2 q1 q2 y1U y2U y_cp H / t \notin q1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ q1 q2) => //; tauto.
      - rewrite cp_sym in y_cp. apply : (W _ _ q2 q1) => //; tauto. }
    apply/bigcupP; exists (x1,y1) => /= ; first exact/setXP. 
    apply: contraTT t_cp => /cpPn' [s _ Hs]. 
    suff: t \notin (pcat p1 (pcat s (prev q1))) by apply: cpNI'.
    by rewrite !mem_pcat !mem_prev (negbTE P1) (negbTE P2) (negbTE Hs).
  Qed.

  (** ** Link Graph *)

  Definition link_rel := [rel x y | (x != y) && (cp x y \subset [set x; y])].

  Lemma link_sym : symmetric link_rel.
  Proof. move => x y. by rewrite /= eq_sym cp_sym set2C. Qed.

  Lemma link_irrefl : irreflexive link_rel.
  Proof. move => x /=. by rewrite eqxx. Qed.

  Definition link_graph := SGraph link_sym link_irrefl.

  Lemma link_avoid (x y z : G) : 
    z \notin [set x; y] -> link_rel x y -> exists2 p, spath x y p & z \notin (x::p).
  Abort. (* not acutally used *)

  Lemma link_seq_cp (y x : G) p :
    @spath link_graph x y p -> cp x y \subset x :: p.
  Proof.
    elim: p x => [|z p IH] x /=.
    - move/spath_nil->. rewrite cpxx. apply/subsetP => z. by rewrite !inE.
    - rewrite spath_cons => /andP [/= /andP [A B] /IH C]. 
      apply: subset_trans (cp_triangle z) _.
      rewrite subset_seqR. apply/subUsetP; split. 
      + apply: subset_trans B _. by rewrite !set_cons setUA subsetUl.
      + apply: subset_trans C _. by rewrite set_cons subset_seqL subsetUr.
  Qed.

  (* Lemma 10 *)
  Lemma link_cycle (p : seq link_graph) : ucycle sedge p -> clique [set x in p].
  Proof. 
    move => cycle_p x y. rewrite !inE /= => xp yp xy. rewrite xy /=.
    case/andP : cycle_p => C1 C2. 
    case: (rot_to_arc C2 xp yp xy) => i p1 p2 _ _ I. 
    have {C1} C1 : cycle sedge (x :: p1 ++ y :: p2) by rewrite -I rot_cycle. 
    have {C2} C2 : uniq (x :: p1 ++ y :: p2) by rewrite -I rot_uniq.
    rewrite /cycle -cat_rcons rcons_cat cat_path last_rcons in C1. 
    case/andP : C1 => /rcons_spath P1 /rcons_spath /spath_rev P2. 
    rewrite srev_rcons in P2. 
    move/link_seq_cp in P1. move/link_seq_cp in P2.
    have D: [disjoint p1 & p2].
    { move: C2 => /= /andP [_]. rewrite cat_uniq -disjoint_has disjoint_cons disjoint_sym.
      by case/and3P => _ /andP [_ ?] _. }
    apply: contraTT D. case/subsetPn => z. rewrite !inE negb_or => A /andP [B C].
    move: (subsetP P1 _ A) (subsetP P2 _ A). 
    rewrite !(inE,mem_rcons,negbTE B,negbTE C,mem_rev) /=. 
    exact: disjointNI.
  Qed.

  (** ** Intervals and bags/petals *)

  Definition sinterval x y := 
    [set z in ~: [set x; y] | connect (restrict (predC1 y) (@sedge G)) z x && 
                              connect (restrict (predC1 x) (@sedge G)) z y ].

  Definition interval x y := [set x;y] :|: sinterval x y.

  Definition petal (U : {set G}) x :=
    locked [set z | [forall y in CP U, x \in cp z y]].

  Lemma petal_id (U : {set G}) x : x \in petal U x.
  Proof. rewrite /petal -lock inE. apply/forall_inP => y _. exact: mem_cpl. Qed.

  Lemma petalP (U : {set G}) x z : 
    reflect (forall y, y \in CP U -> x \in cp z y) (z \in petal U x).
  Proof. rewrite /petal -lock inE. exact: (iffP forall_inP). Qed.

  Lemma petalPn (U : {set G}) x z : 
    reflect (exists2 y, y \in CP U & x \notin cp z y) (z \notin petal U x).
  Proof.
    rewrite /petal -lock inE negb_forall. apply: (iffP existsP) => [[y]|[y] A B].
    - rewrite negb_imply => /andP[? ?]. by exists y.
    - exists y. by rewrite A.
  Qed.

  (* Lemma 16 *)
  Lemma CP_base U x y : x \in CP U -> y \in CP U ->
    exists x' y':G, [/\ x' \in U, y' \in U & [set x;y] \subset cp x' y'].
  Proof.
    move => U1 U2. case/bigcupP : U1 => [[x1 x2]]. case/bigcupP : U2 => [[y1 y2]] /=.
    rewrite !inE /= => /andP[Uy1 Uy2] cp_y /andP[Ux1 Ux2] cp_x.
    case: (boolP (x \in cp y1 y2)) => [C|Wx]; first by exists y1; exists y2; rewrite subUset !sub1set C.
    case: (boolP (y \in cp x1 x2)) => [C|Wy]; first by exists x1; exists x2; rewrite subUset !sub1set C.
    gen have H,A: x x1 x2 y1 y2 {Ux1 Ux2 Uy1 Uy2 Wy cp_y} Wx cp_x /
      (x \in cp x1 y1) || (x \in cp x2 y2).
    { case/cpPn' : Wx => p irr_p av_x. 
      apply: contraTT cp_x. rewrite negb_or => /andP[/cpPn' [s s1 s2] /cpPn' [t t1 t2]].
      apply (cpNI' (p := pcat s (pcat p (prev t)))). 
      by rewrite !mem_pcat !mem_prev (negbTE av_x) (negbTE s2) (negbTE t2). }
    have {H} B : (y \in cp x1 y1) || (y \in cp x2 y2).
    { rewrite -(cp_sym y1 x1) -(cp_sym y2 x2). exact: H. }
    wlog {A} /andP [Hx Hy] : x1 x2 y1 y2 A B cp_x cp_y Ux1 Ux2 Uy1 Uy2 Wx Wy
        / (x \in cp x1 y1) && (y \notin cp x1 y1).
    { case: (boolP (y \in cp x1 y1)) A B => A; case: (boolP (x \in cp x1 y1)) => /= B C D W. 
      - by exists x1; exists y1; rewrite subUset !sub1set B. 
      - (* TOTHINK: why the second case anlysis in this case? *)
        case: (boolP (y \in cp x2 y2)) => E. 
        + exists x2; exists y2; by rewrite subUset !sub1set C.
        + move: (W x2 x1 y2 y1). rewrite (cp_sym x2 x1) (cp_sym y2 y1) A C /= orbT. exact.
      - apply: (W x1 x2 y1 y2) => //. by rewrite B. by rewrite D.
      - exists x2; exists y2; by rewrite subUset !sub1set C D. }
    rewrite (negbTE Hy) /= in B.
    case: (boolP (x \in cp x2 y2)) => [C|Wx']; first by exists x2; exists y2; rewrite subUset !sub1set C.
    exists x1. exists y2. rewrite subUset !sub1set. split => //. apply/andP; split.
    - apply: contraTT cp_x => C. apply: cpN_cat C _. by rewrite cp_sym.
    - apply: contraTT cp_y. apply: cpN_cat. by rewrite cp_sym.
  Qed.

  (* TOTHINK: Is it really worthwile to have this as a graph in addition to the set [CP U]? *)
  Definition CP_ U := @induced link_graph (CP U).

  Lemma CP_SubK (U : {set G}) x (Px : x \in CP U) :
    x = val (Sub x Px : CP_ U). 
  Proof. by rewrite SubK. Qed.

  Lemma index_uniq_inj (T:eqType) (s : seq T) : 
    {in s, injective (index^~ s)}. 
  Proof. 
    move => x in_s y E. 
    have A : y \in s by rewrite -index_mem -E index_mem.
    by rewrite -(nth_index x in_s) E nth_index.
  Qed.

  Lemma CP_base_ U (x y : CP_ U) : 
    exists x' y':G, [/\ x' \in U, y' \in U & [set val x;val y] \subset cp x' y'].
  Proof. exact: CP_base  (svalP x) (svalP y). Qed.


  Lemma CP_triangle_avoid x' y' (x y z: link_graph) : 
    x -- y -> y -- z -> z -- x -> x \in cp x' y' -> y \in cp x' y' -> z \notin cp x' y'.
  Proof.
    move => xy yz zx Cx Cy. apply/negP => Cz.
    case/uPathP : (G_conn x' y') => p irr_p.
    move: (cpP' Cx p) (cpP' Cy p) (cpP' Cz p) => x_in_p y_in_p z_in_p.
    pose I := idx p. 
    have D (x1 x2 : link_graph) : x1 -- x2 -> x1 \in nodes p -> I x1 <> I x2.
    { move => H in_p. move/idx_inj. case/(_ _ )/Wrap => //. 
      move => ?. subst. by rewrite sgP in H. }
    wlog /andP [x_lt_y y_lt_z] : x y z xy yz zx x_in_p y_in_p z_in_p Cy {Cx Cz D}
      / I x < I y < I z => [W|].
    { wlog x_lt_y : x y xy yz zx Cx Cy x_in_p y_in_p z_in_p / I x < I y => [W2|].
      { case: (ltngtP (I x) (I y)); [exact: W2|apply:W2; by rewrite // sg_sym |exact: D]. }
      case: (ltngtP (I y) (I z)) => [Hyz|Hyz|]; last exact: D. 
      - exact: (W x y z).
      - case: (ltngtP (I z) (I x)) => [Hzx|Hzx|]; last exact: D. 
        + exact: (W z x y).
        + apply: (W x z y); by rewrite // sg_sym. }
    suff: y \notin cp x' y' by rewrite Cy.
    case/(isplitP (G := G) irr_p) def_p : {1}p / (x_in_p) => [p1 p2 irr_p1 irr_p2 D]. subst.
    case: (idx_nLR irr_p y_in_p) => // Y1 Y2.
    (case: (idx_nLR irr_p z_in_p); first by apply: ltn_trans y_lt_z) => Z1 Z2.
    case/(isplitP (G:=G) irr_p2) def_p1 : {1}p2 / (tailW Z2) => [p21 p22 irr21 irr22 D2]. subst.
    have Hy' : y \notin tail p22.
    { rewrite (idxR irr_p2) ?tailW //. rewrite -(idx_catL irr_p Z2 Y2). by rewrite -leqNgt ltnW. }
    have/cpPn' [q q1 q2] : y \notin cp x z. 
    { case/andP : zx => _ sub. apply/negP. rewrite cp_sym. move/(subsetP sub). 
      rewrite !inE. by case/orP => /eqP ?;subst; rewrite sg_irrefl in xy yz. }
    apply: (cpNI' (p := pcat p1 (pcat q p22))). 
    by rewrite mem_pcat mem_pcatT (negbTE Hy') (negbTE Y1) (negbTE q2).
  Qed.

  
  Lemma CP_triangle U (x y z: CP_ U) : 
    x -- y -> y -- z -> z -- x -> 
    exists x' y' z':G, 
      [/\ x' \in U, y' \in U & z' \in U] /\
      [/\ [set val x;val y] \subset cp x' y',
         [set val y;val z] \subset cp y' z'&
         [set val z;val x] \subset cp z' x'].
  Proof.
    move => xy yz zx.
    move: (CP_base_ x y) => [x'] [y'] [Ux Uy]. 
    rewrite subUset !sub1set => /andP[cp_x cp_y].
    have ncp_z : val z \notin cp x' y' by apply: CP_triangle_avoid cp_x cp_y. 
    case/cpPn' : ncp_z => p irr_p av_z. 
    have x_in_p : val x \in p by apply/cpP'.
    have y_in_p : val y \in p by apply/cpP'.
  
    wlog x_before_y : x' y' Ux Uy cp_x cp_y p irr_p av_z x_in_p y_in_p / 
      idx p (val x) < idx p (val y). 
    { move => W. case: (ltngtP (idx p (val x)) (idx p (val y))) => H.
      - exact: (W x' y' _ _ _ _ p). 
      - apply: (W y' x' _ _ _ _ (prev p)); rewrite 1?cp_sym //. 
        + exact: prev_irred.
        + by rewrite mem_prev.
        + rewrite /=. (* FIXME: why is this needed *) by rewrite mem_prev.
        + by rewrite /= mem_prev.
        + exact: idx_swap H. 
      - move/idx_inj : H. move/(_ x_in_p)/val_inj => ?. subst y. by rewrite sgP in xy. }
    
    move: (CP_base_ x z) => [x''] [z'] [Ux' Uz]. 
    rewrite subUset !sub1set => /andP[cp_x' cp_z].
    have ncp_z : val y \notin cp x'' z' by apply: CP_triangle_avoid cp_x' cp_z; by rewrite sgP.
    case/cpPn' : ncp_z => q irr_q av_y.
    have x_in_q : val x \in q by apply/cpP'.
    have z_in_q : val z \in q by apply/cpP'.

    wlog x_before_z : x'' z' Ux' Uz cp_x' cp_z q irr_q av_y x_in_q z_in_q / 
      idx q (val x) < idx q (val z).
    { move => W. case: (ltngtP (idx q (val x)) (idx q (val z))) => H.
      - exact: (W x'' z' _ _ _ _ q).
      - apply: (W z' x'' _ _ _ _ (prev q)); try rewrite 1?cp_sym /= ?mem_prev //. 
        + exact: prev_irred.
        + exact: idx_swap H. 
      - move/idx_inj : H. move/(_ x_in_q)/val_inj => ?. subst z. by rewrite sgP in zx. }

    case: (three_way_split irr_p x_in_p y_in_p x_before_y) => p1 [p2] [p3] [? ? ?]. subst p.
    rewrite !mem_pcat 2!negb_or in av_z. case/and3P : av_z => p1_z p2_z p3_z. 
    case: (three_way_split irr_q x_in_q z_in_q x_before_z) => q1 [q2] [q3] [? ? ?]. subst q.
    rewrite !mem_pcat 2!negb_or in av_y. case/and3P : av_y => q1_y q2_y q3_y.

    (* have _ : (val x) \in cp x' (val y).  *)
    clear x_before_y y_in_p x_in_p x_before_z z_in_q x_in_q irr_p irr_q.

    exists x'. exists y'. exists z'. split; split; rewrite // subUset !sub1set; apply/andP;split.
    - done.
    - done.
    - apply: contraTT cp_y. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat p1 (pcat q2 (pcat q3 (prev r))))).
      rewrite /= !mem_pcat !mem_prev 3!negb_or. exact/and4P.
    - apply: contraTT cp_z. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat q1 (pcat p2 (pcat p3 r)))).
      rewrite /= !mem_pcat 3!negb_or. exact/and4P.
    - rewrite cp_sym. 
      apply: contraTT cp_z. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat q1 (pcat (prev p1) r))).
      rewrite /= !mem_pcat mem_prev 2!negb_or. exact/and3P.
    - rewrite cp_sym. 
      have: val x \notin cp (val y) (val z).
      { apply/negP. move: yz => /= /andP [_ B] /(subsetP B).
        rewrite !inE => /orP[]/eqP/val_inj=>?; subst x. 
        by rewrite sgP in xy. by rewrite sgP in zx. }
      case/cpPn' => s _ Hs. 
      apply: contraTT cp_x. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat r (pcat (prev q3) (pcat (prev s) p3)))).
      rewrite /= !mem_pcat !mem_prev 3!negb_or. exact/and4P.
  Qed.
  
  Lemma cp_neighbours (x y : G) z : 
    x != y -> (forall x', x -- x' -> z \in cp x' y) -> z \in cp x y.
  Proof.
    move => A B. apply/cpP => p. case: p => [|x' p].
    - move/spath_nil/eqP => ?. by contrab.
    - rewrite spath_cons in_cons => /andP [C D]. apply/orP;right. 
      apply/(cpP (y := y)) => //. exact: B. 
  Qed.

  Lemma CP_clique U : @clique link_graph U -> CP U = U.
  Proof.
    move => clique_U. apply/setP => x. apply/bigcupP/idP. 
    - case => [[x1 x2]]. rewrite !inE /= => /andP [U1 U2]. 
      move: (clique_U x1 x2 U1 U2). case: (boolP (x1 == x2)) => A B.
      + rewrite (eqP A) cpxx inE. by move/eqP->.
      + case/andP: (B erefl) => _ /subsetP => S /S. by case/setUP => /set1P->.
    - move => inU. by exists (x,x); rewrite ?inE /= ?inU // cpxx inE. 
  Qed.

  (** ** Neighouring Checkpoints *)

  Definition ncp (U : {set G}) (p : G) : {set G} := 
    locked [set x in CP U | connect (restrict [pred z | (z \in CP U) ==> (z == x)] sedge) p x].

  Arguments Path : clear implicits.

  (* TOTHINK: Do we also want to require [irred q] *)
  Lemma ncpP (U : {set G}) (p : G) x : 
    reflect (x \in CP U /\ exists q : Path G p x, forall y, y \in CP U -> y \in q -> y = x) 
            (x \in ncp U p).
  Proof.
    rewrite /ncp -lock inE. apply: (iffP andP) => [[cp_x A]|[cp_x [q Hq]]]; split => //.
    - case: (boolP (p == x)) => [/eqP ?|px]. 
      + subst p. exists (idp x) => y _ . by rewrite mem_idp => /eqP.
      + case/(uPathRP px) : A => q irr_q /subsetP sub_q. 
        exists q => y CPy /sub_q. by rewrite !inE CPy => /eqP.
    - apply: (connectRI (p := q)) => y y_in_q.
      rewrite inE. apply/implyP => A. by rewrite [y]Hq.
  Qed.

  Lemma ncp_petal (U : {set G}) (p : G) x :
    x \in CP U -> (p \in petal U x) = (ncp U p == [set x]).
  Proof.
    move => Ux. apply/petalP/eq_set1P.
    - move => A. split.
      + apply/ncpP; split => //.
        case/uPathP : (G_conn p x) => q irr_q. 
        case: (boolP [exists y in CP U, y \in [predD1 q & x]]).
        * case/exists_inP => y /= B. rewrite inE eq_sym => /= /andP [C D]. 
          case:notF. apply: contraTT (A _ B) => _. apply/cpPn'.
          case/(isplitP irr_q) def_q : q / D => [q1 q2 irr_q1 irr_q2 D12].
          exists q1 => //. rewrite (disjointFl D12) //. 
          suff: x \in q2. by rewrite mem_path inE (negbTE C). 
          by rewrite nodes_end.
        * rewrite negb_exists_in => /forall_inP B.
          exists q => y /B => C D. apply/eqP. apply: contraNT C => C. 
          by rewrite inE C.
      + move => y /ncpP [Uy [q Hq]]. 
        have Hx : x \in q. { apply/cpP'. exact: A. }
        apply: esym. exact: Hq. 
    - case => A B y Hy. apply/cpP' => q.
      have qy : y \in q by rewrite nodes_end.
      move: (split_at_first Hy qy) => [x'] [q1] [q2] [def_q cp_x' Hq1]. 
      suff ?: x' = x. { subst x'. by rewrite def_q mem_pcat nodes_end. }
      apply: B. apply/ncpP. split => //. exists q1 => z' H1 H2. exact: Hq1.
  Qed.
      
  Lemma petal_disj (U : {set G}) x y :
    x \in CP U -> y \in CP U -> x != y -> [disjoint petal U x & petal U y].
  Proof.
    move => Ux Uy xy. apply/pred0P => p /=. apply:contraNF xy => /andP[].
    rewrite [x](CP_SubK Ux) [y](CP_SubK Uy) !ncp_petal //.
    by move => /eqP-> /eqP/set1_inj->.
  Qed.

  (** the root of a petal is a checkpoint separating the petal from
  the rest of the graph *)
  Lemma petal_exit (U : {set G}) x u v : 
    x \in CP U -> u \in petal U x -> v \notin petal U x -> x \in cp u v.
  Proof.
    move => cp_x. rewrite [v \in _]ncp_petal // => N1 N2.
    have [y [Y1 Y2 Y3]] : exists y, [/\ y \in CP U, x != y & y \in ncp U v].
    { (* [ncp U v] cannot be empy and is different from [set x] *) admit. } 
    move/petalP : N1 => /(_ _ Y1). 
    apply: contraTT => /cpPn' [p] irr_p av_x. 
    case/ncpP : Y3 => _ [q] /(_ _ cp_x) A. 
    have {A} Hq : x \notin q. { apply/negP => /A ?. subst. by rewrite eqxx in Y2. }
    apply: (cpNI' (p := pcat p q)). by rewrite mem_pcat negb_or av_x.
  Admitted.

  Lemma petal_exit' (U : {set G}) x u v : 
    x \in CP U -> u \in petal U x -> v \in x |: ~: petal U x -> x \in cp u v.
  Proof. 
    move => cp_x Hu. case/setU1P => [->|]; first by rewrite cp_sym mem_cpl.
    rewrite inE. exact: petal_exit Hu.
  Qed.

  Lemma petal_extension (U : {set G}) x y : 
    x \in CP U -> y \notin petal U x -> petal U x = petal (y |: U) x.
  Proof.
    move => CPx Hy. apply/setP => u. apply/petalP/petalP.
    - move => A z. 
      have cp_x : x \in cp u y. { apply: petal_exit Hy => //. exact/petalP. }
      case/bigcupP => [[v0 v1]] /setXP /= []. 
      do 2 (case/setU1P => [->|?]). 
      + by rewrite cpxx inE => /eqP->. 
      + move => Hz. apply/negPn/negP => B. 
        (* take irredundant [p : Path y v1] and split at z *)
        case/uPathP : (G_conn y v1) => p irr_p. 
        have z_in_p : z \in p by apply/cpP'.
        case/(isplitP irr_p) def_p : {1}p / z_in_p => [p1 p2 irr_p1 irr_p2 D].
        (* have x in the z-v1 part (follows with A) *)
        (* hence x not in the y-z part *)
        (* contradicts cp_x *)
        admit.
      + (* symmetric *) admit.
      + move => Hz. apply: A. apply/bigcupP; exists (v0,v1) => //. exact/setXP.
    - move => A z Hz. apply: A. move: z Hz. apply/subsetP. 
      apply: CP_mono. exact: subsetUr.
  Admitted.  
  
  Lemma ncp_CP (U : {set G}) (u : G) :
    u \in CP U -> ncp U u = [set u].
  Proof. 
    move => Hu.
    apply/setP => x. rewrite [_ \in [set _]]inE. apply/ncpP/eqP.
    - move => [Hx [q Hq]]. apply: esym. apply: Hq => //. exact: nodes_start.
    - move => ->. split => //. exists (idp u) => y _. by  rewrite mem_idp => /eqP.
  Qed.
  
  Lemma ncp0 (U : {set G}) x p : 
    x \in U -> ncp U p == set0 = false.
  Proof. 
    move => Ux'. 
    case/uPathP : (G_conn p x) => q irr_q. 
    have Ux: x \in CP U by apply: CP_extensive.
    case: (split_at_first Ux (nodes_end q)) => y [q1] [q2] [def_q CPy Hy].
    suff: y \in ncp U p. { apply: contraTF => /eqP->. by rewrite inE. }
    apply/ncpP. split => //. by exists q1. 
  Qed.
  Arguments ncp0 [U] x p.
  
  (** NOTE: This looks fairly specific, but it also has a fairly
  straightforward proof *)
  Lemma interval_petal_disj U (x y : G) :
    y \in CP U -> [disjoint petal U x & sinterval x y].
  Proof.
    move => Uy. rewrite disjoint_sym disjoints_subset. apply/subsetP => z.
    rewrite 3!inE negb_or !in_set1 => /and3P [/andP [A1 A2] B C]. 
    rewrite inE. apply:contraTN C => /petalP/(_ _ Uy). 
    apply: contraTN. case/uPathRP => // p _ /subsetP sub_p. 
    apply: (cpNI' (p := p)). apply/negP => /sub_p. by rewrite inE eqxx.
  Qed.
  
  Lemma ncp_interval U (x y p : G) : 
    x != y -> [set x;y] \subset ncp U p  -> p \in sinterval x y.
  Proof.
    rewrite subUset !sub1set => xy /andP[Nx Ny]. 
    rewrite !inE negb_or. 
    gen have A,Ax : x y xy Nx Ny / p != x.
    { have Ux : x \in CP U. by case/ncpP : Nx.
      apply: contraNN xy => /eqP => ?; subst p. apply/eqP.
      case/ncpP : Ny => Uy [q] /(_ _ Ux). rewrite nodes_start. 
      by apply. }
    have Ay: p != y. apply: (A y x) => //. by rewrite eq_sym.
    rewrite Ax Ay /=. 
    gen have S,_: x y Nx Ny xy {A Ax Ay} / connect (restrict (predC1 y) sedge) p x.
    { case/ncpP : Nx => Ux [q Hq]. apply: (connectRI (p := q)).
      move => z in_q. apply: contraNT xy. rewrite negbK => /eqP ?; subst z.
      rewrite [y]Hq //. by case/ncpP : Ny. }
    apply/andP;split; apply: S => //. by rewrite eq_sym.
  Qed.


  Lemma CP_petals U x y : x != y -> x \in CP U -> y \in CP U -> 
    exists x' y', [/\ x' \in U, y' \in U, x' \in petal [set x; y] x & y' \in petal [set x;y] y].
  Admitted. (* follows with [three_way_split] and [CP_base] *)

  (* TOTHINK: The following lemma is a strengthening of [CP_triangle]
  and could be obtained by extending the proof of that lemma. Possible
  alternative: strenthen [CP_base] and replace rework the proof of
  [CP_triangle] *)
  Lemma CP_triangle_petals U (x y z : CP_ U) : 
    x -- y -> y -- z -> z -- x -> 
    let U3 : {set G} := [set val x; val y; val z] in
    exists x' y' z' : G, 
      [/\ x' \in U, y' \in U & z' \in U] /\ 
      [/\ x' \in petal U3 (val x), y' \in petal U3 (val y) & z' \in petal U3 (val z)].
  Proof.
    move => xy yz zx U3.
  Admitted.
 
End CheckPoints.

Notation "x ⋄ y" := (@sedge (link_graph _) x y) (at level 30).
Notation "x ⋄ y" := (@sedge (CP_ _) x y) (at level 30).

(** ** Checkpoint Order *)

Section CheckpointOrder.

  Variables (G : sgraph) (i o : G).
  Hypothesis conn_io : connect sedge i o.
  Implicit Types x y : G.

  (* TODO: This uses upath in a nontrivial way. *)

  Lemma the_upath_proof : exists p, upath i o p.
  Proof. case/upathP : conn_io => p Hp. by exists p. Qed.
                                                                
  Definition the_upath := xchoose (the_upath_proof).

  Lemma the_upathP x y : upath i o (the_upath).
  Proof. exact: xchooseP. Qed.

  Definition cpo x y := let p := the_upath in 
                        index x (i::p) <= index y (i::p).

  Lemma cpo_trans : transitive cpo.
  Proof. move => ? ? ?. exact: leq_trans. Qed.

  Lemma cpo_total : total cpo.
  Proof. move => ? ?. exact: leq_total. Qed.

  Lemma cpo_antisym : {in cp i o&,antisymmetric cpo}.
  Proof. 
    move => x y Cx Cy. rewrite /cpo -eqn_leq. 
    have Hx: x \in i :: the_upath. 
    { move/cpP : Cx => /(_ (the_upath)). 
      apply. apply upathW. exact: the_upathP. }
    have Hy: y \in i :: the_upath.
    { move/cpP : Cy => /(_ (the_upath)). 
      apply. apply upathW. exact: the_upathP. }
    by rewrite -{2}[x](nth_index i Hx) -{2}[y](nth_index i Hy) => /eqP->.
  Qed.

  (** All paths visist all checkpoints in the same order as the canonical upath *)
  (* TOTHINK: Is this really the formulation that is needed in the proofs? *)
  Lemma cpo_order (x y : G) p : x \in cp i o -> y \in cp i o -> upath i o p -> 
    cpo x y = (index x (i::p) <= index y (i::p)).
    move => cp_x cp_y pth_p. rewrite /cpo. 
  Admitted.

End CheckpointOrder.

Arguments ncp0 [G] G_conn [U] x p.

Lemma CP_treeI (G : sgraph) (G_conn : forall x y : G, connect sedge x y) (U : {set G}) :
  (~ exists x y z : CP_ U, [/\ x -- y, y -- z & z -- x]) -> is_tree (CP_ U).
Proof.
(* - is_tree is decidable, so we can prove the contraposition
   - argue that CP_ U is connected whenever G is
   - hence there exist nodes x and y and two distinct irredundant xy-paths p and q
   - let z be the first vertex with different sucessors z1 in p and z2 in q
   - the z1-y-z2 path avoids z, so removing cycles on that path yields an 
     irred cycle containing {z, z1, z2}
   - this cycle is a clique by [link_cycle] *)
Admitted.