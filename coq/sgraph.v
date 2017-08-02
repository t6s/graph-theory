From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

Lemma disjointE (T : finType) (A B : pred T) x : 
  [disjoint A & B] -> x \in A -> x \in B -> False.
Proof. by rewrite disjoint_subset => /subsetP H /H /negP. Qed.

(** * Simple Graphs *)

Record sgraph := SGraph { svertex :> finType ; 
                         sedge: rel svertex; 
                         sg_sym: symmetric sedge;
                         sg_irrefl: irreflexive sedge}.

Record sgraph2 := SGraph2 { sgraph_of :> sgraph; 
                            s_in : sgraph_of; 
                            s_out : sgraph_of}.

Arguments s_in [s].
Arguments s_out [s].
Notation "x -- y" := (sedge x y) (at level 30).
Definition sgP := (sg_sym,sg_irrefl).
Prenex Implicits sedge.

(** ** Homomorphisms *)

Definition hom_s (G1 G2 : sgraph) (h : G1 -> G2) := 
  forall x y, x -- y -> (h x = h y) \/ (h x -- h y).

Definition hom_s2 (G1 G2 : sgraph2) (h : G1 -> G2) :=
  [/\ hom_s h , h s_in = s_in & h s_out = s_out].

Definition subgraph (S G : sgraph) := 
  exists2 h : S -> G, injective h & hom_s h.

Section InducedSubgraph.
  Variables (G : sgraph) (S : {set G}).

  Definition induced_type := sig [eta mem S].

  Definition induced_rel := [rel x y : induced_type | val x -- val y].

  Lemma induced_sym : symmetric induced_rel.  
  Proof. move => x y /=. by rewrite sgP. Qed.
         
  Lemma induced_irrefl : irreflexive induced_rel.  
  Proof. move => x /=. by rewrite sgP. Qed.

  Definition induced := SGraph induced_sym induced_irrefl.

  Lemma induced_sub : subgraph induced G.
  Proof. exists val => //. exact: val_inj. by right. Qed.

End InducedSubgraph.

Lemma irreflexive_restrict (T : Type) (e : rel T) (A : pred T) : 
  irreflexive e -> irreflexive (restrict A e).
Proof. move => irr_e x /=. by rewrite irr_e. Qed.

Definition srestrict (G : sgraph) (A : pred G) :=
  Eval hnf in SGraph (symmetric_restrict A (@sg_sym G))
                     (irreflexive_restrict A (@sg_irrefl G)).


(** ** Paths through simple graphs *)


Section SimplePaths.
Variable (G : sgraph).

Implicit Types (x y z : G).

Definition srev x p := rev (belast x p).

Lemma last_rev_belast x y p : 
  last x p = y -> last y (srev x p) = x.
Proof. case: p => //= a p _. by rewrite /srev rev_cons last_rcons. Qed.

Lemma path_srev x p : 
  path sedge x p = path sedge (last x p) (srev x p).
Proof. 
  rewrite rev_path [in RHS](eq_path (e' := sedge)) //. 
  move => {x} x y. exact: sg_sym. 
Qed.

(** Lemmas on splitting and concatenating paths between nodes *)
Definition spath (x y : G) p := path sedge x p && (last x p == y).

Lemma spathW y x p : spath x y p -> path sedge x p.
Proof. by case/andP. Qed.

Lemma spath_last y x p : spath x y p -> last x p = y.
Proof. by case/andP => _ /eqP->. Qed.

Lemma rcons_spath x y p : path sedge x (rcons p y) -> spath x y (rcons p y).
Proof. move => A. apply/andP. by rewrite last_rcons eqxx. Qed.

Lemma spathxx x : spath x x [::].
Proof. exact: eqxx. Qed.

Lemma spath_nil x y : spath x y [::] -> x = y.
Proof. by case/andP => _ /eqP. Qed.

Lemma spath_rcons x y z p: spath x y (rcons p z) -> y = z.
Proof. case/andP => _ /eqP <-. exact: last_rcons. Qed.

Lemma spath_cat x y p1 p2 : 
  spath x y (p1++p2) = (spath x (last x p1) p1) && (spath (last x p1) y p2).
Proof. by rewrite {1}/spath cat_path last_cat /spath eqxx andbT /= -andbA. Qed.

Lemma spath_cons x y z p : 
  spath x y (z :: p) = x -- z && spath z y p.
Proof. by rewrite -cat1s spath_cat {1}/spath /= eqxx !andbT. Qed.

Lemma spath_concat x y z p q : 
  spath x y p -> spath y z q -> spath x z (p++q).
Proof. 
  move => /andP[A B] /andP [C D]. 
  rewrite spath_cat (eqP B) /spath -andbA. exact/and4P.
Qed.

Lemma spath_end x y p : spath x y p -> y \in x :: p.
Proof. move => A. by rewrite -(spath_last A) mem_last. Qed.

Lemma spath_endD x y p : spath x y p -> x != y -> y \in p.
Proof. move => A B. move: (spath_end A). by rewrite !inE eq_sym (negbTE B). Qed.

Lemma srev_rcons x z p : srev x (rcons p z) = rcons (rev p) x.
Proof. by rewrite /srev belast_rcons rev_cons. Qed.

(** Note that the converse of the following does not hold since [srev
x p] forgets the last element of [p]. Consequently, doulbe reversal
only cancels if the right nodes are added back. *)
Lemma spath_rev x y p : spath x y p -> spath y x (srev x p).
Proof.
  rewrite /spath. elim/last_ind: p => /= [|p z _]; first by rewrite eq_sym.
  rewrite !srev_rcons !last_rcons eqxx andbT path_srev last_rcons srev_rcons. 
  by move/andP => [A /eqP <-].
Qed.

Lemma srevK x y p : last x p = y -> srev y (srev x p) = p.
Proof. 
  elim/last_ind: p => // p z _. 
  by rewrite last_rcons !srev_rcons revK => ->.
Qed.

Lemma srev_nodes x y p : spath x y p -> x :: p =i y :: srev x p.
Proof. 
  elim/last_ind: p => //; first by move/spath_nil ->.
  move => p z _ H a. rewrite srev_rcons !(inE,mem_rcons,mem_rev). 
  rewrite (spath_rcons H). by case: (a == x).
Qed.

CoInductive spath_split z x y : seq G -> Prop := 
  SSplit p1 p2 : spath x z p1 -> spath z y p2 -> spath_split z x y (p1 ++ p2).

Lemma ssplitP z x y p : z \in x :: p -> spath x y p -> spath_split z x y p.
Proof. 
  case/splitPl => p1 p2 /eqP H1 /andP [H2 H3]. 
  rewrite cat_path last_cat in H2 H3. case/andP : H2 => H2 H2'.
  constructor; last rewrite -(eqP H1); exact/andP. 
Qed.


End SimplePaths.
Arguments spath_last [G].

(** ** Irredundant Paths *)

Section Upath.
Variable (G : sgraph).
Implicit Types (x y z : G).

Definition upath x y p := uniq (x::p) && spath x y p.

Lemma upathW x y p : upath x y p -> spath x y p.
Proof. by case/andP. Qed.

Lemma upath_uniq x y p : upath x y p -> uniq (x::p).
Proof. by case/andP. Qed.

Lemma rev_upath x y p : upath x y p -> upath y x (srev x p).
Proof. 
  case/andP => A B. apply/andP; split; last exact: spath_rev.
  apply: leq_size_uniq A _ _. 
  - move => z. by rewrite -srev_nodes.
  - by rewrite /= size_rev size_belast.
Qed.

Lemma upath_sym x y : unique (upath x y) -> unique (upath y x).
Proof. 
  move => U p q Hp Hq. 
  suff S: last y p = last y q. 
  { apply: rev_belast S _. apply: U; exact: rev_upath. }
  rewrite !(spath_last x) //; exact: upathW.
Qed.

Lemma upath_cons x y z p : 
  upath x y (z::p) = [&& x -- z, x \notin (z::p) & upath z y p].
Proof. 
  rewrite /upath spath_cons [z::p]lock /= -lock.
  case: (x -- z) => //. by case (uniq _).
Qed.

Lemma upath_consE x y z p : upath x y (z :: p) -> [/\ x -- z, x \notin z :: p & upath z y p].
Proof. rewrite upath_cons. by move/and3P. Qed.

(* TODO: should be upathxx *)
Lemma upath_refl x : upath x x [::].
Proof. by rewrite /upath spathxx. Qed.

Lemma upath_nil x p : upath x x p -> p = [::].
Proof. case: p => //= a p /and3P[/= A B C]. by rewrite -(eqP C) mem_last in A. Qed.

CoInductive usplit z x y : seq G -> Prop := 
  USplit p1 p2 : upath x z p1 -> upath z y p2 -> [disjoint x::p1 & p2]
                 -> usplit z x y (p1 ++ p2).

Lemma usplitP z x y p : z \in x :: p -> upath x y p -> usplit z x y p.
Proof. 
  move => in_p /andP [U P]. case: (ssplitP in_p P) U  => p1 p2 sp1 sp2.
  rewrite -cat_cons cat_uniq -disjoint_has disjoint_sym => /and3P [? C ?].
  suff H: z \notin p2 by constructor.
  apply/negP. apply: disjointE C _. by rewrite -(spath_last z x p1) // mem_last. 
Qed.

(* CoInductive usplitr z x y : seq G -> Prop :=  *)
(*   USplit p1 p2 : upath x z p1 -> upath z y p2 -> [disjoint x::rcons p1 z & p2] *)
(*                  -> usplit z x y (p1 ++ p2). *)


(* Lemma usplitPr z x y p : z \in p -> upath x y p -> usplit z x y p. *)


Lemma upathP x y : reflect (exists p, upath x y p) (connect sedge x y).
Proof.
  apply: (iffP connectP) => [[p p1 p2]|[p /and3P [p1 p2 /eqP p3]]]; last by exists p.
  exists (shorten x p). case/shortenP : p1 p2 => p' ? ? _ /esym/eqP ?. exact/and3P. 
Qed.

(* Really useful? *)
Lemma spathP x y : reflect (exists p, spath x y p) (connect sedge x y).
Proof. 
  apply: (iffP idP) => [|[p] /andP[A /eqP B]]; last by apply/connectP; exists p.
  case/upathP => p /upathW ?. by exists p.
Qed.

End Upath.

Lemma restrict_upath (G:sgraph) (x y:G) (A : pred G) (p : seq G) : 
  @upath (srestrict A) x y p -> upath x y p.
Proof. 
  elim: p x => // z p IH x /upath_consE [/= /andP [_ u1] u2 u3]. 
  rewrite upath_cons u1 u2 /=. exact: IH.
Qed.

Lemma lift_spath (G H : sgraph) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  spath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, spath a b p /\ map f p = p'.
Proof. 
  move => A I /andP [B /eqP C] D.  case: (lift_path A B D) => p [p1 p2]; subst. 
  exists p. split => //. apply/andP. split => //. rewrite last_map in C. by rewrite (I _ _ C).
Qed.

Lemma lift_upath (G H : sgraph) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  upath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath a b p /\ map f p = p'.
Proof.
  move => A B /andP [C D] E. case: (lift_spath A B D E) => p [p1 p2].
  exists p. split => //. apply/andP. split => //. by rewrite -(map_inj_uniq B) /= p2.
Qed.



Ltac spath_tac :=
  repeat match goal with [H : is_true (upath _ _ _) |- _] => move/upathW : H => H end;
  eauto using spath_concat, spath_rev.

(** ** Packaged paths *)

Section Pack.
Variables (G : sgraph).
Implicit Types x y z : G.
  
Definition Path x y := { p : seq G | spath x y p }.

Section Primitives.
  Variables (x y z : G) (p : Path x y) (q : Path y z).

  Definition nodes := x :: val p.
  Definition irred := uniq nodes.
  Definition tail := val p.

  Definition pcat_proof := spath_concat (valP p) (valP q).
  Definition pcat : Path x z := Sub (val p ++ val q) pcat_proof.

  Definition prev_proof := spath_rev (valP p).
  Definition prev : Path y x := Sub (srev x (val p)) prev_proof.

  Lemma path_last: last x (val p) = y.
  Proof. move: (valP p). exact: spath_last. Qed.
End Primitives.

Lemma mem_pcat u x y z (p : Path x y) (q : Path y z) :
  u \in nodes (pcat p q) = (u \in nodes p) || (u \in nodes q).
Admitted.

Lemma mem_prev u x y (p : Path x y) : 
  (u \in nodes (prev p)) = (u \in nodes p).
Admitted.


Lemma Path_split z x y (p : Path x y) : 
  z \in nodes p -> exists (p1 : Path x z) p2, p = pcat p1 p2.
Proof.
  move: (valP p) => pth_p in_p. 
  case/(ssplitP in_p) E : {1}(val p) / pth_p => [p1 p2 P1 P2].
  exists (Sub p1 P1). exists (Sub p2 P2). exact: val_inj. 
Qed.

Lemma prev_irred x y (p : Path x y) : irred p -> irred (prev p).
Admitted.
 
Lemma uPathP x y : reflect (exists p : Path x y, irred p) (connect sedge x y).
Admitted.

CoInductive isplit z x y : Path x y -> Prop := 
  ISplit (p1 : Path x z) (p2 : Path z y) : 
    irred p1 -> irred p2 -> [disjoint nodes p1 & tail p2] -> isplit z (pcat p1 p2).

Lemma isplitP z x y (p : Path x y) : irred p -> z \in nodes p -> isplit z p.
Admitted.
                                                   

(* Lemma isplitP z x y (p : Path x y) : irred p -> z \in nodes p ->  *)
(*   exists (p1 : Path x z) (p2 : Path z y), [/\ irred p1, irred p2 & [disjoint nodes p1 & tail p2]]. *)
(* Proof. *)
(*   move => irr_p in_p. case: (Path_split in_p) => p1 [p2] E. subst. *)
(*   exists p1. exists p2. rewrite /irred /= cat_uniq mem_cat negb_or -andbA in irr_p.  *)
(*   case/and5P : irr_p => A B C D E. split => //. *)
(* Admitted. *)
  
End Pack.



(** ** Forests *)

(** We define forests to be simple graphs where there exists at most one
duplicate free path between any two nodes *)


Definition tree_axiom (G:sgraph) := forall (x y : G), unique (upath x y).
  
Record tree := Tree { sgraph_of_tree :> sgraph ; 
                      treeP : tree_axiom sgraph_of_tree}.

Lemma restrict_tree (T : tree) (A : pred T) : 
  connect_sym (restrict A sedge).
Proof. apply: connect_symI => x y /=. by rewrite sgP [(x \in A) && _]andbC. Qed.


(** ** Disjoint Union *)

Section JoinSG.
  Variables (G1 G2 : sgraph).
  
  Definition join_rel (a b : G1 + G2) := 
    match a,b with
    | inl x, inl y => x -- y
    | inr x, inr y => x -- y
    | _,_ => false
    end.

  Lemma join_rel_sym : symmetric join_rel.
  Proof. move => [x|x] [y|y] //=; by rewrite sg_sym. Qed.

  Lemma join_rel_irrefl : irreflexive join_rel.
  Proof. move => [x|x] //=; by rewrite sg_irrefl. Qed.

  Definition sjoin := SGraph join_rel_sym join_rel_irrefl. 

  Lemma join_disc (x : G1) (y : G2) : connect join_rel (inl x) (inr y) = false.
  Proof. 
    apply/negP. case/connectP => p. elim: p x => // [[a|a]] //= p IH x.
    case/andP => _. exact: IH. 
  Qed.

End JoinSG.

Prenex Implicits join_rel.

(** ** Tree Decompositions *)


(** Covering is not really required, but makes the renaming theorem easier to state *)
Record sdecomp (T:tree) (G : sgraph) (bag : T -> {set G}) := SDecomp
  { sbag_cover x : exists t, x \in bag t; 
    sbag_edge x y : x -- y -> exists t, (x \in bag t) && (y \in bag t);
    sbag_conn x t1 t2  : x \in bag t1 -> x \in bag t2 ->
      connect (restrict [pred t | x \in bag t] sedge) t1 t2}.

Arguments sdecomp T G bag : clear implicits.

(** Non-standard: we do not substract 1 *)
Definition width (T G : finType) (D : T -> {set G}) := \max_(t:T) #|D t|.


Definition subtree (T : tree) (A : {set T}) :=
  {in A&A, forall (x y : T) p, upath x y p -> {subset p <= A}}.



Lemma upathPR (G : sgraph) (x y : G) A : 
  reflect (exists p : seq G, @upath (srestrict A) x y p) 
          (connect (restrict A sedge) x y).
Proof. exact: (@upathP (srestrict A)). Qed.



Set Printing Implicit Defensive.
Lemma subtree_connect (T : tree) (c : T) (a : pred T) : 
  subtree [set c' | connect (restrict a sedge) c c'].
Proof.
  move => u u' H1 H2 p H3.  
  have/upathPR [q pth_q] : connect (restrict a sedge) u u'.
  { apply: (connect_trans (y := c)).
    - by rewrite restrict_tree inE in H1 *.
    - by rewrite inE in H2. }
  have -> : p = q. { move/restrict_upath : pth_q. exact: treeP H3. }
  move => c' /(mem_tail u) in_q. 
  case: (usplitP (G := srestrict a) in_q pth_q) => p1 p2 A _ _.
  rewrite !inE in H1 H2 *. apply: connect_trans H1 _.
  apply/upathPR. by exists p1.
Qed.

Lemma subtree_link (T : tree) (C : {set T}) t0 c0 c p : 
  subtree C -> t0 \notin C -> c0 \in C -> t0 -- c0 -> c \in C -> upath t0 c p -> c0 \in p.
Proof.
  move => sub_C H1 H2 H3 H4 H5. 
  have [q Hq] : exists p, upath  c0 c p. 
  { apply/upathP. apply: (connect_trans (y := t0)). 
    + apply: connect1. by rewrite sgP.
    + apply/upathP. by exists p. }
  have X : upath  t0 c (c0::q). 
  { rewrite upath_cons H3 Hq /= andbT inE. 
    apply/orP => [[/eqP X|X]]. by subst; contrab. 
    move/sub_C : Hq. case/(_ _ _)/Wrap => // /(_ _ X) ?. by contrab. }
  rewrite (treeP H5 X). exact: mem_head.
Qed.


Definition clique (G : sgraph) (S : {set G}) :=
  {in S&S, forall x y, x != y -> x -- y}.

Lemma upathWW (G : sgraph) (x y : G) p : upath x y p -> path (@sedge G) x p.
Proof. by move/upathW/spathW. Qed.

Section DecompTheory.
  Variables (G : sgraph) (T : tree) (B : T -> {set G}).
  Implicit Types (t u v : T) (x y z : G).

  Hypothesis decD : sdecomp T G B.

  (* This lemma is not acutally used below *)
  Lemma sbag_mid t u v p : upath u v p -> t \in p -> B u :&: B v \subset B t.
  Proof.
    move => upth_p in_p. apply/subsetP => z /setIP [z_in_u z_in_v].
    case/upathPR : (sbag_conn decD z_in_u z_in_v) => q upth_q.
    have ? : q = p. { apply: treeP upth_p. exact: restrict_upath upth_q. }
    subst q. move/upathWW/path_restrict : upth_q. by apply.
  Qed.
    
  Arguments sbag_conn [T G B] dec x t1 t2 : rename.

  Lemma decomp_clique (S : {set G}) : 
    0 < #|S| -> clique S -> exists t : T, S \subset B t.
  Proof. 
    move: S. 
    apply: (nat_size_ind (f := fun S : {set G} => #|S|)) => S IH inh_S clique_S.
    case: (leqP #|S| 2) => card_S. 
    - case: (card12 inh_S card_S) => [[x]|[x] [y] [Hxy]] ?; subst S.
      + case: (sbag_cover decD x) => t A. exists t. by rewrite sub1set.
      + have xy: x -- y. by apply: clique_S => //; rewrite !inE !eqxx ?orbT.
        case: (sbag_edge decD xy) => t A. exists t. by rewrite subUset !sub1set.
    - have [v [v0] [[Hv Hv0 X]]] := card_gt2 (ltnW card_S).
      pose S0 := S :\ v.
      pose T0 := [set t | S0 \subset B t]. 
      (* Wlog. no bag from [T0] contains [v] *)
      case: (boolP [forall t in T0, v \notin B t]); last first. (* TODO: wlog? *)
      { rewrite negb_forall_in. case/exists_inP => t. rewrite inE negbK => H1 H2.
        exists t. by rewrite -(setD1K Hv) subUset sub1set H2 H1. }
      move/forall_inP => HT0.
      have HT0' t : v \in B t -> ~~ (S0 \subset B t).
      { apply: contraTN => C. apply: HT0. by rewrite inE. }
      have pairs x y : x \in S -> y \in S -> exists t, x \in B t /\ y \in B t.
      { move => xS yS.  case: (IH [set x;y]). 
        - rewrite cardsU1 cards1 addn1. case (_ \notin _) => //=. exact: ltnW.
        - by rewrite cards2. 
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subUset !sub1set xS. 
        - move => t. rewrite subUset !sub1set => /andP [? ?]. by exists t. }
      (* obtain some node [c] whose bag contains [[set v,v0]] and
      consider its subtree outside of T0 *)
      have [c [Hc1 Hc2]] : exists t, v \in B t /\ v0 \in B t by apply: pairs. 
      pose C := [set t | connect (restrict [predC T0] sedge) c t].
      have inC: c \in C by rewrite inE connect0. 
      have C_subtree : subtree C by apply: subtree_connect.
      have disC: [disjoint C & T0]. 
      { rewrite disjoints_subset. apply/subsetP => c0. rewrite 2!inE.
        case/connectP => p /path_restrict H ->. case: p H => /=. 
        - move => _. apply/negPn. move/HT0. by rewrite Hc1. 
        - move => a p. apply. exact: mem_last. }
      (* Let [t0 -- c0] be the link connecting [T0] to [C] *)
      have [t0 [c0 [Ht0 Hc0 tc0]]] : exists t0 c0, [/\ t0 \in T0, c0 \in C & t0 -- c0].
      { case: (IH S0 _ _) => [|||t Ht].
        - by rewrite [#|S|](cardsD1 v) Hv.
        - apply/card_gt0P. exists v0. by rewrite !inE eq_sym X.
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subD1set.
        - have A : v0 \in B t. { apply (subsetP Ht). by rewrite !inE eq_sym X. }
          have H : connect sedge c t. 
          { apply: connect_mono (sbag_conn decD v0 c t Hc2 A). exact: subrel_restrict. }
          (* bespoke - is there a reasonable lemma? *)
          case/connectP : H => p. generalize c inC. 
          elim: p => /= [|a p IHp] c0 inC0.
          + move => _ /= ?. subst c0. 
            case: (disjointE disC inC0 _). by rewrite !inE.
          + case/andP => H1 H2 H3. case: (boolP (a \in T0)) => Ha.
            * exists a. exists c0. by rewrite sgP.
            * apply: IHp H3 => //. rewrite inE. 
              apply: (connect_trans (y := c0)).
              by rewrite inE in inC0.
              apply: connect1 => /=. rewrite !in_simpl /= Ha H1 !andbT. 
              apply/negP. exact: disjointE disC inC0. }
      have t0P p c' : c' \in C -> upath t0 c' p -> c0 \in p.
      { apply: subtree_link tc0 => //.  apply/negP => H. exact: (disjointE disC H Ht0). }
      suff A : c0 \in T0 by case: (disjointE disC Hc0 A).
      rewrite inE. apply/subsetP => u u_in_S0.
      have Hu: u \in B t0. { rewrite inE in Ht0. exact: (subsetP Ht0). }
      have [cu [Hcu1 Hcu2]] : exists t,  u \in B t /\ v \in B t. 
      { apply: (pairs u v) => //. move: u_in_S0. rewrite inE. by case: (_ \notin _). }
      move:(sbag_conn decD u t0 cu Hu Hcu1). case/upathPR => q upth_q. 
      suff Hq : c0 \in q. { move/upathWW/path_restrict : upth_q. by apply. }
      apply: t0P (restrict_upath upth_q).
      rewrite inE. move: (sbag_conn decD v c cu Hc1 Hcu2).
      apply: connect_mono => t t' /=. 
      rewrite !inE -andbA => /and3P [*]. by rewrite !HT0'.
  Qed.
      
End DecompTheory.

Definition K4_rel := [rel x y : 'I_4 | x != y].

Fact K4_sym : symmetric K4_rel. 
Proof. move => x y /=. by rewrite eq_sym. Qed.

Fact K4_irrefl : irreflexive K4_rel. 
Proof. move => x /=. by rewrite eqxx. Qed.

Definition K4 := SGraph K4_sym K4_irrefl.

Lemma K4_bag (T : tree) (D : T -> {set K4}) : 
  sdecomp T K4 D -> exists t, 4 <= #|D t|.
Proof.
  move => decD.
  case: (@decomp_clique _ _ _ decD setT _ _) => //.
  - by rewrite cardsT card_ord.
  - move => t A. exists t. rewrite -[4](card_ord 4) -cardsT. 
    exact: subset_leq_card.
Qed.

Lemma K4_width (T : tree) (D : T -> {set K4}) : 
  sdecomp T K4 D -> 4 <= width D.
Proof. case/K4_bag => t Ht. apply: leq_trans Ht _. exact: leq_bigmax. Qed.

(** ** Minors *)

Definition connected (G : sgraph) (S : {set G}) :=
  {in S & S, forall x y : G, connect (restrict (mem S) sedge) x y}.  

Notation "f @^-1 x" := (preimset f (mem (pred1 x))) (at level 24) : set_scope.  

(** H is a minor of G -- The order allows us to write [minor G] for the
colletion of [G]s minors *)

CoInductive minor (G H : sgraph) : Prop :=
  MinorI (phi : G -> option H) of 
    (forall y : H, exists x, phi x = Some y) 
  & (forall y : H, connected (phi @^-1 Some y)) 
  & (forall x y : H, x -- y -> 
     exists x0 y0, [/\ x0 \in phi @^-1 Some x, y0 \in phi @^-1 Some y & x0 -- y0]).

Lemma minor_trans : Transitive minor.
Proof.
  move => G H I [f f1 f2 f3] [g g1 g2 g3].
  exists (fun x => obind g (f x)).
  - move => y. case: (g1 y) => y'. case: (f1 y') => x E1 ?.
    exists x. by rewrite E1.
  - move => z x y. rewrite !inE. 
    case Ef : (f x) => [fx|] //= gfx. case Eg : (f y) => [fy|] //= gfy.
    move: (g2 z fx fy). rewrite !inE. case/(_ _ _)/Wrap => // /connectP => [[p]]. 
    elim: p x fx Ef gfx => /= [|a p IH] x fx Ef gfx.
    + move => _ ?. subst fy. 
      move: (f2 fx x y). rewrite !inE Ef Eg. case/(_ _ _)/Wrap => //. 
      apply: connect_mono => a b /=. rewrite !inE -andbA. 
      case/and3P => /eqP-> /eqP-> -> /=. by rewrite (eqP gfx) !eqxx.
    + rewrite !inE -!andbA => /and4P [H1 H2 H3 H4] H5. 
      case: (f1 a) => x' Hx'. apply: (connect_trans (y := x')); last exact: IH H5.
      move/f3 : (H3) => [x0] [y0] [X1 X2 X3]. 
      apply: (connect_trans (y := x0)); last apply: (connect_trans (y := y0)).
      * move: (f2 fx x x0). rewrite !inE ?Ef ?eqxx in X1 *. case/(_ _ _)/Wrap => //.
        apply: connect_mono => u v /=. rewrite !inE -andbA. 
        case/and3P => /eqP-> /eqP-> -> /=. by rewrite H1.
      * apply: connect1. rewrite /= !inE ?X3 ?andbT in X1 X2 *. 
        by rewrite (eqP X1) (eqP X2) /= (eqP gfx) eqxx.
      * move: (f2 a y0 x' X2). case/(_ _)/Wrap. by rewrite !inE Hx'.
        apply: connect_mono => u v /=. rewrite !inE -andbA. 
        case/and3P => /eqP-> /eqP-> -> /=. by rewrite H2.
  - move => x y /g3 [x'] [y'] [Hx' Hy'] /f3 [x0] [y0] [Hx0 Hy0 ?].
    exists x0. exists y0. rewrite !inE in Hx' Hy' Hx0 Hy0 *. 
    split => //; reflect_eq; by rewrite (Hx0,Hy0) /= (Hx',Hy'). 
Qed.

CoInductive strict_minor (G H : sgraph) : Prop :=
  SMinorI (phi : G -> H) of 
    (forall y : H, exists x, phi x = y) 
  & (forall y : H, connected (phi @^-1 y)) 
  & (forall x y : H, x -- y -> 
     exists x0 y0, [/\ x0 \in phi @^-1 x, y0 \in phi @^-1 y & x0 -- y0]).

Lemma strict_is_minor (G H : sgraph) : strict_minor G H -> minor G H.
Proof.
  case => phi A B C. exists (Some \o phi) => //= y.
  case: (A y) => x <-. by exists x.
Qed.

Lemma sub_minor (S G : sgraph) : subgraph S G -> minor G S.
Proof.
  move => [h inj_h hom_h].
  pose phi x := if @idP (x \in codom h) is ReflectT p then Some (iinv p) else None.
  exists phi.
  - move => y. exists (h y). rewrite /phi. 
    case: {-}_ / idP => [p|]; by rewrite ?iinv_f ?codom_f.
  - move => y x0 y0. rewrite !inE {1 2}/phi. 
    case: {-}_ / idP => // p /eqP[E1]. 
    case: {-}_ / idP => // q /eqP[E2]. 
    suff -> : (x0 = y0) by exact: connect0. 
    by rewrite -(f_iinv p) -(f_iinv q) E1 E2. 
  - move => x y A. move/hom_h : (A). 
    case => [/inj_h ?|B]; first by subst; rewrite sgP in A.
    exists (h x). exists (h y). rewrite !inE /phi B. 
    by do 2 case: {-}_ / idP => [?|]; rewrite ?codom_f ?iinv_f ?eqxx //.
Qed.

Lemma induced_minor (G : sgraph) (S : {set G}) : minor G (induced S).
Proof. apply: sub_minor. exact: induced_sub. Qed.

Definition rename (T G G' : finType) (B: T -> {set G}) (h : G -> G') := [fun x => h @: B x].

Definition edge_surjective (G1 G2 : sgraph) (h : G1 -> G2) :=
  forall x y : G2 , x -- y -> exists x0 y0, [/\ h x0 = x, h y0 = y & x0 -- y0].

(* The following should hold but does not fit the use case for minors *)
Lemma rename_sdecomp (T : tree) (G H : sgraph) D (dec_D : sdecomp T G D) (h :G -> H) : 
  hom_s h -> surjective h -> edge_surjective h -> 
  (forall x y, h x = h y -> exists t, (x \in D t) && (y \in D t)) -> 
  @sdecomp T _ (rename D h).
Abort. 

(* This should hold, but there are several choices for S, the induced
subgraph of the range of [phi] seems to be the canonical one. *)
Lemma minor_split (G H : sgraph) : 
  minor G H -> exists2 S, subgraph S G & strict_minor S H.
Proof.
  move => [phi p1 p2 p3].
  set S := [set x | phi x]. 
  exists (induced S); first exact: induced_sub.
  wlog x0 : / H.
  { admit. (* the empty graph is a minor of ever graph *) }
  pose f (x : induced S) := odflt x0 (phi (val x)).
  exists f. 
Abort. 


Lemma width_minor (G H : sgraph) (T : tree) (B : T -> {set G}) : 
  sdecomp T G B -> minor G H -> exists B', sdecomp T H B' /\ width B' <= width B.
Proof.
  move => decT [phi p1 p2 p3].
  pose B' t := [set x : H | [exists (x0 | x0 \in B t), phi x0 == Some x]].
  exists B'. split.
  - split. 
    + move => y. case: (p1 y) => x /eqP Hx.
      case: (sbag_cover decT x) => t Ht.
      exists t. apply/pimsetP. by exists x.
    + move => x y xy. move/p3: xy => [x0] [y0]. rewrite !inE => [[H1 H2 H3]].
      case: (sbag_edge decT H3) => t /andP [T1 T2]. exists t. 
      apply/andP; split; apply/pimsetP; by [exists x0|exists y0].
    + have conn_pre1 t1 t2 x x0 :
        phi x0 == Some x -> x0 \in B t1 -> x0 \in B t2 ->
        connect (restrict [pred t | x \in B' t] sedge) t1 t2.
      { move => H1 H2 H3. case: (sbag_conn decT H2 H3).
        apply: connect_mono => u v /=. rewrite !in_simpl -!andbA => /and3P [? ? ?]. 
        apply/and3P; split => //; apply/pimsetP; eexists; eauto. }
      move => x t1 t2 /pimsetP [x0 X1 X2] /pimsetP [y0 Y1 Y2].
      move: (p2 x x0 y0). rewrite !inE. case/(_ _ _)/Wrap => // /connectP [p]. 
      elim: p t1 x0 X1 X2 => /= [|z0 p IH] t1 x0 X1 X2. 
      * move => _ E. subst x0. exact: conn_pre1 X1 Y1.
      * rewrite -!andbA => /and3P [H1 H2 /andP [H3 H4] H5].
        case: (sbag_edge decT H3) => t /andP [T1 T2].
        apply: (connect_trans (y := t)). 
        -- move => {p IH H4 H5 y0 Y1 Y2 X2}. rewrite !inE in H1 H2.
           exact: conn_pre1 X1 T1.
        -- apply: IH H4 H5 => //. by rewrite inE in H2.
  - apply: max_mono => t. exact: pimset_card.
Qed.


Definition K4_free (G : sgraph) := ~ minor G K4.

Lemma TW2_K4_free (G : sgraph) (T : tree) (B : T -> {set G}) : 
  sdecomp T G B -> width B <= 3 -> K4_free G.
Proof.
  move => decT wT M. case: (width_minor decT M) => B' [B1 B2].
  suff: 4 <= 3 by []. 
  apply: leq_trans wT. apply: leq_trans B2. exact: K4_width.
Qed.

(** decidability of cycle agnostic path properties *)
Definition short_prop (T:eqType) e (P : T -> seq T -> bool) := 
  forall x p, path e x p -> P x (shorten x p) -> P x p.

Lemma short_prop_dec (T : finType) e (P : T -> seq T -> bool) x : 
  short_prop e P -> decidable (forall p, path e x p -> P x p).
Proof.
  move => spP. 
  pose Pb := [forall n : 'I_#|T|, forall p : n.-tuple T, path e x p ==> P x p].
  apply: (decP (b := Pb)). apply: (iffP forallP) => H.
  - move => p pth_p. apply: spP => //. 
    case/shortenP : pth_p => p' pth_p' uniq_p' _. 
    have bound_p' : size p' < #|T|. 
    { move/card_uniqP : uniq_p' => /= <-. exact: max_card. }
    move/forall_inP: (H (Ordinal bound_p')) => /(_ (in_tuple p')). 
    by apply.
  - move => n. apply/forall_inP => p. exact: H.
Qed.

Lemma dec_eq (P : Prop) (decP : decidable P) : decP <-> P.
Proof. by case: decP. Qed.

(** ** Checkpoints *)

Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types x y z : G.

  Let avoids z x y (p : seq G) := upath x y p && (z \notin x::p).
  Definition avoidable z x y := [exists n : 'I_#|G|, exists p : n.-tuple G, avoids z x y p].

  Definition cp x y := locked [set z | ~~ avoidable z x y].

  Lemma cpPn z x y : reflect (exists2 p, upath x y p & z \notin x::p) (z \notin cp x y).
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

  Hypothesis G_conn : forall x y:G, connect sedge x y.

  (* Lemma cpPn' x y z :  *)
  (*   reflect [/\ z != x, z != y & exists p, [/\ spath x y p & z \notin p]] (z \notin cp x y). *)
  (* Proof. apply: (iffP (cpPn _ _ _)).         *)
  (* Admitted. (* should not be used *) *)

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
    apply/subsetP => u /cpP cp_u. rewrite -[_ \in _]negbK inE negb_or.
    apply/negP => /andP[]. 
    case/cpPn => (* A B *) [p] [/upathW p1 p2]. case/cpPn => (* C D *) [q] [/upathW q1 /notin_tail q2]. 
    move: (cp_u (p ++ q)). case/(_ _)/Wrap; first exact: spath_concat q1.
    by rewrite -cat_cons mem_cat (negbTE p2) (negbTE q2).
  Qed.

  Lemma cpN_cat a x z y : a \notin cp x z -> a \notin cp z y -> a \notin cp x y.
  Proof. 
    move => /negbTE A /negbTE B. apply/negP. move/(subsetP (cp_triangle z)). 
    by rewrite !inE A B.
  Qed.

  Definition CP (U : {set G}) := \bigcup_(xy in setX U U) cp xy.1 xy.2.
  
  (* could provide upaths if needed *)
  Lemma cp_mid z x y t : z \in cp x y -> 
    exists p1 p2, [/\ spath z x p1, spath z y p2 & t \notin p1 \/ t \notin p2].
  Proof.
    case/upathP : (G_conn x y) => p /andP [p1 p2] /cpP cp_z.
    move/(_ _ p2) : cp_z => H. 
    case: (ssplitP H p2) p1 => {p p2 H} pl pr Pl Pr U. 
    exists (srev x pl). exists pr. split => //. 
    - exact: spath_rev.
    - apply/orP. rewrite -negb_and !mem_rev. apply/negP => /andP[/mem_belast E F].
      rewrite -cat_cons cat_uniq in U. case/and3P : U => _ /hasPn /= B _.
      by rewrite (negbTE (B _ F)) in E.
  Qed.

  (* Lemma 13 *)
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
    move: (cp_mid t x_cp) => [p1] [p2] [u1 u2] H.
    wlog P1 : p1 p2 x1 x2 u1 u2 H x1U x2U x_cp / t \notin p1 => [W|{H}].
    (* FIXME: This [done] takes to long *)
    { case: H => H; [apply: (W p1 p2 x1 x2)|apply: (W p2 p1 x2 x1)] => //; try tauto. 
      by rewrite cp_sym. }
    move: (cp_mid t y_cp) => [q1] [q2] [v1 v2] H.
    wlog P2 : q1 q2 y1 y2 v1 v2 H y1U y2U y_cp / t \notin q1 => [W|{H}].
    { case: H => H; [apply: (W q1 q2 y1 y2)|apply: (W q2 q1 y2 y1)] => //; try tauto. 
      by rewrite cp_sym. }
    apply/bigcupP; exists (x1,y1) => /= ; first exact/setXP. 
    apply: contraTT t_cp => /cpPn [s] [/upathW s1 /notin_tail s2].
    apply: (cpNI (p := p1++s++srev y q1)). 
    - apply: spath_concat u1 _. apply: spath_concat s1 _. exact: spath_rev. 
    - rewrite !inE !mem_cat !negb_or mem_rev T1 P1 s2 /=.  
      apply/negP. move/mem_belast. by rewrite !inE (negbTE T2) (negbTE P2).
  Qed.

  (* BEGIN TEST *)
  Lemma cpP' x y z : reflect (forall p : Path x y, z \in nodes p) (z \in cp x y).
  Admitted.

  Lemma cpPn' x y z : reflect (exists2 p : Path x y, irred p & z \notin nodes p) (z \notin cp x y).
  Admitted.

  Lemma cpNI' x y (p : Path x y) z : z \notin nodes p -> z \notin cp x y.
  Admitted.


  Lemma nodes_prev x y (p : Path x y) : nodes (prev p) =i nodes p.
  Admitted.

  Unset Printing Implicit Defensive.

  Lemma cp_mid' (z x y t : G) : t != z -> z \in cp x y ->
   exists (p1 : Path z x) (p2 : Path z y), t \notin nodes p1 \/ t \notin nodes p2.
  Proof. 
    move => tNz cp_z.
    case/uPathP : (G_conn x y) => p irr_p.
    move/cpP'/(_ p) : cp_z. case/(isplitP irr_p) => p1 p2 A B C.
    exists (prev p1). exists p2. rewrite nodes_prev. apply/orP. 
    case E : (t \in nodes p1) => //=. rewrite !inE (negbTE tNz) /=.
    apply/negP. exact: disjointE C _.
  Qed.
  
  Lemma CP_closed' U x y : 
    x \in CP U -> y \in CP U -> cp x y \subset CP U.
  Proof.
    case/bigcupP => [[x1 x2] /= /setXP [x1U x2U] x_cp]. 
    case/bigcupP => [[y1 y2] /= /setXP [y1U y2U] y_cp]. 
    apply/subsetP => t t_cp. 
    case (boolP (t == y)) => [/eqP-> //|T2].
    { apply/bigcupP. exists (y1,y2); by [exact/setXP|]. }
    case (boolP (t == x)) => [/eqP-> //|T1].
    { apply/bigcupP. exists (x1,x2); by [exact/setXP|]. }
    move: (cp_mid' T1 x_cp) => [p1] [p2] H.
    wlog P1 : x1 x2 p1 p2 x1U x2U x_cp H / t \notin nodes p1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ p1 p2) => //; tauto.
      - rewrite cp_sym in x_cp. apply : (W _ _ p2 p1) => //; tauto. }
    move: (cp_mid' T2 y_cp) => [q1] [q2] H.
    wlog P2 : y1 y2 q1 q2 y1U y2U y_cp H / t \notin nodes q1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ q1 q2) => //; tauto.
      - rewrite cp_sym in y_cp. apply : (W _ _ q2 q1) => //; tauto. }
    apply/bigcupP; exists (x1,y1) => /= ; first exact/setXP. 
    apply: contraTT t_cp => /cpPn' [s _ Hs]. 
    suff: t \notin nodes (pcat p1 (pcat s (prev q1))) by apply: cpNI'.
    by rewrite !mem_pcat !mem_prev (negbTE P1) (negbTE P2) (negbTE Hs).
  Qed.

  (* END TEST *)

  Definition link_rel := [rel x y | (x != y) && (cp x y \subset [set x; y])].

  Lemma link_sym : symmetric link_rel.
  Proof. move => x y. by rewrite /= eq_sym cp_sym set2C. Qed.

  Lemma link_irrefl : irreflexive link_rel.
  Proof. move => x /=. by rewrite eqxx. Qed.

  Definition link_graph := SGraph link_sym link_irrefl.

  Lemma link_avoid (x y z : G) : 
    z \notin [set x; y] -> link_rel x y -> exists2 p, spath x y p & z \notin (x::p).
  Admitted.
  (* Proof. *)
  (*   move => Hz /andP[l1 l2]. *)
  (*   suff/cpPn [[p] [? ?]] : z \notin cp x y by exists p. *)
  (*   apply: contraNN Hz. by move/(subsetP l2).  *)
  (* Qed. *)

  (* Lemma path_ind y (P : forall x, Path x y -> Prop) :  *)
  (*   (forall x (p : Path x x), nodes p = [:: x] -> P x p)  *)
  (*   (forall x y (p : Path x y) *)
  (*   forall x (p : Path x y) : P x P  *)

  (* Lemma link_seq_cp (y x : G) (p : @Path link_graph x y) :  *)
  (*   cp x y \subset nodes p. *)
  (* Proof. *)
    
    
  Lemma link_seq_cp (y x : G) p :
    @spath link_graph x y p -> cp x y \subset x :: p.
  Proof.
    elim: p x => [|z p IH] x /=.
    - move/spath_nil->. rewrite cpxx. admit.
    - rewrite spath_cons => /andP [/= /andP [A B] /IH C]. 
      apply: subset_trans (cp_triangle z) _.
      (* TODO: set theory reasoning *)
  Admitted.

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
    move/link_seq_cp : P1 => P1. move/link_seq_cp : P2 => P2.
    (* TODO: p1 and p2 are disjoint, so the intersection is just {x,y} *)
  Admitted.

  
  (** This is redundant, but a boolean property. See [checkpoint_seq]
  in extraction.v *)
  Variables (i o : G).
  Hypothesis conn_io : connect sedge i o.

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

  Variable (U : {set G}).

  Lemma notin_srev z x p : z \notin x::p -> z \notin srev x p.
  Proof. apply: contraNN. rewrite /srev mem_rev. exact: mem_belast. Qed.

  (* Lemma 16 *)
  Lemma CP_base x y : x \in CP U -> y \in CP U ->
    exists x' y':G, [/\ x' \in U, y' \in U & [set x;y] \subset cp x' y'].
  Proof.
    move => U1 U2. case/bigcupP : U1 => [[x1 x2]]. case/bigcupP : U2 => [[y1 y2]] /=.
    rewrite !inE /= => /andP[Uy1 Uy2] cp_y /andP[Ux1 Ux2] cp_x.
    case: (boolP (x \in cp y1 y2)) => [C|Wx]; first by exists y1; exists y2; rewrite subUset !sub1set C.
    case: (boolP (y \in cp x1 x2)) => [C|Wy]; first by exists x1; exists x2; rewrite subUset !sub1set C.
    gen have H,A: x x1 x2 y1 y2 {Ux1 Ux2 Uy1 Uy2 Wy cp_y} Wx cp_x /
      (x \in cp x1 y1) || (x \in cp x2 y2).
    { case/cpPn : Wx => p pth_p av_x.
      apply: contraTT cp_x. rewrite negb_or => /andP[/cpPn [s s1 s2] /cpPn [t t1 t2]].
      apply: (cpNI (p := s++p++srev x2 t)); first by spath_tac.
      by rewrite -cat_cons !mem_cat /= 2!negb_or s2 (notin_tail av_x) notin_srev. }
    move: (H _ _ _ _ _ Wy cp_y) => B {H}. rewrite (cp_sym y1 x1) (cp_sym y2 x2) in B. 
    wlog {A} /andP [Hx Hy] : x1 x2 y1 y2 A B cp_x cp_y Ux1 Ux2 Uy1 Uy2 Wx Wy
        / (x \in cp x1 y1) && (y \notin cp x1 y1).
    { case: (boolP (y \in cp x1 y1)) A B => A; case: (boolP (x \in cp x1 y1)) => /= B C D W. 
      - by exists x1; exists y1; rewrite subUset !sub1set B. 
      - case: (boolP (y \in cp x2 y2)) => E. (* TOTHINK: why the second case anlysis in this case? *)
        + exists x2; exists y2; by rewrite subUset !sub1set C.
        + move: (W x2 x1 y2 y1). rewrite (cp_sym x2 x1) (cp_sym y2 y1) A C /= orbT. exact.
      - apply: (W x1 x2 y1 y2) => //. by rewrite B. by rewrite D. (* exact/andP. *)
      - exists x2; exists y2; by rewrite subUset !sub1set C D. }
    rewrite (negbTE Hy) /= in B.
    case: (boolP (x \in cp x2 y2)) => [C|Wx']; first by exists x2; exists y2; rewrite subUset !sub1set C.
    exists x1. exists y2. rewrite subUset !sub1set. split => //. apply/andP; split.
    - apply: contraTT cp_x => C. apply: cpN_cat C _. by rewrite cp_sym.
    - apply: contraTT cp_y. apply: cpN_cat. by rewrite cp_sym.
  Qed.

  (* BEGIN TEST *)

  Lemma CP_base' x y : x \in CP U -> y \in CP U ->
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
    move: (H _ _ _ _ _ Wy cp_y) => B {H}. rewrite (cp_sym y1 x1) (cp_sym y2 x2) in B. 
    wlog {A} /andP [Hx Hy] : x1 x2 y1 y2 A B cp_x cp_y Ux1 Ux2 Uy1 Uy2 Wx Wy
        / (x \in cp x1 y1) && (y \notin cp x1 y1).
    { case: (boolP (y \in cp x1 y1)) A B => A; case: (boolP (x \in cp x1 y1)) => /= B C D W. 
      - by exists x1; exists y1; rewrite subUset !sub1set B. 
      - case: (boolP (y \in cp x2 y2)) => E. (* TOTHINK: why the second case anlysis in this case? *)
        + exists x2; exists y2; by rewrite subUset !sub1set C.
        + move: (W x2 x1 y2 y1). rewrite (cp_sym x2 x1) (cp_sym y2 y1) A C /= orbT. exact.
      - apply: (W x1 x2 y1 y2) => //. by rewrite B. by rewrite D. (* exact/andP. *)
      - exists x2; exists y2; by rewrite subUset !sub1set C D. }
    rewrite (negbTE Hy) /= in B.
    case: (boolP (x \in cp x2 y2)) => [C|Wx']; first by exists x2; exists y2; rewrite subUset !sub1set C.
    exists x1. exists y2. rewrite subUset !sub1set. split => //. apply/andP; split.
    - apply: contraTT cp_x => C. apply: cpN_cat C _. by rewrite cp_sym.
    - apply: contraTT cp_y. apply: cpN_cat. by rewrite cp_sym.
  Qed.

  (* END TEST *)

  Print Assumptions CP_base.

  (* Lemma 16 *)
  Definition CP_ := @induced link_graph (CP U).

  Lemma link_sup (x y : CP_) : x -- y -> (val x:G) -- val y.
  Abort.

  Lemma index_uniq_inj (T:eqType) (s : seq T) : 
    {in s, injective (index^~ s)}. 
  Proof. 
    move => x in_s y E. 
    have A : y \in s by rewrite -index_mem -E index_mem.
    by rewrite -(nth_index x in_s) E nth_index.
  Qed.

  Lemma mem_catD (T:finType) (x:T) (s1 s2 : seq T) : [disjoint s1 & s2] ->
      (x \in s1 ++ s2) = (x \in s1) (+) (x \in s2).
  Proof. 
    move => D. rewrite mem_cat. case C1 : (x \in s1) => //=. 
    symmetry. apply/negP. exact: disjointE D _.
  Qed.
  Arguments mem_catD [T x s1 s2].
    

 Lemma CP_base_ (x y : CP_) : 
    exists x' y':G, [/\ x' \in U, y' \in U & [set val x;val y] \subset cp x' y'].
  Proof. exact: CP_base  (svalP x) (svalP y). Qed.

  Lemma CP_triangle_avoid x' y' (x y z: link_graph) : 
    x -- y -> y -- z -> z -- x -> x \in cp x' y' -> y \in cp x' y' -> z \notin cp x' y'.
  Proof.
    move => xy yz zx Cx Cy. apply/negP => Cz.
    case/upathP : (G_conn x' y') => p pth_p. 
    gen have Hp,x_in_p: x Cx {xy yz zx} / x \in x'::p.
    { apply/cpP. apply: Cx. by spath_tac. }
    move: (Hp _ Cy) (Hp _ Cz) => y_in_p z_in_p.
    pose I (x: link_graph) := index (x) (x'::p).
    have D (x1 x2 : link_graph) : x1 -- x2 -> x1 \in x'::p -> I x1 <> I x2.
    { move => H in_p. move/index_uniq_inj. case/(_ _ )/Wrap => //.
      move => ?. subst. by rewrite sgP in H. }
    wlog /andP [x_lt_y y_lt_z] : x y z xy yz zx x_in_p y_in_p z_in_p Cy {Cx  Cz D Hp}
         / I x < I y < I z.
    { move => W. 
      wlog x_lt_y : x y xy yz zx Cx Cy x_in_p y_in_p z_in_p / I x < I y => [W2|].
      { case: (ltngtP (I x) (I y)); [exact: W2|apply:W2; by rewrite // sg_sym |exact: D]. }
      case: (ltngtP (I y) (I z)) => [Hyz|Hyz|]; last exact: D. 
      - exact: (W x y z).
      - case: (ltngtP (I z) (I x)) => [Hzx|Hzx|]; last exact: D. 
        + exact: (W z x y).
        + apply: (W x z y); by rewrite // sg_sym. }
    case/(usplitP (G := G) x_in_p) def_p : {1}p / pth_p => [p1 p2 pth1 pth2 D]. subst.
    gen have Gy, Hy : y x_lt_y {xy yz y_in_p Cy y_lt_z} / y \notin x' :: p1.
    { apply: contraTN (x_lt_y) => X. 
      rewrite -leqNgt /I -cat_cons !index_cat (spath_end (upathW pth1)) X. 
      rewrite -(spath_last _ _ _ (upathW pth1)) index_last; last exact: upath_uniq pth1.
      by rewrite -ltnS index_mem. }
    have {Gy} Hz : z \notin x' :: p1 by apply: Gy; exact: ltn_trans y_lt_z. 
    rewrite -!cat_cons !(mem_catD D)  (negbTE Hy) (negbTE Hz) /= in y_in_p z_in_p.
    move/(mem_tail (x)) : z_in_p => C. (* this looses information that needs to be recovered *)
    case/(usplitP (G:=G) C) def_p1 : {1}p2 / pth2 => [p21 p22 pth21 pth22 D2]. subst.
    have Hy': y \notin p22. 
    { move: D2. rewrite disjoint_cons => /andP [? D2].
      apply: contraTN y_lt_z => X. 
      rewrite -leqNgt /I -!cat_cons !index_cat (negbTE Hy) (negbTE Hz) leq_add2l.
      have -> : y \in p21 = false. 
      { apply/negP. apply: disjointE X. by rewrite disjoint_sym. }
      have Y : z \in p21. 
      { rewrite (spath_endD (upathW pth21)) //. by rewrite eq_sym; apply: contraTN zx => /= ->. }
      apply: leq_trans (leq_addr _ _). rewrite Y. apply: ltnW. by rewrite index_mem. }
    move: Cy. apply/negP. 
    have: (y) \notin cp (x) (z). 
    { case/andP : zx => _ sub. apply/negP. rewrite cp_sym. move/(subsetP sub). 
      rewrite !inE. by case/orP => /eqP ?;subst; rewrite sg_irrefl in xy yz. }
    case/cpPn => q pth_q /notin_tail Hq. 
    apply: (cpNI (p := p1++q++p22)); first by spath_tac.
    rewrite -cat_cons !mem_cat (negbTE Hy) (negbTE Hq) //=.
  Qed.

  Arguments cpP' [x y z].

  (* BEGIN TEST*)

  Lemma disjointFr (T : finType) (A B : pred T) (x:T) : 
    [disjoint A & B] -> x \in A -> x \in B = false.
  Admitted.

  Lemma disjointFl (T : finType) (A B : pred T) (x:T) : 
    [disjoint A & B] -> x \in B -> x \in A = false.
  Admitted.

  Definition idx x y (p : Path x y) u := index u (nodes p).

  Lemma idx_end x y (p : Path x y) : 
    irred p -> idx p y = size (tail p).
  Proof.
    move => irr_p. by rewrite /idx /nodes -[in index _](path_last p) index_last.
  Qed.


  Section IDX.
    Variables (x z y : G) (p : Path x z) (q : Path z y).
    Implicit Types u v : G.

    Lemma nodes_end : z \in nodes p.
    Admitted.


    Lemma idx_inj : {in nodes p, injective (idx p) }.
    Proof.
      move => u in_s v E. rewrite /idx in E.
      have A : v \in nodes p. by rewrite -index_mem -E index_mem.
      by rewrite -(nth_index x in_s) E nth_index.
    Qed.

    Lemma mem_pcatT u : (u \in nodes (pcat p q)) = (u \in nodes p) || (u \in tail q).
    Admitted.

    Lemma tailW : {subset tail p <= nodes p}.
    Proof. move => u. exact: mem_tail. Qed.

    Hypothesis irr_pq : irred (pcat p q).
    
    Let dis_pq : [disjoint nodes p & tail q].
    Admitted.

    Let irr_p : irred p.
    Admitted.  

    Let irr_q : irred q.
    Admitted.  


    Lemma idxR u : u \in nodes (pcat p q) -> 
      (u \in tail q) = (idx (pcat p q) z < idx (pcat p q) u).
    Proof.
      move => A. symmetry. rewrite /idx /pcat /nodes -cat_cons index_cat nodes_end.
      rewrite index_cat mem_pcatT in A *. case/orP: A => A.
      - rewrite A (disjointFr dis_pq A). apply/negbTE. 
        rewrite -leqNgt -!/(idx _ _) (idx_end irr_p) -ltnS.
        apply: leq_ltn_trans (index_size _ _) _. rewrite ltnS.
        
    Admitted.

    (* Lemma idxL u : u \in nodes (pcat p q) ->  *)
    (*   (u \in nodes p) = (idx (pcat p q) u <= idx (pcat p q) z). *)
    (* Admitted. *)

    Lemma idx_catL u v : u \in tail q -> v \in tail q ->
      (idx (pcat p q) u < idx (pcat p q) v) = (idx q u < idx q v).
    Proof.
      move => A B. rewrite /idx /nodes -!cat_cons !index_cat.
      have C : (u \notin x :: val p). 
      { apply/negP. apply: disjointE A. by rewrite disjoint_sym. }
      have D : (v \notin x :: val p). 
      { apply/negP. apply: disjointE B. by rewrite disjoint_sym. }
      rewrite (negbTE C) (negbTE D) ltn_add2l /=.
      have -> : z == u = false. apply: contraTF C => /eqP<-. by rewrite negbK nodes_end.
      have -> : z == v = false. apply: contraTF D => /eqP<-. by rewrite negbK nodes_end.
      by rewrite ltnS.
    Qed.

    Lemma idx_nLR u : u \in nodes (pcat p q) -> 
      idx (pcat p q) z < idx (pcat p q) u -> u \notin nodes p /\ u \in tail q.
    Admitted.
  
  End IDX.

  Lemma CP_triangle_avoid' x' y' (x y z: link_graph) : 
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
    case: (idx_nLR D y_in_p) => // Y1 Y2.
    (case: (idx_nLR D z_in_p); first by apply: ltn_trans y_lt_z) => Z1 Z2.
    case/(isplitP (G:=G) irr_p2) def_p1 : {1}p2 / (tailW Z2) => [p21 p22 irr21 irr22 D2]. subst.
    have Hy' : y \notin tail p22.
    { rewrite (idxR D2) ?tailW //. rewrite -(idx_catL D Z2 Y2). by rewrite -leqNgt ltnW. }
    have/cpPn' [q q1 q2] : y \notin cp x z. 
    { case/andP : zx => _ sub. apply/negP. rewrite cp_sym. move/(subsetP sub). 
      rewrite !inE. by case/orP => /eqP ?;subst; rewrite sg_irrefl in xy yz. }
    apply: (cpNI' (p := pcat p1 (pcat q p22))). 
    by rewrite mem_pcat mem_pcatT (negbTE Hy') (negbTE Y1) (negbTE q2).
  Qed.
    

  Lemma CP_triangle (x y z: CP_) : 
    x -- y -> y -- z -> z -- x -> 
    exists x' y' z':G, 
      [/\ x' \in U, y' \in U & z' \in U] /\
      [/\ [set val x;val y] \subset cp x' y',
         [set val y;val z] \subset cp y' z'&
         [set val z;val x] \subset cp z' x'].
  Proof.
    move => xy yz zx.
    move: (CP_base_ x y) => [x'] [y'] [Ux Uy]. rewrite subUset !sub1set => /andP[cp_x cp_y].
    have cp_z : val z \notin cp x' y' by apply: CP_triangle_avoid (cp_x) (cp_y). 
    case/cpPn : cp_z => p pth_p av_z. 
    have [z1 [z2 [Uz1 Uz2 cp_z]]] : exists z1 z2, [/\ z1 \in U, z2 \in U & val z \in cp z1 z2].
    { case: (CP_base_ z z) => z1 [z2] [? ?]. rewrite setUid sub1set => ?. by exists z1; exists z2. }

    
    
    (* TODO: Obtain x' and y' from x -- y and x'' -- z' from x -- z,
    show that x' can play the role of x'', and then show y,z in [cp y'z']
    (see notes)  *)
  Admitted.
    
End CheckPoints.
