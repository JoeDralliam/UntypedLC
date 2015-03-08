Require Import Arith.

Inductive term : Set :=
| TVar : nat -> term
| TApp : term -> term -> term
| TAbstr : term -> term.

(*
Inductive appears_free_in (x : identifier) : term -> Prop :=
| afi_var : appears_free_in x (TVar x)
| afi_app1 : forall (t1 t2 : term),
               appears_free_in x t1 -> appears_free_in x (TApp t1 t2)
| afi_app2 : forall (t1 t2 : term),
               appears_free_in x t2 -> appears_free_in x (TApp t1 t2)
| afi_abstr : forall (y : identifier) (t : term),
                x <> y -> appears_free_in x t -> appears_free_in x (TAbstr y t).

Inductive appears_bound_in (x : identifier) : term -> Prop :=
| abi_app1 : forall (t1 t2 : term),
               appears_bound_in x t1 -> appears_bound_in x (TApp t1 t2)
| abi_app2 : forall (t1 t2 : term),
               appears_bound_in x t2 -> appears_bound_in x (TApp t1 t2)
| abi_abstr : forall (y : identifier) (t : term),
                x <> y -> appears_bound_in x t -> appears_bound_in x (TAbstr y t)
| abi_capture : forall (t : term),
                  appears_free_in x t -> appears_bound_in x (TAbstr x t).

 *)


Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint rescope (s : term) (deep: nat) : term :=
  match s with
    | TVar k =>
      if leb deep k
      then TVar (S k)
      else TVar k
    | TApp t1 t2 => TApp (rescope t1 deep) (rescope t2 deep)
    | TAbstr t => TAbstr (rescope t (S deep))
  end.

Fixpoint subst (var : nat) (s : term) (t : term) :=
  match t with
    | TApp t1 t2 => TApp (subst var s t1) (subst var s t2)
    | TVar v =>
      match nat_compare var v with
        | Lt => TVar (pred v)
        | Eq => s
        | Gt => TVar v
      end
    | TAbstr t1 => TAbstr (subst (S var) (rescope s 0) t1)
  end

where "'[' x ':=' s ']' t" := (subst x s t).


Reserved Notation "u '-->' v" (at level 20).

Inductive beta_reduction : term -> term -> Prop :=
| b_app1 : forall (t1 t1' t2 : term),
            beta_reduction t1 t1' ->
            beta_reduction (TApp t1 t2) (TApp t1' t2)
| b_app2 : forall (t1 t2 t2' : term),
            beta_reduction t2 t2' ->
            beta_reduction (TApp t1 t2) (TApp t1 t2')
| b_abstr : forall (u u' : term),
             beta_reduction u u' ->
             beta_reduction (TAbstr u) (TAbstr u')
| b_red : forall (u : term) (v : term),
            beta_reduction (TApp (TAbstr u) v) ([0 := v]u)

where "u '-->' v" := (beta_reduction u v).


Section Confluence.
  Require Import Relation_Definitions.
  Require Import Operators_Properties.
  Require Import Relation_Operators.

  Variable A : Type.
  Variable R : relation A.
  Definition RStar := clos_refl_trans_1n A R.

  Inductive RRefl : relation A :=
  | r_refl : forall (x : A), RRefl x x
  | r_step : forall (x y : A),  R x y -> RRefl x y.

  Definition confluent_from (x : A) : Prop :=
    forall (y z : A),
      RStar x y -> RStar x z ->
      exists (w : A), RStar y w /\ RStar z w.


  Definition confluent : Prop :=
    forall (x : A), confluent_from x.

  Definition locally_confluent : Prop :=
    forall (x y z : A),
      R x y -> R x z ->
      exists (w : A), RStar y w /\ RStar z w.

  Definition strongly_confluent : Prop :=
    forall (x y z : A),
      R x y -> R x z ->
      exists (w : A), RRefl y w /\ RRefl z w.

  Definition church_rosser : Prop :=
    forall (x y : A),
      (clos_refl_sym_trans_1n A R) x y
      <-> exists (w : A), RStar x w /\ RStar y w.


  Inductive terminating_from (x : A) :=
  | tf_imm : (forall (y : A),  ~(R x y)) -> terminating_from x
  | tf_step : (forall (y : A),  R x y -> terminating_from y) -> terminating_from x.

  Definition terminating := forall (x : A), terminating_from x.

  Lemma confluence_implies_locally :
    confluent -> locally_confluent.
  Proof. unfold confluent, locally_confluent.
         intros H x y z H1 H2.
         apply (clos_rt1n_step A R x y) in H1.
         apply (clos_rt1n_step A R x z) in H2.
         apply (H x y z H1 H2).
  Qed.

  Lemma end_of : forall (x : A),
                   (forall (y : A),  ~(R x y)) -> forall (y : A),  RStar x y -> x = y.
  Proof. intros x H y G.
         induction G.
         - reflexivity.
         - contradict (H y H0).
  Qed.

  Lemma rstar_trans : forall x y z, RStar x y -> RStar y z -> RStar x z.
  Proof. intros x y z Hxy Hyz.
         unfold RStar. rewrite <- clos_rt_rt1n_iff.
         apply rt_trans with y ; apply clos_rt_rt1n_iff ; assumption.
  Qed.

  Lemma confluence_trans :
    forall (x y : A), RStar x y -> confluent_from x -> confluent_from y.
  Proof. intros x y HR Hc z1 z2 HR1 HR2.
         apply Hc ; apply rstar_trans with y ; auto.
  Qed.


  Lemma loc_confl_termination :
    locally_confluent ->
    forall (x : A),
      (forall (y : A), R x y -> confluent_from y) -> confluent_from x.
  Proof. unfold locally_confluent.
    intros lc x Hi y z Hy Hz.
    destruct Hy ; destruct Hz.
    - exists x. split ; apply rt1n_refl.
    - exists z. split ; [apply rt1n_trans with y ; assumption | apply rt1n_refl].
    - exists z0. split ; [apply rt1n_refl | apply rt1n_trans with y ; assumption].
    - elim (lc x y y0 H H0). intros t [s0 s].
      elim (Hi y H z0 t). elim (Hi y0 H0 z t).
      intros x0 [Hzx0 Ht0] x1 [Hzx1 Htx1].
      assert (confluent_from t). apply confluence_trans with y. assumption. auto.
      elim (H1 x0 x1). intros x2 [Hx0x2 Hx1x2].
      exists x2.
      split.
      apply rstar_trans with x1 ; assumption.
      apply rstar_trans with x0 ; assumption.
      assumption. assumption. assumption. assumption. assumption. assumption.
  Qed.

  Theorem newmann :
    terminating -> locally_confluent -> confluent.
  Proof. unfold terminating, locally_confluent, confluent.
         intros term lc x.
         induction (term x) ; apply loc_confl_termination ; try assumption.
         - intros y Hr. contradict (n y Hr).
  Qed.

  Lemma rt_implies_srt : forall (x y : A),
                           RStar x y -> (clos_refl_sym_trans_1n A R x y).
  Proof. intros x y H. induction H.
         - apply rst1n_refl.
         - apply rst1n_trans with y ; [left | idtac] ; assumption.
  Qed.

  Theorem cr :
    church_rosser <-> confluent.
  Proof. unfold church_rosser, confluent.
    split.
    - intros cr. intros x y z Hy Hz. apply cr.
      apply clos_rst1n_trans with x ; [apply clos_rst1n_sym | idtac] ; apply rt_implies_srt ; assumption.
    - intros conf x y. split.
      + intros rst. induction rst.
        * exists x. split ; apply rt1n_refl.
        * inversion IHrst as [w [Hyw Hzw]]. elim H.
          intros Hxy.
          exists w. split ; [apply rt1n_trans with y | idtac] ; assumption.
          intros Hyx. apply (clos_rt1n_step A R y x) in Hyx.
          elim (conf y x w Hyx Hyw). intros s [Hxs Hws].
          exists s. split ; [idtac | apply rstar_trans with w] ; assumption.
      + intros H. inversion H as [w [Hxw Hyw]].
        apply clos_rst1n_trans with w ; [ idtac | apply clos_rst1n_sym] ; apply rt_implies_srt ; assumption.
  Qed.

  Lemma refl_implies_rt :
    forall (x y : A),  RRefl x y -> RStar x y.
  Proof.
    intros x y H. induction H. apply rt1n_refl. apply clos_rt1n_step. assumption.
  Qed.

  Inductive path_of_length : nat -> A -> A -> Prop :=
  | pl_refl : forall (x : A),  path_of_length 0 x x
  | pl_trans : forall (x y z : A) (n : nat),
                 R x y ->
                 path_of_length n y z ->
                 path_of_length (S n) x z.

  Lemma exists_length :
    forall (x y : A),  RStar x y -> exists n, path_of_length n x y.
  Proof.
    intros x y H. induction H.
    - exists 0. apply pl_refl.
    - inversion IHclos_refl_trans_1n as [n Hn].
      exists (S n). apply pl_trans with y ; assumption.
  Qed.

  Lemma length_relates :
    forall (n : nat) (x y : A),  path_of_length n x y -> RStar x y.
  Proof.
    intros n x y Hn. induction Hn.
    - apply rt1n_refl.
    - apply rt1n_trans with y ; assumption.
  Qed.

  Lemma strongly_one_sided :
    strongly_confluent ->
    forall (x y z : A),
      R x y -> RStar x z ->
      exists w,  RStar y w /\ RStar z w.
  Proof.
    intros sc x y z Hxy Hxz. generalize dependent y.
    induction Hxz as [| x z0 z ].
    - intros y Hxy.
      exists y. split. apply rt1n_refl. apply clos_rt1n_step. assumption.
    - intros y Hxy.
      elim (sc x y z0 Hxy H).
      intros w [Hyw Hz0w].
      inversion Hz0w ; subst.
      + exists z. split.
       * apply rstar_trans with w ;
           [apply refl_implies_rt | idtac] ; assumption.
       * apply rt1n_refl.
      + apply IHHxz in H0. elim H0.
        intros t [Hwt Hzt]. exists t.
        split.
        apply rstar_trans with w ; [apply refl_implies_rt | idtac] ; assumption.
        assumption.
  Qed.

Lemma strongly_length :
    strongly_confluent ->
    forall (n : nat) (x y z : A),
      path_of_length n x y -> RStar x z ->
      exists w, RStar y w /\ RStar z w.
  Proof.
    intros sc n. induction n.
    - intros x y z Hxy Hxz.
      inversion Hxy ; subst ; clear Hxy.
      exists z. split. assumption. apply rt1n_refl.
    - intros x y z Hxy Hxz.
      inversion Hxy ; subst ; clear Hxy.
      elim (strongly_one_sided sc x y0 z H0 Hxz).
      intros u [Hy0u Hzu].
      elim (IHn y0 y u H1 Hy0u).
      intros v [Hyv Huv].
      exists v. split. assumption. apply rstar_trans with u ; assumption.
  Qed.

  Theorem strongly_confluent_confluent :
    strongly_confluent -> confluent.
  Proof.
    unfold strongly_confluent, confluent.
    intros sc x y z Hy Hz.
    elim (exists_length x y Hy).
    intros n Hnxy.
    apply strongly_length with (n:=n) (x:=x) ; assumption.
  Qed.
End Confluence.

Require Import Operators_Properties.
Require Import Relation_Operators.

Definition beta_star :=
  RStar term beta_reduction.

Notation "u '-->*' v" := (beta_star u v) (at level 20).


Lemma b_app1_star :
  forall (t1 t1' t2: term),
    t1 -->* t1' ->
    (TApp t1 t2) -->* (TApp t1' t2).
Proof.
  intros t1 t1' t2 H1. induction H1.
  - apply rt1n_refl.
  - apply rt1n_trans with (TApp y t2) ; [constructor | idtac] ; assumption.
Qed.

Lemma b_app2_star :
  forall (t1 t2 t2': term),
    t2 -->* t2' ->
    (TApp t1 t2) -->* (TApp t1 t2').
Proof.
  intros t1 t2 t2' H2. induction H2.
  - apply rt1n_refl.
  - apply rt1n_trans with (TApp t1 y) ; [constructor | idtac] ; assumption.
Qed.

Lemma b_abstr_star :
  forall (t1 t1': term),
    t1 -->* t1' ->
    (TAbstr t1) -->* (TAbstr t1').
Proof.
  intros t1 t1' H1. induction H1.
  - apply rt1n_refl.
  - apply rt1n_trans with (TAbstr y) ; [constructor | idtac] ; assumption.
Qed.

Module Parallel.
  Require Import Omega.
  Hint Resolve nat_compare_eq_iff.
  Hint Resolve nat_compare_lt.
  Hint Resolve nat_compare_gt.
  Hint Resolve nat_compare_Lt_lt.
  Hint Resolve nat_compare_Gt_gt.


  Reserved Notation "u '==>' v" (at level 20).

  Inductive par_reduction : term -> term -> Prop :=
  | p_app : forall (t1 t1' t2 t2' : term),
             t1 ==> t1' ->
             t2 ==> t2' ->
             (TApp t1 t2) ==> (TApp t1' t2')
  | p_id : forall (u : term),
             u ==> u
  | p_abstr : forall (u u' : term),
               u ==> u' ->
               (TAbstr u) ==> (TAbstr u')
  | p_red : forall (u u' : term) (v v' : term),
             u ==> u' ->
             v ==> v' ->
             (TApp (TAbstr u) v) ==> ([0 := v']u')
  where "u '==>' v" := (par_reduction u v).

  Hint Constructors par_reduction.

  Lemma beta_implies_par :
    forall (a b : term),
      a --> b -> a ==> b.
  Proof.
    intros a b H. induction H.
    - apply p_app. assumption. apply p_id.
    - apply p_app. apply p_id. assumption.
    - apply p_abstr. assumption.
    - apply p_red ; apply p_id.
  Qed.

  Lemma par_implies_beta_star :
    forall (a b : term),
      a ==> b -> a -->* b.
  Proof.
    intros a b H. induction H.
    - apply rstar_trans with (TApp t1' t2) ;
      [apply b_app1_star | apply b_app2_star] ; assumption.
    - apply rt1n_refl.
    - apply b_abstr_star ; assumption.
    - apply rstar_trans with (TApp (TAbstr u') v').
      apply rstar_trans with (TApp (TAbstr u') v).
      apply b_app1_star. apply b_abstr_star. assumption.
      apply b_app2_star. assumption.
      apply clos_rt1n_step. apply b_red.
  Qed.

  Lemma par_refl :
    forall (u v : term),
      RRefl term par_reduction u v -> par_reduction u v.
  Proof.
    intros u v Hrefl.
    induction Hrefl.
    - apply p_id.
    - assumption.
  Qed.

  Lemma subs_rescope :
    forall (k : nat) (u v : term),
      [k := v](rescope u k) = u.
  Proof.
    intros k u. generalize dependent k.
    induction u ; intros k v.

    - simpl.
      destruct (leb k n) eqn:Eq.
      + assert (nat_compare k (S n) = Lt).
        apply nat_compare_lt. apply le_n_S. apply leb_complete. assumption.
        simpl. rewrite H. reflexivity.
      + assert (nat_compare k n = Gt).
        apply nat_compare_gt. apply leb_complete_conv. assumption.
        simpl. rewrite H. reflexivity.
    - simpl. rewrite IHu1. rewrite IHu2. reflexivity.
    - simpl. rewrite IHu. reflexivity.
  Qed.

  Lemma rescope_comm :
    forall (v : term) (j k : nat),
      k <= j -> rescope (rescope v j) k = rescope (rescope v k) (S j).
  Proof with auto.
    intros v.
    induction v ; intros j k Hjk.
    - unfold rescope.
      destruct (leb j n) eqn:E1.
      + assert (j <= n). apply le_S_n. apply leb_complete. assumption.
        assert (leb j n = true). apply leb_correct. assumption.
        assert (leb k n = true). apply leb_correct. omega.
        assert (leb k (S n) = true). apply leb_correct. omega.
        assert (leb (S j) (S n) = true). apply leb_correct. omega.
        simpl. rewrite H1. rewrite H2. rewrite H3. reflexivity.
      + destruct (leb k n).
        * assert (j > n). apply leb_complete_conv. assumption.
          assert (leb (S j) (S n) = false). apply leb_correct_conv. omega.
          rewrite H0. reflexivity.
        * assert (j > n). apply leb_complete_conv. assumption.
          assert (leb (S j) n = false). apply leb_correct_conv. omega.
          rewrite H0. reflexivity.
    - simpl. rewrite IHv1... rewrite IHv2...
    - simpl. rewrite IHv... omega.
  Qed.

  Lemma rescope_factorization :
    forall (k : nat) (u v : term) (d : nat),
      d <= k ->
      ([S k := rescope v d]rescope u d) = rescope ([k := v]u) d.
  Proof with auto.
    intros k u. generalize dependent k.
    induction u ; intros k v d Hdk.
    - simpl.
      destruct (nat_compare k n) eqn:E.
      + assert (k = n). apply nat_compare_eq_iff. assumption. subst.
        replace (leb d n) with true. simpl. rewrite E. reflexivity.
        symmetry. apply leb_correct. assumption.
      + simpl.
        assert (k < n). apply nat_compare_lt. assumption.
        replace (leb d (pred n)) with true.
        replace (leb d n) with true.
        simpl. rewrite E.
        rewrite <- S_pred with n k. reflexivity.
        assumption.
        symmetry. apply leb_correct. omega.
        symmetry. apply leb_correct. omega.
      + simpl. destruct (leb d n) ; unfold subst.
        * rewrite nat_compare_S. rewrite E. reflexivity.
        * assert (nat_compare (S k) n = Gt).
          apply nat_compare_gt. apply le_S. apply nat_compare_Gt_gt. assumption.
          rewrite H. reflexivity.
    - simpl. rewrite IHu1... rewrite IHu2...
    - simpl. rewrite rescope_comm. rewrite IHu. reflexivity.
      omega. omega.
  Qed.

  Lemma rescope_factorization' :
    forall (k : nat) (u v : term) (d : nat),
      k <= d ->
      ([k := rescope v d]rescope u (S d)) = rescope ([k := v]u) d.
  Proof with auto.
    intros k u. generalize dependent k.
    induction u ; intros k v d Hkd.
    - destruct (nat_compare k n) eqn:E.
      + assert (k = n). apply nat_compare_eq. assumption. subst.
        assert (leb (S d) n = false). apply leb_correct_conv. omega.
        unfold rescope. rewrite H. simpl. rewrite E. reflexivity.
      + assert (k < n). apply nat_compare_lt. assumption.
        unfold rescope.
        destruct (leb (S d) n) eqn:Eq.
        * simpl. rewrite E.
          assert (nat_compare k (S n) = Lt). apply nat_compare_lt. omega.
          assert (S d <= n). apply leb_complete. assumption.
          assert (leb d (pred n) = true). apply leb_correct. omega.
          rewrite H0. rewrite H2. replace (S (pred n)) with n. reflexivity.
          omega.
        * fold rescope. unfold subst. rewrite E.
          unfold rescope.
          assert (n < (S d)). apply leb_complete_conv. assumption.
          assert (leb d (pred n) = false). apply leb_correct_conv. omega.
          rewrite H1. reflexivity.
      + assert (k > n). apply nat_compare_gt. assumption.
        unfold rescope, subst. rewrite E.
        assert (leb d n = false). apply leb_correct_conv. omega.
        assert (leb (S d) n = false). apply leb_correct_conv. omega.
        rewrite H0. rewrite H1. rewrite E. reflexivity.
    - simpl. rewrite IHu1... rewrite IHu2...
    - simpl. rewrite rescope_comm. rewrite IHu...
      omega. omega.
  Qed.

  Lemma subst_commutator :
    forall (k j: nat) (v1 v2 : term) (u : term),
      j <= k -> [k := v1]([j := v2]u) = [j := [k := v1]v2]([S k := rescope v1 j]u).
  Proof with auto.
    intros k j v1 v2 u.
    generalize dependent v2. generalize dependent v1. generalize dependent j.
    generalize dependent k.
    induction u ; intros k j v1 v2 Hjk.
    - unfold subst. destruct (nat_compare (S k) n) eqn:E1.
      + fold subst. rewrite subs_rescope.
        assert (S k = n). apply nat_compare_eq_iff. assumption.
        subst.
        assert (nat_compare j (S k) = Lt). apply nat_compare_lt. omega.
        rewrite H. simpl. rewrite <- nat_compare_S. rewrite E1. reflexivity.
      + fold subst.
        assert ((S k) < n). apply nat_compare_lt. assumption.
        assert (nat_compare j (pred n) = Lt). apply nat_compare_lt. omega.
        assert (nat_compare j n = Lt). apply nat_compare_lt. omega.
        rewrite H0. rewrite H1. simpl.
        assert (nat_compare k (pred n) = Lt). apply nat_compare_lt. omega.
        rewrite H2. reflexivity.
      + fold subst. assert (S k > n). apply nat_compare_gt. assumption.
        destruct (nat_compare j n) eqn:E2...
        * assert (j < n). apply nat_compare_lt. assumption.
          simpl.
          assert (nat_compare k (pred n) = Gt). apply nat_compare_gt. omega.
          rewrite H1. reflexivity.
        * assert (n < j). apply nat_compare_gt. assumption. simpl.
          assert (nat_compare k n = Gt). apply nat_compare_gt. omega.
          rewrite H1. reflexivity.
    - simpl. rewrite IHu1... rewrite IHu2...
    - simpl. rewrite IHu... rewrite rescope_factorization...
      pattern (rescope (rescope v1 j) 0). rewrite rescope_comm.
      reflexivity. omega. omega. omega.
  Qed.


  Lemma rescope_par :
    forall (v v' : term) (k : nat),
      v ==> v' -> rescope v k ==> rescope v' k.
  Proof with auto.
    intros v v' k Hv. generalize dependent k.
    induction Hv ; intros k ; simpl...
    - rewrite <- rescope_factorization'. apply p_red... omega.
  Qed.

  Lemma subs_par_id :
    forall u (v v' : term) (k : nat),
    par_reduction v v' ->
    par_reduction ([k := v]u) ([k := v']u).
  Proof with auto.
    intros u. induction u ; intros v v' k Hv.
    - unfold subst.
      destruct (nat_compare k n) ; subst ; try (apply p_id)...
    - simpl. apply p_app...
    - simpl. apply p_abstr... apply IHu. apply rescope_par...
  Qed.

  Lemma par_abstr_inv :
    forall (u v : term),
      TAbstr u ==> v -> exists u', u ==> u' /\ v = TAbstr u'.
  Proof.
    intros u v H.
    inversion H ; subst.
    - exists u. split ; auto.
    - exists u'. split ; auto.
  Qed.

  Lemma subst_par :
    forall (u u' : term) (v v' : term) (k : nat),
      par_reduction u u' ->
      par_reduction v v' ->
      par_reduction ([k := v]u) ([k := v']u').
  Proof with auto.
    intros u u' v v' k Hu.
    generalize dependent k. generalize dependent v'. generalize dependent v.
    induction Hu ; intros w w' k Hv.
    - simpl. apply p_app...
    - simpl. apply subs_par_id...
    - simpl. apply p_abstr... apply IHHu. apply rescope_par...
    - simpl. rewrite subst_commutator. apply p_red...
      apply IHHu1. apply rescope_par... omega.
  Qed.

  Lemma par_strongly_confluent :
    strongly_confluent term par_reduction.
  Proof with auto.
    intros x y z Hxy. generalize dependent z.
    induction Hxy ; intros z Hxz.
    - inversion Hxz ; subst.
      + elim (IHHxy1 t1'0 H1).
        elim (IHHxy2 t2'0 H3).
        intros w2 [H2' H2'0] w1 [H1' H1'0].
        exists (TApp w1 w2).
        split ; apply r_step ; (apply p_app ; apply par_refl ; assumption).
      + exists (TApp t1' t2').
        split ; apply r_step ; [apply p_id | apply p_app ; assumption].
      + elim (IHHxy1 (TAbstr u')).
        elim (IHHxy2 v' H3).
        intros w2 [H2' H2'0] w1 [H1' H1'0].
        apply par_refl in H1'0.
        elim (par_abstr_inv u' w1 H1'0).
        intros w1' [Huw1' Hw1w1']. subst.
        exists ([0 := w2]w1').
        elim (par_abstr_inv u t1' Hxy1).
        intros s [Hus Ht1's]. subst.
        apply par_refl in H2'.
        apply par_refl in H2'0.
        apply par_refl in H1'. inversion H1'. subst.
        * split ; apply r_step.
          apply p_red...
          apply subst_par...
        * split ; apply r_step.
          apply p_red...
          apply subst_par...
        * constructor...
   - exists z. split ; apply r_step...
   - elim (par_abstr_inv u z Hxz).
     intros v [Huv Hv]. subst.
     elim (IHHxy v Huv).
     intros w [Hu'x Hvx].
     exists (TAbstr w).
     apply par_refl in Hu'x.
     apply par_refl in Hvx.
     split ; apply r_step...
   - inversion Hxz ; subst.
     + elim (par_abstr_inv u t1' H1).
       intros x [Hux Ht1'x]. subst.
       elim (IHHxy2 t2' H3).
       elim (IHHxy1 x Hux).
       intros u0 [Hu'u0 Hxu0] v0 [Hv'v0 Ht2'v0].
       apply par_refl in Hu'u0.
       apply par_refl in Hxu0.
       apply par_refl in Hv'v0.
       apply par_refl in Ht2'v0.
       exists ([0 := v0]u0).
       split ; apply r_step...
       apply subst_par...
     + exists ([0 := v']u').
       split ; apply r_step...
     + elim (IHHxy2 v'0 H3).
       elim (IHHxy1 u'0 H1).
       intros u0 [Hu'u0 Hu'0u0] v0 [Hv'v0 Hv'0v0].
       apply par_refl in Hu'u0.
       apply par_refl in Hu'0u0.
       apply par_refl in Hv'v0.
       apply par_refl in Hv'0v0.
       exists ([0 := v0]u0).
       split ; apply r_step ; apply subst_par...
  Qed.

End Parallel.