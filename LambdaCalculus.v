Require Import Arith.

Function iterate {X : Type} (n : nat) (f : X -> X) (x0 : X) :=
  match n with
    | 0 => x0
    | S n => f (iterate n f x0)
  end.


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

  Definition par_star :=
    RStar term par_reduction.


  Notation "u '==>*' v" := (par_star u v) (at level 20).


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

  Lemma par_star_equiv_beta_star :
    forall (a b : term),
      a ==>* b <-> a -->* b.
  Proof.
    intros a b.
    split.
    - intros H. induction H.
      + apply rt1n_refl.
      + apply rstar_trans with y. apply par_implies_beta_star. assumption. assumption.
    - intros H. induction H.
      + apply rt1n_refl.
      + apply rt1n_trans with y. apply beta_implies_par. assumption. assumption.
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

  Theorem par_confluent : confluent term par_reduction.
  Proof. apply strongly_confluent_confluent.
         apply par_strongly_confluent.
  Qed.

End Parallel.




Theorem beta_confluent :
  confluent term beta_reduction.
Proof.
  intros x y z Hy Hz.
  apply Parallel.par_star_equiv_beta_star in Hy.
  apply Parallel.par_star_equiv_beta_star in Hz.
  elim (Parallel.par_confluent x y z Hy Hz).
  intros w [Hyw Hzw].
  apply Parallel.par_star_equiv_beta_star in Hyw.
  apply Parallel.par_star_equiv_beta_star in Hzw.
  exists w. auto.
Qed.


Lemma rescope_app_congr :
  forall (s u1 u2 : term) (n : nat),
    rescope s n = TApp u1 u2 ->
    exists (s1 : term),
      exists (s2 : term),
        s = TApp s1 s2 /\ rescope s1 n = u1 /\ rescope s2 n = u2.
Proof.
  intros s u1 u2 n H.
  destruct s.
  - simpl in H. destruct (leb n n0) ; inversion H.
  - simpl in H. inversion H.
    exists s1. exists s2. split ; [idtac | split] ; reflexivity.
  - simpl in H. inversion H.
Qed.


Lemma rescope_abstr_congr :
  forall (s u1 : term) (n : nat),
    rescope s n = TAbstr u1 ->
    exists (s1 : term), s = TAbstr s1 /\ rescope s1 (S n) = u1.
Proof.
  intros s u1 n H.
  destruct s ; simpl in H.
  - destruct (leb n n0) ; inversion H.
  - inversion H.
  - inversion H. exists s. split ; reflexivity.
Qed.

Lemma rescope_reduction :
  forall (u w : term) (n : nat),
    rescope u n --> w ->
    exists (v : term), w = rescope v n /\ u --> v.
Proof.
  intros u w n Hw.
  remember (rescope u n). generalize dependent n. generalize u.
  induction Hw.
  - intros s n Heq.
    symmetry in Heq.
    assert (G := rescope_app_congr s t1 t2 n Heq).
    destruct G as [s1 [s2 [Geq [Gu1 Gu2]]]].
    symmetry in Gu1.
    destruct (IHHw s1 n Gu1) as [v1 [K1 Kr]].
    exists (TApp v1 s2). split.
    simpl. rewrite Gu2. rewrite K1. reflexivity.
    rewrite Geq. apply b_app1. assumption.
  - intros s n Heq.
    symmetry in Heq.
    assert (G := rescope_app_congr s t1 t2 n Heq).
    destruct G as [s1 [s2 [Geq [Gu1 Gu2]]]].
    symmetry in Gu2.
    destruct (IHHw s2 n Gu2) as [v2 [K2 Kr]].
    exists (TApp s1 v2). split.
    simpl. rewrite Gu1. rewrite K2. reflexivity.
    rewrite Geq. apply b_app2. assumption.
  - intros s n Heq.
    symmetry in Heq.
    assert (G := rescope_abstr_congr s u0 n Heq).
    destruct G as [s1 [Geq Gu0]].
    symmetry in Gu0.
    destruct (IHHw s1 (S n) Gu0) as [v [K0 Kr]].
    exists (TAbstr v). split.
    * simpl. rewrite K0. reflexivity.
    * rewrite Geq. apply b_abstr. assumption.
  - intros u1 n Heq.
    symmetry in Heq.
    destruct (rescope_app_congr u1 (TAbstr u0) v n Heq)
      as [abs1 [arg1 [Geq [G1 G2]]]].
    destruct (rescope_abstr_congr _ _ _ G1) as [abs2 [Keq K2]].
    rewrite Geq. exists ([0 := arg1]abs2).
    rewrite <- Parallel.rescope_factorization'.
    rewrite G2. rewrite K2. split. reflexivity. rewrite Keq.
    apply b_red. omega.
Qed.

Lemma rescope_congr :
  forall (u v : term) (n : nat), u --> v -> (rescope u n) --> (rescope v n).
Proof.
  intros u v n H. generalize dependent n.
  induction H.
  - intros n. simpl. apply b_app1. apply IHbeta_reduction.
  - intros n. simpl. apply b_app2. apply IHbeta_reduction.
  - intros n. simpl. apply b_abstr. apply IHbeta_reduction.
  - intros n. simpl. rewrite <- Parallel.rescope_factorization'.
    apply b_red. omega.
Qed.


Lemma subst_reduction :
  forall (u u' v : term) (n : nat), u --> u' -> [n := v]u --> [n := v]u'.
Proof.
  intros u. induction u.
  - intros u' v k Hcontra. inversion Hcontra.
  - intros u' v k H. inversion H ; subst.
    + simpl. apply b_app1. apply IHu1. assumption.
    + simpl. apply b_app2. apply IHu2. assumption.
    + rewrite Parallel.subst_commutator. simpl.
      apply b_red. omega.
  - intros u' v n Hu. inversion Hu. simpl.
    apply b_abstr. apply IHu. assumption.
Qed.

Lemma subst_abstr_inversion :
  forall (u v : term) (p k : nat),
    TAbstr u = [p := TVar k]v -> exists (w : term),  v = TAbstr w.
Proof.
  intros u v. generalize dependent u.
  induction v ; simpl.
  - intros u p s contra. destruct (nat_compare p n) ; inversion contra.
  - intros u p s contra. inversion contra.
  - intros u p k H. exists v. reflexivity.
Qed.


Lemma subst_reduction_inversion :
  forall (u v : term) (p n : nat),
    [p := TVar n]u --> v ->
    exists (u' : term), v = [p := TVar n]u' /\ u --> u'.
Proof.
  intros u. induction u ; simpl.
  - intros v p k Hcontra. destruct (nat_compare p n) ; inversion Hcontra.
  - intros v p k H. inversion H ; subst ; simpl.
    + destruct (IHu1 _ _ _ H3) as [w [Hw Hr]].
      exists (TApp w u2). split. rewrite Hw. reflexivity.
      apply b_app1. assumption.
    + destruct (IHu2 _ _ _ H3) as [w [Hw Hr]].
      exists (TApp u1 w). split. rewrite Hw. reflexivity.
      apply b_app2. assumption.
    + destruct (subst_abstr_inversion _ _ _ _ H1) as [w Hw].
      exists ([0 := u2]w). rewrite Parallel.subst_commutator.
      rewrite Hw in H1. simpl in H1. inversion H1.
      split. reflexivity. rewrite Hw. apply b_red. omega.
  - intros v p k H. inversion H ; subst ; simpl.
    destruct (IHu _ _ _ H1) as [w [Hw Hr]].
    exists (TAbstr w). rewrite Hw. split. reflexivity. apply b_abstr. assumption.
Qed.



(*
Module LeftmostUppermost.
  Require Import List.
  Open Scope list_scope.

  Inductive as_head_term : Set :=
  | ht_normal : forall (i : nat), as_head_term
  | ht_redex : forall (u v : term), as_head_term.

  Function head_term_value (t : as_head_term) :=
    match t with
      | ht_normal i => TVar i
      | ht_redex u v => TApp (TAbstr u) v
    end.

  Fixpoint head_abstractions term :=
    match term with
      | TVar _ | TApp _ _ => 0
      | TAbstr u => S (head_abstractions u)
    end.

  Fixpoint head_term term :=
    match term with
      | TVar i => ht_normal i
      | TApp u v =>
        match u with
          | TAbstr u' => ht_redex u' v
          | _ => head_term u
        end
      | TAbstr u => head_term u
    end.

  Fixpoint other_terms term :=
    match term with
      | TVar i => nil
      | TApp u v =>
        match u with
          | TAbstr _ => nil
          | _ => other_terms u ++ (v :: nil)
        end
      | TAbstr u => other_terms u
    end.

  Fixpoint all_terms term :=
    match term with
      | TVar i => (TVar i :: nil)
      | TApp u v =>
        match u with
          | TAbstr _ => u :: v :: nil
          | _ => all_terms u ++ (v :: nil)
        end
      | TAbstr u => all_terms u
    end.

 Function term_of_simili_head_form nabs t ot :=
   iterate nabs TAbstr (fold_left TApp ot t).

 Function term_of_head_form nabs ht ot :=
   term_of_simili_head_form nabs (head_term_value ht) ot.



  Lemma head_term_app_app :
    forall (u v w : term),
      head_term (TApp (TApp u v) w) = head_term (TApp u v).
  Proof. reflexivity. Qed.

  Lemma other_terms_app_app :
    forall (u v w : term),
      other_terms (TApp (TApp u v) w) = other_terms (TApp u v) ++ (w :: nil).
  Proof. reflexivity. Qed.

  Lemma term_of_simili_hf_app :
    forall (l : list term) (t : term) (h : term),
      term_of_simili_head_form 0 h (l ++ (t :: nil)) =
      TApp (term_of_simili_head_form 0 h l) t.
  Proof.
    intros l t h. induction l.
    - reflexivity.
    - unfold term_of_simili_head_form. apply fold_left_app.
  Qed.

  Lemma term_of_hf_app :
    forall (l : list term) (t : term) (h : as_head_term),
      term_of_head_form 0 h (l ++ (t :: nil)) =
      TApp (term_of_head_form 0 h l) t.
  Proof.
    intros l t h.
    unfold term_of_head_form. apply term_of_simili_hf_app.
  Qed.


  Lemma term_hf_id :
    forall (u : term),
      term_of_head_form (head_abstractions u) (head_term u) (other_terms u) = u.
  Proof.
    intros u. induction u.
    - unfold term_of_head_form. reflexivity.
    - generalize dependent u2. destruct u1.
      + reflexivity.
      + intros u2 IHu2.
        rewrite head_term_app_app.
        rewrite other_terms_app_app.
        simpl (head_abstractions _).
        rewrite term_of_hf_app.
        simpl (head_abstractions _) in IHu1. rewrite IHu1. reflexivity.
      + intros u2 IHu2. unfold term_of_head_form. reflexivity.
    - unfold term_of_head_form. unfold term_of_simili_head_form.
      unfold term_of_head_form in IHu. unfold term_of_simili_head_form in IHu.
      simpl. rewrite IHu. reflexivity.
  Qed.

  Lemma head_abstractions_apps :
    forall (ht : term) (ot : list term),
      ot <> nil ->
      head_abstractions (fold_left TApp ot ht) = 0.
  Proof.
    intros ht ot. generalize dependent ht.
    induction ot ; intros ht Habs.
    - contradict Habs. reflexivity.
    - simpl. destruct ot.
      + reflexivity.
      + apply IHot. intros H. discriminate H.
  Qed.

  Lemma head_term_abs :
    forall (nabs : nat) (u : term),
      head_term (iterate nabs TAbstr u) = head_term u.
  Proof. intros nabs. induction nabs ; intros u.
         - reflexivity.
         - simpl. apply IHnabs.
  Qed.

  Lemma head_term_app :
    forall (ot : list term) (ht : as_head_term),
      head_term (fold_left TApp ot (head_term_value ht)) = ht.
  Proof. intros ot. induction ot using rev_ind.
         - intros ht. destruct ht ; reflexivity.
         - intros ht.
           rewrite fold_left_app. simpl. rewrite IHot.
           induction ot using rev_ind.
           + simpl. destruct ht ; reflexivity.
           + rewrite fold_left_app. reflexivity.
  Qed.

  Lemma other_terms_abs :
    forall (nabs : nat) (u : term),
      other_terms (iterate nabs TAbstr u) = other_terms u.
  Proof.
    intros nabs. induction nabs ; auto.
  Qed.

  Lemma other_terms_app :
    forall (ot : list term) (ht : as_head_term),
      other_terms (fold_left TApp ot (head_term_value ht)) = ot.
  Proof.
    induction ot using rev_ind.
    - intros ht. destruct ht ; reflexivity.
    - intros ht. rewrite fold_left_app. simpl. rewrite IHot.
      induction ot using rev_ind.
      + simpl. destruct ht ; reflexivity.
      + rewrite fold_left_app. reflexivity.
  Qed.

  Lemma hf_term_id :
    forall (nabs : nat) (ht : as_head_term) (ot : list term),
      head_abstractions (term_of_head_form nabs ht ot) = nabs /\
      head_term (term_of_head_form nabs ht ot) = ht /\
      other_terms (term_of_head_form nabs ht ot) = ot.
  Proof.
    intros nabs ht ot.
    split ; [ idtac | split].
    - induction nabs.
      + unfold term_of_head_form. simpl.
        induction ot.
        * simpl. destruct ht ; reflexivity.
        * apply head_abstractions_apps. intro H. discriminate H.
      + simpl. unfold term_of_head_form in IHnabs.
        unfold term_of_simili_head_form in IHnabs.
        rewrite IHnabs. reflexivity.
    - unfold term_of_head_form.
      unfold term_of_simili_head_form.
      rewrite head_term_abs.
      rewrite head_term_app. reflexivity.
    - unfold term_of_head_form.
      unfold term_of_simili_head_form.
      rewrite other_terms_abs.
      rewrite other_terms_app. reflexivity.
  Qed.


  Lemma hf_term_id_abs :
    forall (nabs : nat) (ht : as_head_term) (ot : list term),
      head_abstractions (term_of_head_form nabs ht ot) = nabs.
  Proof. intros nabs ht ot. destruct (hf_term_id nabs ht ot) as [H _ _].
         assumption. Qed.

  Inductive head_reduction : term -> term -> Prop :=
  | hd_beta : forall (nabs : nat) (u v : term) (ot : list term),
                head_reduction (term_of_head_form nabs (ht_redex u v) ot)
                               (term_of_simili_head_form nabs ([0 := v]u) ot).


  Definition head_reduction_star := RStar term head_reduction.

  Lemma head_reduction_app :
    forall (u1 u1' u2 : term),
      head_reduction u1 u1' -> head_abstractions u1 = 0 ->
      head_reduction (TApp u1 u2) (TApp u1' u2).
  Proof.
    intros u1 u1' u2 H Habs.
    inversion H.
    rewrite <- H0 in Habs.
    rewrite hf_term_id_abs in Habs. subst.
    rewrite <- term_of_hf_app.
    rewrite <- term_of_simili_hf_app.
    apply hd_beta.
  Qed.

  Lemma head_reduction_star_app :
    forall (u1 u1' u2 : term),
      head_reduction_star u1 u1' -> head_abstractions u1 = 0 ->
      head_reduction_star (TApp u1 u2) (TApp u1' u2).
  Proof.
    intros u1 u1' u2 H.
    induction H ; intros G.
    - apply rt1n_refl.
    - apply rt1n_trans with (TApp y u2).
      apply head_reduction_app ; assumption.


  Inductive leftmost_uppermost : term -> term -> Prop :=
  | lu_red : forall (u v w: term),
               head_reduction_star u v ->
               on_components (all_terms v) (all_terms w) ->
               leftmost_uppermost u w
  | lu_var : forall (i : nat),  leftmost_uppermost (TVar i) (TVar i)
  with on_components : list term -> list term -> Prop :=
       | oc_nil : on_components nil nil
       | oc_cons : forall (a b : term) (la lb : list term), leftmost_uppermost a b -> on_components la lb -> on_components (a :: la) (b :: lb).


  Scheme lu_on_components_ind := Induction for leftmost_uppermost Sort Prop
    with on_components_lu_ind := Induction for on_components Sort Prop.

  Combined Scheme lu_mutind from lu_on_components_ind.


  Lemma all_terms_non_empty : forall (u : term), nil <> all_terms u.
  Proof.
    intros u. induction u.
    - simpl. intros G. discriminate G.
    - simpl. destruct u1 ; try apply app_cons_not_nil.
      + intros G. discriminate G.
    - simpl. apply IHu.
  Qed.

  Lemma head_form_induction :
    forall (P : term -> Prop),
      (forall (i : nat),  P (TVar i)) ->
      (forall (u : list term) -> nabs u > 0 ->

  Lemma all_term_head_tail :
    forall (u : term),
    exists (hd : term), exists (tl : list term),
                          all_terms u = hd :: tl.
  Proof.
    intros u.
    destruct (all_terms u) eqn:Eq.
    - symmetry in Eq. exfalso.
      contradict (all_terms_non_empty u Eq).
    - exists t. exists l. reflexivity.
  Qed.

  (*
  Lemma lu_app :
    forall (u1 u1' u2 u2' : term),
      leftmost_uppermost u1 u1' -> leftmost_uppermost u2 u2' ->
      leftmost_uppermost (TApp u1 u2) (TApp u1' u2').
  Proof.
    intros u1 u1' u2 u2' G1. generalize dependent u2'. generalize dependent u2.
    induction G1.
    - intros u2 u2' G2.
      destruct (all_term_head_tail (TApp u u2)) as [x [y Hxy]].
      eapply lu_red.
      + apply rt1n_refl.
      + apply Hxy.
      +
*)
  Lemma lu_refl_n :
    forall (u : term),
      leftmost_uppermost u u.
  Proof.
    intros u.
    remember (all_terms u). generalize dependent u.
    induction l ; intros u Heql.
    - exfalso. eapply all_terms_non_empty. apply Heql.
    -
    - apply lu_var.
    -
    - destruct (all_term_head_tail (TApp u1 u2)) as [t [l H]].
      eapply lu_red.
      + apply rt1n_refl.
      + apply H.
      +

    ; intros u ; remember (all_terms u).
    - intros Hlen. inversion Hlen.
      destruct l.
      + exfalso. apply (all_terms_non_empty _ Heql).
      + simpl in H0. discriminate H0.
    - destruct u.
      + intros H. apply lu_var.
      +

End LeftmostUppermost.
 *)

Inductive StronglyNormalizing : term -> Prop :=
| SN_Step :
    forall u : term,
      (forall v : term, u --> v -> StronglyNormalizing v) ->
      StronglyNormalizing u.


Lemma sn_rescope :
  forall (u : term) (n : nat), StronglyNormalizing u <-> StronglyNormalizing (rescope u n).
Proof.

  intros u n. split.
  - intros Hu. generalize dependent n.
    induction Hu.
    intros n. apply SN_Step.
    * intros n0 G.
      apply rescope_reduction in G.
      destruct G as [v [Gr Gred]].
      rewrite Gr. apply H0. assumption.
  - intros Hu.
    remember (rescope u n). generalize dependent n. generalize u.
    induction Hu.
    intros v n Hv. apply SN_Step. intros w Hw.
    apply H0 with (rescope w n) n. rewrite Hv.
    apply rescope_congr. assumption. reflexivity.
Qed.

Lemma sn_subst :
  forall (u : term) (k n : nat),
    StronglyNormalizing u <-> StronglyNormalizing ([k := TVar n]u).
Proof.
  intros u k n. split.
  - intros Hu. generalize dependent n. generalize dependent k.
    induction Hu. intros k n. apply SN_Step.
    intros v Hv.
    destruct (subst_reduction_inversion _ _ _ _ Hv) as [w [Hw Hr]].
    rewrite Hw. apply H0. assumption.
  - intros Hu. remember ([k := TVar n]u).
    generalize dependent n. generalize dependent k. generalize dependent u.
    induction Hu. intros v k n Hv. apply SN_Step.
    intros w Hw. apply H0 with (v:=[k := TVar n]w) (k:=k) (n:=n).
    rewrite Hv. apply subst_reduction. assumption. reflexivity.
Qed.


Lemma sn_sub_app1 :
  forall (u v : term), StronglyNormalizing (TApp u v) -> StronglyNormalizing u.
Proof.
  intros u v H.
  remember (TApp u v).
  generalize dependent v. generalize dependent u.
  induction H.
  + intros u0 v0 Heq.
    apply SN_Step. intros w0 Hu0w0.
    apply H0 with (v:=TApp w0 v0) (v0:=v0).
    rewrite Heq. apply b_app1. assumption. reflexivity.
Qed.


Module SimpleType.
  Inductive ty : Set :=
  | TBase : ty
  | TArrow : ty -> ty -> ty.

  Module Context.
    Definition t := list ty.

    Definition add (c : t) (typ : ty) :=
      (typ :: c)%list.

    Definition find (c : t) (n : nat) :=
      List.nth n c.

    Inductive MapsTo : t -> nat -> ty -> Prop :=
    | MT_Head :
        forall (c : t) (T : ty),
          MapsTo (T :: c)%list 0 T
    | MT_Tail :
        forall (c : t) (n : nat) (T O : ty),
          MapsTo c n T ->
          MapsTo (O :: c)%list (S n) T.
  End Context.


  Inductive typing : Context.t -> term -> ty -> Prop :=
  | TAxiom :
      forall (gamma : Context.t) (n : nat) (T : ty),
        Context.MapsTo gamma n T -> typing gamma (TVar n) T
  | TArrowElim :
      forall (gamma : Context.t) (u v : term) (U V : ty),
        typing gamma u (TArrow U V) ->
        typing gamma v U ->
        typing gamma (TApp u v) V
  | TArrowIntro :
      forall (gamma : Context.t) (u : term) (U V : ty),
        typing (Context.add gamma U) u V ->
        typing gamma (TAbstr u) (TArrow U V).


  Inductive reductible_arrow (Pdom Papp : term->Prop) : term->Prop :=
  | RAArrow :
      forall (u : term),
        (forall (v : term),  Pdom v -> Papp (TApp u v)) ->
        reductible_arrow Pdom Papp u.

  Fixpoint reductible (T : ty) : term -> Prop :=
    match T with
      | TBase => StronglyNormalizing
      | TArrow U V => reductible_arrow (reductible U) (reductible V)
    end.

  Inductive neutral : term -> Prop :=
  | NVar : forall (n : nat), neutral (TVar n)
  | NApp : forall (u1 u2 : term), neutral (TApp u1 u2).


  Definition cr1_def (T : ty) :=
    forall (u : term),  reductible T u -> StronglyNormalizing u.

  Definition cr2_def (T : ty) :=
    forall (u u' : term),
      u --> u' ->
      reductible T u ->
      reductible T u'.

  Definition cr3_def (T : ty) :=
    forall (u : term),
      neutral u ->
      (forall (v : term),  u --> v -> reductible T v) ->
      reductible T u.

  Theorem crAll :
    forall (T : ty), cr1_def T /\ cr2_def T /\ cr3_def T.
  Proof.
    induction T ;
    unfold cr1_def, cr2_def, cr3_def ;
    (split ; [idtac | split]) ; simpl.
    - auto.
    - intros u u'. intros Huu' HSN. inversion HSN ; subst. auto.
    - intros u _ H. apply SN_Step. assumption.


    - intros u G. inversion G ; subst.
      apply sn_sub_app1 with (TVar 0).
      destruct IHT1 as [_ [_ cr31]]. unfold cr3_def in cr31.
      destruct IHT2 as [cr12 [_ _]]. unfold cr1_def in cr12.
      apply cr12. apply H. apply cr31. apply NVar.
      intros v contra. inversion contra.

    - unfold cr2_def. simpl.
      destruct IHT2 as [_ [cr22 _]]. unfold cr2_def in cr22.
      intros u u' Hr Hu. apply RAArrow.
      intros v Hv. apply cr22 with (TApp u v). apply b_app1. assumption.
      inversion Hu. subst. apply H. assumption.

    - destruct IHT1 as [cr11 [cr21 _]].
      unfold cr1_def in cr11. unfold cr2_def in cr21.
      destruct IHT2 as [_ [_ cr32]]. unfold cr3_def in cr32.
      intros u Hnu Hr.
      apply RAArrow. intros v Hv.
      assert (Hind := cr11 v Hv). induction Hind.
      apply cr32. apply NApp. intros w Hw.
      inversion Hw ; subst.
      + apply Hr in H4. inversion H4 ; subst. apply H1. assumption.
      + apply H0. assumption. apply cr21 with u0 ; assumption.
      + inversion Hnu.
  Qed.

  Lemma cr1 : forall (T : ty), cr1_def T.
  Proof. intros T. destruct (crAll T) as [H1 _]. assumption. Qed.

  Lemma cr2 : forall (T : ty), cr2_def T.
  Proof. intros T. destruct (crAll T) as [_ [H2 _]]. assumption. Qed.

  Lemma cr3 : forall (T : ty), cr3_def T.
  Proof. intros T. destruct (crAll T) as [_ [_ H3]]. assumption. Qed.

  Lemma cr3' : forall (T : ty) (n : nat),  reductible T (TVar n).
  Proof. intros T n. apply cr3. apply NVar. intros v Hcontra. inversion Hcontra. Qed.

  Lemma substRed :
    forall (u : term) (U V : ty),
      reductible V u ->
      (forall (v : term), reductible U v -> reductible V ([0 := v]u) ) ->
      reductible (TArrow U V) (TAbstr u).
  Proof.
    intros u U V Hred H.
    simpl. apply RAArrow.
    assert (Hind := cr1 V u Hred).
    induction Hind.
    intros v Hv.
    assert (Hind2 := cr1 U v Hv).
    induction Hind2.
    apply cr3. apply NApp.
    assert (Hcr2 := cr2). unfold cr2_def in Hcr2.
    intros w Hw. inversion Hw ; subst.
    - inversion H7 ; subst. apply H1 ; try assumption.
      + apply Hcr2 with u ; assumption.
      + intros z Hz.
        apply Hcr2 with ([0 := z]u). apply subst_reduction.
        assumption. apply H. assumption.
    - apply H3. assumption. apply Hcr2 with u0 ; assumption.
    - apply H. assumption.
  Qed.


  Lemma subst_rescope_red :
    forall (U : ty) (u : term),
      (forall (k n : nat), reductible U u <-> reductible U ([k := TVar n]u))
   /\ (forall (n : nat), reductible U u <-> reductible U (rescope u n)).
  Proof.
    induction U.
    - simpl. intros u. split. apply sn_subst. apply sn_rescope.
    - intros u. split.
      intros k n ; split.
      + simpl. intro H. inversion H ; subst.
        apply RAArrow. intros v.
        intro G. rewrite <- Parallel.subs_rescope with k v (TVar n).
        destruct (IHU1 v) as [_ HU1].
        destruct (IHU2 (TApp u (rescope v k))) as [HU2 _].
        simpl in HU2. rewrite <- HU2.
        apply H0. rewrite <- HU1. assumption.
      + simpl. intro H. inversion H ; subst.
        apply RAArrow. intros v G.
        destruct (IHU1 v) as [HU1 _].
        destruct (IHU2 (TApp u v)) as [HU2 _].
        rewrite HU2. simpl. apply H0.
        rewrite <- HU1. assumption.
      + intros n. split. intro H.
        remember (rescope u n).
        assert (M := H).
        apply cr1 in H. rewrite (sn_rescope _ n) in H.
        rewrite <- Heqt in H.
        generalize dependent n. generalize dependent u.
        induction H. intros v M k K.
        destruct u eqn:Eq.
        * apply cr3'.
        * apply cr3. apply NApp.
          intros w Hw.
          rewrite K in Hw. destruct (rescope_reduction _ _ _ Hw) as [o [Ho Hr]].
          apply H0 with o k. rewrite K. assumption.
          assert (Hcr2 := cr2). unfold cr2_def in Hcr2.
          apply Hcr2 with v ; assumption. assumption.
        * assert (Hcr2 := cr2). unfold cr2_def in Hcr2.
          apply substRed.

          assert (reductible U2 (TApp v (TVar k))).
          simpl in M. inversion M ; subst. apply H1. apply cr3'.
          destruct (IHU2 t) as [GU2 _].
          destruct (IHU2 (TApp v (TVar k))) as [_ HU2].
          assert (reductible U2 (rescope (TApp v (TVar k)) k)).
          apply HU2. assumption.
          simpl in H2. rewrite <- K in H2.
          assert (leb k k = true). apply leb_correct. omega.
          rewrite H3 in H2.
          rewrite GU2. apply Hcr2 with (TApp (TAbstr t) (TVar (S k))).
          apply b_red. assumption.

          intros w Hw.
          apply Hcr2 with (TApp (TAbstr t) w).
          apply b_red.
          destruct (IHU2 (TApp (rescope v k) w)) as [HU2 _].
          assert (GU2 := HU2 k k).
          simpl in GU2.
          rewrite Parallel.subs_rescope in GU2.
          rewrite <- K in GU2.
          rewrite GU2.
          simpl in M. inversion M ; subst.
          apply H1.
          destruct (IHU1 w) as [HU1 _].
          rewrite <- HU1. assumption.
        * intros H. simpl. apply RAArrow.
          intros v Hv.
          destruct (IHU2 (TApp u v)) as [_ HU2].
          rewrite HU2.
          inversion H ; subst.
          simpl. apply H0.
          destruct (IHU1 v) as [_ HU1].
          rewrite <- HU1. assumption.
  Qed.



  Lemma rescope_red :
    forall (U : ty) (u : term) (n : nat),
      reductible U u <-> reductible U (rescope u n).
  Proof.
    intros U u. destruct (subst_rescope_red U u) as [_ P]. exact P.
  Qed.

  Require Export Coq.FSets.FMapList.
  Require Export Coq.Structures.OrderedTypeEx.

  Module NatMap := FMapList.Make (Nat_as_OT).

  Definition rescope_parallel (l : list term) :=
    (TVar 0 :: (List.map (fun t => rescope t 0) l))%list.

  Fixpoint subst_parallel (l : list term) (u : term) :=
    match u with
      | TVar n => List.nth n l (TVar n)
      | TApp u1 u2 =>
        TApp (subst_parallel l u1) (subst_parallel l u2)
      | TAbstr u => TAbstr (subst_parallel (rescope_parallel l) u)
    end.

  Fixpoint replace (l : list term) (n : nat) (u : term) :=
   (match l with
      | nil => nil
      | a :: t =>
        match n with
          | 0 => u :: t
          | S p => a :: replace t p u
        end
    end)%list.

  Inductive AssocSubst : Context.t -> list term -> Prop :=
  | ASEmpty : AssocSubst nil nil
  | ASCons : forall (U : ty) (Tl : Context.t) (u : term) (tl : list term),
               reductible U u ->
               AssocSubst Tl tl ->
               AssocSubst (U :: Tl)%list (u :: tl)%list.

  Lemma nth_replace_eq :
    forall (s : list term) (n : nat) (u v : term),
      n < List.length s ->
      List.nth n (replace s n u) v = u.
  Proof.
    induction s.
    - intros n u v H. inversion H.
    - intros n u v H.
      destruct n.
      + reflexivity.
      + simpl. rewrite IHs. reflexivity. simpl in H. omega.
  Qed.

  Lemma nth_replace_neq :
    forall (s : list term) (p q : nat) (u v : term),
      p <> q ->
      List.nth p (replace s q u) v = List.nth p s v.
  Proof.
    induction s.
    - intros. simpl. reflexivity.
    - intros. simpl.
      destruct q ; destruct p.
      + contradict H. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. apply IHs. omega.
  Qed.



  Lemma assoc_mapsto :
    forall (gamma : Context.t) (sub : list term) (n : nat) (U : ty),
      AssocSubst gamma sub ->
      Context.MapsTo gamma n U ->
      exists (u : term), reductible U u /\
                         (forall k : nat,  List.nth n sub (TVar k) = u).
  Proof.
    induction gamma.
    - intros sub n U _ H. inversion H.
    - intros sub n U Hassoc Hmaps.
      destruct n.
      + inversion Hmaps ; subst.
        inversion Hassoc ; subst.
        exists u. split. assumption. simpl. reflexivity.
      + inversion Hassoc; subst. simpl.
        inversion Hmaps ; subst.
        apply IHgamma ; assumption.
  Qed.

  Lemma assoc_rescope :
    forall (gamma : Context.t) (sub : list term) (U : ty),
      AssocSubst gamma sub ->
      AssocSubst (Context.add gamma U) (rescope_parallel sub).
  Proof.
    intros gamma. unfold Context.add, rescope_parallel.
    intros sub U Hassoc.
    apply ASCons. apply cr3'.
    generalize dependent sub.
    induction gamma.
    - intros sub Hassoc. inversion Hassoc. simpl. apply ASEmpty.
    - intros sub Hassoc. inversion Hassoc ; subst.
      simpl. apply ASCons. apply rescope_red. assumption.
      apply IHgamma. assumption.
  Qed.


  Lemma S_iterate :
    forall (n : nat) (A : Set) (f : A -> A) (a : A),
      iterate (S n) f a = f (iterate n f a).
  Proof. intros. reflexivity. Qed.


  Lemma iterate_S :
    forall (n : nat) (A : Set) (f : A -> A) (a : A),
      iterate (S n) f a = iterate n f (f a).
  Proof.
    induction n.
    - reflexivity.
    - intros A f a. replace (iterate (S (S n)) f a) with (f (iterate (S n) f a)).
      pattern (iterate (S n) f a) at 1. rewrite IHn. simpl. reflexivity.
      reflexivity.
  Qed.

  Lemma existing_nth_map :
    forall (sub : list term) (n : nat) (r : term),
      (forall (u : term), List.nth n sub u = r) ->
      (forall (u : term) (f : term -> term),  List.nth n (List.map f sub) u = f r).
  Proof.
    induction sub.
    - intros n r H.
      assert (G := H (TVar 0)).
      assert (TVar 0 = r). rewrite <- G. simpl. destruct n ; reflexivity.
      assert (K := H (TVar 1)).
      assert (TVar 1 = r). rewrite <- K. simpl. destruct n ; reflexivity.
      rewrite <- H0 in H1. discriminate H1.
    -intros n r H.
     destruct n.
     + simpl. simpl in H. assert (G := H (TVar 0)). rewrite G.
       reflexivity.
     + simpl. apply IHsub. simpl in H. exact H.
  Qed.

  Definition it_rescope (k n : nat) (u : term)  :=
    iterate n (fun (t : term) => rescope t k) u.

  Lemma nth_rescope_parallel :
    forall (sub : list term) (n k : nat) (u : term),
      n < k -> List.nth n (iterate k rescope_parallel sub) u = TVar n.
  Proof.
    intros sub n k. generalize dependent sub. generalize dependent n.
    induction k.
    - intros n sub u H. inversion H.
    - intros n sub u H.
      inversion H. simpl.
      destruct k. reflexivity.
      + rewrite existing_nth_map with (r := TVar k). reflexivity.
        intros w. apply IHk. omega.
      + subst.
        destruct n.
        * reflexivity.
        * simpl. rewrite existing_nth_map with (r := TVar n).
          reflexivity.
          intros w. apply IHk. omega.
  Qed.

  Lemma nth_rescope_parallel' :
    forall (sub : list term) (n k : nat) (u : term),
      n >= k ->
      List.nth n (iterate k rescope_parallel sub) u
      = List.nth (n - k) (List.map (it_rescope 0 k) sub) u.
  Proof.
    intros sub n k. generalize dependent n. generalize dependent sub.
    induction k.
    - intros sub n. replace (n - 0) with n. simpl. generalize dependent n.
      induction sub ; intros n u H.
      + simpl. destruct n ; reflexivity.
      + simpl. destruct n. reflexivity. apply IHsub. omega.
      + omega.
    - intros sub n u H. rewrite iterate_S. rewrite IHk.
      simpl. assert (n - k <> 0). omega.
      destruct (n - k) eqn:Eq. contradict H0. reflexivity.
      assert ((n - S k) = n0). omega. rewrite H1.
      unfold it_rescope.
      rewrite List.map_map.
      remember (fun v : term => rescope v 0).
      remember (fun x : term => iterate k t (rescope x 0)) as f.
      remember (fun t0 : term => rescope (iterate k t t0) 0) as g.
      rewrite List.map_ext with term term f g sub. rewrite Heqg. rewrite Heqt. simpl.
       reflexivity.
       intros z. rewrite Heqf. rewrite Heqg.
       replace (rescope z 0) with (t z). rewrite <- iterate_S.
       simpl. rewrite Heqt. reflexivity. rewrite Heqt. reflexivity.
       omega.
  Qed.


  Hint Unfold it_rescope.

  Lemma rescope_iterate_var :
    forall (n k p : nat),
      k <= p -> it_rescope k n (TVar p) = TVar (p + n).
  Proof.
    unfold it_rescope.
    induction n.
    - simpl. auto.
    - intros. rewrite iterate_S. simpl.
      assert (G := H). apply leb_correct in H. rewrite H.
      rewrite IHn. replace (S p + n) with (p + S n). reflexivity.
      omega. omega.
  Qed.

  Lemma rescope_iterate_var' :
    forall (n k p : nat),
      k > p -> it_rescope k n (TVar p) = TVar p.
  Proof.
    unfold it_rescope.
    induction n.
    - simpl. reflexivity.
    - intros. rewrite iterate_S. simpl.
      assert (G := H). apply leb_correct_conv in H. rewrite H.
      rewrite IHn. reflexivity. assumption.
  Qed.


  Lemma rescope_iterate_app :
    forall (n k : nat) (u1 u2 : term),
      it_rescope k n (TApp u1 u2) =
      TApp (it_rescope k n u1) (it_rescope k n u2).
  Proof.
    unfold it_rescope.
    induction n.
    - simpl. reflexivity.
    - simpl. intros. rewrite IHn. simpl. reflexivity.
  Qed.

  Lemma rescope_iterate_abs :
    forall (n k : nat) (u : term),
      it_rescope k n (TAbstr u) =
      TAbstr (it_rescope (S k) n u).
  Proof.
    unfold it_rescope.
    induction n.
    - simpl. reflexivity.
    - simpl. intros. rewrite IHn. simpl. reflexivity.
  Qed.




  Lemma subst_rescope_iterate :
    forall (k p s : nat) (u v : term),
      p <= s -> s <= p + k ->
      [s := v](it_rescope p (S k) u) =
               it_rescope p    k  u.
  Proof.
    intros k p s u.
    generalize dependent s. generalize dependent p. generalize dependent k.
    induction u.
    - simpl. intros k p s v G K.
      destruct (le_lt_dec p n).
      + rewrite rescope_iterate_var.
        rewrite rescope_iterate_var.
        simpl. assert (nat_compare s (n + S k) = Lt).
        apply nat_compare_lt. omega. rewrite H.
        replace (pred (n + S k)) with (n + k).
        reflexivity. omega. assumption. assumption.
      + rewrite rescope_iterate_var'.
        rewrite rescope_iterate_var'.
        simpl. assert (nat_compare s n = Gt).
        apply nat_compare_gt. omega.
        rewrite H. reflexivity. assumption. assumption.
    - intros k p s v G K. simpl.
      repeat (rewrite rescope_iterate_app). simpl.
      rewrite IHu1. rewrite IHu2. reflexivity.
      assumption. assumption.
      assumption. assumption.
    - intros k p s v G K. simpl.
      repeat (rewrite  rescope_iterate_abs). simpl.
      rewrite IHu. reflexivity.
      omega. omega.
  Qed.

  Lemma rescope_it_rescope :
    forall (u : term) (i p k : nat),
      p <= i ->
      rescope (it_rescope k i u) k = rescope (it_rescope k i u) (k + p).
  Proof.
    induction u.
    - intros i p k H.
      destruct (le_lt_dec k n).
      + rewrite rescope_iterate_var. simpl.
        rewrite leb_correct. rewrite leb_correct. reflexivity.
        omega. omega. omega.
      + rewrite rescope_iterate_var'. simpl.
        rewrite leb_correct_conv. rewrite leb_correct_conv. reflexivity.
        omega. omega. omega.
    - intros. rewrite rescope_iterate_app. simpl.
      rewrite IHu1 with i p k. rewrite IHu2 with i p k.
      reflexivity. assumption. assumption.
    - intros i p k H. rewrite rescope_iterate_abs. simpl.
      rewrite IHu with i p (S k). simpl. reflexivity.
      omega.
  Qed.


  Lemma rescope_parallel_iterate_var :
    forall (p k : nat) (sub : list term),
      k < p ->
      subst_parallel (iterate p rescope_parallel sub) (TVar k) = TVar k.
  Proof. intros. simpl. rewrite nth_rescope_parallel. reflexivity. assumption. Qed.

  Lemma rescope_parallel_iterate_var' :
    forall (p k : nat) (sub : list term),
      p <= k ->
      subst_parallel (iterate p rescope_parallel sub) (TVar k)
      = it_rescope 0 p (List.nth (k - p) sub (TVar (k - p))).
  Proof.
    intros. simpl. rewrite nth_rescope_parallel'.
    replace (TVar k) with (it_rescope 0 p (TVar (k - p))).
    rewrite List.map_nth. reflexivity.
    rewrite rescope_iterate_var.
    replace (k - p + p) with k. reflexivity.
    omega. omega. omega.
  Qed.

  Lemma subst_rescope_parallel_var :
    forall (p k : nat) (sub : list term),
      subst_parallel (rescope_parallel (iterate p rescope_parallel sub))
                     (rescope (TVar k) p)
      = rescope (subst_parallel (iterate p rescope_parallel sub) (TVar k)) p.
  Proof.
    intros p k sub.
    destruct (le_lt_dec p k).
    - rewrite rescope_parallel_iterate_var'.
      simpl. rewrite leb_correct. rewrite <- S_iterate.
      rewrite rescope_parallel_iterate_var'.
      assert(G := rescope_it_rescope).
      unfold it_rescope. unfold it_rescope in G.
      rewrite S_iterate. replace (S k - S p) with (k - p).
      rewrite G with (p := p). replace (0 + p) with p.
      reflexivity. omega. omega. omega. omega. assumption. assumption.
    - rewrite rescope_parallel_iterate_var. simpl.
      rewrite leb_correct_conv.
      rewrite <- S_iterate. rewrite rescope_parallel_iterate_var. reflexivity.
       omega. assumption. assumption.
  Qed.

  Lemma subst_rescope_parallel_iterate_var :
    forall (i p : nat) (k : nat) (sub : list term),
      subst_parallel (iterate (i + p) rescope_parallel sub)
                     (it_rescope p i (TVar k) )
      = it_rescope p i (subst_parallel (iterate p rescope_parallel sub) (TVar k)).
  Proof.
    induction i.
    - unfold it_rescope. simpl. reflexivity.
    - intros p k sub.
      replace (it_rescope p (S i) (TVar k))
      with (rescope (it_rescope p i (TVar k)) (i + p)).
      destruct (le_lt_dec p k).
      + simpl.
        rewrite rescope_iterate_var. rewrite subst_rescope_parallel_var.
        rewrite <- rescope_iterate_var with (k := p). rewrite IHi.
        unfold it_rescope. simpl.
        assert (G := rescope_it_rescope). unfold it_rescope in G.
        rewrite G with (p := i). replace (i + p) with (p + i).
        reflexivity. omega. omega. assumption. assumption.
      + rewrite rescope_iterate_var'.
        rewrite rescope_parallel_iterate_var.
        simpl. rewrite leb_correct_conv.
        rewrite <- S_iterate. rewrite rescope_parallel_iterate_var.
        rewrite rescope_iterate_var'. reflexivity.
        omega. omega. omega. omega. omega.
      + assert (G := rescope_it_rescope).
        rewrite plus_comm. rewrite <- G.
        unfold it_rescope. simpl. reflexivity.
        apply le_refl.
  Qed.

  Lemma subst_rescope_parallel_iterate :
    forall (u : term) (i p : nat) (sub : list term),
      subst_parallel (iterate (i + p) rescope_parallel sub)
                     (it_rescope p i u )
      = it_rescope p i (subst_parallel (iterate p rescope_parallel sub) u).
  Proof.
    induction u.
    - intros i p sub. apply subst_rescope_parallel_iterate_var.
    - intros i p sub. simpl.
      repeat (rewrite rescope_iterate_app).
      simpl. rewrite IHu1. rewrite IHu2. reflexivity.
    - intros i p sub. simpl.
      repeat (rewrite rescope_iterate_abs). simpl.
      rewrite <- S_iterate. replace (S (i + p)) with (i + S p).
      rewrite IHu. simpl. reflexivity. omega.
  Qed.

  Lemma iterate_rescope_parallel_length :
    forall (k : nat) (sub : list term),
      length (iterate k rescope_parallel sub) = k + length sub.
  Proof.
    induction k.
    - simpl. reflexivity.
    - intros sub. simpl. rewrite List.map_length.
      rewrite IHk. reflexivity.
  Qed.

  Lemma replace_rescope_parallel :
    forall (sub : list term) (k : nat) (v : term),
      replace (rescope_parallel sub) (S k) (rescope v 0) =
      rescope_parallel (replace sub k v).
  Proof.
    induction sub.
    - intros k v. simpl. unfold rescope_parallel. simpl. reflexivity.
    - intros k v.
      destruct k.
      + simpl. unfold rescope_parallel. simpl. reflexivity.
      + simpl.
        assert (G := IHsub k v).
        simpl in G. unfold rescope_parallel in G.
        inversion G ; subst. rewrite H0.
        unfold rescope_parallel. simpl. reflexivity.
  Qed.

  Lemma subst_subst_parallel :
    forall (u v : term) (sub : list term) (k : nat),
      rescope ([k := v](subst_parallel (iterate (S k) rescope_parallel sub) u)) k =
      subst_parallel (replace (iterate (S k) rescope_parallel sub) k (rescope v k)) u.
  Proof.
    induction u.
    - intros v sub k.
      destruct (le_lt_dec n k).
      + rewrite rescope_parallel_iterate_var.
        inversion l. remember (S k).
        * simpl. replace (nat_compare k k) with Eq.
          rewrite nth_replace_eq. reflexivity.
          rewrite iterate_rescope_parallel_length. omega.
          symmetry. apply nat_compare_eq_iff. reflexivity.
        * remember (S m). remember (S n0).
          simpl. replace (nat_compare n0 n) with Gt.
          rewrite nth_replace_neq. rewrite nth_rescope_parallel.
          simpl. rewrite leb_correct_conv. reflexivity.
          omega. omega. omega. symmetry. rewrite <- nat_compare_gt. omega.
        * omega.
      + replace (TVar n) with (it_rescope k 1 (TVar (n - 1))).
        replace (S k) with (1 + k).
        rewrite subst_rescope_parallel_iterate.
        unfold it_rescope.
        remember (1 + k). simpl. rewrite Parallel.subs_rescope.
        rewrite leb_correct. simpl.
        rewrite nth_replace_neq. rewrite Heqn0. simpl.
        remember (fun t => rescope t 0).
        replace (TVar (S (n - 1))) with (t (TVar (n - 1))).
        rewrite List.map_nth.
        rewrite nth_rescope_parallel'.
        replace (TVar (n - 1)) with (it_rescope 0 k (TVar (n - 1 - k))).
        rewrite List.map_nth. rewrite Heqt.
        rewrite rescope_it_rescope with (p := k). replace (0 + k) with k.
        reflexivity.
        omega. omega.
        rewrite rescope_iterate_var. replace (n - 1 - k + k) with (n - 1).
        reflexivity. omega. omega. omega. rewrite Heqt. simpl. reflexivity.
        omega. omega. omega.
        unfold it_rescope. simpl. rewrite leb_correct.
        replace (S (n - 1)) with n. reflexivity.
        omega. omega.
    - intros v sub k.
      remember (S k). simpl. rewrite Heqn.
      rewrite IHu1. rewrite IHu2. reflexivity.
    - intros v sub k.
      remember (S k). simpl.
      rewrite Heqn. rewrite <- S_iterate. rewrite IHu.
      rewrite S_iterate.
      rewrite iterate_S. rewrite <- Parallel.rescope_comm.
      rewrite replace_rescope_parallel. reflexivity.
      omega.
  Qed.

  Lemma map_rescope_assoc_subst :
    forall (sub : list term) (gamma : Context.t),
      AssocSubst gamma sub ->
      AssocSubst gamma (List.map (fun t => rescope t 0) sub).
  Proof.
    induction sub.
    - simpl. auto.
    - intros gamma H. inversion H ; subst. simpl.
      apply ASCons. rewrite <- rescope_red. assumption.
      apply IHsub. assumption.
  Qed.

  Theorem typing_implies_reductible :
    forall (gamma : Context.t) (u : term) (U : ty),
      typing gamma u U ->
      forall (sub : list term),
        AssocSubst gamma sub ->
        reductible U (subst_parallel sub u).
  Proof.
    intros gamma u U Hderiv. induction Hderiv.
    - intros sub G. simpl.
      assert (H1 := assoc_mapsto gamma sub n T).
      destruct H1 as [u [Hru Hln]] ; try assumption.
      rewrite Hln. assumption.
    - intros sub Hassoc. simpl.
      assert (H1 := IHHderiv1 sub Hassoc).
      simpl in H1. inversion H1 ; subst.
      apply H. apply IHHderiv2. assumption.
    - intros sub Hassoc. simpl. apply substRed.
      apply IHHderiv. apply assoc_rescope. assumption.
      intros v Hv.
      rewrite rescope_red. rewrite subst_subst_parallel.
      apply IHHderiv. simpl.
      apply ASCons. rewrite <- rescope_red. assumption.
      apply map_rescope_assoc_subst. assumption.
  Qed.