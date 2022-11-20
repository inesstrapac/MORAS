Goal forall X Y, ~(X /\ Y) \/ (~X /\ Y) \/ (~X /\ ~Y) <-> ~(X /\ Y).
Proof.
  intros. split.
  intros H neg. destruct H.  apply H.  exact neg. 
  destruct H.  apply H.  destruct neg. apply H0. apply H. destruct neg. apply H1.
  intros. left. exact H.
Qed.


Goal forall X Y Z, ~(~X /\ Y /\ ~Z) /\ ~(X /\ Y /\ Z) /\ (X /\ ~Y /\ ~Z) <-> (X /\ ~Y /\ ~Z).
Proof.
  intros. split.
  intros. destruct H. destruct H0. apply H1.
  intros. split.  intros neg. destruct neg. destruct H1. destruct H.  unfold not. apply H0. apply H. 
  split. intros neg. destruct H. destruct H0. destruct neg. destruct H3. apply H1. apply H4. 
  exact H. 
Qed.