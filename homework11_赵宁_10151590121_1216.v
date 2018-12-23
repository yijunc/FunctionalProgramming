(* homework11_\u8d75\u5b81_10151590121_1216 *)Set Warnings "-notation-overridden,-parsing".
Add LoadPath "coq/coq_project".Require Export IndProp.Require Export Rel.(* 1 *)(** **** Exercise: 2 stars, optional (le_antisymmetric)  *)Theorem le_antisymmetric :  antisymmetric le.Proof.
  unfold antisymmetric.
  intros a b Ha Hb.
  inversion Ha as [| m H'].
  - reflexivity.
  - Print le_trans. 
    assert(S m <= m). {
    apply le_trans with a.
    rewrite H.
    + assumption. 
    + assumption. }
    apply le_Sn_n in H0.
    inversion H0.
Qed. (* 2 *)(** **** Exercise: 2 stars, optional (le_step)  *)Theorem le_step : forall n m p,  n < m ->  m <= S p ->  n <= p.Proof.  intros n m p Hnm Hmp. Print lt. unfold lt in Hnm.  assert (S n <= S p).  {    apply le_trans with m.     - assumption.    - assumption.  }  apply le_S_n.  assumption.Qed.(* 3 *)(** **** Exercise: 2 stars, optional (rsc_trans)  *)Lemma rsc_trans :  forall (X:Type) (R: relation X) (x y z : X),      clos_refl_trans_1n R x y  ->      clos_refl_trans_1n R y z ->      clos_refl_trans_1n R x z.Proof.  intros X R  x y z Hxy Hyz.
  induction Hxy as [x| x y y' Rxy Hyy].
  - assumption.
  - apply rt1n_trans with y.
    + assumption.
    + apply IHHyy in Hyz. apply Hyz.Qed.