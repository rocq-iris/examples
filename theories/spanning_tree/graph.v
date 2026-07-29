From stdpp Require Import mapset.
From iris.algebra Require Import gmap.

Section Graphs.
  Context {T : Type} {HD : EqDecision T} {HC : @Countable T HD}.

  Definition graph := gmap T (option T * option T).

  Identity Coercion graph_to_gmap : graph >-> gmap.

  Definition get_left (g : graph) x : option T := g !! x ≫= fst.
  Definition get_right (g : graph) x : option T := g !! x ≫= snd.

  Definition strict_sub_child (ch ch' : option T) :=
    match ch, ch' with
    | Some c, Some c' => c = c'
    | Some c, None => True
    | None, Some _ => False
    | None, None => True
    end.

  Definition strict_sub_children (ch ch' : option T * option T) : Prop :=
    strict_sub_child (ch.1) (ch'.1) ∧ strict_sub_child (ch.2) (ch'.2).

  Definition strict_subgraph (g g' : graph) : Prop :=
    ∀ x, strict_sub_children (get_left g x, get_right g x)
           (get_left g' x, get_right g' x).

(* A path is a list of booleans true for left child and false for the right *)
(* The empty list is the identity trace (from x to x). *)
  Definition path := list bool.

  Identity Coercion path_to_list : path >-> list.

  Inductive valid_path (g : graph) (x y : T) : path → Prop :=
  | valid_path_E : x ∈ dom g → x = y → valid_path g x y []
  | valid_path_l (xl : T) p : get_left g x = Some xl → valid_path g xl y p →
      valid_path g x y (true :: p)
  | valid_path_r (xr : T) p : get_right g x = Some xr → valid_path g xr y p →
      valid_path g x y (false :: p).

  Definition connected (g : graph) (x : T) :=
    ∀ z, z ∈ dom g → ∃ p, valid_path g x z p.

  Definition front (g : graph) (t t' : gset T) := t ⊆ dom g ∧
    ∀ x v, x ∈ t → (get_left g x = Some v) ∨ (get_right g x = Some v) →
       v ∈ t'.

  Definition maximal (g : graph) := front g (dom g) (dom g).

  Definition tree (g : graph) (x : T) :=
    ∀ z, z ∈ dom g → exists !p, valid_path g x z p.

  (* graph facts *)

  Lemma front_t_t_dom g z t :
    z ∈ t → connected g z → front g t t → t = dom g.
  Proof.
    intros Hz Hc [Hsb Hdt].
    apply set_eq_subseteq; split; trivial.
    apply elem_of_subseteq => x Hx. destruct (Hc x Hx) as [p pv].
    clear Hc Hx; revert z Hz pv.
    induction p => z Hz pv.
    - by inversion pv; subst.
    - inversion pv as [|? ? Hpv1 Hpv2 Hpv3|? ? Hpv1 Hpv2 Hpv3]; subst.
      + eauto.
      + eauto.
  Qed.

  Lemma front_mono g t t' s : front g t t' → t' ⊆ s → front g t s.
  Proof. intros [Htd Hf] Hts; split; eauto. Qed.

  Lemma front_empty g : front g ∅ ∅.
  Proof. split; auto. intros ? Hcn; inversion Hcn. Qed.

  Lemma strict_sub_children_refl v : strict_sub_children v v.
  Proof. by destruct v as [[] []]. Qed.

  Lemma strict_sub_children_trans v1 v2 v3 : strict_sub_children v1 v2 →
    strict_sub_children v2 v3 → strict_sub_children v1 v3.
  Proof.
   destruct v1 as [[] []]; destruct v2 as [[] []];
   destruct v3 as [[] []]; cbv; by intuition subst.
  Qed.

  Lemma strict_sub_children_None v : strict_sub_children v (None, None).
  Proof. by destruct v as[[] []]. Qed.

  Lemma strict_subgraph_empty g : strict_subgraph g ∅.
  Proof.
    intros i.
    rewrite /get_left /get_right /strict_sub_child lookup_empty //=.
    by destruct (g !! i) as [[[] []]|].
  Qed.

  Lemma get_left_dom g x y : get_left g x = Some y → x ∈ dom g.
  Proof.
    rewrite /get_left elem_of_dom. case _ : (g !! x); inversion 1; eauto.
  Qed.

  Lemma get_right_dom g x y : get_right g x = Some y → x ∈ dom g.
  Proof.
    rewrite /get_right elem_of_dom. case _ : (g !! x); inversion 1; eauto.
  Qed.

  Lemma path_start g x y p : valid_path g x y p → x ∈ dom g.
  Proof. inversion 1; subst; eauto using get_left_dom, get_right_dom. Qed.

  Lemma path_end g x y p : valid_path g x y p → y ∈ dom g.
  Proof. induction 1; subst; eauto. Qed.

End Graphs.

Global Arguments graph _ {_ _}.
