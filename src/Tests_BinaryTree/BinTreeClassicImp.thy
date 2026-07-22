theory BinTreeClassicImp
  imports Main
  BinTreeClassic
  Refine_Imperative_HOL.Sepref
begin

fun bin_tree_assn :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a bin_tree \<Rightarrow> 'c bin_tree \<Rightarrow> assn" where
"bin_tree_assn P Leaf Leaf = emp" |
"bin_tree_assn P (Node xa la ra) (Node xc lc rc) = P xa xc * bin_tree_assn P la lc * bin_tree_assn P ra rc" |
"bin_tree_assn P _ _ = false" 

find_theorems "list_assn"

lemmas hn_ctxt_bin_tree = hn_ctxt_eq[of "bin_tree_assn A" for A]

lemma hn_Leaf[sepref_fr_rules]: 
  "hn_refine emp (return Leaf) emp (bin_tree_assn P) (RETURN$Leaf)"
  unfolding hn_refine_def
  by sep_auto

lemma hn_Node[sepref_fr_rules]: 
  "hn_refine 
    (hn_ctxt P x x' * hn_ctxt (bin_tree_assn P) la lc * hn_ctxt (bin_tree_assn P) ra rc) 
    (return (Node x' lc rc)) 
    (hn_invalid P x x' * hn_invalid (bin_tree_assn P) la lc * hn_invalid (bin_tree_assn P) ra rc)
    (bin_tree_assn P)
    (RETURN$((Node) $x$la$ra))
  "
  unfolding hn_refine_def
  apply (sep_auto simp: hn_ctxt_def)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of P]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "bin_tree_assn P"]], frame_inference)
  apply solve_entails
  by (smt (verit, del_insts) assn_times_comm ent_iffI ent_true_drop(1) invalidate_clone'
      prec_split2_aux star_aci(3))

lemma bt_assn_aux_simps[simp]:
  "bin_tree_assn P Leaf t' = (\<up>(t'=Leaf))"
  "bin_tree_assn P t Leaf = (\<up>(t=Leaf))"
  unfolding hn_ctxt_def
  apply (cases t')
  apply simp
  apply simp
  apply (cases t)
  apply simp
  apply simp
  done

lemma bt_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>bt_rel \<equiv> {(t,t'). bt_all2 (\<lambda>x x'. (x,x')\<in>R) t t'}"
  by (simp add: bin_tree_rel_def_internal relAPP_def)

lemma bt_assn_pure_conv[constraint_simps]: "bin_tree_assn (pure R) = pure (\<langle>R\<rangle>bt_rel)"
proof (intro ext)
  fix ta tc
  show "bin_tree_assn (pure R) ta tc = pure (\<langle>R\<rangle>bt_rel) ta tc"
    apply (induction "pure R" ta tc rule: bin_tree_assn.induct)
    by (simp_all add: pure_def bt_rel_def)
qed

lemma bt_assn_aux_ineq_len: "nb_node ta \<noteq> nb_node tc \<Longrightarrow> bin_tree_assn A ta tc = false"
proof (induction ta arbitrary: tc)
  case Leaf
  then show ?case
    by (cases tc) (simp_all add: nb_node.simps bin_tree_assn.simps)
next
  case (Node va la ra)
  show ?case
  proof (cases tc)
    case Leaf
    then show ?thesis by (simp add: bin_tree_assn.simps)
  next
    case (Node vc lc rc)
    with Node.prems have neq:
      "nb_node la + nb_node ra \<noteq> nb_node lc + nb_node rc"
      by (simp add: nb_node.simps)
    then have "nb_node la \<noteq> nb_node lc \<or> nb_node ra \<noteq> nb_node rc"
      by linarith
    then show ?thesis
    proof
      assume "nb_node la \<noteq> nb_node lc"
      hence "bin_tree_assn A la lc = false" by (rule Node.IH(1))
      then show ?thesis
        using \<open>tc = Node vc lc rc\<close> by (simp add: bin_tree_assn.simps)
    next
      assume "nb_node ra \<noteq> nb_node rc"
      hence "bin_tree_assn A ra rc = false" by (rule Node.IH(2))
      then show ?thesis
        using \<open>tc = Node vc lc rc\<close> by (simp add: bin_tree_assn.simps)
    qed
  qed
qed
lemma hn_case_bst[sepref_prep_comb_rule, sepref_comb_rules]:
  fixes ta tc P
  defines [simp]: "INVE \<equiv> hn_invalid (bin_tree_assn P) ta tc"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (bin_tree_assn P) ta tc * F"
  assumes Rn: "ta=Leaf \<Longrightarrow> hn_refine (hn_ctxt (bin_tree_assn P) ta tc * F) f1' (hn_ctxt XX1 ta tc * \<Gamma>1') R f1"
  assumes Rs: "\<And>xa la ra xc lc rc. \<lbrakk> ta=(Node xa la ra); tc=(Node xc lc rc) \<rbrakk> \<Longrightarrow> 
    hn_refine 
      (hn_ctxt P xa xc * hn_ctxt (bin_tree_assn P) la lc * hn_ctxt (bin_tree_assn P) ra rc * INVE * F) 
      (f2' xc lc rc) 
      (hn_ctxt P1' xa xc * hn_ctxt (bin_tree_assn P2') la lc * hn_ctxt (bin_tree_assn P3') ra rc * hn_ctxt XX2 ta tc * \<Gamma>2')
      R 
      (f2 xa la ra)"
  assumes MERGE_VAL[unfolded hn_ctxt_def]: "\<And>xa xc. hn_ctxt P1' xa xc \<Longrightarrow>\<^sub>t hn_ctxt P' xa xc"  
  assumes MERGE_L[unfolded hn_ctxt_def]: "\<And>la lc. hn_ctxt (bin_tree_assn P2') la lc \<Longrightarrow>\<^sub>t hn_ctxt (bin_tree_assn P') la lc"  
  assumes MERGE_R[unfolded hn_ctxt_def]: "\<And>ra rc. hn_ctxt (bin_tree_assn P3') ra rc \<Longrightarrow>\<^sub>t hn_ctxt (bin_tree_assn P') ra rc"
  assumes MERGE2: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<Longrightarrow>\<^sub>t \<Gamma>'"  
  shows "hn_refine \<Gamma> (case_bin_tree f1' f2' tc) (hn_ctxt (bin_tree_assn P') ta tc * \<Gamma>') R (case_bin_tree$f1$(\<lambda>\<^sub>2x l r. f2 x l r)$ta)"
  using assms
  apply (cases ta; cases tc; simp add: bin_tree_assn.simps[THEN hn_ctxt_bin_tree])
  subgoal (*cas des feuilles*)
    apply (rule hn_refine_cons[OF _ Rn _ entt_refl]; assumption?)
     applyS (simp add: hn_ctxt_def)
    apply (subst mult.commute, rule entt_fr_drop)
    apply (rule entt_trans[OF _ MERGE2])
    apply (simp add: ent_disjI1' ent_disjI2')
    done
  subgoal 
    by (simp add: hn_refine_cons_pre)
  subgoal 
    by (simp add: hn_refine_cons_pre)
  subgoal for xa la ra xc lc rc 
    apply (simp only: hn_ctxt_def Rs)
    sorry
  done

  

definition bin_tree_nres_contains :: "('a::linorder) bin_tree \<Rightarrow> 'a \<Rightarrow> bool nres" where
  "bin_tree_nres_contains t v \<equiv> RECT (\<lambda>D (t,v).
     case t of
       Leaf \<Rightarrow> RETURN False
     | Node x l r \<Rightarrow>
         if v < x then D (l, v)
         else if x < v then D (r, v)
         else RETURN True
   ) (t, v)"

sepref_definition bin_tree_imp_contains is "uncurry bin_tree_nres_contains" ::
  "(bin_tree_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding bin_tree_nres_contains_def
  by sepref
lemma bt_assn_aux_insert[simp]:
  assumes "ta = tc"
  shows "bin_tree_assn P (insert ta a) (insert tc c) 
    = bin_tree_assn P ta tc * P a c'"
  sorry

lemma hn_insert[sepref_fr_rules]: 
  "hn_refine 
   (hn_ctxt (bin_tree_assn P) ta tc * hn_ctxt P a c)
   (return (insert tc c))
   (hn_invalid (bin_tree_assn P) ta tc * hn_invalid P a c) 
   (bin_tree_assn P)
   (RETURN$((insert) $ta$a))"
  apply (rule; sep_auto simp: hn_ctxt_def; subst bin_tree_assn.cases)
      apply blast
      apply fast
  subgoal
    
    sorry
  subgoal 
    by (induction ta; auto)
  subgoal by auto
  
  sorry

definition bin_tree_nres_id :: "'a bin_tree \<Rightarrow> 'a bin_tree nres" where
"bin_tree_nres_id t = RETURN t"

sepref_definition bin_tree_imp_id is "bin_tree_nres_id" ::
"(bin_tree_assn  id_assn)\<^sup>k \<rightarrow>\<^sub>a bin_tree_assn id_assn "
  unfolding bin_tree_nres_id_def
  by sepref_dbg_keep


definition bin_tree_nres_insert :: "('a::linorder) bin_tree \<Rightarrow> 'a \<Rightarrow> 'a bin_tree nres" where
  "bin_tree_nres_insert t x \<equiv> do {
    (t', _) \<leftarrow> RECT(\<lambda>D (t, x).
    case t of
      Leaf \<Rightarrow> RETURN (Node x .. .., x) |
      (Node v l r) \<Rightarrow> 
        if x = v then RETURN (t,x)
        else if x > v then do {
            (l', _) \<leftarrow> D (l, x);
            RETURN (Node v l' r, x)}
        else do {
          (r', _) \<leftarrow> D(r, x);
          RETURN (Node v l r', x)
        }
  ) (t, x);
  RETURN t'
}"
lemma test : "(uncurry f,uncurry(\<lambda>t x. 
          REC\<^sub>T
               (\<lambda>D (t, x).
                   case t of 
                    .. \<Rightarrow> RETURN (Node x .. .., x)|
                    Node v l r \<Rightarrow> if x = v then RETURN (t, x)
                                  else if v < x then D (l, x) \<bind> (\<lambda>(l', _). RETURN (Node v l' r, x))
                                  else D (r, x) \<bind> (\<lambda>(r', _). RETURN (Node v l r', x)))
               (t, x) \<bind>
              (\<lambda>(t', _). RETURN t')))
    \<in> (bin_tree_assn id_assn \<times>\<^sub>a id_assn)\<^sup>k \<rightarrow>\<^sub>a bin_tree_assn id_assn "
  sorry
sepref_definition bin_tree_imp_insert is "uncurry bin_tree_nres_insert" ::
"(bin_tree_assn  id_assn \<times>\<^sub>a id_assn)\<^sup>k \<rightarrow>\<^sub>a (bin_tree_assn id_assn)"
  unfolding bin_tree_nres_insert_def
  using test
  by (auto; sepref) 
  
export_code bin_tree_imp_insert in Haskell
end