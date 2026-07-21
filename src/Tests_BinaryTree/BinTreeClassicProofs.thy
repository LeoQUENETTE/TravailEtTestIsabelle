theory BinTreeClassicProofs
imports 
Main
BinTreeClassic
begin

lemma finite_t[simp] : "finite (to_set t)" by (induction t;auto)

(* ----------------------- nb_leaf ----------------------- *)
subsection nb_leaf

lemma "nb_leaf t = nb_node t + 1"
  by (induction t ; auto)
(* ----------------------- to_set ----------------------- *)
subsection to_set

lemma to_set_work : "v\<in>to_set (Node v l r)"  
  by (smt (verit) Un_iff bin_tree.distinct(1) bin_tree.sel(1) insertCI
      to_set.elims)
lemma to_set_decomp : "v\<in>to_set (Node v l r) \<Longrightarrow> v\<in>to_set l \<union> to_set r \<union> {v}" by auto
lemma to_set_decomp2 : "x\<noteq>v \<Longrightarrow> x\<in>to_set (Node v l r) \<Longrightarrow> x\<in>to_set l \<union> to_set r"
  by simp
lemma to_set_decomp3 : "x \<in>to_set (Node v l r) \<Longrightarrow> x = v \<or> x\<in> to_set l \<or> x \<in> to_set r"
  by simp

lemma to_set_include_l : 
  assumes "x \<in> to_set l"
  shows "x \<in> to_set (Node v l r)" 
  using assms
  by (smt (verit) UnCI bin_tree.distinct(1) bin_tree.sel(2) empty_iff to_set.elims)


lemma to_set_include_r : 
  assumes "x \<in> to_set r"
  shows "x \<in> to_set (Node v l r)"
  using assms
  by (smt (verit) UnI2 bin_tree.discI bin_tree.inject equals0D to_set.elims)


lemma to_set_include : 
  assumes "x = v "
  shows "x \<in> to_set (Node v l r)"
  using assms 
  unfolding to_set.simps
  by (smt (verit) UnCI bin_tree.distinct(1) bin_tree.sel(1) singletonI to_set.elims)

lemma to_set_to_list: "set (to_list t) = to_set t"
proof (induction t)
  case Leaf
  then show ?case by auto
next
  case (Node v l r)
  then show ?case 
    by (smt (verit) Un_insert_left bin_tree.discI bin_tree.inject empty_set
        insert_is_Un list.simps(15) self_append_conv self_append_conv2 set_append
        to_list.elims to_set.elims)
qed



lemma to_set_node_union: 
  "to_set (Node v l r) = {v} \<union> to_set l \<union> to_set r" 
  by (induct l; induct r; auto)
(* ----------------------- count_val ----------------------- *)
subsection count_val

lemma count_val_decrement_l :
  assumes "x = v"
  shows "count_val (Node v l r) x > count_val l x"
  using assms
  by (induct l; auto)
lemma count_val_decrement_r :
  assumes "x = v"
  shows "count_val (Node v l r) x > count_val r x"
  using assms
  by (induct r; auto)
lemma count_val_decomp : 
  assumes "v \<noteq> x"
  shows "count_val (Node v l r) x = count_val l x + count_val r x"
  using assms by auto
lemma count_val_decomp2 : 
  assumes "count_val (Node v l r) x > 1"
  assumes "v = x"
  shows "count_val l x + count_val r x \<ge> 1"
  using assms by auto

lemma count_val_pos_imp_mem :
  "count_val t x > 0 \<Longrightarrow> x \<in> to_set t"
proof (induction t)
  case Leaf
  then show ?case by simp
next
  case (Node v l r)
  show ?case
  proof (cases "v = x")
    case True
    then show ?thesis
      using to_set_work by auto
  next
    case False
    from Node.prems False
    have H:
      "count_val l x > 0 \<or> count_val r x > 0"
      by auto

    then show ?thesis
    proof
      assume "count_val l x > 0"
      hence "x \<in> to_set l"
        using Node.IH(1) by blast
      have "x \<in> to_set l \<Longrightarrow> x\<in> to_set (Node v l r)" 
        using to_set_decomp[of x l r] to_set_decomp3[of x v l r]
        by simp
      thus ?thesis
        by (metis \<open>x \<in> to_set l \<Longrightarrow> x \<in> to_set (Node v l r)\<close> \<open>x \<in> to_set l\<close>)
    next
      assume "count_val r x > 0"
      hence "x \<in> to_set r"
        using Node.IH(2) by blast
      thus ?thesis
        using to_set_decomp[of x l r] 
        by (smt (verit) Un_upper2 bin_tree.discI bin_tree.inject in_mono insert_absorb
            insert_not_empty to_set.elims)
    qed
  qed
qed

lemma count_val_pos_iff_mem: "count_val t x > 0 \<longleftrightarrow> x \<in> to_set t"
proof (induction t)
  case Leaf
  then show ?case by auto
next
  case (Node v l r)
  consider "v=x"|"v\<noteq>x" by fastforce
  then show ?case 
  proof (cases)
    case 1
    then show ?thesis
    proof -
      from `v=x` have "count_val (Node v l r) x > 0" by auto
      from  `v=x` have "x \<in> to_set (Node v l r)" 
        using to_set_work
        by auto
      then show ?thesis
        by (metis \<open>x \<in> to_set (Node v l r)\<close> \<open>0 < count_val (Node v l r) x\<close>)
    qed
  next
    case 2
    then show ?thesis 
    proof -
      from `v\<noteq>x` 
      have "count_val (Node v l r) x = count_val l x + count_val r x" 
        by auto
      from `v\<noteq>x` have "x \<in> to_set (Node v l r) \<Longrightarrow> x \<in> to_set l \<union> to_set r" 
        using to_set_decomp2[of x v l r]
        by auto
      from `v\<noteq>x` have "0 < count_val l x \<or> 0 < count_val r x \<Longrightarrow> x\<in>to_set (Node v l r)" 
        by (metis count_val_pos_imp_mem \<open>count_val (Node v l r) x = count_val l x + count_val r x\<close> gr0I zero_eq_add_iff_both_eq_0)
      then show ?thesis using `v\<noteq>x` 
        using Node.IH(1,2) \<open>x \<in> to_set (Node v l r) \<Longrightarrow> x \<in> to_set l \<union> to_set r\<close>
        by force
    qed
  next
  qed
qed
lemma count_val_duplicate :
  assumes "v = x"
  assumes "count_val (Node v l r) x > 1"
  shows "\<not>(\<forall>y \<in> to_set l \<union> to_set r. y \<noteq> v)"
proof -
  from assms(2) have "count_val l x + count_val r x > 0"
    using assms(1) by simp
  then have "count_val l x > 0 \<or> count_val r x > 0"
    by auto
  then have "x \<in> to_set l \<or> x \<in> to_set r"
    using count_val_pos_iff_mem by auto
  then have "x \<in> to_set l \<union> to_set r"
    by auto
  then show ?thesis
    using assms(1) by auto
qed 

(* ----------------------- bst_invariant ----------------------- *)
subsection bst_invariant
lemma bst_invariant_no_dup_root:
  "bst_invariant (Node v l r) \<Longrightarrow> count_val (Node v l r) v \<le> 1"
  using count_val_duplicate[of v v l r] by force

lemma bst_invariant_no_dup_root2:
  "count_val (Node v l r) v > 1 \<Longrightarrow> bst_invariant (Node v l r) = False"
  using count_val_duplicate[of v v l r] by force

lemma bst_invariant_count_l: 
  "bst_invariant (Node v l r) \<Longrightarrow> count_val l v = 0"
proof -
  assume "bst_invariant (Node v l r)"
  then have "\<forall>x\<in>to_set l. x < v"
    by simp
  then have "v \<notin> to_set l"
    by auto
  then show "count_val l v = 0"
    using count_val_pos_iff_mem[of l v] by auto
qed

lemma bst_invariant_count_r: "bst_invariant (Node v l r) \<Longrightarrow> count_val r v = 0"
proof -
  assume "bst_invariant (Node v l r)"
  then have "\<forall>x\<in>to_set r. x > v"
    by simp
  then have "v \<notin> to_set r"
    by auto
  then show "count_val r v = 0"
    using count_val_pos_iff_mem[of r v] by auto
qed

lemma bst_invariant_max_node : 
  assumes inv : "bst_invariant (Node v l r)"
  assumes neq : "v \<noteq> Max (to_set (Node v l r))"
  shows "Max (to_set (Node v l r)) \<in> to_set r"
  
proof -

  have l_bound: "\<forall>x \<in> to_set l. x < v" using inv by auto
  have r_bound: "\<forall>x \<in> to_set r. v < x" using inv by auto
  have l_r_relation: "\<forall>xl\<in>to_set l. \<forall>xr\<in>to_set r. xl < xr" using l_bound r_bound inv 
  by fastforce
  show ?thesis
    using assms l_r_relation finite_t
    by (metis Max.coboundedI emptyE l_bound leD obtains_Max to_set_decomp3 to_set_include)
qed
lemma bst_invariant_min_node : 
  assumes inv : "bst_invariant (Node v l r)"
  assumes neq : "v \<noteq> Min (to_set (Node v l r))"
  assumes fin : "finite (to_set (Node v l r))"
  shows "Min (to_set (Node v l r)) \<in> to_set l"
proof -
  have l_bound: "\<forall>x \<in> to_set l. x < v" using inv by auto
  have r_bound: "\<forall>x \<in> to_set r. v < x" using inv by auto
  have l_r_relation: "\<forall>xl\<in>to_set l. \<forall>xr\<in>to_set r. xl < xr" using l_bound r_bound inv 
  by fastforce
  show ?thesis 
    using assms l_r_relation
    by (metis Min.coboundedI empty_iff leD obtains_Min r_bound to_set_decomp3 to_set_work)
qed

(* ----------------------- insert ----------------------- *)
subsection insert
lemma insert_correct : "x \<in> to_set (insert t x)"
proof (induct t)
  case (Leaf)
  then show ?case 
    by auto
next
  case (Node v l r)
  then show ?case
    by (induct l; induct r; auto)
qed

lemma insert_adds: "to_set (insert t x) = to_set t \<union> {x}"
proof (induct t)
  case Leaf
  then show ?case by auto 
next
  case (Node v l r)
  then show ?case
    by (smt (verit) Un_insert_left bin_tree.distinct(1) bin_tree.inject insert.elims insert_absorb
        insert_correct sup_assoc sup_bot_right sup_commute to_set.elims)
qed
lemma insert_adds2 : "to_set (insert t x) = Set.insert x (to_set t)"
proof (induct t)
  case Leaf
  then show ?case by auto
next
  case (Node v l r)
  then show ?case
    by (metis Un_commute insert_adds insert_is_Un)
qed
  
lemma insert_subset :
  assumes "x \<noteq> y"
  assumes "x \<in> to_set (insert t y)"
  shows "x \<in> to_set t"
  using assms insert_adds2 by blast
lemma to_set_insert_subset: "to_set t \<subseteq> to_set (insert t x)"
  by (simp add: insert_adds2 subset_insertI)

lemma insert_preserves_lower:
  assumes "\<forall>y\<in>to_set t. a < y"
  assumes "a < x"
  shows "\<forall>y\<in>to_set (insert t x). a < y"
  using assms 
  by (simp add: insert_adds)

lemma insert_preserves_upper:
  assumes "\<forall>y\<in>to_set t. y \<le> a"
  assumes "x \<le> a"
  shows "\<forall>y\<in>to_set (insert t x). y \<le> a"
  using assms by (simp add: insert_adds)
                                                                   
lemma inv_holds: "bst_invariant t \<Longrightarrow> bst_invariant (insert t (x::nat))"
proof (induction t )
  case Leaf
  then show ?case by simp
next
  case (Node v l r)
  consider "x < v" | "x > v" | "x = v" 
    by linarith
  then show ?case
  proof (cases)
    case 1
    then show ?thesis 
      using Node by (auto ; metis insert_adds2 insert_iff)
  next
    case 2
    then have "insert (Node v l r) x = Node v l (insert r x)" by auto 
    moreover have "\<forall>xa \<in> to_set (insert r x). xa > v" 
      using Node 2 
      by (metis bin_tree.distinct(1) bst_invariant.simps(2) insert_preserves_lower)
    ultimately show ?thesis using Node by force
  next
    case 3
    then show ?thesis 
      using Node.prems 
      by fastforce
  qed
qed
lemma preserves_Max : 
  assumes "finite (to_set t)"
  assumes "t \<noteq> Leaf"
  assumes "x < Max (to_set t)"
  shows "Max (to_set t) = Max (to_set (insert t x))"
  using assms
proof (induction t)
  case Leaf
  then show ?case by auto
next
  case (Node v l r)
  then show ?case 
    apply (subst to_set.simps)
    apply (subst Max_def)
    by (simp add: Max.semilattice_set_axioms Max_def insert_adds2 semilattice_set.insert)
qed
  
(* ----------------------- is_present ----------------------- *)
subsection is_present

lemma 
    assumes "x \<in> to_set t"
    shows "is_present t x = True"
    using assms
proof (induction t)
  case Leaf
  then show ?case by auto
next
  case (Node v l r)
  then show ?case
    by auto
 qed

lemma "x \<notin> to_set t \<Longrightarrow> is_present t x = False"
proof (induction t)
  case Leaf
  then show ?case by auto
next
  case (Node x1 t1 t2)
  then show ?case 
     by (induct t1; induct t2; auto)
 qed

(* ----------------------- bst_is_present ----------------------- *)
subsection bst_is_present

lemma bst_is_present_1 : "bst_is_present (Node v l r) v = True"
  by auto


(* ----------------------- insert_lists ----------------------- *)
subsection insert_lists

lemma to_set_insert_lists_subset: "to_set t \<subseteq> to_set (insert_lists t xs)"
proof (induct xs arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    using to_set_insert_subset[of t x]
    by fastforce
qed
lemma to_set_insert_lists_list:
  "xa \<in> set xs \<Longrightarrow> xa \<in> to_set (insert_lists t xs)"
proof (induct xs arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "xa = x")
    case True
    then show ?thesis
      using to_set_insert_lists_subset insert_correct
      by fastforce
  next
    case False
    then have "xa \<in> set xs" using Cons.prems by simp
    then show ?thesis using Cons.hyps by simp
  qed
qed
lemma insert_lists_subset_l:
  assumes "xa  \<in> to_set l"
  shows "xa \<in> to_set (insert_lists l (to_list r))"
proof (cases l)
  case Leaf
  then show ?thesis 
    using assms to_set_include_r to_set_include_l to_set_decomp2
    by auto
next
  case (Node v' l' r')
    consider "xa = v'"|"xa \<in> to_set(l')"| "xa \<in>to_set( r')"
    using assms to_set_include_r to_set_include_l to_set_decomp2 Node
    by fastforce
  then show ?thesis
  using assms to_set_insert_lists_subset to_set_include_r to_set_include_l to_set_decomp2 to_set_decomp Node to_set_work
      by fastforce
qed

lemma insert_lists_subset_r:
  assumes "xa \<in> to_set r"
  shows "xa \<in> to_set (insert_lists l (to_list r))"
proof -
  have "xa \<in> set (to_list r)"
    using assms to_set_to_list by fastforce
  then show ?thesis
    using to_set_insert_lists_list by auto
qed
lemma to_set_insert_correct : "to_set (insert t x) = to_set t \<union> {x}"
  by (metis insert_adds)


  
(* ----------------------- search_max ----------------------- *)
lemma search_max_work:
  assumes "bst_invariant t"
  shows "\<forall>x \<in> to_set(t). search_max t \<ge> x"
  using assms
  by (induction t rule: search_max.induct; auto)

lemma search_max_subset :
  assumes "bst_invariant t"
  and "t \<noteq> Leaf"
  shows "search_max t \<in> to_set t"
  using assms
  by (induction t rule: search_max.induct; auto)

(* ----------------------- delete ----------------------- *)
subsection delete

value "bst_invariant (Node (5::nat) (Node (5::nat) .. ..) ..)"

lemma delete_subset_core: 
  assumes "bst_invariant t"
  shows "to_set (delete t x) \<subseteq> to_set t"
  using assms
proof (induction t arbitrary: x)
  case Leaf
  then show ?case 
    by auto
next
  case (Node v l r)
  then show ?case
  proof -
    have "to_set l \<union> to_set r \<subseteq> to_set (Node v l r)" by auto 
    then have "l \<noteq> .. \<Longrightarrow> to_set (delete l (search_max l)) \<subseteq> to_set l"
      by (metis bst_invariant.simps(2) Node.prems Node.IH(1))
    then have l_node1: "x = v \<Longrightarrow> l \<noteq> ..\<Longrightarrow>to_set (Node (search_max l) (delete l (search_max l)) r)  \<subseteq> to_set (Node v l r)"
      using Node.prems search_max_subset by auto
    then have l_node2: "x = v \<Longrightarrow> l \<noteq> .. \<Longrightarrow> r \<noteq> .. \<Longrightarrow>to_set (Node (search_max l) (delete l (search_max l)) r) = to_set (delete (Node v l r) x)"
      proof -
        assume hxv: "x = v"
        assume hl: "l \<noteq> Leaf"
        assume hr: "r \<noteq> Leaf"
        obtain vl ll rl where hl_eq: "l = Node vl ll rl"
          using hl by (cases l) auto
        obtain vr lr rr where hr_eq: "r = Node vr lr rr"
          using hr by (cases r) auto
        show ?thesis
          using hxv hl_eq hr_eq
          by (simp add: delete.simps hl_eq hr_eq) 
      qed
    then have l_node3: "x = v \<Longrightarrow> l \<noteq> .. \<Longrightarrow> r = .. \<Longrightarrow>to_set l = to_set (delete (Node v l r) x)"
      by (simp add: bin_tree.case_eq_if)
    then have l_leaf:"x = v \<Longrightarrow> l = .. \<Longrightarrow> to_set (r)  = to_set (delete (Node v l r) x)"
      by auto
  then have "x = v \<Longrightarrow> to_set (delete (Node v l r) x)
    \<subseteq> to_set (Node v l r)"
    using l_node1 l_node2 l_node3 l_leaf
    using \<open>to_set l \<union> to_set r \<subseteq> to_set (Node v l r)\<close> by blast
  then have "to_set (Node v (delete l x) r) \<subseteq> to_set (Node v l r)"
    using Node.IH(1) Node.prems by auto
  then have "to_set (Node v l (delete r x)) \<subseteq> to_set (Node v l r)"
    using Node.IH(2) Node.prems by auto
  then have "x < v \<Longrightarrow> to_set (Node v (delete l x) r) = to_set (delete (Node v l r) x)"
    by auto
  then have "x > v \<Longrightarrow> to_set (Node v l (delete r x)) = to_set (delete (Node v l r) x)"
    by (metis delete.simps(2) less_le_not_le)
  then show ?thesis 
    by (metis \<open>v < x \<Longrightarrow>
      to_set (Node v l (delete r x)) = to_set (delete (Node v l r) x)\<close> \<open>to_set (Node v l (delete r x)) \<subseteq> to_set (Node v l r)\<close> \<open>x = v \<Longrightarrow>
      to_set (delete (Node v l r) x) \<subseteq> to_set (Node v l r)\<close> \<open>to_set (Node v (delete l x) r) \<subseteq> to_set (Node v l r)\<close> delete.simps(2))
  qed
qed


lemma delete_subset_r:
  assumes "bst_invariant (Node v l r)"
  shows "to_set (Node v l (delete r x)) \<subseteq> to_set (Node v l r)"
  using delete_subset_core[of r x]
  using assms by auto

lemma delete_subset_l:
  assumes "bst_invariant (Node v l r)"
  shows "to_set (Node v (delete l x) r) \<subseteq> to_set (Node v l r)"
  using delete_subset_core[of l x] assms
  by auto
lemma delete_only_one_element : 
  assumes "x \<in> to_set t"
  assumes "finite (to_set t)"
  assumes "bst_invariant t"
  assumes "t \<noteq> Leaf"
  shows "to_set (delete t x) = to_set t - {x}"
  using assms
proof (induction t arbitrary: x)
  case Leaf
  then show ?case by auto
next
  case (Node v l r)
  have inv: "bst_invariant (Node v l r)" 
    using Node.prems(3) by simp
  have hx_in: "x \<in> to_set (Node v l r)" 
    using Node.prems(1) by simp
  have hfin: "finite (to_set (Node v l r))" 
    using Node.prems(2) by simp
  consider "x = v" | "x < v" | "x > v" by fastforce
  then show ?case
  proof cases
    case h1 : 1
    then show ?thesis 
      proof -
      have inv: "bst_invariant (Node v l r)" using Node.prems by simp
      consider 
    "l = Leaf" | 
    "r = Leaf \<and> l \<noteq> Leaf" | 
    "l \<noteq> Leaf \<and> r \<noteq> Leaf"
    by auto
  then show ?thesis
    proof cases
      case 1
      then show ?thesis 
        using inv Node.IH h1
        by force
    next
      case 2
        have "\<And>vl ll rl. l = Node vl ll rl \<Longrightarrow> to_set (delete (Node v l r) x) = to_set ((Node v l r)) - {x}"
        using inv 2 h1
        by auto
      then show ?thesis 
        using inv 2 h1 Node.IH
        by (metis bst_invariant.elims(2) bst_invariant.simps(2))
    next
      case 3
        have "\<And>vl ll rl vr lr rr.  l = Node vl ll rl \<and> r = Node vr lr rr \<Longrightarrow>
                x \<notin> to_set (Node (search_max l) (delete l (search_max l)) r)"
        using inv 3 h1
        by (metis bst_invariant.simps(2) bst_invariant_count_l
            bst_invariant_count_r count_val_pos_iff_mem delete_subset_core
            less_numeral_extra(3) search_max_subset subsetD to_set_decomp3)
      then have "\<And>vl ll rl vr lr rr. l = Node vl ll rl \<and> r = Node vr lr rr \<Longrightarrow>
                to_set (Node (search_max l) (delete l (search_max l)) r) = to_set r \<union> to_set l"
        using inv 3 h1
        by (metis Node.IH(1) Un_commute bst_invariant.simps(2) finite_t insert_Diff insert_is_Un
            search_max_subset to_set_node_union)
      then have "\<And>vl ll rl vr lr rr. l = Node vl ll rl \<and> r = Node vr lr rr \<Longrightarrow> 
                to_set (delete (Node v l r) x) = to_set r \<union> to_set l"
        using inv 3 h1
        by fastforce
      then have res_nodes: "\<And>vl ll rl vr lr rr. l = Node vl ll rl \<and> r = Node vr lr rr \<Longrightarrow> 
                to_set (delete (Node v l r) x) = to_set(Node v l r) - {x}"
        using inv 3 h1
        by fastforce
      then show ?thesis 
        by (meson "3" bst_invariant.elims(2) bst_invariant.simps(2) inv)
    qed
  qed
  next
    case 2
    then show ?thesis 
    proof -
      have inv: "bst_invariant (Node v l r)" using Node.prems by simp 
      then have "to_set (delete (Node v l r) x) = to_set (Node v (delete l x) r)"
        using 2 delete.simps 
        by auto
      then have "to_set (delete l x) \<union> to_set r \<union> {v} = to_set (Node v (delete l x) r)"
        using 2 delete.simps 
        by auto
      then have "to_set (l) - {x} = to_set (delete l x)"
        using inv 2 
        by (metis  inv delete.simps(1) "2" hx_in bst_invariant.simps(2) to_set_decomp3 Node.IH(1) to_set.simps(1) empty_Diff less_le_not_le finite_t)
      then have "to_set (l) - {x} \<union> to_set r \<union> {v} = to_set (Node v (delete l x) r)"
        by auto
      then show ?thesis
        by (smt (verit) "2" Diff_empty Diff_insert0 Node.IH(1) Un_Diff
            \<open>to_set (delete (Node v l r) x) = to_set (Node v (delete l x) r)\<close> bst_invariant.simps(2)
            empty_iff finite_t hx_in insert_Diff insert_Diff_if inv not_less_iff_gr_or_eq to_set.simps(1)
            to_set_decomp3 to_set_node_union)
      qed
  next
    case 3
    then show ?thesis 
      using Node.IH(2) hx_in inv not_less_iff_gr_or_eq 
      by fastforce
  qed
qed 

lemma
  assumes "x\<in>to_set t"
  assumes "finite (to_set t)"
  assumes "bst_invariant t"
  shows "x \<notin> to_set (delete t x)"
  using assms
proof (induction t arbitrary: x)
  case Leaf
  then show ?case 
    by auto
next
  case (Node v l r)
  consider "v=x"|"v<x"|"v>x" 
    by (metis linorder_less_linear)
  then show ?case 
  proof (cases)
    case 1
    then show ?thesis 
    proof -
      have "v = x \<Longrightarrow> l = .. \<Longrightarrow> delete (Node v l r) x = r" 
        by auto
      then have "v = x \<Longrightarrow> l = .. \<Longrightarrow>x \<notin> to_set (delete (Node v l r) x)" 
        using Node.prems
        using bst_invariant.simps by fastforce
      have "\<And>vl ll rl. v = x \<Longrightarrow> r = .. \<and> l = (Node vl ll rl) \<Longrightarrow> delete (Node v l r) x = l"
        by auto
      then have "\<And>vl ll rl. v = x \<Longrightarrow> r = .. \<and> l = (Node vl ll rl) \<Longrightarrow> x \<notin> to_set(delete (Node v l r) x)"
        using Node.prems(3) by fastforce
      have "\<And>vl ll rl vr lr rr. v = x \<Longrightarrow> l = (Node vl ll rl) \<and> r = (Node vr lr rr) \<Longrightarrow> to_set (delete (Node v l r) x) = to_set(Node (search_max l) (delete l (search_max l)) r)"
        by auto
      then have "\<And>vl ll rl. l = (Node vl ll rl) \<Longrightarrow> to_set(Node (search_max l) (delete l (search_max l)) r) = to_set l \<union> to_set r"
        using search_max_subset Node.prems to_set_decomp 
      proof -
        fix vl ll rl
        assume hl: "l = Node vl ll rl"
        have sm_in: "search_max l \<in> to_set l" 
          using Node.prems(3) bst_invariant.simps(2) hl search_max_subset
          by blast
        have inv_l: "bst_invariant l" using Node.prems(3) by auto
        have del_set: "to_set (delete l (search_max l)) = to_set l - {search_max l}"
          using delete_only_one_element finite_t hl inv_l sm_in 
          by blast
        have "to_set (Node (search_max l) (delete l (search_max l)) r) = {search_max l} \<union> to_set (delete l (search_max l)) \<union> to_set r"
          using delete.simps by auto
        also have "... = {search_max l} \<union> (to_set l - {search_max l}) \<union> to_set r"
          using del_set by simp
        also have "... = to_set l \<union> to_set r"
          using sm_in by blast  
        finally show "to_set (Node (search_max l) (delete l (search_max l)) r) = to_set l \<union> to_set r"
          by simp
      qed
      then have "\<And>vl ll rl vr lr rr. v = x \<Longrightarrow> l = (Node vl ll rl) \<and> r = (Node vr lr rr) \<Longrightarrow> to_set (delete (Node v l r) x) = to_set l \<union> to_set r"
        by auto
      then have "\<And>vl ll rl vr lr rr. v = x \<Longrightarrow> l = (Node vl ll rl) \<and> r = (Node vr lr rr) \<Longrightarrow> x \<notin> to_set l \<union> to_set r"
        by (metis Node.prems(3) Un_iff bst_invariant_count_l bst_invariant_count_r count_val_pos_iff_mem
            order_less_irrefl)
      then show ?thesis
        by (metis "1" Node.prems(3)
            \<open>\<And>vl rl ll. v = x \<Longrightarrow> r = .. \<and> l = Node vl ll rl \<Longrightarrow> x \<notin> to_set (delete (Node v l r) x)\<close>
            \<open>\<And>vr vl rr rl lr ll. v = x \<Longrightarrow> l = Node vl ll rl \<and> r = Node vr lr rr \<Longrightarrow> to_set (delete (Node v l r) x) = to_set l \<union> to_set r\<close>
            \<open>v = x \<Longrightarrow> l = .. \<Longrightarrow> delete (Node v l r) x = r\<close> bst_invariant_count_r count_val_pos_iff_mem
            order_less_irrefl to_list.cases)
    qed
  next
    case 2
    then show ?thesis 
    proof (cases l)
      case Leaf
      then show ?thesis 
        using Node.IH(2) Node.prems(1,3) not_less_iff_gr_or_eq 
          by fastforce
    next
      case (Node vl ll rl)
      consider "x = vl"|"x < vl"|"x > vl" by fastforce
      then show ?thesis 
      proof (cases)
        case 1
        then show ?thesis
          by (metis "1" bst_invariant.simps(2) Node.prems(3) to_set_decomp3 Node to_set_work delete.simps(2) Node.IH(1) less_le_not_le finite_t)
      next
        case 2
        then show ?thesis 
          by (metis Node Node.IH(1,2) Node.prems(1,3) bst_invariant.simps(2)
              delete.simps(2) finite_t not_less_iff_gr_or_eq to_set_decomp3
              to_set_work)
      next
        case 3
        then show ?thesis 
          using "2" Node.IH(2) Node.prems(1,3) not_less_iff_gr_or_eq
          by fastforce
      qed
    qed
  next
    case 3
    then show ?thesis 
      using assms
      proof (cases r)
        case Leaf
        then show ?thesis 
          by (metis Node.prems(1) bst_invariant.simps(2) Node.prems(3) to_set_decomp3 "3" delete.simps(2) Node.IH(1) finite_t less_le_not_le)
      next
        case (Node vr lr rr)
        then show ?thesis
          by (metis bst_invariant.simps(2) Node.prems(3) Node.prems(1) "3" Node.IH(1) delete.simps(2) finite_t less_le_not_le to_set_decomp2 Un_iff)
      qed
  qed
qed

lemma delete_invariant:
  assumes "finite (to_set t)"
  assumes "bst_invariant t"
  shows "bst_invariant (delete t x)"
  using assms
proof (induction t x arbitrary: x rule:delete.induct)
  case (1 x)
  then show ?case 
    by auto
next
  case (2 v l r x)
  consider "x = v" | "x < v" | "x > v" by fastforce
  then show ?case 
  proof (cases)
    case 1
    have "r = .. \<Longrightarrow> bst_invariant (l)"
      by (metis bst_invariant.simps(2) "2.prems"(2))
    have "l = .. \<Longrightarrow> bst_invariant (r)"  
    by (metis bst_invariant.simps(2) "2.prems"(2)) 
  have "\<And>vr lr rr vl ll rl. r = Node vr lr rr \<Longrightarrow> l = Node vl ll rl\<Longrightarrow>
        bst_invariant (Node (search_max l) (delete l (search_max l)) r)" 
    
    sorry
    then show ?thesis 
      sorry
  next
    case 2
    then show ?thesis sorry
  next
    case 3
    then show ?thesis sorry
  qed
qed

end