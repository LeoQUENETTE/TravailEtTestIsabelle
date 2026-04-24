theory Path_Indexing
  imports
    Linear_Unification
    "Finite-Map-Extras.Finite_Map_Extras"
begin

section \<open>Trie structure\<close>

datatype (plugins del: size) ('f,'v) trie =
  Leaf "('f,'v) term set"
| SymbolNode (children: "('f symbol, (nat, ('f, 'v) trie) fmap) fmap")
  where
    "children (Leaf x) = fmempty"

abbreviation empty_trie :: "('f, 'v) trie"
  where "empty_trie \<equiv> SymbolNode fmempty"

function (domintros) trie_depth :: "('f,'v) trie \<Rightarrow> nat" where
  "trie_depth (Leaf ts)       = 1"
| "trie_depth (SymbolNode m) = Suc (Max (trie_depth ` \<Union> (fmran' ` (fmran' m))))"
  by pat_completeness auto
termination
proof -
  have "\<And>x. trie_depth_dom x"
  proof -
    fix x :: "('f ,'v) trie"
    show "trie_depth_dom x"
    proof (induction x)
      case (Leaf ts)
      then show ?case using trie_depth.domintros(1) by blast
    next
      case (SymbolNode m)
      then show ?case using trie_depth.domintros(2) by blast
    qed
  qed
  then show ?thesis by auto
qed

instantiation trie :: (type, type) size
begin
definition size_trie where
  size_trie_overloaded_def: "size_trie = Path_Indexing.trie_depth"
instance ..
end

lemma subtrie_size_lt [simp]: "m2 \<in> fmran' m1 \<Longrightarrow> tr \<in> fmran' m2 \<Longrightarrow> size tr < size (SymbolNode m1)"
proof -
  assume "m2 \<in> fmran' m1" and "tr \<in> fmran' m2"
  then have t_elem: "tr \<in> \<Union> (fmran' ` fmran' m1)" by auto
  then show ?thesis unfolding size_trie_overloaded_def using t_elem
    by (simp add: le_imp_less_Suc fmran'_alt_def)
qed

lemma subtrie_size_lt_alt [simp]: "m1 $$ s = Some m2 \<Longrightarrow> i \<in> fmdom' m2 \<Longrightarrow> size (m2 $$! i) < size (SymbolNode m1)"
  by (metis fmdom'_notI fmran'I option.collapse subtrie_size_lt)

text \<open>The collection of all terms in the leaves of the trie.\<close>

fun to_set :: "('f,'v) trie \<Rightarrow> ('f,'v) term set" where
  "to_set (Leaf ts) = ts"
| "to_set (SymbolNode m) = \<Union> (to_set ` \<Union> (fmran' ` (fmran' m)))"

section \<open>Preliminaries: paths and subtries\<close>

type_synonym 'f tpath = "('f symbol \<times> nat) list"

inductive subtrie_at_path :: "('f,'v) trie \<Rightarrow> 'f tpath \<Rightarrow> ('f,'v) trie \<Rightarrow> bool" where
  subtrie_at_path_empty: "subtrie_at_path tr [] tr"
| subtrie_at_path_step: "m1 $$ s = Some m2 \<Longrightarrow> m2 $$ i = Some tr1 \<Longrightarrow> subtrie_at_path tr1 ps tr2 \<Longrightarrow> subtrie_at_path (SymbolNode m1) ((s, i) # ps) tr2"

lemma subtrie_inj:
  assumes "subtrie_at_path tr1 p tr2"
      and "subtrie_at_path tr1 p tr3"
    shows "tr2 = tr3"
  using assms by (induct rule: subtrie_at_path.induct) (auto elim: subtrie_at_path.cases)

lemma fmran_empty': "fmran' {$$} = {}"
  by (simp add: fmran'_alt_def)

lemma update_entry_ran:
  assumes "m $$ k = None"
    shows "fmran' (m(k $$:= v)) = insert v (fmran' m)"
proof (rule set_eqI)
  fix x
  show "x \<in> fmran' (m(k $$:= v)) \<longleftrightarrow> x \<in> insert v (fmran' m)"
  proof
    assume "x \<in> fmran' (m(k $$:= v))"
    then show "x \<in> insert v (fmran' m)"
      by (metis fmlookup_ran'_iff fmupd_lookup insertCI option.sel)
  next
    assume "x \<in> insert v (fmran' m)"
    then show "x \<in> fmran' (m (k $$:= v))"
    proof
      assume "x = v"
      then show "x \<in> fmran' (m (k $$:= v))"
        using fmlookup_ran'_iff by fastforce
    next
      assume "x \<in> fmran' m"
      then show "x \<in> fmran' (m (k $$:= v))"
        by (metis assms fmlookup_ran'_iff fmupd_lookup option.distinct(1))
    qed
  qed
qed

lemma subtrie_at_nil: "\<not> subtrie_at_path (SymbolNode m) [] (Leaf ts)"
  using subtrie_at_path_empty subtrie_inj by blast

lemma subtrie_cons: "subtrie_at_path (SymbolNode m) ((s, i) # p) (Leaf ts) \<Longrightarrow> \<exists>a m2. m $$ s = Some a \<and> a $$ i = Some m2 \<and> subtrie_at_path m2 p (Leaf ts)"
  using subtrie_at_path.cases by fastforce

lemma subtrie_to_set:
  assumes "subtrie_at_path tr p (Leaf (insert t ts))"
    shows "t \<in> to_set tr"
  using assms proof (induction tr arbitrary: p)
  case (Leaf ts)
  then show ?case
    using subtrie_at_path.cases by auto 
next
  case (SymbolNode m)
  then show ?case 
  proof (cases p)
    case Nil
    then show ?thesis
      using SymbolNode.prems subtrie_at_path_empty subtrie_inj by blast 
  next
    case (Cons a ps)    
    obtain s i where "a = (s, i)"
      by (metis prod.exhaust)
    then obtain m2 tr2 where h1: "m $$ s = Some m2"
                         and h2: "m2 $$ i = Some tr2"
                         and h3: "subtrie_at_path tr2 ps (Leaf (insert t ts))"
      using SymbolNode Cons subtrie_cons by blast
    then have "t \<in> to_set tr2"
      by (meson SymbolNode.IH fmran'I)
    then show ?thesis
      using h1 h2  by (metis (no_types, lifting) UN_I fmran'I to_set.simps(2))
  qed
qed

lemma elim_sub:
  assumes "subtrie_at_path (SymbolNode m) ((s, i) # p) (Leaf (insert e ts))"
      and "m $$ s = Some m2"
      and "m2 $$ i = Some tr" 
    shows "subtrie_at_path tr p (Leaf (insert e ts))" 
  using assms subtrie_at_path.cases by fastforce

lemma subtrie_to_set_entry: "subtrie_at_path (SymbolNode m1) ((s, i) # p) (Leaf (insert t ts)) \<Longrightarrow>
    m1 $$ s = Some m2 \<Longrightarrow> m2 $$ i = Some tr \<Longrightarrow> t \<in> to_set tr"
  by (meson elim_sub subtrie_to_set)

lemma to_set_entry: "m1 $$ s = Some m2 \<Longrightarrow>
                     m2 $$ i = Some n \<Longrightarrow>
                     t \<in> to_set n \<Longrightarrow>
                     t \<in> to_set (SymbolNode m1)"
  by (metis (no_types, opaque_lifting) UN_I fmran'I to_set.simps(2))

inductive_cases subtrie_at_path_cases: "subtrie_at_path tr1 p tr2"
declare subtrie_at_path_cases [elim!]

lemma subtrie_string_1:
  assumes "subtrie_at_path (SymbolNode {s $$:= {i $$:= Leaf ts1}}) [(s, i)] (Leaf ts2)"
    shows "ts1 = ts2"
  using assms subtrie_at_path.cases subtrie_cons
  by force

lemma subtrie_string_2:
  assumes "subtrie_at_path (SymbolNode {s $$:= m}) ((s2, i) # p) (Leaf ts)"
    shows "s2 = s"
  using assms
  by (metis fmempty_lookup fmupd_lookup option.distinct(1) subtrie_cons)

lemma subtrie_string_3: 
  assumes "subtrie_at_path (SymbolNode {s $$:= m}) ((s2, i) # p) (Leaf ts)"
    shows "i \<in> fmdom' m"
  using assms
  by (metis fmdom'I fmupd_lookup option.sel subtrie_cons subtrie_string_2)

lemma subtrie_string_4:
  assumes "subtrie_at_path (SymbolNode {s $$:= {i $$:= Leaf ts1}}) p (Leaf ts2)"
    shows "p = [(s, i)]"
proof (cases p)
  case Nil
  then show ?thesis
    using assms subtrie_at_nil by blast
next
  case (Cons a rest)
  then obtain f j where h1: "a = (f, j)" by (cases a, blast)
  then show ?thesis
  proof -
    have "rest = []"
      using assms Cons h1    
      by (metis fmempty_lookup fmran'I fmran_empty' singletonD subtrie_cons subtrie_at_path_cases trie.distinct(1) update_entry_ran)
    moreover have t1: "f = s" 
      by (metis assms h1 local.Cons subtrie_string_2) 
    moreover have "j = i" 
      by (metis fmempty_lookup fmupd_lookup assms h1 local.Cons option.distinct(1) option.sel subtrie_cons)
    ultimately show ?thesis
      using h1 local.Cons by force
  qed
qed

inductive path_of_term :: "('f,'v) term \<Rightarrow>'f tpath \<Rightarrow> bool" where
  path_of_term_var: "path_of_term (Var x) [(Star, 0)]"
| path_of_term_const: "path_of_term (Fun f []) [(F f 0, 0)]"
| path_of_term_func: "f_args \<noteq> [] \<Longrightarrow> i < length f_args \<Longrightarrow> path_of_term (f_args ! i) p \<Longrightarrow> path_of_term (Fun f f_args) ((F f (length f_args), i) # p)"

lemma path_of_term_nil [simp]: "\<not> path_of_term t []"
  using path_of_term.cases by blast

lemma last_path_term: 
  assumes "path_of_term t p"
    shows "last p = (Star, 0) \<or> (\<exists>f. last p = (F f 0, 0))"
  using assms by (induct rule: path_of_term.induct) (auto intro: path_of_term.cases)

lemma path_var: "path_of_term (Var x) p \<longleftrightarrow> p = [(Star, 0)]"
  using path_of_term.simps path_of_term_var by fast

lemma path_const: "path_of_term (Fun f []) p \<longleftrightarrow> p = [(F f 0, 0)]"
  using path_of_term.simps path_of_term_const by auto

lemma path_func: 
  assumes "path_of_term (Fun f (a # f_args)) p " 
    shows "fst (hd p) = F f (Suc (length f_args)) \<and>
    snd (hd p) < Suc (length f_args) \<and> path_of_term ((a # f_args) ! snd (hd p)) (tl p)"
  using assms by (auto elim: path_of_term.cases)

inductive subterm_at_path :: "('f,'v) term \<Rightarrow>'f tpath \<Rightarrow> ('f,'v) term \<Rightarrow> bool" where
  subterm_at_path_empty: "subterm_at_path t [] t"
| subterm_at_path_step:  "i < length f_args \<Longrightarrow> f_args \<noteq> [] \<Longrightarrow> subterm_at_path (f_args ! i) ps t \<Longrightarrow> subterm_at_path (Fun f f_args) ((F f (length f_args), i) # ps) t"

lemma subterm_inj: 
  assumes "subterm_at_path tr p t1"
      and "subterm_at_path tr p t2"
    shows "t1 = t2" 
  using assms by (induct rule: subterm_at_path.induct) (auto elim: subterm_at_path.cases)

lemma subterm_at_path_path_of_term:
  assumes "subterm_at_path t p t2" 
      and "path_of_term t2 p2"
    shows "path_of_term t (p @ p2)" 
  using assms by (induction rule: subterm_at_path.induct) (auto intro: path_of_term_func)

lemma path_of_subterm: 
  assumes "subterm_at_path t p t2"
      and "path_of_term t (p @ p2)"
    shows "path_of_term t2 p2" 
  using assms by (induction rule: subterm_at_path.induct) (auto intro: path_of_term.cases)

lemma var_is_subterm_at_last: 
  assumes "path_of_term t (p @ [(Star, 0)])"
  obtains x where "subterm_at_path t p (Var x) "
  using assms
proof  (induct t arbitrary: p)
  case (Var x) 
  then have l1: "p = []"
    by (simp add: path_var)
  then have h1: "subterm_at_path (Var x) [] (Var x)"
    by (simp add: subterm_at_path_empty) 
  then show ?case
    using Var.prems(1) l1 by blast
next
  case (Fun f f_args)
  then show ?case
  proof (cases f_args)
    case Nil
    then have "\<not>path_of_term (Fun f []) (p @ [(Star, 0)])"
      by (simp add: path_const)
    then show ?thesis
      using Fun.prems local.Nil by blast
  next
    case c1: (Cons t ts)
    then show ?thesis
    proof (cases p)
      case Nil
      then have "path_of_term (Fun f (t # ts)) [(Star, 0)]"
        using Fun c1 by force
      then show ?thesis
        using path_func by fastforce
    next
      case c2: (Cons c cl)
      then have h1 : "path_of_term (Fun f (t # ts)) (c # cl @ [(Star, 0)])"
        using Fun.prems c1 by auto
      then show ?thesis using c1 c2 subterm_at_path_step path_func Fun.hyps  
        by (smt (verit) Fun.prems(1) list.distinct(1) list.sel(1) list.sel(3) nth_mem path_of_term.simps term.sel(4))
    qed
  qed
qed

lemma end_path_const:
  assumes "path_of_term t (p @ (F f 0, i) # q)"
    shows "i = 0 \<and> q = []"
  using assms
proof (induct p arbitrary: t )
  case Nil
  then show ?case 
    using Pair_inject path_of_term.cases by force
next
  case (Cons _ _)
  then show ?case 
    by (smt (verit, del_insts) Nil_is_append_conv append_Cons list.distinct(1) list.inject path_of_term.simps)
qed

lemma end_path_var:
  assumes "path_of_term t (p @ (Star, i) # q)"
    shows "i = 0 \<and> q = []"
  using assms proof (induct p arbitrary: t )
  case Nil
  then show ?case 
    using Pair_inject path_of_term.cases by force
next
  case (Cons _ _)
  then show ?case 
    by (smt (verit, del_insts) Nil_is_append_conv append_Cons list.distinct(1) list.inject path_of_term.simps)
qed

lemma fun_is_subterm_at_last:
  assumes "path_of_term t (p1 @ (F f n, i) # p2)"
    shows "\<exists>f_args. subterm_at_path t p1 (Fun f f_args) \<and> n = length f_args" 
  using assms
proof (induction p1 arbitrary: t )
  case Nil
  then show ?case 
    by (smt (verit) Pair_inject list.size(3) nth_Cons_0 path_of_term.cases self_append_conv2 subterm_at_path_empty symbol.distinct(1) symbol.inject) 
next
  case (Cons _ _)
  then show ?case 
    by (smt (verit, ccfv_SIG) Nil_is_append_conv append_Cons list.distinct(1) list.inject path_of_term.simps subterm_at_path_step)
qed

lemma sub_path_not_path:
  assumes "subterm_at_path t1 p t2"
    shows "\<not> path_of_term t3 p"
  using assms
proof (induction p arbitrary: t3 t1)
  case Nil
  then show ?case  by simp
next
  case (Cons a p)
  then show ?case
  proof (cases a)
    case (Pair s i)
    then show ?thesis  
      by (smt (verit, ccfv_SIG) Cons Pair_inject gr_implies_not0 list.distinct(1) list.sel(1,3) path_of_term.simps subterm_at_path.simps symbol.simps(1) symbol.simps(3))  
  qed   
qed

lemma exists_path: "\<exists> p. path_of_term t p"
proof (induction t)
  case (Var x)
  then show ?case
    using path_of_term_var by force 
next
  case (Fun f f_args)
  then show ?case
    by (metis length_greater_0_conv nth_mem path_of_term_const path_of_term_func) 
qed

lemma subsubterm_at_path: 
  assumes "subterm_at_path t p (Fun f f_args)" 
      and "i < (length f_args)"
    shows "subterm_at_path t (p @ [(F f (length f_args), i)]) (f_args ! i)"
  using assms
proof (induction p arbitrary: t)
  case Nil
  then show ?case
    by (metis append.left_neutral less_zeroE list.size(3) subterm_at_path_empty subterm_at_path_step subterm_inj) 
next
  case (Cons _ _)
  then show ?case 
    by (smt (verit, ccfv_threshold) append_Cons list.distinct(1) list.sel(3) subterm_at_path.simps)
qed

declare subtrie_at_path_cases [rule del]

lemma exists_leaf:
  assumes "e \<in> to_set tr " 
    shows "\<exists>ts p. subtrie_at_path tr p (Leaf (insert e ts))"
  using assms
proof (induct tr)
  case (Leaf ts)
  then show ?case
    by (metis insert_absorb subtrie_at_path_empty to_set.simps(1)) 
next
  case (SymbolNode m) then show ?case 
    by (fastforce  intro: subtrie_at_path_step  )
qed

section \<open>Invariants\<close>

text \<open>The structure of the trie (number and nature of children for each SymbolNode) is consistent with the symbols\<close>

inductive well_structured :: "('f, 'v) trie \<Rightarrow> bool"
  and well_structured_map_entry :: "'f symbol \<Rightarrow> (nat, ('f, 'v) trie) fmap \<Rightarrow> bool"
  where
    ws_node: "(\<forall>s. s \<in> fmdom' m \<longrightarrow> well_structured_map_entry s (m $$! s)) \<Longrightarrow> well_structured (SymbolNode m)"
  | wsme_var: "fmdom' m = {0} \<Longrightarrow> (\<forall>t. t \<in> fmran' m \<longrightarrow> (\<exists>s. t = Leaf s)) \<Longrightarrow> well_structured_map_entry Star m"
  | wsme_const: "fmdom' m = {0} \<Longrightarrow> (\<forall>t. t \<in> fmran' m \<longrightarrow> (\<exists>s. t = Leaf s)) \<Longrightarrow> well_structured_map_entry (F f 0) m"
  | wsme_func: "arity \<noteq> 0 \<Longrightarrow> fmdom' m = {..< arity} \<Longrightarrow> (\<forall>t. t \<in> fmran' m \<longrightarrow> well_structured t) \<Longrightarrow> well_structured_map_entry (F f arity) m"

lemma ws_dom_var: 
  assumes "well_structured (SymbolNode m)"
      and "m $$ Star = Some m2"
    shows "fmdom' m2 = {0} \<and> (\<exists>ts. m2 $$ 0 = Some (Leaf ts))"
proof - 
  from assms(1) have "\<forall>s. s \<in> fmdom' m \<longrightarrow> well_structured_map_entry s (m $$! s)"
    by (simp add: well_structured.simps)
  then have 1:"well_structured_map_entry Star m2"
    by (metis fmdom'I assms(2) option.sel)
  then have fmd: " fmdom' m2 = {0}"
    by (simp add: well_structured_map_entry.simps)
  also obtain s where "m2 $$ 0 = Some (Leaf s)"
    by (metis "1" fmlookup_dom'_iff fmran'I singletonI symbol.distinct(1) well_structured_map_entry.simps)
  thus ?thesis
    by (simp add: fmd)
qed

lemma ws_dom_const: 
  assumes "well_structured (SymbolNode m)"
      and "m $$ F f 0 = Some a"
    shows "fmdom' a = {0} \<and> (\<exists>ts. a $$ 0 = Some (Leaf ts))"
proof- 
  from assms(1) have h1: "\<forall>s. s \<in> fmdom' m \<longrightarrow> well_structured_map_entry s (m $$! s)"
    by (simp add: well_structured.simps)
  from assms(2) have " F f 0 \<in> fmdom' m"
    by (simp add: fmdom'I)
  then have h2: "well_structured_map_entry (F f 0) a"
    using assms(2) h1 by (metis option.sel)
  then have fmd: "fmdom' a = {0}"
    by (simp add: well_structured_map_entry.simps)
  also have "(\<exists>ts. a $$ 0 = Some (Leaf ts))"
    by (metis (no_types, lifting) h2 fmdom'E fmdom'I fmran'I insertI1 singletonD symbol.inject well_structured_map_entry.simps)
  thus ?thesis
    by (simp add: fmd)
qed

lemma ws_dom_fun: 
  assumes "well_structured (SymbolNode m)"
      and "m $$ F f (length f_args) = Some a"
      and "i < length f_args"
    shows "i \<in> fmdom' a"
proof -
  from assms(1) have h: "\<forall>s. s \<in> fmdom' m \<longrightarrow> well_structured_map_entry s (m $$! s)"
    using well_structured.cases by auto
  from assms(2) have "F f (length f_args) \<in> fmdom' m"
    by (simp add: fmdom'I)
  then have "well_structured_map_entry (F f (length f_args)) a"
    using assms(2) h by (metis option.sel)
  thus ?thesis
    using assms(3) well_structured_map_entry.cases by fastforce 
qed

lemma ws_dom_fun2: 
  assumes "well_structured (SymbolNode m)"
      and "m $$ F f (Suc (length f_args)) = Some a"
      and "i \<in> fmdom' a"
    shows "i < Suc (length f_args)"
proof -
  from assms(1) have h: "\<forall>s. s \<in> fmdom' m \<longrightarrow> well_structured_map_entry s (m $$! s)"
    using well_structured.cases by auto
  from assms(2) have "F f (Suc (length f_args)) \<in> fmdom' m"
    by (simp add: fmdom'I)
  then have "well_structured_map_entry (F f (Suc (length f_args))) a"
    using assms(2) h by (metis option.sel)
  thus ?thesis
    using assms(3) well_structured_map_entry.cases by auto
qed

lemma key_map_entry:
  assumes "well_structured (SymbolNode m)" 
      and "m $$ F f (length largs) = Some a " 
      and "largs \<noteq> [] "
      and "i \<in> fmdom' a"
    shows "i < length largs "
proof-
  have "F f (length largs) \<in> fmdom' m"
    by (simp add: assms(2) fmdom'I) 
  then have "well_structured_map_entry (F f (length largs)) (m $$! (F f (length largs)))"
    using assms(1) well_structured.cases by auto
  then have "fmdom' a = {..<length largs} \<and> (\<forall>t. t \<in> fmran' a \<longrightarrow> well_structured t) "
    by (simp add: assms(2) assms(3) well_structured_map_entry.simps)
  then show ?thesis
    using assms(4) by blast
qed

lemma key_map_entry_simp:
  assumes "well_structured (SymbolNode m)" 
      and "m $$ F f (length largs) = Some a" 
      and "largs \<noteq> []"
    shows "i \<in> fmdom' a \<longleftrightarrow> i < length largs"
  using assms by (meson key_map_entry ws_dom_fun) 

lemma ws_fmdom': 
  assumes "well_structured (SymbolNode m)"
     and "m $$ F f (length f_args) = Some a"
     and "f_args \<noteq> []"
   shows "fmdom' a = {..<length f_args}"
  using assms
  by (metis fmdom'I length_0_conv option.sel symbol.distinct(1) symbol.inject trie.inject(2) well_structured.cases well_structured_map_entry.cases)

lemma not_well_structured_leaf: "\<not> well_structured (Leaf s)" 
  using well_structured.simps by blast

lemma well_structured_drop [simp]:
  assumes "well_structured (SymbolNode m)"
    shows "well_structured (SymbolNode (fmdrop symb m))"
  using assms  by (metis Diff_iff fmdom'_drop fmdom'_notI fmlookup_drop trie.sel(3) well_structured.cases ws_node)

lemma well_structured_split:  
  assumes "well_structured (SymbolNode m)" 
      and "well_structured (SymbolNode {symb $$:= a})" 
    shows "well_structured (SymbolNode (m(symb $$:= a)))"
  using assms by (metis fmdom'_fmupd fmupd_lookup insert_iff trie.sel(3) well_structured.cases ws_node)

text \<open>A term is stored in a leaf only if that leaf is located on a path of the term\<close>

definition sound_storage :: "('f, 'v) trie \<Rightarrow> bool" where
  "sound_storage tr = (\<forall>t p. (\<exists>s. subtrie_at_path tr p (Leaf (insert t s))) \<longrightarrow> path_of_term t p)"

text \<open>A term stored in the trie must appear in all the leaves located on paths of that term\<close>

definition complete_storage :: "('f, 'v) trie \<Rightarrow> bool" where
  "complete_storage tr = (\<forall>t\<in>to_set tr. \<forall>p. path_of_term t p \<longrightarrow> (\<exists>s. subtrie_at_path tr p (Leaf (insert t s))))"

text \<open>The trie contains no empty subtries\<close>

inductive minimal_storage :: " ('f,'v) trie\<Rightarrow> bool" where
  minimal_storage_leaf: "ts \<noteq> {} \<Longrightarrow> minimal_storage (Leaf ts)"
| minimal_storage_node: "(\<forall>m2 \<in> fmran' m. \<forall>tr \<in> fmran' m2. minimal_storage tr \<and> tr \<noteq> empty_trie) \<Longrightarrow> minimal_storage (SymbolNode m)" 

text \<open>The empty trie satisfies all four invariants\<close>

lemma well_structured_empty_trie [simp]: "well_structured empty_trie"
  by (simp add: ws_node)

lemma sound_empty_trie [simp]: "sound_storage empty_trie"
  by (metis fmempty_lookup list.exhaust option.simps(3) prod.exhaust sound_storage_def subtrie_at_nil subtrie_cons)

lemma complete_empty_trie [simp]: "complete_storage empty_trie"
  by (metis complete_storage_def fmempty_lookup fmran'E mem_simps(8) option.simps(3) to_set.simps(2))

lemma minimal_empty_trie [simp]: "minimal_storage empty_trie"
  by (metis fmempty_lookup fmran'E minimal_storage.intros(2) option.distinct(1))

lemma subtrie_at_nil_iff_eq: "subtrie_at_path tr [] str \<longleftrightarrow> str = tr"
  using subtrie_at_path_empty subtrie_inj by blast

subsection \<open>Inductive invariants\<close>

text \<open>complete storage and sound storage must be expressed as inductive invariants.
       For this we must take into account the position of a node within the trie\<close>

definition complete_storage_from_position :: "('f, 'v) trie \<Rightarrow> 'f tpath \<Rightarrow> bool" where
  "complete_storage_from_position tr p = (\<forall>t . t \<in> to_set tr \<longrightarrow> (\<forall> p2.  path_of_term t (p @ p2) \<longrightarrow> (\<exists>s. subtrie_at_path tr p2 (Leaf (insert t s)))))"

lemma complete_storage_alt_def: "complete_storage t = complete_storage_from_position t []"
  unfolding complete_storage_def complete_storage_from_position_def by auto

lemma complete_storage_from_position_subtrie:
  assumes "complete_storage_from_position (SymbolNode m1) p"
      and "m1 $$ f = Some m2"
      and "m2 $$ i = Some tr"
    shows "complete_storage_from_position tr (p @ [(f, i)])"
proof -
  have "\<And> t p2. t \<in> to_set tr \<Longrightarrow> path_of_term t (p @ [(f, i)] @ p2) \<Longrightarrow> \<exists>s. subtrie_at_path tr p2 (Leaf (insert t s))"
  proof -
    fix t p2
    assume elem: "t \<in> to_set tr" and path: "path_of_term t (p @ [(f, i)] @ p2)"
    have elem': "t \<in> to_set (SymbolNode m1)"
      by (metis (no_types, opaque_lifting) UN_iff fmlookup_ran'_iff to_set.simps(2) assms(2,3) elem)
    have path': "path_of_term t (p @ [(f, i)] @ p2)" using path by blast
    have "\<exists>s. subtrie_at_path (SymbolNode m1) ((f, i) # p2) (Leaf (insert t s))" using assms(1) elem' path' unfolding complete_storage_from_position_def by force
    then show "\<exists>s. subtrie_at_path tr p2 (Leaf (insert t s))" using assms(2,3) subtrie_at_path.cases by fastforce
  qed
  then show ?thesis unfolding complete_storage_from_position_def by auto
qed

definition sound_storage_from_position :: "('f, 'v) trie \<Rightarrow> 'f tpath \<Rightarrow> bool" where
  "sound_storage_from_position tr p = (\<forall>t p2 s. subtrie_at_path tr p2 (Leaf (insert t s)) \<longrightarrow> path_of_term t (p @ p2))"

lemma sound_storage_alt_def: "sound_storage t = sound_storage_from_position t []"
  unfolding sound_storage_def sound_storage_from_position_def by auto

lemma sound_storage_from_position_subtrie:
  assumes "sound_storage_from_position (SymbolNode m1) p"
      and "m1 $$ f = Some m2"
      and "m2 $$ i = Some tr"
    shows "sound_storage_from_position tr (p @ [(f, i)])"
  using assms(1,2,3) subtrie_at_path_step unfolding sound_storage_from_position_def 
  by (metis append.assoc append_Cons append_Nil)

lemma non_empty_to_set_subtrie: "to_set tr \<noteq> {} \<Longrightarrow> \<exists>p t s. subtrie_at_path tr p (Leaf (insert t s))"
  by (meson all_not_in_conv exists_leaf)

lemma no_subtrie_in_empty_trie : "\<not> subtrie_at_path empty_trie p (Leaf S)"
  using subtrie_at_path.cases by fastforce

section \<open>Retrieval operations\<close>

fun var_terms :: "(('f symbol , (nat, ('f, 'v) trie) fmap) fmap) \<Rightarrow> ('f, 'v) term set" where 
  "var_terms m = (case m $$ Star of
                    None \<Rightarrow> {}
                  | Some m2 \<Rightarrow> to_set (m2 $$! 0))"

fun retrieve_generalizations :: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term set" where
  "retrieve_generalizations (Leaf ts) t = undefined"
| "retrieve_generalizations (SymbolNode m) (Var x) = var_terms m"
| "retrieve_generalizations (SymbolNode m) (Fun f f_args) =
     var_terms m \<union> (case m $$ (F f (length f_args)) of
                      None \<Rightarrow> {}
                    | Some m2 \<Rightarrow> if f_args = []
                                 then to_set (m2 $$! 0)
                                 else \<Inter> i \<in> fmdom' m2. retrieve_generalizations (m2 $$! i) (f_args ! i))"

fun retrieve_unifications :: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term set" where
  "retrieve_unifications (Leaf ts) t = undefined"
| "retrieve_unifications (SymbolNode m) (Var x) = to_set (SymbolNode m)"
| "retrieve_unifications (SymbolNode m) (Fun f f_args) =
     var_terms m \<union> (case m $$ (F f (length f_args)) of
                      None \<Rightarrow> {}
                    | Some m2 \<Rightarrow> if f_args = []
                                 then to_set (m2 $$! 0)
                                 else \<Inter> i \<in> fmdom' m2. retrieve_unifications (m2 $$! i) (f_args ! i))"

fun retrieve_instances :: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term set" where
  "retrieve_instances (Leaf ts) t = undefined"
| "retrieve_instances (SymbolNode m) (Var x) = to_set (SymbolNode m)"
| "retrieve_instances (SymbolNode m) (Fun f f_args) =
     (case m $$ (F f (length f_args)) of
        None \<Rightarrow> {}
      | Some m2 \<Rightarrow> if f_args = []
                   then to_set (m2 $$! 0)
                   else \<Inter> i \<in> fmdom' m2. retrieve_instances (m2 $$! i) (f_args ! i))"

fun retrieve_variants:: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term set" where
  "retrieve_variants (Leaf ts) t = undefined"
| "retrieve_variants (SymbolNode m) (Var x) = var_terms m"
| "retrieve_variants (SymbolNode m) (Fun f f_args) =
     (case m $$ (F f (length f_args)) of
        None \<Rightarrow> {}
      | Some m2 \<Rightarrow> if f_args = []
                   then to_set (m2 $$! 0)
                   else \<Inter> i \<in> fmdom' m2. retrieve_variants (m2 $$! i) (f_args ! i))"

lemma var_terms_in_set: 
  assumes "well_structured (SymbolNode m)"
    shows "var_terms m \<subseteq> to_set (SymbolNode m)"
proof -
  have wsme: "\<And>s. s \<in> fmdom' m \<Longrightarrow> well_structured_map_entry s (m $$! s)"
    using well_structured.cases assms by blast
  show ?thesis
  proof (cases "m $$ Star")
    case None
    then show ?thesis by force
  next
    case (Some m2)
    then have "well_structured_map_entry Star m2"
      by (metis fmdom'I option.sel wsme)
    then have dom: "fmdom' m2 = { 0 }"
      by (simp add: well_structured_map_entry.simps)
    have "m2 \<in> fmran' m"
      by (meson Some fmran'I)
    then have "to_set (m2 $$! 0) \<subseteq> \<Union> (to_set ` \<Union> (fmran' ` (fmran' m)))"
      by (metis Sup_upper UN_I dom fmdom'_notI fmran'I image_eqI insertI1 option.collapse)
    then show ?thesis
      using Some by auto
  qed
qed

lemma simp_storage :
  assumes "complete_storage_from_position tr p"
      and "sound_storage_from_position tr p"
      and "e \<in> to_set tr "
    shows "(path_of_term e (p @ p') \<longleftrightarrow>  (\<exists>s. subtrie_at_path tr p' (Leaf (insert e  s)))) "
  using assms complete_storage_from_position_def sound_storage_from_position_def 
  by metis  

lemma not_sound_storage : 
  assumes "well_structured (SymbolNode m1)"
      and "sound_storage_from_position (SymbolNode m1) p "
      and "subterm_at_path e p t "
      and "to_symbol t \<noteq> (to_symbol (Fun f largs))" 
      and "e \<in> to_set (m2 $$! 0)" 
      and "m1 $$ F f (length largs) = Some m2"
    shows "False"
  using assms 
proof - 
  obtain p3 s where h0: "subtrie_at_path (m2 $$! 0) p3 (Leaf (insert e s))"
    using assms(5) exists_leaf by metis
  then obtain p4 where h1:"( path_of_term (Fun f largs)( (F f (length largs) ,0)#p4))"
    by (metis exists_path length_greater_0_conv list.size(3) path_of_term_const path_of_term_func)
  then have h2: "  (\<exists>s. subtrie_at_path (SymbolNode m1) ((F f (length largs), 0) # p3) (Leaf (insert e s))) \<longrightarrow>
       path_of_term e (p @ (F f (length largs), 0) # p3) "
    using assms(2) sound_storage_from_position_def by metis
  then obtain s where h3: " subtrie_at_path (SymbolNode m1) ((F f (length largs), 0) # p3) (Leaf (insert e s))"
    by (metis assms(1) assms(6) fmdom'I fmdom'_notI h0 length_greater_0_conv list.size(3) option.collapse subtrie_at_path_step ws_dom_const ws_dom_fun)
  then have " path_of_term e (p @ (F f (length largs), 0) # p3)"
    using assms(2) sound_storage_from_position_def  by metis
  then show ?thesis
    by (smt (verit, best) assms(3) assms(4) list.sel(1) list.size(3) path_of_term.simps prod.inject path_of_subterm symbol.distinct(1) to_symbol.simps(2))
qed

lemma not_sound_storage_at_star: 
  assumes "well_structured (SymbolNode m1)"
      and "sound_storage_from_position (SymbolNode m1) p"
      and "subterm_at_path e p (Fun f f_args) "
      and "e \<in> to_set (m2 $$! 0)"
      and "m1 $$ Star = Some m2"
    shows "False"
  using assms  not_sound_storage
proof -
  have  H1: "(\<exists>s. subtrie_at_path (SymbolNode m1) [(symbol.Star, 0)] (Leaf (insert e s)))" 
  proof -   
    have "\<exists> s. m2 $$! 0 = Leaf s"
      using assms(1,5) ws_dom_var by fastforce
    then show ?thesis
      by (metis assms(1,4,5) fmdom'_notI insert_absorb insert_iff option.collapse subtrie_at_path_empty subtrie_at_path_step to_set.simps(1) ws_dom_var)
  qed
  then have "\<forall>p2 t. (\<exists>s. subtrie_at_path (SymbolNode m1) p2 (Leaf (insert t s))) \<longrightarrow> path_of_term t (p @ p2)"
    using assms(2) sound_storage_from_position_def by metis 
  then have "(\<exists>s. subtrie_at_path (SymbolNode m1) [(symbol.Star, 0)] (Leaf (insert e s))) \<longrightarrow> path_of_term e (p @ [(symbol.Star, 0)])"
    by metis
  then have "path_of_term e (p @ [(symbol.Star, 0)])"
    using H1 by blast   
  then show ?thesis
    using assms(3) subterm_inj var_is_subterm_at_last 
    by (metis term.distinct(1))
qed

subsection \<open>Correctness of retrieval of generalizations\<close>

lemma retrieve_generalizations_in_set:
  assumes "well_structured tr"
      and "e \<in> retrieve_generalizations tr t"
    shows "e \<in> to_set tr"
  using assms 
proof (induct tr arbitrary: t rule: trie.induct)
  case (Leaf _)
  then show ?case by (simp add: not_well_structured_leaf)
next
  case (SymbolNode m)
  then show ?case
  proof (cases t)
    case (Var x)
    then show ?thesis
      using SymbolNode.prems(1,2) subset_iff var_terms_in_set by fastforce
  next 
    case (Fun f f_args) then show ?thesis 
    proof (cases "e \<in> var_terms m")
      case True
      then show ?thesis
        by (meson SymbolNode.prems(1) subsetD var_terms_in_set) 
    next
      case False
      then show ?thesis  
      proof (cases "m $$ F f (length f_args)")
        case None
        then have "e \<in> {}"
          using SymbolNode Fun False by simp 
        then show ?thesis by simp
      next
        case (Some m2)
        then show ?thesis
        proof (cases f_args)
          case Nil
          then show ?thesis
            by (smt (verit, ccfv_threshold) SymbolNode.prems(1,2) Fun Some UN_iff UN_iff Un_iff fmdom'I fmdom'_notI fmdom'_notI fmran'I fmran'I insertI1 list.size(3) option.case_eq_if option.collapse option.sel retrieve_generalizations.simps(3) subsetD symbol.distinct(1) symbol.inject to_set.simps(2) trie.sel(3) var_terms_in_set well_structured.cases well_structured_map_entry.simps)        next
          case (Cons aa list) 
          then have h1: "e \<in> retrieve_generalizations (SymbolNode m)  (Fun f (aa # list))" 
            using SymbolNode(3) Fun Cons by simp
          then consider
              (a) "e \<in> var_terms m"
            | (b) "e \<in> (\<Inter>i\<in>fmdom' m2. retrieve_generalizations (m2 $$! i) ((aa # list) ! i))"
            using Some Cons by fastforce
          then show ?thesis
          proof cases
            case a
            then show ?thesis by (meson SymbolNode.prems(1) subsetD var_terms_in_set) 
          next
            case b
            then show ?thesis
            proof -
              have h0: "0 \<in> fmdom' m2"
                by (metis SymbolNode.prems(1) Some fmdom'I insertI1 lessThan_Suc_eq_insert_0 old.nat.exhaust option.sel trie.inject(2) well_structured.cases well_structured_map_entry.cases)
              then have h1: "well_structured (m2 $$! 0)"
                using SymbolNode.prems well_structured.simps
                by (metis Some fmdom'I fmdom'_notI fmran'I length_0_conv list.simps(3) local.Cons option.collapse option.sel symbol.inject symbol.simps(3) trie.inject(2) well_structured_map_entry.cases)
              then have "e \<in> to_set (m2 $$! 0)"
                by (smt (verit, ccfv_threshold) SymbolNode.hyps INT_iff Some h0 b fmdom'_notI fmran'I option.collapse)
              then have "\<exists>m2\<in>fmran' m. \<exists>n\<in>fmran' m2. e \<in> to_set n"
                by (meson Some fmdom'_notI fmran'I h0 option.exhaust_sel)
              then show ?thesis by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma retrieve_generalizations_sound:
  assumes "well_structured tr"
      and "sound_storage_from_position tr p"
      and "subterm_at_path e p e' "
      and "e \<in> retrieve_generalizations tr t"
    shows "linear_instance t e'"
  using assms
proof  (induct arbitrary: e p e' rule: retrieve_generalizations.induct)
  case (1 s t)
  then show ?case
    by (simp add: not_well_structured_leaf)
next
  case (2 m x)
  then show ?case
  proof (cases "m $$ Star" )
    case None
    then show ?thesis
      using "2.prems"(4) by fastforce
  next
    case (Some a)
    then show ?thesis
    proof (cases e')
      case (Var _)
      then show ?thesis
        by (simp add: li_var)
    next
      case (Fun g g_args)
      then show ?thesis
        using "2.prems"(1-4) Some not_sound_storage_at_star by fastforce
    qed
  qed
next
  case (3 m f f_args)
  then show ?case
  proof(cases e')
    case (Var x)
    then show ?thesis
      by (simp add: li_var)
  next
    case (Fun g g_args)
    show ?thesis
    proof (cases "(f = g \<and> length f_args = length g_args)")
      case True
      then consider (a) "e \<in> var_terms m"
        | (b) "e \<in> (case m $$ F f (length f_args) of
                                None \<Rightarrow> {}
                              | Some m2 \<Rightarrow> if f_args = []
                                           then to_set (m2 $$! 0)
                                           else \<Inter>i\<in>fmdom' m2. retrieve_generalizations (m2 $$! i) (f_args ! i))"
        using "3.prems"(4) by fastforce
      then show ?thesis
      proof cases
        case a
        then show ?thesis
          by (metis (no_types, lifting) "3.prems"(1-3) Fun empty_iff not_sound_storage_at_star option.collapse option.split_sel_asm var_terms.simps)
      next
        case b
        then show ?thesis
        proof (cases "m $$ F f (length f_args)")
          case None
          then show ?thesis
            using b by auto
        next
          case (Some m2)
          then show ?thesis
          proof (cases f_args)
            case Nil
            then show ?thesis
              using "3.prems"(1-3) Fun Some b linear_instance.simps  not_sound_storage True by fastforce
          next
            case (Cons _ _)
            have th0: "e'= Fun f g_args" by (simp add: Fun True)
            then show ?thesis 
            proof(safe, rule_tac li_func)
              show "length f_args = length g_args"   by (simp add: True)
              show th2: "\<forall>i < length f_args. linear_instance (f_args ! i) (g_args ! i)"
              proof safe
                fix i
                show "i < length f_args \<Longrightarrow> linear_instance (f_args ! i) (g_args ! i)"
                proof-
                  assume h1: "i < length f_args"
                  have ws:" well_structured (m2 $$! i)" using ws_dom_fun
                    by (metis "3.prems"(1) Some fmdom'I fmdom'_notI fmran'I h1 length_0_conv list.simps(3) local.Cons option.collapse option.sel symbol.inject symbol.simps(3) trie.inject(2) well_structured.cases well_structured_map_entry.cases)
                  then have sond: "sound_storage_from_position (m2 $$! i) (p @ [(F f (length g_args), i)])"
                    by (metis "3.prems"(1,2) Some True h1 fmdom'_notI option.collapse sound_storage_from_position_subtrie ws_dom_fun)
                  then  have  subter: "  subterm_at_path e (p@ [(F f (length g_args),i)]) (g_args ! i) "
                    using "3.prems"(3) True h1 subsubterm_at_path th0 by fastforce
                  then show ?thesis
                  proof-
                    have "i \<in> fmdom' m2"
                      by (meson "3.prems"(1) Some h1 ws_dom_fun)
                    then show ?thesis
                      using "3.hyps" Cons Some b sond subter ws by auto
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    next
      case False
      then consider (a) "e \<in> var_terms m"
        | (b) "e \<in> (case m $$ F f (length f_args) of
                                None \<Rightarrow> {}
                              | Some m2 \<Rightarrow> if f_args = []
                                           then to_set (m2 $$! 0)
                                           else \<Inter>i\<in>fmdom' m2. retrieve_generalizations (m2 $$! i) (f_args ! i))"
        using "3.prems"(4) by fastforce
      then show ?thesis
      proof cases
        case a
        then show ?thesis
          by (metis (no_types, lifting) "3.prems"(1-3) Fun insert_Diff insert_not_empty not_sound_storage_at_star option.case_eq_if option.collapse var_terms.simps)
      next
        case b
        then show ?thesis
        proof(cases "m $$ F f (length f_args)")
          case None
          then show ?thesis
            using b by fastforce
        next
          case (Some a)
          then show ?thesis
          proof (cases f_args)
            case Nil
            then show ?thesis 
              by (smt (verit, best) "3.prems"(1-3) False Fun Some b not_sound_storage option.simps(5) symbol.inject to_symbol.simps(2))
          next
            case c: (Cons _ _)
            then have dom: "fmdom' a = {..<length f_args}"
              by (metis "3.prems"(1) Some list.simps(3) ws_fmdom')
            then have h: "\<forall>i\<in>fmdom' a. e \<in> retrieve_generalizations (a $$! i) (f_args ! i)"
              using False Some b  c   by (simp )
            then have j:  "f_args \<noteq> []"using c  by auto
            have  " \<forall>i < length f_args. \<exists>ts p. subtrie_at_path (SymbolNode m) ((F f (length f_args), i) # p) (Leaf (insert e ts))"
            proof (intro allI impI)
              fix i 
              assume h1: "i < length f_args"
              obtain m3 where h3: "a $$ i = Some m3"
                using dom fmdom'_notI h1 by fastforce
              have ws: "well_structured (a $$! i)"
                by (metis "3.prems"(1) Some fmdom'I fmran'I h3 j length_greater_0_conv list.size(3) option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.simps)
              have "e \<in> retrieve_generalizations (a $$! i) (f_args ! i)"
                by (meson fmdom'I h h3)
              then have ts: "e \<in> to_set m3"
                using retrieve_generalizations_in_set ws
                using h3 by auto 
              show "\<exists>s p. subtrie_at_path (SymbolNode m) ((F f (length f_args), i) # p) (Leaf (insert e s))"
                by (meson Some exists_leaf h3 subtrie_at_path_step ts)
            qed
            then show ?thesis  
              by (metis "3.prems"(2-3) False Fun fun_is_subterm_at_last j length_greater_0_conv sound_storage_from_position_def subterm_inj term.inject(2))
          qed
        qed
      qed
    qed
  qed
qed


lemma retrieve_generalizations_complete_var:
  assumes "complete_storage_from_position (SymbolNode m) p"
      and "sound_storage_from_position (SymbolNode m) p "
      and "e \<in> to_set (SymbolNode m) " 
      and "subterm_at_path e p (Var x)" 
    shows "e \<in> retrieve_generalizations (SymbolNode m) t"
  using assms
proof- 
  have "path_of_term  (Var x) [(Star,0)]"
    by (simp add: path_of_term_var)
  then have  "path_of_term e (p @ [(Star,0)])"
    using assms(4) subterm_at_path_path_of_term by auto
  then have sub_fin: " \<exists>s. subtrie_at_path (SymbolNode m) [(symbol.Star, 0)] (Leaf (insert e s)) "
    using assms(1-3) simp_storage by blast
  then show ?thesis
  proof (cases t)
    case (Var x)
    then show ?thesis
    proof(cases "m $$ Star")
      case None
      then show ?thesis
        using sub_fin
          subtrie_cons by fastforce 
    next
      case (Some m2)
      then show ?thesis
        using Var sub_fin subtrie_cons
          subtrie_to_set_entry by fastforce   
    qed
  next
    case (Fun g g_args)
    then have "t = Fun g g_args"
      by (simp add: Fun)
    then have "e \<in> (case m $$ Star of None \<Rightarrow> {} | Some m2 \<Rightarrow> to_set (m2 $$! 0))"
    proof (cases "m $$ Star")
      case None
      then show ?thesis
        using subtrie_cons sub_fin
        by force  
    next
      case (Some m2)
      then show ?thesis
        using  subtrie_cons sub_fin subtrie_to_set_entry by fastforce 
    qed
    then show ?thesis
      using Fun by auto  
  qed
qed

lemma retrieve_generalizations_complete:
  assumes "linear_instance t e'"
      and "well_structured tr "
      and "complete_storage_from_position tr p "
      and "sound_storage_from_position tr p "
      and "e \<in> to_set tr " 
      and "subterm_at_path e p e' "
    shows "e \<in> retrieve_generalizations tr t"
  using assms
proof (induction arbitrary: e p e' rule: retrieve_generalizations.induct)
  case (1 s t)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x)
  then show ?case
  proof (cases e')
    case (Var _)
    then show ?thesis
      by (metis "2.prems"(3-6) retrieve_generalizations_complete_var)
  next
    case (Fun g g_args)
    then show ?thesis
      using "2.prems"(1) linear_instance.cases by blast 
  qed
next
  case (3 m f f_args)
  then show ?case
  proof (cases e')
    case (Var x)
    then show ?thesis
      by (metis "3.prems"(3-6) retrieve_generalizations_complete_var) 
  next
    case (Fun g g_args)
    then have h1: "g = f \<and> length g_args  = length f_args"
      by (metis "3.prems"(1) linear_instance.simps term.distinct(1) term.inject(2))
    then have "e \<in> (case m $$ F f (length f_args) of None \<Rightarrow> {}
                    | Some m2 \<Rightarrow> if f_args = []
                                 then to_set (m2 $$! 0)
                                 else \<Inter>i\<in>fmdom' m2. retrieve_generalizations (m2 $$! i) (f_args ! i))" 
    proof (cases "m $$ F f (length f_args)")
      case None
      then show ?thesis
      proof(simp) 
        assume "m $$ F f (length f_args) = None"
        show False
          by (smt (verit, del_insts) "3.prems"(2-6) Fun None Pair_inject exists_leaf fmdom'I fmdom'_notI h1 list.inject list.size(3) path_of_term.simps sound_storage_from_position_def path_of_subterm subtrie_at_path.simps term.distinct(1) to_symbol.simps(2) trie.sel(3) not_well_structured_leaf)
      qed
    next
      case (Some m2)
      then show ?thesis
      proof (cases f_args)
        case Nil
        then have " \<exists>ts. subtrie_at_path (SymbolNode m) [(F f 0, 0)] (Leaf (insert e ts)) "
          by (metis "3.prems"(3) "3.prems"(4) "3.prems"(5) "3.prems"(6) Fun h1 length_0_conv path_of_term_const simp_storage subterm_at_path_path_of_term)
        then show ?thesis
          using Nil Some Fun
            subtrie_cons subtrie_to_set_entry by fastforce
      next
        case (Cons _ _)
        then have not_nil: "f_args \<noteq> []" by auto
        then  have "e \<in> ( \<Inter>i\<in>fmdom' m2. retrieve_generalizations (m2 $$! i) (f_args ! i))" 
        proof(clarsimp)
          fix i
          assume dom: "i \<in> fmdom' m2"
          then have  ws: "well_structured (m2 $$! i)"
            by (metis "3.prems"(2) not_nil Some dom fmdom'I fmdom'_notI fmran'I length_0_conv option.collapse option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.cases)
          have com: "complete_storage_from_position (m2 $$! i) (p @ [(F f (length f_args), i)])"
            by (metis "3.prems"(3) Some dom complete_storage_from_position_subtrie fmdom'_notI option.collapse)
          have so: "sound_storage_from_position (m2 $$! i) (p @ [(F f (length f_args), i)])"
            by (metis "3.prems"(4) Some dom fmdom'_notI option.collapse sound_storage_from_position_subtrie) 
          have  li: "linear_instance (f_args ! i) (g_args ! i)"
            by (metis "3.prems"(1) "3.prems"(2) not_nil Fun Some dom key_map_entry linear_instance.simps term.distinct(1) term.sel(4))
          have st: "subterm_at_path e (p @ [(F f (length f_args),i)]) (g_args ! i)"
            by (smt (verit, ccfv_SIG) "3.prems"(2) "3.prems"(6) not_nil Fun Some Suc_length_conv dom gr0_implies_Suc h1 key_map_entry length_greater_0_conv subsubterm_at_path)
          have ts: "e \<in> to_set (m2 $$! i)" 
          proof - 
            obtain p3 where "path_of_term (Fun f g_args) ((F f (length g_args), i) # p3)"
              by (metis (no_types, lifting) "3.prems"(6) Fun append.assoc append_Cons exists_path h1 path_of_subterm st subterm_at_path_path_of_term)
            then have" path_of_term e (p @ ((F f (length f_args), i) # p3))"
              using "3.prems"(6) Fun h1 subterm_at_path_path_of_term by auto
            then show ?thesis
              by (meson "3.prems"(3-5) Some dom fmdom'_notI option.exhaust_sel simp_storage subtrie_to_set_entry)
          qed
          then show "e \<in> retrieve_generalizations (m2 $$! i) (f_args ! i)"
            using "3.IH" not_nil Some com li so st ws dom by blast
        qed
        then show ?thesis
          using Cons Some by force 
      qed
    qed
    then show ?thesis
      by simp 
  qed
qed


subsection \<open>Correctness of retrieval of instances\<close>

lemma retrieve_instances_in_set:
  assumes ws :"well_structured tr"
      and ret: "e \<in> retrieve_instances tr t"
    shows "e \<in> to_set tr"
  using assms
proof (induct tr arbitrary: t rule:trie.induct)
  case (Leaf _) then
  show ?case  by (simp add: not_well_structured_leaf)
next
  case (SymbolNode m1)
  then show ?case
  proof (cases t)
    case (Var _)
    then show ?thesis
      using SymbolNode.prems(1) SymbolNode.prems(2) var_terms_in_set by fastforce
  next 
    case (Fun f f_args)
    then show ?thesis
    proof  (cases "m1 $$ F f (length f_args)")
      case None
      then show ?thesis 
        using SymbolNode.prems(1) SymbolNode.prems(2) Fun subsetD var_terms_in_set by fastforce 
    next
      case (Some m2)
      then show ?thesis 
      proof (cases f_args)
        case Nil
        then have "e \<in> retrieve_instances (SymbolNode m1) (Fun f [])"
          using SymbolNode.prems(2) Fun by fastforce
        then have "e \<in> to_set (m2 $$! 0)"
          using Some Nil by auto 
        then show ?thesis using to_set_entry
          by (metis SymbolNode.prems(1) Some Nil fmlookup_dom'_iff insertI1 list.size(3) option.sel symbol.inject trie.inject(2) well_structured.cases well_structured_map_entry.cases)
      next
        case (Cons _ _)
        have h1: "m1 $$ F f (length f_args) = Some m2"
          by (metis Some)
        then have h2: " e \<in> retrieve_instances (SymbolNode m1) (Fun f f_args)" 
          using SymbolNode(3) Fun Cons by simp
        then have h3: "e \<in> (\<Inter>i\<in>fmdom' m2. retrieve_instances (m2 $$! i) (f_args ! i))"
          using Cons h1 by simp
        then show ?thesis 
        proof-
          have h0: "0 \<in> fmdom' m2"
            by (metis SymbolNode.prems(1) Some fmdom'I insertI1 lessThan_Suc_eq_insert_0 old.nat.exhaust option.sel trie.inject(2) well_structured.cases well_structured_map_entry.cases)
          then  have h1:" well_structured (m2 $$! 0)"
            by (metis SymbolNode.prems(1) fmdom'I fmdom'_notI fmran'I h1 length_0_conv list.simps(3) local.Cons option.collapse option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.cases)
          then have "e \<in> to_set (m2 $$! 0)"
            by (smt (verit) SymbolNode.hyps INT_iff Some fmdom'_notI fmran'I h0 h3 option.collapse)
          then show ?thesis
            by (metis Some fmdom'_notI h0 option.collapse to_set_entry) 
        qed
      qed
    qed
  qed
qed

lemma retrieve_instances_sound:
  assumes "well_structured tr"
      and "sound_storage_from_position tr p"
      and "subterm_at_path e p e'"
      and "e \<in> retrieve_instances tr t"
    shows "linear_instance e' t"
  using assms
proof  (induct arbitrary: e p e' rule: retrieve_instances.induct)
  case (1 s t)
  then show ?case
    by (simp add: not_well_structured_leaf)
next
  case (2 m1 x)
  then show ?case
  proof (cases "m1 $$ Star" )
    case None
    then show ?thesis
      by (simp add: li_var)
  next
    case (Some m2)
    then show ?thesis
    proof (cases e')
      case (Var _)
      then show ?thesis
        by (simp add: li_var)
    next
      case (Fun g g_args)
      then show ?thesis
        by (simp add: li_var)
    qed
  qed
next
  case (3 m1 f f_args)
  then show ?case
  proof(cases "m1 $$ F f (length f_args)" )
    case None
    then show ?thesis
      using "3.prems"(4) by auto 
  next
    case (Some m2)
    then show ?thesis proof (cases "f_args = []")
      case True
      then show ?thesis proof (cases e')
        case (Var x)
        have "e \<in> to_set (m2 $$! 0)"
          using "3.prems"(4) Some True by auto
        then show ?thesis
          using "3.prems"(1-4) Some True not_sound_storage 
          by (metis Var symbol.distinct(1) to_symbol.simps(1) to_symbol.simps(2)) 
      next
        case (Fun g g_args)
        have "linear_instance (Fun f [] ) (Fun f [] )"
          by (simp add: li_func)
        then show ?thesis
          using "3.prems"(1-4) Fun Some True not_sound_storage 
          by (smt (verit) length_0_conv option.simps(5) retrieve_instances.simps(3) symbol.inject to_symbol.simps(2))  
      qed
    next
      case False
      have h0: "\<forall>x\<in>fmdom' m2. well_structured (m2 $$! x)"
        by (metis "3.prems"(1) False Some fmdom'I fmdom'_notI fmran'I length_0_conv option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases)
      have "e \<in> (\<Inter>i\<in>fmdom' m2. retrieve_instances (m2 $$! i) (f_args ! i))"
        using "3.prems"(4) False Some by force
      then have h1: "\<forall> x\<in>fmdom' m2. e \<in> retrieve_instances (m2 $$! x) (f_args ! x) "
        by blast 
      then show ?thesis
      proof (cases "to_symbol e' = to_symbol (Fun f f_args)")
        case True
        then show ?thesis proof (cases e')
          case (Var _)
          then show ?thesis
            using True by force 
        next
          case (Fun g g_args)
          then have "\<And> i . i < length f_args \<Longrightarrow>linear_instance (g_args ! i) (f_args ! i)"
          proof -
            fix i
            assume h2: "i < length f_args"
            then have h3: "i \<in> fmdom' m2"
              by (meson "3.prems"(1) Some ws_dom_fun)
            then have h4: "well_structured (m2 $$! i)"
              using h0 by auto
            then have h5: "sound_storage_from_position (m2 $$! i) (p @ [(F f (length f_args),i)] )"
              by (metis "3.prems"(2) Some fmdom'_notI h3 option.collapse sound_storage_from_position_subtrie)
            then have "subterm_at_path e (p@[(F f (length f_args),i)] )  (g_args ! i) "
              by (smt (verit, ccfv_threshold) "3.prems"(3) Fun Suc_length_conv True h2 remove_nth_len subsubterm_at_path symbol.inject to_symbol.simps(2))
            then show "linear_instance (g_args ! i) (f_args ! i)"
              using "3.hyps" False Some h1 h3 h4 h5 by blast
          qed
          then show ?thesis
            by (metis Fun True li_func symbol.inject to_symbol.simps(2)) 
        qed
      next
        case False
        then have h6: "0\<in> fmdom' m2"
          by (metis "3.prems"(1) Some fmdom'I length_greater_0_conv list.size(3) ws_dom_const ws_dom_fun) 
        then have ws0: "well_structured (m2 $$! 0)" using h0
          by blast
        then have "e \<in> retrieve_instances (m2 $$! 0) (f_args ! 0) "
          using h1 h6 by blast
        then have "e \<in> to_set (m2 $$! 0)"
          using retrieve_instances_in_set ws0 by blast  
        then show ?thesis
          by (meson "3.prems"(1-3) False Some not_sound_storage)
      qed
    qed
  qed
qed


lemma retrieve_instances_complete: 
  assumes "linear_instance  e' t"
      and "well_structured tr"
      and "complete_storage_from_position tr p"
      and "sound_storage_from_position tr p"
      and "e \<in> to_set tr" 
      and "subterm_at_path e p e' "
    shows "e \<in> retrieve_instances tr t"
  using assms
proof (induction arbitrary: e p e' rule: retrieve_instances.induct)
  case (1 s t)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x)
  then show ?case
    by fastforce
next
  case (3 m1 f f_args)
  then show ?case
  proof (cases e')
    case (Var _)
    then show ?thesis
      using "3.prems"(1) linear_instance.simps by force
  next
    case (Fun g g_args)
    then have h1: "g = f \<and> length g_args = length f_args"
      by (metis "3.prems"(1) linear_instance.simps term.distinct(1) term.inject(2))
    then have "e \<in> (case m1 $$ F f (length f_args) of
                      None \<Rightarrow> {}
                    | Some m2 \<Rightarrow> if f_args = []
                                 then to_set (m2 $$! 0)
                                 else \<Inter>i\<in>fmdom' m2. retrieve_instances (m2 $$! i) (f_args ! i))" 
    proof (cases "m1 $$ F f (length f_args)")
      case None
      then show ?thesis
      proof simp 
        assume "m1 $$ F f (length f_args) = None"
        show False
          by (smt (verit, del_insts) "3.prems"(2-6) Fun None Pair_inject exists_leaf fmdom'I fmdom'_notI h1 list.inject list.size(3) path_of_term.simps sound_storage_from_position_def path_of_subterm subtrie_at_path.simps term.distinct(1) to_symbol.simps(2) trie.sel(3) not_well_structured_leaf)
      qed
    next
      case (Some m2)
      then show ?thesis
      proof (cases f_args)
        case Nil
        then have "\<exists>s. subtrie_at_path (SymbolNode m1) [(F f 0, 0)] (Leaf (insert e s))"
          by (metis "3.prems"(3-6) Fun h1 length_0_conv path_of_term_const simp_storage subterm_at_path_path_of_term)
        then show ?thesis
          using Nil Some Fun subtrie_cons subtrie_to_set_entry
          by fastforce
      next
        case (Cons _ _)
        then have not_nil: "f_args \<noteq> []" by auto
        then have "e \<in> (\<Inter>i\<in>fmdom' m2. retrieve_instances (m2 $$! i) (f_args ! i))" 
        proof(clarsimp)
          fix i
          assume dom: "i \<in> fmdom' m2"
          then have ws: " well_structured (m2 $$! i)"
            by (metis "3.prems"(2) not_nil Some dom fmdom'I fmdom'_notI fmran'I length_0_conv option.collapse option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.cases)
          have com: "complete_storage_from_position (m2 $$! i) (p @ [(F f (length f_args), i)])"
            by (metis "3.prems"(3) Some dom complete_storage_from_position_subtrie fmdom'_notI option.collapse)
          have so: "sound_storage_from_position (m2 $$! i) (p@[(F f (length f_args),i)])"
            by (metis "3.prems"(4) Some dom fmdom'_notI option.collapse sound_storage_from_position_subtrie) 
          have li: "linear_instance (g_args ! i) (f_args ! i)"
            by (metis "3.prems"(1-2) not_nil Fun Some dom key_map_entry linear_instance.simps term.distinct(1) term.sel(4))
          have st: "subterm_at_path e (p @ [(F f (length f_args), i)]) (g_args! i)"
            by (smt (verit, ccfv_SIG) "3.prems"(2,6) not_nil Fun Some Suc_length_conv dom  gr0_implies_Suc h1 key_map_entry length_greater_0_conv subsubterm_at_path)
          have "e \<in> to_set (m2 $$! i)"
          proof - 
            obtain p3 where "path_of_term (Fun f g_args) ((F f (length g_args), i) # p3)" 
              by (metis (no_types, lifting) "3.prems"(6) Fun append.assoc append_Cons exists_path h1 path_of_subterm st subterm_at_path_path_of_term)
            then have" path_of_term e (p @((F f (length f_args), i) # p3))"
              using "3.prems"(6) Fun h1 subterm_at_path_path_of_term by auto
            then show ?thesis
              by (meson "3.prems"(3-5) Some dom fmdom'_notI option.exhaust_sel simp_storage subtrie_to_set_entry)
          qed
          then show "e \<in> retrieve_instances (m2 $$! i) (f_args ! i)"
            using "3.IH" not_nil Some com dom li so st ws by blast
        qed
        then show ?thesis
          using not_nil Some by force 
      qed
    qed
    then show ?thesis
      by simp 
  qed
qed

subsection \<open>Correctness of retrieval of unifications\<close>

lemma retrieve_unifications_in_set:
  assumes "well_structured tr"
      and "e \<in> retrieve_unifications tr t"
    shows "e \<in> to_set tr"
  using assms
proof (induct tr arbitrary: t rule: trie.induct)
  case (Leaf _)
  then show ?case by (simp add: not_well_structured_leaf)
next
  case (SymbolNode m1)
  then show ?case
  proof (cases t)
    case (Var x)
    then show ?thesis
      using SymbolNode.prems var_terms_in_set by fastforce
  next 
    case (Fun f f_args)
    then show ?thesis
    proof  (cases "m1 $$ F f (length f_args)")
      case None
      then show ?thesis 
        using SymbolNode.prems(1) SymbolNode.prems(2) Fun subsetD var_terms_in_set by fastforce 
    next
      case (Some m2)
      then have h0: " 0 \<in> fmdom' m2"
        by (metis SymbolNode.prems(1) bot_nat_0.not_eq_extremum fmdom'I ws_dom_const ws_dom_fun)
      then show ?thesis
      proof (cases f_args)
        case Nil 
        then have "e \<in> retrieve_unifications (SymbolNode m1) (Fun f [])"
          using SymbolNode.prems(2) Fun by fastforce
        then consider
            (a) "e \<in> var_terms m1"
          | (b) "e \<in> to_set (m2 $$! 0)"
          using Some Nil by auto 
        then show ?thesis
        proof cases
          case a
          then show ?thesis
            by (meson SymbolNode.prems(1) in_mono var_terms_in_set) 
        next
          case b
          then show ?thesis
            by (metis Some fmdom'_notI h0 option.collapse to_set_entry) 
        qed
      next
        case (Cons _ _)
        have h1: "m1 $$ F f (length f_args) = Some m2"
          by (metis Some)
        then have "e \<in> retrieve_unifications (SymbolNode m1) (Fun f f_args)" 
          using SymbolNode(3) Fun Cons by simp      
        then consider (a) "e \<in> var_terms m1"
          | (b) "e \<in> (\<Inter>i\<in>fmdom' m2. retrieve_unifications (m2 $$! i) (f_args ! i))"
          using Cons h1 by fastforce
        then show ?thesis proof cases
          case a
          then show ?thesis
            by (meson SymbolNode.prems(1) subsetD var_terms_in_set) 
        next
          case b
          then show ?thesis
          proof -
            have "0 \<in> fmdom' m2"
              by (metis SymbolNode.prems(1) Some fmdom'I insertI1 lessThan_Suc_eq_insert_0 old.nat.exhaust option.sel trie.inject(2) well_structured.cases well_structured_map_entry.cases)
            then have "well_structured (m2 $$! 0)"
              by (metis SymbolNode.prems(1) h1 fmdom'I fmdom'_notI fmran'I length_0_conv list.simps(3) local.Cons option.collapse option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.simps well_structured_map_entry.cases)
            then have "e \<in> to_set (m2 $$! 0)"
              by (smt (verit) SymbolNode.hyps INT_iff Some b fmdom'_notI fmran'I h0 option.collapse)
            then show ?thesis
              by (metis Some fmdom'_notI h0 option.collapse to_set_entry) 
          qed
        qed
      qed
    qed
  qed
qed

lemma retrieve_unifications_sound:
  assumes "well_structured tr"
      and "sound_storage_from_position tr p"
      and "subterm_at_path e p e'"
      and "e \<in> retrieve_unifications tr t"
    shows "linear_unification t e'"
  using assms
proof (induct arbitrary: e p e' rule: retrieve_unifications.induct)
  case (1 s t)
  then show ?case
    by (simp add: not_well_structured_leaf)
next
  case (2 m x)
  then show ?case
    by (meson lu_varl)
next
  case (3 m1 f f_args)
  then show ?case
  proof (cases e')
    case (Var x)
    then show ?thesis
      by (simp add: lu_varr)
  next
    case (Fun g g_args)
    show ?thesis
    proof (cases "f = g \<and> length f_args = length  g_args")
      case True
      then consider
          (a) "e \<in> var_terms m1"
        | (b) "e \<in> (case m1 $$ F f (length f_args) of
                     None \<Rightarrow> {}
                   | Some m2 \<Rightarrow> if f_args = [] then to_set (m2 $$! 0) else \<Inter>i\<in>fmdom' m2. retrieve_unifications (m2 $$! i) (f_args ! i))"
        using "3.prems"(4) by fastforce
      then show ?thesis proof cases
        case a
        then show ?thesis
          by (metis (no_types, lifting) "3.prems"(1-3) Fun empty_iff not_sound_storage_at_star option.collapse option.split_sel_asm var_terms.simps)
      next
        case b
        then show ?thesis
        proof (cases "m1 $$ F f (length f_args)")
          case None
          then show ?thesis
            using b by auto
        next
          case (Some m2)
          then show ?thesis
          proof (cases f_args)
            case Nil
            then show ?thesis
              using "3.prems"(1-3) Fun Some b linear_unification.simps not_sound_storage True by fastforce 
          next
            case (Cons _ _)
            have "e'= Fun f g_args" by (simp add: Fun True)
            then show ?thesis 
            proof (safe, rule_tac lu_func)
              show "length f_args = length g_args" by (simp add: True)
              show "\<forall>i<length f_args. linear_unification (f_args ! i) (g_args ! i)"
              proof safe
                fix i
                show "i < length f_args \<Longrightarrow> linear_unification (f_args ! i) (g_args ! i)"
                proof -
                  assume h0: "i < length f_args"
                  have h1: "well_structured (m2 $$! i)" using ws_dom_fun
                    by (metis "3.prems"(1) Some fmdom'I fmdom'_notI fmran'I h0 length_0_conv list.simps(3) local.Cons option.collapse option.sel symbol.inject symbol.simps(3) trie.inject(2) well_structured.cases well_structured_map_entry.cases)
                  then have h2: "sound_storage_from_position (m2 $$! i) (p @ [(F f (length g_args), i)]) "
                    by (metis "3.prems"(1,2) Some True h0 fmdom'_notI option.collapse sound_storage_from_position_subtrie ws_dom_fun)
                  then  have h3: "subterm_at_path e (p @ [(F f (length g_args), i)]) (g_args ! i)"
                    using "3.prems"(3) Fun True h0 subsubterm_at_path by fastforce   
                  then show ?thesis
                  proof-
                    have "i \<in> fmdom' m2"
                      by (meson "3.prems"(1) Some h0 ws_dom_fun)
                    then show ?thesis
                      using "3.hyps" Cons Some b h1 h2 h3 by auto
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    next
      case False
      then have h1: "to_symbol (Fun f f_args) \<noteq> to_symbol (Fun g g_args)"
        by auto
      then consider (a) "e \<in> var_terms m1"
        | (b) "e \<in> (case m1 $$ F f (length f_args) of
                                None \<Rightarrow> {}
                              | Some m2 \<Rightarrow> if f_args = [] then to_set (m2 $$! 0) else \<Inter>i\<in>fmdom' m2. retrieve_unifications (m2 $$! i) (f_args ! i))"
        using "3.prems"(4) by fastforce
      then show ?thesis
      proof cases
        case a
        then show ?thesis
          by (metis (no_types, lifting) "3.prems"(1-3) Fun insert_Diff insert_not_empty not_sound_storage_at_star option.case_eq_if option.collapse var_terms.simps)
      next
        case b
        then show ?thesis
        proof (cases "m1 $$ F f (length f_args) ")
          case None
          then show ?thesis
            using b by fastforce
        next
          case (Some m2)
          then show ?thesis
          proof (cases f_args)
            case Nil
            then show ?thesis
              using "3.prems"(1-3) False Fun Some b not_sound_storage 
              by (smt (verit, best) h1 option.simps(5))  
          next
            case (Cons _ _)
            then have h: "\<forall>i\<in>fmdom' m2. e \<in> retrieve_unifications (m2 $$! i) (f_args ! i)"
              using False Some b by auto
            then have "f_args \<noteq> []"
              using Cons by blast
            then have "e \<in> to_set (m2 $$! 0)"
              by (metis (no_types, lifting) "3.prems"(1) Some h fmdom'I fmdom'_notI fmran'I length_0_conv length_greater_0_conv option.collapse option.sel retrieve_unifications_in_set symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.cases ws_dom_fun)
            then have False
              by (metis "3.prems"(1-3) Fun Some h1 not_sound_storage) 
            then show ?thesis
              by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma retrieve_unifications_complete_var:
  assumes "complete_storage_from_position (SymbolNode m) p"
      and "sound_storage_from_position (SymbolNode m) p "
      and "e \<in> to_set (SymbolNode m) " 
      and "subterm_at_path e p (Var x)" 
    shows "e \<in> retrieve_unifications (SymbolNode m) t"
  using assms
proof -
  have "path_of_term (Var x) [(Star,0)]"
    by (simp add: path_of_term_var)
  then have "path_of_term e (p @ [(Star,0)])"
    using assms(4) subterm_at_path_path_of_term by auto
  then have sub_fin: "\<exists>s. subtrie_at_path (SymbolNode m) [(symbol.Star, 0)] (Leaf (insert e s)) "
    using simp_storage assms(1-3) by blast
  then show ?thesis
  proof (cases t)
    case (Var y)
    then show ?thesis
    proof (cases "m $$ Star")
      case None
      then show ?thesis
        using Var assms(3) by force
    next
      case (Some m2)
      then show ?thesis
        by (metis Var retrieve_unifications.simps(2) assms(3))
    qed
  next
    case (Fun f f_args)
    then have "t = Fun f f_args"
      by (simp add: Fun)
    then have "e \<in> (case m $$ Star of None \<Rightarrow> {} | Some m2 \<Rightarrow> to_set (m2 $$! 0))"
    proof (cases "m $$ Star")
      case None
      then show ?thesis
        by (meson fmdom'I fmdom'_notI sub_fin subtrie_cons)
    next
      case (Some m2)
      then show ?thesis
        using sub_fin
          subtrie_cons subtrie_to_set_entry by fastforce 
    qed
    then show ?thesis
      using Fun by auto  
  qed
qed

lemma retrieve_unifications_complete:
  assumes "linear_unification t e'"
      and "well_structured tr"
      and "complete_storage_from_position tr p"
      and "sound_storage_from_position tr p"
      and "e \<in> to_set tr"
      and "subterm_at_path e p e'"
    shows "e \<in> retrieve_unifications tr t"
  using assms
proof (induction  arbitrary: e p e' rule: retrieve_unifications.induct)
  case (1 s t)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x)
  then show ?case
    by auto   
next
  case (3 m f f_args)
  then show ?case
  proof (cases e')
    case (Var x)
    then show ?thesis
      by (metis "3.prems"(3-6) retrieve_unifications_complete_var)
  next
    case (Fun g g_args) then have  hyp1: "g = f \<and> length g_args  = length f_args"
      using "3.prems"(1) linear_unification.cases by fastforce
    then have " e \<in> (case m $$ F f (length f_args) of
                       None \<Rightarrow> {}
                     | Some m2 \<Rightarrow> if f_args = []
                                  then to_set (m2 $$! 0)
                                  else \<Inter>i\<in>fmdom' m2. retrieve_unifications (m2 $$! i) (f_args ! i))" 
    proof (cases "m $$ F f (length f_args)")
      case None
      then show ?thesis  proof(simp) 
        assume "m $$ F f (length f_args) = None" show False
          by (smt (verit, del_insts) "3.prems"(2-6) Fun None Pair_inject exists_leaf fmdom'I fmdom'_notI hyp1 list.inject list.size(3) path_of_term.simps sound_storage_from_position_def path_of_subterm subtrie_at_path.simps term.distinct(1) to_symbol.simps(2) trie.sel(3) not_well_structured_leaf)
      qed
    next
      case (Some m2)
      then show ?thesis proof (cases "f_args = []" )
        case True
        have "\<exists>ts. subtrie_at_path (SymbolNode m) [(F f 0, 0)] (Leaf (insert e ts)) "
          by (metis "3.prems"(3-6) Fun True hyp1 length_0_conv path_of_term_const simp_storage subterm_at_path_path_of_term)
        then show ?thesis
          using True Some subtrie_to_set_entry ws_dom_const subtrie_cons by fastforce 
      next
        case False
        then  have "e \<in> (\<Inter>i\<in>fmdom' m2. retrieve_unifications (m2 $$! i) (f_args ! i))" 
        proof(clarsimp)
          fix i
          assume dom: "i \<in> fmdom' m2"
          then have  ws: " well_structured (m2 $$! i)"
            by (metis "3.prems"(2) False Some dom fmdom'I fmdom'_notI fmran'I length_0_conv option.collapse option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.cases)
          have com: "complete_storage_from_position (m2 $$! i) (p@[(F f (length f_args),i)])"
            by (metis "3.prems"(3) Some dom complete_storage_from_position_subtrie fmdom'_notI option.collapse)
          have so :"sound_storage_from_position (m2 $$! i) (p@[(F f (length f_args),i)])"
            by (metis "3.prems"(4) Some dom fmdom'_notI option.collapse sound_storage_from_position_subtrie) 
          have  li: "linear_unification (f_args ! i) (g_args ! i)"
            by (metis (no_types, lifting) "3.prems"(1-2) False Fun Some dom key_map_entry linear_unification.simps term.distinct(1) term.sel(4))
          have le: "i < length f_args"
            by (meson "3.prems"(2) False Some dom key_map_entry)
          have st:" subterm_at_path e (p@[(F f (length f_args),i)]) (g_args ! i)"
            by (smt (verit, ccfv_SIG) "3.prems"(2) "3.prems"(6) False Fun Some Suc_length_conv dom  gr0_implies_Suc hyp1 key_map_entry length_greater_0_conv subsubterm_at_path)
          have ts:" e \<in> to_set (m2 $$! i)"
          proof - 
            obtain p3 where " path_of_term (Fun f g_args) ((F f (length g_args), i) # p3)"
              by (metis (mono_tags, opaque_lifting) "3.prems"(6) Fun append.assoc append_Cons exists_path hyp1 path_of_subterm st subterm_at_path_path_of_term to_symbol.simps(2))   
            then have" path_of_term e (p @((F f (length f_args), i) # p3))"
              using "3.prems"(6) Fun hyp1 subterm_at_path_path_of_term by auto
            then show ?thesis
              by (meson "3.prems"(3-5) Some dom fmdom'_notI option.exhaust_sel simp_storage subtrie_to_set_entry)
          qed
          then  show "e \<in> retrieve_unifications (m2 $$! i) (f_args ! i)"
            using "3.IH" False Some com dom li so st ws by blast
        qed
        then  show ?thesis
          using False Some by force 
      qed
    qed
    then show ?thesis
      by simp 
  qed
qed

subsection \<open>Correctness of retrieval of variants\<close>

lemma retrieve_variants_in_set:
  assumes "well_structured tr"
      and "e \<in> retrieve_variants tr t"
    shows "e \<in> to_set tr"
  using assms
proof (induct tr arbitrary:t rule:trie.induct)
  case (Leaf _) then
  show ?case  by (simp add: not_well_structured_leaf)
next
  case (SymbolNode m)
  then show ?case
  proof (cases t)
    case (Var _)
    then show ?thesis
      using SymbolNode.prems(1,2) var_terms_in_set by fastforce
  next 
    case (Fun f f_args)
    then show ?thesis
    proof  (cases "m $$ F f (length f_args)")
      case None
      then show ?thesis 
        using SymbolNode.prems(1,2) Fun subsetD var_terms_in_set by fastforce 
    next
      case (Some m2)
      then show ?thesis 
      proof (cases f_args)
        case Nil
        then have "e \<in> retrieve_variants (SymbolNode m) (Fun f [])"
          using SymbolNode.prems(2) Fun by fastforce
        then have "e \<in> to_set (m2 $$! 0)"
          using Some Nil by auto 
        then show ?thesis
          using to_set_entry
          by (metis SymbolNode.prems(1) Some Nil fmlookup_dom'_iff insertI1 list.size(3) option.sel symbol.inject trie.inject(2) well_structured.cases well_structured_map_entry.cases)
      next
        case (Cons _ _)
        have h1: "m $$ F f (length f_args) = Some m2"
          by (metis Some)
        then have h2: "e \<in> retrieve_variants (SymbolNode m) (Fun f f_args)" 
          using SymbolNode(3) Fun Cons by simp
        then have h3: "e \<in> (\<Inter>i\<in>fmdom' m2. retrieve_variants (m2 $$! i) (f_args ! i))"
          using Cons h1 by simp
        then show ?thesis 
        proof -
          have h0: "0 \<in> fmdom' m2"
            by (metis Some SymbolNode.prems(1) length_greater_0_conv list.simps(3) local.Cons ws_dom_fun)
          then have h1: "well_structured (m2 $$! 0)"
            by (metis SymbolNode.prems(1) fmdom'I fmdom'_notI fmran'I h1 length_0_conv list.simps(3) local.Cons option.collapse option.sel symbol.inject symbol.simps(3) trie.inject(2) well_structured.simps well_structured_map_entry.cases)
          then have "e \<in> to_set (m2 $$! 0)"
            by (smt (verit) SymbolNode.hyps INT_iff Some fmdom'_notI fmran'I h0 h3 option.collapse)
          then show ?thesis
            by (metis Some fmdom'_notI h0 option.collapse to_set_entry) 
        qed
      qed
    qed
  qed
qed

lemma retrieve_variants_sound:
  assumes "well_structured tr "
      and "sound_storage_from_position tr p "
      and "subterm_at_path e p e' "
      and "e \<in> retrieve_variants tr t"
    shows "linear_variant e' t "
  using assms
proof  (induct arbitrary: e p e' rule: retrieve_variants.induct)
  case (1 s t)
  then show ?case
    by (simp add: not_well_structured_leaf)
next
  case (2 m x)
  then show ?case
  proof (cases "m $$ symbol.Star")
    case None
    then show ?thesis
      using "2.prems"(4) by auto
  next
    case (Some m2)
    then show ?thesis
    proof (cases e')
      case (Var _)
      then show ?thesis
        by (simp add: lv_var)
    next
      case (Fun g g_args)
      then show ?thesis
        using "2.prems"(1-4) Some not_sound_storage_at_star by fastforce
    qed
  qed
next
  case (3 m f f_args)
  then show ?case
  proof (cases "m $$ F f (length f_args)" )
    case None
    then show ?thesis
      using "3.prems"(4) by auto 
  next
    case (Some m2)
    then show ?thesis
    proof (cases f_args)
      case Nil
      then show ?thesis
      proof (cases e')
        case (Var x)
        then have "e \<in> to_set (m2 $$! 0)"
          using "3.prems"(1-4) Some Nil by simp
        then show ?thesis
          using "3.prems"(1-4) Var Some Nil not_sound_storage 
          by fastforce 
      next
        case (Fun g g_args)
        have "linear_variant (Fun f [] ) (Fun f [] )"
          by (simp add: lv_func)
        then show ?thesis
          using "3.prems"(1-4) Fun Some Nil not_sound_storage 
          by (smt (verit, del_insts) length_greater_0_conv option.simps(5) retrieve_variants.simps(3) symbol.inject to_symbol.simps(2))  
      qed
    next
      case (Cons _ _)
      then have h0: "\<forall> x\<in>fmdom' m2. well_structured (m2 $$! x)"
        by (metis "3.prems"(1) Some fmdom'I fmdom'_notI fmran'I length_0_conv list.simps(3) option.collapse option.sel symbol.simps(1) symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.cases)
      have "e \<in>  (\<Inter>i\<in>fmdom' m2. retrieve_variants (m2 $$! i) (f_args ! i))"
        using "3.prems"(4) Cons Some by force
      then have h1: "\<forall> x\<in>fmdom' m2. e \<in> retrieve_variants (m2 $$! x) (f_args ! x) "
        by blast 
      then show ?thesis
      proof (cases "to_symbol e' = to_symbol (Fun f f_args)")
        case True
        then show ?thesis proof (cases e')
          case (Var x1)
          then show ?thesis
            using True by force 
        next
          case (Fun g g_args)
          then  have "\<And> i . i < length f_args \<Longrightarrow> linear_variant (g_args ! i) (f_args ! i)"
          proof -
            fix i
            assume h2: "i < length f_args"
            then have h3: "i \<in> fmdom' m2"
              by (meson "3.prems"(1) Some ws_dom_fun)
            then have h4: "well_structured (m2 $$! i)"
              using h0 by auto
            then have h5: "sound_storage_from_position (m2 $$! i) (p @ [(F f (length f_args), i)])"
              by (metis "3.prems"(2) Some fmdom'_notI h3 option.collapse sound_storage_from_position_subtrie)
            then have "subterm_at_path e (p @ [(F f (length f_args),i)]) (g_args ! i)"
              by (smt (verit, ccfv_threshold) "3.prems"(3) Fun Suc_length_conv True h2 remove_nth_len subsubterm_at_path symbol.inject to_symbol.simps(2))
            then show "linear_variant (g_args ! i) (f_args ! i)"
              using "3.hyps" Cons Some h1 h3 h4 h5 by blast
          qed
          then show ?thesis
            by (metis Fun True lv_func symbol.inject to_symbol.simps(2))
        qed
      next
        case False
        then have h6: "0 \<in> fmdom' m2"
          using "3.prems"(1) Some ws_dom_const ws_dom_fun by fastforce 
        then have h7: "well_structured (m2 $$! 0)" using h0
          by blast
        then have " e \<in> retrieve_variants (m2 $$! 0) (f_args ! 0) "
          using h1 h6 by blast
        then have "e \<in> to_set (m2 $$! 0)"
          using retrieve_variants_in_set h7 by blast
        then show ?thesis
          by (meson "3.prems"(1-3) False Some not_sound_storage)
      qed
    qed
  qed
qed

lemma retrieve_variants_complete:
  assumes "linear_variant e' t"
      and "well_structured tr "
      and "complete_storage_from_position tr p "
      and "sound_storage_from_position tr p "
      and "e \<in> to_set tr "
      and "subterm_at_path e p e' "
    shows "e \<in> retrieve_variants tr t"
  using assms
proof (induction arbitrary: e p e' rule: retrieve_variants.induct)
  case (1 s t)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x)
  then show ?case
  proof (cases )
    case (lv_var x)
    then show ?thesis
      by (metis "2.prems"(2-6) retrieve_generalizations_complete li_var retrieve_generalizations.simps(2) retrieve_variants.simps(2)) 
  next
    case lv_func
  qed
next
  case (3 m f f_args)
  then show ?case
  proof (cases e')
    case (Var _)
    then show ?thesis
      using "3.prems"(1) linear_variant.simps by force
  next
    case (Fun g g_args)
    then have h1: "g = f \<and> length g_args = length f_args"
      using "3.prems"(1) linear_variant.cases by blast

    then have "e \<in> (case m $$ F f (length f_args) of
                      None \<Rightarrow> {}
                    | Some m2 \<Rightarrow> if f_args = []
                                 then to_set (m2 $$! 0)
                                 else \<Inter>i\<in>fmdom' m2. retrieve_variants (m2 $$! i) (f_args ! i))" 
    proof (cases "m $$ F f (length f_args)")
      case None
      then show ?thesis
      proof simp 
        assume "m $$ F f (length f_args) = None"
        show False
          by (smt (verit, del_insts) "3.prems"(2-6) Fun None Pair_inject exists_leaf fmdom'I fmdom'_notI h1 list.inject list.size(3) path_of_term.simps sound_storage_from_position_def path_of_subterm subtrie_at_path.simps term.distinct(1) to_symbol.simps(2) trie.sel(3) not_well_structured_leaf)
      qed
    next
      case (Some m2)
      then show ?thesis
      proof (cases "f_args = []")
        case True
        have "\<exists>s. subtrie_at_path (SymbolNode m) [(F f 0, 0)] (Leaf (insert e s))"
          by (metis "3.prems"(3-6) Fun True h1 length_0_conv path_of_term_const simp_storage subterm_at_path_path_of_term)
        then show ?thesis
          using True  Some subtrie_to_set_entry ws_dom_const subtrie_cons by fastforce
      next
        case False
        then have "e \<in> (\<Inter>i\<in>fmdom' m2. retrieve_variants (m2 $$! i) (f_args ! i))" 
        proof clarsimp
          fix i
          assume dom: "i \<in> fmdom' m2"
          then have  ws: "well_structured (m2 $$! i)"
            by (metis "3.prems"(2) False Some dom fmdom'I fmdom'_notI fmran'I length_0_conv option.collapse option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.cases)
          have com: "complete_storage_from_position (m2 $$! i) (p@[(F f (length f_args), i)])"
            by (metis "3.prems"(3) Some dom complete_storage_from_position_subtrie fmdom'_notI option.collapse)
          have so: "sound_storage_from_position (m2 $$! i) (p@[(F f (length f_args), i)])"
            by (metis "3.prems"(4) Some dom fmdom'_notI option.collapse sound_storage_from_position_subtrie) 
          have li: "linear_variant  (g_args ! i) (f_args ! i)"
            by (metis "3.prems"(1-2) False Fun Some dom key_map_entry linear_variant.simps term.distinct(1) term.inject(2))
          have le: "i< length f_args"
            by (meson "3.prems"(2) False Some dom key_map_entry)
          have st: "subterm_at_path e (p @ [(F f (length f_args), i)]) (g_args! i)"
            by (smt (verit, ccfv_SIG) "3.prems"(2) "3.prems"(6) False Fun Some Suc_length_conv dom  gr0_implies_Suc h1 key_map_entry length_greater_0_conv subsubterm_at_path)
          have ts: "e \<in> to_set (m2 $$! i)"
          proof - 
            obtain p3 where "path_of_term (Fun f g_args) ((F f (length g_args), i) # p3)"
              by (metis (no_types, opaque_lifting) "3.prems"(6) Fun append.assoc append_Cons exists_path h1 path_of_subterm st subterm_at_path_path_of_term)
            then have "path_of_term e (p @((F f (length f_args), i) # p3))"
              using "3.prems"(6) Fun h1 subterm_at_path_path_of_term by auto
            then show ?thesis
              by (meson "3.prems"(3-5) Some dom fmdom'_notI option.exhaust_sel simp_storage subtrie_to_set_entry)
          qed
          then show "e \<in> retrieve_variants (m2 $$! i)(f_args ! i)"
            using "3.IH" False Some com dom li so st ws by blast
        qed
        then  show ?thesis
          using False Some by force 
      qed
    qed
    then show ?thesis
      by simp 
  qed
qed

section \<open>Term insertion\<close>

fun update_entry :: "('a, 'b) fmap \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap" where
  "update_entry m k f v = fmupd k (f (case m $$ k of None \<Rightarrow> v | Some v0 \<Rightarrow> v0)) m"

lemma update_entry_all_ran: "\<forall>y \<in> fmran' m. P y \<Longrightarrow> P (f v) \<Longrightarrow> \<forall>x. P x \<longrightarrow> P (f x) \<Longrightarrow> \<forall>y \<in> fmran' (update_entry m k f v). P y"
  by (smt (z3) fmdom'_notD fmlookup_dom'_iff fmlookup_ran'_iff fmupd_lookup option.case(1) option.case(2) update_entry.simps)

lemma update_entry_all_dom:
  assumes "\<forall>x \<in> fmdom' m. P x (m $$! x)"
      and "P k (f v)"
      and "\<forall>x \<in> fmdom' m. P x (f (m $$! x))"
    shows "\<forall>x \<in> fmdom' (update_entry m k f v). P x (update_entry m k f v $$! x)"
  using assms
  by (metis fmdom'_notD fmdom'_notI fmupd_lookup option.case_eq_if option.sel update_entry.simps)

fun update_entries :: "('a, 'b) fmap \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap" where
  "update_entries m [] f v = m"
| "update_entries m (k # ks) f v = update_entries (update_entry m k (f k) v) ks f v"

lemma update_entries_dom: "fmdom' (update_entries m ls f v) = set ls \<union> fmdom' m"
  by  (induction ls arbitrary: m ) auto

lemma updt_entries_some:
  assumes "k \<notin> set ks"
      and "m $$ k = Some v0"
    shows "update_entries m (k # ks) f v $$ k = Some (f k v0)"
  using assms
proof (induction ks arbitrary: m)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a ks)
  then show ?case
    by (smt (z3) fmupd_lookup fmupd_reorder_neq list.sel(1) list.sel(3) list.set_intros(1) list.set_intros(2) update_entries.simps(2) update_entry.simps) 
qed

lemma upd_entries_some:
  assumes "distinct ks"
      and "k \<in> set ks"
      and "m $$ k = Some v0"
    shows "update_entries m ks f v $$ k = Some (f k v0)"
  using assms
proof (induction ks arbitrary: m)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a ks)
  then show ?case
    by (metis distinct.simps(2) fmupd_lookup set_ConsD updt_entries_some update_entries.simps(2) update_entry.simps) 
qed

lemma rew_ran_upd_entries_none :
  assumes "distinct ls"
      and "\<forall>k\<in>set ls. m $$ k = None"
    shows "fmran' (update_entries m ls f v) = (\<lambda>y. f y v) ` set ls \<union> fmran' m"
  using assms
proof (induction ls arbitrary: m)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a ls)
  assume distinct_ls: "distinct (a # ls)"
  assume none_m_ls: "\<forall>k\<in>set (a # ls). m $$ k = None"
  have "m $$ a = None" and "\<forall>k\<in>set ls. m $$ k = None"
    using none_m_ls by auto
  let ?m' = "m(a $$:= f a v)"
  have "fmran' (update_entries m (a # ls) f v) = fmran' (update_entries ?m' ls f v)"
    by (simp add: none_m_ls)
  have IH: "fmran' (update_entries ?m' ls f v) = (\<lambda>y. f y v) ` set ls \<union> fmran' ?m'"
    by (metis Cons.IH distinct.simps(2) distinct_ls fmupd_lookup none_m_ls set_subset_Cons subsetD)
  have "fmran' ?m' = insert (f a v) (fmran' m)"
    by (simp add: \<open>m $$ a = None\<close> update_entry_ran)
  show "fmran' (update_entries m (a # ls) f v) = (\<lambda>y. f y v) ` set (a # ls) \<union> fmran' m"
    by (simp add: IH \<open>m $$ a = None\<close> update_entry_ran)
qed

fun insert_leaf :: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) trie" where
  "insert_leaf (Leaf s) t = Leaf (insert t s)"
| "insert_leaf (SymbolNode m) t = undefined"

function insert_aux :: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) trie" where
  "insert_aux (Leaf s) t t0 = undefined"
| "insert_aux (SymbolNode m) (Var x) t0 = 
   SymbolNode (update_entry m Star (\<lambda>m2. update_entry m2 0 (\<lambda>tr. insert_leaf tr t0) (Leaf {})) fmempty)"
| "insert_aux (SymbolNode m) (Fun f []) t0 =
   SymbolNode (update_entry m (F f 0)(\<lambda>m2. update_entry m2 0 (\<lambda>tr. insert_leaf tr t0) (Leaf {})) fmempty)"
| "insert_aux (SymbolNode m) (Fun f (a # largs)) t0 =
   SymbolNode (update_entry m (F f (Suc (length largs)))
     (\<lambda>m2. update_entries m2 [0..<Suc (length largs)] (\<lambda>i tr. if i < Suc (length largs) then insert_aux tr ((a # largs) ! i) t0 else undefined) empty_trie) {$$})"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(p, q, r). depth q)")
  apply simp+
  by (metis List.finite_set Max_ge finite_imageI image_eqI image_insert le_imp_less_Suc length_Cons list.simps(15) nth_mem)

declare List.upt.upt_Suc [simp del]

lemma fmran_updt_entries_empty:
  assumes "distinct ls" 
    shows "fmran'(update_entries {$$} ls f v) = (\<lambda>y. f y v) ` set ls"
  using assms by (simp add: rew_ran_upd_entries_none fmran_empty')

lemma in_fmran_updt_entries:
  assumes "distinct ls "
    and" fmdom' aa = set ls "
    and " t \<in> fmran' (update_entries aa ls f v) "
  shows" \<exists>i\<in>set ls. t = f i (aa $$! i)"
  using assms
proof-
  have "\<forall>k\<in>set ls. aa $$ k \<noteq> None"
    by (metis assms(2) fmdom'_notI)
  then show ?thesis using  upd_entries_some update_entries_dom
    by (smt (verit, ccfv_threshold) Un_iff assms(1) assms(2) assms(3) fmdom'I fmdom'_alt_def fmdomE fmran'E option.sel)
qed

lemma in_fmran_updt_entries_left: 
  assumes "distinct ls"
      and "fmdom' m = set ls"
      and "i \<in> set ls" 
    shows "f i (m $$! i) \<in> fmran' (update_entries m ls f v)"
  using assms  by (metis fmdom'_notI fmran'I option.exhaust_sel upd_entries_some)

lemma rew_upd_entries_none:
  assumes h1:"distinct ls"
      and h2:"k \<in> set ls"
      and h3: "m $$ k = None"
    shows "(update_entries m ls f v) $$ k = Some(f k v)"
  using assms
proof (induction m ls f v arbitrary:k rule: update_entries.induct)
  case (1 m)
  then show ?case 
    by simp
next
  case (2 m k' ks f v)
  then show ?case 
  proof (cases "k = k'")
    case True
    then show ?thesis proof (cases "m $$ k'")
      case None
      then show ?thesis 
        by (simp, metis (mono_tags, lifting) "2.prems"(1) True distinct.simps(2) fmupd_idem fmupd_lookup option.simps(5) updt_entries_some update_entries.simps(2) update_entry.simps)
    next
      case (Some a)
      then show ?thesis
        using "2.prems"(3) True by auto  
    qed
  next
    case False
    then show ?thesis
      using "2.IH" "2.prems"(1,2,3) by auto
  qed
qed

lemma fmran_updt_entries:
  assumes "distinct ls"
      and "fmdom' m = set ls"
    shows "fmran' (update_entries m ls f v) = (\<lambda>i. f i (m $$! i)) ` set ls"
proof -
  have h1: "fmran' (update_entries m ls f v) \<subseteq> (\<lambda>i. f i (m $$! i)) ` set ls"
  proof
    fix t
    assume "t \<in> fmran' (update_entries m ls f v)"
    then obtain i where "i \<in> set ls" and "t = f i (m $$! i)"
      using in_fmran_updt_entries
      by (metis assms(1) assms(2))
    thus "t \<in> (\<lambda>i. f i (m $$! i)) ` set ls"
      by simp
  qed
  have "(\<lambda>i. f i (m $$! i)) ` set ls \<subseteq> fmran' (update_entries m ls f v)"
  proof
    fix t
    assume "t \<in> (\<lambda>i. f i (m $$! i)) ` set ls"
    then obtain i where "i \<in> set ls" and "t = f i (m $$! i)"
      by auto
    hence "t \<in> fmran' (update_entries m ls f v)"
      by (simp add: assms(1) assms(2) in_fmran_updt_entries_left)
    thus "t \<in> fmran' (update_entries m ls f v)"
      by simp
  qed
  thus ?thesis
    using h1 by force
qed

lemma rew_fmran_updt_entries_empty: "fmran' (update_entries {$$} [0..<Suc (length largs)] f v) = (\<lambda>y. f y v) ` set [0..<Suc (length largs)]"
  by (metis distinct_upt fmran_updt_entries_empty)

lemma insert_none_image: "k < Suc (length largs) \<Longrightarrow>
  update_entries {$$} ([0..<Suc (length largs)] )
       (\<lambda>i tr. if i < Suc (length largs) then insert_aux tr ((a # largs) ! i) t0 else undefined) empty_trie $$ k =
 Some (insert_aux empty_trie((a # largs) ! k) t0) "
  by (simp add: rew_upd_entries_none)

lemma insert_none_image':" k < Suc (length largs) \<Longrightarrow>
  update_entries {$$} ([0..<Suc (length largs)] )
       (\<lambda>i tr.  insert_aux tr ((a # largs) ! i) t0 ) empty_trie $$ k =
 Some (insert_aux empty_trie((a # largs) ! k) t0) "
  by (simp add: rew_upd_entries_none)

lemma rew_insert_none: " fmran' (update_entries {$$} ([0..<Suc (length largs)])
       (\<lambda>i tr. if i < Suc (length largs) then insert_aux tr ((a # largs) ! i) t0 else undefined) empty_trie)= (\<lambda>i. (insert_aux empty_trie ((a # largs) ! i) t0)) ` set [0..<Suc (length largs)]"
  by (simp add: rew_fmran_updt_entries_empty)

lemma fmdom'_fmap_of_list: " fmdom' (fmap_of_list xs) = set (map fst xs)"
  by (metis dom_map_of_conv_image_fst fmap_of_list.rep_eq fmdom'.rep_eq image_set)

lemma insert_some_image:
  assumes a1:  "k < Suc (length largs)"
      and a2: "fmdom' aa = set [0..<Suc (length largs)]" 
    shows "update_entries aa [0..<Suc (length largs)] (\<lambda>i tr. if i < Suc (length largs) then insert_aux tr ((a # largs) ! i) t0 else undefined) empty_trie $$ k = Some (insert_aux (aa $$! k) ((a # largs) ! k) t0)"
proof -
  have "distinct([0..<Suc (length largs)] )"
    using distinct_upt by blast 
  then have a3: "k \<in> set [0..<Suc (length largs)]"
    using a1 atLeast_upt by blast then 
  obtain tt :: "('a, 'b) trie" where
    f4: "k \<in> fmdom' aa \<longrightarrow> aa $$ k = Some tt"
    by (meson fmlookup_dom'_iff)
  have "k \<in> fmdom' aa"
    using a3 a2 by blast
  then have "aa $$ k = Some tt"
    using f4 by blast
  then show ?thesis
    using a3 a1 by (simp add: upd_entries_some)
qed

inductive_cases well_structured_cases: "well_structured tr"
declare well_structured_cases [elim!]

inductive_cases well_structured_map_entry_cases: "well_structured_map_entry s m"
declare well_structured_map_entry_cases [elim!]

lemma ws_insert_var: 
  assumes "well_structured (SymbolNode m)"
    shows "well_structured (insert_aux (SymbolNode m) (Var x) t)"
  using assms
proof (cases "m $$ Star")
  case None
  then show ?thesis
    using assms by (clarsimp simp add: fmran_empty' update_entry_ran ws_node wsme_var)
next
  case (Some m2)
  then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
    by (meson assms ws_dom_var)
  then have "symbol.Star \<in> fmdom' m"
    by (simp add: fmdom'I Some)
  then  have h3: "fmdom' (m2 (0 $$:= insert_leaf (Leaf ts) t)) = {0}"
    using Some assms by auto
  then have "\<forall>tr2. tr2 \<in> fmran' (m2 (0 $$:= insert_leaf (Leaf ts) t)) \<longrightarrow> (\<exists>ts. tr2 = Leaf ts)"
    by (metis fmdom'I fmlookup_ran'_iff fmupd_lookup insert_leaf.simps(1) option.sel singleton_iff)
  then have " well_structured_map_entry symbol.Star (m2 (0 $$:= insert_leaf (Leaf ts) t))"
    using h3 wsme_var by blast
  then have "well_structured (SymbolNode (m(symbol.Star $$:= m2(0 $$:= insert_leaf (Leaf ts) t))))"
    using assms
    by (metis fmdom'_fmupd fmupd_lookup insert_iff option.sel trie.inject(2) well_structured.cases ws_node)
  then show ?thesis 
    by (simp add: h Some)
qed

lemma ws_insert_const: 
  assumes "well_structured (SymbolNode m)"
    shows "well_structured (insert_aux (SymbolNode m) (Fun f []) t0)"
  using assms
proof (cases "m $$ F f 0")
  case None  
  from assms have h0: "\<forall>s. s \<in> fmdom' m \<longrightarrow>  well_structured_map_entry s (m $$! s)"
    by force
  then  have h3: "well_structured_map_entry (F f 0) {0 $$:= Leaf {t0}}"
    by (simp add: fmran_empty' update_entry_ran wsme_const)
  then have h4 : "F f 0 \<in> fmdom' m \<longrightarrow> well_structured_map_entry (F f 0) {0 $$:= Leaf {t0}}"
    by simp
  then have "well_structured (SymbolNode (m(F f 0 $$:= {0 $$:= Leaf {t0}})))"
    by (simp add: h0 h3 ws_node)
  then show ?thesis by (simp add: None) 
next
  case (Some m2)
  then obtain ts where h1: "m2 $$ 0 = Some (Leaf ts)"
    by (meson assms ws_dom_const)
  then have "fmdom' (m2 (0 $$:= Leaf (insert t0 ts))) = {0}"
    by (metis assms Some fmdom'I fmdom'_fmupd insert_absorb ws_dom_const)
  then have h2: " well_structured_map_entry (F f 0) (m2 (0 $$:= Leaf (insert t0 ts)))"
    by (metis fmdom'I fmran'E fmupd_lookup option.sel singleton_iff wsme_const)
  then have " \<forall>s. s \<in> fmdom' m \<longrightarrow>  well_structured_map_entry s (m $$! s)"
    using assms by fastforce
  then show ?thesis by (simp add: Some h1 h2 ws_node)
qed

lemma insert_preserves_structure:
  assumes "well_structured tr"
    shows "well_structured (insert_aux tr t t0)"
  using assms
proof (induct tr t t0 rule: insert_aux.induct)
  case (1 s t t0)
  then show ?case by auto
next
  case (2 m x t0)
  then show ?case by (meson ws_insert_var)
next
  case (3 m f t0)
  then show ?case by (meson ws_insert_const)
next
  case (4 m f a f_args t0)
  then have dom_well_structured: "\<forall>s. s \<in> fmdom' m \<longrightarrow> well_structured_map_entry s (m $$! s)"
    using "4.prems" by blast
  have length_non_zero: "Suc (length f_args) \<noteq> 0"
    by simp
  show ?case
  proof (cases "m $$ F f (Suc (length f_args))")
    case None
    let ?m' = "update_entries {$$} [0..<Suc (length f_args)]
                 (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) 
                 empty_trie"
    have dom_m': "fmdom' ?m' = {..<Suc (length f_args)}"
      by (simp add: atLeast_upt update_entries_dom)
    have well_structured_fmran: "\<And>t. t \<in> fmran' ?m' \<Longrightarrow> well_structured t"
    proof -
      fix t 
      assume "t \<in> fmran' ?m'"
      then obtain i where in_dom':"i \<in> fmdom' ?m'" and "?m' $$ i = Some t"
        by (meson fmdom'I fmlookup_ran'_iff)
      then have k: "insert_aux empty_trie ((a # f_args) ! i) t0 = t"
        by (simp add: dom_m' rew_upd_entries_none)
      then have "i < Suc (length f_args)"
        using dom_m' in_dom' by blast
      then show  "well_structured t"
        by (metis "4.hyps" fmdom'_notI fmempty_lookup k ws_node)
    qed
    then have "well_structured_map_entry (F f (Suc (length f_args))) ?m'"
      by (metis (no_types, lifting) length_non_zero dom_m' wsme_func)
    then show ?thesis
      by (simp add: None dom_well_structured ws_node)
  next
    case (Some m2)
    let ?m'' = "update_entries m2 [0..<Suc (length f_args)]
                 (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) 
                 empty_trie"
    have dom_m2: "fmdom' m2 = {..<Suc (length f_args)}"
      by (metis "4.prems" Some length_Cons list.distinct(1) ws_fmdom')
    have all_well_structured: "\<forall>i \<in> fmdom' m2. well_structured (m2 $$! i)"
      by (metis Some dom_well_structured fmdom'I fmdom'_notI fmran'I length_non_zero option.collapse option.sel symbol.distinct(1) symbol.inject well_structured_map_entry.cases)
    obtain i where in_dom':"i \<in> fmdom' m2"
      using dom_m2 by blast
    then have "i < Suc (length f_args)"
      by (meson "4.prems" Some ws_dom_fun2)
    then have insert_well_structured: "well_structured (insert_aux (m2 $$! i) ((a # f_args) ! i) t0)"
      using "4.hyps" all_well_structured in_dom' by blast
    have dom_m'': "fmdom' ?m'' = {..<Suc (length f_args)}"
      by (simp add: atLeast_upt dom_m2 update_entries_dom)
    have ran_m'': "fmran' ?m'' = (\<lambda>i. insert_aux (m2 $$! i) ((a # f_args) ! i) t0) ` set [0..<Suc (length f_args)]"
      using fmran_updt_entries[of "[0..<Suc (length f_args)]" m2] atLeast_upt dom_m2 by auto
    have well_structured_fmran'': "\<And>t. t \<in> fmran' ?m'' \<Longrightarrow> well_structured t"
      using "4.hyps" all_well_structured dom_m2 ran_m'' by auto
    then show ?thesis 
      by (simp add: Some ws_node dom_m'' "4.prems" dom_well_structured wsme_func)
  qed
qed

lemma minimal_storage_drop [simp]:
  assumes "minimal_storage (SymbolNode m)"
  shows "minimal_storage (SymbolNode (fmdrop s m))"
proof -
  have "\<And>m2 tr. m2\<in>fmran' (fmdrop s m) \<Longrightarrow> tr\<in>fmran' m2 \<Longrightarrow> minimal_storage tr \<and> tr \<noteq> empty_trie"
  proof -
    fix m2 tr
    assume "m2 \<in> fmran' (fmdrop s m)" and h: "tr \<in> fmran' m2"
    then have "m2 \<in> fmran' m"
      by (metis fmlookup_drop fmlookup_ran'_iff option.simps(3))
    then show "minimal_storage tr \<and> tr \<noteq> empty_trie"
      using assms h minimal_storage.cases by auto
  qed
  then show ?thesis
    by (simp add: minimal_storage_node)
qed

lemma minimal_storage_udt: 
  assumes "minimal_storage (SymbolNode m)"
      and "minimal_storage (SymbolNode {s $$:= m2})"
    shows "minimal_storage (SymbolNode (m(s $$:= m2)))"
  by (smt (verit, del_insts) assms(1) assms(2) fmlookup_ran'_iff fmupd_lookup minimal_storage.cases minimal_storage_node trie.sel(3) trie.simps(4))

lemma insert_preserves_minimal: 
  assumes "well_structured tr "
      and "minimal_storage tr" 
    shows "minimal_storage (insert_aux tr t t0)"
  using assms
proof  (induction tr t t0  rule: insert_aux.induct)
  case (1 s t t0)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x t0)
  then show ?case
  proof (cases "m $$ Star")
    case None
    have "minimal_storage (SymbolNode ({symbol.Star $$:= {0 $$:= Leaf {t0}}}))"
      by (metis fmran'_alt_def fmran_singleton fsingleton_iff insert_not_empty minimal_storage.simps trie.simps(4))
    then show ?thesis
      using "2.prems"(2) minimal_storage_udt None 
      by auto
  next
    case (Some m2)
    then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "2.prems"(1) ws_dom_var)
    have "minimal_storage (SymbolNode {Star $$:= m2(0 $$:= insert_leaf (Leaf ts) t0)})"
      by (smt (verit, ccfv_threshold) "2.prems"(1) Some dom_res_singleton fmempty_lookup fmfilter_true fmlookup_dom'_iff fmran_empty' fmupd_idem insert_leaf.simps(1) insert_not_empty minimal_storage.simps singletonD trie.distinct(1) update_entry_ran ws_dom_var)
    then show ?thesis
      using "2.prems"(2) Some h minimal_storage_udt by auto
  qed
next
  case (3 m f t0)
  then show ?case
  proof (cases "m $$ F f 0")
    case None
    have "minimal_storage (SymbolNode ({F f 0 $$:= {0 $$:= Leaf {t0}}}))"
      by (metis fmempty_lookup fmran_empty' insert_not_empty minimal_storage.simps singletonD trie.simps(4) update_entry_ran)
    then show ?thesis
      using "3.prems"(2) minimal_storage_udt  None 
      by auto
  next
    case (Some m2)
    then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "3.prems"(1) ws_dom_const)
    have "minimal_storage (SymbolNode {F f 0 $$:= m2(0 $$:= insert_leaf (Leaf ts) t0)})"
      by (smt (verit, best) "3.prems"(1) Some fmdom'I fmdom'_empty fmlookup_ran'_iff fmupd_lookup insert_absorb insert_leaf.simps(1) insert_not_empty minimal_storage.simps option.sel singletonD trie.distinct(1) ws_dom_const)
    then show ?thesis
      using "3.prems"(2) Some h minimal_storage_udt by auto
  qed
next
  case (4 m f a f_args t0)
  then show ?case 
  proof (cases "m $$ F f (Suc (length f_args))")
    case None
    let ?m' = "update_entries {$$} [0..<Suc (length f_args)]
          (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) empty_trie"
    have hi: "\<And>i. i < Suc (length f_args) \<Longrightarrow> minimal_storage (insert_aux empty_trie ((a # f_args) ! i) t0)"
      by (simp add: 4)
    have "\<And> m2 tr. m2\<in>fmran' {F f (Suc (length f_args)) $$:= ?m'} \<Longrightarrow> tr\<in>fmran' m2 \<Longrightarrow> minimal_storage tr \<and> tr \<noteq> empty_trie"
    proof -
      fix t r 
      assume h1: "t \<in> fmran' {F f (Suc (length f_args)) $$:= ?m'}"
      assume h2: "r \<in> fmran' t"
      obtain i where h3: "t $$ i = Some r"
        using h2 by auto
      have i: "i < Suc (length f_args)"
        by (metis (no_types, lifting) One_nat_def add_Suc_shift add_diff_cancel_left' distinct_Ex1 distinct_upt fmdom'I fmdom'_empty fmempty_lookup fmran_empty' h1 h3 length_upt nat_add_left_cancel_less nth_upt plus_1_eq_Suc singletonD sup_bot.right_neutral update_entries_dom update_entry_ran)
      then have h4: "r = insert_aux (SymbolNode {$$})  ((a # f_args) ! i) t0" using rew_insert_none 
        by (smt (verit, ccfv_SIG) distinct_upt fmdom'I fmdom'_empty fmempty_lookup fmran'_alt_def fmran_singleton fsingleton_iff h1 h3 option.sel rew_upd_entries_none sup_bot.right_neutral update_entries_dom)
      then have ms: "minimal_storage r" using hi h1 h2 i by blast
      then have"r \<noteq> empty_trie" 
        using fmap_distinct(1) h4 insert_aux.elims trie.distinct(1) trie.sel(3) by force
      then show "minimal_storage r \<and> r \<noteq> empty_trie" 
        using ms  by fastforce 
    qed
    then have "minimal_storage (SymbolNode {F f (Suc (length f_args)) $$:= ?m'})"
      using minimal_storage_node by blast
    then show ?thesis using "4.prems"(2)minimal_storage_udt None by auto  
  next
    case (Some m2)
    have dom_m2: "fmdom' m2= {0..<(Suc (length f_args))}"
      by (metis "4.prems"(1) Some atLeastLessThan_upt atLeast_upt length_suffixes list.size(3) nat.distinct(1) ws_fmdom')
    have h0: "\<And> i. i< Suc (length f_args) \<Longrightarrow> minimal_storage (insert_aux (m2 $$! i) ((a # f_args) ! i) t0)"
    proof-
      fix i 
      assume h1: "i< Suc (length f_args)"
      then have in_dom:"i  \<in>  fmdom' m2"
        by (simp add: dom_m2)
      then have h2: "well_structured (m2 $$! i)"
        using "4.prems"(1) Some
        by (metis fmdom'I fmdom'_notI fmran'I nat.distinct(1) option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases) 
      have "minimal_storage (m2 $$! i)"
        using "4.prems"(2) Some
        by (metis fmlookup_dom'_iff fmlookup_ran'_iff in_dom minimal_storage.simps option.sel trie.distinct(1) trie.sel(3))
      then show "minimal_storage (insert_aux (m2 $$! i) ((a # f_args) ! i) t0)"
        using 4 h1 h2 by presburger 
    qed
    have h3: "minimal_storage empty_trie" by auto
    have h4: "minimal_storage (SymbolNode (fmdrop (F f (Suc (length f_args))) m))"
      by (simp add: "4.prems"(2))
    let ?m' = "update_entries m2 [0..<Suc (length f_args)] (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) empty_trie"
    have ir: "\<And> i r . ?m'$$ i = Some r \<Longrightarrow> minimal_storage r \<and> r \<noteq> empty_trie"
    proof-
      fix i r
      assume h5: "?m'$$ i = Some r"
      then have h6:"i<Suc (length f_args)"
        by (metis (no_types, lifting) "4.prems"(1) Some Un_iff dom_m2 fmdom'I set_upt update_entries_dom ws_dom_fun2)
      then have h7: "r = insert_aux (m2 $$! i) ((a # f_args) ! i) t0  "
        using dom_m2 h5 insert_some_image by fastforce
      then have h8: "minimal_storage r"
        using h0 h6 by blast
      have "well_structured (m2 $$! i)"
        using h6 by (metis "4.prems"(1) Some fmdom'I fmdom'_notI fmran'I length_Cons nat.simps(3) option.collapse option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.simps ws_dom_fun)
      then have "r \<noteq> empty_trie"
        using h7 by (smt (verit, ccfv_SIG) fmap_distinct(1) insert_aux.elims trie.distinct(1) trie.sel(3) update_entry.elims well_structured.cases)
      then show "minimal_storage r \<and> r \<noteq> empty_trie"
        using h8 by blast
    qed
    then have "minimal_storage (SymbolNode {F f (Suc (length f_args)) $$:= ?m'})"
      by (smt (verit, del_insts) fmempty.rep_eq fmran'E fmran_empty' minimal_storage_node singletonD update_entry_ran)
    then show ?thesis  
      using "4.prems"(2) minimal_storage_udt by (auto simp add: Some h3 h4)
  qed
qed

lemma fmran'_singleton: "fmran' {k $$:= v} = {v}"
  by (simp add: fmran'_alt_def fmran_singleton)

lemma insert_var_adds_element:
  assumes "well_structured tr"
    shows "t \<in> to_set (insert_aux tr (Var x) t)"
  using assms
proof (cases tr)
  case (ws_node m)
  then show ?thesis  
  proof (cases "m $$ Star")
    case None
    then show ?thesis using ws_node None 
      by (simp add: update_entry_ran)
  next
    case (Some m2)
    then obtain ts where "m2 $$ 0 = Some (Leaf ts)"
      by (metis assms local.ws_node(1) ws_dom_var)
    then show ?thesis
      by (smt (verit, ccfv_SIG) fmdom'I fmdom'_notI fmupd_lookup insertCI insert_aux.simps(2) insert_leaf.simps(1) local.ws_node(1) option.case_eq_if option.sel Some to_set.simps(1) to_set_entry update_entry.simps)
  qed
qed

lemma insert_var_keeps_elements:
  assumes "well_structured (SymbolNode m)"
      and "t \<in> to_set (SymbolNode m)"
    shows "t \<in> to_set (insert_aux (SymbolNode m) (Var x) t0)"
proof (cases "m $$ Star")
  case None
  then show ?thesis 
    using assms None by (simp add: update_entry_ran) 
next
  case (Some m2)
  then obtain ts where "m2 $$ 0 = Some (Leaf ts)"
    by (meson assms(1) ws_dom_var)
  then show ?thesis using Some assms
    by (simp, metis fmlookup_ran'_iff fmupd_lookup insert_iff option.sel to_set.simps(1))
qed

lemma insert_var_subset:
  assumes "well_structured (SymbolNode m)"
  shows "to_set (insert_aux (SymbolNode m) (Var x) t) \<subseteq> insert t (to_set (SymbolNode m))"
proof (cases "m $$ Star")
  case None
  then show ?thesis
    by (clarsimp, metis fmempty_lookup fmran_empty' insertE singletonD to_set.simps(1) update_entry_ran)
next
  case (Some m2)
  then obtain ts where "m2 $$ 0 = Some (Leaf ts)"
    by (meson assms(1) ws_dom_var)
  then show ?thesis using Some assms
    by (simp, smt (verit, del_insts) UN_iff fmlookup_ran'_iff fmupd_lookup insert_iff option.sel subsetI to_set.simps(1))
qed

lemma insert_const_adds_element:
  assumes "well_structured tr"
   shows "t \<in> to_set (insert_aux tr (Fun f []) t)"
proof (cases tr)
  case (Leaf ts)
  then show ?thesis
    using assms by fastforce 
next
  case (SymbolNode m)
  then show ?thesis 
  proof (cases "m $$ F f 0")
    case None
    then show ?thesis 
      by (simp add: update_entry_ran SymbolNode)
  next
    case (Some m2)
    then obtain ts where "m2 $$ 0 = Some (Leaf ts)"
      by (metis SymbolNode assms ws_dom_const)
    then show ?thesis using SymbolNode Some 
      by (simp, metis fmran'I fmupd_lookup insert_iff to_set.simps(1))
  qed
qed

lemma insert_const_keeps_elements:
  assumes "well_structured (SymbolNode m)"
      and "t \<in> to_set (SymbolNode m)"
    shows "t \<in> to_set (insert_aux (SymbolNode m) (Fun f []) t0)"
  using assms
proof (cases "m $$ F f 0")
  case None
  then show ?thesis using assms None by (simp add: update_entry_ran) 
next
  case s1: (Some m)
  then obtain ts where "m $$ 0 = Some (Leaf ts)"
    by (metis assms(1) ws_dom_const)
  then show ?thesis using s1 assms
    by (simp, metis fmlookup_ran'_iff fmupd_lookup insert_iff option.sel to_set.simps(1))
qed

lemma insert_const_subset:
  assumes "well_structured (SymbolNode tr)"
    shows "to_set (insert_aux (SymbolNode tr) (Fun f []) t) \<subseteq> insert t (to_set (SymbolNode tr))"
proof (cases "tr $$ F f 0")
  case None
  then show ?thesis
    by (clarsimp, metis fmempty_lookup fmran_empty' insertE singletonD to_set.simps(1) update_entry_ran)
next
  case (Some m)
  then obtain ts where "m $$ 0 = Some (Leaf ts)"
    by (metis assms(1) ws_dom_const)
  then show ?thesis using Some assms
    by (clarsimp, metis (no_types, lifting) fmlookup_ran'_iff fmupd_lookup insert_iff option.sel to_set.simps(1))
qed

lemma insert_aux_adds_element: 
  assumes "well_structured tr "
    shows "t0 \<in> to_set (insert_aux tr t t0)"
  using assms
proof (induction t arbitrary: tr)
  case (Var x)
  then show ?case by (meson insert_var_adds_element)
next
  case (Fun f f_args) then show ?case
  proof (cases f_args)
    case Nil
    then show ?thesis
      by (simp add: Fun.prems insert_const_adds_element)  
  next
    case (Cons a as)
    then show ?thesis
    proof (cases tr)
      case (Leaf ts)
      then show ?thesis 
        using Fun.prems by force
    next
      case (SymbolNode m)
      then show ?thesis
      proof (cases "m $$ F f (Suc (length as))")
        case None
        let ?m' = " update_entries {$$} [0..<Suc (length as)] (\<lambda>i tr. if i < Suc (length as) then insert_aux tr ((a # as) ! i) t0 else undefined) empty_trie"
        have "t0 \<in> to_set (insert_aux empty_trie ((a # as) ! 0) t0)"
          using Fun.IH by (simp add: Cons ws_node)
        then have "\<exists>x\<in>fmran'?m' . t0 \<in> to_set x" 
          by (simp only: rew_fmran_updt_entries_empty, force)
        then show ?thesis by (simp add: local.Cons None update_entry_ran SymbolNode)
      next
        case (Some m2)
        let ?m'' = "update_entries m2 [0..<Suc (length as)]
        (\<lambda>i tr. if i < Suc (length as) then insert_aux tr ((a # as) ! i) t0 else undefined) empty_trie"
        have h0: "distinct [0..<Suc (length as)]"
          using distinct_upt by blast
        then have h1: "fmdom' m2 = set [0..<Suc (length as)]"
          by (metis SymbolNode Fun.prems Some atLeast_upt length_Cons list.distinct(1) ws_fmdom')
        have  h2: "t0 \<in> to_set (insert_aux (m2 $$! 0) ((a # as) ! 0) t0)"
          using Fun.IH by (metis SymbolNode Fun.prems Some fmdom'I fmdom'_notI fmran'I length_Cons list.set_intros(1) local.Cons nat.distinct(1) nth_Cons_0 option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases ws_dom_fun zero_less_Suc) 
        then have "fmran' ?m'' = (\<lambda>i.  (insert_aux (m2 $$! i) ((a # as) ! i) t0)) ` set  [0..<Suc (length as)]"
          using fmran_updt_entries [of "[0..<Suc (length as)]" m2 ] h0 h1 
          by auto
        then have "insert_aux (m2 $$! 0) ((a # as) ! 0) t0 \<in> fmran' ?m''"
          by (simp add: upt_conv_Cons)  
        then show ?thesis
          by (simp add: Some SymbolNode Cons, metis (no_types, lifting) h2 fmran'I fmupd_lookup nth_Cons_0)
      qed
    qed
  qed
qed 

lemma insert_aux_keeps_elements: 
  assumes "well_structured tr"
      and "t \<in> to_set tr"
    shows "t \<in> to_set (insert_aux tr t1 t2)"
    using assms
proof (induction tr t1 t2 rule: insert_aux.induct)
  case (1 s t t0)
  then show ?case
    by (simp add: not_well_structured_leaf) 
next
  case (2 m x t0)
  then show ?case
    by (meson insert_var_keeps_elements)
next
  case (3 m f t0)
  then show ?case 
    by (meson insert_const_keeps_elements)
next
  case (4 m f a f_args t0)
  then show ?case
  proof (cases "m $$ F f (Suc (length f_args))")
    case None
    then have "t \<in> to_set (SymbolNode m)"
      using "4.prems"(2) by blast
    then show ?thesis by (simp add: None  update_entry_ran)
  next
    case (Some m2)
    then obtain m3 where h1: "m3 \<in> fmran' m" and h2: "\<exists>tr2\<in>fmran' m3. t \<in> to_set tr2"
      using "4.prems"(2) by auto
    then show ?thesis
    proof (cases "m2 = m3")
      case True
      then have h3: "fmdom' m2 = {0..<Suc (length f_args)}"
        by (metis "4.prems"(1) Some atLeastLessThan_upt atLeast_upt diff_zero length_upt list.size(3) nat.distinct(1) ws_fmdom')
      then  obtain i where h4: "t\<in>to_set (m2 $$! i)" and h5: "i \<in> fmdom' m2"
        by (metis True fmdom'I fmran'E option.sel h2)
      then have ws: "well_structured (m2 $$! i)"
        by (metis "4.prems"(1) Some fmdom'I fmdom'_notI fmran'I nat.simps(3) option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases)
      then have "i <  Suc (length f_args)"
        by (meson "4.prems"(1) Some h5 ws_dom_fun2)
      then have gh: "t \<in> to_set (insert_aux (m2 $$! i) ((a # f_args) ! i) t0)"
        using "4.IH" h4 ws by presburger
      have di: "distinct [0..<Suc (length f_args)]"
        using distinct_upt by blast
      then have fm: "fmdom' m2 = set  [0..<Suc (length f_args)]"
        using atLeastLessThan_upt h3 by presburger
      let ?m'' = "update_entries m2 [0..<Suc (length f_args)]
        (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) empty_trie"
      have "fmran' ?m'' = (\<lambda>i.  (insert_aux (m2 $$! i) ((a # f_args) ! i) t0)) ` set  [0..<Suc (length f_args)]"
        using fmran_updt_entries [of "[0..<Suc (length f_args)]" m2] di fm
        by auto
      then have h6: "\<exists>m3\<in>fmran' ?m''. t \<in> to_set m3"
        using fm gh h5 by blast
      then have "?m''\<in> fmran' (m(F f (Suc (length f_args)) $$:= ?m''))"
        by (meson fmlookup_ran'_iff fmupd_lookup)
      then show ?thesis 
        using h6 Some 
        by auto
    next
      case False
      then show ?thesis using 4 h1 h2 Some
        by (simp, metis (no_types, lifting) fmlookup_ran'_iff fmupd_lookup option.inject)
    qed
  qed
qed

lemma insert_aux_subset:
  assumes "well_structured tr"
    shows "to_set (insert_aux tr t t0 ) \<subseteq> insert t0 (to_set tr)"
proof
  fix x
  assume "x \<in> to_set (insert_aux tr t t0)"
  then show "x \<in> insert t0 (to_set tr)"
    using assms
  proof (induction tr t t0 rule: insert_aux.induct)
    case (1 s t t0)
    then show ?case
      by blast 
  next
    case (2 m x t0)
    then show ?case
      by (meson subsetD insert_var_subset)
  next
    case (3 m f t0)
    then show ?case
      by (meson in_mono insert_const_subset)
  next
    case (4 m f a f_args t0)
    have h1: "x \<in> to_set (insert_aux (SymbolNode m) (Fun f (a # f_args)) t0)"
      using "4.prems" by blast
    then show ?case
    proof (cases "m $$ F f (Suc (length f_args))")
      case None  
      let ?m' = " update_entries {$$} [0..<Suc (length f_args)] (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) empty_trie"
      obtain xa where h2: "xa \<in> fmran' (children (insert_aux (SymbolNode m) (Fun f (a # f_args)) t0))"
        and h3: "\<exists> xaa \<in> fmran' xa. x\<in>  to_set xaa"
        using None update_entry_ran h1 subtrie_at_path.cases subtrie_to_set by auto
      then   have"xa \<in> fmran' (m(F f (Suc (length f_args)) $$:=?m'))"
        by (simp add: None)
      then  have "xa \<in> fmran' m \<or> xa = ?m'"
        using None update_entry_ran by force
      then  show ?thesis  
      proof (rule disjE)
        assume "xa \<in> fmran' m"
        then show ?thesis
          using h3 by fastforce 
      next
        assume h4: "xa = ?m'"
        then  obtain  xb where h5: "xb \<in> fmran' xa" and h6: "x \<in> to_set xb"
          using h2 h3 by blast
        obtain i where h1: "xa $$ i = Some xb"
          using h5 by auto
        then have "i\<in> fmdom' xa"
          by (simp add: fmdom'I)
        then have n0:"i < Suc (length f_args)"
          by (simp add: h4 update_entries_dom)
        then have n1: " xb = insert_aux empty_trie ((a # f_args) ! i) t0" using h1 h4 
          by (simp add: rew_upd_entries_none)
        consider (a) "x = t0" | (b) "x \<in> to_set xb"
          using h6 by blast
        then show ?thesis
        proof cases
          case a
          then show ?thesis
            by blast 
        next
          case b
          then show ?thesis 
            using h4
            by (simp, smt (verit, ccfv_threshold) well_structured_empty_trie 4 exists_leaf fmempty_lookup insert_iff n0 n1 not_well_structured_leaf option.distinct(1) subtrie_at_path.simps trie.sel(3))
        qed
      qed
    next
      case (Some m2)
      let ?m' = " update_entries m2 [0..<Suc (length f_args)] (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) empty_trie"
      obtain xa where h1: "xa \<in> fmran' (children (insert_aux (SymbolNode m) (Fun f (a # f_args)) t0))"
        and h2: "\<exists> xm2 \<in> fmran' xa. x\<in>  to_set xm2"
        using Some update_entry_ran h1 subtrie_at_path.cases subtrie_to_set by auto
      then   have"xa \<in> fmran' (m(F f (Suc (length f_args)) $$:=?m'))"
        by (simp add: Some)
      then  have " xa \<in> fmran' m \<or> xa = ?m'"
        using Some  update_entry_ran
        by (smt (verit, best) fmlookup_ran'_iff fmupd_lookup option.inject) 
      then  show ?thesis  
      proof (rule  disjE)
        assume " xa \<in> fmran' m"
        then show ?thesis
          using h2 by fastforce 
      next
        assume h3: "xa = ?m'"
        then obtain xb where h4: " xb \<in> fmran' xa" and h5: " x\<in>  to_set xb"
          using h1 h2 by blast
        obtain  i where h1: "xa $$ i = Some xb"
          using h4 by auto
        then have r:"i\<in> fmdom' xa"
          by (simp add: fmdom'I)
        then have b: "fmdom' m2 = (set  [0..<Suc (length f_args)])"
          by (metis Some atLeast_upt length_Cons list.size(3) nat.distinct(1)  "4.prems"(2) ws_fmdom')
        then have n0:"i < Suc (length f_args)"
          using h3 b r by (simp add:  update_entries_dom)
        then have n3: "xb = insert_aux (m2 $$!i )  ((a # f_args) ! i) t0"  using h1 h3 b  n0 insert_some_image[of i f_args m2 a t0]
          by fastforce
        have n1: "well_structured (m2 $$! i)"
          by (metis (no_types, lifting) "4.prems"(2) Some Un_iff h3 b fmdom'I fmdom'_notI fmran'I nat.simps(3) option.collapse option.sel r symbol.distinct(1) symbol.inject trie.sel(3) update_entries_dom well_structured.cases well_structured_map_entry.cases)
        then have g: "x = t0 \<or> x \<in> to_set xb"
          by (simp add: h5)
        then show ?thesis
        proof (cases "x = t0")
          case True
          then show ?thesis
            by blast 
        next
          case False
          then show ?thesis
            by (metis "4.IH" "4.prems"(2) Some fmdom'_notI h5 insertE insertI2 key_map_entry_simp length_Cons list.discI n0 n1 n3 option.exhaust_sel to_set_entry)
        qed
      qed
    qed
  qed
qed

lemma elim_sound_fp:
  assumes h1: "sound_storage_from_position (SymbolNode m) p" 
      and h2: "sound_storage_from_position (SymbolNode {s $$:= m1}) p"
    shows "sound_storage_from_position (SymbolNode (m(s $$:= m1))) p"
  unfolding sound_storage_from_position_def
proof (intro allI impI)
  fix t p2 sa 
  assume h: "subtrie_at_path (SymbolNode (m(s $$:= m1))) p2 (Leaf (insert t sa))"
  show "path_of_term t (p @ p2)"
  proof (cases p2)
    case Nil
    then show ?thesis
      using h subtrie_at_nil by blast 
  next
    case (Cons a list)
    then show ?thesis 
    proof-
      from h1 have g1: "subtrie_at_path (SymbolNode m) (a # list) (Leaf (insert t sa)) \<longrightarrow> path_of_term t (p @ (a # list))"
        using Cons sound_storage_from_position_def by blast
      from  h2 have g2: "subtrie_at_path (SymbolNode {s $$:= m1}) (a # list) (Leaf (insert t sa))\<longrightarrow> path_of_term t (p @ (a # list))" 
        using Cons sound_storage_from_position_def by blast
      then show ?thesis
        by (smt (verit, ccfv_threshold) h fmupd_lookup g1 g2 list.distinct(1) local.Cons subtrie_at_path.simps trie.sel(3))
    qed
  qed
qed

lemma subtrie_at_path_step_simp:
  "subtrie_at_path (SymbolNode m) ((k, val) # ps) (Leaf ts) =
    (\<exists>a m2. m $$ k = Some a \<and> a $$ val = Some m2 \<and> subtrie_at_path m2 ps (Leaf ts))"
  using subtrie_cons subtrie_at_path_step by blast

declare well_structured_cases [rule del]

lemma insert_preserves_sound:
  assumes ws: "well_structured f_args "
      and sub: "subterm_at_path t p t' "
      and ss: "sound_storage_from_position f_args p "
  shows "sound_storage_from_position (insert_aux f_args t' t ) p"
  using assms
proof (induct f_args t' t arbitrary: p rule: insert_aux.induct)
  case (1 s t t0)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x t0)
  then show ?case
  proof (cases "m $$ Star")
    case None
    have h1: "sound_storage_from_position (SymbolNode {Star $$:= {0 $$:= Leaf {t0}}}) p"
      unfolding sound_storage_from_position_def
    proof (intro allI impI)
      fix t p2 sa
      assume h1: "subtrie_at_path (SymbolNode {symbol.Star $$:= {0 $$:= Leaf {t0}}}) p2 (Leaf (insert t sa))"
      have "p2 = [(Star, 0)]"
        by (meson h1 subtrie_string_4)
      then show "path_of_term t (p @ p2)"
        using "2.prems"(2) h1 path_of_term_var subterm_at_path_path_of_term 
        using subtrie_string_1 by fastforce
    qed
    then show ?thesis using 2 None
      by (auto intro: elim_sound_fp)
  next
    case (Some m2)
    then obtain ts where s2: "m2 $$ 0 = Some (Leaf ts)"
      using "2.prems"(1) ws_dom_var by blast
    have "sound_storage_from_position (SymbolNode ({Star $$:= {0 $$:= Leaf (insert t0 ts)}})) p"
      unfolding sound_storage_from_position_def
    proof (intro allI impI)
      fix t p2 s
      assume hy1: "subtrie_at_path (SymbolNode {Star $$:= {0 $$:= Leaf (insert t0 ts)}}) p2 (Leaf (insert t s)) "
      show "path_of_term t (p @ p2)"
      proof -
        have "p2 = [(Star, 0)]"
          by (meson hy1 subtrie_string_4)
        then show ?thesis
          using "2.prems" hy1 Some s2
          by (smt (verit, ccfv_threshold) insertE insertI1 insert_Diff non_empty_to_set_subtrie path_of_term_var singletonD sound_storage_from_position_def subterm_at_path_path_of_term subtrie_at_path_cases subtrie_at_path_step subtrie_string_1 to_set.simps(1) trie.distinct(1))
      qed
    qed
    then have "sound_storage_from_position (SymbolNode ({Star $$:= m2(0 $$:= Leaf (insert t0 ts))})) p"
      by (metis (no_types, lifting) "2.prems"(1) dom_res_singleton fmdom'_notD fmfilter_true fmupd_idem option.distinct(1) Some ws_dom_var)
    then show ?thesis using 2 Some s2
      by (auto intro: elim_sound_fp)
  qed
next
  case (3 m f t0)
  then show ?case
  proof (cases "m $$ F f 0")
    case None
    have h1: "sound_storage_from_position (SymbolNode {  F f 0 $$:= {0 $$:= Leaf {t0}}}) p"
      unfolding sound_storage_from_position_def
    proof (intro allI impI)
      fix t p2 sa
      assume hy1: "subtrie_at_path (SymbolNode { F f 0 $$:= {0 $$:= Leaf {t0}}}) p2 (Leaf (insert t sa))"
      show  "path_of_term t (p @ p2)"
      proof -
        have "p2 = [( F f 0, 0)]"
          by (meson hy1 subtrie_string_4)
        then show ?thesis
          using "3.prems"(2) hy1 path_of_term_const subterm_at_path_path_of_term  subtrie_string_1 by fastforce 
      qed
    qed
    then show ?thesis using 3 None
      by (auto intro: elim_sound_fp)
  next
    case (Some m2)
    then obtain ts where s2: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "3.prems"(1) ws_dom_const)
    have "sound_storage_from_position (SymbolNode ({  F f 0 $$:= {0 $$:= Leaf (insert t0 ts)}})) p"
      unfolding sound_storage_from_position_def
    proof (intro allI impI)
      fix t p2 s
      assume hy1:" subtrie_at_path (SymbolNode { F f 0 $$:= {0 $$:= Leaf (insert t0 ts)}}) p2 (Leaf (insert t s))"
      have "p2 = [(F f 0, 0)]"
        by (meson hy1 subtrie_string_4)
      then show "path_of_term t (p @ p2)"
        using "3.prems" hy1 Some s2
        by (smt (verit, ccfv_threshold) insertE insertI1 insert_Diff path_of_term.intros(2) sound_storage_from_position_def subterm_at_path_path_of_term subtrie_at_path.simps subtrie_string_1)
    qed
    then have "sound_storage_from_position (SymbolNode ({F f 0 $$:= m2(0 $$:= Leaf (insert t0 ts))})) p"
      by (metis (no_types, lifting) "3.prems"(1) dom_res_singleton fmdom'_notD fmfilter_true fmupd_idem option.distinct(1) Some ws_dom_const)
    then show ?thesis using 3 s2 Some 
      by (auto intro: elim_sound_fp)
  qed
next
  case (4 m f a f_args t0)
  then show ?case
  proof (cases "m $$ F f (Suc (length f_args))")
    case None
    let ?m' = "update_entries {$$} [0..<Suc (length f_args)]
            (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) empty_trie"
    have domm': "fmdom' ?m' = {..<Suc (length f_args)}"
      by (simp add: atLeast_upt update_entries_dom)
    have hi: "\<And> i. i < Suc (length f_args) \<Longrightarrow> sound_storage_from_position (insert_aux empty_trie ((a # f_args) ! i) t0) (p@[(F f (Suc (length f_args)) , i)])"
    proof -
      fix i
      assume h1: "i < Suc (length f_args)"
      show " sound_storage_from_position (insert_aux empty_trie ((a # f_args) ! i) t0) (p@[(F f (Suc (length f_args)) , i)])"
      proof -
        have  h2: "well_structured empty_trie"
          by  (simp add: ws_node)
        then  have h3: "subterm_at_path t0  (p @ [(F f (Suc (length f_args)) , i)])((a # f_args) ! i) "
          using "4.prems"(2) h1 subsubterm_at_path by fastforce   
        then show ?thesis
          using "4.hyps"[of i "empty_trie" "(p @ [(F f (Suc (length f_args)), i)])"] h1 h2 
          by (metis sound_storage_from_position_def no_subtrie_in_empty_trie )
      qed
    qed
    have "sound_storage_from_position(SymbolNode {F f (Suc (length f_args)) $$:= ?m'}) p" 
      unfolding sound_storage_from_position_def
    proof(intro allI impI )
      fix t p2 s
      assume h0: "subtrie_at_path (SymbolNode {F f (Suc (length f_args)) $$:= ?m'}) p2 (Leaf (insert t s))"
      show "path_of_term t (p @ p2) "
      proof (cases p2)
        case Nil
        then show ?thesis
          using h0 subtrie_at_nil by blast  
      next
        case (Cons p0 list)
        then show ?thesis proof(cases p0)
          case (Pair symb b)
          then have h1: "symb = F f (Suc (length f_args)) " using h0 subtrie_string_2 Cons by meson
          then have h2 : "b <  (Suc (length f_args))" using h0  Cons  subtrie_string_3 domm' Pair
            by (metis (no_types, lifting) atLeast_upt ex_nat_less_eq not_less_eq set_upt)
          have "sound_storage_from_position (insert_aux empty_trie ((a # f_args) ! b) t0) (p @ [(F f (Suc (length f_args)), b)])"
            using h2 hi by presburger
          then show ?thesis 
            by (smt (verit, best) Pair append.assoc append.left_neutral append_Cons atLeast_upt distinct_upt domm' elim_sub fmempty_lookup fmupd_lookup h0 h1 h2 local.Cons rew_upd_entries_none sound_storage_from_position_def subtrie_string_3)
        qed
      qed
    qed
    then show ?thesis
      by (auto simp add:None  intro: elim_sound_fp "4.prems"(3))
  next
    case (Some aa)
    let ?m'= "update_entries aa [0..<Suc (length f_args)]
            (\<lambda>i tr. if i < Suc (length f_args) then insert_aux tr ((a # f_args) ! i) t0 else undefined) empty_trie"
    have domaa' :"fmdom' aa = {..<Suc (length f_args)}"
      by (metis "4.prems"(1) Some length_Cons neq_Nil_conv ws_fmdom')
    then have domm' :"fmdom' ?m' = {..<Suc (length f_args)}"
      by (simp add: atLeast0LessThan update_entries_dom)
    have hi:" \<And> i. i  < Suc (length f_args) \<Longrightarrow> sound_storage_from_position (insert_aux  (aa$$!i)((a # f_args) ! i) t0) (p@[(F f (Suc (length f_args)) , i)])"
    proof-
      fix i
      assume h1: " i  < Suc (length f_args)"
      show " sound_storage_from_position (insert_aux  (aa$$!i) ((a # f_args) ! i) t0) (p@[(F f (Suc (length f_args)) , i)])"
      proof-  have  h2: " well_structured (aa$$!i)"
          by (metis "4.prems"(1) Some fmdom'I fmdom'_notI fmran'I h1 key_map_entry_simp length_Cons list.distinct(1) nat.distinct(1) option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases)
        then  have h3: " subterm_at_path t0  (p@[(F f (Suc (length f_args)) , i)])((a # f_args) ! i) "
          using "4.prems"(2) h1 subsubterm_at_path by fastforce 
        then show ?thesis
          using "4.hyps"[of i "(aa$$!i)" "(p @ [(F f (Suc (length f_args)), i)])"] h1 h2
          by (metis "4.prems"(1) "4.prems"(3) Some fmdom'_notI key_map_entry_simp length_Cons list.distinct(1) option.collapse sound_storage_from_position_subtrie) 
      qed
    qed
    have "sound_storage_from_position(SymbolNode {F f (Suc (length f_args)) $$:= ?m'})p" 
      unfolding sound_storage_from_position_def
    proof(intro allI impI )
      fix t p2 s
      assume h0: "subtrie_at_path (SymbolNode{F f (Suc (length f_args)) $$:= ?m'}) p2 (Leaf (insert t s))"
      show " path_of_term t (p @ p2) " proof (cases p2)
        case Nil
        then show ?thesis
          using h0  subtrie_at_nil by blast 
      next
        case (Cons p0 list)
        then show ?thesis
        proof(cases p0)
          case (Pair symb b)
          then have h1: "symb =F f (Suc (length f_args)) " using h0 subtrie_string_2 Cons   by meson
          then have h2 : "b <(Suc (length f_args))" using h0  Cons  subtrie_string_3 domm' Pair
            by (metis (no_types, lifting) atLeast_upt ex_nat_less_eq not_less_eq set_upt)
          have h13:"?m' $$! b = (insert_aux (aa$$!b) ((a # f_args) ! b) t0)"
            using insert_some_image [of b f_args aa] domaa' h2
            by (simp add: atLeast_upt)
          have h32 :"sound_storage_from_position (insert_aux (aa$$!b) ((a # f_args) ! b) t0) (p @ [(F f (Suc (length f_args)), b)])"
            using h2 hi by presburger
          have  h5: "subtrie_at_path  (insert_aux (aa$$!b) ((a # f_args) ! b) t0) list (Leaf (insert t s))"
            using h0 h1 h13 Pair Cons
            by (metis (no_types, lifting) elim_sub fmdom'_notI fmupd_lookup option.collapse subtrie_string_3)
          then show ?thesis
            by (metis Pair append.assoc append_Cons append_Nil h1 h32 local.Cons sound_storage_from_position_def)
        qed
      qed
    qed
    then show ?thesis
      by (auto simp add:Some  intro: elim_sound_fp "4.prems"(3))
  qed
qed

lemma  elim_complete_fp:
  assumes "m $$ s = None"
      and "complete_storage_from_position (SymbolNode m) p"
      and "complete_storage_from_position (SymbolNode {s $$:= a}) p" 
    shows "complete_storage_from_position (SymbolNode (m(s $$:= a))) p"
(*proof -
  have "\<And>t p2. t \<in> to_set (SymbolNode (m(s $$:= a))) \<Longrightarrow>
        path_of_term t (p @ p2) \<Longrightarrow>
              (\<exists>ts. subtrie_at_path (SymbolNode (m(s $$:= a))) p2 (Leaf (insert t ts)))"
  proof -
    fix t p2
    assume h1: "t \<in> to_set (SymbolNode (m(s $$:= a)))" and h2: "path_of_term t (p @ p2)"
    show "\<exists>ts. subtrie_at_path (SymbolNode (m(s $$:= a))) p2 (Leaf (insert t ts))"
    proof (cases p2)
      case Nil
      then show ?thesis
        by (smt (verit, ccfv_threshold) assms(2,3) complete_storage_from_position_def exists_leaf fmap_of_list_simps(2) fmempty_of_list fmlookup_add fmupd_alt_def h1 h2 subtrie_at_nil subtrie_at_path.cases subtrie_to_set to_set_entry trie.sel(3))
    next
      case (Cons a as)
      then show ?thesis using assms subtrie_cons subtrie_at_path_step apply(clarsimp simp add: complete_storage_from_position_def) sledgehammer
        by (smt (verit) assms(2) assms(3) complete_storage_from_position_def exists_leaf fmempty_lookup fmupd_lookup h1 h2 subtrie_at_path.cases subtrie_at_path_step subtrie_string_2 subtrie_to_set to_set_entry trie.distinct(1) trie.sel(3))
    qed
  then show ?thesis
    using complete_storage_from_position_def by blast
qed*)
  using assms apply(clarsimp simp add: complete_storage_from_position_def)
  apply (case_tac p2)
   apply (metis fmempty_lookup insert_iff subtrie_at_nil update_entry_ran)
  apply auto
  by (smt (z3) fmempty_lookup fmlookup_ran'_iff fmupd_lookup option.distinct(1) subtrie_cons subtrie_at_path_step)

lemma complete_var:
  assumes "well_structured (SymbolNode m)"
      and "subterm_at_path t0 p (Var x)"
      and "complete_storage_from_position (SymbolNode m) p"
    shows "complete_storage_from_position (insert_aux (SymbolNode m) (Var x) t0) p"
  using assms
proof (cases "m $$ Star")
  case None
  have "\<And>p2. path_of_term t0 (p @ p2) \<Longrightarrow>
          \<exists>s. subtrie_at_path (SymbolNode {symbol.Star $$:= {0 $$:= Leaf {t0}}}) p2 (Leaf (insert t0 s))" 
    using assms
    by (metis (no_types, lifting) fmupd_lookup path_var path_of_subterm subtrie_at_path_empty subtrie_at_path_step)
  then have "complete_storage_from_position (SymbolNode {symbol.Star $$:= {0 $$:= Leaf {t0}}}) p"
    by (simp add: fmran'_alt_def fmran_singleton complete_storage_from_position_def)
  then show ?thesis 
    using assms None  by  (auto intro:elim_complete_fp) 
next
  case (Some m2)
  then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
    using assms(1) ws_dom_var by blast
  then show ?thesis
    unfolding complete_storage_from_position_def
  proof (intro allI impI)
    fix t p2
    assume to: "t \<in> to_set (insert_aux (SymbolNode m) (Var x) t0) "
    assume p1: "path_of_term t (p @ p2) "
    consider
         (c1)  "t = t0"
      |  (c2) " t \<in> to_set  (SymbolNode m)"
      using assms(1) insert_aux_subset to by blast
    then show " \<exists>ts. subtrie_at_path (insert_aux (SymbolNode m) (Var x) t0) p2 (Leaf (insert t ts))"
    proof cases
      case c1
      then have "p2 = [(Star,0)]"
        by (metis assms(2) p1 path_var path_of_subterm)
      then show ?thesis using p1 c1 h Some
        by (simp, meson fmupd_lookup subtrie_at_path_empty subtrie_at_path_step_simp)
    next
      case c2
      then obtain ts2 where s1: "subtrie_at_path (SymbolNode m) p2 (Leaf (insert t ts2))"
        by (meson assms(3) complete_storage_from_position_def p1)
      then show ?thesis
      proof (cases "p2")
        case Nil
        then show ?thesis
          using s1 subtrie_at_nil by blast  
      next
        case (Cons p0 list) 
        then show ?thesis
        proof (cases p0)
          case (Pair s i)
          then show ?thesis
          proof (cases "s = Star")
            case True
            then have b0: "i = 0"
              using Pair Cons s1 assms  end_path_var p1 by blast 
            then have "list = []" 
              using Pair True end_path_var local.Cons p1 by blast 
            then have p2: "p2 = [(Star,0)]"
              using Pair True b0 local.Cons by blast
            then obtain ts3 where "insert t0 ts = insert t ts3"
              using Some  Pair b0 h s1 Cons True assms  
              by (metis (no_types, lifting) insert_absorb insert_iff subtrie_to_set_entry to_set.simps(1))
            then show ?thesis
              by (clarsimp simp add: Some Pair h p2, metis (no_types, opaque_lifting) fmupd_lookup subtrie_at_path.simps)
          next
            case False
            from s1 obtain m4 m3 where "m $$ s = Some m4 \<and> m4 $$ i = Some m3 \<and> subtrie_at_path m3 list (Leaf (insert t ts2)) "
              by (metis Pair local.Cons subtrie_cons)
            then have "subtrie_at_path (insert_aux (SymbolNode m) (Var x) t0) p2 (Leaf (insert t ts2))"
              by (simp add: Pair Cons, metis False fmupd_lookup subtrie_at_path_step_simp)
            then show ?thesis 
              by meson 
          qed
        qed
      qed
    qed
  qed
qed

lemma complete_const:
  assumes "well_structured (SymbolNode m)"
      and "subterm_at_path t0 p (Fun f [])"
      and "complete_storage_from_position (SymbolNode m) p"
    shows "complete_storage_from_position (insert_aux (SymbolNode m) (Fun f []) t0) p"
  using assms
proof (cases "m $$ F f 0")
  case None
  have "\<And>p2. path_of_term t0 (p @ p2) \<Longrightarrow>
          \<exists>s. subtrie_at_path (SymbolNode {F f 0 $$:= {0 $$:= Leaf {t0}}}) p2 (Leaf (insert t0 s))" 
    using assms
    by (metis (no_types, lifting) fmupd_lookup path_const path_of_subterm subtrie_at_path_empty subtrie_at_path_step)
  then  have "complete_storage_from_position (SymbolNode {F f 0 $$:= {0 $$:= Leaf {t0}}}) p"
    by (simp add: fmran'_alt_def fmran_singleton complete_storage_from_position_def)
  then show ?thesis 
    using assms None by (auto intro: elim_complete_fp) 
next
  case (Some m2)
  then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
    by (meson assms(1) ws_dom_const)
  then show ?thesis
    unfolding  complete_storage_from_position_def
  proof (intro allI impI)
    fix t p2
    assume to: "t \<in> to_set (insert_aux (SymbolNode m) (Fun f []) t0) "
    assume p1: "path_of_term t (p @ p2) "
    consider 
         (c1) "t = t0"
      |  (c2) "t \<in> to_set  (SymbolNode m)"
      by (meson assms(1) in_mono insertE insert_aux_subset to)
    then  show" \<exists>ts. subtrie_at_path (insert_aux (SymbolNode m) (Fun f []) t0) p2 (Leaf (insert t ts))"
    proof cases
      case c1
      then have "p2 = [(F f 0, 0)]"
        by (metis assms(2) p1 path_const path_of_subterm)
      then show ?thesis  using  p1 c1 h Some
        by (simp, meson fmupd_lookup subtrie_at_path_empty subtrie_at_path_step_simp)
    next
      case c2
      then obtain s where s1: "subtrie_at_path (SymbolNode m) p2 (Leaf (insert t s))"
        by (meson assms(3) complete_storage_from_position_def p1)
      then show ?thesis
      proof (cases p2)
        case Nil
        then show ?thesis
          using s1 
          using subtrie_at_nil by blast 
      next
        case (Cons p0 list) 
        then show ?thesis
        proof (cases p0)
          case (Pair sym i) then show ?thesis
          proof (cases "sym = F f 0")
            case True
            then have b0: "i = 0" 
              using Pair Cons s1 assms
              by (metis end_path_const p1)  
            then have "list = []" 
              by (metis h Pair Some True elim_sub local.Cons s1 subtrie_at_path_cases trie.distinct(1))
            then have p2: "p2 = [(F f 0, 0)]"
              using Pair True b0 local.Cons by blast
            then obtain s where t1: "insert t0 ts = insert t s"
              using Some  Pair b0 s1 h Cons True assms  
              by (metis (no_types, lifting) insert_absorb insert_iff subtrie_to_set_entry to_set.simps(1))
            then show ?thesis
              by (simp add: Some Pair h p2 ,metis (no_types, opaque_lifting) fmupd_lookup subtrie_at_path.simps)
          next
            case False
            from s1  obtain m3 m2 where "m $$ sym = Some m3 \<and> m3 $$ i = Some m2 \<and> subtrie_at_path m2 list (Leaf (insert t s)) "
              by (metis Pair local.Cons subtrie_cons)
            then have "subtrie_at_path (insert_aux (SymbolNode m) (Fun f []) t0) p2 (Leaf (insert t s))"
              by (simp add: Pair Cons, metis False fmupd_lookup subtrie_at_path_step_simp)
            then show ?thesis
              by meson 
          qed
        qed
      qed
    qed
  qed
qed

lemma exists_term_at_end_path: 
  assumes "path_of_term t ((F f n, b) # list)"
      and "k < n" 
    shows "\<exists>list2. path_of_term t ((F f n, k) # list2)" 
proof (cases t)
  case (Var x)
  then show ?thesis  using assms by(simp add: path_var)
next
  case (Fun f f_args)
  then show ?thesis
  proof (cases f_args)
    case Nil
    then show ?thesis using assms 
      by (simp add: Fun path_const)
  next
    case (Cons a list)
    then show ?thesis using assms Fun path_func 
      by (metis exists_path fst_conv length_Cons list.distinct(1) list.sel(1) path_of_term_func symbol.inject)
  qed
qed

lemma insert_preserves_complete:
  assumes "well_structured f_args "
      and "subterm_at_path t p t' "
      and "complete_storage_from_position f_args p"
    shows "complete_storage_from_position (insert_aux f_args t' t) p"
  using assms
proof(induct f_args t' t arbitrary:p rule:insert_aux.induct)
  case (1 s t t0)
  then show ?case 
    using not_well_structured_leaf by blast
next
  case (2 m x t0)
  then show ?case 
    by (meson complete_var)
next
  case (3 m f t0)
  then show ?case
    by (meson complete_const)
next
  case (4 m f a largs t0)
  then show ?case 
  proof (cases "m $$ F f (Suc(length largs))")
    case None
    let ?m' = " update_entries {$$} [0..<Suc (length largs)]
         (\<lambda>i tr. if i < Suc (length largs) then insert_aux tr ((a # largs) ! i) t0 else undefined)
         empty_trie"
    have dom':"fmdom'?m' = {0..<Suc (length largs)} "
      by (simp add: atLeast_upt update_entries_dom)
    have hi: "\<And>i.   i < Suc (length largs) \<Longrightarrow> complete_storage_from_position (insert_aux empty_trie ((a # largs) ! i) t0) (p@[( F f (Suc(length largs)),i )])"
    proof- 
      fix i
      assume hi1: " i < Suc (length largs) " 
      have hi0: "well_structured empty_trie"
        by (simp add: ws_node)
      have hi2: "subterm_at_path t0 (p@[( F f (Suc(length largs)),i )]) ((a # largs) ! i) "
        using "4.prems"(2) hi1 subsubterm_at_path by fastforce    
      have "complete_storage_from_position empty_trie (p@[( F f (Suc(length largs)),i )])"
        by (meson complete_storage_from_position_def exists_leaf no_subtrie_in_empty_trie )
      then  show " complete_storage_from_position (insert_aux empty_trie ((a # largs) ! i) t0)   (p @ [(F f (Suc (length largs)), i)]) "
        using "4.hyps" hi0 hi1 hi2 by blast
    qed
    have "complete_storage_from_position (SymbolNode {F f (Suc (length largs)) $$:= ?m'}) p"
      unfolding complete_storage_from_position_def 
    proof (intro allI impI ,clarsimp ; elim fmran'E; simp split:if_splits ; clarsimp)
      fix t  p2 m0 i
      assume as0 : "?m' $$ i = Some m0"
      assume as1:" t \<in> to_set m0" 
      assume as3:"path_of_term t (p @ p2)" 
      have indom':" i < Suc (length largs)" using dom' as0
        by (metis (no_types, lifting) ex_nat_less_eq fmdom'I not_less_eq) 
      then have defxa: "m0 = (insert_aux empty_trie ((a # largs) ! i) t0)"  using  insert_none_image  as0 by fastforce
      then have r1:"t= t0"
        by (metis insert_aux_subset as1 empty_iff in_mono insert_iff no_subtrie_in_empty_trie non_empty_to_set_subtrie well_structured_empty_trie)
      then  show "\<exists>s. subtrie_at_path  (SymbolNode  {F f (Suc (length largs)) $$:=?m' })  p2 (Leaf (insert t s)) " 
      proof  (cases p2)
        case Nil
        then show ?thesis
          by (metis "4.prems"(2) append.right_neutral as3 sub_path_not_path) 
      next
        case (Cons p0 list)
        then show ?thesis proof(cases p0)
          case (Pair sym  b)
          then  have t0:  "sym = F f (Suc( length largs))"
            using path_func path_of_subterm "4.prems"(2) as3 local.Cons r1 by fastforce 
          then have g:  " b < (Suc( length largs))"using path_func path_of_subterm Pair as3 
            by (metis "4.prems"(2) list.sel(1) local.Cons r1 snd_conv)
          have h2: "t\<in> to_set (insert_aux empty_trie ((a # largs) ! b) t)"
            by (simp add: insert_aux_adds_element ws_node)
          then  obtain s where h1:" subtrie_at_path (insert_aux empty_trie ((a # largs) ! b) t0) list (Leaf (insert t s))"
            using Pair as3 local.Cons t0 g hi h2
            by (metis append_Cons append_assoc complete_storage_from_position_def r1 same_append_eq self_append_conv)
          then have "subtrie_at_path  (SymbolNode   {F f (Suc (length largs)) $$:=   ?m'})   ((sym, b) # list)(Leaf (insert t s))"
            by (simp add: g insert_none_image subtrie_at_path_step t0) 
          then show ?thesis
            by (metis Pair local.Cons) 
        qed
      qed
    qed
    then show ?thesis 
      by  (fastforce  simp add: None  intro:  None "4.prems"(3)  elim_complete_fp  )
  next
    case (Some aa)
    let ?m' = " update_entries aa [0..<Suc (length largs)]
         (\<lambda>i tr. if i < Suc (length largs) then insert_aux tr ((a # largs) ! i) t0 else undefined)
         empty_trie"
    have domaa:"fmdom' aa = {0..<Suc (length largs)} "
      by (metis "4"(2) Some atLeastLessThan_upt atLeast_upt length_suffixes list.size(3) nat.distinct(1) ws_fmdom') 
    then  have dom':"fmdom'?m' = {0..<Suc (length largs)} " 
      using update_entries_dom  by (metis atLeastLessThan_upt sup.idem)
    have  fmran_image: "\<And>i.   i < Suc (length largs) \<Longrightarrow> (?m' $$ i = Some  (insert_aux (aa$$! i) ((a # largs) ! i) t0))"
      by (simp add: domaa insert_some_image)
    have his: "\<And>i.   i < Suc (length largs) \<Longrightarrow> complete_storage_from_position (insert_aux (aa$$! i) ((a # largs) ! i) t0) (p@[( F f (Suc(length largs)),i )])"
    proof- 
      fix i
      assume hi1: " i < Suc (length largs) " 
      have hi0: "well_structured (aa$$! i)" 
        using Some hi1  
        by (metis "4.prems"(1) fmdom'I fmdom'_notI fmran'I length_suffixes nat.simps(3) option.collapse option.sel symbol.distinct(1) symbol.inject trie.inject(2) well_structured.cases well_structured_map_entry.cases ws_dom_fun)
      have hi2: "subterm_at_path t0 (p@[( F f (Suc(length largs)),i )]) ((a # largs) ! i) "
        using "4.prems"(2) hi1 subsubterm_at_path by fastforce 
      have th1:  "complete_storage_from_position (aa$$! i) (p@[( F f (Suc(length largs)),i )])"
        by (metis "4.prems"(1,3) Some complete_storage_from_position_subtrie fmdom'_notI hi1 length_Cons option.collapse ws_dom_fun)
      then  show hi:" complete_storage_from_position (insert_aux (aa$$! i) ((a # largs) ! i) t0)   (p @ [(F f (Suc (length largs)), i)]) "
        using "4.hyps" hi0 hi1 hi2 by blast
    qed
    show ?thesis unfolding complete_storage_from_position_def 
    proof (intro allI impI )
      fix t  p2
      assume as0 : "t \<in> to_set (insert_aux (SymbolNode m) (Fun f (a # largs)) t0) "
      assume as3:"path_of_term t (p @ p2)"
      then  have r1:"\<exists> s. subtrie_at_path (insert_aux (SymbolNode m) (Fun f (a # largs)) t0) p2 (Leaf (insert t s))"
      proof (cases "p2")
        case Nil
        then show ?thesis
          by (metis "4.prems"(2) append.right_neutral as3 sub_path_not_path) 
      next
        case (Cons p0 list)
        then show ?thesis proof(cases p0)
          case (Pair sym  b)
          then show ?thesis
          proof(cases "sym = F f (Suc (length largs)) ")
            case T1: True
            then have binf: "b < Suc (length largs)"
              using path_func path_of_subterm fun_is_subterm_at_last local.Cons 
              by (smt (verit, ccfv_SIG) Pair Suc_le_length_iff as3 le_refl length_Cons list.sel(1) snd_conv)
            then have w1:  "well_structured (aa $$! b)" 
              by (metis (no_types, lifting) "4.prems"(1) Some Zero_neq_Suc dom' domaa fmdom'_alt_def fmdomI fmdom_notI fmran'I fmran_image option.exhaust_sel option.sel symbol.distinct(1) symbol.inject trie.inject(2) well_structured.simps well_structured_map_entry.cases)
            then have in_to:" t \<in> to_set (insert_aux (aa $$! b) ((a # largs) ! b) t0)"
              by (smt (verit, ccfv_threshold) "4.prems"(1,3) Pair Some T1 as0 as3 binf complete_storage_from_position_def dom' domaa fmdom'_notD fmdom'_notI in_mono insert_aux_adds_element insert_aux_subset insert_iff insert_aux_keeps_elements insert_some_image local.Cons option.collapse set_upt subtrie_to_set_entry update_entries_dom)
            then have com:"complete_storage_from_position (insert_aux (aa$$! b) ((a # largs) ! b) t0)   (p @ [(F f (Suc (length largs)), b)])"
              using his binf   by blast
            then obtain s where  " subtrie_at_path (insert_aux (aa $$! b) ((a # largs) ! b) t0) list (Leaf (insert t s)) "
              by (metis Pair T1 append.assoc append_Cons append_Nil as3 complete_storage_from_position_def in_to local.Cons) 
            then have "subtrie_at_path (SymbolNode (m(F f (Suc (length largs)) $$:= ?m'))) ((F f (Suc (length largs)), b) # list) (Leaf (insert t s))"
              by (simp add: binf fmran_image subtrie_at_path_step) 
            then show ?thesis           
              by (simp add: Some Cons Pair T1, metis)  
          next
            case False
            then obtain s where "subtrie_at_path (SymbolNode m) p2 (Leaf (insert t s))" using path_func path_of_subterm insert_aux_subset
              by (metis "4.prems"(1-3) Pair as0 as3 complete_storage_from_position_def fst_conv insert_iff list.sel(1) local.Cons subsetD)
            then have   "subtrie_at_path (insert_aux (SymbolNode m) (Fun f (a # largs)) t0) p2 (Leaf (insert t s))"
              using 4 False Some Cons Pair
              by (clarsimp, simp add: subtrie_at_path_step_simp) 
            then show ?thesis
              by meson  
          qed
        qed
      qed
      show " \<exists>s. subtrie_at_path (insert_aux (SymbolNode m) (Fun f (a # largs)) t0) p2 (Leaf (insert t s))"
        using r1 by blast
    qed
  qed
qed

section \<open>Term removal\<close>

fun update_or_remove_entry :: "('a, 'b) fmap \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b option) \<Rightarrow> ('a, 'b) fmap" where
  "update_or_remove_entry m k f = (case m $$ k of
                                    None \<Rightarrow> m
                                  | Some v \<Rightarrow> (case f v of
                                                None \<Rightarrow> fmdrop k m
                                              | Some v0 \<Rightarrow> fmupd k v0 m))"

fun update_or_remove_entries :: "('a, 'b) fmap \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow> ('a, 'b) fmap" where
  "update_or_remove_entries m [] f = m"
| "update_or_remove_entries m (k # ks) f = update_or_remove_entries (update_or_remove_entry m k (f k)) ks f"

lemma update_or_remove_entries_dom : "fmdom' (update_or_remove_entries m ks f) \<subseteq> fmdom' m"
proof (induction ks arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  then show ?case
  proof (cases "m $$ k")
    case None
    then show ?thesis using Cons 
      by simp
  next
    case (Some v)
    then show ?thesis using Cons 
      by (smt (verit, del_insts) fmdom'_drop fmdom'_notD fmdom'_notI fmupd_lookup insert_Diff insert_iff option.case_eq_if subset_iff update_or_remove_entries.simps(2) update_or_remove_entry.simps)
  qed
qed 

lemma update_or_remove_entries_hd:
  assumes "k \<notin> set ks"
      and "m $$ k = Some v"
    shows "update_or_remove_entries m (k # ks) f $$ k = f k v"
  using assms proof (induction ks arbitrary: m)
  case Nil
  then show ?case 
    by (simp add: option.case_eq_if) 
next
  case (Cons a ks)
  then show ?case
  proof (cases "f k v")
    case None
    then show ?thesis using Cons 
      by (metis (mono_tags, lifting) fmdom'_drop fmdom'_notD option.case_eq_if option.distinct(1) option.sel subset_Diff_insert update_or_remove_entries.simps(2) update_or_remove_entries_dom update_or_remove_entry.simps)  
  next
    case (Some v)
    then show ?thesis
    proof (cases "m $$ a")
      case None
      then show ?thesis 
        using Cons.IH Cons.prems(1) Cons.prems(2) Some by force
    next
      case s1:(Some u)
      then show ?thesis
      proof (cases "f a u")
        case None
        then show ?thesis using s1 Some Cons  by (clarsimp simp add: fmdrop_fmupd)
      next
        case s2: (Some x)
        then show ?thesis using s1 Some Cons
          by (simp, metis fmupd_lookup fmupd_reorder_neq)
      qed
    qed
  qed
qed

lemma update_or_remove_entries_some: 
  assumes "distinct ks"
      and "k \<in> set ks"
      and "m $$ k = Some v"
    shows "update_or_remove_entries m ks f $$ k = f k v"
  using assms
proof (induction ks arbitrary: m)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a ks)
  then show ?case
  proof (cases "m $$ a")
    case None
    then show ?thesis using Cons
      by auto
  next
    case (Some a)
    then show ?thesis using Cons  
      by (smt (verit, del_insts) distinct.simps(2) fmlookup_drop fmupd_lookup option.case_eq_if set_ConsD update_or_remove_entries.simps(2) update_or_remove_entry.simps update_or_remove_entries_hd) 
  qed
qed

lemma update_or_remove_entries_none:
  assumes "distinct ks"
    and "k \<in> set ks"
    and "m $$ k = None"
  shows "update_or_remove_entries m ks f $$ k =  None"
  using assms  proof(induction ks arbitrary: m)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a ks)
  then show ?case 
    by (meson fmdom'_notD fmdom'_notI subsetD update_or_remove_entries_dom)
qed 

fun remove_leaf :: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) trie option" where
  "remove_leaf (Leaf s) t = (if s = {t} then None else Some (Leaf (Set.remove t s)))"
| "remove_leaf (SymbolNode m) t = undefined"

function remove_aux :: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) trie option" where
  "remove_aux (Leaf s) t t0 = undefined"
| "remove_aux (SymbolNode m) (Var x) t0 = (let nm = update_or_remove_entry m symbol.Star
               (\<lambda>m2. let nm2 = update_or_remove_entry m2 0 (\<lambda>tr. remove_leaf tr t0)
                      in if nm2 = {$$} then None else Some nm2)
     in if nm = {$$} then None else Some (SymbolNode nm))"

| "remove_aux (SymbolNode m) (Fun f []) t0 =  (let nm = update_or_remove_entry m (F f 0)
               (\<lambda>m2. let nm2 = update_or_remove_entry m2 0 (\<lambda>tr. remove_leaf tr t0)
                      in if nm2 = {$$} then None else Some nm2)
     in if nm = {$$} then None else Some (SymbolNode nm))"

| "remove_aux (SymbolNode m) (Fun f (a # largs)) t0 =  (let nm = update_or_remove_entry m (F f (length (a # largs)))
               (\<lambda>m2. let nm2 =
                           update_or_remove_entries m2 [0..<(length (a # largs))]
                            (\<lambda>i tr. if i < Suc (length largs) then remove_aux tr ((a # largs) ! i) t0 else undefined)
                     in if nm2 = {$$} then None else Some nm2)
     in if nm = {$$} then None else Some (SymbolNode nm))"
  by pat_completeness auto termination
  apply (relation "measure (\<lambda>(p, q, r). depth q)")
  apply blast
  apply clarsimp
  by (metis List.finite_set Max_ge finite_imageI image_eqI image_insert le_imp_less_Suc length_Cons list.simps(15) nth_mem)

fun remove_term :: "('f, 'v) trie \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) trie" where
  "remove_term tr t t0 = (case remove_aux tr t t0 of Some x \<Rightarrow> x | None \<Rightarrow> empty_trie)"

lemma updrem_image:
  assumes "fmdom' aa = {0..<Suc (length largs)}"
      and "k < Suc (length largs)"
    shows "update_or_remove_entries aa [0..<Suc (length largs)] (\<lambda>i tr. if i < Suc (length largs) then remove_aux tr ((a # largs) ! i) t0 else undefined) $$ k = remove_aux (aa $$! k) ((a # largs) ! k) t0" 
  using assms
proof -
  have "distinct [0..<Suc (length largs)]" and "k \<in> set [0..<Suc (length largs)]" and "aa $$ k = Some (aa $$! k)"
     apply force
     apply (simp add: assms(2))
    by (metis assms(1) assms(2) atLeast0LessThan fmdom'_notI lessThan_iff option.exhaust_sel)
  then have "update_or_remove_entries aa [0..<Suc (length largs)] (\<lambda>i tr. if i < Suc (length largs) then remove_aux tr ((a # largs) ! i) t0 else undefined) $$ k= ( if k < Suc (length largs) then remove_aux (aa $$! k) ((a # largs) ! k) t0 else undefined) "
    using update_or_remove_entries_some [of "[0..<Suc ((length largs))]" k aa "(aa $$! k)" ]
    by blast 
  then show ?thesis
    using assms(2) 
    by simp
qed

lemma exists_in_non_fmempty:
  assumes "m \<noteq> {$$}"
  shows"\<exists>x\<in>fmdom' m. \<exists>z. m $$ x = Some z"
  using assms by (metis fmap_ext fmdom'I fmempty.rep_eq not_Some_eq)

lemma remove_keeps_elements:
  assumes ws: "well_structured tr"
      and in_rem: "u \<in> Set.remove t0 (to_set tr)"
    shows "u \<in> to_set (remove_term tr t t0)"
  using assms
proof (induction  tr t t0 arbitrary: u rule: remove_aux.induct)
  case (1 s t t0)
  then show ?case
    using not_well_structured_leaf by blast
next
  case (2 m x t0)
  then show ?case
  proof (cases "m $$ Star")
    case None
    then show ?thesis using 2 by auto 
  next
    case (Some m2)
    then obtain ts where s1: "m2 $$ 0 = Some (Leaf ts)"
      using "2.prems"(1) ws_dom_var by blast
    then show ?thesis
    proof (cases "ts = {t0}")
      case t1: True
      then have "fmdrop 0 m2 = {$$}"
        by (metis "2.prems"(1) Some fmdrop_set_fmdom fmdrop_set_single ws_dom_var)
      then show ?thesis
        using t1 s1 Some 2
        by (simp, smt (verit) fmdom'I fmdom'_notI fmlookup_drop fmlookup_ran'_iff option.case_eq_if option.sel singletonD to_set.simps(1) to_set_entry ws_dom_var)
    next
      case False
      then show ?thesis using 2
        by (simp add: Some s1 False, metis Some fmlookup_ran'_iff fmupd_lookup member_remove option.sel s1 to_set.simps(1))
    qed
  qed
next
  case (3 m f t0)
  then show ?case
  proof (cases "m $$ F f 0")
    case None
    then show ?thesis using 3 by auto
  next
    case (Some m2)
    then obtain ts where s1: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "3.prems"(1) ws_dom_const)
    then show ?thesis
    proof (cases "ts = {t0}")
      case T1: True
      then have T2: "fmdrop 0 m2 = {$$}"
        by (metis "3.prems"(1) Some fmdrop_set_fmdom fmdrop_set_single ws_dom_const)
      then show ?thesis using T2 T1 s1 Some 3 to_set.simps
        by (simp, smt (verit, del_insts) fmdom'I fmdom'_notI fmlookup_drop fmlookup_ran'_iff option.case_eq_if option.sel singletonD to_set.simps(1) to_set_entry ws_dom_const)
    next
      case False
      then show ?thesis using  3 Some s1 False
        by (simp, metis Some fmlookup_ran'_iff fmupd_lookup member_remove option.sel s1 to_set.simps(1))
    qed
  qed 
next
  case (4 m f a f_args t0)
  then show ?case 
  proof (cases "m $$ F f (Suc (length f_args))")
    case None
    then show ?thesis using "4.prems"(2)  by force 
  next
    case (Some m2)
    let ?m'= "update_or_remove_entries m2 [0..<Suc (length f_args)]
      (\<lambda>i tr. if i < Suc (length f_args) then remove_aux tr ((a # f_args) ! i) t0 else undefined)"
    have dom_m2: "fmdom' m2 = {0..<Suc (length f_args)}"
      by (metis "4"(2) Some atLeastLessThan_upt atLeast_upt length_suffixes list.size(3) nat.distinct(1) ws_fmdom') 
    then have eq_domain: "\<And>i .i < Suc (length f_args) \<longleftrightarrow> i \<in> fmdom' m2"
          and dist: "distinct[0..<Suc (length f_args)]"
      by simp+
    then have ws_image: "\<And>i. i < Suc (length f_args) \<Longrightarrow> well_structured (m2$$!i)"
      by (metis "4"(2) Some fmdom'I fmdom'_notI fmran'I nat.distinct(1) option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases)
    then have h: "\<And>i. i < Suc (length f_args) \<Longrightarrow> ?m' $$ i = remove_aux (m2 $$! i) ((a # f_args) ! i) t0"
      by (simp add: dom_m2 updrem_image)
    show ?thesis
    proof (cases "?m'= {$$}")
      case True
      have h_rem_image: "\<And>i .i < Suc (length f_args) \<Longrightarrow> (remove_aux (m2$$! i) ((a # f_args) ! i) t0) = None"
        using True h by force 
      then show ?thesis 
      proof (cases "fmdrop (F f (Suc (length f_args))) m = {$$}")
        case T1: True
        have dom_m:"fmdom' m = {(F f (Suc (length f_args)))}"
          by (metis Some T1 fmdom'I fmdom'_drop fmdom'_empty insert_Diff)
        then obtain i where "i\<in> fmdom' m2" and in_ts_im:" u\<in> to_set (m2 $$! i)" 
          using "4.prems"(2) Some
          by (simp, metis fmdom'I fmran'E option.sel singleton_iff)
        then have i: "i < Suc (length f_args)"
          using eq_domain by force
        then have " u \<in> to_set (remove_term ((m2$$! i)) ((a # f_args) ! i) t0)" 
          by (metis "4.IH" "4.prems"(2) in_ts_im member_remove ws_image)  
        then show ?thesis  
          by (simp add: T1 True Some Let_def, metis exists_leaf h_rem_image i option.simps(4) no_subtrie_in_empty_trie)
      next
        case False
        then show ?thesis 
          using 4
          by (clarsimp simp add: True Some, smt (verit, best) Some eq_domain exists_leaf fmdom'_notD fmlookup_drop fmlookup_ran'_iff h_rem_image option.sel option.simps(3) option.simps(4) no_subtrie_in_empty_trie  ws_image)
      qed
    next
      case False
      from "4.prems"(2)  obtain  sym  m3 k  xa where  u1:"m $$ sym  = Some m3 " and u2 : " m3 $$ k = Some xa "  and u3: "u \<in> to_set xa " 
        by (fastforce ) 
      then  show ?thesis  proof(cases "sym = F f (Suc (length f_args))" )
        case True
        have t1:"?m' $$ k = remove_aux (m2 $$! k) ((a # f_args) ! k) t0 "
        proof -
          have "k < Suc (length f_args)"
            using Some True eq_domain u1 u2 by fastforce
          then show ?thesis
            by (simp add: dom_m2 updrem_image)
        qed
        have "m2 = m3"
          using Some True u1 by force
        have "k < Suc (length f_args)"
          by (simp add: \<open>m2 = m3\<close> eq_domain fmdom'I u2)
        have h1:  " u \<in> to_set (remove_term (m2 $$! k) ((a # f_args) ! k) t0)"
          by (metis "4.IH" "4.prems"(2) \<open>m2 = m3\<close> eq_domain fmdom'I member_remove option.sel u2 u3 ws_image)
        then show ?thesis 
        proof (cases "remove_aux (m2 $$! k) ((a # f_args) ! k) t0")
          case None
          then show ?thesis
            by (metis exists_leaf h1 option.simps(4) remove_term.simps no_subtrie_in_empty_trie) 
        next
          case y: (Some r)
          obtain m3 where  "m3 \<in> fmran' ?m' "and "u \<in> to_set m3"
            using fmran'I t1 y h1 by fastforce 
          then show ?thesis
            by (simp add: Some False, meson fmlookup_ran'_iff fmupd_lookup)
        qed
      next
        case F2:False
        then show ?thesis
          by (simp add: Some False, metis (no_types, lifting) u1 u2 u3 fmran'I fmupd_lookup)
      qed
    qed
  qed
qed

lemma remove_term_subset:
  assumes "well_structured tr"
      and "u \<in> to_set (remove_term tr t t0)"
    shows "u \<in> (to_set tr)   "
  using assms 
proof (induction tr t t0  rule: remove_aux.induct )
  case (1 s t t0)
  then show ?case
    by (simp add: not_well_structured_leaf) 
next
  case (2 m x t0)
  then show ?case 
  proof (cases "m $$ Star")
    case None
    then show ?thesis using 2 by (clarsimp simp add : split: if_splits)
  next
    case (Some m2)
    then obtain ts where s1: "m2 $$ 0 = Some (Leaf ts)"
      using "2.prems"(1) ws_dom_var by blast
    then show ?thesis
    proof (cases "ts = {t0}")
      case True
      then show ?thesis using 2
        apply (auto simp add: s1 Some Let_def split: if_splits)
        apply (metis fmlookup_drop fmlookup_ran'_iff option.discI)
        by (metis Some fmdrop_set_fmdom fmdrop_set_single ws_dom_var)
    next
      case False
      then show ?thesis
        using 2 s1 Some
        apply (auto  simp add: s1 Some Let_def split: if_splits)
        apply (metis s1 Some fmlookup_ran'_iff fmupd_lookup member_remove option.sel to_set.simps(1))
        by  (metis (no_types, lifting) s1 Some fmran'E fmran'I fmupd_lookup member_remove option.inject to_set.simps(1))
    qed
  qed
next
  case (3 m f t0)
  then show ?case 
  proof (cases "m $$ F f 0")
    case None
    then show ?thesis using 3 by (clarsimp simp add: split: if_splits)
  next
    case (Some m2)
    then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "3.prems"(1) ws_dom_const)
    then show ?thesis
    proof (cases "ts = {t0}")
      case T0: True
      then have h2: "fmdrop 0 m2 = {$$}"
        by (metis "3.prems"(1) Some fmdrop_set_fmdom fmdrop_set_single ws_dom_const)
      then show ?thesis
      proof (cases "fmdrop (F f 0) m = {$$}")
        case True
        then show ?thesis using h h2 Some T0 3 by auto
      next
        case False
        then show ?thesis using 3 h h2 Some T0 fmlookup_drop fmlookup_ran'_iff 
            by (clarsimp, metis (no_types, opaque_lifting) fmlookup_drop fmlookup_ran'_iff option.simps(3))
      qed
    next
      case False
      then show ?thesis using 3 h Some member_remove  
        by (clarsimp, smt (verit, ccfv_threshold) fmlookup_ran'_iff fmupd_lookup member_remove option.inject to_set.simps(1)) 
    qed
  qed
next
  case (4 m f a f_args t0)
  then show ?case
  proof (cases "m $$ F f (Suc (length f_args))")
    case None
    then show ?thesis using "4.prems"(2) by (auto simp add: split: if_splits) 
  next
    case (Some m2)
    let ?m' = " update_or_remove_entries m2 [0..<Suc (length f_args)] (\<lambda>i tr. if i < Suc (length f_args) then remove_aux tr ((a # f_args) ! i) t0 else undefined)"
    have domm2: "fmdom' m2 = {0..<Suc (length f_args)}"
      by (metis "4"(2) Some atLeastLessThan_upt atLeast_upt length_suffixes list.size(3) nat.distinct(1) ws_fmdom')
    then  have in_domm: "\<And>i. i\<in> fmdom' ?m' \<Longrightarrow> i < Suc (length f_args)"
      by (meson "4.prems"(1) Some subsetD update_or_remove_entries_dom ws_dom_fun2)
    then  have in_d: "\<And>i. i\<in> fmdom' ?m' \<Longrightarrow> ?m' $$ i = remove_aux  (m2 $$! i)  ((a # f_args) ! i) t0"
      using domm2 updrem_image by blast
    show ?thesis
    proof (cases "?m' = {$$}")
      case True
      then show ?thesis 
        using "4.prems"(2) True Some Let_def
        apply (auto simp add: True Some Let_def split: if_splits )
        by (metis (no_types, lifting) fmlookup_drop fmlookup_ran'_iff option.discI)
    next
      case False
      then have h1: "\<And>m2 i symb m3.  m2 $$ i = Some m3 \<Longrightarrow> u \<in> to_set m3 \<Longrightarrow> F f (Suc (length f_args)) \<noteq> symb \<Longrightarrow> m $$ symb = Some m2 \<Longrightarrow>  u \<in> to_set (SymbolNode m)"
        using to_set_entry by blast
      obtain s  m1  where r: " (m(F f (Suc (length f_args)) $$:=?m')) $$ s = Some m1" and  j: "\<exists> m2 \<in> fmran' m1. u \<in> to_set m2" 
        using "4.prems"(2)
        by (fastforce simp add: Let_def Some False )
      then show ?thesis 
      proof (cases "s = F f (Suc (length f_args))")
        case True
        then have g: "m1  = ?m'"
          using r by auto
        then obtain m3 i where t0: "m1 $$ i = Some m3" and t2: " u \<in> to_set m3"
          using j by blast
        have hj: "i < Suc (length f_args)"
          by (metis fmdom'I g in_domm t0)
        then have th0: "m3 = (remove_term  (m2 $$! i)  ((a # f_args) ! i) t0)"
          using t0 fmdom'I in_d   by ( auto simp add: fmlookup_dom'_iff g)
        then have " u \<in> to_set m3"
          using t2 by blast
        then show ?thesis 
          using "4.prems"(2) True r t0 
          by (metis (no_types, lifting) "4.IH" "4.prems"(1) Some Zero_not_Suc fmdom'I fmdom'_notI fmran'I hj length_Cons option.collapse option.sel symbol.distinct(1) symbol.inject th0 to_set_entry trie.sel(3) well_structured_cases well_structured_map_entry.cases ws_dom_fun)
      next
        case F0: False
        then show ?thesis
          using j r to_set_entry by fastforce
      qed
    qed
  qed
qed

lemma remove_deletes_element:
  assumes "well_structured tr"
      and so: "sound_storage_from_position tr p"
      and sub: "subterm_at_path t0 p t" 
      and rem: "remove_aux tr t t0 = Some n "
    shows "t0 \<notin> to_set n  "
  using assms
proof (induct  tr t t0 arbitrary: p n rule:remove_aux.induct )
  case (1 s t t0)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x t0)
  have pat_term: "path_of_term t0 (p @ [(Star,0)] )"
    by (meson "2.prems"(3) path_var subterm_at_path_path_of_term)
  then show ?case 
  proof (cases "m $$ Star")
    case None
    then show ?thesis
      using 2
      by (clarsimp, metis exists_leaf option.distinct(1) option.inject path_var sound_storage_from_position_def path_of_subterm subtrie_cons)
  next
    case (Some m2)
    then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
      using "2.prems"(1) ws_dom_var by blast
    have tr: "\<And>m3 tr2.  m3 \<in> fmran' (fmdrop Star m) \<Longrightarrow> tr2 \<in> fmran' m3 \<Longrightarrow> t0 \<notin> to_set tr2"
      using "2.prems"(2,3) 
      apply (elim fmran'E)
      apply (auto  simp add: sound_storage_from_position_def split:if_splits)
      using pat_term  
      by (smt (verit) exists_leaf list.inject path_var prod.sel(1) path_of_subterm subtrie_at_path_step_simp)
    then show ?thesis     
    proof (cases "ts = {t0}")
      case True
      then have "fmdrop 0 m2 = {$$}"
        by (metis "2.prems"(1) Some fmdrop_set_fmdom fmdrop_set_single ws_dom_var)
      then show ?thesis using 2 tr by ( clarsimp simp add: Let_def Some h True split:if_splits)
    next
      case False
      then show ?thesis 
        using 2 
        apply (auto simp add:Let_def Some h False fmran'E )
        apply (elim fmran'E) 
        apply (clarsimp simp add: split:if_splits)
        apply (metis Some bot_nat_0.not_eq_extremum fmdom'I singletonD ws_dom_var) using tr
        by (metis fmlookup_drop fmran'I)
    qed 
  qed
next
  case (3 m f t0)
  have pat_term:  "path_of_term t0 (p @ [(F f 0, 0)])"
    by (meson "3.prems"(3) path_const subterm_at_path_path_of_term)
  then show ?case 
  proof(cases "m $$ F f 0")
    case None
    then show ?thesis using 3 
      by (clarsimp, metis exists_leaf option.distinct(1) option.inject path_const sound_storage_from_position_def path_of_subterm subtrie_cons)
  next
    case (Some m2)
    then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "3.prems"(1) ws_dom_const)
    have tr: "\<And> m3 tr2. m3 \<in> fmran' (fmdrop (F f 0) m) \<Longrightarrow> tr2 \<in> fmran' m3 \<Longrightarrow> t0 \<notin> to_set tr2"
      using "3.prems"(2)  "3.prems"(3) 
      apply (elim fmran'E)
      apply (auto  simp add: sound_storage_from_position_def split:if_splits)
      using pat_term 
      by (smt (verit) exists_leaf list.inject path_const prod.sel(1) path_of_subterm subtrie_at_path_step_simp)
    then show ?thesis     
    proof (cases "ts = {t0}")
      case True
      then have "fmdrop 0 m2 = {$$}"
        by (metis "3.prems"(1) Some fmdrop_set_fmdom fmdrop_set_single ws_dom_const)
      then show ?thesis using 3 tr by (clarsimp simp add:Let_def Some h True split:if_splits )
    next
      case False
      then show ?thesis 
        using 3
        apply (  auto simp add:Let_def Some h False fmran'E)
        apply (elim fmran'E) 
        apply ( clarsimp simp add: split:if_splits)
        apply (metis Some bot_nat_0.not_eq_extremum fmdom'I singletonD ws_dom_const) using tr
        by (metis fmlookup_drop fmran'I)
    qed
  qed
next
  case (4 m f a f_args t0)
  then show ?case
  proof (cases "m $$ F f (Suc (length f_args))")
    case None
    then show ?thesis using 4 apply (clarsimp simp add: None sound_storage_from_position_def split: if_splits)
      using path_func path_of_subterm subtrie_at_path_step None exists_leaf 
      by (smt (verit, ccfv_SIG) fmdom'_notI fmlookup_dom'_iff fmran'E fst_conv list.sel(1))  
  next
    case (Some m2)
    let ?m' = "update_or_remove_entries m2 [0..<Suc (length f_args)] (\<lambda>i tr. if i < Suc (length f_args) then remove_aux tr ((a # f_args) ! i) t0 else undefined)"
    have domm2: "fmdom' m2 = {0..<Suc (length f_args)}"
      by (metis "4"(2) Some atLeastLessThan_upt atLeast_upt length_suffixes list.size(3) nat.distinct(1) ws_fmdom')
    then  have in_domm: "\<And>i. i\<in> fmdom' ?m' \<Longrightarrow> i < Suc (length f_args)"
      by (meson "4.prems"(1) Some subsetD update_or_remove_entries_dom ws_dom_fun2)
    then  have in_d: "\<And>i. i\<in> fmdom' ?m' \<Longrightarrow> ?m' $$ i =   (remove_aux  (m2 $$! i)  ((a # f_args) ! i) t0) "
      using domm2 updrem_image by blast
    have tr: "\<And> xa xm2.  xa \<in> fmran' (fmdrop (F f (Suc (length f_args))) m) \<Longrightarrow> xm2 \<in> fmran' xa \<Longrightarrow> t0 \<notin> to_set xm2 "
      using "4.prems"(2)  "4.prems"(3) 
      apply (elim fmran'E)
      apply (auto  simp add: sound_storage_from_position_def split:if_splits) 
      using  path_func path_of_subterm   
      by (metis (mono_tags, lifting) exists_leaf fst_conv list.sel(1) subtrie_at_path_step) 
    show ?thesis
    proof (cases "?m' = {$$}")
      case True
      then show ?thesis 
        using 4 True Some Let_def
        apply (auto simp add: True Some Let_def split: if_splits)
        using tr by auto 
    next
      case False
      then have "\<And>tr2 i. ?m' $$ i = Some tr2 \<Longrightarrow> t0 \<notin> to_set tr2" 
      proof -
        fix tr2 i
        assume y: "?m' $$ i = Some tr2"
        then have vi: "i < Suc (length f_args)"
          using in_domm by force
        then have t0: "well_structured (m2 $$! i)"
          by (metis "4.prems"(1) Some bot_nat_0.not_eq_extremum fmdom'I fmdom'_notI fmran'I key_map_entry_simp length_Cons list.distinct(1) option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases zero_less_Suc)
        have t2: "sound_storage_from_position (m2 $$! i) (p @ [(F f (Suc (length f_args)), i)])"
          by (metis "4.prems"(1) "4.prems"(2) Some fmdom'_notI key_map_entry_simp length_Cons list.distinct(1) option.collapse sound_storage_from_position_subtrie vi)
        have t3: "subterm_at_path t0 (p@[(F f (Suc (length f_args)), i)]) ((a # f_args) ! i)  "
          using "4.prems"(3) subsubterm_at_path vi by fastforce 
        have "remove_aux (m2$$!i) ((a # f_args) ! i) t0 = Some tr2"
          using fmdom'I in_d y by fastforce
        then show "t0 \<notin> to_set tr2"
          using "4.hyps" t0 t2 t3 vi by blast 
      qed
      then show ?thesis using 4 tr
        apply (auto simp add: Let_def Some False)
        apply (elim fmran'E)
        apply (clarsimp simp add: split:if_splits)
        by(metis (no_types, lifting) fmlookup_drop fmlookup_ran'_iff tr)
    qed
  qed
qed

lemma term_removed_from_trie_set: 
  assumes "well_structured tr"
      and "sound_storage_from_position tr p"
      and "subterm_at_path t0 p t"
    shows "t0 \<notin> to_set (remove_term tr t t0)"
  using assms
  by (metis exists_leaf option.case_eq_if option.collapse remove_deletes_element remove_term.simps no_subtrie_in_empty_trie)

lemma to_set_remove: 
  assumes "well_structured tr"
      and "sound_storage tr"
    shows "Set.remove t (to_set tr) = to_set (remove_term tr t t)"
proof
  show "Set.remove t (to_set tr) \<subseteq> to_set (remove_term tr t t)"
    using assms(1) remove_keeps_elements by blast
  show "to_set (remove_term tr t t) \<subseteq> Set.remove t (to_set tr)"
    by (metis assms member_remove remove_term_subset sound_storage_alt_def subsetI subterm_at_path_empty term_removed_from_trie_set)
qed

lemma remove_preserves_sound:
  assumes "well_structured tr"
      and "sound_storage_from_position tr p"
      and "subterm_at_path t0 p t"
    shows "sound_storage_from_position (remove_term tr t t0) p"
  using assms
proof (induct tr t t0 arbitrary: p rule: remove_aux.induct)
  case (1 s t t0)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x t0)
  then show ?case
  proof (cases "m $$ Star")
    case None
    then show ?thesis using 2 
      by force 
  next
    case (Some m2)
    then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
      using "2.prems"(1) ws_dom_var by blast
    then show ?thesis
    proof (cases "ts = {t0}")
      case True
      then have "fmdrop 0 m2 = {$$}"
        by (metis "2.prems"(1) Some fmdrop_set_fmdom fmdrop_set_single ws_dom_var)
      then show ?thesis using 2
        apply (clarsimp simp add: Let_def h Some True split: if_splits)
        by (smt (verit, ccfv_threshold) fmlookup_drop option.discI sound_storage_from_position_def subtrie_at_path.simps subtrie_at_path_step trie.distinct(1) trie.sel(3)) 
    next
      case False
      have "sound_storage_from_position (SymbolNode ({Star $$:= m2(0 $$:= Leaf (Set.remove t0 ts))})) p"
        using 2
        apply (clarsimp simp add: sound_storage_from_position_def) 
        by (smt (verit, ccfv_threshold) h Set.set_insert Some fmupd_lookup insertI1 member_remove option.inject subtrie_at_nil_iff_eq subtrie_at_path_cases subtrie_at_path_step_simp subtrie_string_2 to_set.simps(1) trie.simps(4))
      then show ?thesis 
        using 2
        by (auto simp add:Let_def Some h False intro: elim_sound_fp) 
    qed
  qed
next
  case (3 m f t0)
  then show ?case
  proof (cases "m $$ F f 0")
    case None
    then show ?thesis using 3 
      by force 
  next
    case (Some m2)
    then obtain ts where h: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "3.prems"(1) ws_dom_const)
    show ?thesis
    proof (cases "ts = {t0}")
      case True
      then have "fmdrop 0 m2 = {$$}"
        by (metis "3.prems"(1) Some fmdrop_set_fmdom fmdrop_set_single ws_dom_const)
      then show ?thesis using 3
        apply (clarsimp simp add:Let_def Some h True split:if_splits)
        by (smt (verit, ccfv_threshold) fmlookup_drop option.discI sound_storage_from_position_def subtrie_at_path.simps subtrie_at_path_step trie.distinct(1) trie.sel(3)) 
    next
      case False
      have "sound_storage_from_position (SymbolNode ({F f 0 $$:= m2(0 $$:= Leaf (Set.remove t0 ts))})) p"
        unfolding sound_storage_from_position_def
      proof (intro allI impI) 
        fix t p2 s 
        assume h1: "subtrie_at_path (SymbolNode {F f 0 $$:= m2(0 $$:= Leaf (Set.remove t0 ts))}) p2 (Leaf (insert t s))"
        then have "p2 = [(F f 0, 0)]" 
          by (smt (verit, del_insts) "3.prems"(1) Some fmdom'I fmupd_lookup option.sel singletonD subtrie_at_path.simps subtrie_string_2 trie.distinct(1) trie.sel(3) ws_dom_const) 
        then show "path_of_term t (p @ p2)"
          by (smt (verit, ccfv_threshold) "3.prems"(2) h Some append_Nil2 exists_leaf fmupd_lookup h1 member_remove nth_Cons_0 option.inject snd_conv sound_storage_from_position_def sound_storage_from_position_subtrie subtrie_at_path.simps subtrie_string_2 subtrie_to_set to_set.simps(1) trie.distinct(1) trie.sel(3))
      qed
      then show ?thesis 
        using 3
        by (auto simp add: Let_def Some h False intro: elim_sound_fp) 
    qed 
  qed
next
  case (4 m f a largs t0)
  then show ?case
  proof (cases "m $$ F f (Suc (length largs))")
    case None
    then show ?thesis using 4 by force 
  next
    case (Some aa)
    then have domaa: "fmdom' aa = {0..<Suc (length largs)}"
      by (metis "4"(2) atLeastLessThan_upt atLeast_upt length_suffixes less_Suc_eq_0_disj less_numeral_extra(3) list.size(3) ws_fmdom')
    let ?m' = "update_or_remove_entries aa [0..<Suc (length largs)] (\<lambda>i tr. if i < Suc (length largs) then remove_aux tr ((a # largs) ! i) t0 else undefined)"
    show ?thesis proof (cases "?m'= {$$}")
      case True
      then show ?thesis proof(cases "fmdrop (F f (Suc (length largs))) m = {$$} ")
        case T1:True
        then show ?thesis using 4 Some True  by(clarsimp simp add: sound_storage_from_position_def no_subtrie_in_empty_trie  Let_def)
      next
        case False
        then show ?thesis  using "4.prems"(2) Some True  False apply (clarsimp simp add: Some True  False sound_storage_from_position_def Let_def)
          by (smt (verit, ccfv_SIG) fmlookup_drop option.discI subtrie_at_path.simps trie.distinct(1) trie.sel(3)) 
      qed    
    next
      case False
      have hi: "\<And>i. i < Suc (length largs) \<Longrightarrow>
         sound_storage_from_position (remove_term (aa $$! i) ((a # largs) ! i) t0) (p @ [(F f (Suc (length largs)), i)])"
      proof-
        fix i 
        assume vi: "i < Suc (length largs)"
        then have indom: "i\<in> fmdom' aa"
          by (metis "4.prems"(1) Some length_suffixes ws_dom_fun)
        then  have wel: "well_structured (aa $$! i)"
          by (metis "4.prems"(1) Some fmdom'I fmdom'_notI fmran'I nat.distinct(1) option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases) 
        then have so: "sound_storage_from_position (aa $$! i)  (p @ [(F f (Suc (length largs)), i)])"
          by (metis "4.prems"(2) Some fmdom'_notI indom option.collapse sound_storage_from_position_subtrie)
        then have "subterm_at_path t0 (p @ [(F f (Suc (length largs)), i)]) ((a # largs) ! i)"
          using "4.prems"(3) subsubterm_at_path vi by fastforce 
        then show "sound_storage_from_position (remove_term (aa $$! i) ((a # largs) ! i) t0) (p @ [(F f (Suc (length largs)), i)])"
          using "4.hyps" so vi wel by blast
      qed
      have " sound_storage_from_position  (SymbolNode {F f (Suc (length largs)) $$:= ?m'})  p" 
        unfolding sound_storage_from_position_def proof(intro allI impI)
        fix t p2 s
        assume h1: "subtrie_at_path (SymbolNode {F f (Suc (length largs)) $$:= ?m'})  p2 (Leaf (insert t s)) "
        have h0: "?m' \<noteq> {$$}"
          by (simp add: False)
        show " path_of_term t (p @ p2) "
        proof (cases p2)
          case Nil
          then show ?thesis 
            using h1 subtrie_at_nil by blast
        next
          case (Cons hp list)
          then show ?thesis
          proof (cases hp)
            case (Pair symb b)
            then have sy: "symb = F f (Suc (length largs))"
              using h1 local.Cons subtrie_string_2 by blast
            then have vi: "b < Suc (length largs)"
              by (metis (no_types, lifting) Pair domaa ex_nat_less_eq h1 local.Cons not_less_eq subsetD subtrie_string_3 update_or_remove_entries_dom)
            then obtain  val where h0: "?m' $$ b = Some val"
              using h0
              by (metis (no_types, lifting) Pair fmlookup_dom'_iff h1 local.Cons subtrie_string_3)
            then have "Some val= remove_aux (aa $$! b) ((a # largs) ! b) t0"
              using updrem_image domaa  vi h0      by fastforce
            then have "val= remove_term (aa $$! b) ((a # largs) ! b) t0"
              by (metis option.simps(5) remove_term.simps) 
            then show ?thesis using hi vi h1 Cons Pair sy  h0 subtrie_cons by (fastforce simp add: sound_storage_from_position_def)
          qed
        qed
      qed
      then show ?thesis using 4 Some False apply (clarsimp simp add: Let_def)
        using elim_sound_fp by blast
    qed 
  qed 
qed

lemma to_set_remove_none: 
  assumes "well_structured tr"
      and "subterm_at_path t0 p t"
      and "sound_storage_from_position tr p"
      and "remove_aux tr t t0 = None" 
    shows "to_set tr \<subseteq> {t0}"
  using assms by (metis all_not_in_conv empty_subsetI exists_leaf remove_keeps_elements insert_Diff member_remove option.case_eq_if remove_def remove_term.simps subset_refl no_subtrie_in_empty_trie )

lemma remove_preserves_complete:
  assumes "well_structured tr"
      and "complete_storage_from_position tr p"
      and "sound_storage_from_position tr p"
      and "subterm_at_path t0 p t"
    shows "complete_storage_from_position (remove_term tr t t0) p"
  using assms 
proof (induct  tr t t0  arbitrary: p rule:remove_aux.induct)
  case (1 s t t0)
  then show ?case 
    using not_well_structured_leaf by blast
next
  case (2 m x t0)
  then show ?case
  proof (cases "m $$ Star")
    case None
    then show ?thesis using "2.prems"(2) by force
  next case (Some m2)
    then obtain ts where Leaf: "m2 $$ 0 = Some (Leaf ts)"
      using "2.prems"(1) ws_dom_var by blast
    then show ?thesis
      unfolding complete_storage_from_position_def
    proof (intro allI impI)
      fix t p2
      assume hy1: "t \<in> to_set (remove_term (SymbolNode m) (Var x) t0)"
      assume hy2: "path_of_term t (p @ p2)"
      have inset: "t \<in> to_set (SymbolNode m) " using "2.prems"(1) hy1 remove_term_subset by  blast
      then have t0: "t\<noteq> t0" using "2.prems"(1) "2.prems"(3) "2.prems"(4) hy1  term_removed_from_trie_set by blast
      obtain ts2 where str:" subtrie_at_path (SymbolNode m) p2 (Leaf (insert t ts2))" 
        using "2.prems"(2) complete_storage_from_position_def hy2 inset by blast
      then show "\<exists>ts3. subtrie_at_path (remove_term (SymbolNode m) (Var x) t0) p2 (Leaf (insert t ts3))"
      proof (cases p2) 
        case Nil
        then show ?thesis
          using str subtrie_at_nil by blast
      next case (Cons hp list) 
        then show ?thesis
        proof (cases hp)
          case (Pair s b) 
          have th: "s \<in> fmdom' m " by (metis Pair fmdom'I local.Cons str subtrie_cons) 
          then show ?thesis
          proof (cases "s = Star" ) 
            case T1: True 
            then have b0: "b=0"  by (metis "2.prems"(1) Pair fmdom'_notD local.Cons option.distinct(1) singletonD str subtrie_cons ws_dom_var) 
            then have nil: "list= []" using Leaf Pair Some T1 elim_sub local.Cons str subtrie_at_path_cases by blast
            then have hn: "ts = (insert t ts2)" by (metis Leaf Pair Some T1 b0  elim_sub local.Cons str subtrie_at_nil_iff_eq trie.inject(1)) 
            then show ?thesis 
              using Pair Cons b0 Leaf Some T1 nil t0 by (simp add: subtrie_at_path_step_simp , metis insertI1 insert_absorb member_remove subtrie_at_path_empty) 
          next 
            case False 
            then have "subtrie_at_path (remove_term (SymbolNode m) (Var x) t0) p2 (Leaf (insert t ts2))" 
              using str Pair Cons hy1 by (fastforce simp add: Some Let_def subtrie_at_path_step_simp ) 
            then show ?thesis by blast
          qed 
        qed
      qed
    qed
  qed
next
  case (3 m f t0)
  then show ?case
  proof (cases" m $$ F f 0")
    case None
    then show ?thesis using "3.prems"(2) by force
  next case (Some a) 
    then show ?thesis
    proof (cases "a $$ 0")
      case None
      then show ?thesis by (metis "3.prems"(1) Some option.discI ws_dom_const)
    next case s1: (Some aa) 
      then show ?thesis
      proof(cases  aa) 
        case (Leaf x1) 
        then show ?thesis 
          unfolding complete_storage_from_position_def
        proof (intro allI impI) 
          fix t p2 
          assume hy1:"t \<in> to_set (remove_term (SymbolNode m) (Fun f []) t0)"
          assume hy2: "path_of_term t (p @ p2)"
          have inset: "t \<in> to_set (SymbolNode m) " using "3.prems"(1) hy1 remove_term_subset by  blast
          then have t0: "t\<noteq> t0" using "3.prems"(1) "3.prems"(3) "3.prems"(4) hy1  
            using term_removed_from_trie_set by blast  
          obtain s where str:" subtrie_at_path (SymbolNode m) p2 (Leaf (insert t s))" using "3.prems"(2) complete_storage_from_position_def hy2 inset by blast 
          then show "\<exists>s. subtrie_at_path (remove_term (SymbolNode m) (Fun f []) t0) p2 (Leaf (insert t s))"
          proof (cases "p2") 
            case Nil
            then show ?thesis
              using str subtrie_at_nil by blast
          next case (Cons hp list) 
            then show ?thesis  proof(cases hp) 
              case (Pair symb b) 
              have th: "symb \<in> fmdom' m " by (metis Pair fmdom'I local.Cons str subtrie_cons) 
              then show ?thesis
              proof(cases "symb = F f 0" ) 
                case T1:True 
                then have b0: "b=0" by (metis "3.prems"(1) Pair fmdom'_notD local.Cons option.distinct(1) singletonD str subtrie_cons ws_dom_const) 
                then have nil:"list= []" using Leaf Pair Some T1 elim_sub local.Cons s1 str subtrie_at_path_cases by blast
                then have hn: "x1 = (insert t s)" by (metis Leaf Pair Some T1 b0  elim_sub local.Cons s1 str subtrie_at_nil_iff_eq trie.inject(1)) 
                then show ?thesis 
                  using Pair Cons b0 Leaf Some s1 T1 nil t0 by ( simp add: subtrie_at_path_step_simp , metis insertI1 insert_absorb member_remove subtrie_at_path_empty) 
              next 
                case False 
                then have "subtrie_at_path (remove_term (SymbolNode m) (Fun f []) t0) p2 (Leaf (insert t s))" 
                  using str Pair Cons hy1 by (fastforce simp  add: Some Let_def subtrie_at_path_step_simp ) 
                then show ?thesis by blast
              qed 
            qed 
          qed 
        qed 
      next 
        case (SymbolNode x2)
        then show ?thesis using "3.prems"(1) Some s1 ws_dom_const by force
      qed 
    qed 
  qed
next
  case (4 m f a largs t0)
  then show ?case
  proof (cases "m $$ F f (Suc (length largs))")
    case None
    then show ?thesis 
      using "4.prems"(2)  by force 
  next
    case (Some aa)
    let ?m'= "(update_or_remove_entries aa [0..<Suc (length largs)] (\<lambda>i tr. if i < Suc (length largs) then remove_aux tr ((a # largs) ! i) t0 else undefined))"
    have domaa :"fmdom' aa = {0..< (Suc (length largs))}"
      by (metis "4"(2) Some atLeastLessThan_upt atLeast_upt length_suffixes list.size(3) nat.distinct(1) ws_fmdom')
    have  image_m : " \<And>i. i < Suc (length largs) \<Longrightarrow>  ?m' $$ i = (remove_aux (aa $$! i) ((a # largs) ! i) t0)"
      by (simp add: updrem_image domaa)
    have hi: " \<And>i. i < Suc (length largs) \<Longrightarrow> complete_storage_from_position (remove_term (aa $$! i) ((a # largs) ! i) t0) (p @ [(F f (Suc (length largs)), i)])"
    proof -
      fix i
      assume  vali: "i < Suc (length largs)"
      then have  w:" well_structured (aa$$!i)" 
        by (metis (no_types, opaque_lifting) "4.prems"(1) Some diff_zero fmlookup_dom'_iff fmran'I length_upt nat.distinct(1) option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases ws_dom_fun)
      then have c: " complete_storage_from_position (aa$$!i)  (p @ [(F f (Suc (length largs)), i)])" 
        by (metis "4.prems"(1) "4.prems"(2) Some complete_storage_from_position_subtrie fmdom'_notI length_Cons option.collapse vali ws_dom_fun)
      then have s:" sound_storage_from_position (aa$$!i)  (p @ [(F f (Suc (length largs)), i)])" 
        by (metis "4.prems"(1) "4.prems"(3) Some fmdom'_notI length_Cons option.collapse sound_storage_from_position_subtrie vali ws_dom_fun)
      then have  su: " subterm_at_path t0  (p @ [(F f (Suc (length largs)), i)]) ((a # largs) ! i)"
        using "4.prems"(4) subsubterm_at_path vali by fastforce  
      then show comp:"complete_storage_from_position (remove_term (aa $$! i) ((a # largs) ! i) t0) (p @ [(F f (Suc (length largs)), i)])"
        using "4.hyps" c s vali w by blast
    qed
    show ?thesis
      unfolding complete_storage_from_position_def
    proof (intro allI impI)
      fix t p2
      assume hy1: "t \<in> to_set (remove_term (SymbolNode m) (Fun f (a # largs)) t0)"
      then have  to:" t \<in> to_set (SymbolNode m)"
        using "4.prems"(1) remove_term_subset by blast 
      then have not:"t\<noteq> t0"
        using "4.prems"(1) "4.prems"(3) "4.prems"(4)  hy1 term_removed_from_trie_set by blast
      assume hy2: "path_of_term t (p @ p2) "
      then obtain s where h1: "( subtrie_at_path (SymbolNode m) p2 (Leaf (insert t s))) "
        using  "4.prems"(2) to by (fastforce  simp add: complete_storage_from_position_def )  
      show " \<exists>s. subtrie_at_path (remove_term (SymbolNode m) (Fun f (a # largs)) t0) p2 (Leaf (insert t s))"
      proof (cases p2 )
        case Nil
        then show ?thesis    using h1 subtrie_at_nil by blast 
      next
        case (Cons p0 list) 
        then show ?thesis
        proof (cases p0)
          case (Pair symb b)
          then show ?thesis
          proof (cases "symb = F f (Suc (length largs))")
            case True
            have bval: "b < Suc (length largs)"  
              by (metis "4.prems"(1) Pair True fmdom'I h1 local.Cons subtrie_cons ws_dom_fun2)    
            have w: "well_structured (aa $$! b)"
              by (metis "4.prems"(1) Some bval fmdom'I fmdom'_notI fmran'I length_suffixes nat.simps(3) option.collapse option.sel symbol.distinct(1) symbol.inject trie.inject(2) well_structured.cases well_structured_map_entry.cases ws_dom_fun)
            have  su: "subterm_at_path t0 (p @ [(F f (Suc (length largs)), b)]) ((a # largs) ! b)"
              using "4.prems"(4) bval subsubterm_at_path by fastforce 
            have "sound_storage_from_position (aa $$! b) (p @ [(F f (Suc (length largs)), b)])"
              by (metis "4.prems"(1) "4.prems"(3) Some bval fmdom'_notI length_Cons option.collapse sound_storage_from_position_subtrie ws_dom_fun)
            then have g1:"(remove_aux (aa $$! b) ((a # largs) ! b) t0) = None \<Longrightarrow> to_set (aa$$! b) \<subseteq> {t0}"
              using su to_set_remove_none w by blast
            then show ?thesis 
            proof (cases "?m' = {$$}")
              case T1: True
              have th: "(remove_aux (aa $$! b) ((a # largs) ! b) t0) = None"
                using T1 bval image_m by force
              then show ?thesis
                using h1 not subtrie_to_set g1
                by(fastforce simp add: Some  True subtrie_at_path_step_simp Cons Pair  )
            next
              case False
              then show ?thesis
              proof (cases "remove_aux (aa $$! b) ((a # largs) ! b) t0 ")
                case None
                then show ?thesis using h1 not subtrie_to_set g1
                  by (fastforce simp add: Some  True subtrie_at_path_step_simp Cons Pair  )
              next
                case s2:(Some val)
                then have h0 :"val= remove_term (aa $$! b) ((a # largs) ! b) t0"
                  by simp
                have "t \<in> to_set val "
                  by (metis Pair Some True h0 h1 remove_keeps_elements local.Cons member_remove not option.sel subtrie_cons subtrie_to_set_entry w)
                then obtain s where "subtrie_at_path val list (Leaf (insert t s))"
                  using hi[of b] bval  by (metis Pair True append_Cons append_Nil append_assoc complete_storage_from_position_def h0 hy2 local.Cons) 
                then show ?thesis using  bval image_m s2  by (auto simp add: Some Let_def s2 False True subtrie_at_path_step_simp Cons Pair )
              qed
            qed 
          next
            case False
            then have "subtrie_at_path (remove_term (SymbolNode m) (Fun f (a # largs)) t0) p2 (Leaf (insert t s))"
              using h1 by (auto simp add: Some Let_def subtrie_at_path_step_simp Pair Cons , metis fmempty_lookup fmlookup_drop option.distinct(1) )
            then show ?thesis
              by blast  
          qed
        qed
      qed
    qed 
  qed
qed

lemma remove_some_not_empty: 
  assumes "well_structured tr"
      and "remove_aux tr t t0 = Some r"
    shows "r \<noteq> empty_trie"
  using assms  by (induct tr t t0  arbitrary: r rule:remove_aux.induct) (auto simp add: not_well_structured_leaf Let_def split:if_splits)

lemma remove_preserves_minimal: 
  assumes "well_structured tr "
      and "minimal_storage  tr" 
    shows "minimal_storage (remove_term tr t t0)"
  using assms 
proof (induct tr t t0 rule: remove_aux.induct)
  case (1 s t t0)
  then show ?case
    using not_well_structured_leaf by blast 
next
  case (2 m x t0)
  then show ?case
  proof (cases "m $$ Star")
    case None
    then show ?thesis
      using "2.prems"(2) by auto 
  next
    case (Some m2)
    then obtain ts where s2: "m2 $$ 0 = Some (Leaf ts)"
      using "2.prems"(1) ws_dom_var by blast
    then have "ts \<noteq> {}"
      by (metis "2.prems"(2) Some fmran'I minimal_storage.cases trie.distinct(1) trie.inject(1) trie.sel(3))
    then have h1: "ts \<noteq> {t0} \<Longrightarrow> minimal_storage (SymbolNode ({symbol.Star $$:= {0 $$:= Leaf (Set.remove t0 ts)}}))"
      by (metis Diff_empty Diff_insert0 fmran'_singleton insert_Diff minimal_storage_leaf minimal_storage_node remove_def singletonD trie.distinct(1))
    have h3: "ts = {t0} \<Longrightarrow> fmdrop 0 (m $$! Star) = {$$} \<Longrightarrow> fmdrop symbol.Star m \<noteq> {$$} \<Longrightarrow> minimal_storage (SymbolNode (fmdrop symbol.Star m))"
      by (simp add: "2.prems"(2))
    have h4: "ts = {t0} \<Longrightarrow> fmdrop 0 (m $$! Star) \<noteq> {$$} \<Longrightarrow> minimal_storage (SymbolNode (m(symbol.Star $$:= fmdrop 0 (m $$! Star))))"
      by (metis "2.prems"(1) Some fmdrop_set_fmdom fmdrop_set_single option.sel ws_dom_var)
    show ?thesis apply (clarsimp simp add: Some s2 Let_def) using h1 h3 h4
      by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) Some dom_res_singleton fmdom'_notD fmfilter_true fmupd_idem minimal_storage_udt option.sel option.simps(3) ws_dom_var)   
  qed
next
  case (3 m f t0)
  then show ?case
  proof (cases "m $$ F f 0")
    case None
    then show ?thesis
      using "3.prems"(2) by auto 
  next
    case (Some m2)
    then obtain ts where s2: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "3.prems"(1) ws_dom_const)
    have "ts \<noteq> {}"
      by (metis "3.prems"(2) Some fmran'I minimal_storage.cases s2 trie.distinct(1) trie.sel(1) trie.sel(3))
    then have "ts \<noteq> {t0} \<Longrightarrow> minimal_storage (SymbolNode ({F f 0 $$:= {0 $$:= Leaf (Set.remove t0 ts)}}))"
      by (metis Diff_empty Diff_insert0 fmran'_singleton insert_Diff minimal_storage_leaf minimal_storage_node remove_def singletonD trie.distinct(1))
    then show ?thesis using "3.prems"(2) apply (clarsimp simp add: Some s2 fmran_empty' Let_def)
      by (smt (verit, ccfv_SIG) "3.prems"(1) Some dom_res_singleton fmdom'_notD fmdrop_set_fmdom fmdrop_set_single fmfilter_true fmupd_idem minimal_storage_udt option.simps(3) ws_dom_const)
  qed
next
  case (4 m f a largs t0)
  then show ?case 
  proof (cases "m $$ F f (Suc (length largs))" )
    case None
    then show ?thesis     using "4.prems"(2) by force
  next
    case (Some aa)
    have domaa:"fmdom' aa= {0..<(Suc (length largs))}"
      by (metis "4.prems"(1) Some atLeastLessThan_upt atLeast_upt length_suffixes list.size(3) nat.distinct(1) ws_fmdom')
    have hi: "\<And> i. i< Suc (length largs) \<Longrightarrow> minimal_storage (remove_term (aa $$! i) ((a # largs) ! i) t0)"
    proof-
      fix i 
      assume  H1: "i< Suc (length largs)"
      then have in_dom:"i  \<in>  fmdom' aa"
        by (simp add: domaa)
      then   have w:  "   well_structured (aa $$! i)  "
        using "4.prems"(1)  Some
        by (metis fmdom'I fmdom'_notI fmran'I nat.distinct(1) option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases) 
      have "minimal_storage (aa$$!i)"
        using  "4.prems"(2) Some 
        by (metis fmlookup_dom'_iff fmran'I in_dom minimal_storage.simps option.sel trie.distinct(1) trie.sel(3))
      then show " minimal_storage(remove_term (aa $$! i) ((a # largs) ! i) t0)"
        using "4.hyps" H1 w by presburger 
    qed
    have a1: " minimal_storage  empty_trie"
      by auto
    have a2: " minimal_storage (SymbolNode (fmdrop (F f (Suc (length largs))) m))"
      by (simp add: "4.prems"(2))
    let ?m'= "(update_or_remove_entries aa [0..<Suc (length largs)] (\<lambda>i tr. if i < Suc (length largs) then remove_aux tr ((a # largs) ! i) t0 else undefined))"
    have ir: "\<And> i r . ?m'$$ i = Some r \<Longrightarrow> minimal_storage r \<and> r \<noteq> empty_trie"
    proof-
      fix i r
      assume h0: "?m'$$ i = Some r"
      then have ival:"i<Suc (length largs)"
        by (meson "4.prems"(1) Some fmdom'I subsetD update_or_remove_entries_dom ws_dom_fun2)
      then have re: "r = remove_term (aa $$! i) ((a # largs) ! i) t0  "
        using domaa h0 updrem_image by fastforce
      then have hn: "minimal_storage r"
        using hi ival by blast
      have w: "well_structured (aa $$! i)"        
        by (metis "4.prems"(1) Some fmdom'I fmdom'_notI fmran'I ival length_Cons nat.simps(3) option.collapse option.sel symbol.inject symbol.simps(3) trie.sel(3) well_structured.cases well_structured_map_entry.simps ws_dom_fun)
      then  have "r \<noteq> empty_trie" 
        using remove_some_not_empty [of "(aa $$! i)" "((a # largs) ! i) " t0 r ]  w re  h0 updrem_image [of aa largs i a t0] domaa ival  by fastforce
      then show "  minimal_storage r \<and> r \<noteq> empty_trie"
        using hn by blast
    qed
    then have " minimal_storage (SymbolNode {F f (Suc (length largs)) $$:= ?m' })"
      by (smt (verit) fmran'E fmran'_singleton minimal_storage_node singletonD)
    then show ?thesis  
      using  "4.prems"(2)  minimal_storage_udt  by (auto simp add: Let_def Some a1 a2)
  qed
qed

lemma not_empty_to_set:
  assumes "well_structured tr"
      and "tr \<noteq> empty_trie"
      and "minimal_storage tr"
    shows "to_set tr \<noteq> {}"
  using assms
proof (induction tr rule: trie.induct)
  case (Leaf ts)
  then show ?case
    using not_well_structured_leaf
    by blast
next
  case (SymbolNode m)
  then obtain s where h0: "s \<in> fmdom' m"
    using SymbolNode.prems(2) exists_in_non_fmempty by blast
  then obtain m2 where t0: "m $$ s = Some m2"
    by (meson fmlookup_dom'_iff)
  then have  "m2 \<noteq> {$$}"
    by (metis SymbolNode.prems(1) fmdom'_empty h0 insert_not_empty lessThan_empty_iff option.sel trie.inject(2) well_structured.cases well_structured_map_entry.cases)
  then  show ?case
  proof (cases s)
    case Star
    then have " to_set (m2 $$! 0) \<noteq> {}"
      by (metis (no_types, opaque_lifting) SymbolNode.prems(1) SymbolNode.prems(3) fmlookup_ran'_iff minimal_storage.cases option.sel t0 to_set.simps(1) trie.distinct(1) trie.inject(2) ws_dom_var)
    then show ?thesis
      using SymbolNode.prems(1) Star t0 to_set_entry ws_dom_var by fastforce  
  next
    case (F f n)
    then show ?thesis
    proof (cases n)
      case 0
      then have "to_set (m2 $$! 0) \<noteq> {}"
        by (metis F SymbolNode.prems(1) SymbolNode.prems(3) fmran'I minimal_storage.cases option.sel t0 to_set.simps(1) trie.distinct(1) trie.sel(3) ws_dom_const)
      then show ?thesis
        using "0" F SymbolNode.prems(1) t0 to_set_entry ws_dom_const by fastforce 
    next
      case (Suc m)
      have ind: "0 \<in> fmdom' m2"
        by (metis F SymbolNode.prems(1) Suc add_diff_cancel_left' length_upt t0 ws_dom_fun zero_less_Suc)
      then  have nef: "minimal_storage  (m2 $$! 0)"
        by (metis SymbolNode.prems(3) fmlookup_dom'_iff fmran'I minimal_storage.cases option.sel t0 trie.distinct(1) trie.inject(2))
      have net: "m2 $$! 0 \<noteq> empty_trie"
        by (metis SymbolNode.prems(3) fmdom'_notI fmran'I ind minimal_storage.cases option.collapse t0 trie.distinct(1) trie.sel(3))
      have  w: " well_structured (m2 $$! 0)" 
        by (metis F SymbolNode.prems(1) Suc fmdom'_notI fmran'I h0 ind nat.distinct(1) option.collapse option.sel symbol.distinct(1) symbol.inject t0 trie.sel(3) well_structured.cases well_structured_map_entry.cases)
      have "to_set (m2 $$! 0) \<noteq> {}"
        by (metis SymbolNode.IH fmdom'_notI fmran'I ind nef net option.collapse t0 w)
      then show ?thesis 
        by (metis empty_iff equals0I fmdom'_notI ind option.collapse t0 to_set_entry)
    qed
  qed
qed

lemma remove_preserves_structure:
  assumes "well_structured tr"
      and "complete_storage_from_position tr p"
      and "minimal_storage tr"
      and "sound_storage_from_position tr p"
      and "subterm_at_path t0 p t"
    shows "well_structured (remove_term tr t t0)"
  using assms
proof (induction tr t t0 arbitrary: p rule: remove_aux.induct)
  case (1 s t t0)
  then show ?case 
    by (simp add: not_well_structured_leaf) 
next
  case (2 m x t0)
  then show ?case
  proof (cases "m $$ Star")
    case None
    then show ?thesis 
      using "2.prems"(1) by force
  next
    case (Some m2)
    then obtain ts where s2: "m2 $$ 0 = Some (Leaf ts)"
      using "2.prems"(1) ws_dom_var by blast
    have "well_structured (SymbolNode {Star $$:= {0 $$:= Leaf (Set.remove t0 ts)}})"
      by (simp add: fmran'_singleton ws_node wsme_var)
    then show ?thesis
      using "2.prems"(1)
      apply (auto simp add: ws_node Let_def Some)
      by (metis (no_types, lifting) s2 Some dom_res_singleton fmdom'_notD fmdrop_set_fmdom fmdrop_set_single fmfilter_true fmupd_idem option.case_eq_if option.discI option.sel remove_leaf.simps(1) well_structured_split ws_dom_var)
  qed
next
  case (3 m f t0)
  then show ?case
  proof (cases "m $$ F f 0")
    case None
    then show ?thesis 
      using "3.prems"(1) by force
  next
    case (Some m2)
    then obtain ts where s2: "m2 $$ 0 = Some (Leaf ts)"
      by (meson "3.prems"(1) ws_dom_const)
    have "well_structured (SymbolNode {F f 0 $$:= {0 $$:= Leaf (Set.remove t0 ts)}})"
      by (simp add: fmran'_singleton ws_node wsme_const)
    then show ?thesis
      using "3.prems"(1)
      apply (auto simp add: ws_node Let_def Some) 
      by (metis (no_types, lifting) s2 Some dom_res_singleton fmdom'_notD fmdrop_set_fmdom fmdrop_set_single fmfilter_true fmupd_idem option.case_eq_if option.discI option.sel remove_leaf.simps(1) well_structured_split ws_dom_const)
  qed
next
  case (4 m f a largs t0)
  then show ?case
  proof (cases "m $$ F f (Suc (length largs))")
    case None
    then show ?thesis 
      using "4.prems"(1) None by force
  next
    case (Some m0)
    have dom_m0: "fmdom' m0 = {0..<Suc (length largs)}"
      by (metis "4.prems"(1) Some atLeastLessThan_upt atLeast_upt length_suffixes list.size(3) nat.distinct(1) ws_fmdom')
    have hi: "\<And> i. i < Suc (length largs) \<Longrightarrow> well_structured (remove_term (m0 $$! i) ((a # largs) ! i) t0)"
    proof -
      fix i 
      assume H1: "i< Suc (length largs)"
      then have in_dom:"i  \<in>  fmdom' m0"
        by (simp add: dom_m0)
      then  have w:  "   well_structured (m0 $$! i)  "
        using "4.prems"(1) Some
        by (metis fmdom'I fmdom'_notI fmran'I nat.distinct(1) option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases) 
      have nefun:"minimal_storage (m0 $$! i)"
        by (metis "4.prems"(3) Some fmdom'_notI fmran'I in_dom minimal_storage.cases option.collapse trie.distinct(1) trie.sel(3))
      have co:" complete_storage_from_position (m0 $$! i) (p @ [(F f (Suc (length largs)),i) ])"
        by (metis "4.prems"(2) Some complete_storage_from_position_subtrie fmdom'_notI in_dom option.collapse) 
      have so: " sound_storage_from_position (m0 $$! i) (p @ [(F f (Suc (length largs)),i) ])"
        by (metis "4.prems"(4) Some fmdom'_notI in_dom option.collapse sound_storage_from_position_subtrie)
      have "subterm_at_path t0 (p @ [(F f (Suc (length largs)),i) ]) ((a# largs) ! i) "
        using "4.prems"(5) H1 subsubterm_at_path by fastforce  
      then show "well_structured  (remove_term (m0 $$! i) ((a # largs) ! i) t0)"
        using 4 H1 co nefun so w by blast
    qed
    have a1: "well_structured empty_trie"
      by (simp add: ws_node)
    have a2: "well_structured(SymbolNode (fmdrop (F f (Suc (length largs))) m))"
      by (simp add: "4.prems"(1))
    let ?m'= "(update_or_remove_entries m0 [0..<Suc (length largs)] (\<lambda>i tr. if i < Suc (length largs) then remove_aux tr ((a # largs) ! i) t0 else undefined))"
    have HL: "\<And> i. i \<in> fmdom'?m'  \<Longrightarrow>   i < Suc (length largs)"
      by (meson "4.prems"(1) Some subsetD update_or_remove_entries_dom ws_dom_fun2)
    have HR: "\<And> i . i < Suc (length largs) \<Longrightarrow> ?m' \<noteq> {$$}\<Longrightarrow> i \<in> fmdom'?m' "
    proof- 
      fix i :: nat
      assume h1:"i < Suc (length largs)" 
      have "i\<in> fmdom' m0"
        by (simp add: dom_m0 h1)
      assume  h2: "?m' \<noteq> {$$}"
      obtain k r where h0:  "?m'$$ k = Some r" using h2 exists_in_non_fmempty by blast
      have indom: "k\<in> fmdom' ?m' " by (simp add: fmdom'I h0)
      have valk: "k < Suc (length largs)"  by (meson HL fmdom'I h0)
      then have in_dom: "k\<in> fmdom' m0 " by (simp add: dom_m0)
      then have wsk: "well_structured (m0 $$! k)"    by (metis "4.prems"(1) Some fmdom'I fmdom'_notI fmran'I h1 less_nat_zero_code option.collapse option.sel symbol.distinct(1) symbol.inject trie.sel(3) well_structured.cases well_structured_map_entry.cases)
      then have remk:"remove_aux (m0 $$! k) ((a # largs) ! k) t0 = Some r"
        using dom_m0 h0 updrem_image valk by fastforce
      then have notfmempty:  "r \<noteq> empty_trie"
        using remove_some_not_empty wsk by blast
      then have re: " r = remove_term (m0 $$! k) ((a # largs) ! k) t0"
        by (simp add: remk)
      then have "to_set r \<noteq> {}"
        using notfmempty wsk   
        by (metis "4.prems"(3) Some fmdom'_notI fmran'I hi in_dom minimal_storage.simps not_empty_to_set option.collapse remove_preserves_minimal trie.distinct(1) trie.sel(3) valk)
      then obtain p0 t  s  where h3: " subtrie_at_path r  p0 (Leaf (insert t s))"  using non_empty_to_set_subtrie by blast
      have so:"sound_storage_from_position r ( p @ [(F f (Suc(length largs)), k)])"
        by (metis "4.prems"(4) "4.prems"(5) Some fmdom'_notI in_dom length_Cons option.collapse re remove_preserves_sound sound_storage_from_position_subtrie subsubterm_at_path valk wsk)
      then have "path_of_term t (p@ ((F f (Suc(length largs)) , k) #p0))"
        using h3 so sound_storage_from_position_def by force
      then obtain pi where  pat_i: "path_of_term t (p @ ((F f (Suc(length largs)), i) # pi))"
        using exists_term_at_end_path h1 by (metis fun_is_subterm_at_last path_of_subterm subterm_at_path_path_of_term)  
      have so2:"sound_storage_from_position  (remove_term (SymbolNode m) (Fun f (a # largs)) t0) (p)"
        using "4.prems"(1,4,5) remove_preserves_sound by blast 
      then have co2:"complete_storage_from_position  (remove_term (SymbolNode m) (Fun f (a # largs)) t0) (p)"
        using "4.prems"(1-5) remove_preserves_complete by blast
      have " t\<in>to_set (remove_term  (SymbolNode m) (Fun f (a # largs)) t0)"
        by (metis "4.prems"(1,4,5) Some fmdom'_notI h3 in_dom remove_keeps_elements length_Cons member_remove option.collapse re remove_term_subset sound_storage_from_position_subtrie subsubterm_at_path subtrie_to_set term_removed_from_trie_set to_set_entry valk wsk) 
      then obtain s where "subtrie_at_path (remove_term  (SymbolNode m) (Fun f (a # largs)) t0) ((F f (Suc (length largs)), i) # pi) (Leaf (insert t s))"
        using co2 complete_storage_from_position_def pat_i by blast
      then show "i \<in> fmdom'?m'"
        using option.sel subtrie_cons
        by ( fastforce simp add: Let_def  Some h2 subtrie_cons  )
    qed
    then have dom_m: "?m' \<noteq> {$$} \<Longrightarrow> fmdom' ?m' = {0..< Suc (length largs)}" 
      by (auto intro: HL)
    have t0: "\<And>i r. ?m' $$ i = Some r \<Longrightarrow>  well_structured r" 
    proof -
      fix i r
      assume h0: "?m'$$ i = Some r"
      then have ival: "i < Suc (length largs)"
        by (meson "4.prems"(1) Some fmdom'I subsetD update_or_remove_entries_dom ws_dom_fun2)
      then have re: "r = remove_term (m0 $$! i) ((a # largs) ! i) t0"
        using dom_m0 h0 updrem_image by fastforce
      then show hn: "well_structured r" using hi ival by blast
    qed
    then have ws: "?m' \<noteq> {$$} \<Longrightarrow>  well_structured_map_entry (F f (Suc (length largs))) ?m'" 
      by (metis (no_types, lifting) atLeastLessThan_upt atLeast_upt dom_m fmlookup_ran'_iff nat.distinct(1) wsme_func) 
    have "?m' \<noteq> fmempty \<Longrightarrow> well_structured (SymbolNode {F f (Suc (length largs)) $$:= ?m'})"
      by (simp add: ws ws_node)
    then show ?thesis
      apply (clarsimp simp add: Let_def Some a1 a2)
      using "4.prems"(1) well_structured_split by blast
  qed 
qed

section \<open>Index type and main theorems\<close>

typedef ('f, 'v) index =
  "{ t :: ('f, 'v) trie. well_structured t \<and> sound_storage t \<and> complete_storage t \<and> minimal_storage t }"
  by (rule exI [of _ "empty_trie"]) auto

setup_lifting type_definition_index

lift_definition index_to_set :: "('f, 'v) index \<Rightarrow> ('f, 'v) term set" is to_set .

lift_definition index_insert :: "('f, 'v) index \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) index" is "\<lambda>tr. \<lambda>t. insert_aux tr t t"
  by (simp add: complete_storage_alt_def insert_preserves_complete insert_preserves_sound insert_preserves_structure insert_preserves_minimal sound_storage_alt_def subterm_at_path.intros(1))

theorem index_insert_spec: "index_to_set (index_insert tr t) = insert t (index_to_set tr)"
  using insert_aux_keeps_elements insert_aux_subset insert_aux_adds_element
  by (metis (mono_tags, lifting) eq_iff Rep_index index_insert.rep_eq index_to_set.rep_eq insertE mem_Collect_eq subsetI)

lift_definition index_remove :: "('f, 'v) index \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) index" is "\<lambda>tr. \<lambda>t. remove_term tr t t"
  by (metis complete_storage_alt_def remove_preserves_complete remove_preserves_minimal remove_preserves_structure remove_preserves_sound sound_storage_alt_def subterm_at_path.intros(1))

theorem index_remove_spec: "index_to_set (index_remove tr t) = Set.remove t (index_to_set tr)"
  by (metis (no_types, lifting) Rep_index index_remove.rep_eq index_to_set.rep_eq mem_Collect_eq to_set_remove)

lift_definition index_retrieve_unifications :: "('f, 'v) index \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term set" is retrieve_unifications.

theorem index_retrieve_unifications_spec: "index_retrieve_unifications tr t1 = {t2. t2 \<in> index_to_set tr \<and> linear_unification t1 t2}"
  using retrieve_unifications_in_set retrieve_unifications_sound retrieve_unifications_complete sound_storage_alt_def complete_storage_alt_def subterm_at_path_empty
  by (smt (verit, best) Rep_index index_retrieve_unifications.rep_eq index_to_set.rep_eq mem_Collect_eq set_eqI)

lift_definition index_retrieve_variants :: "('f, 'v) index \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term set" is retrieve_variants.

theorem index_retrieve_variant_spec: "index_retrieve_variants tr t1 = {t2. t2 \<in> index_to_set tr \<and> linear_variant t2 t1}"
  using retrieve_variants_in_set retrieve_variants_sound retrieve_variants_complete sound_storage_alt_def complete_storage_alt_def subterm_at_path_empty
  by (smt (verit, best) Rep_index index_retrieve_variants.rep_eq index_to_set.rep_eq mem_Collect_eq set_eqI)

lift_definition index_retrieve_instances :: "('f, 'v) index \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term set" is retrieve_instances.

theorem index_retrieve_instances_spec: "index_retrieve_instances tr t1 = {t2. t2 \<in> index_to_set tr \<and> linear_instance t2 t1}"
  using retrieve_instances_in_set retrieve_instances_sound retrieve_instances_complete sound_storage_alt_def complete_storage_alt_def subterm_at_path_empty
  by (smt (verit, best) Rep_index index_retrieve_instances.rep_eq index_to_set.rep_eq mem_Collect_eq set_eqI)

lift_definition index_retrieve_generalizations :: "('f, 'v) index \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term set" is retrieve_generalizations.

theorem index_retrieve_generalizations_spec: "index_retrieve_generalizations tr t1 = {t2. t2 \<in> index_to_set tr \<and> linear_instance t1 t2}"
  using retrieve_generalizations_in_set retrieve_generalizations_sound retrieve_generalizations_complete sound_storage_alt_def complete_storage_alt_def subterm_at_path_empty
  by (smt (verit, best) Rep_index index_retrieve_generalizations.rep_eq index_to_set.rep_eq mem_Collect_eq set_eqI)

end