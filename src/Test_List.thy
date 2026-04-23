theory Test_List
imports
  Main
  Refine_Imperative_HOL.Sepref
  Refine_Imperative_HOL.Sepref_HOL_Bindings
  Refine_Imperative_HOL.IICF

begin

definition search_foreach :: "nat list \<Rightarrow> nat \<Rightarrow> bool nres" where
"search_foreach xs y = do {
  result \<leftarrow> nfoldli xs (\<lambda>found. \<not>found) 
    (\<lambda>x _. RETURN (x = y))
    False;
  RETURN result
}"

sepref_definition search_foreach_impl is "uncurry search_foreach" :: 
"(list_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding search_foreach_def
  apply sepref
  done


definition search_rec :: "nat list \<Rightarrow> nat \<Rightarrow> bool nres" where
"search_rec xs y \<equiv> RECT(\<lambda>self (xs,y).
case xs of
  [] \<Rightarrow> RETURN False |
  x#xss \<Rightarrow> do {
    if x = y then RETURN True
    else do {r \<leftarrow> self(xss,y); RETURN r}
  }
)(xs,y) "

sepref_definition search_rec_impl is "uncurry search_rec" :: "(list_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding search_rec_def
  apply sepref
  done


definition incr_list2 where "incr_list2 l \<equiv> nfoldli 
  [0..<length l]
  (\<lambda>_. True)
  (\<lambda>i l. ASSERT (i<length l) \<then> RETURN (l[i:=1+l!i]))
  l"

sepref_definition incr_list3 is "incr_list2" ::
 "(array_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn nat_assn"
  unfolding incr_list2_def[abs_def]
  by sepref


definition is_list where
"is_list xs \<equiv> case xs of [] \<Rightarrow> RETURN xs | x#xss \<Rightarrow> RETURN xs"

sepref_definition is_list_impl is "is_list" 
  :: "(list_assn  nat_assn)\<^sup>k \<rightarrow>\<^sub>a list_assn  nat_assn"
  unfolding is_list_def[abs_def]
  by sepref

definition append :: "nat \<Rightarrow> nat list \<Rightarrow> nat list nres" where
"append y xs = RETURN (y#xs)"

sepref_definition append_impl is "uncurry append"
::" nat_assn\<^sup>k  *\<^sub>a (list_assn nat_assn)\<^sup>d  \<rightarrow>\<^sub>a list_assn nat_assn"
  unfolding append_def[abs_def]
  apply sepref
  done

export_code append_impl in Haskell

definition remove :: "nat \<Rightarrow> nat list \<Rightarrow> nat list nres" where
"remove y xs = do {
  l \<leftarrow> nfoldli xs 
    (\<lambda>_. True)
    (\<lambda>x acc. if x \<noteq> y then RETURN (x#acc) else RETURN (acc))
     xs;
  RETURN l
}"

sepref_definition remove_impl is "uncurry remove"
:: " nat_assn\<^sup>k *\<^sub>a (list_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a list_assn nat_assn"
  unfolding remove_def[abs_def]
  apply sepref
  done

export_code remove_impl in Haskell



definition bubble_sort_pass :: "('a :: linorder) list \<Rightarrow> 'a list nres" where
  "bubble_sort_pass xs \<equiv> do {
    ASSERT (length xs > 1);
    nfoldli [0..<length xs - 1] (\<lambda>_. True)
      (\<lambda>i xs. do {
        ASSERT (i+1 < length xs);
        if xs ! i > xs ! (i+1) then
          RETURN (xs[i := xs!(i+1), i+1 := xs!i])
        else
          RETURN xs
      }) xs
  }"

definition bubble_sort :: "('a :: linorder) list \<Rightarrow> 'a list nres" where
  "bubble_sort xs \<equiv> do {
    ASSERT (length xs > 1);
    let n = length xs;
    (_, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, xs). i < n)
      (\<lambda>(i, xs). do {
        ASSERT (length xs > 1);
        xs' \<leftarrow> bubble_sort_pass xs;
        ASSERT (length xs' > 1);
        if xs' = xs then RETURN (n, xs')  
        else RETURN (i+1, xs')
      }) (0, xs);
    RETURN xs
  }"
lemma array_assn_keep_merge[sepref_frame_merge_rules]:
  "hn_ctxt (array_assn A) x xi \<or>\<^sub>A hn_ctxt (array_assn A) x xi \<Longrightarrow>\<^sub>t hn_ctxt (array_assn A) x xi"
  by (simp add: entt_disjI1')
lemma array_assn_keep_rule[sepref_frame_match_rules]:
  "hn_ctxt (array_assn A) x xi \<Longrightarrow>\<^sub>t hn_ctxt (array_assn A) x xi"
  by simp
sepref_definition bubble_sort_impl is "bubble_sort" 
::"(array_assn int_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn int_assn"
  unfolding bubble_sort_def[abs_def]
  unfolding bubble_sort_pass_def[abs_def]
  apply (auto simp: rdomp_def array_assn_def)

  apply sepref_dbg_keep
      supply [[goals_limit = 1]]
      apply sepref_dbg_trans_keep
               apply sepref_dbg_trans_step_keep
  apply (sepref_dbg_side_keep)
  done

end