theory Test_BinSearch
imports 
  Main
  Refine_Imperative_HOL.Sepref
  Refine_Imperative_HOL.Sepref_HOL_Bindings
  Refine_Imperative_HOL.IICF
begin

abbreviation "bin_search_invar xs x \<equiv> (\<lambda>(l,h). 
      0\<le>l \<and> l\<le>h \<and> h\<le>length xs 
    \<and> (\<forall>i<l. xs!i<x) \<and> (\<forall>i\<in>{h..<length xs}. x \<le> xs!i))"

definition "bin_search xs x \<equiv> do {
  (l,h) \<leftarrow> WHILEIT (bin_search_invar xs x)
    (\<lambda>(l,h). l<h) 
    (\<lambda>(l,h). do {
      ASSERT (l<length xs \<and> h\<le>length xs \<and> l\<le>h);
      let m = l + (h-l) div 2;
      if xs!m < x then RETURN (m+1,h) else RETURN (l,m)
    }) 
    (0,length xs);
  RETURN l
}"


definition "fi_spec xs x = SPEC (\<lambda>i. i=find_index (\<lambda>y. x\<le>y) xs)"

sepref_definition bin_search_impl is "uncurry bin_search" :: 
  "(list_assn nat_assn)\<^sup>k *\<^sub>a (nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  unfolding bin_search_def
  apply sepref_dbg_keep
  done                         

export_code bin_search_impl in Haskell
end