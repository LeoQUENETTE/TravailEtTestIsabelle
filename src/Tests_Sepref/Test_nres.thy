theory Test_nres

imports 
  Main
  First_Order_Terms.Term
  Refine_Imperative_HOL.IICF
  Refine_Imperative_HOL.Sepref
  "Finite-Map-Extras.Finite_Map_Extras"

begin


datatype 'f symbol =
	Star 
| F 'f nat


datatype (plugins del: size) ('f,'v) trie =
  Leaf "('f,'v) term set"
| SymbolNode (children: "('f symbol, (nat, ('f, 'v) trie) fmap) fmap")
  where
    "children (Leaf x) = fmempty"

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

function trie_depth_nres :: "('f,'v) trie \<Rightarrow> nat nres" where
"trie_depth_nres t \<equiv> do(RETURN 0)"



end

