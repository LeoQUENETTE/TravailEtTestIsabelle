theory Test_Isabelle_C
imports
  Main
  Isabelle_C.C_Main
begin

declare[[C_lexer_trace]]

C \<open>
/*@ preclean  \<open>a > 0 && b > 0\<close>
    postclean \<open>\result >= a && \result >= b\<close>
*/
int add(int a, int b) {
  return a + b;
}
\<close>
 
end