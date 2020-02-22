theory test
  imports Main
begin

section "Introduction"

text \<open>
Isabelle/HOL includes:

\<^item> A functional programming language
\<^item> A system for interactively proving statements

\<close>

lemma blub: "\<forall>x::nat. x + 1 > x"
  by simp


text "Look at @{thm[display] blub}."


end