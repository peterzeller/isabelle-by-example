theory introduction
  imports Main
begin

section "Introduction"

text \<open>
Isabelle/HOL includes:

\<^item> A functional programming language
\<^item> A system for interactively proving statements

\<close>

subsection "Application: Functional Programming"

text \<open>The following example shows an implementation of the binary search algorithm, 
a termination proof for the function, and a correctness proof.\<close>

function binary_search where
\<open>binary_search list key low high = (
  if low \<ge> high then
    None
  else 
    let mid = (low + high) div 2 in
    let (k,v) = list ! mid in
    if k < key then
      binary_search list key low (mid - 1)
    else if k > key then
      binary_search list key (mid + 1) high
    else
      Some v)\<close>
  by pat_completeness auto
termination by (relation "measure (\<lambda>(list,key,low,high). 1 + high - low)") auto

(*
lemma 
  assumes sorted: "sorted list"
    and unique_keys: "distinct (map fst list)"
  shows "if binary_search list key l h = Some v then (key,v) \<in> set list"  

text "Look at @{thm[display] blub}."
*)

subsection "Application: Mathematics"

text \<open>If you are more interested in mathematics than programming, the following example might be for you.
It is a proof that there are infinitely many prime numbers formalized in Isabelle.\<close>


end