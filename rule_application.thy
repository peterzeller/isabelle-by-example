section "Rule Application"

theory rule_application
  imports Main
begin


text \<open>
One of the basic concepts in Isabelle is rule application.
A rule consists of a list of premises and a conclusion.

For example consider the rule @{thm[source] finite_UnI}: 

@{thm finite_UnI}

This rule has two premises: @{term F} must be finite and @{term G} must be finite.
The conclusion is that the union  @{term \<open>F \<union> G\<close>} is also finite.

The variables starting with a question mark denote schematic variables, which we can replace with arbitrary terms of the correct type.
For example we can use @{term \<open>{a,b,c}\<close>} for @{term F} and @{term \<open>{d,e}\<close>} for @{term G} using the syntax 

@{thm[source] finite_UnI[where F=\<open>{a,b,c}\<close> and G=\<open>{d,e}\<close>]}

and get a specialized version of the rule:

@{thm finite_UnI[where F=\<open>{a,b,c}\<close> and G=\<open>{d,e}\<close>]}

When applying a rule, the conclusion is matched against the current goal.
If it matches,  the goal is replaced by the premises of the rule.
As an example consider the following Lemma:
\<close>

lemma rule_application_example_1:
  shows \<open>finite ({a,b,c} \<union> {d,e})\<close>
proof (rule finite_UnI[where F=\<open>{a,b,c}\<close> and G=\<open>{d,e}\<close>])

  text \<open>After starting the proof with this rule, we are left with the following 2 subgoals:

 @{subgoals}

We can then use \<^bold>\<open>show\<close> to start a proof for these subgoals:
\<close>

  show \<open>finite {a, b, c}\<close>
  proof (rule finite.insertI[where a=a and A=\<open>{b, c}\<close>])
    show \<open>finite {b, c}\<close>
    proof (rule finite.insertI[where a=b and A=\<open>{c}\<close>])
      show \<open>finite {c}\<close>
      proof (rule finite.insertI[where a=c and A=\<open>{}\<close>])
        show \<open>finite {}\<close>
        proof (rule finite.emptyI)
        qed
      qed
    qed
  qed

  show \<open>finite {d, e}\<close>
  proof (rule finite.insertI[where a=d and A=\<open>{e}\<close>])
    show \<open>finite {e}\<close>
    proof (rule finite.insertI[where a=e and A=\<open>{}\<close>])
      show \<open>finite {}\<close>
      proof (rule finite.emptyI)
      qed
    qed
  qed
qed

text \<open>
In the proofs for the subgoals used two other rules:

 \<^item> @{thm[source] finite.insertI}: @{thm finite.insertI}
 \<^item> @{thm[source] finite.emptyI}: @{thm finite.emptyI}


Note that the notation @{term \<open>{a,b,c}\<close>} is just a nicer syntax for calls to the @{term insert} function and the unsugared form would be @{term[show_abbrevs=false] \<open>insert a (insert b (insert c {}))\<close>}.


\<close>

subsection "Cutting down on Syntax"

text \<open>The proof above is probably the most verbose and explicit way it can be formulated in Isabelle.\<close>

subsubsection "Matching Variables"

text \<open>First of all, Isabelle can often figure out the values for schematic variables in rules by matching the conclusion and the goal.
So we can simply omit the \<^bold>\<open>where\<close> attribute in the proofs:\<close>

lemma rule_application_example_2:
  shows \<open>finite ({a,b,c} \<union> {d,e})\<close>
proof (rule finite_UnI)

  show \<open>finite {a, b, c}\<close>
  proof (rule finite.insertI)
    show \<open>finite {b, c}\<close>
    proof (rule finite.insertI)
      show \<open>finite {c}\<close>
      proof (rule finite.insertI)
        show \<open>finite {}\<close>
        proof (rule finite.emptyI)
        qed
      qed
    qed
  qed

  show \<open>finite {d, e}\<close>
  proof (rule finite.insertI)
    show \<open>finite {e}\<close>
    proof (rule finite.insertI)
      show \<open>finite {}\<close>
      proof (rule finite.emptyI)
      qed
    qed
  qed
qed

text \<open>When functions are involved, matching can become a bit more complicated.
For more details see Section \ref{unification}.\<close>

subsubsection "Direct proofs with by"

text \<open>When a proof can be completed with a single step, it can be abbreviated using \<^bold>\<open>by\<close>. 
Instead of ``\<^bold>\<open>proof\<close> X \<^bold>\<open>qed\<close>'' we can just write ``\<^bold>\<open>by\<close> X'': \<close>

lemma rule_application_example_3:
  shows \<open>finite ({a,b,c} \<union> {d,e})\<close>
proof (rule finite_UnI)

  show \<open>finite {a, b, c}\<close>
  proof (rule finite.insertI)
    show \<open>finite {b, c}\<close>
    proof (rule finite.insertI)
      show \<open>finite {c}\<close>
      proof (rule finite.insertI)
        show \<open>finite {}\<close>
          by (rule finite.emptyI)
      qed
    qed
  qed

  show \<open>finite {d, e}\<close>
  proof (rule finite.insertI)
    show \<open>finite {e}\<close>
    proof (rule finite.insertI)
      show \<open>finite {}\<close>
        by (rule finite.emptyI)
    qed
  qed
qed

subsection "Apply Style Proofs"

text \<open>For exploration and for short proofs it can be tedious to write down all subgoals explicitly using \<^bold>\<open>show\<close>. 
We can avoid this by starting the proof with \<^bold>\<open>apply\<close> instead of \<^bold>\<open>proof\<close>.
This will just transform the current proof state and we can directly continue on this state with other calls to \<^bold>\<open>apply\<close> or by starting a structured \<^bold>\<open>proof\<close>:
\<close>

lemma rule_application_example_4:
  shows \<open>finite ({a,b,c} \<union> {d,e})\<close>
  apply (rule finite_UnI)
  text \<open>Proof state is now: @{subgoals}\<close>
   apply (rule finite.insertI)
  text \<open>Proof state is now: @{subgoals}\<close>
   apply (rule finite.insertI)
  text \<open>Proof state is now: @{subgoals}\<close>
   apply (rule finite.insertI)
  text \<open>Proof state is now: @{subgoals}\<close>
   apply (rule finite.emptyI)
  text \<open>Proof state is now: @{subgoals}\<close>
  apply (rule finite.insertI)
  text \<open>Proof state is now: @{subgoals}\<close>
  apply (rule finite.insertI)
  text \<open>Proof state is now: @{subgoals}\<close>
  apply (rule finite.emptyI)
  text \<open>We have no more subgoals and can complete the proof with \<^bold>\<open>done\<close>:\<close>
  done

text \<open>Note that this style of proof can be hard to follow by just reading the proof text since the proof text contains no information about the intermediate steps. \<close>

lemma rule_application_example_5:
  shows \<open>finite ({a,b,c} \<union> {d,e})\<close>
  apply (rule finite_UnI)
   apply (rule finite.insertI)
   apply (rule finite.insertI)
   apply (rule finite.insertI)
   apply (rule finite.emptyI)
  apply (rule finite.insertI)
  apply (rule finite.insertI)
  apply (rule finite.emptyI)
  done

subsection "Combining Methods"

text \<open>The proof above contains several repeated lines.
We can add a plus to a proof method to repeat it as often as it is applicable:\<close>

lemma rule_application_example_6:
  shows \<open>finite ({a,b,c} \<union> {d,e})\<close>
  apply (rule finite_UnI)
   apply (rule finite.insertI)+
   apply (rule finite.emptyI)
  apply (rule finite.insertI)+
  apply (rule finite.emptyI)
  done

text \<open>Since the \<^bold>\<open>rule\<close> method accepts several rules (which will be tried from left to right), we can the combine the proof to a single line:\<close>

lemma rule_application_example_7:
  shows \<open>finite ({a,b,c} \<union> {d,e})\<close>
  by (rule finite_UnI finite.insertI finite.emptyI)+



end