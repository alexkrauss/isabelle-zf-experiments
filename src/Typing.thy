theory Typing
  imports Nat_ZF
begin

ML_file "zf_logic.ML"


text \<open>
  We define a syntax for types, which is disconnected from the actual term language, but
  uses the same machinery. It just consists of a type declaration and some uninterpreted symbols,
  most notably for Pi-types (dependent function types).
  
  We define some syntax translations to introduce a telescope-like syntax.
\<close>

typedecl type

axiomatization set :: "i \<Rightarrow> type"
and Type :: "type"
and o :: "type"
and Pi_type :: "type \<Rightarrow> ('a \<Rightarrow> type) \<Rightarrow> type"
and Implicit_Pi_type :: "type \<Rightarrow> ('a \<Rightarrow> type) \<Rightarrow> type"
and has_type :: "('b::{}) \<Rightarrow> type \<Rightarrow> prop" (infix ":::" 40)

syntax
  "_telescope" :: "[pttrn, type, type] \<Rightarrow> type"  ("'(_ : _') \<Rightarrow> _" 50)
  "_telescope_implicit" :: "[pttrn, type, type] \<Rightarrow> type"  ("'{_ : _'} \<Rightarrow> _" 50)
translations
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"
  "{x : A} \<Rightarrow> B" \<rightleftharpoons> "CONST Implicit_Pi_type A (\<lambda>x. B)"

term "(x : A) \<Rightarrow> (y : B) \<Rightarrow> C y"
term "t ::: (x : set A) \<Rightarrow> (set (A + B))"


subsection \<open> Interpretation of soft types as propositions \<close>

definition Univ :: "i \<Rightarrow> o"
  where "Univ x \<longleftrightarrow> True"

definition o_pred :: "o \<Rightarrow> o"
  where "o_pred x \<longleftrightarrow> True"
             
ML_file "soft_type.ML"

term "Nil ::: (A: Type) \<Rightarrow> set (List A)"


lemma eq: "eq ::: (x: set A) \<Rightarrow> (y: set A) \<Rightarrow> o"
  unfolding o_pred_def ..

ML \<open>

  Thm.prop_of @{thm eq}
  |> Soft_Type.judgement_of_schematic_prop @{context}
  |> Soft_Type.mk_judgement
  |> Output.tracing o Syntax.string_of_term @{context}

\<close>



text \<open>
  The interpretation of soft types as defined above is given extra-logically by a function that
  translates typing judgements into propositions.
\<close>


ML_file "soft_type_context.ML"
ML_file "soft_type_inference.ML"


text \<open> Example: Inferring types for list append \<close>

axiomatization
  List :: "i \<Rightarrow> i"
and Nil :: "i \<Rightarrow> i"
and Cons :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
and append :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
declare [[type "Nil ::: (A: Type) \<Rightarrow> set (List A)"]]
declare [[type "Cons ::: (A: Type) \<Rightarrow> (x: set A) \<Rightarrow> (xs : set (List A)) \<Rightarrow> set (List A)"]]

context
  fixes A :: "i"
begin


ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "Nil A = B"}
]\<close>


ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "%A. Nil A"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "%A x xs. Cons A x xs"}
]\<close>

declare [[type "append ::: (A: Type) \<Rightarrow> (xs: set (List A)) \<Rightarrow> (ys : set (List A)) \<Rightarrow> set (List A)"]]

ML \<open>

Soft_Type_Inference.print_inferred_types @{context} [
  @{term "append A (Cons A x xs) ys = Cons A x (append A xs ys)"},
  @{term "append A (Nil A) ys = ys"} 
]
\<close>

(*
ML \<open>

Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<And>A x xs ys. append A (Cons A x xs) ys = Cons A x (append A xs ys)"},
  @{term "\<And>A ys. append A (Nil A) ys = ys"} 
]
\<close>
*)


end

text \<open> Example: Inferring types for vectors of given length \<close>

axiomatization
  Vec :: "i \<Rightarrow> i \<Rightarrow> i"
and VNil :: "i \<Rightarrow> i"
and VCons :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
and add :: "i \<Rightarrow> i \<Rightarrow> i"
and vappend :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
declare [[type "Vec ::: (A: Type) \<Rightarrow> (n: set nat) \<Rightarrow> Type"]]
declare [[type "VNil ::: (A: Type) \<Rightarrow> set (Vec A 0)"]]
declare [[type "VCons ::: (A: Type) \<Rightarrow> (n: set nat) \<Rightarrow> (x: set A) \<Rightarrow> (xs : set (Vec A n)) \<Rightarrow> set (Vec A (succ n))"]]
declare [[type "add ::: (n : set nat) \<Rightarrow> (m : set nat) \<Rightarrow> set nat"]]
declare [[type "succ ::: (n : set nat) \<Rightarrow> set nat"]]
declare [[type "0 ::: set nat"]]
declare [[type "vappend ::: (A: Type) \<Rightarrow> (n: set nat) \<Rightarrow> (m: set nat) \<Rightarrow> (xs: set (Vec A n)) 
\<Rightarrow> (ys: set (Vec A m)) \<Rightarrow> set (Vec A (add n m))"]]

(*

ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "vappend A (succ n) m (VCons A n x xs) ys
   = VCons A (add n m) x (vappend A n m xs ys)"}  
]\<close>

ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "vappend A (succ n) m (VCons A n x xs) ys
   = VCons A (add n m) x (vappend A n m xs ys)"}
]\<close>


axiomatization
  bijective :: "i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> o"
and compose :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i \<Rightarrow> i"
declare [[type "bijective ::: (A: Type) \<Rightarrow> (B: Type) \<Rightarrow> (f:(x:A)\<Rightarrow>B) \<Rightarrow> Type"]]


lemma "f \<in> bij A B \<Longrightarrow> g \<in> bij B C \<Longrightarrow> g O f \<in> bij A C"


*)





end
