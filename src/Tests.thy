theory Tests
imports Typing
begin


context
  fixes A B N :: i \<comment> \<open>some sets\<close>
  fixes f :: "i \<Rightarrow> i" \<comment> \<open>a function\<close>
  fixes vec :: "i \<Rightarrow> i" \<comment> \<open>a type constructor\<close>
  fixes vec_concat :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" \<comment> \<open> Vector concatenation. First two arguments are type arguments \<close>
begin

ML \<open>
  fun testfn ctxt t = 
    let
      val _ = Output.tracing (Syntax.string_of_term ctxt t)
      val j = Soft_Type.judgement_of_schematic_prop ctxt t
      val prp = Soft_Type.prop_of_judgement ctxt j
      (* In the process, we lose type information, but the next step should be a fixpoint *)
      val j2 = Soft_Type.judgement_of_schematic_prop ctxt prp
      val _ = if (j <> j2) then error ("Not inverse" ^ (@{make_string} (prp, t))) else ();
    in 
      Syntax.pretty_term ctxt prp
    end;

    testfn @{context} @{term "f ::: (x : set A) \<Rightarrow> set (A + B)"};
    testfn @{context} @{term "vec_concat ::: {n : set N} \<Rightarrow> {m : set N} \<Rightarrow> (x : set (vec n)) \<Rightarrow> (y : set (vec m)) \<Rightarrow> set (vec (n + m))"};


\<close>

end




end