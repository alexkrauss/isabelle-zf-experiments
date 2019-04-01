(*  Title:      soft_type.ML
    Author:     Alexander Krauss

Basic syntactic operations on soft types.

Soft types can be represented as Pure terms, but these terms have no logical significance.
They merely allow us to use Isabelle's syntax machinery.

A typing judgement can be converted into a proposition in Pure, which then expresses its actual
semantics.
*)

signature SOFT_TYPE =
sig
  val typeT: typ

  (* Constants for the term representation *)
  val set_const: term
  val Type_const: term
  val Pi_const: bool -> typ -> term 

  datatype judgement =
    Judgement of term * term

  (* convert from representation *)
  val read_judgement: term -> judgement
  val mk_judgement: judgement -> term
 
  (* the semantic proposition associated with a typing judgement *)
  val prop_of_judgement: judgement -> term
  val judgement_of_prop: Proof.context -> term -> judgement
  val judgement_of_schematic_prop: Proof.context -> term -> judgement

end;

structure Soft_Type : SOFT_TYPE =
struct

val typeT = @{typ "type"};

datatype judgement =
  Judgement of term * term;

fun read_judgement tm = 
  case tm of 
    Const (@{const_name "has_type"}, _) $ t $ ty => Judgement (t, ty)
  | _ => error ("Invalid judgement: " ^ Syntax.string_of_term @{context} tm);

fun mk_judgement (Judgement (t, ty)) =
  Const (@{const_name "has_type"}, fastype_of t --> typeT --> @{typ prop}) $ t $ ty

fun is_judgement tm = 
  case tm of 
    Const (@{const_name "has_type"}, _) $ _ $ _ => true
  | _ => false


val set_const = @{term "set"};
val Type_const = @{term "Type"}
val o_const = @{term "o"}
fun Pi_const i T = 
  Const (if i then @{const_name "Implicit_Pi_type"} else @{const_name "Pi_type"},
    typeT --> (T --> typeT) --> typeT);

fun prop_of_judgement (Judgement (t, tau)) = 
  case tau of 
    Const (@{const_name "Typing.set"}, _) $ A => 
      ZF_Logic.Trueprop $ ZF_Logic.mk_mem t A
  | Const (@{const_name Type}, _) => ZF_Logic.Trueprop $ (@{term "Univ"} $ t)
  | Const (@{const_name o}, _) => ZF_Logic.Trueprop $ (@{term "o_pred"} $ t)
  | Const (@{const_name "Pi_type"}, _) $ A $ Abs (x, T, B) => 
      Logic.all_const T $ 
        Abs (x, T, Logic.mk_implies (
          prop_of_judgement (Judgement (Bound 0, Term.incr_boundvars 1 A)), 
          prop_of_judgement (Judgement (Term.incr_boundvars 1 t $ Bound 0, B))))
  | _ => error ("Illegal soft type: " ^ @{make_string} tau);


fun decr_bounds t = 
  if (Term.is_dependent t) then error "is_dependent" 
  else Term.subst_bound (Bound 0, t)




(* The inverse of prop_of_judgement. 

This function requires its input to be precisely in the form produced by prop_of_judgement.
Equivalent forms, such as hhf normal form are not converted correctly.
*)
fun judgement_of_prop1 t =
  case t of
    Const (@{const_name "Pure.all"}, _) $ 
      Abs (v, T, Const (@{const_name "Pure.imp"}, _) $ u $ s) =>
        let
          val Judgement (x, A) = judgement_of_prop1 u
          val Judgement (fx, Bx) = judgement_of_prop1 s
        in 
          case fx of
            f $ x1 => 
              if x aconv x1 
              then Judgement (decr_bounds f, Pi_const false T $ decr_bounds A $ Abs (v, T, Bx))
              else error ("Bad prop: " ^ @{make_string} (fx, x, Bx))
          | _ => error "Bad prop 2"
        end
  | Const (@{const_name "Trueprop"}, _) $ (Const (@{const_name "mem"}, _) $ x $ A) =>
       Judgement (x, set_const $ A)
  | Const (@{const_name "Trueprop"}, _) $ (Const (@{const_name "Univ"}, _) $ x) =>
       Judgement (x, Type_const)
  | Const (@{const_name "Trueprop"}, _) $ (Const (@{const_name "o_pred"}, _) $ x) =>
       Judgement (x, o_const)






(* decomposes a hhf-style proposition in its components, i.e.
  - newly fixed variables
  - assumptions
  - a conclusion
*)
fun dest_hhf ctxt t =
  let
    val ((params, imp), ctxt') = Variable.focus NONE t ctxt
  in
    (ctxt', map #2 params, Logic.strip_imp_prems imp, Logic.strip_imp_concl imp)
  end


fun is_composite t = case t of
   Const (@{const_name "Pure.imp"}, _) $ _ $ _ => true
 | Const (@{const_name "Pure.all"}, _) $ _ => true
 | _ => false


fun judgement_of_prop ctxt local_types t =
  (Output.tracing ("judgement_of_prop: " ^ Syntax.string_of_term ctxt t);
  case t of
    Const (@{const_name "Trueprop"}, _) $ (Const (@{const_name "mem"}, _) $ x $ A) =>
       Judgement (x, set_const $ A)
  | Const (@{const_name "Trueprop"}, _) $ (Const (@{const_name "Univ"}, _) $ x) =>
       Judgement (x, Type_const)
  | Const (@{const_name "Trueprop"}, _) $ (Const (@{const_name "o_pred"}, _) $ x) =>
       Judgement (x, o_const)
  | _ => if is_composite t then
      let
        val (ctxt', _, assms, concl) = dest_hhf ctxt t
        val type_assms = map (judgement_of_prop ctxt' local_types) assms
        val local_type_context = map (fn Judgement (t, st) => (t, st)) type_assms
        val Judgement (f_xs, st) = judgement_of_prop ctxt' local_types concl
        val (f, xs) = Term.strip_comb f_xs (* assume for now that the number of variables matches *)

        fun get_var_type v = case AList.lookup (op aconv) local_type_context v of
          SOME st => st
          | NONE => error ("Cannot find type of variable: " ^ @{make_string} v)

        fun mk_Pi_type x tau =
          Pi_const false (fastype_of x) $ get_var_type x $ lambda x tau

        val fun_type = fold_rev mk_Pi_type xs st
      in
        Judgement (f, fun_type)
      end
      else error ("Cannot analyze typing proposition: " ^ @{make_string} t))


fun judgement_of_schematic_prop ctxt p =
  let
    val ([p_fixed], ctxt') = Variable.import_terms true [p] ctxt
    val Judgement (t, st) = judgement_of_prop ctxt [] p_fixed
    val [t_exported, st_exported] = Variable.export_terms ctxt' ctxt [t, st]
  in
    Judgement (t_exported, st_exported)
  end


(* Input check phase that replaces a typing judgement by the corresponding proposition.
   Thus, typing judgements can be used to state properties. *)
fun replace_judgement ctxt t = 
  if is_judgement t 
  then prop_of_judgement (read_judgement t)
  else case t of
    s $ u => replace_judgement ctxt s $ replace_judgement ctxt u
  | Abs (x, T, b) => Abs (x, T, replace_judgement ctxt b)
  | t => t;

val _ = Context.>> (Syntax_Phases.term_check 0 "soft_type_expand" (fn ctxt => (map (replace_judgement ctxt))));


end
