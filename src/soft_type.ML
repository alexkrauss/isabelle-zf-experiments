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

  (* Locally nameless ML representation of soft types. *)
  datatype soft_type =
    Set of term (* May contain Bound occurrences from Pi binding. *)
  | Pi of bool (* implicit *) 
          * string (* bound var name *)
          * typ (* bound var meta type *)
          * soft_type (* left hand side type *)
          * soft_type (* right-hand side (dependent) type *)
  | STVar of indexname (* unification variable *)

  datatype judgement =
    Judgement of term * soft_type

  (* convert from and to term representation *)
  val read_soft_type: term -> soft_type
  val read_judgement: term -> judgement
  val encode_soft_type: soft_type -> term
 
  (* the semantic proposition associated with a typing judgement *)
  val prop_of_judgement: judgement -> term
  val judgement_of_prop: term -> judgement

  (* cf. analogous operations that we already have on terms ( Term.* ) *)
  val subst_bound: term -> soft_type -> soft_type
  val abstract_over: term -> soft_type -> soft_type
  val subst_STVars: (indexname * soft_type) list -> soft_type -> soft_type

end;

structure Soft_Type : SOFT_TYPE =
struct

val typeT = @{typ "type"};

datatype soft_type =
  Set of term  
| Pi of bool * string * typ * soft_type * soft_type
| STVar of indexname;

datatype judgement =
  Judgement of term * soft_type;

fun read_soft_type tm =
  case tm of 
    Const (@{const_name "set"}, _) $ set => 
      Set set
  | Const (@{const_name "Pi_type"}, _) $ A $ Abs (x, ty, B) =>
      Pi (false, x, ty, read_soft_type A, read_soft_type B)
  | Const (@{const_name "Implicit_Pi_type"}, _) $ A $ Abs (x, ty, B) =>
      Pi (true, x, ty, read_soft_type A, read_soft_type B)
  | Var (idxn, _) =>
      STVar idxn
  | _ => error ("Invalid soft type: " ^ Syntax.string_of_term @{context} tm);

fun read_judgement tm = 
  case tm of 
    Const (@{const_name "has_type"}, _) $ t $ ty => Judgement (t, read_soft_type ty)
  | _ => error ("Invalid judgement: " ^ Syntax.string_of_term @{context} tm);

fun is_judgement tm = 
  case tm of 
    Const (@{const_name "has_type"}, _) $ _ $ _ => true
  | _ => false


val set_const = @{term "set"};
fun Pi_const i T = 
  Const (if i then @{const_name "Implicit_Pi_type"} else @{const_name "Pi_type"},
    typeT --> (T --> typeT) --> typeT);

fun encode_soft_type st =
  case st of 
    Set t => set_const $ t
  | Pi (i, x, T, stA, stB) =>
      Pi_const i T $ encode_soft_type stA $ Abs (x, T, encode_soft_type stB)
  | STVar idxn => Var (idxn, typeT);


fun incr_boundvars i st =
  case st of 
    Set A => Set (Term.incr_boundvars i A)
  | Pi (b, x, ty, A, B) => Pi (b, x, ty, incr_boundvars i A, incr_boundvars i B)
  | st as _ => st


fun prop_of_judgement (Judgement (t, tau)) = 
  case tau of 
    Set A => 
      ZF_Logic.Trueprop $ ZF_Logic.mk_mem t A
  | Pi (_, x, ty, A, B) => 
      Logic.all_const ty $ 
        Abs (x, ty, Logic.mk_implies (
          prop_of_judgement (Judgement (Bound 0, incr_boundvars 1 A)), 
          prop_of_judgement (Judgement (Term.incr_boundvars 1 t $ Bound 0, B))))
  | STVar _ => error ("Illegal unification variable.");


fun decr_bounds t = 
  if (Term.is_dependent t) then error "is_dependent" 
  else Term.subst_bound (Bound 0, t)

fun decr_bounds_st st =
  case st of
    Set A => Set (decr_bounds A)
  | Pi (b, x, T, A, B) => Pi (b, x, T, decr_bounds_st A, decr_bounds_st B)
  | st as _ => st

(* The inverse of prop_of_judgement. 

This function requires its input to be precisely in the form produced by prop_of_judgement.
Equivalent forms, such as hhf normal form are not converted correctly.
*)
fun judgement_of_prop t =
  case t of
    Const (@{const_name "Pure.all"}, _) $ 
      Abs (v, T, Const (@{const_name "Pure.imp"}, _) $ u $ s) =>
        let
          val Judgement (x, A) = judgement_of_prop u
          val Judgement (fx, Bx) = judgement_of_prop s
        in 
          case fx of
            f $ x1 => 
              if x aconv x1 
              then Judgement (decr_bounds f, Pi (false, v, T, decr_bounds_st A, Bx))
              else error ("Bad prop: " ^ @{make_string} (fx, x, Bx))
          | _ => error "Bad prop 2"
        end
  | Const (@{const_name "Trueprop"}, _) $ (Const (@{const_name "mem"}, _) $ x $ A) =>
       Judgement (x, Set A)



fun subst_bound arg sty =
  let 
    (* stolen from Term.subst_bound *)
    fun subst (Bound i, lev) =
          if i < lev then raise Same.SAME   (*var is locally bound*)
          else if i = lev then Term.incr_boundvars lev arg
          else Bound (i - 1)   (*loose: change it*)
      | subst (Abs (a, T, body), lev) = Abs (a, T, subst (body, lev + 1))
      | subst (f $ t, lev) =
          (subst (f, lev) $ (subst (t, lev) handle Same.SAME => t)
            handle Same.SAME => f $ subst (t, lev))
      | subst _ = raise Same.SAME;

    fun subst_sT lev (Set t) = Set (subst (t, lev)) 
      | subst_sT lev (Pi (imp, n, ty, sTA, sTB)) = 
          (Pi (imp, n, ty, subst_sT lev sTA handle Same.SAME => sTA, subst_sT (lev + 1) sTB)
           handle Same.SAME => (Pi (imp, n, ty, subst_sT lev sTA, sTB)))
      | subst_sT _ (STVar _) = raise Same.SAME;
    in
      subst_sT 0 sty handle Same.SAME => sty
    end;

fun abstract_over v st =
  let
    fun abs lev tm =
      if v aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (lev + 1) t)
        | t $ u =>
            (abs lev t $ (abs lev u handle Same.SAME => u)
              handle Same.SAME => t $ abs lev u)
        | _ => raise Same.SAME);
    fun abs_st lev st =
      case st of
          Set t => Set (abs lev t)
        | Pi (i, x, T, stA, stB) => 
           let 
             val stA1 = (abs_st lev stA handle Same.SAME => stA)
           in
             Pi (i, x, T, stA1, abs_st (lev + 1) stB)
               handle Same.SAME => Pi (i, x, T, abs_st lev stA, stB)
           end
        | STVar _ => raise Same.SAME

  in abs_st 0 st handle Same.SAME => st end;


fun subst_STVars [] st = st
  | subst_STVars inst st = 
      let
        fun subst (v as STVar xi) = the_default v (AList.lookup (op =) inst xi)
          | subst (Pi (i, x, T, stA, stB)) = Pi (i, x, T, subst stA, subst stB)
          | subst st = st;
      in subst st end;   




(* Antiquotation: Soft types as ML values *)

fun ml_print_boolean b = if b then "true" else "false";

fun ml_print_soft_type (Set t) = "Soft_Type.Set " ^ ML_Syntax.atomic (ML_Syntax.print_term t)
  | ml_print_soft_type (Pi (i, x, T, stA, stB)) = "Soft_Type.Pi (" ^ 
      commas [
        ml_print_boolean i,
        ML_Syntax.print_string x,
        ML_Syntax.print_typ T,
        ml_print_soft_type stA,
        ml_print_soft_type stB
      ] ^ ")"
  | ml_print_soft_type (STVar idxn) = "Soft_Type.STVar " ^ ML_Syntax.print_indexname idxn;
  

val _ = Theory.setup (ML_Antiquotation.inline @{binding soft_type} 
  (Args.term >> (ML_Syntax.atomic o ml_print_soft_type o read_soft_type)));



(* Input check phase that replaces a typing judgement by the corresponding proposition.
   Thus, typing judgements can be used to state properties. *)
fun replace_judgement t = 
  if is_judgement t then prop_of_judgement (read_judgement t)
  else case t of
    s $ u => replace_judgement s $ replace_judgement u
  | Abs (x, T, b) => Abs (x, T, replace_judgement b)
  | t => t;

val _ = Context.>> (Syntax_Phases.term_check 3 "soft_type_expand" (K (map replace_judgement)));


end
