(* absyn/absyn-check.sml *)

signature ABSYN_CHECK =
  sig
    structure Absyn: ABSYN
    val program: Absyn.program -> unit
  end (* signature ABSYN_CHECK *)

functor AbsynCheckFn(Absyn : ABSYN) : ABSYN_CHECK =
struct

  structure Absyn = Absyn

  (*
   * Reporting errors.
   *
   * Source file context is not easily available everywhere, so
   * a detected error is instead thrown as an exception.
   * At the top level where we do have the source file context,
   * we catch this exception and generate appropriate messages
   * before re-throwing the exception.
   * Limitation: We can't continue after an error. Big deal.
   *)

  type msg = string * int * int (* same as what Absyn.Source.sayMsg wants *)
  exception AbsynCheckError of msg list

  fun with_source source f =
    f()
    handle (exn as AbsynCheckError(msgs)) =>
      (List.app (Absyn.Source.sayMsg source) msgs;
        raise exn)

  fun error1 msg = raise AbsynCheckError[msg]
  fun error2 msg1 msg2 = raise AbsynCheckError[msg1, msg2]

  fun mk_id_err_msg (msg, (Absyn.IDENT(name, left, right))) =
    ("Error: "^msg^name, left, right)
  fun do_err (msg, left, right) = error1("Error: "^msg, left, right)
  fun id_err msg id = error1(mk_id_err_msg(msg, id))
  fun exp_err msg (Absyn.EXP(_, left, right)) = do_err (msg, left, right)
  fun stmt_err msg (Absyn.STMT(_, left, right)) = do_err (msg, left, right)

  (*
   *
   * Hints:
   * - You need to represent uC types.
   * - You need an environment/symbol-table for identifiers.
   * - You need recursive functions over expressions and statements.
   * - You need to check type constraints at various places.
   * - Abstract syntax 'declarators' aren't types. You'll need
   *   to translate them.
   * - You need to process top-level declarations.
   *)

   (* environment *)
   structure Env = Absyn.IdentDict

   (* Representation of types for UC language *)
   datatype ty = Int
     | Char  
     | Void 
     | IntArr of int 
     | CharArr of int
     | IntFunc of ty list
     | CharFunc of ty list
     | VoidFunc of ty list 
     | Error 
     | Ok
        
   (* Checking the global variables *)

   fun check_globals t (Absyn.VARdecl(id)) env =
       (case Env.find(env, id) of 
           SOME Int => (id_err "Identifier name is in use: " id; env)
         | SOME Char => (id_err "Identifier name is in use: " id; env)
         | _   => case t of 
                     Absyn.INTty  => (Env.insert (env, id, Int))
                   | Absyn.CHARty => (Env.insert (env, id, Char))
                   | Absyn.VOIDty => (Env.insert (env, id, Void)))

     | check_globals t (Absyn.ARRdecl(id, SOME i)) env =
       (case Env.find(env, id) of 
           SOME _ => (id_err "Identifier name is in use: " id; env)
         | _      => case t of 
                      Absyn.INTty  => (Env.insert (env, id, IntArr(i)))
                    | Absyn.CHARty => (Env.insert (env, id, CharArr(i)))
                    | Absyn.VOIDty => (id_err "Identifier name is in use: " id; env))

     | check_globals t (Absyn.ARRdecl(id, NONE)) env =
           (case Env.find(env, id) of 
              SOME _ => (id_err "Identifier name is in use: " id; env)
            | _   => case t of 
                       Absyn.INTty  => (Env.insert (env, id, IntArr(0)))
                     | Absyn.CHARty => (Env.insert (env, id, CharArr(0)))
                     | Absyn.VOIDty => (print("Array type is incompatibel!\n"); env))

   fun check_function name forms ret env = 
     (case Env.find(env, name) of 
        SOME (_) => (id_err "Identifier name is in use: " name; env) 
      | _   => case ret of 
                 Absyn.INTty  => (Env.insert (env, name, IntFunc(makeFormList(forms))))
               | Absyn.CHARty => (Env.insert (env, name, CharFunc(makeFormList(forms))))
               | Absyn.VOIDty => (Env.insert (env, name, VoidFunc(makeFormList(forms)))))

   and makeFormList [] = []
     | makeFormList (Absyn.VARDEC(Absyn.INTty, v)::fs) = 
         (case v of 
               Absyn.VARdecl(_) => (Int::(makeFormList fs))
             | Absyn.ARRdecl(_,SOME i) => (IntArr(i)::(makeFormList fs))
             | Absyn.ARRdecl(_,NONE) => (IntArr(0)::(makeFormList fs)))
     | makeFormList (Absyn.VARDEC(Absyn.CHARty, v)::fs) = 
         (case v of 
               Absyn.VARdecl(_) => (Char::(makeFormList fs))
             | Absyn.ARRdecl(_,SOME i) => (CharArr(i)::(makeFormList fs))
             | Absyn.ARRdecl(_,NONE) => (CharArr(0)::(makeFormList fs)))
     | makeFormList (Absyn.VARDEC(Absyn.VOIDty, _)::fs) = makeFormList fs

   fun process_declarations [] env = env
     | process_declarations (Absyn.VARDEC(Absyn.INTty,Absyn.VARdecl(id))::decs) env =
          (case Env.find(env, id) of 
             SOME _ => (id_err "Identifier name is in use: " id; process_declarations decs env) 
           | NONE   => process_declarations decs (Env.insert(env, id, Int)))
     | process_declarations (Absyn.VARDEC(Absyn.CHARty,Absyn.VARdecl(id))::decs) env =   
          (case Env.find(env, id) of 
             SOME _ => (id_err "Identifier name is in use: " id; process_declarations decs env) 
           | NONE   => process_declarations decs (Env.insert(env, id, Char)))
     | process_declarations(Absyn.VARDEC(Absyn.VOIDty,Absyn.VARdecl(id))::decs) env =   
          (case Env.find(env, id) of 
             SOME _ => (id_err "Identifier name is in use: " id; process_declarations decs env) 
           | NONE   => process_declarations decs (Env.insert(env, id, Void)))
     | process_declarations(Absyn.VARDEC(Absyn.INTty,Absyn.ARRdecl(id, SOME i))::decs) env =
          (case Env.find(env, id) of 
             SOME _ => (id_err "Identifier name is in use: " id; process_declarations decs env) 
           | NONE   => process_declarations decs (Env.insert(env, id, IntArr(i))))
     | process_declarations (Absyn.VARDEC(Absyn.CHARty, Absyn.ARRdecl(id, SOME i))::decs) env =
          (case Env.find(env, id) of 
             SOME _ => (id_err "Identifier name is in use: " id; process_declarations decs env) 
           | NONE   => process_declarations decs (Env.insert(env, id, CharArr(i))))
     | process_declarations (Absyn.VARDEC(Absyn.VOIDty, Absyn.ARRdecl(id, SOME i))::decs) env =
          (print("Array must be of type int or char!\n"); process_declarations decs env)  
     | process_declarations (Absyn.VARDEC(Absyn.INTty,Absyn.ARRdecl(id, NONE))::decs) env =
          (case Env.find(env,id) of 
             SOME _ => (print("Array name is in use!\n"); process_declarations decs env) 
           | NONE   => process_declarations decs (Env.insert(env, id, IntArr(0))))
     | process_declarations (Absyn.VARDEC(Absyn.CHARty, Absyn.ARRdecl(id, NONE))::decs) env =
          (case Env.find(env,id) of 
             SOME _ => (print("Array name is in use!\n"); process_declarations decs env) 
           | NONE   => process_declarations decs (Env.insert(env, id, CharArr(0))))
     | process_declarations (Absyn.VARDEC(Absyn.VOIDty, Absyn.ARRdecl(id, NONE))::decs) env =
          (print("Array must be of type int or char!\n"); process_declarations decs env) 
                                  
   (* type checker module *)

   fun check_expression (Absyn.EXP(Absyn.CONST(Absyn.INTcon(i)), _, _)) _ = Int
     | check_expression (Absyn.EXP(Absyn.VAR(id), left, right)) env = 
         (case Env.find'(env, id) of 
            SOME (_, t) => t 
          | NONE => (exp_err "Identifier not defined" (Absyn.EXP(Absyn.VAR(id), left, right)); Error))
     | check_expression (Absyn.EXP(Absyn.ARRAY(id, exp), left, right)) env = 
         (case Env.find'(env, id) of 
            SOME (_, IntArr(_)) => check_expression exp env
          | SOME (_, CharArr(_)) => check_expression exp env
          | SOME (_, Int)  => (exp_err "Indexing integer:" (Absyn.EXP(Absyn.ARRAY(id, exp), left, right)); Error)
          | SOME (_, Char) => (exp_err "Indexing character:" (Absyn.EXP(Absyn.ARRAY(id, exp), left, right)); Error)
          | _  => (exp_err "Undefined Array: " (Absyn.EXP(Absyn.ARRAY(id, exp), left, right)); Error))

     | check_expression (Absyn.EXP(Absyn.ASSIGN(exp1, exp2), left, right)) env = 
         let 
           val lht = check_expression exp1 env
           val rht = check_expression exp2 env
         in 
           if not (is_left_value lht exp1) then 
             (exp_err "Left hand side of assignment is not a l-value" (Absyn.EXP(Absyn.ASSIGN(exp1, exp2), left, right)); Error)
           else if not (are_compatible lht rht) then 
             (exp_err "Right hand side and left hand side of assign are not convertibel"
              (Absyn.EXP(Absyn.ASSIGN(exp1,exp2),left,right)); Error)  
           else rht 
         end
    | check_expression (Absyn.EXP(Absyn.UNARY(uo, exp), left, right)) env = 
        (case check_expression exp env of 
           Int => Int
         | Char => Char
         | _    => (exp_err "unary operator is not applicable"
                   (Absyn.EXP(Absyn.UNARY(uo, exp), left, right)); Error))
    | check_expression (Absyn.EXP(Absyn.BINARY(bo, ex1, ex2), left, right)) env = 
        (case check_expression ex1 env of 
           Int => (case check_expression ex2 env of 
                     Int => Int
                   | Char => Char
                   | _   => (exp_err "RHS of binary operator is not applicable"
                            (Absyn.EXP(Absyn.BINARY(bo, ex1, ex2), left, right)); Error))
         | Char => (case check_expression ex2 env of 
                      Int => Int
                    | Char => Char
                    | _   => (exp_err "RHS of binary operator is not applicable"
                             (Absyn.EXP(Absyn.BINARY(bo, ex1, ex2), left, right)); Error))
         | _ => (exp_err "LHS of binary operator is not applicable"
                (Absyn.EXP(Absyn.BINARY(bo, ex1, ex2), left, right)); Error))
    | check_expression (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)) env = 
        (case Env.find'(env, id) of 
           SOME (_, IntFunc(t)) => 
             if List.length(t) > (List.length(exlist)) then 
               (exp_err "Too few arguments to function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error) 
             else if List.length(t) < (List.length(exlist)) then 
               (exp_err "Too many arguments to function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error) 
             else if match_arguments exlist t env then Int 
             else (exp_err "Unexpected argument type to the function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error)
         | SOME (_, CharFunc(t)) => 
             if List.length(t) > (List.length(exlist)) then 
               (exp_err "Too few arguments to function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error) 
             else if List.length(t) < (List.length(exlist)) then 
               (exp_err "Too many arguments to function: " (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error) 
             else if match_arguments exlist t env then Char 
             else (exp_err "Unexpected argument type to the function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error)
         (* fix this *)
         | SOME (_, VoidFunc(t)) => 
             if List.length(t) > (List.length(exlist)) then 
               (exp_err "Too few arguments to function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error) 
             else if List.length(t) < (List.length(exlist)) then 
               (exp_err "Too many arguments to function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error) 
             else if match_arguments exlist t env then Void 
             else (exp_err "Unexpected argument type to the function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error) 
         | _ => (exp_err "Is not a function" (Absyn.EXP(Absyn.FCALL(id, exlist), left, right)); Error))
   and is_left_value (Int) exp = check_var exp   
     | is_left_value (Char) exp  = check_var exp   
     | is_left_value (IntArr(_)) exp  = check_array exp
     | is_left_value (CharArr(_)) exp = check_array exp
     | is_left_value _ exp = false
   and check_array (Absyn.EXP(Absyn.VAR(_), _, _)) = false 
     | check_array (Absyn.EXP(Absyn.ARRAY(_, _), _, _)) = true
     | check_array (Absyn.EXP(Absyn.CONST(Absyn.INTcon(_)), _, _)) = false
     | check_array _ = false
   and check_var (Absyn.EXP(Absyn.VAR(_), _, _)) = true 
     | check_var (Absyn.EXP(Absyn.ARRAY(_, _), _, _)) = true
     | check_var (Absyn.EXP(Absyn.CONST(Absyn.INTcon (_)), _, _)) = false
     | check_var _ = false
   and are_compatible (Int) (Char) = true
     | are_compatible (Int) (Int)  = true  
     | are_compatible (Int) (IntFunc(_))  = true  
     | are_compatible (Int) (CharFunc(_))  = true  
     | are_compatible (Int) _  = false  
     | are_compatible (Char) (Char) = true
     | are_compatible (Char) (Int) = true
     | are_compatible (Char) (IntFunc(_)) = true
     | are_compatible (Char) (CharFunc(_)) = true
     | are_compatible (Char) _ = false
     | are_compatible (IntArr(_)) (IntArr(_)) = true
     | are_compatible (IntArr(_)) (CharArr(_)) = true
     | are_compatible (IntArr(_)) _ = false
     | are_compatible (CharArr(_)) (CharArr(_)) = true
     | are_compatible (CharArr(_)) (IntArr(_)) = false
     | are_compatible (CharArr(_)) _ = false
     | are_compatible _ _ = false
   and match_arguments [] _ env = true 
     | match_arguments _ [] env = true
     | match_arguments (r::rs) (f::fs) env = 
         let 
           val rt =  check_expression r env
         in 
           if are_compatible rt f then match_arguments rs fs env else false
         end

   fun analyze_body name ret body env =
     case body of 
       Absyn.STMT(Absyn.EMPTY, _, _) => env
     | Absyn.STMT(Absyn.EFFECT(exp), _, _) => (check_expression exp env; env)
     | Absyn.STMT(Absyn.IF(exp, stmt, SOME st), _, _) => 
          (check_expression exp env; analyze_body name ret stmt env; analyze_body name ret st env; env)
     | Absyn.STMT(Absyn.IF(exp, stmt, NONE), _, _) => 
          (check_expression exp env; analyze_body name ret stmt env; env)
     | Absyn.STMT(Absyn.WHILE(exp, stmt), _, _) => 
          (check_expression exp env; analyze_body name ret stmt env; env)
     | Absyn.STMT(Absyn.SEQ(st1, st2), _, _) => 
          (analyze_body name ret st1 env; analyze_body name ret st2 env; env)
     | Absyn.STMT(Absyn.RETURN(SOME exp), left, right) => 
         let val retTy = check_expression exp env 
         in
           (case ret of 
              Absyn.VOIDty => (stmt_err "function cannot return a value"
                              (Absyn.STMT(Absyn.RETURN(SOME exp), left, right)); env)
            | _            => env)
         end             
     | Absyn.STMT(Absyn.RETURN(NONE), left, right) => 
         (case ret of 
            Absyn.VOIDty => env 
          | Absyn.INTty  => (stmt_err "function must return integer"
                            (Absyn.STMT(Absyn.RETURN(NONE), left, right)); env)
          | Absyn.CHARty => (stmt_err "function must return character"
                            (Absyn.STMT(Absyn.RETURN(NONE), left, right)); env))
   fun analyze_function name form ret loc body env =
     let 
       val locForm = (form@loc)
       val envGlob = check_function name form ret env
       val envFunc = Env.empty
       val envLoc = process_declarations locForm envFunc
       val env2 = Env.plus (envGlob, envLoc)
     in 
       (analyze_body name ret body env2; envGlob)
     end
   fun check_external name formals retTy env = check_function name formals retTy env

   (***********************************************************************)
   fun check_declaration env dec =
     case dec of 
       Absyn.GLOBAL(Absyn.VARDEC(t, d))  => check_globals t d env
     | Absyn.FUNC{name,formals,retTy,locals,body} => 
          analyze_function name formals retTy locals body env
     | Absyn.EXTERN{name,formals,retTy} => 
          check_external name formals retTy env

   (* Auxiliary function to traverse the list of declarations *)
   fun check_declarations' [] _ = ()
     | check_declarations' (dec::decs) env = 
         let val env' = check_declaration env dec
         in 
           check_declarations' decs env'
         end

   (* initial empty environment *)
   val en = Env.empty 

   fun check_declarations decs = check_declarations' decs en

   (* Programs *)
   fun program(Absyn.PROGRAM{decs,source}) =
     let fun check() = check_declarations decs 
     in
       with_source source check
     end

end (* functor AbsynCheckFn *)
