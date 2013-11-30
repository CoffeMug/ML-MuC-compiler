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

    fun withSource(source, f) =
      f()
      handle (exn as AbsynCheckError(msgs)) =>
	(List.app (Absyn.Source.sayMsg source) msgs;
	 raise exn)

    fun error1 msg = raise AbsynCheckError[msg]

    fun error2(msg1, msg2) = raise AbsynCheckError[msg1, msg2]

    fun mkIdErrorMsg(msg, Absyn.IDENT(name, left, right)) =
      ("Error: "^msg^name, left, right)
    fun idError(msg, id) = error1(mkIdErrorMsg(msg, id))

    fun doError(msg, left, right) = error1("Error: "^msg, left, right)
    fun expError(msg, Absyn.EXP(_,left,right)) = doError(msg, left, right)
    fun stmtError(msg, Absyn.STMT(_,left,right)) = doError(msg, left, right)

    (*
     * YOUR CODE HERE
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


	(* XXX: REPLACE WITH YOUR CODE *)

	(* environment *)
	structure Env = Absyn.IdentDict


    (* Representation of types for UC language *)
	datatype ty = 
		Int
	  | Char  
	  | Void 
	  | IntArr of int 
	  | CharArr of int
	  | IntFunc of int list
	  | CharFunc of char list
	  | VoidFunc of int 
	  | Error 
	  | Ok
	
		
	(* Checking the global variables *)
	fun checkGlobal (t,dec) env =
		case dec of 
			Absyn.VARdecl(id) =>   
  				 (case Env.find(env,id) of 
					 SOME Int => (print("Variable name is in use!\n");env)
					|SOME Char => (print("Variable name is in use!\n");env)
   				    |NONE   => case t of 
							  Absyn.INTty  => (Env.insert (env,id,Int))
							| Absyn.CHARty => (Env.insert (env,id,Char))
						    | Absyn.VOIDty => (Env.insert (env,id,Void)))

			| Absyn.ARRdecl(id,SOME i) =>
	  	 		(case Env.find(env,id) of 
					SOME _ => (print("Array name is in use!\n");env) 
   				   |NONE   => case t of 
					  		  Absyn.INTty  => (Env.insert (env,id,IntArr(i)))
							| Absyn.CHARty => (Env.insert (env,id,CharArr(i)))
							| Absyn.VOIDty => (print("Array type is incompatibel\n");env))


			| Absyn.ARRdecl(id,NONE) =>
	  	 		(case Env.find(env,id) of 
					SOME _ => (print("Array name is in use!\n");env) 
   				   |NONE   => case t of 
					  		  Absyn.INTty  => (Env.insert (env,id,IntArr(0)))
							| Absyn.CHARty => (Env.insert (env,id,CharArr(0)))
							| Absyn.VOIDty => (print("Array type is incompatibel\n");env))

						   
	(*************************************)	
						
	(*fun checkExtern dec = let *)


	(* Checking functions *)
	fun checkFunction (name,forms,ret,env) = 
		(case Env.find'(env,name) of 
			 SOME (_,IntFunc(_)) => (print("function has already defined!\n");env) 
			|SOME (_,CharFunc(_)) => (print("function has already defined!\n");env)
			|SOME (_,VoidFunc(_)) => (print("function has already defined!\n");env) 
   		    |NONE   => case ret of 
						   	  Absyn.INTty  => (Env.insert (env,name,IntFunc(List.length(forms))))
							| Absyn.CHARty => (Env.insert (env,name,CharFunc(List.length(forms))))
						    | Absyn.VOIDty => (Env.insert (env,name,VoidFunc(List.length(forms)))))


	fun process_declarations ([],env) = env
	| process_declarations ((dec::decs),env) =
		
			case dec of 

			Absyn.VARDEC(Absyn.INTty,Absyn.VARdecl(id)) =>   
  				 (case Env.find(env,id) of 
					 SOME _ => (print("Variable name is in use!\n");process_declarations(decs,env)) 
   				    |NONE   => (process_declarations(decs,Env.insert (env,id,Int))))

			| Absyn.VARDEC(Absyn.CHARty,Absyn.VARdecl(id)) =>   
  				 (case Env.find(env,id) of 
					 SOME _ => (print("Variable name is in use!\n");process_declarations(decs,env)) 
   				    |NONE   => (process_declarations(decs,Env.insert (env,id,Char))))

			| Absyn.VARDEC(Absyn.VOIDty,Absyn.VARdecl(id)) =>   
  				 (case Env.find(env,id) of 
					 SOME _ => (print("Variable name is in use!\n");process_declarations(decs,env)) 
   				    |NONE   => (process_declarations(decs,Env.insert (env,id,Void))))

			| Absyn.VARDEC(Absyn.INTty,Absyn.ARRdecl(id,SOME i)) =>
	  	 		(case Env.find(env,id) of 
					SOME _ => (print("Array name is in use!\n");process_declarations(decs,env)) 
   				   |NONE   => (process_declarations(decs,Env.insert (env,id,IntArr(i)))))

			| Absyn.VARDEC(Absyn.CHARty,Absyn.ARRdecl(id,SOME i)) =>
	  	 		(case Env.find(env,id) of 
					SOME _ => (print("Array name is in use!\n");process_declarations(decs,env)) 
   				   |NONE   => (process_declarations(decs,Env.insert (env,id,CharArr(i)))))


			| Absyn.VARDEC(Absyn.VOIDty,Absyn.ARRdecl(id,SOME i)) =>
	  	 		(case Env.find(env,id) of 
					 _ => (print("Array must be of type int or char!\n");process_declarations(decs,env))) 


			| Absyn.VARDEC(Absyn.INTty,Absyn.ARRdecl(id,NONE)) =>
	  	 		(case Env.find(env,id) of 
					SOME _ => (print("Array name is in use!\n");process_declarations(decs,env)) 
   				   |NONE   => (process_declarations(decs,Env.insert (env,id,IntArr(0)))))

			| Absyn.VARDEC(Absyn.CHARty,Absyn.ARRdecl(id,NONE)) =>
	  	 		(case Env.find(env,id) of 
					SOME _ => (print("Array name is in use!\n");process_declarations(decs,env)) 
   				   |NONE   => (process_declarations(decs,Env.insert (env,id,CharArr(0)))))


			| Absyn.VARDEC(Absyn.VOIDty,Absyn.ARRdecl(id,NONE)) =>
	  	 		(case Env.find(env,id) of 
					 _ => (print("Array must be of type int or char!\n");process_declarations(decs,env))) 
   				  
		   


	fun isConvertible (e1Ty,e2Ty) = 
		
			case e1Ty of Int => (case e2Ty of Char => true 
								 		| Int => true
									    | IntFunc(_)   => true
										| CharFunc(_)  => true
										| _		    => false)
					| Char => 			(case e2Ty of Char => true 
								 		| Int => true
									    | IntFunc(_)   => true
										| CharFunc(_)  => true
										| _		    => false)


					| IntArr(_) => (case e2Ty of CharArr(_) => false 
								 		| IntArr(_) => true
									    | Int  => true
										| Char => true
								   		| _  => false)
					
					| CharArr(_) => (case e2Ty of CharArr(_) => true 
								 		| IntArr(_) => true
									    | Int  => true
										| Char => true
										| _   => false)
					| _ => false




	fun checkExp (ex,envLoc,envGlob) = 

		case ex of Absyn.EXP(Absyn.CONST(Absyn.INTcon (i)),_,_) => Int

				  |Absyn.EXP(Absyn.VAR(id),_,_) => (case Env.find'(envLoc,id) of SOME (_,t) => t 
																			   | NONE => (case Env.find'(envGlob,id) of SOME(_,t) => t 
																													  | NONE => (print("variable is not defined.\n");Error)))

				  |Absyn.EXP(Absyn.ARRAY(id,exp),_,_) => (case Env.find'(envLoc,id) of SOME (_,t) => checkExp(exp,envLoc,envGlob) 
																				  | NONE => (case Env.find'(envGlob,id) of SOME(_,t) => checkExp(exp,envLoc,envGlob)
																														 | NONE => (print("array is not defined\n");Error)))

				  |Absyn.EXP(Absyn.ASSIGN(exp1,exp2),_,_) => 
				   			let val lht = checkExp(exp1,envLoc,envGlob)
								val	rht = checkExp(exp2,envLoc,envGlob)
							in 
				        	if (isLvalue exp1) then    
											(if isConvertible(lht,rht) then Ok else (print("right hand side and left hand side of assign are not convertibel!\n");Error))  
							else (print("Left hand side of assignment is not a l-value!\n");Error)
							end

				  |Absyn.EXP(Absyn.UNARY(_,exp),_,_) => (case checkExp(exp,envLoc,envGlob) of Int => Ok
																				    | Char => Ok
																					| _    => (print("unary operator is not applicable.\n");Error))

				  |Absyn.EXP(Absyn.BINARY(_,ex1,ex2),_,_) => (case checkExp(ex1,envLoc,envGlob) of Int =>
																					   (case checkExp(ex2,envLoc,envGlob) of Int => Int
																	                      | Char => Char
																						  | _   => (print("RHS of binary operator is not applicable.\n");Error))
																						| Char =>
																						  (case checkExp(ex2,envLoc,envGlob) of Int => Int
																	                      | Char => Char
																						  | _   => (print("RHS of binary operator is not applicable.\n");Error))

																						| _ => (print("LHS of binary operator is not applicable.\n");Error))
			  
				  |Absyn.EXP(Absyn.FCALL(id,exlist),_,_) => (case Env.find'(envGlob,id) of SOME (_,IntFunc(t)) => 
																					  if t <> (List.length(exlist)) then (print("number of arguments must match.\n");Error) else Int
															                        | SOME (_,CharFunc(t)) => 
																					  if t <> (List.length(exlist)) then (print("number of arguments must match.\n");Error) else Char

																					| SOME (_,VoidFunc(t)) => 
																					  if t <> (List.length(exlist)) then (print("number of arguments must match.\n");Error) else Ok

																					| _ => (print("the function is not defined.\n");Error))
	
	and isLvalue exp = 
		case exp of Absyn.EXP(Absyn.VAR(_),_,_) => true 
					| Absyn.EXP(Absyn.ARRAY(_,_),_,_) => true
					| _ => false
	


	fun analyzeBody (name,ret,body,envLoc,envGlob) =
		case body of 
   			  Absyn.STMT(Absyn.EMPTY,_,_) => envGlob

			| Absyn.STMT(Absyn.EFFECT(exp),_,_) => (checkExp (exp,envLoc,envGlob);envGlob)

			| Absyn.STMT(Absyn.IF(exp,stmt,st),_,_) => (checkExp(exp,envLoc,envGlob);analyzeBody(name,ret,stmt,envLoc,envGlob);analyzeBody(name,ret,valOf(st),envLoc,envGlob);envGlob)

			| Absyn.STMT(Absyn.WHILE(exp,stmt),_,_) => (checkExp(exp,envLoc,envGlob);analyzeBody(name,ret,stmt,envLoc,envGlob);envGlob)

			| Absyn.STMT(Absyn.SEQ(st1,st2),_,_) => (analyzeBody(name,ret,st1,envLoc,envGlob);analyzeBody(name,ret,st2,envLoc,envGlob);envGlob)

			| Absyn.STMT(Absyn.RETURN(SOME exp),_,_) => let val retTy = checkExp(exp,envLoc,envGlob) in
			  										   														
																(case ret of Absyn.INTty => if (retTy = Int) then envGlob else (print("function must return integer.\n");envGlob)
																			| Absyn.CHARty => if (retTy = Char) then envGlob else (print("function must return character.\n");envGlob)
			  	                                                            | Absyn.VOIDty => (print("function cannot return a value.\n");envGlob))
														end		

			| Absyn.STMT(Absyn.RETURN(NONE),_,_) => (case ret of Absyn.VOIDty => envGlob 
																| Absyn.INTty    => (print("function must return integer.\n");envGlob)
																| Absyn.CHARty   => (print("function must return character.\n");envGlob))
   												



	fun analyzeFunc (name,form,ret,loc,body,env) =
		let val locForm = (form@loc)
			val envGlob = checkFunction (name,form,ret,env)
		    val envFunc = Env.empty
		    val envLoc = process_declarations (locForm,envFunc)
			(*val env2 = Env.plus (env1,env')*)
		in 
			analyzeBody(name,ret,body,envLoc,envGlob)
		end




	fun checkExtern (name,formals,retTy,env) = checkFunction (name,formals,retTy,env)
		


	(***********************************************************************)



	fun checkDeck (env,dec) =
		case dec of 
			  Absyn.GLOBAL(Absyn.VARDEC(t,d))  => checkGlobal (t,d) env
		    | Absyn.FUNC{name,formals,retTy,locals,body} => analyzeFunc (name,formals,retTy,locals,body,env)
			| Absyn.EXTERN{name,formals,retTy} 	=> checkExtern (name,formals,retTy,env)






	(* Auxiliary function to traverse the list of declarations *)
	fun checkDeclarations' [] _ = ()
		| checkDeclarations' (dec::decs) env = 
			let val env' = checkDeck (env,dec)
			in 
				checkDeclarations' decs env'
			end


	(* initial empty environment *)
    val en = Env.empty 

    fun checkDeclarations decs  = checkDeclarations' decs en

    (* Programs *)

    fun program(Absyn.PROGRAM{decs,source}) =
      let fun check() = checkDeclarations decs 
      in
		withSource(source, check)
      end

  end (* functor AbsynCheckFn *)
