(* rtl/absyn-to-rtl.sml *)

signature ABSYN_TO_RTL =
  sig
    structure Absyn : ABSYN
    structure RTL   : RTL
    val program     : Absyn.program -> RTL.program
  end (* signature ABSYN_TO_RTL *)

functor AbsynToRTLFn(structure Absyn : ABSYN structure RTL : RTL) : ABSYN_TO_RTL =
  struct

    structure Absyn = Absyn
    structure RTL = RTL

    structure Env = Absyn.IdentDict

    fun proc_label id = "P" ^ Absyn.identName id
    fun var_label id = "V" ^ Absyn.identName id
    fun arr_label id = "Arr" ^ Absyn.identName id


    exception AbsynToRTL
    fun bug msg =
      (TextIO.output(TextIO.stdErr, "Compiler error: "^msg^"\n");
       raise AbsynToRTL)

    (* REPLACE WITH YOUR CODE *)

    val sav = []    

    val TRUE = RTL.newTemp()
    val FALSE = RTL.newTemp()

    (* global or local *)
    val loc = 0 
    val glob = 1
    val arg  = 2
     
    fun program(Absyn.PROGRAM{decs = xs,...}) = RTL.PROGRAM(declar xs Env.empty sav) 

    and declar [] _ sav = rev sav
      | declar (y::ys) env sav = 
          case y of  
            Absyn.GLOBAL(Absyn.VARDEC(t,d)) => 
              let val (gRtl,gEnv) = global(t,d,env)
              in 
                declar ys gEnv (gRtl::sav)
              end
          | Absyn.FUNC{name = id,formals = forms,retTy = ty,locals = locs, body =fBody} => 
              let 
                val endOfFunLabel = RTL.newLabel()
                val (fRtl,fEnv) = func(id,forms,ty,locs,fBody,env,endOfFunLabel)
              in 
                declar ys fEnv (fRtl::sav)
              end 
          | Absyn.EXTERN {name,formals,retTy} => 
              let val env' = insert_function_name (Absyn.identName(name)) name retTy env
              in  declar ys env' sav
              end

    and global (t,d,en) =  
          case d of 
            Absyn.VARdecl(x) =>
               (if (t = Absyn.INTty) then 
                 let 
                   val ty = RTL.LONG
                   val nam = var_label x
                 in 
                   (RTL.DATA{label = nam, size = RTL.sizeof(RTL.LONG)},Env.insert(en,x,(glob,ty,(0,nam))))
                 end
                else 
                 let 
                   val ty = RTL.BYTE               
                   val nam= var_label x
                 in 
                   (RTL.DATA{label = nam,size = RTL.sizeof(RTL.BYTE)},Env.insert(en,x,(glob,ty,(0,nam))))
                 end)

          | Absyn.ARRdecl(x,SOME i) =>
               (if (t = Absyn.INTty) then  
                 let 
                   val ty = RTL.LONG
                   val nam = arr_label x
                 in 
                   (RTL.DATA{label = nam,size = RTL.sizeof(RTL.LONG)*i},Env.insert(en,x,(glob,ty,(0,nam))))
                 end
                else
                 let 
                   val ty = RTL.BYTE               
                   val nam= arr_label x
                 in 
                   (RTL.DATA{label = nam,size = RTL.sizeof(RTL.BYTE)*i},Env.insert(en,x,(glob,ty,(0,nam))))
                 end)

          | Absyn.ARRdecl(x,NONE) =>
               (if (t = Absyn.INTty) then
                 let 
                   val ty = RTL.LONG
                   val nam = arr_label x
                 in 
                   (RTL.DATA{label = nam,size = 0},Env.insert(en,x,(glob,ty,(0,nam))))
                 end
                else
                 let 
                   val ty = RTL.BYTE               
                   val nam= arr_label x
                 in 
                   (RTL.DATA{label = nam,size = 0},Env.insert(en,x,(glob,ty,(0,nam))))
                 end)

    and func (id,forms,ty,locs,fBody,en,eofLab) =
        let val nam = if (Absyn.identName(id)= "main") then Absyn.identName(id) else proc_label id 
            val (_,envFormals,rtlFormals) = transFormals(forms,en,RTL.FP-1)
            val (frameS,envLocals,rtlLocals) = transLocals (locs,envFormals,RTL.FP-1)
            val envF  = insert_function_name nam id ty envLocals    
            val (fInst,fTmp) = f_body_to_rtl (fBody,envF,ty,eofLab)
            val eofDef = RTL.LABDEF(eofLab)
            val inst = (fInst@[eofDef])
        in
            (RTL.PROC{label= nam, formals = rtlFormals ,locals = (rtlLocals @ fTmp) , 
                    frameSize = frameS , insns = inst},envF)
        end

    and transLocals ([],en,fp) = (fp,en,[])
      | transLocals (x::xs,en,fp) = 
        case x of 
          Absyn.VARDEC(t,Absyn.VARdecl(x)) =>
          let 
            val nam = RTL.newTemp()
          in 
            if (t = Absyn.INTty) then 
             let val (fp',en',xs') = transLocals(xs,Env.insert(en,x,(loc,RTL.LONG,(nam,"0"))),fp) 
             in 
               (fp',en',nam::xs')
             end
            else let val (fp',en',xs') = transLocals(xs,Env.insert(en,x,(loc,RTL.BYTE,(nam,"0"))),fp)
                 in 
                   (fp',en',nam::xs')
                 end
          end
        | Absyn.VARDEC(t,Absyn.ARRdecl(x,SOME i)) =>
          if (t = Absyn.INTty) then 
           let 
             val fp' = fp + (RTL.sizeof(RTL.LONG) * i)
             val (fp'',en',xs') = transLocals(xs,Env.insert(en,x,(loc,RTL.LONG,(fp,"1"))),fp') 
           in (fp'',en',xs')
           end
          else 
           let 
             val fp' = fp + (RTL.sizeof(RTL.BYTE) * i)
             val (fp'',en',xs') = transLocals(xs,Env.insert(en,x,(loc,RTL.BYTE,(fp,"1"))),fp') 
           in (fp'',en',xs')
           end
        | Absyn.VARDEC(t,Absyn.ARRdecl(x,NONE)) =>
          if (t = Absyn.INTty) then 
           let 
             val fp' = fp 
             val (fp'',en',xs')=transLocals(xs,Env.insert(en,x,(loc,RTL.LONG,(fp,"1"))),fp')
           in (fp'',en',xs')
           end
          else 
           let 
             val fp' = fp 
             val (fp'',en',xs')=  transLocals(xs,Env.insert(en,x,(loc,RTL.BYTE,(fp,"1"))),fp')
           in (fp'',en',xs')
           end

    and transFormals ([],en,fp) = (fp,en,[])
      | transFormals (x::xs,en,fp) = 
        case x of 
          Absyn.VARDEC(t,Absyn.VARdecl(x)) =>
          (let val nam = RTL.newTemp()
          in 
            if (t = Absyn.INTty) then 
             let val (fp',en',xs') = transFormals(xs,Env.insert(en,x,(loc,RTL.LONG,(nam,"0"))),fp) 
             in 
               (fp',en',nam::xs')
             end
            else let val (fp',en',xs') = transFormals(xs,Env.insert(en,x,(loc,RTL.BYTE,(nam,"0"))),fp)
                 in 
                   (fp',en',nam::xs')
                 end
          end)

        | Absyn.VARDEC(t,Absyn.ARRdecl(x,SOME i)) =>
          if check_formals x t en then  
          (let val nam = RTL.newTemp() 
               val (fp',en',xs') = transFormals(xs,en,fp) 
           in (fp',en',nam::xs')
           end)
          else 
         (let val nam = RTL.newTemp() 
          in
            if (t = Absyn.INTty) then 
            let 
               val (fp',en',xs') = transFormals(xs,Env.insert(en,x,(arg,RTL.LONG,(nam,"1"))),fp) 
            in (fp',en',nam::xs')
            end
          else 
           let 
               val (fp',en',xs') = transFormals(xs,Env.insert(en,x,(arg,RTL.BYTE,(nam,"1"))),fp) 
           in (fp',en',nam::xs')
           end
          end)

        | Absyn.VARDEC(t,Absyn.ARRdecl(x,NONE)) =>
          if check_formals x t en then   
          (let val nam = RTL.newTemp() 
               val (fp',en',xs')=  transFormals(xs,en,fp)
           in (fp',en',nam::xs')
           end)
        
         else 
          (let val nam = RTL.newTemp() 
           in          
            if (t = Absyn.INTty) then 
            let  
               val (fp',en',xs')=  transFormals(xs,Env.insert(en,x,(arg,RTL.LONG,(nam,"1"))),fp)
            in (fp',en',nam::xs')
            end
           else 
           let  
               val (fp',en',xs')=  transFormals(xs,Env.insert(en,x,(arg,RTL.BYTE,(nam,"1"))),fp)
           in (fp',en',nam::xs')
           end
         end )

	and f_body_to_rtl (stmt,en,ty,eofLab) = 
        case stmt of 
			Absyn.STMT(Absyn.SEQ(st1,st2),_,_) =>  
            let val (st1InstList,st1TmpList) = f_body_to_rtl (st1,en,ty,eofLab)
                val (st2InstList,st2TmpList) = f_body_to_rtl (st2,en,ty,eofLab)
            in 
				(st1InstList@st2InstList,st1TmpList@st2TmpList)
            end
          | Absyn.STMT(Absyn.EFFECT(exp),_,_) => 
			let val (instList,_,tmpList) = check_expr exp en
			in (instList,tmpList)
			end
          | Absyn.STMT(Absyn.EMPTY,_,_) => ([],[])
          | Absyn.STMT(Absyn.IF(exp,stm1,SOME stm2),_,_) =>
            let val (se,te,expTmpList) = check_expr exp en
                val l1 = RTL.newLabel()
                val fals = RTL.newTemp()
                val loadF = RTL.EVAL(fals,RTL.ICON(0))
                val cJump = RTL.CJUMP(RTL.EQ,te,fals,l1)
                val (s1,stm1TmpList) = f_body_to_rtl (stm1,en,ty,eofLab)
                val l2 = RTL.newLabel()
                val jump = RTL.JUMP(l2)
                val labDefL1 = RTL.LABDEF(l1)
                val (s2,stm2TmpList) = f_body_to_rtl (stm2,en,ty,eofLab)
                val labDefL2 = RTL.LABDEF(l2)
                val insList = se@[loadF,cJump]@s1@[jump,labDefL1]@s2@[labDefL2]
            in 
				(insList,fals::expTmpList@stm1TmpList@stm2TmpList)
            end
          | Absyn.STMT(Absyn.IF(exp,stm1,NONE),_,_) =>
            let val (se,te,expTmpList) = check_expr exp en
                val l1 = RTL.newLabel()
                val tru = RTL.newTemp()
                val loadTru = RTL.EVAL(tru,RTL.ICON(0))
                val cJump = RTL.CJUMP(RTL.EQ,te,tru,l1)
                val (s1,stm1TmpList) = f_body_to_rtl (stm1,en,ty,eofLab)
                val labDefL1 = RTL.LABDEF(l1)
                val insList = se@loadTru::cJump::s1@labDefL1::[]
            in 
				(insList,expTmpList@tru::stm1TmpList)
            end
          | Absyn.STMT(Absyn.WHILE(exp,stmt),_,_) =>
            let val (se,te,expTmpList) = check_expr exp en
                val (sIns,stmtTmpList) = f_body_to_rtl (stmt,en,ty,eofLab)
                val loop = RTL.newLabel()
                val stop = RTL.newLabel()
                val loopDef = RTL.LABDEF(loop)
                val fals = RTL.newTemp()
                val loadF = RTL.EVAL(fals,RTL.ICON(0)) 
                val cJump = RTL.CJUMP(RTL.EQ,te,fals,stop)
                val jump = RTL.JUMP(loop)
                val stopDef = RTL.LABDEF(stop)
                val insList = loopDef::se@loadF::cJump::sIns@jump::stopDef::[]
            in 
				(insList,expTmpList@fals::stmtTmpList)
            end
          | Absyn.STMT(Absyn.RETURN(SOME exp),_,_) =>
            let val (inst,res,expTmpList) = check_expr exp en
                val lEnd = eofLab
                val jump = RTL.JUMP(lEnd)
                val lDef = RTL.LABDEF(lEnd)
                val ins = RTL.EVAL(RTL.RV,RTL.TEMP(res))
            in 
				(inst@[ins,jump],expTmpList) 
            end
          | Absyn.STMT(Absyn.RETURN(NONE),_,_) =>
            let val lEnd = eofLab
                val jump = RTL.JUMP(lEnd)
                val lDef = RTL.LABDEF(lEnd)
            in 
				([jump,lDef],[]) 
            end

   and check_expr exp env = 
	   case exp of 
		   Absyn.EXP(Absyn.ASSIGN(ex1,ex2),_,_) =>
		   let val (ex2InstList,tmp,ex2TmpList) = check_expr ex2 env
           in
			   case ex1 of
				   Absyn.EXP(Absyn.ARRAY(id,e),_,_) =>
				   let 
					   val (eInstList,index,eTmpList) = check_expr e env
					   val (stat,ty,(offset,labRef)) = (valOf(Env.find(env,id)))
				   in 
					   if (stat = 0 ) then
						   let 
							   val t1 = RTL.newTemp()
							   val t2 = RTL.newTemp()
							   val t3 = RTL.newTemp()
							   val t4 = RTL.newTemp()
							   val t5 = RTL.newTemp()
							   val ins1 = RTL.EVAL(t1,RTL.ICON(RTL.sizeof(ty)))
							   val ins2 = RTL.EVAL(t2,RTL.BINARY(RTL.MUL,index,t1))
							   val ins3 = RTL.EVAL(t3,RTL.ICON(offset))
							   val ins4 = RTL.EVAL(t4,RTL.BINARY(RTL.ADD,t3,t2))
							   val ins5 = RTL.EVAL(t5,RTL.BINARY(RTL.ADD,t4,RTL.FP))
							   val ins6 = RTL.STORE(ty,t5,tmp)
						   in  
							   ((ex2InstList@eInstList)@([ins1,ins2,ins3,ins4,ins5,ins6]),
								t5,(ex2TmpList@eTmpList)@([t1,t2,t3,t4,t5]))
						   end
					   else if (stat = 2) then 
						   let 
							   val t1 = RTL.newTemp()
							   val t2 = RTL.newTemp()
							   val t3 = RTL.newTemp()
							   val ins1 = RTL.EVAL(t1,RTL.ICON(RTL.sizeof(ty)))
							   val ins2 = RTL.EVAL(t2,RTL.BINARY(RTL.MUL,index,t1))
							   val ins3 = RTL.EVAL(t3,RTL.BINARY(RTL.ADD,offset,t2))
							   val ins4 = RTL.STORE(ty,t3,tmp)
						   in 
							   ((ex2InstList@eInstList)@([ins1,ins2,ins3,ins4]),
								t3,(ex2TmpList@eTmpList)@([t1,t2,t3]))
						   end

					   else
						   let 
							   val t1 = RTL.newTemp()
							   val t2 = RTL.newTemp()
							   val t3 = RTL.newTemp()
							   val t4 = RTL.newTemp()
							   val ins1 = RTL.EVAL(t1,RTL.ICON(RTL.sizeof(ty)))
							   val ins2 = RTL.EVAL(t2,RTL.BINARY(RTL.MUL,index,t1))
							   val ins3 = RTL.EVAL(t3,RTL.LABREF(labRef))
							   val ins4 = RTL.EVAL(t4,RTL.BINARY(RTL.ADD,t3,t2))
							   val ins5 = RTL.STORE(ty,t4,tmp)
						   in 
							   ((ex2InstList@eInstList)@([ins1,ins2,ins3,ins4,ins5]),
								t4,(ex2TmpList@eTmpList)@([t1,t2,t3,t4]))
						   end
				   end
				 | Absyn.EXP(Absyn.VAR(id),_,_) =>
				   let 
					   val (stat,ty,(alocDet,labRef)) = (valOf(Env.find(env,id)))
				   in
					   if (stat = 0) then
						   let 
							   val inst1 = RTL.EVAL(alocDet,RTL.TEMP(tmp))
						   in  (ex2InstList@([inst1]),tmp, ex2TmpList)
						   end
					   else 
						   let 
							   val t0 = RTL.newTemp()
							   val inst1 = RTL.EVAL(t0, RTL.LABREF(labRef))
							   val inst2 = RTL.STORE(ty,t0,tmp)
						   in  (ex2InstList@([inst1,inst2]),t0,ex2TmpList@([t0]))
						   end 
				   end
				 | _ => ([],0,[])
		   end

         | Absyn.EXP(Absyn.VAR(id),_,_) => 
           let   
               val (stat,ty,(offset,labRef)) = (valOf(Env.find(env,id)))
           in 
               if (stat = 0) andalso (labRef = "0") then ([],offset,[])
               else if (stat = 2) andalso (labRef = "1") then 
                   let   
					   val t1   = RTL.newTemp()
					   val ins3 = RTL.EVAL(t1,RTL.UNARY(RTL.LOAD(RTL.LONG),offset))
				   in 
					   ([ins3],t1,[t1]) 
				   end 
               else if (stat = 0) andalso (labRef = "1") then 
				   let val t1   = RTL.newTemp()
					   val t2   = RTL.newTemp()
					   val t3   = RTL.newTemp() 
					   val ins1 = RTL.EVAL(t1,RTL.ICON(offset)) 
					   val ins2 = RTL.EVAL(t2,RTL.BINARY(RTL.ADD,t1,RTL.FP))
					   val ins3 = RTL.EVAL(t3,RTL.UNARY(RTL.LOAD(RTL.LONG),t2))
				   in 
					   ([ins1,ins2,ins3],t3,[t1,t2,t3]) 
				   end 
               else     
				   let
                       val t0 = RTL.newTemp()
                       val tr = RTL.newTemp()
                       val inst1 = RTL.EVAL(t0,RTL.LABREF(labRef))
                       val inst2 = RTL.EVAL(tr,RTL.UNARY(RTL.LOAD(ty),t0))
                   in 
                       ([inst1,inst2],tr,[t0,tr]) 
                   end
           end
         | Absyn.EXP(Absyn.ARRAY(id,exp),_,_) => 
           let 
             val (stat,ty,(offset,labRef)) = (valOf(Env.find(env,id)))
             val (instListMid,index,tmpListMid) = check_expr exp env
           in 
             if stat = 0 then 
               let 
                 val t1 = RTL.newTemp()
                 val t2 = RTL.newTemp()
                 val t3 = RTL.newTemp()
                 val t4 = RTL.newTemp()
                 val t5 = RTL.newTemp()
                 val t6 = RTL.newTemp()
                 val ins1 = RTL.EVAL(t1,RTL.ICON(RTL.sizeof(ty)))
                 val ins2 = RTL.EVAL(t2,RTL.BINARY(RTL.MUL,index,t1))
                 val ins3 = RTL.EVAL(t3,RTL.ICON(offset))
                 val ins4 = RTL.EVAL(t4,RTL.BINARY(RTL.ADD,t3,t2))
                 val ins5 = RTL.EVAL(t5,RTL.BINARY(RTL.ADD,t4,RTL.FP))
                 val ins6 = RTL.EVAL(t6,RTL.UNARY(RTL.LOAD(ty),t5))
               in 
                 (instListMid@([ins1,ins2,ins3,ins4,ins5,ins6]),
                  t6,tmpListMid@([t1,t2,t3,t4,t5,t6]))
               end
             else if stat = 2 then 
               let 
                 val t1 = RTL.newTemp()
                 val t2 = RTL.newTemp()
                 val t3 = RTL.newTemp()
                 val t4 = RTL.newTemp()
                 val t5 = RTL.newTemp()
                 val t6 = RTL.newTemp()
                 val ins1 = RTL.EVAL(t1,RTL.ICON(RTL.sizeof(ty)))
                 val ins2 = RTL.EVAL(t2,RTL.BINARY(RTL.MUL,index,t1))
                 val ins3 = RTL.EVAL(t3,RTL.ICON(0))
                 val ins4 = RTL.EVAL(t4,RTL.BINARY(RTL.ADD,t3,t2))
                 val ins5 = RTL.EVAL(t5,RTL.BINARY(RTL.ADD,t4,offset))
                 val ins6 = RTL.EVAL(t6,RTL.UNARY(RTL.LOAD(ty),t5))
               in 
                 (instListMid@([ins1,ins2,ins3,ins4,ins5,ins6]),
                  t6,tmpListMid@([t1,t2,t3,t4,t5,t6]))
               end
             else 
               let 
                 val t1 = RTL.newTemp()
                 val t2 = RTL.newTemp()
                 val t3 = RTL.newTemp()
                 val t4 = RTL.newTemp()
                 val t5 = RTL.newTemp()
                 val ins1 = RTL.EVAL(t1,RTL.ICON(RTL.sizeof(ty)))
                 val ins2 = RTL.EVAL(t2,RTL.BINARY(RTL.MUL,index,t1))
                 val ins3 = RTL.EVAL(t3,RTL.LABREF(labRef))
                 val ins4 = RTL.EVAL(t4,RTL.BINARY(RTL.ADD,t3,t2))
                 val ins5 = RTL.EVAL(t5,RTL.UNARY(RTL.LOAD(ty),t4))
               in 
                 (instListMid@([ins1,ins2,ins3,ins4,ins5]),
                  t5,tmpListMid@([t1,t2,t3,t4,t5]))
               end
             end
          | Absyn.EXP(Absyn.CONST(Absyn.INTcon(i)),_,_) => 
            let 
              val res = RTL.newTemp()
              val inst = RTL.EVAL(res,RTL.ICON(i))
            in 
              ([inst],res,[res]) 
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.ADD,ex1,ex2),_,_) => 
            let 
              val (il1,t1,tmp1List) = check_expr ex1 env
              val (il2,t2,tmp2List) = check_expr ex2 env
              val t3 = RTL.newTemp()
              val inst = RTL.EVAL(t3,RTL.BINARY(RTL.ADD,t1,t2))
            in
              (il1@il2@[inst],t3,tmp1List@tmp2List@[t3])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.SUB,ex1,ex2),_,_) => 
            let 
              val (il1,t1,tmp1List) = check_expr ex1 env
              val (il2,t2,tmp2List) = check_expr ex2 env
              val t3 = RTL.newTemp()
              val inst  = RTL.EVAL(t3,RTL.BINARY(RTL.SUB,t1,t2))
            in
              (il1@il2@[inst],t3,tmp1List@tmp2List@[t3])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.MUL,ex1,ex2),_,_) => 
            let 
              val (il1,t1,tmp1List) = check_expr ex1 env
              val (il2,t2,tmp2List) = check_expr ex2 env
              val t3 = RTL.newTemp()
              val inst  = RTL.EVAL(t3,RTL.BINARY(RTL.MUL,t1,t2))
            in
              (il1@il2@[inst],t3,tmp1List@tmp2List@[t3])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.DIV,ex1,ex2),_,_) => 
            let 
              val (il1,t1,tmp1List) = check_expr ex1 env
              val (il2,t2,tmp2List) = check_expr ex2 env
              val t3 = RTL.newTemp()
              val inst  = RTL.EVAL(t3,RTL.BINARY(RTL.DIV,t1,t2))
            in
              (il1@il2@[inst],t3,tmp1List@tmp2List@[t3])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.LT,ex1,ex2),_,_) => 
            let 
              val (se1,te1,tmp1) = check_expr ex1 env
              val (se2,te2,tmp2) = check_expr ex2 env
              val res = RTL.newTemp()
              val tru = RTL.newLabel()
              val return = RTL.newLabel()
              val cJump = RTL.CJUMP(RTL.LT,te1,te2,tru)
              val setFal = RTL.EVAL(res,RTL.ICON(0))
              val jump1 = RTL.JUMP(return)
              val labDefTru = RTL.LABDEF(tru)
              val setTru = RTL.EVAL(res,RTL.ICON(1))
              val jump2 = RTL.JUMP(return)
              val labDefReturn = RTL.LABDEF(return)
            in 
              (se1@se2@[cJump,setFal,jump1,labDefTru,setTru,jump2,labDefReturn],res,tmp1@tmp2@[res])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.LE,ex1,ex2),_,_) => 
            let 
              val (se1,te1,tmp1) = check_expr ex1 env
              val (se2,te2,tmp2) = check_expr ex2 env
              val res = RTL.newTemp()
              val tru = RTL.newLabel()
              val return = RTL.newLabel()
              val cJump = RTL.CJUMP(RTL.LE,te1,te2,tru)
              val setFal = RTL.EVAL(res,RTL.ICON(0))
              val jump1 = RTL.JUMP(return)
              val labDefTru = RTL.LABDEF(tru)
              val setTru = RTL.EVAL(res,RTL.ICON(1))
              val jump2 = RTL.JUMP(return)
              val labDefReturn = RTL.LABDEF(return)
            in 
              (se1@se2@[cJump,setFal,jump1,labDefTru,setTru,jump2,labDefReturn],
                res,tmp1@tmp2@[res])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.EQ,ex1,ex2),_,_) => 
            let 
              val (se1,te1,tmp1) = check_expr ex1 env
              val (se2,te2,tmp2) = check_expr ex2 env
              val res = RTL.newTemp()
              val tru = RTL.newLabel()
              val return = RTL.newLabel()
              val cJump = RTL.CJUMP(RTL.EQ,te1,te2,tru)
              val setFal = RTL.EVAL(res,RTL.ICON(0))
              val jump1 = RTL.JUMP(return)
              val labDefTru = RTL.LABDEF(tru)
              val setTru = RTL.EVAL(res,RTL.ICON(1))
              val jump2 = RTL.JUMP(return)
              val labDefReturn = RTL.LABDEF(return)
            in 
              (se1@se2@[cJump,setFal,jump1,labDefTru,setTru,jump2,labDefReturn],
                res,tmp1@tmp2@[res])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.NE,ex1,ex2),_,_) => 
            let 
              val (se1,te1,tmp1) = check_expr ex1 env
              val (se2,te2,tmp2) = check_expr ex2 env
              val res = RTL.newTemp()
              val tru = RTL.newLabel()
              val return = RTL.newLabel()
              val cJump = RTL.CJUMP(RTL.NE,te1,te2,tru)
              val setFal = RTL.EVAL(res,RTL.ICON(0))
              val jump1 = RTL.JUMP(return)
              val labDefTru = RTL.LABDEF(tru)
              val setTru = RTL.EVAL(res,RTL.ICON(1))
              val jump2 = RTL.JUMP(return)
              val labDefReturn = RTL.LABDEF(return)
            in 
              (se1@se2@[cJump,setFal,jump1,labDefTru,setTru,jump2,labDefReturn],
                res,tmp1@tmp2@[res])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.GE,ex1,ex2),_,_) => 
            let 
              val (se1,te1,tmp1) = check_expr ex1 env
              val (se2,te2,tmp2) = check_expr ex2 env
              val res = RTL.newTemp()
              val tru = RTL.newLabel()
              val return = RTL.newLabel()
              val cJump = RTL.CJUMP(RTL.GE,te1,te2,tru)
              val setFal = RTL.EVAL(res,RTL.ICON(0))
              val jump1 = RTL.JUMP(return)
              val labDefTru = RTL.LABDEF(tru)
              val setTru = RTL.EVAL(res,RTL.ICON(1))
              val jump2 = RTL.JUMP(return)
              val labDefReturn = RTL.LABDEF(return)
            in 
              (se1@se2@[cJump,setFal,jump1,labDefTru,setTru,jump2,labDefReturn],
                res,tmp1@tmp2@[res])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.GT,ex1,ex2),_,_) => 
            let 
              val (se1,te1,tmp1) = check_expr ex1 env
              val (se2,te2,tmp2) = check_expr ex2 env
              val res = RTL.newTemp()
              val tru = RTL.newLabel()
              val return = RTL.newLabel()
              val cJump = RTL.CJUMP(RTL.GT,te1,te2,tru)
              val setFal = RTL.EVAL(res,RTL.ICON(0))
              val jump1 = RTL.JUMP(return)
              val labDefTru = RTL.LABDEF(tru)
              val setTru = RTL.EVAL(res,RTL.ICON(1))
              val jump2 = RTL.JUMP(return)
              val labDefReturn = RTL.LABDEF(return)
            in 
              (se1@se2@[cJump,setFal,jump1,labDefTru,setTru,jump2,labDefReturn],
                res,tmp1@tmp2@[res])
            end

          | Absyn.EXP(Absyn.BINARY(Absyn.ANDALSO,ex1,ex2),_,_) => 
            let 
              val (ilist1,restm1,tmpList1) = check_expr ex1 env
              val (ilist2,restm2,tmpList2) = check_expr ex2 env
              val tmptrue  = RTL.newTemp()
              val l1       = RTL.newLabel()
              val loadt2   = RTL.EVAL(tmptrue,RTL.ICON(1))
              val cJump1   = RTL.CJUMP(RTL.EQ,restm1,tmptrue,l1)
              val labdef1  = RTL.LABDEF(l1)
              val l2       = RTL.newLabel()
              val loadt2   = RTL.EVAL(tmptrue,RTL.ICON(1)) 
              val cJump2   = RTL.CJUMP(RTL.EQ,restm2,tmptrue,l2)
              val labdef2  = RTL.LABDEF(l2)
              val res      = RTL.newTemp()
              val restrue  = RTL.EVAL(res,RTL.ICON(1))
              val resfalse = RTL.EVAL(res,RTL.ICON(0))
              val endLabel = RTL.newLabel() 
              val jumpEnd  = RTL.JUMP(endLabel) 
              val labdefEnd= RTL.LABDEF(endLabel)
            in
              (ilist1@[loadt2,cJump1,resfalse,jumpEnd,labdef1]@ilist2
                     @[loadt2,cJump2,resfalse,jumpEnd,labdef2,restrue,jumpEnd,labdefEnd],
               res,tmpList1@tmpList2@[res,tmptrue])
            end

          | Absyn.EXP(Absyn.UNARY(Absyn.NEG,exp),i,j) =>
            let 
              val newExp = Absyn.EXP(Absyn.BINARY(Absyn.SUB,Absyn.EXP(Absyn.CONST(Absyn.INTcon(0)),i,j),exp),i,j) 
            in check_expr newExp env
            end

          | Absyn.EXP(Absyn.UNARY(Absyn.NOT,exp),i,j) =>
            let 
              val newExp = Absyn.EXP(Absyn.BINARY(Absyn.EQ,Absyn.EXP(Absyn.CONST(Absyn.INTcon(0)),i,j),exp),i,j) 
            in check_expr newExp env 
            end

          | Absyn.EXP(Absyn.FCALL(id,exList),_,_) =>
            let 
              val (_,ty,(_,label)) = valOf(Env.find(env,id))
              val (inslist,ftmlist,tmlist) = check_external_list exList env
              val tm = RTL.newTemp()
            in 
              if ty = RTL.BYTE then  
                (inslist@[RTL.CALL(SOME tm,label,ftmlist)],tm,tmlist) 
              else if ty = RTL.LONG then 
                     (inslist@[RTL.CALL(SOME tm,label,ftmlist)],tm,tmlist) 
              else (inslist@[RTL.CALL(NONE,label,ftmlist)],tm,tmlist)
            end

    and check_external_list [] _ = ([],[],[])
      | check_external_list (exp::exps) env = 
        let val (insns,tm,tmplist) = check_expr exp env
            val (inss,restm,tms) = check_external_list exps env 
        in              
			(insns@inss,tm::restm,tmplist@tms)
        end

    and insert_function_name name id typ env = 
		case typ of 
            Absyn.INTty  => Env.insert(env,id,(0,RTL.LONG,(0,name))) 
          | _            => Env.insert(env,id,(0,RTL.BYTE,(0,name)))

    and check_formals var typ env = 
		case Env.find(env, var) of 
            SOME (_,RTL.LONG,_) => typ = Absyn.INTty   
          | SOME (_,RTL.BYTE,_) => typ = Absyn.INTty orelse typ = Absyn.CHARty 
          | _                   => false

  end (* functor AbsynToRTLFn *)
