(* mips/mips-codegen.sml *)


functor MIPSCodegenFn(structure RTL : RTL
		      structure MIPS : MIPS
			) : CODEGEN =
struct

  structure RTL = RTL
  structure Assem = MIPS

  (* help variables and functions *)
  val env = []

  val bEnv = []

  val varTrack = []
 

  val formal_temp_counter = ref 1

  fun tick counter =
    let val i = !counter + 1
        val _ = counter := i
    in
      i
    end
  
  fun reset counter= 
    let val i = ref 0 
    in 
      !i
    end

  fun first (a,_) = a
  fun second (_,b) = b
 
  fun find tm [] = false
    | find tm (t::ts) = if tm = t then true else find tm ts 

  fun find_index tm [] = (false,0)
    | find_index tm ((t,i)::ts) = if tm = t then (true,i) 
                                  else find_index tm ts 

  fun make_index_list [] _ = []
    | make_index_list (t::ts) cntr = 
      let val cntr' = ref (tick cntr) 
      in 
        (t,!cntr')::(make_index_list ts cntr')
      end

  fun insert tm en = if find tm en then en else tm::en

  fun mem _ [] = false
    | mem v (x::xs) = if v = x then true else mem v xs


  fun checkVar lb = String.isPrefix "V" lb 

  fun printVarTrack [] = ()
    | printVarTrack (l::ls) = (print(Int.toString(l));printVarTrack (ls))


  fun f_call_tmp_aloc [] _ _ _ _ _ _ _ = []
    | f_call_tmp_aloc (t::tl) lb frms locals env varTrack bEnv frms_index_list =
        if t = 1 then  
          Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(30,0))))::
          Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
          f_call_tmp_aloc tl lb frms locals env varTrack bEnv frms_index_list
        else if lb = "putstring" andalso find t frms then
          let val (_,index) = find_index t frms_index_list in 
            Assem.INSTRUCTION(Assem.load(8,30,4*index))::
            Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
            f_call_tmp_aloc tl lb frms locals env varTrack bEnv frms_index_list
          end
        
        else if (find t frms) andalso not (find t locals) then
          let val (_,index) = find_index t frms_index_list in    
             Assem.INSTRUCTION(Assem.load(8,30, (index * 4)))::
             Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
             f_call_tmp_aloc tl lb frms locals env varTrack bEnv frms_index_list
          end
        else if (lb = "putint") andalso not (find t varTrack) andalso (find t env) andalso (find t bEnv) then  
          Assem.INSTRUCTION(Assem.load(8,29,t*4))::
          Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
          Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
          f_call_tmp_aloc tl lb frms locals env varTrack bEnv frms_index_list

        else if (lb = "putint") andalso not (find t varTrack) andalso (find t env) then  
          Assem.INSTRUCTION(Assem.load(8,29,t*4))::
          Assem.INSTRUCTION(Assem.load(8,8,0))::
          Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
          f_call_tmp_aloc tl lb frms locals env varTrack bEnv frms_index_list

        else 
          Assem.INSTRUCTION(Assem.load(8,29,t*4))::
          Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
          f_call_tmp_aloc tl lb frms locals env varTrack bEnv frms_index_list

  (*************************************)

  fun program p = program_to_asm p env varTrack bEnv

  and program_to_asm (RTL.PROGRAM([])) env varTrack bEnv = sysCalls ()
    | program_to_asm (RTL.PROGRAM(d::dlist)) env varTrack bEnv = 
      (rtl_to_asm d env varTrack bEnv)@(program_to_asm (RTL.PROGRAM(dlist)) env varTrack bEnv)

  and rtl_to_asm dec env varTrack bEnv = 
    case dec of     
      RTL.DATA {label, size} => data (label, size) 
    | RTL.PROC {label, formals, locals, frameSize, insns} => 
        proc label formals locals frameSize insns env varTrack bEnv

  and proc lb frms locals fs inss env varTrack bEnv = 
    if lb = "Pcheck" then 
    let 
      val i = length(locals)*16 + length(frms)*16 + fs*16 + 2024 (* the size of stack *)
      val cntr = ref 0
      val frms_index_list = make_index_list frms cntr
      val bogus = 1
    in 
      Assem.TEXT::Assem.INSTRUCTION(Assem.label(lb))::
      calle_save(i)@(checkIns inss frms locals env varTrack bEnv frms_index_list bogus)@return_inst(i)
    end
    else 
    let 
      val i = length(locals)*16 + length(frms)*16 + fs*16 + 2024 (* the size of stack *)
      val cntr = ref 0
      val frms_index_list = make_index_list frms cntr
      val bogus = 0
    in 
      Assem.TEXT::Assem.INSTRUCTION(Assem.label(lb))::
      calle_save(i)@(checkIns inss frms locals env varTrack bEnv frms_index_list bogus)@return_inst(i)
    end


  and data (label, size) = 
      Assem.DATASEG::
      Assem.ALIGN(2)::
      Assem.INSTRUCTION(Assem.LABEL(label))::
      Assem.SPACE(size)::[]

  and checkIns [] _ _ _ _ _ _ _ = []
    | checkIns (ins::insns) frms locals env varTrack bEnv frms_index_list bogus = 
      case ins of 
        RTL.CALL (SOME t, label, tmlist) => 
          f_call_tmp_aloc tmlist label frms locals env varTrack bEnv frms_index_list @           
          Assem.INSTRUCTION(Assem.addi(29,29,~4*length(tmlist)))::
          Assem.INSTRUCTION(Assem.JUMP(Assem.JAL(Assem.LAB(label))))::
          Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,2)))::
          Assem.INSTRUCTION(Assem.addi(29,29,4*length(tmlist)))::
          Assem.INSTRUCTION(Assem.store(8,29,t*4))::
          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)


      | RTL.JUMP (lb) =>  Assem.INSTRUCTION(Assem.JUMP(Assem.B(lb)))::(checkIns insns frms locals env varTrack bEnv frms_index_list bogus)

      | RTL.LABDEF (lb)=>  Assem.INSTRUCTION(Assem.label(lb))::(checkIns insns frms locals env varTrack bEnv frms_index_list bogus)


      | RTL.STORE (ty,tmp1,tmp2) => 
          let val (findTm1,index1) = find_index tmp1 frms_index_list 
              val (findTm2,index2) = find_index tmp2 frms_index_list
          in  
            (case ty of 
              RTL.LONG =>
              if findTm1 andalso findTm2 then 
                Assem.INSTRUCTION(Assem.load(8,30,index2*4))::
                Assem.INSTRUCTION(Assem.load(9,30,index1*4))::
                Assem.INSTRUCTION(Assem.store(8,9,0))::
                (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if findTm1 andalso not findTm2 then 
                Assem.INSTRUCTION(Assem.load(8,29,tmp2*4))::
                Assem.INSTRUCTION(Assem.load(9,30,index1*4))::
                Assem.INSTRUCTION(Assem.store(8,9,0))::
                (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if not findTm1 andalso findTm2 then 
                Assem.INSTRUCTION(Assem.load(8,30,index2*4))::
                Assem.INSTRUCTION(Assem.load(9,29,tmp1*4))::
                Assem.INSTRUCTION(Assem.store(8,9,0))::
                (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else 
                Assem.INSTRUCTION(Assem.load(8,29,tmp2*4))::
                Assem.INSTRUCTION(Assem.load(9,29,tmp1*4))::
                Assem.INSTRUCTION(Assem.store(8,9,0))::
                (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)

            | RTL.BYTE =>  
              if findTm1 andalso findTm2 then 
                (if find tmp2 bEnv then 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(30,index2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(30,index1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                 else 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(30,index2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(30,index1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
 
              else if findTm1 andalso not findTm2 then 
                (if find tmp2 bEnv then   
                  Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(29,tmp2*4))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(30,index1*4))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                  (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                else 
                  Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(29,tmp2*4))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(30,index1*4))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                  (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
              else if not findTm1 andalso findTm2 then 
                (if find tmp2 bEnv then 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(30,index2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0)))):: 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(29,tmp1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                 else 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(30,index2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(29,tmp1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))

              else 
                (if find tmp2 bEnv then 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(29,tmp2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(29,tmp1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                 else 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(29,tmp2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(29,tmp1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)))
            end


      | RTL.EVAL (tmp,exp) =>  
         (case exp of
           RTL.BINARY(RTL.ADD,t1,t2) =>
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                 Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso (find t2 env) then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                    Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frms_index_list 
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if find t1 varTrack then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        (*Assem.INSTRUCTION(Assem.load(8,8,0))::*)
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)

                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if find t1 varTrack then 
                        let val varTrack' = insert tmp varTrack in 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                           Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                           (checkIns insns frms locals env varTrack' bEnv frms_index_list bogus)
                         end
                        else
                         Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                         Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                         Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                         Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                         (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
          | RTL.BINARY(RTL.MUL,t1,t2) =>
                if t2 = 1 then 
                  Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                  Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                  Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                  (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                else if (find t1 env) andalso (find t2 env) then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                    Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                else if (find t1 env) andalso not (find t2 env) then
                    let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        (*Assem.INSTRUCTION(Assem.load(8,8,0))::*)
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end

         | RTL.BINARY(RTL.DIV,t1,t2) => 
               if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                 Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
               else if (find t1 env) andalso (find t2 env) then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                    Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
               else if (find t1 env) andalso not (find t2 env) then
                    let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        (*Assem.INSTRUCTION(Assem.load(8,8,0))::*)
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
     

         | RTL.BINARY(RTL.SUB,t1,t2) => 
               if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                 Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
               else if (find t1 env) andalso (find t2 env) then 

                   (if find t1 bEnv then 
                      Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                      Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                      Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                      (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                      Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                      Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                      (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                   else 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                    Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
                else if (find t1 env) andalso not (find t2 env) then
                    let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        (*Assem.INSTRUCTION(Assem.load(8,8,0))::*)
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end

         | RTL.UNARY(RTL.LOAD(ty),tm) => (* load byte and long in differernt way *)
             if ty = RTL.BYTE then 
               let val env' = insert tmp env
                   val bEnv' = insert tmp bEnv 
                   val (findTm,index) = find_index tm frms_index_list 
               in
                 if findTm then 
                    (if find tm varTrack then 
                      let val varTrack' = insert tmp varTrack in
                        Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                        (checkIns insns frms locals env' varTrack' bEnv' frms_index_list bogus)
                      end
                    else  
                      Assem.INSTRUCTION(Assem.load(8,30,index*4))::
                      Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                      (checkIns insns frms locals env' varTrack bEnv' frms_index_list bogus))
                 else if find tm varTrack then 
                   let val varTrack' = insert tmp varTrack in
                      Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                      Assem.INSTRUCTION(Assem.load(8,8,0))::
                      Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                      (checkIns insns frms locals env' varTrack' bEnv' frms_index_list bogus)
                   end 
                 else if bogus = 1 then 
                   Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                   Assem.INSTRUCTION(Assem.load(8,8,0))::                 
                   Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                   (checkIns insns frms locals env' varTrack bEnv' frms_index_list bogus)
                 else 
                 Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (checkIns insns frms locals env' varTrack bEnv' frms_index_list bogus)
               end
             else
                let val env' = insert tmp env
                    val (findTm,index) = find_index tm frms_index_list 
               in
                 if findTm then 
                   Assem.INSTRUCTION(Assem.load(8,30,index*4))::
                   Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                   (checkIns insns frms locals env' varTrack bEnv frms_index_list bogus)
                 else if find tm varTrack then 
                   let val varTrack' = insert tmp varTrack in
                     Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                     Assem.INSTRUCTION(Assem.load(8,8,0))::
                     Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                     (checkIns insns frms locals env' varTrack' bEnv frms_index_list bogus)
                   end 
                 else if bogus = 1 then 
                   Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                   Assem.INSTRUCTION(Assem.load(8,8,0))::                 
                   Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                   (checkIns insns frms locals env' varTrack bEnv frms_index_list bogus)
                 else
                   Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                   Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                   (checkIns insns frms locals env' varTrack bEnv frms_index_list bogus)
               end
         
         | RTL.LABREF (lb) => 
               if checkVar lb then 
                 let val varTrack' = insert tmp varTrack
               in
                 Assem.INSTRUCTION(Assem.OPER(Assem.LA(8,lb)))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (checkIns insns frms locals env varTrack' bEnv frms_index_list bogus)
               end   
               else 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LA(8,lb)))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)       
         | RTL.ICON (i) => 
               Assem.INSTRUCTION(Assem.load_imm(8,i))::
               Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
               (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
         | RTL.TEMP (tm) => 
               if tmp = 0 then 
                 Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                 Assem.INSTRUCTION(Assem.store(8,29,12))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
               else if tm = 2 then 
                 Assem.INSTRUCTION(Assem.load_imm(8,1))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
               else if tm = 3 then
                 Assem.INSTRUCTION(Assem.load_imm(8,0))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
               else if find tm bEnv then 
                 Assem.INSTRUCTION(Assem.load(9,29,tm*4))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                 Assem.INSTRUCTION(Assem.load(8,29,tmp*4))::
                 Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(29,tmp*4))))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
               else 
                 let val (findTmp1,index1) = find_index tm frms_index_list
                     val (findTmp2,index2) = find_index tmp frms_index_list 
                 in
                   if findTmp1 andalso findTmp2 then 
                     Assem.INSTRUCTION(Assem.load(9,30,index1*4))::
                     Assem.INSTRUCTION(Assem.load(8,30,index2*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,30,index2*4))::
                     (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                   else if findTmp1 andalso not findTmp2 then                   
                     Assem.INSTRUCTION(Assem.load(9,30,index1*4))::
                     Assem.INSTRUCTION(Assem.load(8,29,tmp*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                     (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                   else if not findTmp1 andalso findTmp2 then                   
                     Assem.INSTRUCTION(Assem.load(9,29,tm*4))::
                     Assem.INSTRUCTION(Assem.load(8,30,index2*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,30,index2*4))::
                     (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                   else if find tm varTrack then 
                     Assem.INSTRUCTION(Assem.load(9,29,tm*4))::
                     Assem.INSTRUCTION(Assem.load(9,9,0))::
                     Assem.INSTRUCTION(Assem.load(8,29,tmp*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                     (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                   else 
                     Assem.INSTRUCTION(Assem.load(9,29,tm*4))::
                     Assem.INSTRUCTION(Assem.load(8,29,tmp*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                     (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)


                 end)


      | RTL.CJUMP (relop,t1,t2,label) =>
            case relop of 
              RTL.GT => 
              if t2 = 1 then 
                (if find t1 bEnv then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,4*t1))))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                else 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))

              else if (find t1 env) andalso (find t2 env) then 
                     (if not (find t1 bEnv) andalso not (find t2 bEnv) then 
                       Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                       Assem.INSTRUCTION(Assem.load(8,8,0))::
                       Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                       Assem.INSTRUCTION(Assem.load(9,9,0))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                       Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                       (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                     else if find t1 bEnv andalso not (find t2 bEnv) then 
                       Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                       Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                       Assem.INSTRUCTION(Assem.load(9,9,0))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                       Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                       (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                     else if not (find t1 bEnv) andalso find t2 bEnv then
                       Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                       Assem.INSTRUCTION(Assem.load(8,8,0))::
                       Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                       Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                       (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                     else 
                       Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                       Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                       Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                       (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))


              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then
                        (if find t1 bEnv andalso find t2 bEnv then    
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else if find t1 bEnv andalso not (find t2 bEnv) then
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                          else if not (find t1 bEnv) andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                          else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))

                      else 
                        (if find t1 bEnv andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else if find t1 bEnv andalso not (find t2 bEnv) then 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else if not (find t2 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)

                         else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        (if find t2 bEnv andalso find t1 bEnv then  
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,4*index))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else if not (find t1 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                          else if find t1 bEnv andalso not (find t2 bEnv) then
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                          else 
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))

                      else 
                        (if find t2 bEnv andalso find t1 bEnv then 
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else if find t1 bEnv andalso not (find t2 bEnv) then 
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.load(9,9,0))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else if not (find t1 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))

                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        (if find t1 bEnv andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,index1*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)

                         else if not(find t1 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)

                         else if find t1 bEnv andalso not (find t2 bEnv) then 
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,index1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)

                         else 
                           Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                           Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
 
                      else if findTm1 andalso not findTm2 then 
                        (if find t1 bEnv andalso find t2 bEnv then  
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,index1*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else if not (find t1 bEnv) andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else if find t1 bEnv andalso not (find t2 bEnv) then
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,index1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else
                           Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)) 
 
                      else if not(findTm1) andalso findTm2 then 
                        (if find t1 bEnv andalso find t2 bEnv then   
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else if not (find t1 bEnv) andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else if find t1 bEnv andalso not (find t2 bEnv) then

                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
                      else 
                        (if find t1 bEnv andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else if find t1 bEnv andalso not (find t2 bEnv) then
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else if not (find t1 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
                    end

           | RTL.GE => 

              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso (find t2 env) then 
                    if find t1 bEnv then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                   else
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        (if find t2 varTrack then 
                          Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else
 
                          Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.load(9,9,0))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
 
                      else 
                        (if find t2 varTrack then 
                          Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else 
                          Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.load(9,9,0))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))

                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end


            | RTL.NE => 
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso (find t2 env) then 

                   if find t1 bEnv then
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                  else 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
 
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if find t1 bEnv then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end

            | RTL.EQ => 
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso (find t2 env) then 

                   if find t1 bEnv then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                   else 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if find t1 bEnv then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        (if find t2 bEnv then  
                          Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else
                          Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.load(9,9,0))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))  

                      else 
                        (if find t2 bEnv then 
                          Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else 
                          Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.load(9,9,0))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end

            | RTL.LE => 
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso (find t2 env) then 
                    if find t1 bEnv then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    else 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end

            | RTL.LT => 
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso (find t2 env) then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frms_index_list
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        (if find t1 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                         else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frms_index_list
                    in
                      if findTm then
                        (if find t2 bEnv then  
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
 
                      else 
                        (if find t2 bEnv then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                        else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus))
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frms_index_list
                        val (findTm2,index2) = find_index t2 frms_index_list
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (checkIns insns frms locals env varTrack bEnv frms_index_list bogus)
                    end




  and calle_save (i) = 
      Assem.INSTRUCTION(Assem.addi(29,29,~i))::
      Assem.INSTRUCTION(Assem.store(30,29,4))::
      Assem.INSTRUCTION(Assem.store(31,29,8))::
      Assem.INSTRUCTION(Assem.store(4,29,12))::
      Assem.INSTRUCTION(Assem.addi(30,29,i))::[]

 

  and return_inst (i) =
      Assem.INSTRUCTION(Assem.load(2,29,12))::
      Assem.INSTRUCTION(Assem.load(30,29,4))::
      Assem.INSTRUCTION(Assem.load(31,29,8))::
      Assem.INSTRUCTION(Assem.load(4,29,12))::
      Assem.INSTRUCTION(Assem.addi(29,29,i))::
      Assem.INSTRUCTION(Assem.JUMP(Assem.RETURN))::[]



  and sysCalls () = 
      Assem.DATASEG::
      Assem.GLOBAL("putint")::
      Assem.GLOBAL("putstring")::
      Assem.GLOBAL("getint")::
      Assem.GLOBAL("getstring")::
      Assem.TEXT::
      Assem.INSTRUCTION(Assem.label("putint"))::
      Assem.INSTRUCTION(Assem.addi(29,29,~24))::
      Assem.INSTRUCTION(Assem.store(30,29,4))::
      Assem.INSTRUCTION(Assem.store(31,29,8))::
      Assem.INSTRUCTION(Assem.addi(30,29,24))::
      Assem.INSTRUCTION(Assem.load(4,30,4))::
      Assem.INSTRUCTION(Assem.load_imm(2,1))::
      Assem.INSTRUCTION(Assem.syscall)::
      Assem.INSTRUCTION(Assem.load(30,29,4))::
      Assem.INSTRUCTION(Assem.load(31,29,8))::
      Assem.INSTRUCTION(Assem.addi(29,29,24))::   
      Assem.INSTRUCTION(Assem.JUMP(Assem.RETURN))::

      Assem.TEXT::
      Assem.INSTRUCTION(Assem.label("putstring"))::
      Assem.INSTRUCTION(Assem.addi(29,29,~24))::
      Assem.INSTRUCTION(Assem.store(30,29,4))::
      Assem.INSTRUCTION(Assem.store(31,29,8))::
      Assem.INSTRUCTION(Assem.addi(30,29,24))::
      Assem.INSTRUCTION(Assem.load(4,30,4))::
      Assem.INSTRUCTION(Assem.load_imm(2,4))::
      Assem.INSTRUCTION(Assem.syscall)::
      Assem.INSTRUCTION(Assem.load(30,29,4))::
      Assem.INSTRUCTION(Assem.load(31,29,8))::
      Assem.INSTRUCTION(Assem.addi(29,29,24))::   
      Assem.INSTRUCTION(Assem.JUMP(Assem.RETURN))::


      Assem.TEXT::
      Assem.INSTRUCTION(Assem.label("getint"))::
      Assem.INSTRUCTION(Assem.addi(29,29,~24))::
      Assem.INSTRUCTION(Assem.store(30,29,4))::
      Assem.INSTRUCTION(Assem.store(31,29,8))::
      Assem.INSTRUCTION(Assem.addi(30,29,24))::
      Assem.INSTRUCTION(Assem.load(4,30,4))::
      Assem.INSTRUCTION(Assem.load_imm(2,5))::
      Assem.INSTRUCTION(Assem.syscall)::
      Assem.INSTRUCTION(Assem.load(30,29,4))::
      Assem.INSTRUCTION(Assem.load(31,29,8))::
      Assem.INSTRUCTION(Assem.addi(29,29,24))::   
      Assem.INSTRUCTION(Assem.JUMP(Assem.RETURN))::


      Assem.TEXT::
      Assem.INSTRUCTION(Assem.label("getstring"))::
      Assem.INSTRUCTION(Assem.addi(29,29,~24))::
      Assem.INSTRUCTION(Assem.store(30,29,4))::
      Assem.INSTRUCTION(Assem.store(31,29,8))::
      Assem.INSTRUCTION(Assem.addi(30,29,24))::
      Assem.INSTRUCTION(Assem.load(4,30,4))::
      Assem.INSTRUCTION(Assem.load_imm(5,80))::
      Assem.INSTRUCTION(Assem.load_imm(2,8))::
      Assem.INSTRUCTION(Assem.syscall)::
      Assem.INSTRUCTION(Assem.load(30,29,4))::
      Assem.INSTRUCTION(Assem.load(31,29,8))::
      Assem.INSTRUCTION(Assem.addi(29,29,24))::   
      Assem.INSTRUCTION(Assem.JUMP(Assem.RETURN))::[]




end (* functor MIPSCodegenFn *)
