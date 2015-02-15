(* mips/mips-codegen.sml *)

functor MIPSCodegenFn(structure RTL : RTL
		      structure MIPS : MIPS
			) : CODEGEN =
struct

  structure RTL = RTL
  structure Assem = MIPS

  (* help variables and functions *)
  fun tick counter =
    let val i = !counter + 1
        val _ = counter := i
    in
      i
    end
 
  fun find term termList = List.exists (fn x => x = term) termList 

  fun find_index term [] = (false,0)
    | find_index term ((t,i)::ts) =
        if t=term then (true,i) else find_index term ts

  fun make_index_list ts counter = List.map (fn x => (x, !(ref (tick counter)))) ts

  fun insert term en = if find term en then en else term::en

  fun f_call_tmp_aloc [] _ _ _ _ _ _ _ = []
    | f_call_tmp_aloc (t::tl) lb frms locals env varTrack bEnv frmsIndexList =
        if t = 1 then  
          Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(30,0))))::
          Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
          f_call_tmp_aloc tl lb frms locals env varTrack bEnv frmsIndexList
        else if lb = "putstring" andalso find t frms then
          let val (_,index) = find_index t frmsIndexList in 
            Assem.INSTRUCTION(Assem.load(8,30,4*index))::
            Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
            f_call_tmp_aloc tl lb frms locals env varTrack bEnv frmsIndexList
          end
        else if (find t frms) andalso not (find t locals) then
          let val (_,index) = find_index t frmsIndexList in    
             Assem.INSTRUCTION(Assem.load(8,30, (index * 4)))::
             Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
             f_call_tmp_aloc tl lb frms locals env varTrack bEnv frmsIndexList
          end
        else if (lb = "putint") andalso not (find t varTrack) andalso 
        (find t env) andalso (find t bEnv) then  
          Assem.INSTRUCTION(Assem.load(8,29,t*4))::
          Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
          Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
          f_call_tmp_aloc tl lb frms locals env varTrack bEnv frmsIndexList
        else if (lb = "putint") andalso not (find t varTrack) andalso (find t env) then  
          Assem.INSTRUCTION(Assem.load(8,29,t*4))::
          Assem.INSTRUCTION(Assem.load(8,8,0))::
          Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
          f_call_tmp_aloc tl lb frms locals env varTrack bEnv frmsIndexList
        else 
          Assem.INSTRUCTION(Assem.load(8,29,t*4))::
          Assem.INSTRUCTION(Assem.store(8,29,~4*length(tl)))::
          f_call_tmp_aloc tl lb frms locals env varTrack bEnv frmsIndexList

  fun calle_save (i) = 
      Assem.INSTRUCTION(Assem.addi(29,29,~i))::
      Assem.INSTRUCTION(Assem.store(30,29,4))::
      Assem.INSTRUCTION(Assem.store(31,29,8))::
      Assem.INSTRUCTION(Assem.store(4,29,12))::
      Assem.INSTRUCTION(Assem.addi(30,29,i))::[]

  fun return_inst (i) =
      Assem.INSTRUCTION(Assem.load(2,29,12))::
      Assem.INSTRUCTION(Assem.load(30,29,4))::
      Assem.INSTRUCTION(Assem.load(31,29,8))::
      Assem.INSTRUCTION(Assem.load(4,29,12))::
      Assem.INSTRUCTION(Assem.addi(29,29,i))::
      Assem.INSTRUCTION(Assem.JUMP(Assem.RETURN))::[]

  fun system_calls () = 
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
      [Assem.INSTRUCTION(Assem.JUMP(Assem.RETURN))]

  fun check_instructions [] _ _ _ _ _ _ _ = []
    | check_instructions ((RTL.CALL (SOME t, label, tmlist))::insns) frms locals env varTrack bEnv 
      frmsIndexList bogus = 
          f_call_tmp_aloc tmlist label frms locals env varTrack bEnv frmsIndexList @           
          Assem.INSTRUCTION(Assem.addi(29,29,~4*length(tmlist)))::
          Assem.INSTRUCTION(Assem.JUMP(Assem.JAL(Assem.LAB(label))))::
          Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,2)))::
          Assem.INSTRUCTION(Assem.addi(29,29,4*length(tmlist)))::
          Assem.INSTRUCTION(Assem.store(8,29,t*4))::
          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
    | check_instructions ((RTL.CALL (NONE, label, tmlist))::insns) frms locals env varTrack bEnv 
      frmsIndexList bogus = 
          f_call_tmp_aloc tmlist label frms locals env varTrack bEnv frmsIndexList @           
          Assem.INSTRUCTION(Assem.addi(29,29,~4*length(tmlist)))::
          Assem.INSTRUCTION(Assem.JUMP(Assem.JAL(Assem.LAB(label))))::
          Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,2)))::
          Assem.INSTRUCTION(Assem.addi(29,29,4*length(tmlist)))::
          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
    | check_instructions ((RTL.JUMP (lb))::insns) frms locals env varTrack bEnv frmsIndexList bogus = 
          Assem.INSTRUCTION(Assem.JUMP(Assem.B(lb)))::(check_instructions insns frms locals env varTrack 
                                                       bEnv frmsIndexList bogus)
    | check_instructions ((RTL.LABDEF (lb))::insns) frms locals env varTrack bEnv frmsIndexList bogus = 
          Assem.INSTRUCTION(Assem.label(lb))::(check_instructions insns frms locals env varTrack bEnv 
                                               frmsIndexList bogus)
    | check_instructions ((RTL.STORE (ty,tmp1,tmp2))::insns) frms locals env varTrack bEnv frmsIndexList bogus = 
          let val (findTm1,index1) = find_index tmp1 frmsIndexList 
              val (findTm2,index2) = find_index tmp2 frmsIndexList
          in  
            (case ty of  (* add a function here instead *)
              RTL.LONG =>
              if findTm1 andalso findTm2 then 
                Assem.INSTRUCTION(Assem.load(8,30,index2*4))::
                Assem.INSTRUCTION(Assem.load(9,30,index1*4))::
                Assem.INSTRUCTION(Assem.store(8,9,0))::
                (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if findTm1 andalso not findTm2 then 
                Assem.INSTRUCTION(Assem.load(8,29,tmp2*4))::
                Assem.INSTRUCTION(Assem.load(9,30,index1*4))::
                Assem.INSTRUCTION(Assem.store(8,9,0))::
                (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if not findTm1 andalso findTm2 then 
                Assem.INSTRUCTION(Assem.load(8,30,index2*4))::
                Assem.INSTRUCTION(Assem.load(9,29,tmp1*4))::
                Assem.INSTRUCTION(Assem.store(8,9,0))::
                (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else 
                Assem.INSTRUCTION(Assem.load(8,29,tmp2*4))::
                Assem.INSTRUCTION(Assem.load(9,29,tmp1*4))::
                Assem.INSTRUCTION(Assem.store(8,9,0))::
                (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
            | RTL.BYTE =>  
              if findTm1 andalso findTm2 then 
                (if find tmp2 bEnv then 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(30,index2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(30,index1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                 else 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(30,index2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(30,index1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
              else if findTm1 andalso not findTm2 then 
                (if find tmp2 bEnv then   
                  Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(29,tmp2*4))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(30,index1*4))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                  (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                else 
                  Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(29,tmp2*4))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(30,index1*4))))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                  (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
              else if not findTm1 andalso findTm2 then 
                (if find tmp2 bEnv then 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(30,index2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0)))):: 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(29,tmp1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                 else 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(30,index2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(29,tmp1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))

              else 
                (if find tmp2 bEnv then 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(29,tmp2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(29,tmp1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                 else 
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(8,Assem.OFFSET(29,tmp2*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.LW(9,Assem.OFFSET(29,tmp1*4))))::
                   Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(9,0))))::
                   (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)))
            end
  | check_instructions (( RTL.EVAL (tmp,exp))::insns) frms locals env varTrack bEnv frmsIndexList bogus = 
         (case exp of
           RTL.BINARY(RTL.ADD,t1,t2) =>
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                 Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso (find t2 env) then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                    Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frmsIndexList 
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if find t1 varTrack then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)

                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if find t1 varTrack then 
                        let val varTrack' = insert tmp varTrack in 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                           Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                           (check_instructions insns frms locals env varTrack' bEnv frmsIndexList bogus)
                         end
                        else
                         Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                         Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                         Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.ADD,10,8,9)))::
                         Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                         (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
          | RTL.BINARY(RTL.MUL,t1,t2) =>
                if t2 = 1 then 
                  Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                  Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                  Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                  Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                  (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                else if (find t1 env) andalso (find t2 env) then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                    Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                else if (find t1 env) andalso not (find t2 env) then
                    let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.MUL,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end

         | RTL.BINARY(RTL.DIV,t1,t2) => 
               if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                 Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
               else if (find t1 env) andalso (find t2 env) then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                    Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
               else if (find t1 env) andalso not (find t2 env) then
                    let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        (*Assem.INSTRUCTION(Assem.load(8,8,0))::*)
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.DIVU,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end

         | RTL.BINARY(RTL.SUB,t1,t2) => 
               if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                 Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
               else if (find t1 env) andalso (find t2 env) then 

                   (if find t1 bEnv then 
                      Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                      Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                      Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                      (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                      Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                      Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                      (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                   else 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                    Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
                else if (find t1 env) andalso not (find t2 env) then
                    let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SUB,10,8,9)))::
                        Assem.INSTRUCTION(Assem.store(10,29,tmp * 4))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end

         | RTL.UNARY(RTL.LOAD(ty),tm) => (* load byte and long in differernt way *)
             if ty = RTL.BYTE then 
               let val env' = insert tmp env
                   val bEnv' = insert tmp bEnv 
                   val (findTm,index) = find_index tm frmsIndexList 
               in
                 if findTm then 
                    (if find tm varTrack then 
                      let val varTrack' = insert tmp varTrack in
                        Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                        (check_instructions insns frms locals env' varTrack' bEnv' frmsIndexList bogus)
                      end
                    else  
                      Assem.INSTRUCTION(Assem.load(8,30,index*4))::
                      Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                      (check_instructions insns frms locals env' varTrack bEnv' frmsIndexList bogus))
                 else if find tm varTrack then 
                   let val varTrack' = insert tmp varTrack in
                      Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                      Assem.INSTRUCTION(Assem.load(8,8,0))::
                      Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                      (check_instructions insns frms locals env' varTrack' bEnv' frmsIndexList bogus)
                   end 
                 else if bogus = 1 then 
                   Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                   Assem.INSTRUCTION(Assem.load(8,8,0))::                 
                   Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                   (check_instructions insns frms locals env' varTrack bEnv' frmsIndexList bogus)
                 else 
                 Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (check_instructions insns frms locals env' varTrack bEnv' frmsIndexList bogus)
               end
             else
                let val env' = insert tmp env
                    val (findTm,index) = find_index tm frmsIndexList 
               in
                 if findTm then 
                   Assem.INSTRUCTION(Assem.load(8,30,index*4))::
                   Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                   (check_instructions insns frms locals env' varTrack bEnv frmsIndexList bogus)
                 else if find tm varTrack then 
                   let val varTrack' = insert tmp varTrack in
                     Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                     Assem.INSTRUCTION(Assem.load(8,8,0))::
                     Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                     (check_instructions insns frms locals env' varTrack' bEnv frmsIndexList bogus)
                   end 
                 else if bogus = 1 then 
                   Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                   Assem.INSTRUCTION(Assem.load(8,8,0))::                 
                   Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                   (check_instructions insns frms locals env' varTrack bEnv frmsIndexList bogus)
                 else
                   Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                   Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                   (check_instructions insns frms locals env' varTrack bEnv frmsIndexList bogus)
               end
         
         | RTL.LABREF (lb) => 
               if (String.isPrefix "V" lb) then 
                 let val varTrack' = insert tmp varTrack
               in
                 Assem.INSTRUCTION(Assem.OPER(Assem.LA(8,lb)))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (check_instructions insns frms locals env varTrack' bEnv frmsIndexList bogus)
               end   
               else 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LA(8,lb)))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)       
         | RTL.ICON (i) => 
               Assem.INSTRUCTION(Assem.load_imm(8,i))::
               Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
               (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
         | RTL.TEMP (tm) => 
               if tmp = 0 then 
                 Assem.INSTRUCTION(Assem.load(8,29,tm*4))::
                 Assem.INSTRUCTION(Assem.store(8,29,12))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
               else if tm = 2 then 
                 Assem.INSTRUCTION(Assem.load_imm(8,1))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
               else if tm = 3 then
                 Assem.INSTRUCTION(Assem.load_imm(8,0))::
                 Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
               else if find tm bEnv then 
                 Assem.INSTRUCTION(Assem.load(9,29,tm*4))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                 Assem.INSTRUCTION(Assem.load(8,29,tmp*4))::
                 Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.SB(8,Assem.OFFSET(29,tmp*4))))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
               else 
                 let val (findTmp1,index1) = find_index tm frmsIndexList
                     val (findTmp2,index2) = find_index tmp frmsIndexList 
                 in
                   if findTmp1 andalso findTmp2 then 
                     Assem.INSTRUCTION(Assem.load(9,30,index1*4))::
                     Assem.INSTRUCTION(Assem.load(8,30,index2*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,30,index2*4))::
                     (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                   else if findTmp1 andalso not findTmp2 then                   
                     Assem.INSTRUCTION(Assem.load(9,30,index1*4))::
                     Assem.INSTRUCTION(Assem.load(8,29,tmp*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                     (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                   else if not findTmp1 andalso findTmp2 then                   
                     Assem.INSTRUCTION(Assem.load(9,29,tm*4))::
                     Assem.INSTRUCTION(Assem.load(8,30,index2*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,30,index2*4))::
                     (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                   else if find tm varTrack then 
                     Assem.INSTRUCTION(Assem.load(9,29,tm*4))::
                     Assem.INSTRUCTION(Assem.load(9,9,0))::
                     Assem.INSTRUCTION(Assem.load(8,29,tmp*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                     (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                   else 
                     Assem.INSTRUCTION(Assem.load(9,29,tm*4))::
                     Assem.INSTRUCTION(Assem.load(8,29,tmp*4))::
                     Assem.INSTRUCTION(Assem.MOVE(Assem.IMOVE(8,9)))::
                     Assem.INSTRUCTION(Assem.store(8,29,tmp*4))::
                     (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                 end)
  | check_instructions ((RTL.CJUMP (relop,t1,t2,label))::insns) frms locals env varTrack bEnv frmsIndexList bogus = 
            case relop of 
              RTL.GT => 
              if t2 = 1 then 
                (if find t1 bEnv then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,4*t1))))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                else 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))

              else if (find t1 env) andalso (find t2 env) then 
                     (if not (find t1 bEnv) andalso not (find t2 bEnv) then 
                       Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                       Assem.INSTRUCTION(Assem.load(8,8,0))::
                       Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                       Assem.INSTRUCTION(Assem.load(9,9,0))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                       Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                       (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                     else if find t1 bEnv andalso not (find t2 bEnv) then 
                       Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                       Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                       Assem.INSTRUCTION(Assem.load(9,9,0))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                       Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                       (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                     else if not (find t1 bEnv) andalso find t2 bEnv then
                       Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                       Assem.INSTRUCTION(Assem.load(8,8,0))::
                       Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                       Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                       (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                     else 
                       Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                       Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                       Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                       Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                       (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))


              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then
                        (if find t1 bEnv andalso find t2 bEnv then    
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else if find t1 bEnv andalso not (find t2 bEnv) then
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                          else if not (find t1 bEnv) andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                          else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))

                      else 
                        (if find t1 bEnv andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else if find t1 bEnv andalso not (find t2 bEnv) then 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else if not (find t2 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)

                         else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        (if find t2 bEnv andalso find t1 bEnv then  
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,4*index))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else if not (find t1 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                          else if find t1 bEnv andalso not (find t2 bEnv) then
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                          else 
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))

                      else 
                        (if find t2 bEnv andalso find t1 bEnv then 
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else if find t1 bEnv andalso not (find t2 bEnv) then 
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.load(9,9,0))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else if not (find t1 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else
                           Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))

                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        (if find t1 bEnv andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,index1*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)

                         else if not(find t1 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)

                         else if find t1 bEnv andalso not (find t2 bEnv) then 
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,index1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)

                         else 
                           Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                           Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
 
                      else if findTm1 andalso not findTm2 then 
                        (if find t1 bEnv andalso find t2 bEnv then  
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,index1*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else if not (find t1 bEnv) andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else if find t1 bEnv andalso not (find t2 bEnv) then
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(30,index1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else
                           Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)) 
 
                      else if not(findTm1) andalso findTm2 then 
                        (if find t1 bEnv andalso find t2 bEnv then   
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else if not (find t1 bEnv) andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(30,index2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else if find t1 bEnv andalso not (find t2 bEnv) then

                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
                      else 
                        (if find t1 bEnv andalso find t2 bEnv then
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else if find t1 bEnv andalso not (find t2 bEnv) then
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(29,t1*4))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else if not (find t1 bEnv) andalso find t2 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(29,t2*4))))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
                    end

           | RTL.GE => 

              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso (find t2 env) then 
                    if find t1 bEnv then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                   else
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        (if find t2 varTrack then 
                          Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else
 
                          Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.load(9,9,0))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
 
                      else 
                        (if find t2 varTrack then 
                          Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else 
                          Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.load(9,9,0))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))

                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SGE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end


            | RTL.NE => 
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso (find t2 env) then 

                   if find t1 bEnv then
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                  else 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
 
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if find t1 bEnv then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SNE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end

            | RTL.EQ => 
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso (find t2 env) then 

                   if find t1 bEnv then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                   else 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if find t1 bEnv then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        (if find t2 bEnv then  
                          Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else
                          Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.load(9,9,0))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))  

                      else 
                        (if find t2 bEnv then 
                          Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else 
                          Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                          Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                          Assem.INSTRUCTION(Assem.load(9,9,0))::
                          Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                          Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                          (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SEQ,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end

            | RTL.LE => 
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso (find t2 env) then 
                    if find t1 bEnv then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    else 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then 
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLE,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end

            | RTL.LT => 
              if t2 = 1 then 
                 Assem.INSTRUCTION(Assem.OPER(Assem.LEA(8,Assem.OFFSET(Assem.FP,0))))::
                 Assem.INSTRUCTION(Assem.load(9,29,4*t1))::
                 Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                 Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::

                 (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso (find t2 env) then 
                    Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                    Assem.INSTRUCTION(Assem.load(8,8,0))::
                    Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                    Assem.INSTRUCTION(Assem.load(9,9,0))::
                    Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                    Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                    (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
              else if (find t1 env) andalso not (find t2 env) then
                   let val (findTm,index) = find_index t2 frmsIndexList
                    in 
                      if findTm then  
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(8,8,0))::
                        Assem.INSTRUCTION(Assem.load(9,30,index*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        (if find t1 bEnv then 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.LB(8,Assem.OFFSET(8,0))))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                         else 
                           Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                           Assem.INSTRUCTION(Assem.load(8,8,0))::
                           Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                           Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                           Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                           (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
                    end
               else if not (find t1 env) andalso (find t2 env) then
                    let val (findTm,index) = find_index t1 frmsIndexList
                    in
                      if findTm then
                        (if find t2 bEnv then  
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.load(9,9,0))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else
                        Assem.INSTRUCTION(Assem.load(8,30,4*index))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
 
                      else 
                        (if find t2 bEnv then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.LB(9,Assem.OFFSET(9,0))))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                        else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        (*Assem.INSTRUCTION(Assem.load(9,9,0))::*)
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus))
                    end
               else 
                    let val (findTm1,index1) = find_index t1 frmsIndexList
                        val (findTm2,index2) = find_index t2 frmsIndexList
                    in
                      if findTm1 andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if findTm1 andalso not findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,30,index1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else if not(findTm1) andalso findTm2 then 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,30,index2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                      else 
                        Assem.INSTRUCTION(Assem.load(8,29,t1*4))::
                        Assem.INSTRUCTION(Assem.load(9,29,t2*4))::
                        Assem.INSTRUCTION(Assem.OPER(Assem.OP(Assem.SLT,10,8,9)))::
                        Assem.INSTRUCTION(Assem.JUMP(Assem.B2(Assem.BNE,10,0,label)))::
                        (check_instructions insns frms locals env varTrack bEnv frmsIndexList bogus)
                    end

  fun procedure_to_asm "Pcheck" formals locals frameSize insns env varTrack bEnv = 
      let 
		  val i = length(locals)*16 + length(formals)*16 + frameSize*16 + 2024 (* the size of stack *)
		  val cntr = ref 0
		  val frmsIndexList = make_index_list formals cntr
		  val bogus = 1
      in 
		  Assem.TEXT::Assem.INSTRUCTION(Assem.label("Pcheck"))::
		  calle_save(i)@(check_instructions insns formals locals env varTrack bEnv frmsIndexList bogus)
          @return_inst(i)
      end
    | procedure_to_asm label formals locals frameSize insns env varTrack bEnv =
	  let 
		  val i = length(locals)*16 + length(formals)*16 + frameSize*16 + 2024 (* the size of stack *)
		  val cntr = ref 0
		  val frmsIndexList = make_index_list formals cntr
		  val bogus = 0
	  in 
		  Assem.TEXT::Assem.INSTRUCTION(Assem.label(label))::
		  calle_save(i)@(check_instructions insns formals locals env varTrack bEnv frmsIndexList bogus)
          @return_inst(i)
	  end

  fun data label size = 
      Assem.DATASEG::
      Assem.ALIGN(2)::
      Assem.INSTRUCTION(Assem.LABEL(label))::
      [Assem.SPACE(size)]

  fun rtl_to_asm (RTL.DATA {label,size}) _ _ _ = data label size 
    | rtl_to_asm (RTL.PROC {label,formals,locals,frameSize,insns}) env varTrack bEnv = 
      procedure_to_asm label formals locals frameSize insns env varTrack bEnv

  fun program_to_asm (RTL.PROGRAM([])) _ _ _ = system_calls ()
    | program_to_asm (RTL.PROGRAM(d::dlist)) env varTrack bEnv = 
      (rtl_to_asm d env varTrack bEnv)@(program_to_asm (RTL.PROGRAM(dlist)) env varTrack bEnv)

  (* main program with empty lists as initials *)
  fun program p = program_to_asm p [] [] []


end 
