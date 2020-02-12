structure LambdaFlx : LAMBDAFLX =
struct
        datatype lterm = term (* term from FLX *)
                   | VAR of string      (* variables *)
                   | Z                  (* zero *)
                   | T                  (* true *)
                   | F                  (* false *)
                   | P of lterm         (* Predecessor *)
                   | S of lterm         (* Successor *)
                   | ITE of lterm * lterm * lterm       (* If then else *)
                   | IZ of lterm        (* is zero *)
                   | GTZ of lterm       (* is greater than zero *)
                   | LAMBDA of lterm * lterm    (* lambda x [lterm] *)
                   | APP of lterm * lterm       (* application of lambda terms, i.e. (L M) *);

        exception Not_wellformed;
        exception Not_nf;
        exception Not_int;
        exception Not_welltyped;


        fun removeSpaces charList =             if hd(charList) = #" " then removeSpaces (tl(charList))
                                                else charList;

        fun checkIfVar (a :: []) =              if ord(a) >= 97 andalso ord(a) <= 122 then true
                                                else false
          | checkIfVar (a::b) =                 if ord(a) >= 97 andalso ord(a) <= 122 then checkIfVar b
                                                else false
          | checkIfVar (_) =                    false;

        fun checkVarTerm (a :: (#")" :: b)) =   if ord(a) >= 97 andalso ord(a) <= 122 then true
                                                else false
          | checkVarTerm (a :: (#"]" :: b)) =   if ord(a) >= 97 andalso ord(a) <= 122 then true
                                                else false
          | checkVarTerm (a :: b) =             if ord(a) >= 97 andalso ord(a) <= 122
                                                then checkVarTerm b
                                                else false;

        fun getVarTerm (charList,opList) =      if hd(charList) = #")" then (opList,charList)
                                                else if hd(charList) = #"]" then (opList,charList)
                                                else getVarTerm(tl(charList),hd(charList) :: opList);

        fun checkVarITETerm (a :: (#"," :: b))= if ord(a) >= 97 andalso ord(a) <= 122 then true
                                                else false
          | checkVarITETerm (a :: b) =          if ord(a) >= 97 andalso ord(a) <= 122
                                                then checkVarITETerm b
                                                else false;

        fun getVarITETerm (charList,opList) =   if hd(charList) = #"," then (opList,charList)
                                                else getVarITETerm(tl(charList),hd(charList) :: opList);

        fun checkVarITETerm3 (a :: (#">" :: b))=if ord(a) >= 97 andalso ord(a) <= 122 then true
                                                else false
          | checkVarITETerm3 (a :: b) =         if ord(a) >= 97 andalso ord(a) <= 122
                                                then checkVarITETerm3 b
                                                else false;

        fun getVarITETerm3 (charList,opList) =  if hd(charList) = #">" then (opList,charList)
                                                else getVarITETerm3(tl(charList),hd(charList) :: opList);

        fun checkVarLterm (a :: (#" " :: b)) =  if ord(a) >= 97 andalso ord(a) <= 122 then true
                                                else false
          | checkVarLterm (a :: b) =            if ord(a) >= 97 andalso ord(a) <= 122 then checkVarLterm b
                                                else false;

        fun getVarLterm (charList,opList) =     if hd(charList) = #" " then (opList,charList)
                                                else getVarLterm(tl(charList),hd(charList) :: opList);

        fun getITETerm1 charList =              if hd(charList) = #"<" then
                                                        if checkVarITETerm (tl(charList)) = true then
                                                          let val (term1,suffix) = getVarITETerm (tl(charList),[])
                                                          in (VAR(implode(List.rev(term1))),tl(suffix))
                                                          end
                                                        else
                                                          let val (term1,suffix) = getTerm (tl(charList))
                                                          in if hd(suffix) = #"," then (term1,tl(suffix))
                                                             else raise Not_wellformed
                                                          end
                                                else raise Not_wellformed

        and getITETerm2 charList =              if checkVarITETerm charList = true then
                                                        let val (term2,suffix) = getVarITETerm (charList,[])
                                                        in (VAR(implode(List.rev(term2))),tl(suffix))
                                                        end
                                                else
                                                        let val (term2,suffix) = getTerm charList
                                                        in if hd(suffix) = #"," then (term2,tl(suffix))
                                                           else raise Not_wellformed
                                                        end


        and getITETerm3 charList =              if checkVarITETerm3 charList = true then
                                                        let val (term3,suffix) = getVarITETerm3 (charList,[])
                                                        in (VAR(implode(List.rev(term3))),tl(suffix))
                                                        end
                                                else
                                                        let val (term3,suffix) = getTerm charList
                                                        in if hd(suffix) = #">" then (term3,tl(suffix))
                                                           else raise Not_wellformed
                                                        end

        and getLterm0 (charList,opList) =       if ord(hd(charList)) >= 97 andalso ord(hd(charList)) <= 122 then getLterm0 (tl(charList),hd(charList) :: opList)
                                                else (opList,charList)

        and getTerm charList =                  if hd(charList) = #"Z" then (Z,tl(charList))

                                                else if hd(charList) = #"T" then (T,tl(charList))

                                                else if hd(charList) = #"F" then (F,tl(charList))

                                                (*for VAR*)
                                                else if checkVarTerm charList = true then
                                                        let val (lTerm,suffix) = getVarTerm (charList,[])
                                                        in (VAR(implode(List.rev(lTerm))),suffix)
                                                        end

                                                else if hd(charList) = #"("then
                                                        (*for P*)
                                                        if hd(tl(charList)) = #"P" andalso hd(tl(tl(charList))) = #" "then
                                                                let val inTerm = removeSpaces (tl(tl(charList)))
                                                                    val (lTerm,suffix) = getTerm inTerm
                                                                in if hd(suffix) = #")" then (P(lTerm),tl(suffix))
                                                                else raise Not_wellformed
                                                                end

                                                        (*for S*)
                                                        else if hd(tl(charList)) = #"S" andalso hd(tl(tl(charList))) = #" " then
                                                                let val inTerm = removeSpaces (tl(tl(charList)))
                                                                    val (lTerm,suffix) = getTerm inTerm
                                                                in if hd(suffix) = #")" then (S(lTerm),tl(suffix))
                                                                   else raise Not_wellformed
                                                                end

                                                        (*for IZ*)
                                                        else if hd(tl(charList)) = #"I" andalso hd(tl(tl(charList))) = #"Z" andalso hd(tl(tl(tl(charList)))) = #" " then
                                                                let val inTerm = removeSpaces (tl(tl(tl(charList))))
                                                                    val (lTerm,suffix) = getTerm inTerm
                                                                in if hd(suffix) = #")" then (IZ(lTerm),tl(suffix))
                                                                   else raise Not_wellformed
                                                                end

                                                        (*for GTZ*)
                                                        else if hd(tl(charList)) = #"G" andalso hd(tl(tl(charList))) = #"T" andalso hd(tl(tl(tl(charList)))) = #"Z" andalso hd(tl(tl(tl(tl(charList))))) = #" " then
                                                                let val inTerm = removeSpaces (tl(tl(tl(tl(charList)))))
                                                                    val (lTerm,suffix) = getTerm inTerm
                                                                in if hd(suffix) = #")" then (GTZ(lTerm),tl(suffix))
                                                                   else raise Not_wellformed
                                                                end

                                                        (*for ITE*)
                                                        else if hd(tl(charList)) = #"I" andalso hd(tl(tl(charList))) = #"T" andalso hd(tl(tl(tl(charList)))) = #"E" andalso hd(tl(tl(tl(tl(charList))))) = #" "then
                                                                let val inTerm = removeSpaces (tl(tl(tl(tl(charList)))))
                                                                    val (term1,suffix1) = getITETerm1 inTerm
                                                                    val (term2,suffix2) = getITETerm2 suffix1
                                                                    val (term3,suffix3) = getITETerm3 suffix2
                                                                in if hd(suffix3) = #")" then (ITE(term1,term2,term3),tl(suffix3))
                                                                   else raise Not_wellformed
                                                                end
                                                        (*for APP*)
                                                        else if hd(tl(charList)) = #"(" orelse hd(tl(charList)) = #"Z" orelse hd(tl(charList)) = #"T" orelse hd(tl(charList)) = #"F" then
                                                                (case hd(tl(charList)) of 
                                                                      #"Z" => if hd(tl(tl(charList))) = #" " then
                                                                                let val (rterm,suffix) = getTerm (tl(tl(tl(charList))))
										in if hd(suffix) = #")" then (APP(Z,rterm),tl(suffix))
										   else raise Not_wellformed
										end
									      else raise Not_wellformed
								    | #"T" => if hd(tl(tl(charList))) = #" " then
                                                                                let val (rterm,suffix) = getTerm (tl(tl(tl(charList))))
										in if hd(suffix) = #")" then (APP(T,rterm),tl(suffix))
										   else raise Not_wellformed
										end
									      else raise Not_wellformed
								    | #"F" => if hd(tl(tl(charList))) = #" " then
                                                                                let val (rterm,suffix) = getTerm (tl(tl(tl(charList))))
										in if hd(suffix) = #")" then (APP(F,rterm),tl(suffix))
										   else raise Not_wellformed
										end
									      else raise Not_wellformed
								    | #"(" => let val (lterm,lsuffix) = getTerm (tl(charList))
									      in if hd(lsuffix) = #" " then 
											let val (rterm,rsuffix) = getTerm (tl(lsuffix))
											in if hd(rsuffix) = #")" then (APP(lterm,rterm),tl(rsuffix))
											   else raise Not_wellformed
											end
										 else raise Not_wellformed
									      end
                                                                )
                                                        
                                                        else if checkVarLterm (tl(charList)) = true then
                                                                let val (lterm,lsuffix) = getVarLterm (tl(charList),[])
                                                                    val (rterm,rsuffix) = getTerm (tl(lsuffix))
                                                                in if hd(rsuffix) = #")" then (APP(VAR(implode(List.rev(lterm))),rterm),tl(rsuffix))
                                                                   else raise Not_wellformed
                                                                end
                                                        
                                                        else if String.extract(implode(tl(charList)),0,SOME 7) = "LAMBDA " then 
                                                                let val interm = removeSpaces (tl(tl(tl(tl(tl(tl(tl(charList))))))))
                                                                    val (lterm0,lsuffix) = getLterm0 (interm,[])
                                                                in if hd(lsuffix) = #"[" then
                                                                        let val (lterm1,suffix) = getTerm (tl(lsuffix))
                                                                        in if hd(suffix) = #"]" andalso hd(tl(suffix)) = #" "  then 
                                                                                let val (rterm,rsuffix) = getTerm (tl(tl(suffix)))
								                in if hd(rsuffix) = #")" then (APP(LAMBDA(VAR(implode(List.rev(lterm0))),lterm1),rterm),tl(rsuffix))
                                                                                   else raise Not_wellformed
                                                                                end
                                                                           else raise Not_wellformed
                                                                        end
                                                                   else raise Not_wellformed
                                                                end
                                                        
                                                        else raise Not_wellformed

                                                (*for Lambda Term*)
                                                else if hd(charList) = #"L" then
                                                        let val interm = removeSpaces (tl(tl(tl(tl(tl(tl(charList)))))))
                                                            val (lterm0,lsuffix) = getLterm0 (interm,[])
                                                        in if hd(lsuffix) = #"[" then
                                                                let val (lterm1,suffix) = getTerm (tl(lsuffix))
                                                                in if hd(suffix) = #"]" then (LAMBDA(VAR(implode(List.rev(lterm0))),lterm1),tl(suffix))
                                                                   else raise Not_wellformed
                                                                end
                                                           else raise Not_wellformed
                                                        end
                                                 
                                                else raise Not_wellformed;

        fun fromString "Z" =                    Z
          | fromString "T" =                    T
          | fromString "F" =                    F
          | fromString ipString =               if String.sub(ipString,0) = #"(" then
                                                        let val charList = explode(ipString)
                                                            val (lTerm,suffix) = getTerm charList
                                                        in if suffix = [] then lTerm
                                                           else raise Not_wellformed
                                                        end

                                                else if String.extract(ipString,0,SOME 1) = "L" then
                                                        let val charList = explode(ipString)
                                                            val (lTerm,suffix) = getTerm charList
                                                        in if suffix = [] then lTerm 
                                                           else raise Not_wellformed
                                                        end
                                                           
                                                else
                                                        let val charList = explode(ipString)
                                                            val ifVar = checkIfVar charList
                                                        in if ifVar = true then VAR(ipString)
                                                           else raise Not_wellformed
                                                        end;

        fun toString (VAR(x)) =                 x
          | toString (Z) =                      "Z"
          | toString (T) =                      "T"
          | toString (F) =                      "F"
          | toString (P(x)) =                   "(P " ^ toString(x) ^ ")"
          | toString (S(x)) =                   "(S " ^ toString(x) ^ ")"
          | toString (IZ(x)) =                  "(IZ " ^ toString(x) ^ ")"
          | toString (GTZ(x)) =                 "(GTZ " ^ toString(x) ^ ")"
          | toString (ITE(x,y,z)) =             "(ITE <" ^ toString(x) ^ "," ^ toString(y) ^ "," ^ toString(z) ^ ">)"
          | toString (LAMBDA(VAR(x),y)) =       "LAMBDA " ^ x ^ "[" ^ toString(y) ^ "]"
          | toString (LAMBDA(_,_)) =            raise Not_wellformed
          | toString (APP(x,y)) =               "(" ^ toString(x) ^ " " ^ toString(y) ^ ")";

        fun fromInt num =                       if num < 0 then P(fromInt (num+1))
                                                else if num > 0 then S(fromInt (num-1))
                                                else Z;

        fun checkForOnlySPZ (Z) =               true
          | checkForOnlySPZ (S(x)) =            checkForOnlySPZ (x)
          | checkForOnlySPZ (P(x)) =            checkForOnlySPZ (x)
          | checkForOnlySPZ (_) =               false;

        fun toPosInt (Z) =                      0
          | toPosInt (S(x)) =                   toPosInt(x) + 1
          | toPosInt (P(x)) =                   if checkForOnlySPZ (x) = true then raise Not_nf
                                                else raise Not_int
          | toPosInt (_) =                      raise Not_int;

        fun toNegInt (Z) =                      0
          | toNegInt (P(x)) =                   toNegInt(x) - 1
          | toNegInt (S(x)) =                   if checkForOnlySPZ (x) = true then raise Not_nf
                                                else raise Not_int
          | toNegInt (_) =                      raise Not_int;

        fun toInt Z =                           0
          | toInt (S(x)) =                      toPosInt (x) + 1
          | toInt (P(x)) =                      toNegInt (x) - 1
          | toInt(_) =                          raise Not_int;

        fun findVar ([],x) =                            (false," ")
          | findVar (container,x) =                     (case hd(container) of 
                                                                 (m,n) => if n = x then (true,m)
                                                                          else findVar (tl(container),x)
                                                                          )

        fun alphaRename (VAR(x),count,container1,container2) =                  let val (value,newVar) =  findVar (container1,x)
                                                                                in if value = true then (VAR(newVar),container2,count)
                                                                                   else (VAR(x),container2,count)
                                                                                end
          | alphaRename (Z,count,container1,container2) =                       (Z,container2,count)
          | alphaRename (T,count,container1,container2) =                       (T,container2,count)
          | alphaRename (F,count,container1,container2) =                       (F,container2,count)
          | alphaRename (P(lTerm),count,container1,container2) =                let val (newTerm,newContainer,newCount) = alphaRename (lTerm,count,container1,container2)
							                        in (P(newTerm),newContainer,newCount)
                                                                                end
          | alphaRename (S(lTerm),count,container1,container2) =                let val (newTerm,newContainer,newCount) = alphaRename (lTerm,count,container1,container2)
							                        in (S(newTerm),newContainer,newCount)
                                                                                end
          | alphaRename (IZ(lTerm),count,container1,container2) =               let val (newTerm,newContainer,newCount) = alphaRename (lTerm,count,container1,container2)
							                        in (IZ(newTerm),newContainer,newCount)
							                        end
          | alphaRename (GTZ(lTerm),count,container1,container2) =              let val (newTerm,newContainer,newCount) = alphaRename (lTerm,count,container1,container2)
							                        in (GTZ(newTerm),newContainer,newCount)
							                        end
          | alphaRename (ITE(lTerm1,lTerm2,lTerm3),count,container1,container2)=
                                                                                let val (term1,newContainer1,newCount1) = alphaRename (lTerm1,count,container1,container2)
                                                                                    val (term2,newContainer2,newCount2) = alphaRename (lTerm2,newCount1,container1,newContainer1)
										    val (term3,newContainer3,newCount3) = alphaRename (lTerm3,newCount2,container1,newContainer2)
										in (ITE(term1,term2,term3),newContainer3,newCount3)
										end                                                                                
          | alphaRename (LAMBDA(VAR(x),lTerm2),count,container1,container2) =   let val newCount = count+1
									            val newPair as (el1,el2) = ("t"^Int.toString(newCount),x)
									            val (newTerm,newContainer,newCount1) = alphaRename (lTerm2,newCount,newPair :: container1,newPair :: container2)
                                                                                in (LAMBDA(VAR(el1),newTerm),newContainer,newCount1)
									        end
          | alphaRename (LAMBDA(_,_),count,container1,container2) =             raise Not_wellformed
          | alphaRename (APP(lTerm1,lTerm2),count,container1,container2) =      let val (term1,newContainer1,newCount1) = alphaRename (lTerm1,count,container1,container2)
                                                                                    val (term2,newContainer2,newCount2) = alphaRename (lTerm2,newCount1,container1,newContainer1)
										in (APP(term1,term2),newContainer2,newCount2)
										end
        fun assignVarType (x,tType,[]) =                        (true,[(x,tType)])
          | assignVarType (x,"intvar",ipList) =                 (case hd(ipList) of 
                                                                      (var,typ) =>    if var = x then
                                                                                                if typ = "intvar" then (true,ipList)
                                                                                                else if typ = "var" then
                                                                                                        let val newType = "intvar"
                                                                                                        in (true, (var,newType) :: tl(ipList))
                                                                                                        end 
                                                                                                else (false,ipList)
                                                                                      else
                                                                                        let val (value,opList) = assignVarType(x,"intvar",tl(ipList))
                                                                                        in (value,hd(ipList)::opList)
                                                                                        end
                                                                )
          | assignVarType (x,"boolvar",ipList) =                (case hd(ipList) of 
                                                                      (var,typ) =>    if var = x then
                                                                                                if typ = "boolvar" then (true,ipList)
                                                                                                else if typ = "var" then
                                                                                                        let val newType = "boolvar"
                                                                                                        in (true, (var,newType) :: tl(ipList))
                                                                                                        end 
                                                                                                else (false,ipList)
                                                                                      else
                                                                                        let val (value,opList) = assignVarType(x,"boolvar",tl(ipList))
                                                                                        in (value,hd(ipList)::opList)
                                                                                        end
                                                                )
          | assignVarType (x,"var",ipList) =                    (case hd(ipList) of 
                                                                      (var,typ) =>    if var = x then (true,ipList)
                                                                                      else
                                                                                        let val (value,opList) = assignVarType(x,"var",tl(ipList))
                                                                                        in (value,hd(ipList)::opList)
                                                                                        end
                                                                )

        fun findType(x,ipList) =                                (case hd(ipList) of 
                                                                      (var,typ) =>    if var = x then typ
                                                                                      else
                                                                                        findType (x,tl(ipList))
                                                                                        )


        fun checkTermType (VAR(x),typeList) =                   let val (value,opList) = assignVarType (x,"var",typeList)
                                                                in if value = true then (true,"var",opList)
                                                                   else (false,"incorrect",opList)
                                                                end 
          | checkTermType (Z,typeList) =                        (true,"int",typeList)
          | checkTermType (T,typeList) =                        (true,"bool",typeList)
          | checkTermType (F,typeList) =                        (true,"bool",typeList)
          | checkTermType (S(lTerm),typeList) =                 (case lTerm of 
                                                                        Z =>              (true,"int",typeList)
                                                                      | T =>              (false,"incorrect",typeList)
                                                                      | F =>              (false,"incorrect",typeList)
                                                                      | IZ(_) =>          (false,"incorrect",typeList)
                                                                      | GTZ(_) =>         (false,"incorrect",typeList) 
                                                                      | LAMBDA(_,_) =>    (false,"incorrect",typeList)
                                                                      | VAR(var) =>       let val (value,opList) = assignVarType (var,"intvar",typeList)
                                                                                          in if value = true then (true,"int",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end 
                                                                      | (_) =>            let val (value,tType,opList) =  checkTermType (lTerm,typeList)
                                                                                          in if tType = "int" then (true,"int",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                )
          | checkTermType (P(lTerm),typeList) =                 (case lTerm of 
                                                                        Z =>              (true,"int",typeList)
                                                                      | T =>              (false,"incorrect",typeList)
                                                                      | F =>              (false,"incorrect",typeList)
                                                                      | IZ(_) =>          (false,"incorrect",typeList)
                                                                      | GTZ(_) =>         (false,"incorrect",typeList) 
                                                                      | LAMBDA(_,_) =>    (false,"incorrect",typeList)
                                                                      | VAR(var) =>       let val (value,opList) = assignVarType (var,"intvar",typeList)
                                                                                          in if value = true then (true,"int",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                      | (_) =>            let val (value,tType,opList) =  checkTermType (lTerm,typeList)
                                                                                          in if tType = "int" then (true,"int",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                )
          | checkTermType (IZ(lTerm),typeList) =                (case lTerm of 
                                                                        Z =>              (true,"bool",typeList)
                                                                      | T =>              (false,"incorrect",typeList)
                                                                      | F =>              (false,"incorrect",typeList)
                                                                      | IZ(_) =>          (false,"incorrect",typeList)
                                                                      | GTZ(_) =>         (false,"incorrect",typeList) 
                                                                      | LAMBDA(_,_) =>    (false,"incorrect",typeList)
                                                                      | VAR(var) =>       let val (value,opList) = assignVarType (var,"intvar",typeList)
                                                                                          in if value = true then (true,"bool",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                      | (_) =>            let val (value,tType,opList) =  checkTermType (lTerm,typeList)
                                                                                          in if tType = "int" then (true,"bool",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                )
          | checkTermType (GTZ(lTerm),typeList) =               (case lTerm of 
                                                                        Z =>              (true,"bool",typeList)
                                                                      | T =>              (false,"incorrect",typeList)
                                                                      | F =>              (false,"incorrect",typeList)
                                                                      | IZ(_) =>          (false,"incorrect",typeList)
                                                                      | GTZ(_) =>         (false,"incorrect",typeList)
                                                                      | LAMBDA(_,_) =>    (false,"incorrect",typeList)
                                                                      | VAR(var) =>       let val (value,opList) = assignVarType (var,"intvar",typeList)
                                                                                          in if value = true then (true,"bool",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                      | (_) =>            let val (value,tType,opList) =  checkTermType (lTerm,typeList)
                                                                                          in if tType = "int" then (true,"bool",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                )
          | checkTermType (ITE(lTerm1,lTerm2,lTerm3),typeList) =  
                                                                let val (term1Type,opList1) =
                                                                        (case lTerm1 of
                                                                                Z =>              ("incorrect",typeList)
                                                                              | T =>              ("bool",typeList)
                                                                              | F =>              ("bool",typeList)
                                                                              | VAR(var) =>       let val (value,opList) = assignVarType (var,"boolvar",typeList)
                                                                                                  in if value = true then ("bool",opList)
                                                                                                     else ("incorrect",opList)
                                                                                                  end
                                                                              | LAMBDA(_,_) =>    ("incorrect",typeList)
                                                                              | (_) =>            let val (value,tType,opList) =  checkTermType (lTerm1,typeList)
                                                                                                  in if tType = "bool" then ("bool",opList)
                                                                                                     else ("incorrect",opList)
                                                                                                  end
                                                                        )
                                                                    val (term2Type,opList2) = 
                                                                        (case lTerm2 of
                                                                                Z =>              ("int",opList1)
                                                                              | T =>              ("bool",opList1)
                                                                              | F =>              ("bool",opList1)
                                                                              | VAR(var) =>       let val (value,opList) = assignVarType (var,"var",opList1)
                                                                                                  in if value = true then 
                                                                                                        let val typeV = findType(var,opList)
                                                                                                        in (typeV,opList)
                                                                                                        end
                                                                                                     else ("incorrect",opList)
                                                                                                  end
                                                                              | LAMBDA(_,_) =>    ("incorrect",opList1)
                                                                              | (_) =>            let val (value,tType,opList) =  checkTermType (lTerm2,opList1)
                                                                                                  in if tType = "bool" then ("bool",opList)
                                                                                                     else if tType = "int" then ("int",opList)
                                                                                                     else ("incorrect",opList)
                                                                                                  end
                                                                        )
                                                                    val (term3Type,opList3) =
                                                                        (case lTerm3 of
                                                                                Z =>              ("int",opList2)
                                                                              | T =>              ("bool",opList2)
                                                                              | F =>              ("bool",opList2)
                                                                              | VAR(var) =>       let val (value,opList) = assignVarType (var,"var",opList2)
                                                                                                  in if value = true then
                                                                                                        let val typeV = findType(var,opList)
                                                                                                        in (typeV,opList)
                                                                                                        end
                                                                                                     else ("incorrect",opList)
                                                                                                  end
                                                                              | LAMBDA(_,_) =>    ("incorrect",opList2)
                                                                              | (_) =>            let val (value,tType,opList) =  checkTermType (lTerm3,opList2)
                                                                                                  in if tType = "bool" then ("bool",opList)
                                                                                                     else if tType = "int" then ("int",opList)
                                                                                                     else ("incorrect",opList)
                                                                                                  end
                                                                        ) 
                                                                in if term1Type = "bool" orelse term1Type = "boolvar" then
                                                                        if term2Type = "bool" andalso term3Type = "bool" then (true,"bool",opList3)
                                                                        else if term2Type = "int" andalso term3Type = "int" then (true,"int",opList3)
                                                                        else if (term2Type = "bool" orelse term2Type = "boolvar") andalso (term3Type = "var" orelse term3Type = "boolvar") then 
                                                                              (case lTerm3 of 
	                                                                        VAR(x) => let val (valV,opList) = assignVarType (x,"boolvar",opList3)
                                                                                          in if valV = true then (true,"bool",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                              )
                                                                        else if (term2Type = "int" orelse term2Type = "intvar") andalso (term3Type = "var" orelse term3Type = "intvar") then
                                                                              (case lTerm3 of 
	                                                                        VAR(x) => let val (valV,opList) = assignVarType (x,"intvar",opList3)
                                                                                          in if valV = true then (true,"int",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                              )
                                                                        else if (term3Type = "int" orelse term3Type = "intvar") andalso (term2Type = "var" orelse term2Type = "intvar") then
                                                                              (case lTerm2 of 
	                                                                        VAR(x) => let val (valV,opList) = assignVarType (x,"intvar",opList3)
                                                                                          in if valV = true then (true,"int",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                              ) 
                                                                        else if (term3Type = "bool" orelse term3Type = "boolvar") andalso (term2Type = "var" orelse term2Type = "boolvar") then 
                                                                              (case lTerm2 of 
	                                                                        VAR(x) => let val (valV,opList) = assignVarType (x,"boolvar",opList3)
                                                                                          in if valV = true then (true,"bool",opList)
                                                                                             else (false,"incorrect",opList)
                                                                                          end
                                                                              ) 
                                                                        else (false,"incorrect",opList3)
                                                                   else (false,"incorrect",opList3)
                                                                end
          
          | checkTermType (LAMBDA(VAR(x),lTerm1),typeList) =    let val (valv,opList) = assignVarType (x,"var",typeList)
                                                                in if valv = true then
                                                                        let val (value,tType,opList1) =  checkTermType (lTerm1,opList)
                                                                        in if value = true then (true,tType,opList1)
                                                                           else (false,"incorrect",opList1)
                                                                        end 
                                                                   else (false,"incorrect",opList)
                                                                end
          | checkTermType (LAMBDA(_,_),typeList) =              raise Not_wellformed
          
          | checkTermType (APP(lTerm1,lTerm2),typeList) =       (case lTerm1 of 
                                                                      LAMBDA(VAR(x),term1) =>   let val (val2,tType2,opList) = checkTermType (lTerm2,typeList)
			                                                                        in if val2 = true then
				                                                                        if tType2 = "int" orelse tType2 = "intvar" then
				                                                                                let val (varval,opListV) = assignVarType (x,"intvar",opList)
				                                                                                    val (val1,tType1,opList1) = checkTermType (term1,opListV)
				                                                                                in if varval = true then
					                                                                                if val1 = true then (true,"int",opList1)
					                                                                                else (false,"incorrect",opList1)
				                                                                                   else (false,"incorrect",opList1)
				                                                                                end
				                                                                        else if tType2 = "bool" orelse tType2 = "boolvar" then
				                                                                                let val (varval,opListV) = assignVarType (x,"boolvar",opList)
				                                                                                    val (val1,tType1,opList1) = checkTermType (term1,opListV)
				                                                                                    in if varval = true then
					                                                                                        if val1 = true then (true,"bool",opList1)
					                                                                                        else (false,"incorrect",opList1)
				                                                                                        else (false,"incorrect",opList1)
				                                                                                    end
				                                                                        else (false,"incorrect",opList)
			                                                                        else (false,"incorrect",opList)
                                                                                                end
                                                                    | APP(_,_) =>               let val (val1,tType1,opList1) = checkTermType (lTerm1,typeList)
                                                                                                    val (val2,tType2,opList2) = checkTermType (lTerm2,opList1)
                                                                                                in if val1 = true andalso val2 = true then (true,tType1,opList2)
                                                                                                   else (false,"incorrect",opList2)
                                                                                                end 
                                                                    | (_) =>                    (false,"incorrect",typeList)
                                                                )
                                                              
        fun isWellTyped ipLterm =               let val (value,tType,opList) = checkTermType (ipLterm,[])
                                                in value
                                                end


        fun checkForOnlySZ Z =                  true
          | checkForOnlySZ (S(term)) =          checkForOnlySZ term
          | checkForOnlySZ (_) =                false;

        fun checkForOnlyPZ Z =                  true
          | checkForOnlyPZ (P(term)) =          checkForOnlyPZ term
          | checkForOnlyPZ (_) =                false;

        fun betaReduce (VAR(x),VAR(y),normalTerm2) =            if x = y then normalTerm2
                                                                else VAR(y)
          | betaReduce (x,Z,normalTerm2) =                      Z
          | betaReduce (x,T,normalTerm2) =                      T
          | betaReduce (x,F,normalTerm2) =                      F
          | betaReduce (x,S(term1),normalTerm2) =               S(betaReduce (x,term1,normalTerm2))
          | betaReduce (x,P(term1),normalTerm2) =               P(betaReduce (x,term1,normalTerm2))
          | betaReduce (x,IZ(term1),normalTerm2) =              IZ(betaReduce (x,term1,normalTerm2))
          | betaReduce (x,GTZ(term1),normalTerm2) =             GTZ(betaReduce (x,term1,normalTerm2))
          | betaReduce (x,ITE(term1,term2,term3),normalTerm2) = ITE(betaReduce (x,term1,normalTerm2),betaReduce (x,term2,normalTerm2),betaReduce (x,term3,normalTerm2))
          | betaReduce (x,LAMBDA(term1,term2),normalTerm2) =    LAMBDA(term1,betaReduce (x,term2,normalTerm2))
          | betaReduce (x,APP(term1,term2),normalTerm2) =       let val nTerm1 = betaReduce (x,term1,normalTerm2)
                                                                    val nTerm2 = betaReduce (x,term2,normalTerm2)
                                                                in APP(nTerm1,nTerm2)
                                                                end
          
        fun betaNF (Z) =                        Z
          | betaNF (T) =                        T
          | betaNF (F) =                        F
          | betaNF (VAR(x)) =                   VAR(x)
          | betaNF (S(x)) =                     let val normalTerm = betaNF (x)
                                                in S(normalTerm)
                                                end
          | betaNF (P(x)) =                     let val normalTerm = betaNF (x)
                                                in P(normalTerm)
                                                end
          | betaNF (IZ(x)) =                    let val normalTerm = betaNF (x)
                                                in IZ(normalTerm)
                                                end
          | betaNF (GTZ(x)) =                   let val normalTerm = betaNF (x)
                                                in GTZ(normalTerm)
                                                end
          | betaNF (ITE(x1,x2,x3)) =            let val normalTerm0 = betaNF(x1)
                                                    val normalTerm1 = betaNF(x2)
                                                    val normalTerm2 = betaNF(x3)
                                                in ITE(normalTerm0,normalTerm1,normalTerm2)
                                                end
          | betaNF (LAMBDA(VAR(x),lterm1)) =    let val normalTerm1 = betaNF (lterm1)
                                                in LAMBDA(VAR(x),normalTerm1)
                                                end
          | betaNF (APP(lTerm1,lTerm2)) =       (case lTerm1 of
                                                      (LAMBDA(x,y)) =>  let val normalTerm1 = betaNF(y)
                                                                            val normalTerm2 = betaNF lTerm2
                                                                        in betaReduce (x,normalTerm1,normalTerm2)
                                                                        end
                                                    | (_) =>            let val normalTerm1 = betaNF lTerm1
                                                                            val normalTerm2 = betaNF lTerm2
                                                                        in APP(normalTerm1,normalTerm2)
                                                                        end
                                                      )

        fun countApps (Z,count) =                               count
          | countApps (T,count) =                               count
          | countApps (F,count) =                               count
          | countApps (VAR(_),count) =                          count
          | countApps (P(lTerm),count) =                        countApps (lTerm,count)
          | countApps (S(lTerm),count) =                        countApps (lTerm,count)
          | countApps (IZ(lTerm),count) =                       countApps (lTerm,count)
          | countApps (GTZ(lTerm),count) =                      countApps (lTerm,count)
          | countApps (ITE(lTerm1,lTerm2,lTerm3),count) =       let val count1 = countApps (lTerm1,count)
                                                                    val count2 = countApps (lTerm2,count1)
                                                                    val count3 = countApps (lTerm3,count2)
                                                                in count3
                                                                end
          | countApps (LAMBDA(VAR(_),lTerm1),count) =           countApps (lTerm1,count)
          | countApps (APP(lTerm1,lTerm2),count) =              let val count1 = countApps (lTerm1,count)
                                                                    val count2 = countApps (lTerm2,count1)
                                                                in count2 + 1
                                                                end

        fun normalize (Z) =                     Z
          | normalize (T) =                     T
          | normalize (F) =                     F
          | normalize (VAR(x)) =                VAR(x)
          | normalize (S(lTerm)) =
                                                let val normalTerm = normalize (lTerm)
                                                in (case normalTerm of
                                                        Z           => S(Z)
                                                      | VAR(var)    => S(normalTerm)
                                                      | T           => raise Not_welltyped
                                                      | F           => raise Not_welltyped
                                                      | S(normTerm) => S(normalTerm)
                                                      | P(normTerm) => if checkForOnlySPZ normTerm = true then normTerm
                                                                       else S(normalTerm)
                                                      | IZ(_)       => raise Not_welltyped
                                                      | GTZ(_)      => raise Not_welltyped
                                                      | LAMBDA(_,_) => raise Not_welltyped
                                                      | (_)         => S(normalTerm)
                                                   )
                                                end
          | normalize (P(lTerm)) =               
                                                let val normalTerm = normalize (lTerm)
                                                in (case normalTerm of
                                                        Z           => P(Z)
                                                      | VAR(var)    => P(normalTerm)
                                                      | T           => raise Not_welltyped
                                                      | F           => raise Not_welltyped
                                                      | P(normTerm) => P(normalTerm)
                                                      | S(normTerm) => if checkForOnlySPZ normTerm = true then normTerm
                                                                       else P(normalTerm)
                                                      | IZ(_)       => raise Not_welltyped
                                                      | GTZ(_)      => raise Not_welltyped
                                                      | LAMBDA(_,_) => raise Not_welltyped
                                                      | (_)         => P(normalTerm)
                                                   )
                                                end
                                                
          | normalize (IZ(lTerm)) =              
                                                let val normalTerm = normalize (lTerm)
                                                in (case normalTerm of
                                                        Z           => T
                                                      | VAR(var)    => IZ(normalTerm)
                                                      | T           => raise Not_welltyped
                                                      | F           => raise Not_welltyped
                                                      | S(normTerm) => if checkForOnlySZ normTerm = true then F
                                                                       else IZ(normalTerm)
                                                      | P(normTerm) => if checkForOnlyPZ normTerm = true then F
                                                                       else IZ(normalTerm)
                                                      | IZ(_)       => raise Not_welltyped
                                                      | GTZ(_)      => raise Not_welltyped
                                                      | LAMBDA(_,_) => raise Not_welltyped
                                                      | (_)         => IZ(normalTerm)
                                                   )
                                                end
          | normalize (GTZ(lTerm)) =            
                                                let val normalTerm = normalize (lTerm)
                                                in (case normalTerm of
                                                         Z           => F
                                                       | VAR(var)    => GTZ(normalTerm)
                                                       | T           => raise Not_welltyped
                                                       | F           => raise Not_welltyped
                                                       | S(normTerm) => if checkForOnlySZ normTerm = true then T
                                                                        else GTZ(normalTerm)
                                                       | P(normTerm) => if checkForOnlyPZ normTerm = true then F
                                                                        else GTZ(normalTerm)
                                                       | IZ(_)       => raise Not_welltyped
                                                       | GTZ(_)      => raise Not_welltyped
                                                       | LAMBDA(_,_) => raise Not_welltyped
                                                       | (_)         => GTZ(normalTerm)
                                                   )
                                                end
          | normalize (ITE(term0,term1,term2)) =
                                                let val normalTerm0 = normalize(term0)
                                                    val normalTerm1 = normalize(term1)
                                                    val normalTerm2 = normalize(term2)
                                                in  if normalTerm0 = T orelse normalTerm0 = F then
                                                        if normalTerm0 = T then normalTerm1
                                                        else normalTerm2
                                                    else (case normalTerm0 of
                                                                  VAR(_)        => ITE(normalTerm0,normalTerm1,normalTerm2)
                                                                | IZ(_)         => ITE(normalTerm0,normalTerm1,normalTerm2)
                                                                | GTZ(_)        => ITE(normalTerm0,normalTerm1,normalTerm2)
                                                                | ITE(_,_,_)    => ITE(normalTerm0,normalTerm1,normalTerm2)
                                                                | (_)           => raise Not_welltyped
                                                         )
                                                end
          | normalize (LAMBDA(VAR(x),lTerm)) =   
                                                let val normalTerm = normalize (lTerm) 
                                                in LAMBDA(VAR(x),normalTerm)
                                                end
          | normalize (APP(lTerm1,lTerm2)) =    
                                                let val normalTerm1 = normalize (lTerm1)
                                                    val normalTerm2 = normalize (lTerm2)
                                                in APP(normalTerm1,normalTerm2)
                                                end

        fun reduceTillCount (lTerm,count) =    if count = 0 then lTerm
                                               else 
                                                        let val (renamedTerm,container,cnt) = alphaRename (lTerm,0,[],[])
                                                            val wellTypeVal = isWellTyped renamedTerm
                                                        in if wellTypeVal = true then
                                                                let val nextTerm = betaNF renamedTerm
                                                                in reduceTillCount (nextTerm,count - 1)
                                                                end
                                                           else raise Not_welltyped
                                                        end

        fun betanf lTerm =                      let val (renamedTerm,container,count) = alphaRename (lTerm,0,[],[])
                                                    val wellTypeValue = isWellTyped renamedTerm
                                                in if wellTypeValue = true then
                                                        let val normalizedTerm = betaNF renamedTerm
                                                            val count = countApps (normalizedTerm,0)
                                                        in if count = 0 then normalize normalizedTerm 
                                                           else normalize (reduceTillCount (normalizedTerm,count))
                                                        end
                                                    else raise Not_welltyped
                                                end
end(*struct*)                                                              
