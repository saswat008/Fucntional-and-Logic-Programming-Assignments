structure Flx : FLX =
struct
        datatype term = VAR of string (* variable *)
                        | Z           (* zero *)
                        | T           (* true *)
                        | F           (* false *)
                        | P of term   (* Predecessor *)
                        | S of term   (* Successor *)
                        | ITE of term * term * term   (* If then else *)
                        | IZ of term  (* is zero *)
                        | GTZ of term (* is greater than zero *);

        exception Not_wellformed;
        exception Not_nf;
        exception Not_int;

        fun removeSpaces charList =             if hd(charList) = #" " then removeSpaces (tl(charList))
                                                else charList;

        fun checkIfVar (a :: []) =              if ord(a) >= 97 andalso ord(a) <= 122
                                                then true
                                                else false
          | checkIfVar (a::b) =                 if ord(a) >= 97 andalso ord(a) <= 122
                                                then checkIfVar b
                                                else false
          | checkIfVar (_) =                    false;

        fun checkVarTerm (a :: (#")" :: b)) =   if ord(a) >= 97 andalso ord(a) <= 122 then true
                                                else false

          | checkVarTerm (a :: b) =             if ord(a) >= 97 andalso ord(a) <= 122
                                                then checkVarTerm b
                                                else false;

        fun getVarTerm (charList,opList) =      if hd(charList) = #")" then (opList,charList)
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

        and getTerm charList =                  if hd(charList) = #"Z" then (Z,tl(charList))

                                                else if hd(charList) = #"T" then (T,tl(charList))

                                                else if hd(charList) = #"F" then (F,tl(charList))

                                                (*for VAR*)
                                                else if checkVarTerm charList = true then
                                                        let val (term,suffix) = getVarTerm (charList,[])
                                                        in (VAR(implode(List.rev(term))),suffix)
                                                        end

                                                
                                                else if hd(charList) = #"("then 
                                                        (*for P*)
                                                        if hd(tl(charList)) = #"P" andalso hd(tl(tl(charList))) = #" "then 
                                                                let val inTerm = removeSpaces (tl(tl(charList)))
                                                                    val (term,suffix) = getTerm inTerm
                                                                in if hd(suffix) = #")" then (P(term),tl(suffix))
                                                                else raise Not_wellformed
                                                                end

                                                        (*for S*)
                                                        else if hd(tl(charList)) = #"S" andalso hd(tl(tl(charList))) = #" " then 
                                                                let val inTerm = removeSpaces (tl(tl(charList)))
                                                                    val (term,suffix) = getTerm inTerm
                                                                in if hd(suffix) = #")" then (S(term),tl(suffix))
                                                                   else raise Not_wellformed
                                                                end

                                                        (*for IZ*)
                                                        else if hd(tl(charList)) = #"I" andalso hd(tl(tl(charList))) = #"Z" andalso hd(tl(tl(tl(charList)))) = #" " then 
                                                                let val inTerm = removeSpaces (tl(tl(tl(charList))))
                                                                    val (term,suffix) = getTerm inTerm
                                                                in if hd(suffix) = #")" then (IZ(term),tl(suffix))
                                                                   else raise Not_wellformed
                                                                end

                                                        (*for GTZ*)
                                                        else if hd(tl(charList)) = #"G" andalso hd(tl(tl(charList))) = #"T" andalso hd(tl(tl(tl(charList)))) = #"Z" andalso hd(tl(tl(tl(tl(charList))))) = #" " then
                                                                let val inTerm = removeSpaces (tl(tl(tl(tl(charList)))))
                                                                    val (term,suffix) = getTerm inTerm
                                                                in if hd(suffix) = #")" then (GTZ(term),tl(suffix))
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
                                                        else raise Not_wellformed
                                                else raise Not_wellformed;



        fun fromString "Z" =                    Z
          | fromString "T" =                    T
          | fromString "F" =                    F
          | fromString ipString =               if String.sub(ipString,0) = #"(" then
                                                        let val charList = explode(ipString)
                                                            val (term,suffix) = getTerm charList
                                                        in if suffix = [] then term
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
          | toString (ITE(x,y,z)) =             "(ITE <" ^ toString(x) ^ "," ^ toString(y) ^ "," ^ toString(z) ^ ">)";
                                                
        fun fromInt num =                       if num < 0 then P(fromInt (num+1))
                                                else if num > 0 then S(fromInt (num-1))
                                                else Z;

        fun checkForOnlySP (Z) =                true
          | checkForOnlySP (S(x)) =             checkForOnlySP (x)
          | checkForOnlySP (P(x)) =             checkForOnlySP (x)
          | checkForOnlySP (_) =                false;

        fun toPosInt (Z) =                      0
          | toPosInt (S(x)) =                   toPosInt(x) + 1
          | toPosInt (P(x)) =                   if checkForOnlySP (x) = true then raise Not_nf
                                                else raise Not_int
          | toPosInt (_) =                      raise Not_int;

        fun toNegInt (Z) =                      0
          | toNegInt (P(x)) =                   toNegInt(x) - 1
          | toNegInt (S(x)) =                   if checkForOnlySP (x) = true then raise Not_nf
                                                else raise Not_int
          | toNegInt (_) =                      raise Not_int;

        fun toInt Z =                           0
          | toInt (S(x)) =                      toPosInt (x) + 1
          | toInt (P(x)) =                      toNegInt (x) - 1
          | toInt(_) =                          raise Not_int;
       

        fun checkForOnlySZ Z =                  true
          | checkForOnlySZ (S(term)) =          checkForOnlySZ term
          | checkForOnlySZ (_) =                false;

        fun checkForOnlyPZ Z =                  true
          | checkForOnlyPZ (P(term)) =          checkForOnlyPZ term
          | checkForOnlyPZ (_) =                false;
  
        fun normalize (Z) =                     Z
          | normalize (T) =                     T
          | normalize (F) =                     F
          | normalize (VAR(x)) =                VAR(x)
          | normalize (S(term)) =
                                                let val normalTerm = normalize (term)
                                                in (case normalTerm of
                                                        S(normTerm) => S(normalTerm)
                                                      | P(normTerm) => normTerm
                                                      | (_)         => S(normalTerm)
                                                   )
                                                end
          | normalize (P(term)) =
                                                let val normalTerm = normalize (term)
                                                in (case normalTerm of
                                                        P(normTerm) => P(normalTerm)
                                                      | S(normTerm) => normTerm
                                                      | (_)         => P(normalTerm)
                                                   )
                                                end
          | normalize (IZ(term)) =
                                                let val normalTerm = normalize (term)
                                                in (case normalTerm of
                                                         Z           => T
                                                       | S(normTerm) => if checkForOnlySZ normTerm = true then F
                                                                        else IZ(normalTerm)
                                                       | P(normTerm) => if checkForOnlyPZ normTerm = true then F
                                                                        else IZ(normalTerm)
                                                       | (_)         => IZ(normalTerm)
                                                   )
                                                end
          | normalize (GTZ(term)) =             let val normalTerm = normalize (term)
                                                in (case normalTerm of
                                                         Z           => F
                                                       | S(normTerm) => if checkForOnlySZ normTerm = true then T
                                                                        else GTZ(normalTerm)
                                                       | P(normTerm) => if checkForOnlyPZ normTerm = true then F 
                                                                        else GTZ(normalTerm)
                                                       | (_)         => GTZ(normalTerm)
                                                   )
                                                end
          | normalize (ITE(term0,term1,term2)) =
                                                let val normalTerm0 = normalize(term0)
                                                    val normalTerm1 = normalize(term1)
                                                    val normalTerm2 = normalize(term2)
                                                in      if normalTerm1 = normalTerm2 then normalTerm1
                                                        else if normalTerm0 = T then normalTerm1
                                                        else if normalTerm0 = F then normalTerm2
                                                        else ITE(normalTerm0,normalTerm1,normalTerm2)
                                                end;
end(*struct*)

