exception Invalid_Input_exception of string


(*checkValidNumber = fn : char list -> bool : Checks if the input string is a valid integer and outputs true or false based on the result*)
fun checkValidNumber ([]) = false

  | checkValidNumber (a :: []) = 
                        
                        if (ord(a) - ord(#"0")) >= 0 andalso (ord(a)-ord(#"0")) <=9 then true
                                        
                        else if a = #"~" then false
                                        
                        else false

  | checkValidNumber (a :: b) = 
                        
                        if (ord(a) - ord(#"0")) >= 0 andalso (ord(a)-ord(#"0")) <=9 then checkValidNumber (b)
                                        
                        else if a = #"~" then false  
                                    
                        else false;



(*convertStringToStringList = fn : string * string list -> string list : Converts a string to list of strings of length 4 each*)
fun convertStringToStringList (str, oplist) = 

                        let     val x = substring ( str, 0, 4)
                                
                                val y = substring ( str, 4, (size str - 4))

                        in      if (size str) > 4 then convertStringToStringList ( y,oplist@[x])

                                else  oplist@[x]

                        end;



(*pad0 = fn : char list * int -> char list : Prepends required 0s to a charlist to make it a multiple of 4 size list*)
fun pad0 (charList,num0) = 
  
                        if num0 = 0 then charList
                        
                        else  pad0 ((#"0"::charList) , (num0 - 1));



(*trimExtraZeros = fn : int list -> int list : Trims unwanted zeros from the front of the integer list*)
fun trimExtraZeros (h::[]) = [h]

  | trimExtraZeros (h::t) =  if h = 0 then trimExtraZeros t
                                
                             else h::t ;



(*convertStringToInt = fn : string -> int : Converts a string into an integer*)
fun convertStringToInt str = 

                        let     val SOME x = Int.fromString str

                        in      x

                        end;



(*convertStringListToNumList = fn : string list -> int list : Converts a list of string type to an integer list representing an integer of base 10^4*)
fun convertStringListToNumList (strList) = 
  
                        let     val numList = map convertStringToInt strList;

                        in      trimExtraZeros(numList)

                        end; 


                        
(*fromString = fn : string -> int list : Converts a valid integer string into an integer list representing an integer of base 10^4*)
fun fromString (str) = 

                        let     val x = 4 - ((size str) mod 4)
                        
                                val charList = explode(str)

                        in      if x = 4 then convertStringListToNumList(convertStringToStringList(str, []))
                
                                else convertStringListToNumList ( convertStringToStringList (implode (pad0 ( charList , x ) ), [] ) )

                        end;



(*checkFor0 = fn : int list -> bool : Checks if head of an integer list is zero*)
fun checkFor0 numList = 
                        
                        if hd(numList) = 0 then true 
                        
                        else false;



(*decreaseby1 = fn : int list -> int list : Decreases the value of an integer list by 1 and returns reverse of the list if the head element is not 0; otherwise recursively decreases the further elements 
                                            by 1 till a non-zero element is found and then returns the list*)
fun decreaseby1 (numList) = 

                        let     val b = checkFor0 numList

                        in      if b = true then 9999 :: decreaseby1(tl(numList))

                                else rev ((hd(numList) - 1) :: tl(numList))

                        end;



(*decreaseBy1 = fn : int list -> int list : Decreases the value of an integer list by 1 and returns reverse of the list if the head element is not 0; otherwise recursively decreases the further elements 
                                            by 1 till a non-zero element is found and then returns the reverse of the list*)
fun decreaseBy1 (numList) = 
                        
                        let     val b = checkFor0 numList

                        in      if b = true then rev (9999 :: decreaseby1(tl(numList)))
                                
                                else rev ((hd(numList) - 1) :: tl(numList))

                        end;



(*convertProductToNumList = fn : int -> int list : Converts the product of two integers into an integer list*)
fun convertProductToNumList (product) = 

                        if product < 10000 then [product]

                        else 
                          
                          let   val lastFourDigits = [product mod 10000]

                                val firstFourDigits = product div 10000

                          in    firstFourDigits::lastFourDigits

                          end;



(*addZeros = fn : int list * int -> int list : Prepends a fixed number of 0s to an integer list*)
fun addZeros (ipList , numOfZeros) =

                        if numOfZeros = 0 then ipList

                        else addZeros(0::ipList , numOfZeros-1);



(*addListsWithCarry = fn : int * int list * int list -> int list : Adds corresponding elements of a list with carry from the addition of previous list elements*)
fun addListsWithCarry (carry, list1, list2) = 
                        
                        if List.length(list1) = 1 then 
                                
                                let     val sum = hd(list1) + hd(list2) + carry 
                                
                                        val newCarry = sum div 10000

                                        val num = sum mod 10000

                                in      if newCarry = 0 then [sum]

                                        else num::[newCarry]

                                end


                        else    let     val sum = hd(rev(list1)) + hd(rev(list2)) + carry

                                        val newCarry = sum div 10000

                                        val num = sum mod 10000

                                in      if newCarry = 0 then sum :: addListsWithCarry (newCarry, rev(tl(rev(list1))),rev(tl(rev(list2))))

                                        else num::addListsWithCarry (newCarry, rev(tl(rev(list1))),rev(tl(rev(list2))))

                                end;



(*sumOfLists = fn : int list * int list -> int list : Calculates the sum of two integer lists*)
fun sumOfLists (list1,list2) = 

                        let     val len1 = List.length(list1)
                                
                                val len2 = List.length(list2)

                        in      if len1 = len2 then rev(addListsWithCarry(0,list1,list2))

                                else if len1 > len2 then rev(addListsWithCarry(0, list1, addZeros(list2, len1-len2)))

                                else rev(addListsWithCarry(0, addZeros(list1, len2-len1), list2))

                        end;


                        
(*chk0 = fn : int list * bool -> int list : Takes an integer list and checks if the element next to head is 0 or not*)
fun chk0 (ipList, value) = 
  
                        if value = false then (hd(ipList) - 1) :: tl(ipList)

                        else 

                                let     val check = if hd(tl(ipList)) = 0 then true 
                                                    
                                                    else false 

                                 in     9999 :: chk0 (tl(ipList), check)

                                end;



(*findDifference = fn : int list * int list -> int list : Takes two integer lists as input and outputs the difference of those two lists in the form of an integer list*)
fun findDifference (list1, list2) = 

                        if List.length(list1) = List.length(list2) andalso List.length(list1) = 1 then [hd(list1) - hd(list2)]

                        else if List.length(list1) = List.length(list2) andalso List.length(list1) > 1 

                        then 
                                
                                if hd(list1) >= hd(list2) then (hd(list1) - hd(list2)) :: findDifference(tl(list1),tl(list2))

                                else 
                                  
                                  if hd(tl(list1)) > 0 then (10000 - (hd(list2) - hd(list1))) :: findDifference(hd(tl(list1))-1 :: tl(tl(list1)), tl(list2))
                                  
                                  
                                  else 

                                        let     val tailList1 = chk0 (tl(list1), true)

                                        in      (10000 - (hd(list2) - hd(list1))) :: findDifference(tailList1, tl(list2))

                                        end

                        else 

                                let   val list2 = rev(addZeros ( rev(list2), List.length(list1) - List.length(list2)))

                                in    if hd(list1) > hd(list2) then (hd(list1) - hd(list2)) :: findDifference(tl(list1),tl(list2))

                                      else 

                                        if hd(tl(list1)) > 0 then (10000 - (hd(list2) - hd(list1))) :: findDifference(hd(tl(list1))-1 :: tl(tl(list1)), tl(list2))

                                        else 

                                                let     val tailList1 = chk0 (tl(list1), true)

                                                in      (10000 - (hd(list2) - hd(list1))) :: findDifference(tailList1, tl(list2))

                                                end     

                                end;

                              

(* karatsuba = fn : int list -> int list -> int list : Takes 2 integer lists as input and gives their multiplication as output in the form of an integer list *)
fun karatsuba numListX numListY =  

                        let     val sizeNumlistX = List.length(numListX)
                                
                                val sizeNumlistY = List.length(numListY)

                                val n = sizeNumlistX

                                val m = if n mod 2 = 0 then n div 2
                                        else (n div 2) + 1

                                val equalSize = if sizeNumlistX = sizeNumlistY then true 
                                                else false

                        in      if equalSize = true andalso sizeNumlistX = 1
                                then 

                                        let     val firstNum = hd(numListX)

                                                val secondNum = hd(numListY)

                                                val product = firstNum*secondNum

                                        in      convertProductToNumList(product)
                                  
                                        end


                                else if equalSize = true andalso sizeNumlistX > 1
                                then 
                                       let      val (x1,x0) = List.splitAt(numListX,n-m)

                                                val (y1,y0) = List.splitAt(numListY,n-m)

                                                val sumX1X0 = sumOfLists(x1,x0)

                                                val sumY1Y0 = sumOfLists(y1,y0)

                                                val z2Inter = karatsuba x1 y1

                                                val z2 = rev(addZeros(rev(z2Inter), 2*m))

                                                val z0 = karatsuba x0 y0

                                                val z = karatsuba sumX1X0 sumY1Y0

                                                val z1InterRev = findDifference(rev(z), rev(sumOfLists(z2Inter,z0)))

                                                val z1 = rev(addZeros(z1InterRev, m))

                                                val sumList = sumOfLists(z2, sumOfLists(z1, z0))

                                        in      trimExtraZeros (sumList)

                                        end
                                
                                else if equalSize = false andalso sizeNumlistY > m
                                then

                                        let     val numListY = addZeros( numListY, sizeNumlistX - sizeNumlistY)
                                                
                                                val (x1,x0) = List.splitAt(numListX,n-m)

                                                val (y1,y0) = List.splitAt(numListY,n-m)

                                                val sumX1X0 = sumOfLists(x1,x0)

                                                val sumY1Y0 = sumOfLists(y1,y0)

                                                val z2Inter = karatsuba x1 y1

                                                val z2 = rev(addZeros(rev(z2Inter), 2*m))

                                                val z0 = karatsuba x0 y0

                                                val z = karatsuba sumX1X0 sumY1Y0

                                                val z1InterRev = findDifference(rev(z), rev(sumOfLists(z2Inter,z0)))

                                                val z1 = rev(addZeros(z1InterRev, m))

                                                val sumList = sumOfLists(z2, sumOfLists(z1, z0))

                                        in      trimExtraZeros (sumList)             

                                        end

                                else

                                        let     val (x1,x0) = List.splitAt(numListX,n-m)

                                                val (y1,y0) = ([0],numListY)

                                                val sumX1X0 = sumOfLists(x1,x0)

                                                val sumY1Y0 = numListY

                                                val z2 = [0]

                                                val z0 = karatsuba x0 y0

                                                val z = karatsuba sumX1X0 sumY1Y0

                                                val z1InterRev = findDifference(rev(z), rev(z0))

                                                val z1 = rev(addZeros(z1InterRev, m))

                                                val sumList = sumOfLists(z1,z0)

                                        in      trimExtraZeros (sumList)

                                        end

                        end;



(*checkFor0or1 = fn : int list -> bool : Checks if a given Integer list corrresponds to the value 0 or 1*)
fun checkFor0or1 (h :: []) = 
                        
                        if (h=0) orelse (h=1) then true
                        
                        else false

| checkFor0or1 (h :: t) = 
                
                        if h = 0 then checkFor0or1 t

                        else false;



(*factorialInt = fn : int list * int list -> int list : Gives the factorial of a given integer list*)
fun factorialInt (numList1, numList2) =

                        let     val b = checkFor0or1 (numList2)

                        in      if b = true then numList1
                                
                                else
                
                                        if numList1 = [1] then factorialInt(numList2, decreaseBy1(rev(numList2)))

                                        else factorialInt(karatsuba numList1 numList2 , decreaseBy1(rev(numList2)))
          
                        end;



(*prepend0 = fn : string * int -> string : Prepends 0s to a string to make its size 4*)
fun prepend0 (str, numOf0) = 

                        if numOf0 = 0 then str 

                        else "0" ^ prepend0(str, numOf0 - 1); 



(*convertStringListToString = fn : string list -> string : Converts a string list into a string*)
fun convertStringListToString [] = ""

  | convertStringListToString (h :: [] ) = 

                        let     val sizeOfHead = size(h)

                        in      if sizeOfHead = 4 then h

                                else prepend0 (h,4-sizeOfHead)

                        end

  | convertStringListToString (h :: t )  = 

                        let     val sizeOfHead = size(h)

                        in      if sizeOfHead = 4 then h ^ convertStringListToString t

                                else prepend0 (h,4-sizeOfHead) ^ convertStringListToString t

                        end;



(*toString = fn : int list -> string : Converts an integer list into a string*)
fun toString (numList) =  

                        let     val strList = map Int.toString numList

                        in      hd(strList) ^ convertStringListToString (tl(strList))

                        end;



(* val factorial = fn : string -> string : Takes a string as input and finds its factorial if the string is a valid number *)
fun factorial str =

                        if checkValidNumber (explode(str)) = false then raise Invalid_Input_exception str

                        else 

                                let   val numList = fromString (str)

                                in    toString(factorialInt([1], numList))

                                end;
