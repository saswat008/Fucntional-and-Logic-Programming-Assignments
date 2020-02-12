rikudo(Size,Prefilled,Links,Output) :- checkSize(Size),start(Prefilled,Pos),findSolution(Size,Pos,Prefilled,Links,OutputD),sort(OutputD,Output).

checkSize(Size) :- Size =:= 37 ; Size =:= 61 ; Size =:= 91 .

start([(X,Y,Val)|Tail],(Xp,Yp,Valp)) :- (Val is 1, Xp is X, Yp is Y, Valp is Val) ; start(Tail,(Xp,Yp,Valp)) .

findSolution(Size,(X1,Y1,Val),Prefilled,Links,[(0,0,-10)|Prefilled]) :- Size is Val + 1 .
findSolution(Size,(X1,Y1,Val),Prefilled,Links,[(X1,Y1,Val)|OutputList]) :- checkForLink((X1,Y1),Links,(Xl,Yl)) -> 
									   (ifPreFilled((Xl,Yl),Prefilled,Linkval)->
									    ((checkSuccessor(Val,Linkval),findSolution(Size,(Xl,Yl,Linkval),Prefilled,Links,OutputList)) ; 
									    (checkPredecessor(Val,Linkval),findNeighbour(Size,(X1,Y1),(X2,Y2)),not(checkIfPreFilled((X2,Y2),Prefilled)),getSucc(Val,Suc),findSolution(Size,(X2,Y2,Suc),[(X2,Y2,Suc)|Prefilled],Links,OutputList))) ; 
									    (getSucc(Val,Suc1),findSolution(Size,(Xl,Yl,Suc1),[(Xl,Yl,Suc1)|Prefilled],Links,OutputList))) ;
									   findSuccInPre(Val+1,Prefilled,(Xs,Ys,Succ)),
									   ((isValidNode((Xs,Ys)),checkIfNeighbours((Xs,Ys),(X1,Y1)),findSolution(Size,(Xs,Ys,Succ),Prefilled,Links,OutputList)) ; 
									   (isInvalidNode((Xs,Ys)),findNeighbour(Size,(X1,Y1),(X2,Y2)),not(checkIfPreFilled((X2,Y2),Prefilled)),findSolution(Size,(X2,Y2,Succ),[(X2,Y2,Succ)|Prefilled],Links,OutputList))).

findSuccInPre(Val,[],(100,100,Succ)) :- Succ is Val .
findSuccInPre(Val,[(X,Y,Value)|Tail],(Xp,Yp,Valp)) :- (Value is Val , Xp is X , Yp is Y, Valp is Value), ! ; findSuccInPre(Val,Tail,(Xp,Yp,Valp)).

isValidNode((Xs,Ys)) :- Xs =\= 100, Ys =\= 100 .

isInvalidNode((Xs,Ys)) :- Xs =:= 100, Ys =:= 100 .

checkIfNeighbours((Xs,Ys),(X1,Y1)) :- 	(Xs is X1 - 2, Ys is Y1) ; (Xs is X1 + 2,Ys is Y1) ; (Xs is X1 - 1, Ys is Y1 + 1) ; (Xs is X1 + 1, Ys is Y1 + 1) ; (Xs is X1 - 1,Ys is Y1 - 1) ; (Xs is X1 + 1, Ys is Y1 - 1).

findNeighbour(37,(X1,Y1),(X2,Y2)) :- 	X2 is X1 + 1, Y2 is Y1 + 1,(X2,Y2) \== (0,0), abs(Y2) =< 3 , abs(X2) + abs(Y2) =< 6 ;
					X2 is X1 - 1, Y2 is Y1 + 1,(X2,Y2) \== (0,0), abs(Y2) =< 3 , abs(X2) + abs(Y2) =< 6 ;
					X2 is X1 + 1, Y2 is Y1 - 1,(X2,Y2) \== (0,0), abs(Y2) =< 3 , abs(X2) + abs(Y2) =< 6 ;
					X2 is X1 - 1, Y2 is Y1 - 1,(X2,Y2) \== (0,0), abs(Y2) =< 3 , abs(X2) + abs(Y2) =< 6 ;
					X2 is X1 - 2, Y2 is Y1,(X2,Y2) \== (0,0), abs(Y2) =< 3 , abs(X2) + abs(Y2) =< 6 ;
					X2 is X1 + 2, Y2 is Y1,(X2,Y2) \== (0,0), abs(Y2) =< 3 , abs(X2) + abs(Y2) =< 6 .

findNeighbour(61,(X1,Y1),(X2,Y2)) :- 	X2 is X1 + 1, Y2 is Y1 + 1,(X2,Y2) \== (0,0), abs(Y2) =< 4 , abs(X2) + abs(Y2) =< 8 ;
					X2 is X1 - 1, Y2 is Y1 + 1,(X2,Y2) \== (0,0), abs(Y2) =< 4 , abs(X2) + abs(Y2) =< 8 ;
					X2 is X1 + 1, Y2 is Y1 - 1,(X2,Y2) \== (0,0), abs(Y2) =< 4 , abs(X2) + abs(Y2) =< 8 ;
					X2 is X1 - 1, Y2 is Y1 - 1,(X2,Y2) \== (0,0), abs(Y2) =< 4 , abs(X2) + abs(Y2) =< 8 ;
					X2 is X1 - 2, Y2 is Y1,(X2,Y2) \== (0,0), abs(Y2) =< 4 , abs(X2) + abs(Y2) =< 8 ;
					X2 is X1 + 2, Y2 is Y1,(X2,Y2) \== (0,0), abs(Y2) =< 4 , abs(X2) + abs(Y2) =< 8 .

findNeighbour(91,(X1,Y1),(X2,Y2)) :- 	X2 is X1 + 1, Y2 is Y1 + 1,(X2,Y2) \== (0,0), abs(Y2) =< 5 , abs(X2) + abs(Y2) =< 10 ;
					X2 is X1 - 1, Y2 is Y1 + 1,(X2,Y2) \== (0,0), abs(Y2) =< 5 , abs(X2) + abs(Y2) =< 10 ;
					X2 is X1 + 1, Y2 is Y1 - 1,(X2,Y2) \== (0,0), abs(Y2) =< 5 , abs(X2) + abs(Y2) =< 10 ;
					X2 is X1 - 1, Y2 is Y1 - 1,(X2,Y2) \== (0,0), abs(Y2) =< 5 , abs(X2) + abs(Y2) =< 10 ;
					X2 is X1 - 2, Y2 is Y1,(X2,Y2) \== (0,0), abs(Y2) =< 5 , abs(X2) + abs(Y2) =< 10 ;
					X2 is X1 + 2, Y2 is Y1,(X2,Y2) \== (0,0), abs(Y2) =< 5 , abs(X2) + abs(Y2) =< 10 .


checkIfPreFilled((X,Y),[(Xp,Yp,Val)|Tail]) :- (Xp is X, Yp is Y), ! .
checkIfPreFilled((X,Y),[H|Tail]) :- checkIfPreFilled((X,Y),Tail).

checkForLink((X,Y),[(X1,Y1,X2,Y2)|Tail],(Xr,Yr)) :- (X is X1, Y is Y1, Xr is X2, Yr is Y2) ; (X is X2, Y is Y2, Xr is X1, Yr is Y1) ; checkForLink((X,Y),Tail,(Xr,Yr)).

ifPreFilled((X,Y),[(Xp,Yp,Val)|Tail],Valp) :- (Xp is X, Yp is Y, Valp is Val) ; ifPreFilled((X,Y),Tail,Valp). 

checkSuccessor(Val1,Val2) :- Val2 is Val1 + 1 .

checkPredecessor(Val1,Val2) :- Val2 is Val1 - 1.

getSucc(Val,Suc) :- Suc is Val + 1.
