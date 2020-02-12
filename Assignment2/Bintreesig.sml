signature BINTREE =
sig
datatype 'a bintree =   Empty |
                        Node of 'a * 'a bintree * 'a bintree
exception Emptybintree
exception InvalidInorderTraversal
exception OutofRange
exception UnexpectedEmptyNode
exception UnexpectedNodeValue
val root : 'a bintree -> 'a
val leftSubtree : 'a bintree -> 'a bintree
val rightSubtree: 'a bintree -> 'a bintree
val inorder : 'a bintree -> ('a option * int * int) list
val findEmptiesIter  : (int option * 'a * 'b) array * int -> ((int * int * 'a) * int option) bintree list
val areNeighboursP1  : (int * int * int) * (int * int * int) * (int option * 'a * 'b) array -> bool
val keepJoiningNeighboursP  : ((int * int * int) * int option) bintree list * (int option * int * 'a) array -> ((int * int * int) * int option) bintree
val eraseIndices  : ((''a * ''a * 'b) * int option) bintree -> int bintree
val inorderInverse  : (int option * int * int) list -> int bintree
end(*sig*)

structure Bintree : BINTREE =
struct
datatype 'a bintree=Empty
| Node of 'a * 'a bintree * 'a bintree;
exception Emptybintree;
exception OutofRange;
exception InvalidInorderTraversal;
exception UnexpectedEmptyNode;
exception UnexpectedNodeValue;
fun leftSubtree Empty = raise Emptybintree
| leftSubtree (Node (x, LST, RST)) = LST
fun rightSubtree Empty = raise Emptybintree
| rightSubtree (Node (x, LST, RST)) = RST;
fun root Empty = raise Emptybintree
| root (Node (x, LST, RST)) = x;
local fun ino (Empty, Llist, 0) = (NONE,0,0) :: Llist
| ino (Empty, Llist, 1) = (NONE,1,0) :: Llist
| ino (Empty, Llist, 2) = Llist
| ino (Node (N, Empty, Empty), Llist, 0) =      (NONE,0,0) :: ((SOME N, 0, 0) :: ((NONE, 1, 0) :: Llist))
| ino (Node (N, Empty, Empty), Llist, 1) =      (NONE,0,0) :: ((SOME N, 1, 0) :: ((NONE, 1, 0) :: Llist))
| ino (Node (N, LST, RST), Llist, 0) =
let     val Mlist = ino (RST, Llist, 1)
val Nlist = ino (LST, (SOME N, 0, 1)::Mlist, 0)
in Nlist
end
| ino (Node (N, LST, RST), Llist, 1) =
let     val Mlist = ino (RST, Llist, 1)
val Nlist = ino (LST, (SOME N, 1, 1)::Mlist, 0)
in Nlist
end
| ino (Node (N, LST, RST), Llist, 2) =
let     val Mlist = ino (RST, Llist, 1)
val Nlist = ino (LST, (SOME N, 2, 1)::Mlist, 0)
in Nlist
end
in fun inorder T = ino (T, [], 2)
end;
fun findEmptiesIter (ar,n) =
let     val i = ref (n-1)
val NONEs = ref []
in while (!i >= 0) do
( (case Array.sub (ar, !i) of
(NONE: int option,s,c) => NONEs := (Node (((!i,!i,s), NONE: int option), Empty, Empty))::(!NONEs)
|(SOME v,s,c) => NONEs := !NONEs
);
i := (!i)-1
);
!NONEs
end;
fun areNeighboursP1 ((i,j,cl), (k,m,cr), arI) =
let     val inRange = (i >= 0) andalso (j >= 0) andalso
(k >= 0) andalso (m >= 0)
in      if inRange
then
if (i>=0) andalso (i<=j) andalso (j<=k) andalso (k<= m) andalso (cl = 0) andalso (cr = 1)
then
(case Array.sub(arI,j+1) of
(NONE:int option,s,c) => false
|(SOME v,s,c) => (k=j+2)
)
else false
else raise OutofRange
end;
local
fun joinNeighboursP ([],arI) = []
| joinNeighboursP ([bt],arI) = [bt]
| joinNeighboursP ((bt0::(bt1::btList1)),arI) =
let     val ((i,j,cl), rootval0) = root bt0
val ((k,m,cr), rootval1) = root bt1
in      if areNeighboursP1((i,j,cl), (k,m,cr),arI)
then
let
val side=
(case Array.sub(arI,j+1) of (v,s,c) => s )
val cii = (i, m, side)
val rt=
(case Array.sub(arI,j+1) of (v,s,c) => v )
val bt = Node ((cii, rt), bt0, bt1)
in
bt::(joinNeighboursP (btList1,arI))
end

else if null (btList1) then raise InvalidInorderTraversal

else
bt0::(joinNeighboursP ((bt1::btList1),arI))
end
in
fun keepJoiningNeighboursP ([],arI) = raise InvalidInorderTraversal
| keepJoiningNeighboursP ([bt],arI) = bt
| keepJoiningNeighboursP (btList,arI) =
let     val btList1 = joinNeighboursP (btList,arI)
in      keepJoiningNeighboursP (btList1,arI)
end
end;
fun eraseIndices Empty = raise Emptybintree
| eraseIndices (Node (((i, j, k), NONE: int option), Empty, Empty)) =
if (i=j) then Empty
else raise UnexpectedEmptyNode
| eraseIndices (Node (((i, j, k), x), LST, RST)) =
let     val left = eraseIndices LST
val right = eraseIndices RST
in ( case x of
NONE => raise UnexpectedNodeValue
| SOME y => Node (y, left, right)
)
end;
fun inorderInverse [] = raise InvalidInorderTraversal
| inorderInverse [(NONE,0,0)] = Empty
| inorderInverse [(NONE,0,0),(SOME x,0,0),(NONE,0,0)] = Node (x, Empty, Empty)
| inorderInverse II =
let     val arI = Array.fromList II
val n = Array.length arI
val nones = findEmptiesIter (arI,n)
val bt = keepJoiningNeighboursP (nones, arI)

in eraseIndices bt
end;
end(*struct*)
