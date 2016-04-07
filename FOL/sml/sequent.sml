datatype formula =
         True | False | Symb of string
         | And of formula * formula | Or of formula * formula
         | Imp of formula * formula;

type ctx = formula list;

datatype sequent = |- of formula list * formula list;
infix 3 |-
val x = [] |- [True];
val p = [And (Symb "phi", Symb "psi")] |- [Or (Symb "phi", Symb "psi")];

fun concat (xss : ('a list) list) : 'a list =
  case xss of
      [] => []
   |  (xs::xss') => xs @ (concat xss');


fun linear_unfold (s : sequent) : sequent =
  let
      fun linear_unfold_l (s : sequent) : sequent =
        let val (Gamma |- cs) = s
        in case Gamma of
              [] => s
            | (p::ps) =>
              let val (Gamma' |- cs') = linear_unfold_l (ps |- cs)
              in
                  case p of
                      And (a,b) => linear_unfold_l (a::b::Gamma' |- cs')
                    | _ => (p::Gamma' |- cs')
              end
        end
      fun linear_unfold_r (s : sequent) : sequent =
        let val (Gamma |- cs) = s
        in case cs of
              [] => s
            | (c::cs') =>
              let val (Gamma' |- cs'') = linear_unfold_r (Gamma |- cs')
              in
                  case c of
                      Or (a,b) => linear_unfold_r (Gamma' |- a::b::cs'')
                    | Imp (a,b) => linear_unfold_r (a::Gamma |- b::cs'')
                    | _ => (Gamma' |- c::cs'')
              end
        end
  in
      linear_unfold_l (linear_unfold_r s)
  end;

fun branch_unfold (s : sequent) : sequent list =
  let
      fun branch_unfold_l (s : sequent) : sequent list =
        let val (Gamma |- cs) = s
        in case Gamma of
              [] => [s]
            | (p::ps) =>
              let val rest = branch_unfold_l (ps |- cs)
              in
                  case p of
                      Or (a,b) => map (fn (ps |- cs) => a::ps |- cs ) rest @
                                  map (fn (ps |- cs) => b::ps |- cs ) rest
                    | Imp (a,b) => map (fn (ps |- cs) => ps |- a::cs) rest @
                                    map (fn (ps |- cs) => b::ps |- cs) rest
                    | _ => map (fn (ps |- cs) => p::ps |- cs) rest
              end
        end

      fun branch_unfold_r (s : sequent) : sequent list =
        let val (Gamma |- Delta) = s
        in case Delta of
              [] => [s]
            | (c::cs) =>
              let val rest = branch_unfold_r (Gamma |- cs)
              in
                  case c of
                      And (a,b) => map (fn (ps |- cs) => ps |- a::cs) rest @
                                    map (fn (ps |- cs) => ps |- b::cs) rest
                    | _ => map (fn (ps |- cs) => ps |- c::cs) rest
              end
        end
  in
      concat (map branch_unfold_l (branch_unfold_r s))
  end;


fun unfold (s : sequent) : sequent list =
  branch_unfold (linear_unfold s);

fun member (elt : ''a, lst : ''a list) =
  foldr (fn (x, acc) => if x = elt then true else acc) false lst;

exception StuckOnFoldedTerm
fun solve (s : sequent) : bool =
  let
      fun match (s : sequent) : bool =
        let val (Gamma |- Delta) = s
        in foldr (fn (x,acc) =>
                     case x of
                         False => false
                       | True => acc
                       | Symb s => member (Symb s, Gamma) andalso acc
                       | _ => raise StuckOnFoldedTerm ) true Delta
        end
  in
      foldr (fn (x,acc) => match x andalso acc) true (unfold s)
  end;
