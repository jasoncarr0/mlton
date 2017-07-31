functor HashAllocator(S: ALLOCATOR_STRUCTS):ALLOCATOR = 
struct
open S

fun combine (hsh1, hsh2) = 
   hsh1 * 0w11 + hsh2 * 0w7 + 0wx9e3779b9 
   (* = a * 11 + b * 7 + golden ratio *)

structure Config = 
struct
   type t = word
   val scan = Parse.*> (Parse.str "hash:", Parse.<$> (Word.fromInt, Parse.uint))
end
structure Inst =
struct
   type t = (word * word)
   fun layout (_, h) = Layout.str (Word.toString h)
   fun equals ((m, h), (m', h')) = m = m' andalso (Word.mod(h, m)) = (Word.mod(h', m))
   fun hash (_, h) = h
   fun new m = (Word.<< (0w1, m), combine (0w0, m))
   fun preEval ((m, hsh), {var, exp=_}) = (m, combine (0w13 + Sxml.Var.hash var, hsh))
   fun postBind ((m, hsh), {var, exp=_}) = (m, combine (Sxml.Var.hash var, hsh))
end
structure Addr =
struct
   type t = word
   fun alloc (var, (m, hsh)) = combine (Sxml.Var.hash var, hsh) mod m
   val layout = Layout.str o Word.toString
   val equals = op =
   fun hash x = x
   fun store {empty: word -> 'a} =
      let
         val set = HashSet.new {hash=fn (h, _) => h} 
         fun get h = 
            let 
               val (_, res) = HashSet.lookupOrInsert 
                  (set, h, fn (h', _) => h = h', fn () => (h, empty h))
            in
               res
            end
      in
         {get=get, destroy=fn () => ()}
      end
end


end
