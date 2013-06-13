module Minimal where

data Tree = Tip | Bin Int Tree Tree

ht Tip = 0
ht (Bin n _ _) = n

join x y = Bin ((max (ht x) (ht y)) + 1) x y

step t []  = [t]
step t [u] = 
  case compare (ht t) (ht u) of
    LT -> [t,u]
    _  -> [join t u]
step t (u:v:ts) =
  case compare (ht t) (ht u) of
    LT -> [t,u,v] ++ ts
    _  ->
      case compare (ht t) (ht v) of
        LT -> step (join t u) (v:ts)
        _  -> step t (step (join u v) ts)


fold_step input acc =
  case input of
    []      -> acc
    (i:is)  -> 
      case acc of
        []       -> fold_step is ([i])
        [u]      ->
          case compare (ht i) (ht u) of 
            LT      -> fold_step is [i,u]
            _       -> fold_step is [join i u]
        (u:v:us) ->  
          case compare (ht i) (ht u) of
            LT      -> fold_step is (i : u : v : us)
            _       -> 
              case compare (ht i) (ht v) of
                LT      -> fold_step is (fold_step [join i u] (v:us))       
                _       -> fold_step is (fold_step [i] (fold_step [join u v] us))

test1 = foldr step []
test2 xs = fold_step xs []

build = foldl1 join . (foldr step [])
build_fold xs = foldl1 join (fold_step xs [])

instance Show Tree where
    show Tip = show 0
    show (Bin n _ _) = show n

example = [
          Bin 4 Tip Tip
        , Bin 2 Tip Tip
        , Bin 3 Tip Tip
        , Bin 5 Tip Tip
        , Bin 1 Tip Tip
        , Bin 4 Tip Tip
        , Bin 6 Tip Tip 
    ]

--instance Read tree where
--    read a = Bin (read a) Tip Tip
