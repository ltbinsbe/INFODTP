module Minimal where

data Tree = Tip Int | Bin Int Tree Tree

ht (Tip n) = n
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
    show (Tip n) = show n
    show (Bin _ t1 t2) = "(join " ++ show t1 ++ " " ++ show t2 ++ ")"

example1 = map Tip [1..5]

example2 = [
          Tip 4
        , Tip 2
        , Tip 3
        , Tip 5 
        , Tip 1
        , Tip 4
        , Tip 6 
    ]

--instance Read tree where
--    read a = Bin (read a) Tip Tip
