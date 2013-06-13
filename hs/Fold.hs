
--cons :: a -> [a] -> [a]
cons b a = foldr (:) a [b]
