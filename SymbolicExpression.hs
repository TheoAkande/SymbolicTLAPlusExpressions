data Expr
  = Empty
  | Atom String
  | Max Expr Expr
  | Sum [Expr]
  deriving (Eq, Show)

add :: Expr -> Expr -> Expr
add Empty b = b
add a Empty = a
add (Sum xs) (Sum ys) = Sum (xs ++ ys)
add (Sum xs) b        = Sum (xs ++ [b])
add a        (Sum ys) = Sum (a : ys)
add a b = Sum [a, b]

mult :: Expr -> Int -> Expr
mult _ n | n <= 0 = Empty
mult e n = Sum (replicate n e)

le :: Expr -> Expr -> Bool
le Empty _ = True
le _ Empty = False
le (Atom a) (Atom b) =
  a == b || atomLE a b
le (Max a1 a2) (Max b1 b2) =
  le a1 b1 && le a2 b2 || le a1 b2 && le a2 b1
-- a ≤ max(b1, b2) if a ≤ one of them
le a (Max b1 b2) =
  le a b1 || le a b2
-- max(a1, a2) ≤ b if both are ≤ b
le (Max a1 a2) b =
  le a1 b && le a2 b
le (Sum xs) (Sum ys) =
  subset xs ys
le (Sum xs) b =
  le (Sum xs) (Sum [b])
le a (Sum ys) =
  subset [a] ys
le _ _ = False

subset :: [Expr] -> [Expr] -> Bool
subset [] _ = True
subset (x:xs) ys =
  case pickMatch x ys of
    Nothing  -> False
    Just ys' -> subset xs ys'

pickMatch :: Expr -> [Expr] -> Maybe [Expr]
pickMatch _ [] = Nothing
pickMatch x (y:ys)
  | le x y    = Just ys
  | otherwise = fmap (y :) (pickMatch x ys)

toSum :: Expr -> [Expr]
toSum Empty    = []
toSum (Sum xs) = xs
toSum e        = [e]

extractCommon :: [Expr] -> [Expr] -> ([Expr], [Expr], [Expr])
extractCommon [] ys = ([], [], ys)
extractCommon (x:xs) ys =
  case pickEqual x ys of
    Nothing ->
      let (c, xs', ys') = extractCommon xs ys
      in (c, x : xs', ys')
    Just ys' ->
      let (c, xs', ys'') = extractCommon xs ys'
      in (x : c, xs', ys'')

eqExpr :: Expr -> Expr -> Bool
eqExpr a b = le a b && le b a

pickEqual :: Expr -> [Expr] -> Maybe [Expr]
pickEqual _ [] = Nothing
pickEqual x (y:ys)
  | eqExpr x y = Just ys
  | otherwise = fmap (y :) (pickEqual x ys)

sumExpr :: [Expr] -> Expr
sumExpr []  = Empty
sumExpr [e] = e
sumExpr es  = Sum es

maxExpr :: Expr -> Expr -> Expr
maxExpr a b
  -- dominance cases
  | le a b && not (le b a) = b
  | le b a && not (le a b) = a
  -- incomparable: factor common parts
  | otherwise =
      let as = toSum a
          bs = toSum b
          (common, a', b') = extractCommon as bs
      in sumExpr $
           common ++
           case (sumExpr a', sumExpr b') of
             (Empty, Empty) -> []
             (x, Empty)     -> [x]
             (Empty, y)     -> [y]
             (x, y)         -> [Max x y]



--- Test helpers

atomLE :: String -> String -> Bool
atomLE a b = a == b || atomLE' a b
atomLE' "a" "b" = True
atomLE' "b" "c" = True
atomLE' "a" "c" = True
atomLE' _   _   = False

assert :: String -> Bool -> (String, Bool)
assert name cond = (name, cond)

runTests :: [(String, Bool)] -> [(String, Bool)]
runTests = filter (not . snd)

testsEqual :: [(String, Bool)]
testsEqual =
  [ assert "Empty == Empty"
      $ eqExpr Empty Empty

  , assert "Atom eq"
      $ eqExpr (Atom "x") (Atom "x")

  , assert "Atom neq"
      $ not $ eqExpr (Atom "x") (Atom "y")

  , assert "Sum order insensitive"
      $ eqExpr (Sum [Atom "x", Atom "y"])
              (Sum [Atom "y", Atom "x"])

  , assert "Sum multiplicity matters"
      $ not $ eqExpr (Sum [Atom "x", Atom "x"])
                    (Sum [Atom "x"])

  , assert "Max structural equality"
      $ eqExpr (Max (Atom "x") Empty)
              (Max (Atom "x") Empty)

  , assert "Max different children"
      $ eqExpr (Max (Atom "x") Empty)
                    (Max Empty (Atom "x"))
  ]

testsLE_basic :: [(String, Bool)]
testsLE_basic =
  [ assert "Empty <= Atom"
      $ le Empty (Atom "x")

  , assert "Atom !<= Empty"
      $ not $ le (Atom "x") Empty

  , assert "Atom reflexive"
      $ le (Atom "x") (Atom "x")
  ]

testsLE_atoms :: [(String, Bool)]
testsLE_atoms =
  [ assert "atomLE a b"
      $ le (Atom "a") (Atom "b")

  , assert "not atomLE b a"
      $ not $ le (Atom "b") (Atom "a")
  ]

testsLE_sum :: [(String, Bool)]
testsLE_sum =
  [ assert "singleton subset"
      $ le (Sum [Atom "x"])
           (Sum [Atom "x", Atom "y"])

  , assert "multiplicity respected"
      $ not $ le (Sum [Atom "x", Atom "x"])
                 (Sum [Atom "x"])

  , assert "element-wise le"
      $ le (Sum [Atom "a"])
           (Sum [Atom "b"])
  ]

testsLE_max :: [(String, Bool)]
testsLE_max =
  [ assert "a <= max(a,b)"
      $ le (Atom "x") (Max (Atom "x") (Atom "y"))

  , assert "max(a,b) !<= a"
      $ not $ le (Max (Atom "x") (Atom "y")) (Atom "x")

  , assert "max distributes downward"
      $ le (Max (Atom "a") (Atom "b")) (Atom "c")
  ]

testsAdd :: [(String, Bool)]
testsAdd =
  [ assert "Empty is identity (left)"
      $ eqExpr (add Empty (Atom "x")) (Atom "x")

  , assert "Empty is identity (right)"
      $ eqExpr (add (Atom "x") Empty) (Atom "x")

  , assert "Add atoms"
      $ eqExpr (add (Atom "x") (Atom "y"))
              (Sum [Atom "x", Atom "y"])

  , assert "Add flattens sums"
      $ eqExpr (add (Sum [Atom "x"]) (Sum [Atom "y"]))
              (Sum [Atom "x", Atom "y"])
  ]

testsMult :: [(String, Bool)]
testsMult =
  [ assert "mult 0"
      $ eqExpr (mult (Atom "x") 0) Empty

  , assert "mult 1"
      $ eqExpr (mult (Atom "x") 1) (Atom "x")

  , assert "mult 3"
      $ eqExpr (mult (Atom "x") 3)
              (Sum [Atom "x", Atom "x", Atom "x"])

  , assert "mult preserves order"
      $ le (mult (Atom "a") 2)
           (mult (Atom "b") 2)
  ]

testsMax_dominance :: [(String, Bool)]
testsMax_dominance =
  [ assert "a <= b ⇒ max a b = b"
      $ eqExpr (maxExpr (Atom "a") (Atom "b"))
              (Atom "b")

  , assert "b <= a ⇒ max a b = a"
      $ eqExpr (maxExpr (Atom "b") (Atom "a"))
              (Atom "b")
  ]

testsMax_common :: [(String, Bool)]
testsMax_common =
  [ assert "common factor extraction"
      $ eqExpr
          (maxExpr (Sum [Atom "x", Atom "y"])
                   (Sum [Atom "x", Atom "z"]))
          (Sum [Atom "x", Max (Atom "y") (Atom "z")])
  ]

testsMax_incomparable :: [(String, Bool)]
testsMax_incomparable =
  [ assert "pure incomparable atoms"
      $ eqExpr (maxExpr (Atom "x") (Atom "y"))
              (Max (Atom "x") (Atom "y"))
  ]

testsAlgebra :: [(String, Bool)]
testsAlgebra =
  [ assert "idempotence"
      $ eqExpr (maxExpr e e) e

  , assert "commutativity"
      $ eqExpr (maxExpr a b) (maxExpr b a)

  , assert "monotonicity"
      $ le a b ==> le (maxExpr a c) (maxExpr b c)
  ]
  where
    e = Sum [Atom "x"]
    a = Atom "a"
    b = Atom "b"
    c = Atom "c"

(==>) p q = not p || q

tests :: [(String, Bool)]
tests =
     testsEqual
  ++ testsLE_basic
  ++ testsLE_atoms
  ++ testsLE_sum
  ++ testsLE_max
  ++ testsAdd
  ++ testsMult
  ++ testsMax_dominance
  ++ testsMax_common
  ++ testsMax_incomparable

-- atoms
a = Atom "a"
b = Atom "b"
c = Atom "c"
x = Atom "x"
y = Atom "y"
z = Atom "z"

-- nested expressions
-- Sum of Atom and Max
e1 = Sum [x, Max y z]

-- Max of Sums
e2 = Max (Sum [x, y]) (Sum [y, z])

-- Deeply nested: Max inside Sum inside Max
e3 = Max (Sum [x, Max y z]) (Atom "a")

-- Even deeper: Sum of Max of Sums of Max
e4 = Sum [ Max (Sum [x, Max y z]) (Atom "a")
         , Max (Atom "b") (Sum [y, z]) ]

-- Symmetric variant of e4 for eqExpr testing
e4_sym = Sum [ Max (Atom "a") (Sum [Max y z, x])
             , Max (Sum [y, z]) (Atom "b") ]

tests_eqExpr_recursive :: [(String, Bool)]
tests_eqExpr_recursive =
  [ assert "identical deep Max/Sum"
      $ eqExpr e1 (Sum [x, Max y z])

  , assert "Max of Sums equality"
      $ eqExpr e2 (Max (Sum [x, y]) (Sum [y, z]))

  , assert "deep nested Max inside Sum"
      $ eqExpr e3 (Max (Sum [x, Max y z]) (Atom "a"))

  , assert "commutative Max/Sum equality"
      $ eqExpr e4 e4_sym  -- order-insensitive / commutative check
  ]

tests_le_recursive :: [(String, Bool)]
tests_le_recursive =
  [ assert "Atom <= Max"
      $ le x (Max x y)

  , assert "Sum <= Sum with extra"
      $ le (Sum [x, y]) (Sum [x, y, z])

  , assert "nested Max <= Max with extra"
      $ le (Max (Sum [x, y]) z)
           (Max (Sum [x, y, z]) z)

  , assert "deep nested Sum inside Max <= larger Max"
      $ le e3
           (Max (Sum [x, Max y z, a]) (Atom "a"))

  , assert "deep Max <= itself"
      $ le e4 e4  -- reflexivity check
  ]

tests_maxExpr_recursive :: [(String, Bool)]
tests_maxExpr_recursive =
  [ assert "maxExpr on atoms"
      $ eqExpr (maxExpr a b)
               (Max a b)  -- assuming a and b incomparable

  , assert "maxExpr on sums with common element"
      $ eqExpr (maxExpr (Sum [x, y]) (Sum [x, z]))
               (Sum [x, Max y z])

  , assert "maxExpr nested Max inside Sum"
      $ eqExpr (maxExpr e1 (Sum [x, y]))
               (Sum [x, Max y z])  -- demonstrates recursive Max creation

  , assert "maxExpr deep nested e3 vs e3"
      $ eqExpr (maxExpr e3 e3) e3  -- idempotence

  , assert "maxExpr deep nested e4 vs e4_sym"
      $ eqExpr (maxExpr e4 e4_sym) e4  -- commutativity + factoring common
  ]

tests_recursive :: [(String, Bool)]
tests_recursive =
     tests_eqExpr_recursive
  ++ tests_le_recursive
  ++ tests_maxExpr_recursive

-- Run and filter failures
failures = runTests tests_recursive

