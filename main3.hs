{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
import Prelude hiding (min)
import Control.Monad.Writer
import Control.Monad.State
import Data.Monoid
import Data.List

type IVar = String
type Label = String
data T = Label Label | Put E E E | If E T T | Skip | Jump Label | (:>) T T | E E | Init E | FloatInit E
  deriving Show
data E = Lit Int | IVar IVar | Extern String | Out String | Index IVar | Value IVar | BinOp String E E | Next IVar | Offset E E
       | Call String E
  deriving Show

data GenI i = Gen
  { current :: (i -> T) -> T
  , value   :: (Maybe E -> T) -> T
  , next    :: (Maybe T -> T) -> T
  , initialize :: T
  }
type Gen = GenI (Maybe E)

gmap f g gen = Gen
  { current = current gen . (. fmap f)
  , value = value gen . (. fmap g)
  , next = next gen
  , initialize = initialize gen
  }

sparseVec index_array value_array = gmap
  (Offset (Extern index_array))
  (Offset (Extern value_array))

le a b = BinOp "<" a b
min a b k = If (le a b) (k a) (k b)
eq a b = BinOp "=" a b
times a b = BinOp "*" a b
plus a b = BinOp "+" a b

range :: Int -> IVar -> Gen
range n var =
  let i = Index var in
  let
    --current k = k $ Just $ Index var
    --value   k = k $ Just $ Value var
    current k = If (le i (Lit n)) (k $ Just $ Index var) (k Nothing)
    value   k = If (le i (Lit n)) (k $ Just $ Value var) (k Nothing)
    next    k = If (le i (Lit n)) (k $ Just $ E $ Next var) (k Nothing)
    -- foo     k = If (le i (Lit n)) (k $ (Just $ Index var, Just $ Value var, Just $ Next var)) (k (Nothing, Nothing, Nothing))
  in
  Gen { current, value, next, initialize = Init $ IVar var }

extern fn n = gmap id (Call fn) . range n

add a b =
  let
    c k = current a $ \ia -> case ia of
      Nothing -> current b k
      Just ia -> current b $ \ib -> case ib of
        Nothing -> k $ Just ia
        Just ib -> min ia ib (k . Just)
    v k = current a $ \ia -> case ia of
      Nothing -> value b k
      Just ia -> current b $ \ib -> case ib of
        Nothing -> value a k
        Just ib -> If (le ia ib) (value a $ \va -> case va of
                                     Nothing -> Skip
                                     Just _ -> k va)
                                    (If (le ib ia)
                                    (value b (\vb -> case vb of
                                                 Nothing -> Skip
                                                 Just _ -> k vb))
                                      (value a (\va -> value b (\vb -> case (va, vb) of
                                                                   (Just va, Just vb) -> k $ Just (plus va vb)
                                                                   (Nothing, Just _) -> k vb
                                                                   (Just _, Nothing) -> k va
                                                                   (Nothing, Nothing) -> k $ Just (Lit 0)))))
    n k = current a $ \ia -> case ia of
      Nothing -> next b k
      Just ia -> current b $ \ib -> case ib of
        Nothing -> next a k
        Just ib -> If (le ia ib) (next a k) $ If (le ib ia) (next b k) $ next a $ \na -> next b $ \nb ->
          case (na, nb) of
            (Just na, Just nb) -> k $ Just (na :> nb)
            (Nothing, Just _) -> k nb
            (Just _, Nothing) -> k na
            (Nothing, Nothing) -> k $ Nothing
  in
    Gen { current = c, value = v, next = n, initialize = initialize a :> initialize b }

mul a b =
  let
    c k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current b $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> min ia ib (k . Just)
    v k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current b $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> If (le ia ib) (k Nothing) $ If (le ib ia) (k Nothing) $
          value a $ \va -> case va of
            Nothing -> k Nothing
            Just va -> value b $ \vb -> case vb of
              Nothing -> k Nothing
              Just vb -> k (Just (times va vb))
    n k = current a $ \ia -> case ia of
      Nothing -> next b k
      Just ia -> current b $ \ib -> case ib of
        Nothing -> next a k
        Just ib -> If (le ia ib) (next a k) (next b k)
  in
    Gen { current = c, value = v, next = n, initialize = initialize a :> initialize b }

flatten outer inner =
  let
    n k =
      value inner $ \vi -> case vi of
      Nothing -> next outer k
      Just _ -> current inner $ \ii -> case ii of
        Nothing -> next outer k
        Just _ -> next inner k
    c k =
      current outer $ \io -> case io of
      Nothing -> k (Nothing, Nothing)
      Just io -> current inner $ \ii -> case ii of
        Nothing -> k $ (Just io, Nothing)
  in
    Gen { next = n }

loop :: Label -> Label -> E -> Gen -> T
loop loop done acc g =
  initialize g :>
  FloatInit acc :>
  Label loop :>
  (current g $ \mi -> case mi of
      Nothing -> Skip
      Just i -> value g $ \mv -> case mv of
        Nothing -> Skip
        Just v -> Put acc i v ) :>
  (next g $ \ms -> case ms of
      Nothing -> Jump done
      Just s -> s :> Jump loop)
  :> Label done

t1 = loop "loop" "done" (Out "acc") (add (range 10 "a") (range 3 "b"))
t2 = loop "loop" "done" (Out "acc") (mul (range 10 "a") (range 3 "b"))
t3 = loop "loop" "done" (Out "acc") (add (sparseVec "is" "vs" $ range 10 "a") (range 3 "b"))

wrap s = "(" ++ s ++ ")"

e2c :: E -> String
e2c e = case e of
  Lit i -> show i
  IVar i -> i
  Out i -> i
  -- todo
  Index i -> i
  Value i -> i
  Extern i -> i
  Next i -> wrap $ i ++ "++"
  BinOp op e1 e2 -> wrap $ e2c e1 ++ op ++ e2c e2
  Offset b i -> e2c b ++ "[" ++ e2c i ++ "]"
  Call f e -> f ++ (wrap $ e2c e)

init_buffer var = "for(int i = 0; i < BUFFER_SIZE; i++) { "++var++"[i] = 0; }\n"

t2c :: T -> String
t2c t = case t of
  Label l -> l ++ ":\n"
  --Put l r -> e2c l ++ " = " ++ e2c r ++ ";"
  Put l i r -> "put" ++ (wrap $ intercalate "," (map e2c [l, i, r])) ++ ";"
  If c t e -> "if (" ++ e2c c ++ ") {" ++ t2c t ++ "} else {" ++ t2c e ++ "}"
  Jump l -> "goto " ++ l ++ ";"
  Skip -> ""
  a :> b -> t2c a ++ t2c b
  E e -> e2c e ++ ";\n"
  Init e -> "int " ++ e2c e ++ " = 0;\n"
  FloatInit (Out v) -> "num* " ++ v ++ " = (num*)malloc(BUFFER_SIZE*sizeof(float));\n" ++ init_buffer v
  FloatInit _ -> error "todo, FloatInit"

  -- "#include \"stdio.h\"\n#include \"stdlib.h\"\n#include \"stdbool.h\"\n\
  -- \int main() {\n" ++ s
addHeader s =
  "#include \"prefix.c\"\n"
  ++ s
  ++ "#include \"suffix.c\"\n"
compile :: T -> IO ()
compile = writeFile "out.c" . addHeader . t2c

{-
put sparse output
*
hierarchy

load input
size inference for malloc
-}
