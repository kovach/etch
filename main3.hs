{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
import Prelude hiding (min)
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import Data.List
import Data.String
import System.Process

sorry = undefined

type Label = String
type IVar = String
type Var = String
-- data Index = Unit | Pair E Index deriving Show
data T = Label Label | Put E [E] E | If E T T | Skip | Jump Label | (:>) T T | E E | Init E | FloatInit E | Store Var E
  deriving Show
data E = Lit Int | IVar IVar | Var Var | Extern String | Out String | Index IVar | Value IVar | BinOp String E E | Next IVar | Offset E E
       | Call String E
  deriving (Show, Eq)

data GenIV i v = Gen
  { current    :: (i -> T) -> T
  , value      :: (v -> T) -> T
  , next       :: (Maybe T -> T) -> T
  , initialize :: T
  }
type GenV = GenIV (Maybe E)
type Gen = GenIV (Maybe E) (Maybe E)

genFMap f g gen = Gen
  { current = current gen . (. fmap f)
  , value = value gen . (. fmap g)
  , next = next gen
  , initialize = initialize gen
  }

genMap f g gen = Gen
  { current = current gen . (. f)
  , value = value gen . (. g)
  , next = next gen
  , initialize = initialize gen
  }

imap f = genMap f id
vmap f = genMap id f

sparseVec index_array value_array = genFMap
  (Offset (Extern index_array))
  (Offset (Extern value_array))

le    a b   = BinOp "<" a b
min   a b k = If (le b a) (k b) (k a)
eq    a b   = BinOp "=" a b
times a b   = BinOp "*" a b
plus  a b   = BinOp "+" a b

range :: Int -> IVar -> Gen
range n var =
  let i = Index var in
  let
    current k = If (le i (Lit n)) (k $ Just $ Index var) (k Nothing)
    value   k = If (le i (Lit n)) (k $ Just $ Value var) (k Nothing)
    next    k = If (le i (Lit n)) (k $ Just $ E $ Next var) (k Nothing)
  in
  Gen { current, value, next, initialize = Init $ IVar var }

extern fn n = genFMap id (Call fn) . range n

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
                    (If (le ib ia) (value b (\vb -> case vb of
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

mul :: Gen -> Gen -> Gen
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

-- hmm
memoIndex :: Var -> Gen -> Gen
memoIndex loc g = g
  { next = \k -> next g $ \mt -> case mt of
      Just t -> (current g $ \i -> case i of
        Just i -> k $ Just $ t :> Store loc i
        Nothing -> Skip {- ? -} )
      Nothing -> k Nothing
  , current = ($ Just $ Var loc)
  }

wrap s = "(" ++ s ++ ")"

e2c :: E -> String
e2c e = case e of
  Lit i          -> show i
  IVar i         -> i
  Index i        -> i
  Value i        -> i
  Var i          -> i
  Out i          -> i
  Extern i       -> i
  Next i         -> wrap $ i ++ "++"
  BinOp op e1 e2 -> wrap $ e2c e1 ++ op ++ e2c e2
  Offset b i     -> e2c b ++ "[" ++ e2c i ++ "]"
  Call f e       -> f ++ (wrap $ e2c e)

init_buffer var = "for(int i = 0; i < BUFFER_SIZE; i++) { "++var++"[i] = 0; }"

type M = WriterT String (Reader [E])
runM :: M () -> String
runM = flip runReader [] . execWriterT

emit :: String -> M ()
emit s = tell s

instance (IsString (M ())) where
  fromString = emit

wrapm :: M () -> M ()
wrapm s = emit "(" >> s >> ")"

trivial :: T -> Bool
trivial Skip = True
trivial (If c t e) = trivial t && trivial e
trivial (a :> b) = trivial a && trivial b
trivial _ = False

t2c :: T -> M ()
t2c t = case t of
  _ | trivial t     -> ""
  Put l [i] r       -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
  Put l (i:_) r     -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
  If c t e          -> do
    pathCondition <- ask -- some premature code simplification
    if c `elem` pathCondition then t2c t else do
      emit $ "if (" ++ e2c c ++ ") {" ; local (c:) (t2c t) ; emit "}";
      if trivial e then "" else do emit " else {" ; t2c e ; "}"
      -- case e of
      --   Skip        -> return ()
      --   _           -> do emit " else {" ; t2c e ; "}"
  Label l           -> emit $ "\n" ++ l ++ ":\n"
  Jump  l           -> emit $ "goto " ++ l ++ ";"
  Skip              -> ""
  a :> b            -> t2c a >> t2c b
  E e               -> emit $ e2c e ++ ";\n"
  Init e            -> emit $ "int " ++ e2c e ++ " = 0;\n"
  Store v e         -> emit $ v ++ " = " ++ e2c e ++ ";"
  FloatInit (Out v) -> emit $ "num* " ++ v ++ " = (num*)malloc(BUFFER_SIZE*sizeof(float));\n" ++ init_buffer v
  FloatInit _       -> error "todo, FloatInit"

compile :: T -> IO ()
compile t = do
  writeFile "out.c" . addHeader . runM . t2c $ t
  callCommand "clang-format -i out.c"
  where
    addHeader s =
      "#include \"prefix.c\"\n"
      ++ s
      ++ "#include \"suffix.c\"\n"

flatten :: GenIV i1 (Maybe T) -> GenIV i2 b -> GenIV (i1, i2) b
flatten outer inner =
  let
    n k =
      next inner $ \mstep -> case mstep of
        Just _ -> k mstep -- increment inner
        Nothing -> next outer $ \mstep -> case mstep of
          Just mstep -> k $ Just $ mstep :> (value outer $ \mv -> case mv of
            Nothing -> Skip
            Just step -> step) :> initialize inner
          Nothing -> k Nothing -- finished
    c k = current outer $ \i1 -> current inner $ \i2 -> k (i1, i2)
    v = value inner
  in
    Gen { next = n, current = c, value = v, initialize = initialize outer :> initialize inner }

fff :: GenIV (Maybe i1, Maybe i2) v -> GenIV (Maybe (i1, i2)) v
fff = imap maybeTuple where maybeTuple = uncurry $ liftM2 (,)

loop :: Label -> Label -> E -> Gen -> T
loop loop done acc g =
  initialize g :>
  FloatInit acc :>
  Label loop :>
  (current g $ \mi -> case mi of
      Nothing -> Skip
      Just i -> value g $ \mv -> case mv of
        Nothing -> Skip
        Just v -> Put acc [i] v ) :>
  (next g $ \ms -> case ms of
      Nothing -> Jump done
      Just s -> s :> Jump loop)
  :> Label done

m1 = (mul (range 10 "a") (range 3 "b"))
t1 = loop "loop" "done" (Out "acc") (add (range 10 "a") (range 3 "b"))
t2 = loop "loop" "done" (Out "acc") (mul (range 10 "a") (range 3 "b"))
t3 = loop "loop" "done" (Out "acc") (add (sparseVec "is" "vs" $ range 10 "a") (range 3 "b"))

tf1 = loop "loop" "done" (Out "acc") $ imap (\(_, i2) -> i2) $ flatten (vmap (const (Just Skip)) $ range 3 "r") (range 5 "c")
tf2 = loop "loop" "done" (Out "acc") $ imap (\(_, i2) -> i2) $ flatten (vmap (const (Just Skip)) $ m1) (range 5 "c")
tf3 = loop "loop" "done" (Out "acc") $ imap (fmap snd) $ fff $ flatten (vmap (const (Just $ Jump $ "foo")) $ m1) (range 5 "c")
tf4 = loop "loop" "done" (Out "acc") $ imap (fmap snd) $ fff $ flatten
  (denseRows 3 "r" "is" "vs")
  (sparseVec "is" "vs" $ range 5 "c")


denseRows n i indicesPtr valuesPtr = genFMap id f (range n i)
  where
    f _ = E (Next indicesPtr) :> E (Next valuesPtr)
