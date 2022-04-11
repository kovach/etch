{-
handle () at base of Gen
avoid monad?
out vs extern
aggregation
  need to compute semantic bracket
    semantics typeclass
  handle output
    need locate and iter/locate mul?
contraction
initialize tries
-}
{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
import Prelude hiding (min)
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import Data.Maybe
import Data.List hiding (singleton)
import Data.String
import Data.Function
import System.Process

sorry = undefined

type Label = String
type IVar = String
type Var = String

data T = Label Label | Put E [E] E | If E T T | Skip | Jump Label | (:>) T T | E E | Declare IVar | Init E | FloatInit E | Store Var E
       | Alarm String
       | Unreachable
       | ExternT String
  deriving Show
data E = Lit Integer | IVar IVar | Var Var | Extern String | Out String
       | Index IVar | Value IVar | Next IVar | SkipTo IVar E
       | Offset E E | BinOp String E E
       | RecordAccess E String
       | Call String E
  deriving (Show, Eq)

instance (IsString E)
  where fromString = Extern

instance Num E
  where fromInteger = Lit

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

instance Functor (GenIV i) where
  fmap f = genMap id f

imap f = genMap f id

sparseVec index_array value_array = genFMap
  (Offset index_array)
  (Offset value_array)

le    a b   = BinOp "<" a b
min   a b k = If (le b a) (k b) (k a)
eq    a b   = BinOp "==" a b
times a b   = BinOp "*" a b
plus  a b   = BinOp "+" a b

singleton :: a -> GenIV () a
singleton v = Gen
    { next = ($ Nothing)
    -- todo does this need a check?
    , current = ($ ())
    , value = ($ v)
    , initialize = Skip
    }

range :: E -> IVar -> Gen
range n var =
  let i = Index var in
  let
    current k = If (le i n) (k $ Just $ Index var) (k Nothing)
    value   k = If (le i n) (k $ Just $ Value var) (k Nothing)
    next    k = If (le i n) (k $ Just $ E $ Next var) (k Nothing)
  in
  Gen { current, value, next, initialize = Init . IVar $ var }

replicate n v g = (\_ -> g) <$> range n v

extern fn n = genFMap id (Call fn) . range n

-- a; b
sequenceGen :: GenIV i v -> GenIV i v -> GenIV i v
sequenceGen a b = Gen
  { next = \k -> next a $ \mstep -> case mstep of
      Nothing -> next b k
      Just mstep -> k (Just mstep)
  , current = \k -> next a $ \mstep -> case mstep of
      Nothing -> current a k
      Just _ -> current b k
  , value = \k -> next a $ \mstep -> case mstep of
      Nothing -> value a k
      Just _ -> value b k
  , initialize = initialize a :> initialize b
  }

addGen :: Gen -> Gen -> Gen
addGen a b =
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

class Mul a where
  mul :: a -> a -> a

mulgen :: (Mul a) => GenV (Maybe a) -> GenV (Maybe a) -> GenV (Maybe a)
mulgen a b =
  let
    c k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current b $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> If (eq ia ib) (k (Just ia)) (k Nothing)
    v k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current b $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> If (eq ia ib)
          (value a $ \va -> case va of
            Nothing -> k Nothing
            Just va -> value b $ \vb -> case vb of
              Nothing -> k Nothing
              Just vb -> k (Just (mul va vb)))
          (k Nothing)
    n k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current b $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> If (le ia ib) (next a k) (next b k)
  in
    Gen { current = c, value = v, next = n, initialize = initialize a :> initialize b }

instance Mul E where
  mul = times

instance Mul a => Mul (GenV (Maybe a)) where
  mul = mulgen

wrap s = "(" ++ s ++ ")"
e2c :: E -> String
e2c e = case e of
  Lit i            -> show i
  IVar i           -> i
  Index i          -> i
  Value i          -> i
  Var i            -> i
  Out i            -> i
  Extern i         -> i
  Next i           -> wrap $ i ++ "++"
  BinOp op e1 e2   -> wrap $ e2c e1 ++ op ++ e2c e2
  Offset b i       -> e2c b ++ "[" ++ e2c i ++ "]"
  Call f e         -> f ++ (wrap $ e2c e)
  RecordAccess e f -> e2c e ++ "." ++ f
  e                -> error (show e)

init_buffer var = "for(int i = 0; i < BUFFER_SIZE; i++) { "++var++"[i] = 0; }"

data Context = Context
  { trueConditions :: [E]
  , falseConditions :: [E] }

disablePathCondition = False
pushTrue e c  = if disablePathCondition then c else c { trueConditions = e : trueConditions c}
pushFalse e c = if disablePathCondition then c else c { falseConditions = e : falseConditions c}
trueElem e c = e `elem` trueConditions c
falseElem e c = e `elem` falseConditions c
emptyContext = Context [] []

type M = StateT Int (WriterT String (Reader Context))
runM :: M () -> String
runM = flip runReader emptyContext . execWriterT . flip evalStateT 0

emit :: String -> M ()
emit s = tell s

instance (IsString (M ())) where
  fromString = emit

wrapm :: M () -> M ()
wrapm s = emit "(" >> s >> ")"

evalTrivial :: T -> M Bool
evalTrivial Skip       = return True
--evalTrivial (If c t e) = return False
evalTrivial (If c t e) = do
  pathCondition <- ask
  if c `trueElem` pathCondition then evalTrivial t else
    if c `falseElem` pathCondition then evalTrivial e else do
      tt <- evalTrivial t
      et <- evalTrivial e
      return $ tt && et
evalTrivial (a :> b)   = pure (&&) <*> (evalTrivial a) <*> (evalTrivial b)
evalTrivial _          = return False

t2c :: T -> M ()
t2c t = do
  triv <- evalTrivial t
  if triv then "" else case t of
    Put l [i] r       -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
    Put l (i:_) r     -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
    If c t e          -> do
      pathCondition <- ask -- some premature code simplification
      if c `trueElem` pathCondition then t2c t else
        if c `falseElem` pathCondition then t2c e else do
          emit $ "if (" ++ e2c c ++ ") {" ; local (pushTrue c) (t2c t) ; emit "}";
          eTriv <- evalTrivial e
          if eTriv then "" else do emit " else {" ; local (pushFalse c) (t2c e) ; "}"
    Label l           -> emit $ "\n" ++ l ++ ":\n"
    Jump  l           -> emit $ "goto " ++ l ++ ";"
    Skip              -> ""
    a :> b            -> t2c a >> local (\_ -> emptyContext) (t2c b)
    E e               -> emit $ e2c e ++ ";\n"
    Declare e         -> emit $ "int " ++ e ++ " = 0;\n"
    Init e            -> emit $ e2c e ++ " = 0;\n"
    --Init e            -> emit $ "int " ++ e2c e ++ " = 0;\n"
    Store v e         -> emit $ v ++ " = " ++ e2c e ++ ";"
    FloatInit (Out v) -> emit $ "num* " ++ v ++ " = (num*)malloc(BUFFER_SIZE*sizeof(float));\n" ++ init_buffer v
    FloatInit _       -> error "todo, FloatInit"
    Alarm s           -> emit $ "// " ++ s ++ "\n"
    Unreachable       -> emit $ "// unreachable\n"
    ExternT s         -> emit s
    t                 -> error (show t)

maybeTuple :: (Maybe a1, Maybe a2) -> Maybe (a1, a2)
maybeTuple = uncurry $ liftM2 (,)

class HasTop a where
  top :: a

instance HasTop (Maybe E) where
  top = Nothing

flatten :: (HasTop i2) => GenIV i1 (Maybe (GenIV i2 (Maybe a))) -> GenIV (i1, i2) (Maybe a)
flatten outer =
  let
    n k =
      value outer $ \minner -> case minner of
        Nothing -> next outer $ k . fmap ( :> (value outer $ \minner -> case minner of
                                       Nothing -> Alarm "still nothing"
                                       Just inner -> initialize inner))
        Just inner  -> next inner $ \mstep -> case mstep of
          Just _ -> k mstep
          Nothing -> next outer $ k . fmap (:> initialize inner)
    c k = current outer $ \i1 -> value outer $ \minner -> case minner of
            Nothing -> k (i1, top)
            Just inner -> current inner $ \i2 -> k (i1, i2)
    v k = value outer $ \minner -> case minner of
            Nothing -> (k Nothing)
            Just inner -> value inner k
    init = initialize outer :>
           (value outer $ \minner -> case minner of
                                      Nothing -> Alarm "nothing yet"
                                      Just inner -> initialize inner)
  in
    Gen { next = n, current = c, value = v, initialize = init }


fresh :: String -> M String
fresh n = do
  k <- get
  put (k+1)
  return $ n ++ show k

-- todo recursive
loop :: E -> Gen -> M T
loop acc g = do
  loop <- fresh "loop"
  done <- fresh "done"
  return $
    initialize g :>
    FloatInit acc :>
    -- ExternT "__i = 0;" :>
    Label loop :>
    ExternT "__i++;" :>
    (current g $ maybe Skip $ \i -> value g $ maybe Skip $ \v -> Put acc [i] v) :>
    (next g $ \ms -> case ms of
        Nothing -> Jump done
        Just s -> s :> Jump loop) :>
    Label done
    :> ExternT "printf(\"loops: %d\\n\", __i);\n"

loopGen :: Gen -> M (GenIV () (Maybe E))
loopGen g = do
  temp <- fresh "temp"
  initialize <- loop (Out temp) g
  return $ Gen
    { next = ($ Nothing)
    -- todo does this need a check?
    , current = ($ ())
    , value = ($ Just (Out temp))
    , initialize
    }

compile :: M T -> IO ()
compile t = do
  let outName = "out.cpp"
  writeFile outName . addHeader . runM $ t >>= t2c
  callCommand $ "clang-format -i " ++ outName
  where
    addHeader s =
      "#include \"prefix.cpp\"\n"
      ++ s
      ++ "#include \"suffix.cpp\"\n"

parseNode :: E -> (E, E, E)
parseNode e = (RecordAccess e "length", RecordAccess e "indices", RecordAccess e "children")
parseNodeIter :: Gen -> GenV (Maybe (E, E, E))
parseNodeIter = fmap $ fmap $ parseNode

uncurry3 f (a,b,c) = f a b c

leafIter i (len, is, vs) = range len i & sparseVec is vs
nodeIter i (len, is, vs) = range len i & sparseVec is vs & parseNodeIter

gmap :: (v -> v') -> GenIV i (Maybe v) -> GenIV i (Maybe v')
gmap = fmap . fmap

(.>) = flip (.)
tIJK       = parseNode "tree" & nodeIter "i" & gmap (nodeIter "j" .> gmap (leafIter "k"))
t2 t i j   = parseNode t & nodeIter i & gmap (leafIter j)
t3 t i j k = parseNode t & nodeIter i & gmap (nodeIter j) & gmap (gmap (leafIter k))

-- todo
fl :: GenIV (Maybe a) (Maybe (GenV (Maybe a1))) -> GenV (Maybe a1)
fl = flatten .> imap (maybeTuple .> fmap snd)

fl2 = fl . gmap fl

chk = compile . loop (Out "acc")

main1 = chk . fl2 $ tIJK
main2 = chk $ fl  $ mul (t2 "A" "iA" "jA" ) (t2 "B" "iB" "jB" )
main3 = chk $ fl2 $ mul (t3 "C" "iA" "jA" "kA") (t3 "D" "iB" "jB" "kB")

agg :: Gen -> M (GenIV () (), E)
agg = sorry

memo :: Gen -> M (GenIV () (Maybe Gen))
memo g = do
  (ag, output) <- agg g
  return $ sequenceGen
    (ag & fmap (const Nothing))
    (singleton $ Just $ parseNode output & leafIter "todo")

-- hmmmmmmmmm
--memo t = do
--  accName <- fresh "temp"
--  code <- loop (Out accName) t
--  var <- fresh "i"
--  return $
--    code :>
--    parseNode (Out accName) & leafIter var

contraction1 :: GenIV (Maybe a) (Maybe Gen) -> M Gen
contraction1 = fl .> memo .> fmap (imap (\s -> Just s) .> fl)

-- agg
--
