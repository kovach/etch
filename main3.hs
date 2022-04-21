{-
fold maybe in Gen/LGen value type
add init/reset commands

how to split up trie management
  initialize
  haskell decides to push float vs node
  emits simple instructions: next, skipto, index, value
  fix index value next skipto e2c

contraction
  aggregate vectors

? remove deref/address
out vs extern
initialize input tries
maybe implement semantics bracket too?
-}
{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
import Prelude hiding (min)
import Control.Monad (join)
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

data ExternIteratorType
  = ExternCounter | ExternInnerNode | ExternLeafNode
  deriving (Show, Eq)
data T
  = E E
  | Put E [E] E | Accum E E | Store E E
  | Label Label | If E T T | Jump Label | (:>) T T | Skip
  | Declare IVar | Init E | FloatInit E
  | Comment String
  | Unreachable String
  | Debug String
  deriving Show
data E
  = Lit Integer | IVar IVar | Ident String
  | Incr E
  | Index E | Value E
  | Next E
  | SkipTo E E
  | Offset E E | BinOp String E E
  | RecordAccess E String
  | Call E [E]
  | Deref E
  | Address E
  | Extern String
  deriving (Show, Eq)

instance (IsString E)
  where fromString = Ident

instance Num E
  where fromInteger = Lit

data GenIV' i v = Gen
  { current    :: (i -> T) -> T
  , value      :: (v -> T) -> T
  , next       :: (Maybe T -> T) -> T
  , initialize :: T
  }
type GenIV i = GenIV' (Maybe i)
type GenV = GenIV E
type Gen = GenIV E (Maybe E)
type UnitGen = GenIV () (Maybe E)

data LGenIV' i v = LGen
  { gen :: GenIV' i v
  , locate :: i -> T
  }
type LGenIV i = LGenIV' (Maybe i)
type LGenV = LGenIV E
type LGen  = LGenIV E (Maybe E)

genMap' f g gen = Gen
  { current = current gen . (. f)
  , value = value gen . (. g)
  , next = next gen
  , initialize = initialize gen
  }

genMap f g gen = Gen
  { current = current gen . (. fmap f)
  , value = value gen . (. fmap g)
  , next = next gen
  , initialize = initialize gen
  }

instance Functor (GenIV' i) where
  fmap f = genMap' id f
instance Functor (LGenIV' i) where
  fmap f lg = lg { gen = fmap f (gen lg) }

imap f = genMap' (fmap f) id

sparseVec index_array value_array = genMap
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
    , current = ($ (Just ()))
    , value = ($ v)
    , initialize = Skip
    }

-- opaqueGen :: ExternIteratorType -> IVar -> Gen
-- opaqueGen t v = Gen
--   { next = ($ Just $ E $ Next t v)
--   , current = ($ Just (Index t v))
--   , value   = ($ Just (Value t v))
--   , initialize = Skip
--   }

-- TODO merge with lrange
range :: E -> IVar -> Gen
range n var' =
  let var = IVar var' in
  let i = var in
  let
    current k = If (le i n) (k $ Just $ var) (k Nothing)
    value   k = If (le i n) (k $ Just $ var) (k Nothing)
    next    k = If (le i n) (k $ Just $ E $ Incr var) (k Nothing)
  in
  Gen { current, value, next, initialize = Init var }

-- lrange' :: E -> IVar -> LGen
-- lrange' n var =
--   let t = ExternCounter in
--   let i = Index t var in
--   let
--     current k = If (le i n) (k $ Just $ Index t var) (k Nothing)
--     value   k = If (le i n) (k $ Just $ Value t var) (k Nothing)
--     next    k = If (le i n) (k $ Just $ E $ Next t var) (k Nothing)
--   in
--   LGen { gen = Gen { current, value, next, initialize = Init . IVar $ var }
--        , locate = \e -> case e of
--            Nothing -> Store var n
--            Just e -> Store var e
--        }

-- lrange :: E -> IVar -> LGen
-- lrange n var =
--   let i = Index var in
--   let stari = Deref $ Index var in
--   let
--     current k = If (le stari n) (k $ Just $ stari) (k Nothing)
--     value   k = If (le stari n) (k $ Just $ stari) (k Nothing)
--     next    k = If (le i n) (k $ Just $ E $ Next var) (k Nothing)
--   in
--   LGen { gen = Gen { current, value, next, initialize = Init . IVar $ var }
--        , locate = \e -> case e of
--            Nothing -> Store var (Deref $ plus (Address $ Extern var) n)
--            Just e -> Store var (Deref $ plus (Address $ Extern var) e)
--        }

replicate n v g = (\_ -> g) <$> range n v

-- extern fn n = genMap id (Call fn) . range n

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

mulGen :: (Mul a) => GenV (Maybe a) -> GenV (Maybe a) -> GenV (Maybe a)
mulGen a b =
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

mulGL :: (Mul a) => GenV (Maybe a) -> LGenV (Maybe a) -> GenV (Maybe a)
mulGL a b =
  let
    c k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current (gen b) $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> If (eq ia ib) (k (Just ia)) (k Nothing)
    v k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current (gen b) $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> If (eq ia ib)
          (value a $ \va -> case va of
            Nothing -> k Nothing
            Just va -> value (gen b) $ \vb -> k $ case vb of
              Nothing -> Nothing
              Just vb -> Just (mul va vb))
          (k Nothing)
    n k = next a $ fmap (\step -> step :> (current a $ locate b)) .> k
  in
    Gen { current = c, value = v, next = n, initialize = initialize a :> initialize (gen b) }

instance Mul E where
  mul = times

instance Mul a => Mul (GenV (Maybe a)) where
  mul = mulGen

--instance (Mul a, Num a) => Num (GenV (Maybe a)) where
--  (+) = addGen
--  (*) = mulGen

wrap s = "(" ++ s ++ ")"
e2c :: E -> String
e2c e = case e of
  Lit i            -> show i
  IVar i           -> i
  --Index i        -> externIndex t i
  --Value i        -> externValue t i
  --Next i         -> externNext t i -- wrap $ i ++ "++"
  --SkipTo i e     -> externSkip t i -- ++ ".skip" ++ wrap (e2c e)
  Incr i           -> wrap $ e2c i ++ "++"
  Ident i          -> i
  BinOp op e1 e2   -> wrap $ e2c e1 ++ op ++ e2c e2
  Offset b i       -> e2c b ++ "[" ++ e2c i ++ "]"
  Call f es         -> e2c f ++ (wrap $ intercalate "," $ map e2c es)
  RecordAccess e f -> e2c e ++ "." ++ f
  Deref e          -> wrap $ "*" ++ wrap (e2c e)
  Address e          -> "&" ++ e2c e
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

-- todo Text? or reverse output
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
    Accum l r         -> emit $ e2c l ++ " += " ++ e2c r ++";"
    Label l           -> emit $ "\n" ++ l ++ ":\n"
    Jump  l           -> emit $ "goto " ++ l ++ ";"
    Skip              -> ""
    a :> b            -> t2c a >> local (\_ -> emptyContext) (t2c b)
    E e               -> emit $ e2c e ++ ";\n"
    Declare e         -> emit $ "int " ++ e ++ " = 0;\n"
    Init e            -> emit $ e2c e ++ " = 0;\n"
    --Init e            -> emit $ "int " ++ e2c e ++ " = 0;\n"
    Store l r         -> emit $ e2c l ++ " = " ++ e2c r ++ ";"
    FloatInit (Ident v) -> emit $ "num* " ++ v ++ " = (num*)malloc(BUFFER_SIZE*sizeof(float));\n" ++ init_buffer v
    FloatInit _       -> error "todo, FloatInit"
    Comment s           -> emit $ "// " ++ s ++ "\n"
    Unreachable s       -> emit $ "// unreachable: " ++ s ++ "\n"
    Debug s         -> emit s
    If c t e          -> do
      pathCondition <- ask -- some premature code simplification
      if c `trueElem` pathCondition then t2c t else
        if c `falseElem` pathCondition then t2c e else do
          emit $ "if (" ++ e2c c ++ ") {" ; local (pushTrue c) (t2c t) ; emit "}";
          eTriv <- evalTrivial e
          if eTriv then "" else do emit " else {" ; local (pushFalse c) (t2c e) ; "}"
    t                 -> error (show t)

maybeTuple :: (Maybe a1, Maybe a2) -> Maybe (a1, a2)
maybeTuple = uncurry $ liftM2 (,)

class HasTop a where
  top :: a

instance HasTop (Maybe E) where
  top = Nothing

flatten :: GenIV i1 (Maybe (GenIV i2 (Maybe a))) -> GenIV (i1, Maybe i2) (Maybe a)
flatten outer =
  let
    n k =
      value outer $ \minner -> case minner of
        Nothing -> next outer $ k . fmap ( :> (value outer $ \minner -> case minner of
                                       Nothing -> Comment "still nothing"
                                       Just inner -> initialize inner))
        Just inner  -> next inner $ \mstep -> case mstep of
          Just _ -> k mstep
          Nothing -> next outer $ k . fmap (:> initialize inner)
    c k = current outer $ \i1 -> case i1 of
            Nothing -> k Nothing
            Just i1 -> value outer $ \minner -> case minner of
              Nothing -> k $ Just (i1, Nothing)
              Just inner -> current inner $ \i2 -> k $ Just (i1, i2)
    v k = value outer $ \minner -> case minner of
            Nothing -> (k Nothing)
            Just inner -> value inner k
    init = initialize outer :>
           (value outer $ \minner -> case minner of
                                      Nothing -> Comment "nothing yet"
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
    Label loop :>
    Debug "__i++;" :>
    (current g $ maybe Skip $ \i -> value g $ maybe Skip $ \v -> Put acc [i] v) :>
    (next g $ \ms -> case ms of
        Nothing -> Jump done
        Just s -> s :> Jump loop) :>
    Label done
    :> Debug "printf(\"loops: %d\\n\", __i);\n"

loopT :: GenIV () (Maybe T) -> M T
loopT g = do
  loop <- fresh "loop"
  done <- fresh "done"
  return $
    initialize g :>
    Debug "__i = 0;" :>
    Label loop :>
    Debug "__i++;" :>
    (value g $ fromMaybe Skip) :>
    (next g $ \ms -> case ms of
        Nothing -> Jump done
        Just s -> s :> Jump loop) :>
    Label done
    :> Debug "printf(\"loops: %d\\n\", __i);\n"

(.>) = flip (.)

--gmap :: (v -> v') -> GenIV i (Maybe v) -> GenIV i (Maybe v')
gmap :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
gmap = fmap . fmap

fl :: GenIV i1 (Maybe (GenIV i2 (Maybe a))) -> GenIV i2 (Maybe a)
fl = flatten .> imap snd .> genMap' join id
fl2 = fl . gmap fl

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

main1 = chk . fl2 $ tIJK
main2 = chk $ fl  $ mul (t2 "A" "iA" "jA" ) (t2 "B" "iB" "jB" )
main3 = chk $ fl2 $ mul (t3 "C" "iA" "jA" "kA") (t3 "D" "iB" "jB" "kB")

tIJK       = parseNode "tree" & nodeIter "i" & gmap (nodeIter "j" .> gmap (leafIter "k"))
t2 t i j   = parseNode t & nodeIter i & gmap (leafIter j)
t3 t i j k = parseNode t & nodeIter i & gmap ((nodeIter j) .> gmap (leafIter k))

chk = compile . loop (Ident "acc")
chk' = compile . loopT

class Storable l r out where
  store :: l -> r -> out
instance Storable E E T where
  store loc val = Store (Deref loc) (plus (Deref loc) val)
instance (Storable l r out) =>
  Storable (LGenIV i (Maybe l))
           (GenIV  i (Maybe r))
           (GenIV () (Maybe out)) where
  store l r = Gen
    { next = \k -> next r $ fmap (\step -> value r $ \mv -> step :> case mv of
                                         Nothing -> Skip
                                         Just _ -> (current r $ locate l)) .> k
    , current = ($ Just ())
    , value = \k -> value (gen l) $ \mloc -> case mloc of
        Nothing -> Comment "unreachable"
        Just loc -> value r $ fmap (\val -> store loc val) .> k
    -- , initialize = initialize (gen l) :> initialize r
    , initialize = initialize (gen l) :> initialize r :> (current r $ locate l)
    }

externGen :: E -> Gen
externGen x =
  let call op = Call (RecordAccess x op) [] in
  let check op k = If (call "done") (k Nothing) (k (Just $ E $ call op)) in
  let check' op k = If (call "done") (k Nothing) (k (Just $ call op)) in
  Gen
  { next = check "next"
  , current = check' "current"
  , value = check' "value"
  , initialize = Store (RecordAccess x "i") 0
  }

externLGen :: E -> LGen
externLGen x =
  let call op = Call (RecordAccess x op) [] in
  let check op k = If (call "done") (k Nothing) (k (Just $ E $ call op)) in
  let check' op k = If (call "done") (k Nothing) (k (Just $ call op)) in
  LGen
  { gen = Gen
    { next = check "next"
    , current = check' "current"
    , value = check' "value_ref"
    , initialize = Skip :> Comment "todo"
    }
  , locate = \i -> case i of
      Nothing -> E $ call "finish"
      Just i -> E $ Call (RecordAccess x "skip") [i]
  }


accumulator :: E -> LGenIV () (Maybe E)
accumulator acc = LGen {gen = singleton $ Just acc, locate = const Skip}

prefixGen t gen = gen { initialize = t :> initialize gen }

contraction1 :: GenV (Maybe UnitGen) -> M UnitGen
contraction1 v = do
  (acc, storingGen) <- contract1 v
  loop <- loopT storingGen
  return $ prefixGen loop $
    (singleton $ Just $ acc)
  where
    contract1 :: GenV (Maybe (GenIV () (Maybe E))) -> M (E, GenIV () (Maybe T))
    contract1 v = do
      acc <- Ident <$> fresh "acc"
      return (acc, store (accumulator acc) (fl v))

eg1 = chk' $ store (externLGen "out") (range 10 "i")
eg2 = chk' $ store (externLGen "out1") (externGen "t2")
eg3 = compile $ do
  b1 <- (loopT (store (externLGen "out1") (range 10 "i")))
  b2 <- (loopT (store (externLGen "out2") (range 10 "i")))
  b3 <- (loopT (store (externLGen "out") (addGen (externGen "t2") (externGen "t1"))))
  return $ b1 :> b2 :> Debug "t1 = *toVal(out1); t2 = *toVal(out2);" :> b3

eg4 = compile $ do
  b1 <- (loopT (contraction1 $ range 10 "i" & fmap (Just . singleton)))
  return b1
