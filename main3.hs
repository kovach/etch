{-

front end
  basic syntax
  read monadic actions from input
  helpers

fix UnitGen handling
  fix add/mul
  insert by default

remove initialize?
cleanup file

non-scalar contraction


cleanup T, E
maybe implement semantics bracket?
-}
{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
import Prelude hiding (min, replicate)
import Control.Monad (join)
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import Data.Maybe
import Data.List hiding (singleton, replicate)
import Data.String
import Data.Function
import System.Process

sorry = undefined

type Label = String
type IVar = String

data T
  = E E
  | Put E [E] E | Accum E E | Store E E
  | Label Label | If E T T | Jump Label | (:>) T T | Skip
  | DeclareInt IVar | FloatInit E
  | AutoDecl IVar E
  | Comment String
  | Debug String
  | Block T
  | Labels [String]
  deriving Show
unreachable s = Comment $ "unreachable: " ++ s

data E
  = Lit Integer | IVar IVar | Ident String
  | Incr E
  --- | Index E | Value E | Next E | SkipTo E E
  | Offset E E | BinOp String E E
  | RecordAccess E String
  | Call E [E]
  | Deref E
  | Address E
  | Extern String
  deriving (Show, Eq)

instance (IsString E)
  where fromString = Ident

instance Num E where
  fromInteger = Lit
  (+) = BinOp "+"
  (*) = BinOp "*"

le    a b   = BinOp "<" a b
min   a b k = If (le b a) (k b) (k a)
eq    a b   = BinOp "==" a b

data GenIV' i v = Gen
  { current    :: (i -> T) -> T
  , value      :: (Maybe v -> T) -> T
  , next       :: (Maybe T -> T) -> T
  , reset :: T
  , initialize :: T
  }
type GenIV i v = GenIV' (Maybe i) v
type GenV v = GenIV E v
type Gen = GenIV E E
type UnitGen = GenIV () E

data LGenIV' i v = LGen
  { gen :: GenIV' i v
  , locate :: i -> T
  }
type LGenIV i v = LGenIV' (Maybe i) v
type LGenV v = LGenIV E v
type LGen  = LGenIV E E

genMap' f g gen = Gen
  { current = current gen . (. f)
  , value = value gen . (. g)
  , next = next gen
  , reset = reset gen
  , initialize = initialize gen
  }

genMap f g gen = Gen
  { current = current gen . (. fmap f)
  , value = value gen . (. fmap g)
  , next = next gen
  , reset = reset gen
  , initialize = initialize gen
  }

instance Functor (GenIV' i) where
  fmap f = genMap' id (fmap f)
instance Functor (LGenIV' i) where
  fmap f lg = lg { gen = fmap f (gen lg) }

imap f = genMap' (fmap f) id

sparseVec index_array value_array = genMap
  (Offset index_array)
  (Offset value_array)

emptyGen :: GenIV i v
emptyGen = Gen { next = ($ Nothing) , current = ($ Nothing) , value = ($ Nothing) , reset = Skip , initialize = Skip }

singleton :: a -> GenIV () a
singleton v = Gen { next = ($ Nothing) , current = ($ (Just ())) , value = ($ Just v) , reset = Skip , initialize = Skip }

range :: E -> E -> Gen
range n var =
  let i = var in
  let
    current k = If (le i n) (k $ Just $ var) (k Nothing)
    value   k = If (le i n) (k $ Just $ var) (k Nothing)
    next    k = If (le i n) (k $ Just $ E $ Incr var) (k Nothing)
  in
  Gen { current, value, next, initialize = Skip, reset = Store var 0 }

replicate n v g = (\_ -> g) <$> range n v

-- a; b
sequenceGen :: GenIV' i v -> GenIV' i v -> GenIV' i v
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
  , reset = reset a :> reset b
  , initialize = initialize a :> initialize b
  }

class Add a where
  add :: a -> a -> a
  zero :: a

addGen :: Add a => GenV a -> GenV a -> GenV a
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
                                                    (Just va, Just vb) -> k $ Just (add va vb)
                                                    (Nothing, Just _) -> k vb
                                                    (Just _, Nothing) -> k va
                                                    (Nothing, Nothing) -> k $ Just zero))))
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
    Gen { current = c, value = v, next = n, initialize = initialize a :> initialize b, reset = reset a :> reset b }

instance Add E where
  add = (+)
  zero = Lit 0

instance Add a => Add (GenV a) where
  add = addGen
  zero = emptyGen

class Mul a where
  mul :: a -> a -> a

mulGen :: (Mul a) => GenV a -> GenV a -> GenV a
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
    Gen { current = c, value = v, next = n, initialize = initialize a :> initialize b, reset = reset a :> reset b }

mulGL :: (Mul a) => GenV a -> LGenV a -> GenV a
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
    Gen { current = c, value = v, next = n, initialize = initialize a :> initialize (gen b), reset = reset a :> reset (gen b) }

instance Mul E where
  mul = (*)

instance Mul a => Mul (GenV a) where
  mul = mulGen

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
  Call f es        -> e2c f ++ (wrap $ intercalate "," $ map e2c es)
  RecordAccess e f -> e2c e ++ "." ++ f
  Deref e          -> wrap $ "*" ++ e2c e
  Address e        -> "&" ++ e2c e
  e                -> error (show e)

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
data CType = CFloat | CInt | Storage CType | Sparse CType
type Map a b = [(a, b)]
type SymbolTable = Map String CType
type M = StateT (Int, SymbolTable) (WriterT String (Reader Context))
mapFst f (a, b) = (f a, b)
mapSnd f (a, b) = (a, f b)
runM :: M () -> (SymbolTable, String)
runM = mapFst snd . flip runReader emptyContext . runWriterT . flip execStateT (0, [])

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
      Put l [i] r         -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
      Put l (i:_) r       -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
      Accum l r           -> emit $ e2c l ++ " += " ++ e2c r ++";"
      Label l             -> emit $ "\n" ++ l ++ ":\n"
      Jump  l             -> emit $ "goto " ++ l ++ ";"
      Skip                -> ""
      a :> b              -> t2c a >> local (\_ -> emptyContext) (t2c b)
      E e                 -> emit $ e2c e ++ ";\n"
      AutoDecl i e        -> emit $ "auto " ++ i ++ " = " ++ e2c e ++ ";\n"
      DeclareInt e        -> emit $ "int " ++ e ++ " = 0;\n"
      Store l r           -> emit $ e2c l ++ " = " ++ e2c r ++ ";"
      FloatInit (Ident v) -> emit $ "num " ++ v ++ " = 0.0;\n"
      FloatInit _         -> error "todo, FloatInit"
      Comment s           -> emit $ "// " ++ s ++ "\n"
      Debug s             -> emit s
      If c t e            -> compileIf c t e
      Block t             -> emit "{" >> t2c t >> emit "}"
      Labels ls           -> emit $ "__label__ " ++ intercalate "," ls ++ ";\n"
      t                   -> error $ show t
  where
    compileIf c t e = do
      pathCondition <- ask -- some premature code simplification
      if c `trueElem` pathCondition then t2c t else
        if c `falseElem` pathCondition then t2c e else do
          emit $ "if (" ++ e2c c ++ ") {" ; local (pushTrue c) (t2c t) ; emit "}";
          eTriv <- evalTrivial e
          if eTriv then "" else do emit " else {" ; local (pushFalse c) (t2c e) ; "}"

maybeTuple :: (Maybe a1, Maybe a2) -> Maybe (a1, a2)
maybeTuple = uncurry $ liftM2 (,)

class HasTop a where
  top :: a

instance HasTop (Maybe E) where
  top = Nothing

freshLabel :: String -> M String
freshLabel n = do
  (k, m) <- get
  let name = n ++ show k
  put (k+1, m)
  return $ name

fresh :: String -> CType -> M String
fresh n t = do
  (k, m) <- get
  let name = n ++ show k
  put (k+1, (name, t) : m)
  return $ name

loopT :: M (GenIV () T -> T)
loopT = do
  loop <- freshLabel "loop"
  done <- freshLabel "done"
  return $ \g ->
    -- initialize g :>
    Block $
      Labels [loop, done] :>
      reset g :>
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

initHeader :: SymbolTable -> String
initHeader = concatMap step
  where
    typeString CFloat = "num"
    typeString CInt = "index"
    typeString (Storage t) = "SparseStorageArray<" ++ typeString t ++ ">"
    typeString (Sparse t) = "SparseArray<" ++ typeString t ++ ">"
    step (name, CFloat) = "num " ++ name ++ " = 0;\n"
    step (name, CInt) = "index " ++ name ++ " = 0;\n"
    step (name, t) = typeString t ++ " " ++ name ++ ";\n"

compile :: M T -> IO ()
compile t = do
  let outName = "out.cpp"
  writeFile outName . addHeader . runM $ t >>= t2c
  callCommand $ "clang-format -i " ++ outName
  where
    addHeader (st, s) =
      "#include \"prefix.cpp\"\n"
      ++ initHeader st
      ++ s
      ++ "#include \"suffix.cpp\"\n"

-- remove examples:
fl2 = fl . fmap fl
parseNode :: E -> (E, E, E)
parseNode e = (RecordAccess e "length", RecordAccess e "indices", RecordAccess e "children")
parseNodeIter :: Gen -> GenV (E, E, E)
parseNodeIter = fmap $ parseNode
uncurry3 f (a,b,c) = f a b c
leafIter i (len, is, vs) = range len i & sparseVec is vs
nodeIter i (len, is, vs) = range len i & sparseVec is vs & parseNodeIter
--chk = compile . loop (Ident "acc")
--main1 = chk . fl2 $ tIJK
--main2 = chk $ fl  $ mul (t2 "A" "iA" "jA" ) (t2 "B" "iB" "jB" )
--main3 = chk $ fl2 $ mul (t3 "C" "iA" "jA" "kA") (t3 "D" "iB" "jB" "kB")
tIJK       = parseNode "tree" & nodeIter "i" & fmap (nodeIter "j" .> fmap (leafIter "k"))
t2 t i j   = parseNode t & nodeIter i & fmap (leafIter j)
t3 t i j k = parseNode t & nodeIter i & fmap ((nodeIter j) .> fmap (leafIter k))
-- remove examples ^

chk' = compile . (loopT <**> )

flatten :: GenIV i1 (GenIV i2 a) -> GenIV (i1, Maybe i2) a
flatten outer =
  let
    n k =
      value outer $ \minner -> case minner of
        Nothing -> next outer $ k . fmap ( :> (value outer $ \minner -> case minner of
                                       Nothing -> Comment "still nothing"
                                       Just inner -> reset inner))
        Just inner  -> next inner $ \mstep -> case mstep of
          Just _ -> k mstep
          Nothing -> next outer $ k . fmap (:> reset inner)
    c k = current outer $ \i1 -> case i1 of
            Nothing -> k Nothing
            Just i1 -> value outer $ \minner -> case minner of
              Nothing -> k $ Just (i1, Nothing)
              Just inner -> current inner $ \i2 -> k $ Just (i1, i2)
    v k = value outer $ \minner -> case minner of
            Nothing -> (k Nothing)
            Just inner -> value inner k
    r = reset outer :>
        (value outer $ \minner -> case minner of
            Nothing -> Comment "nothing yet"
            Just inner -> initialize inner :> reset inner)
    i = initialize outer :> Comment "wrong?"
  in
    Gen { next = n, current = c, value = v, reset = r, initialize = i }

fl :: GenIV i1 (GenIV i2 a) -> GenIV i2 a
fl = flatten .> imap snd .> genMap' join id -- flatten Maybe nesting in coordinate
fl' :: GenIV () (GenIV i2 a) -> GenIV i2 a
fl' = fl

externGen :: E -> Gen
externGen x =
  let call op = Call (RecordAccess x op) [] in
  let check op k = If (call "done") (k Nothing) (k (Just $ E $ call op)) in
  let check' op k = If (call "done") (k Nothing) (k (Just $ call op)) in
  Gen
  { next = check "next"
  , current = check' "current"
  , value = check' "value"
  , reset = (E $ call "reset")
  , initialize = Skip
  }

externStorageGen :: E -> LGen
externStorageGen x =
  let g = externGen x in
  let call op = Call (RecordAccess x op) [] in
  let check' op k = If (call "done") (k Nothing) (k (Just $ call op)) in
  LGen
  {
    -- no bounds check done; assume that it can always give a storage location
    gen = g { value = \k -> (k (Just $ Deref $ call "value_ref"))
  }
  , locate = \i -> case i of
      Nothing -> E $ call "finish"
      Just i -> E $ Call (RecordAccess x "skip") [i]
  }

accumulator :: E -> LGenIV () E
accumulator acc = LGen {gen = singleton (acc), locate = const Skip}

accumulateLoop :: E -> UnitGen -> GenIV () T
accumulateLoop acc gen =
  let g = fmap (\e -> Accum acc e) gen
  in g { reset      = Store acc 0 :> reset g }

prefixGen t gen = gen { reset = t :> reset gen }

class Storable l r out where
  store :: l -> r -> out
instance Storable E E T where
  store loc val = Accum loc val
instance Storable E UnitGen (GenIV () T) where
  store = accumulateLoop
instance (Storable l r out) =>
  Storable (LGenIV i l)
           (GenIV  i r)
           (GenIV () out) where
  store l r = Gen
    { next = \k -> next r $ fmap (\step -> step :> (value r $ \mv -> case mv of
                                         Nothing -> Skip
                                         Just _ -> (current r $ locate l))) .> k
    , current = ($ Just ())
    , value = \k -> value (gen l) $ \mloc -> case mloc of
        Nothing -> error "unreachable"
        Just loc -> value r $ fmap (\val -> store loc val) .> k
    , reset = reset (gen l) :> reset r :> (current r $ locate l)
    , initialize = initialize (gen l) :> initialize r
    }

contraction1 :: M (GenV UnitGen -> UnitGen)
contraction1 = do
  acc <- Ident <$> fresh "acc" CFloat
  loop <- loopT
  return $ \v ->
    prefixGen
      (Store acc 0 :> loop (store (accumulator acc) (fl v)))
      (singleton $ acc)

f <**> a = f <*> (pure a)

index' i = Ident <$> fresh i CInt
index = index' "i"
accum a = Ident <$> fresh a CFloat
matrix = Ident <$> fresh "t" (Sparse (Sparse CFloat))
vector = Ident <$> fresh "v" (Sparse (CFloat))
storeVec = Ident <$> fresh "v" (Storage (CFloat))
storeMat = Ident <$> fresh "v" (Storage (Storage CFloat))

--putT = do
--  out <- matrix
--  i <- index "i"
--  j <- index "i"
--  b1 <- loopT <**> (store (externStorageGen out & gmap externStorageGen) (range 10 i & gmap (const (range 4 j))))
--  return (out, b1)
eg1 = chk' $ store (externStorageGen "out") (range 10 "i")
eg2 = chk' $ store (externStorageGen "out1") (externGen "t2")
eg3 = compile $ do
  let tv x = Call "toVal" [x]
  out1 <- storeVec
  out2 <- storeVec
  out <- storeVec
  v1 <- vector
  v2 <- vector
  i <- index
  let n = 5
  b1 <- (loopT <**> (store (externStorageGen out1) (range n i)))
  b2 <- (loopT <**> (store (externStorageGen out2) (range n i)))
  b3 <- (loopT <**> (store (externStorageGen out) (mulGen (externGen v1) (externGen v2))))
  return $ b1 :> b2 :> Store v1 (tv out1) :> Store v2 (tv out2) :> b3 :> E (Call "printArray_" [out])
eg3' = compile $ do
  let tv x = Call "toVal" [x]
  out <- storeVec
  v1 <- vector
  v2 <- vector
  i <- index
  b3 <- (loopT <**> (store (externStorageGen out) (mulGen (externGen v1) (externGen v2))))
  return $  b3 :> E (Call "printArray_" [out])
eg4 = compile $ do
  let p = (fl' $ (store (externStorageGen "out2" & fmap externStorageGen) (range 10 "i" & fmap (const $ range 20 "j")))) :: GenIV () T
  b1 <- (loopT <**> p)
  return b1
eg5 = compile $ do
  i <- index
  j <- index
  let expr = range 10 i & fmap (singleton)
  out1 <- contraction1 <*> pure expr
  --out2 <- contraction1 out1
  acc <- accum "out_acc"
  b1 <- loopT <**> accumulateLoop acc out1
  return $ b1 :> Debug ("printf(\"result: %.1f\\n\", " ++ e2c acc ++ ");\n")

-- double contraction
eg6 rows = compile $ do
  i <- Ident <$> fresh "i" CInt
  j <- Ident <$> fresh "j" CInt
  let expr = range rows i & fmap (const (range 4 j) .> fmap (singleton ))
  c1 <- contraction1
  c2 <- contraction1
  let out1 = fmap c1 expr
  let out2 = c2 out1
  acc <- Ident <$> fresh "out_acc" CFloat
  b1 <- loopT <**> accumulateLoop acc out2
  return $ b1 :> Debug ("printf(\"result: %.1f\\n\", " ++ e2c acc ++ ");\n")

eg7 = compile $ do
  t1 <- matrix
  t2 <- matrix
  v1 <- vector
  i <- index
  j <- index
  c1 <- contraction1
  -- let t1' = replicate 5 i t1
  let a1 = fmap externGen $  externGen t1
  let a2 = replicate 5 i $ externGen v1
  let result = fmap c1 $ fmap (fmap singleton) $ mulGen a1 a2
  out <- Ident <$> fresh "t" (Storage CFloat)
  loopT <**> (fl' $ store (externStorageGen out) result)
