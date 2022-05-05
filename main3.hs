{-

merge branch
  cleanup T, E
  cleanup file

fix code size?
  ! add complete boolean conditions to path
compare taco

non-scalar contraction

fix broadcasting syntax
automatic broadcasting
  index types

modularity over semiring

automatic flatten stores?
  typeclass for output/flatten
insert structural comments into output

maybe implement semantics bracket?
-}
{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Codegen where
import Prelude hiding (min, max, replicate, String, concat)
import Control.Monad (join)
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import Data.Maybe
import Data.List hiding (singleton, replicate, intercalate, concat)
import Data.String (IsString, fromString)
import Data.Text (Text, intercalate, unpack, pack, concat)
import qualified Data.Text.IO as T
import Data.Function
import System.Process

debug = False

type String = Text

showT :: Show a => a -> String
showT = fromString . show

sorry = undefined

type Label = Text
type IVar = Text

data T
  = E E
  | Put E [E] E | Accum E E | Store E E
  | Label Label | If E T T | If1 E T | Jump Label | (:>) T T | Skip
  | Comment Text
  | Debug Text
  | Block T
  | Labels [Text]
  deriving Show
unreachable s = Comment $ "unreachable: " <> s

data E
  = Lit Integer | IVar IVar | Ident Text
  | Incr E
  | Offset E E | BinOp Text E E
  | RecordAccess E Text
  | Call E [E]
  | Deref E
  | Address E
  | Extern Text
  deriving (Show, Eq)

instance (IsString E)
  where fromString = Ident . fromString

instance Num E where
  fromInteger = Lit
  (+) = BinOp "+"
  (*) = BinOp "*"
  abs = sorry
  signum = sorry
  negate = sorry

le    a b   = BinOp "<" a b
min   a b k = If (le b a) (k b) (k a)
max   a b k = If (le b a) (k a) (k b)
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
type UnitGenV v = GenIV () v
type UnitGen = UnitGenV E

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

emptyGen :: GenIV i v
emptyGen = Gen { next = ($ Nothing) , current = ($ Nothing) , value = ($ Nothing) , reset = Skip , initialize = Skip }

singleton :: a -> GenIV () a
singleton v = Gen
  { next = ($ Nothing) , current = ($ (Just ())) , value = ($ Just v) , reset = Skip , initialize = Skip }

range :: E -> E -> Gen
range n var =
  let i = var in
  let
    current k = If (le i n) (k $ Just $ var) (k Nothing)
    value   k = If (le i n) (k $ Just $ var) (k Nothing)
    next    k = If (le i n) (k $ Just $ E $ Incr var) (k Nothing)
  in
  Gen { current, value, next, initialize = Skip, reset = Store var 0 }

--replicate n v g = const g <$> range n v
replicateGen n v g =
  let gen = (const g <$> range n v) in
    gen { initialize = initialize gen :> initialize g
        , next = \k -> next gen $ fmap (:> reset g) .> k }

-- a; b
sequenceGen :: GenIV' i v -> GenIV' i v -> GenIV' i v
sequenceGen a b = Gen
  { next = \k -> next a $ \mstep -> case mstep of -- repeated check after a done
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

addUnitGen :: (Add a) => UnitGenV a -> UnitGenV a -> UnitGenV a
addUnitGen = sequenceGen

instance Add E where
  add = (+)
  zero = Lit 0

instance Add a => Add (GenV a) where
  add = addGen
  zero = emptyGen

class Mul a where
  mul :: a -> a -> a

mulUnitGen :: (Mul a) => UnitGenV a -> UnitGenV a -> UnitGenV a
mulUnitGen a b =
  let
    c = ($ (Just ()))
    v k = value a $ \va -> case va of
            Nothing -> k Nothing
            Just va -> value b $ \vb -> case vb of
              Nothing -> k Nothing
              Just vb -> k (Just (mul va vb))
    n k =
      let warning = "multiplied unit generators must be static singletons. did you forget to aggregate?" in
      next a $ \ia -> case ia of
      Nothing -> next b $ \ib -> case ib of
        Nothing -> k Nothing
        Just _ -> error warning
      Just _ -> error warning
  in
    Gen { current = c, value = v, next = n, initialize = initialize a :> initialize b, reset = reset a :> reset b }

mulGen :: (Mul a) => GenV a -> GenV a -> GenV a
mulGen a b =
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

    -- potential optimization: include definedness in the next condition; take the max of the children as the next possible non-zero
    c' k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current b $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> max ia ib (k . Just)
    n' k = current a $ \ia -> case ia of
      Nothing -> k Nothing
      Just ia -> current b $ \ib -> case ib of
        Nothing -> k Nothing
        Just ib -> If (le ia ib) (next a k) $ If (le ib ia) (next b k) $
          value a $ \va -> case va of
            Nothing -> next a k
            Just _ -> next b k
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
instance Mul a => Mul (UnitGenV a) where
  mul = mulUnitGen

wrap s = "(" <> s <> ")"
e2c :: E -> Text
e2c e = case e of
  Lit i            -> showT i
  IVar i           -> i
  Incr i           -> wrap $ e2c i <> "++"
  Ident i          -> i
  BinOp op e1 e2   -> wrap $ e2c e1 <> op <> e2c e2
  Offset b i       -> e2c b <> "[" <> e2c i <> "]"
  Call f es        -> e2c f <> (wrap $ intercalate "," $ map e2c es)
  RecordAccess e f -> e2c e <> "." <> f
  Deref e          -> wrap $ "*" <> e2c e
  Address e        -> "&" <> e2c e
  e                -> error (show e)

data Context = Context
  { trueConditions :: [E]
  , falseConditions :: [E] }

disablePathCondition = False
negateOp "==" = "!="
negateOp "!=" = "=="
negateOp "<" = ">="
negateOp ">=" = "<"
negateOp ">" = "<="
negateOp "<=" = ">"
--completeNegationCondition _ = []
completeNegationCondition e@(BinOp "==" a b) = [BinOp "!=" a b, BinOp "<" a b, BinOp "<" b a]
completeNegationCondition e@(BinOp "<" a b) = [BinOp "==" a b, BinOp ">" a b]
completeNegationCondition _ = []
pushTrue e c  = if disablePathCondition then c else c {
  trueConditions = e : trueConditions c,
  falseConditions = completeNegationCondition e ++ falseConditions c }
pushFalse e c = if disablePathCondition then c else c { falseConditions = e : falseConditions c}
trueElem e c = e `elem` trueConditions c
falseElem e c = e `elem` falseConditions c
emptyContext = Context [] []

data SemiringType = SInt | SFloat
data TensorType
  = TTAtom SemiringType
  | TTStorage TensorType
  | TTSparse TensorType
toCType :: TensorType -> CType
toCType (TTAtom SInt) = CInt
toCType (TTAtom SFloat) = CDouble
toCType (TTStorage t) = CStorage (toCType t)
toCType (TTSparse t) = CSparse (toCType t)

data CType = CDouble | CInt | CStorage CType | CSparse CType
type Map a b = [(a, b)]
type SymbolTable = Map Text TensorType
type M = StateT (Int, SymbolTable) (WriterT Text (Reader Context))
symbolType :: String -> M TensorType
symbolType s = do
  (_, m) <- get
  return $ fromJust $ lookup s m

mapFst f (a, b) = (f a, b)
mapSnd f (a, b) = (a, f b)
runM :: M () -> (SymbolTable, Text)
runM = mapFst snd . flip runReader emptyContext . runWriterT . flip execStateT (0, [])

emit :: Text -> M ()
emit s = tell s

instance (IsString (M ())) where
  fromString = emit . pack

wrapm :: M () -> M ()
wrapm s = emit "(" >> s >> ")"

-- returns Nothing if t can be shown to have no effect
-- returns a recursively simplified version of t otherwise
evalTrivial :: T -> M (Maybe T)
evalTrivial Skip       = return Nothing
evalTrivial (Comment _) = return Nothing
evalTrivial (If c t e) = do
  pathCondition <- ask
  if c `trueElem` pathCondition then evalTrivial t else
    if c `falseElem` pathCondition then evalTrivial e else do
      tt <- local (pushTrue c) $ evalTrivial t
      et <- local (pushFalse c) $ evalTrivial e
      return $
        case (tt, et) of
          (Nothing, Nothing) -> Nothing
          (Just t, Nothing) -> Just $ If1 c t
          _ -> Just $ If c (fromMaybe t tt) (fromMaybe e et)

evalTrivial e@(a :> b) = do
  ma <- evalTrivial a
  mb <- local (\_ -> emptyContext) $ evalTrivial b
  return $ case ma of
    Nothing -> mb
    Just a ->
      case mb of
        Nothing -> ma
        Just b -> Just $ a :> b
evalTrivial e          = return $ Just e

t2c :: T -> M ()
t2c t = do
    triv <- evalTrivial t
    case triv of
      Nothing -> ""
      Just t -> case t of
        Put l [i] r         -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
        Put l (i:_) r       -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
        Accum l r           -> emit $ e2c l <> " += " <> e2c r <>";"
        Label l             -> emit $ "\n" <> l <> ":\n"
        Jump  l             -> emit $ "goto " <> l <> ";"
        Skip                -> ""
        Skip :> Skip              -> "// oops\n"
        a :> b              -> t2c a >> local (\_ -> emptyContext) (t2c b)
        E e                 -> emit $ e2c e <> ";\n"
        Store l r           -> emit $ e2c l <> " = " <> e2c r <> ";"
        Comment s           -> emit $ "// " <> s <> "\n"
        Debug s             -> emit s
        If c t e            -> do
          emit $ "if (" <> e2c c <> ") {" ; local (pushTrue c) (t2c t) ; emit "}";
          emit " else {" ; local (pushFalse c) (t2c e) ; "}"
        If1 c t             -> do
          emit $ "if (" <> e2c c <> ") {" ; local (pushTrue c) (t2c t) ; emit "}";
        Block t             -> emit "{// block\n" >> t2c t >> emit "}"
        Labels ls           -> emit $ "__label__ " <> intercalate "," ls <> ";\n"
        t                   -> error $ show t
  where
    --compileIf c t e = do
    --  pathCondition <- ask -- some premature code simplification
    --  if c `trueElem` pathCondition then t2c t else
    --    if c `falseElem` pathCondition then t2c e else do
    --      emit $ "if (" <> e2c c <> ") {" ; local (pushTrue c) (t2c t) ; emit "}";
    --      eTriv <- evalTrivial e
    --      if eTriv then "" else do emit " else {" ; local (pushFalse c) (t2c e) ; "}"
    --compileIf c t e = do
    --      emit $ "if (" <> e2c c <> ") {" ; local (pushTrue c) (t2c t) ; emit "}";
    --      eTriv <- evalTrivial e
    --      if eTriv then "" else do emit " else {" ; local (pushFalse c) (t2c e) ; "}"

maybeTuple :: (Maybe a1, Maybe a2) -> Maybe (a1, a2)
maybeTuple = uncurry $ liftM2 (,)

class HasTop a where
  top :: a

instance HasTop (Maybe E) where
  top = Nothing

freshLabel :: String -> M String
freshLabel n = do
  (k, m) <- get
  let name = n <> showT k
  put (k+1, m)
  return $ name

freshBad :: String -> TensorType -> M String
freshBad n t = do
  (k, m) <- get
  let name = n
  put (k+1, (name, t) : m)
  return $ name

fresh :: String -> TensorType -> M String
fresh n t = do
  (k, m) <- get
  let name = n <> showT k
  put (k+1, (name, t) : m)
  return $ name

loopT :: M (GenIV () T -> T)
loopT = do
  let loop = "loop"
  let done = "done"
  --loop <- freshLabel "loop"
  --done <- freshLabel "done"
  return $ \g ->
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
      :> Debug ";"
      :> if debug then Debug "printf(\"loops: %d\\n\", __i);\n" else Skip

(.>) = flip (.)

initHeader :: SymbolTable -> String
initHeader = concat . map (step . mapSnd toCType)
  where
    typeString CDouble = "num"
    typeString CInt = "index"
    typeString (CStorage t) = "SparseStorageArray<" <> typeString t <> ">"
    typeString (CSparse t) = "SparseArray<" <> typeString t <> ">"
    step (name, CDouble) = "num " <> name <> " = 0;\n"
    step (name, CInt) = "index " <> name <> " = 0;\n"
    step (name, t) = typeString t <> " " <> name <> ";\n"

printingSuffix :: SymbolTable -> String
printingSuffix = concat . mapMaybe (step . mapSnd toCType)
  where
    step (name, (CStorage (CStorage CDouble))) =
      Just $ "printMat_(" <> name <> ");\n"
    step (name, (CStorage CDouble)) =
      Just $ "printArray_(" <> name <> ");\n"
    step (name, CDouble) =
      Just $ "printf(\"" <> name <> ": %f\\n\"," <> name <> ");\n"
    step _ = Nothing

disablePrinting = False

compile :: M T -> IO ()
compile t = do
  let outName = "out.cpp"
  T.writeFile outName . addHeader . runM $ t >>= t2c
  callCommand $ "clang-format -i " <> outName
  where
    addHeader (st, s) =
      "#include \"prefix.cpp\"\n"
      <> initHeader st
      <> s
      <> (if disablePrinting then "" else printingSuffix st)
      <> "#include \"suffix.cpp\"\n"

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
          Nothing -> next outer $ \mstep -> case mstep of
            Nothing -> k Nothing
            Just step -> k $ Just $ step :> (value outer $ \minner -> case minner of
              Nothing -> (Comment "nothing")
              Just inner -> reset inner)
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
            Just inner -> reset inner)
            --Just inner -> initialize inner :> reset inner)
    i = initialize outer :> Comment "wrong?"
  in
    Gen { next = n, current = c, value = v, reset = r, initialize = i }

fl :: GenIV i1 (GenIV i2 a) -> GenIV i2 a
fl = flatten .> imap snd .> genMap' join id -- flatten Maybe nesting in coordinate
-- needed for type inference in some cases
fl' :: GenIV () (GenIV i2 a) -> GenIV i2 a
fl' = fl
down = fl'
down2 = fl' . fl'
down3 = fl' . fl' . fl'

externGen :: E -> Gen
externGen x =
  let call op = Call (RecordAccess x op) [] in
  let check  op k = If (call "done") (k Nothing) (k (Just $ E $ call op)) in
  let check' op k = If (call "done") (k Nothing) (k (Just $ call op)) in
  Gen
  { next = check "next"
  , current = check' "current"
  , value = check' "value"
  , reset = E $ call "reset"
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

accumulateLoop :: E -> UnitGen -> GenIV () T
accumulateLoop acc gen =
  let g = fmap (\e -> Accum acc e :> if debug then E (Call "printf" ["\"acc: %f\"", e]) else Skip) gen
  in g { reset      = Store acc 0 :> reset g }

prefixGen t gen = gen { reset = t :> reset gen }

class Storable l r out where
  store :: l -> r -> out
instance Storable E UnitGen (GenIV () T) where
  store = accumulateLoop
instance (Storable l r out) =>
  Storable (LGenIV i l)
           (GenIV  i r)
           (GenIV () out) where
  store l r = Gen
    { next = \k -> next r $ fmap (\step -> step :> (value r $ \mv -> case mv of
                                         Nothing -> Comment "don't update storage"
                                         Just _ -> (current r $ locate l))) .> k
    , current = ($ Just ())
    , value = \k -> value (gen l) $ \mloc -> case mloc of
        Nothing -> error "unreachable"
        Just loc -> value r $ fmap (\val -> store loc val) .> k
    , reset = reset (gen l) :> reset r :> (current r $ locate l)
    , initialize = initialize (gen l) :> initialize r
    }

cdouble = TTAtom SFloat
cint = TTAtom SInt
cstorage x = TTStorage x
csparse x = TTSparse x

contraction1 :: M (GenV UnitGen -> UnitGen)
contraction1 = do
  --let acc = "acc"
  acc <- Ident <$> fresh "acc" cdouble
  loop <- loopT
  return $ \v ->
    (prefixGen
      (Store acc 0 :> loop (store (acc) (fl v)))
      ((singleton $ acc) { initialize = initialize v, reset = reset v }))

f <**> a = f <*> (pure a)

index' i = Ident <$> fresh i cint
index = index' "i"
accum a = Ident <$> fresh a cdouble
matrix = Ident <$> fresh "t" (csparse (csparse cdouble))
vector = Ident <$> fresh "v" (csparse (cdouble))
storeVec = Ident <$> fresh "v" (cstorage (cdouble))
storeMat = Ident <$> fresh "v" (cstorage (cstorage cdouble))

run mgen = compile $ do
  gen <- mgen
  l <- loopT
  return $ initialize gen :> (l gen)

-- Short operators for constructing expressions
type VectorGen = GenIV' (Maybe E) (GenIV () E)
type MatrixGen = GenIV' (Maybe E) (GenIV' (Maybe E) (GenIV () E))
m :: String -> M MatrixGen
m v = do
  let file = "cavity11/cavity11.mtx"
  --let file = "smallM.mtx"
  var <- Ident <$> fresh v (csparse (csparse cdouble))
  let gen = fmap (fmap singleton) $ fmap externGen (externGen $ var)
  return $ gen {initialize = Store var (Call "loadmtx" [Ident $ "\"" <> file <> "\""])}
v :: String -> M VectorGen
v v = do
  --let file = "cavity11/cavity_ones.mtx"
  --let file = "cavity11/cavity11_x.mtx"
  let file = "smallV.mtx"
  var <- Ident <$> fresh v (csparse (cdouble))
  let gen = fmap singleton $ externGen $ var
  return $ gen { initialize = Store var (Call "loadvec" [Ident $ "\"" <> file <> "\""])}
vvar  = do
  var <- Ident <$> fresh "t" (cstorage cdouble)
  return $ externStorageGen var
mvar  = do
  var <- Ident <$> fresh "t" (cstorage (cstorage cdouble))
  return $ fmap externStorageGen (externStorageGen var)
float = Ident <$> fresh "v" cdouble
int = Ident <$> fresh "v" cint

infixl 6 <+>
(<+>) :: Add a => M a -> M a -> M a
(<+>) = liftM2 add
infixl 7 <.>
(<.>) :: Mul a => M a -> M a -> M a
(<.>) = liftM2 mul
infix 2 <--
(<--) :: Storable a b c => M a -> M b -> M c
(<--) = liftM2 store
sum1 x = contraction1 <*> x
sum2 x = liftM fmap contraction1 <*> x
sum3 x = do
  c <- contraction1
  (fmap (fmap c)) <$> x
-- todo fix
repl1 x = replicateGen 3000  <$> int <*> x
repl2 x = do
  i <- int
  fmap (replicateGen 5 i) <$> x

egMdotM  = run $ down2 <$> (mvar <-- m "A" <.> m "B")
egMMM  = run $ down2 <$> (mvar <-- m "A" <.> m "B" <.> m "C")
egMdotMSum = run $ float <-- sum1 (sum2 (m "A" <.> m "B"))
-- dot, matrix-vector product, matrix-matrix product
egVV = run $ float <-- sum1 (v "u" <.> v "v")
egMV = run $ down <$> (vvar <-- sum2 (m "A" <.> repl1 (v "x")))
egMV' = run $ down2 <$> (mvar <-- (m "A" <.> repl1 (v "x")))
egMM = run $ down2 <$> (mvar <-- sum3 (repl2 (m "A") <.> repl1 (m "B")))
egVVV = run $ down <$> (vvar <-- (v "u" <.> v "v" <.> v "w"))
egMSum = run $ (float <-- sum1 (sum2 (m "A")))
