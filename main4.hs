{-
add addGen
-}
{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Codegen where
import Prelude hiding (min, max, replicate, String, concat, and, or, repeat)
import Control.Monad (join)
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import Data.Maybe
--import Data.List hiding (singleton, replicate, intercalate, concat, and, repeat)
import Data.String (IsString, fromString)
import Data.Text (Text, intercalate, unpack, pack, concat)
import qualified Data.Text.IO as T
import Data.Function
import Data.Functor.Identity
import System.Process
import System.IO.Unsafe

type String = Text

showT :: Show a => a -> String
showT = fromString . show

-- utils
sorry = undefined
(.>) = flip (.)
mapFst f (a, b) = (f a, b)
mapSnd f (a, b) = (a, f b)
unsafePrint s e = unsafePerformIO $ print s >> return e

------- Begin Types -------

type Label = Text
type IVar = Text

data E
  = Lit Integer | IVar IVar | Ident Text
  | BinOp Text E E
  | RecordAccess E Text
  | Call E [E]
  | Deref E

  | Ternary E E E | And E E | Or E E
  deriving (Show, Eq)

instance (IsString E)
  where fromString = Ident . fromString
instance Num E where
  fromInteger = Lit;
  (+) = BinOp "+"; (*) = BinOp "*"
  abs = sorry; signum = sorry; negate = sorry;

le a b   = BinOp "<" a b
eq a b   = BinOp "==" a b
min a b = Call "min" [a, b]
--min a b = Ternary (le a b) a b
and a 1 = a
and 1 a = a
and a b = And a b
or 0 a = a
or a 0 = a
or a b = Or a b

data T
  = E E
  | Put E [E] E | Accum E E | Store E E
  | Next E
  | If E T T | If1 E T | (:>) T T | Block T
  | Label Label | Labels [Text] | Jump Label
  | Comment Text | Debug Text
  | Skip
  deriving (Show, Eq)

data GenIV i v = Gen
  { current    :: i , value      :: v
  , ready      :: E , empty      :: E
  , next       :: (Maybe T -> T) -> T
  , reset      :: T , initialize :: T
  }
type GenV v = GenIV E v
type Gen = GenIV E E
type UnitGenV v = GenIV () v
type UnitGen = UnitGenV E

data LGenIV i v = LGen { gen :: GenIV i v , locate :: i -> T}
type LGenV v = LGenIV E v
type LGen  = LGenIV E E

instance Functor (GenIV i) where
  fmap f g = g { value = f $ value g }
instance Functor (LGenIV i) where
  fmap f lg = lg { gen = fmap f (gen lg) }

imap f g = g {current = g & current & f}

class HasTop a where
  top :: a
instance HasTop (Maybe E) where
  top = Nothing
instance HasTop () where
  top = ()

------- Begin Gen combinators -------

loopT :: GenIV () T -> T
loopT g =
  let loop = "loop" in
  let done = "done" in
  Block $
    Labels [loop, done] :>
    reset g :>
    Debug "__i = 0;" :>
    Label loop :>
    Debug "__i++;" :>
    If (ready g) (value g) Skip :>
    (next g $ \ms -> case ms of
        Nothing -> Jump done
        Just s -> s :> Jump loop) :>
    Label done
    :> if debug then Debug "printf(\"loops: %d\\n\", __i);\n" else Skip

emptyGen :: GenIV () v
emptyGen = Gen
  { current = top , value = sorry
  , ready = 0 , empty = 1
  , next = ($ Nothing)
  , reset = Skip , initialize = Skip
}

singleton :: a -> GenIV () a
singleton v = emptyGen { value = v , current = () , ready = 1 }

range :: E -> E -> Gen
range n var = Gen
  { current = var , value = var
  , ready = le var n , empty = eq var n
  , next = \k -> If (le var n) (k $ Just $ Next var) (k Nothing)
  , reset = Store var 0 , initialize = Skip
  }

repeat :: E -> GenIV i a -> GenV (GenIV i a)
repeat var v = Gen
  { current = var , value = v
  , ready = 1 , empty = 0
  , next = \k -> k . Just $ Next var :> reset v
  , reset = Store var 0 , initialize = initialize v
  }

class Mul a where
  mul :: a -> a -> a

mulGen :: Mul a => GenV a -> GenV a -> GenV a
mulGen a b = Gen
  { current = min (current a) (current b)
  , value = value a `mul` value b
  , ready = eq (current a) (current b) `and` ready a `and` ready b
  , empty = empty a `or` empty b
  , next = \k -> If (empty a `or` empty b) (k Nothing) $
      If (le (current a) (current b)) (next a k) (next b k)
  , reset = reset a :> reset b
  , initialize = initialize a :> initialize b
  }

mulUnitGen :: Mul a => UnitGenV a -> UnitGenV a -> UnitGenV a
mulUnitGen a b = Gen
  { current = ()
  , value = value a `mul` value b
  , ready = ready a `and` ready b
  , empty = empty a `or` empty b
  , next = \k ->
      let warning = "multiplied unit generators must be static singletons. did you forget to aggregate?" in
      next a $ \ma -> case ma of
      Nothing -> next b $ \mb -> case mb of
        Nothing -> k Nothing
        Just _ -> error warning
      Just _ -> error warning
  , reset = reset a :> reset b
  , initialize = initialize a :> initialize b
  }

instance Mul E where
  mul = (*)
instance Mul a => Mul (GenV a) where
  mul = mulGen
instance Mul a => Mul (UnitGenV a) where
  mul = mulUnitGen

externGen :: E -> Gen
externGen x =
  let call op = Call (RecordAccess x op) [] in
  let check  op k = If (call "done") (k Nothing) (k (Just $ E $ call op)) in
  let check' op k = If (call "done") (k Nothing) (k (Just $ call op)) in
  Gen
  { current = call "current" , value = call "value"
  , ready = 1 , empty = call "done"
  , next = check "next"
  , reset = E $ call "reset" , initialize = Skip
  }

externStorageGen :: E -> LGen
externStorageGen x =
  let g = externGen x in
  let call op = Call (RecordAccess x op) in
  LGen
  { gen = g { value = call "value" [] }
  , locate = \i -> E $ call "skip" [i]
  }

flatten :: GenIV i1 (GenIV i2 a) -> GenIV (i1, i2) a
flatten outer =
  let inner = value outer in Gen
  { current = (current outer, current inner)
  , value = value (value outer)
  , ready = ready outer `and` ready inner
  , empty = empty outer
  , next = \k -> next (value outer) $ \ms -> case ms of
      Just _ -> k ms
      Nothing -> next outer $ \ms -> case ms of
        Nothing -> k Nothing
        Just s -> k . Just $ s :> If1 (ready outer) (reset inner)
  , reset = reset outer :> reset inner
  , initialize = initialize outer :> initialize inner -- ?
  }

fl :: GenIV i1 (GenIV i2 a) -> GenIV i2 a
fl = flatten .> imap snd
-- needed for type inference
fl' :: GenIV () (GenIV () a) -> GenIV () a
fl' = fl
down = fl'
down2 = fl' . fl'

class Storable l r out where
  store :: l -> r -> out
instance Storable E UnitGen (GenIV () T) where
  store acc = fmap (Accum acc) -- e -> Accum acc e
-- basic idea: when we step r, locate a new spot in l to store the result
instance (Storable l r out) =>
  Storable (LGenIV i l)
           (GenIV  i r)
           (GenIV () out) where
  store l r = Gen
    { current = ()
    , value = store (l & gen & value) (value r)
    , ready = ready (gen l) `and` ready r
    , empty = empty r
    , next = \k -> next r $ fmap (\step -> step :> If1 (ready r) (locate l (current r))) .> k
    , reset = reset (gen l) :> reset r :> locate l (current r)
    , initialize = initialize (gen l) :> initialize r
    }

contraction :: E -> GenV UnitGen -> UnitGen
contraction acc v =
  prefixGen
    (Store acc 0 :> loopT (store acc (fl v)))
    ((singleton acc) { initialize = initialize v, reset = reset v })
  where
    prefixGen t gen = gen { reset = t :> reset gen }

------- End Gen combinators -------

------- Begin code output -------

-- see evalTrivial
data Context = Context
  { trueConditions :: [E]
  , falseConditions :: [E] }

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

runM :: M () -> (SymbolTable, Text)
runM = mapFst snd . flip runReader emptyContext . runWriterT . flip execStateT (0, [])

emit :: Text -> M ()
emit s = tell s

instance (IsString (M ())) where
  fromString = emit . pack

wrapm :: M () -> M ()
wrapm s = emit "(" >> s >> ")"

{- evalTrivial: janky path condition simulator -}

-- \forall c \in cPC e, (!e -> !c)
completePositiveConditions e@(Or a b) = e : completePositiveConditions a ++ completePositiveConditions b
completePositiveConditions e = [e]
-- \forall c \in cNC e, (e -> !c)
completeNegativeCondition e@(BinOp "==" a b) = [BinOp "!=" a b, BinOp "<" a b, BinOp "<" b a]
completeNegativeCondition e@(BinOp "<" a b) = [BinOp "==" a b, BinOp ">" a b]
completeNegativeCondition (Or a b) =
  completeNegativeCondition a ++ completeNegativeCondition b
completeNegativeCondition e = [e]
pushTrue e c  = if disablePathCondition then c else c {
  trueConditions = e : trueConditions c,
  falseConditions = completeNegativeCondition e ++ falseConditions c }
pushFalse e c = if disablePathCondition then c else c {
  falseConditions = completePositiveConditions e ++ falseConditions c }
trueElem e c = e `elem` trueConditions c
falseElem e c = e `elem` falseConditions c
emptyContext = Context [] []

-- returns Nothing if t can be shown to have no effect
-- returns a recursively simplified version of t otherwise
evalTrivial :: T -> M (Maybe T)
evalTrivial Skip       = return Nothing
evalTrivial (Comment _) = return Nothing
evalTrivial (If1 c t) = evalTrivial (If c t Skip)
evalTrivial (If c t e) = do
  pathCondition <- ask
  if c `trueElem` pathCondition then evalTrivial t else
    if c `falseElem` pathCondition then evalTrivial e else do
      tt <- local (pushTrue c) $  evalTrivial t
      et <- local (pushFalse c) $  evalTrivial e
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

wrap s = "(" <> s <> ")"
e2c :: E -> Text
e2c e = case e of
  Lit i            -> showT i
  IVar i           -> i
  Ident i          -> i
  BinOp op e1 e2   -> wrap $ e2c e1 <> op <> e2c e2
  Call f es        -> e2c f <> (wrap $ intercalate "," $ map e2c es)
  RecordAccess e f -> e2c e <> "." <> f
  Deref e          -> wrap $ "*" <> e2c e
  Ternary c t e    -> wrap $ wrap (e2c c) <> "?" <> e2c t <> ":" <> e2c e
  And a b          -> wrap $ e2c a <> "&&" <> e2c b
  Or a b           -> wrap $ e2c a <> "||" <> e2c b

t2c :: T -> M ()
t2c t = do
  triv <- evalTrivial t
  case triv of
    Nothing -> ""
    Just t -> case t of
      Put l [i] r         -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
      Put l (i:_) r       -> do { emit "put"; (wrapm $ emit $ intercalate "," (map e2c [l, i, r])); ";" }
      Accum l r           -> emit $ e2c l <> " += " <> e2c r <>";"
      Next i              -> emit $ e2c i <> "++" <> ";"
      Label l             -> emit $ "\n" <> l <> ":;\n"
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

debug = False

compile :: M T -> IO ()
compile t = do
  let outName = "out4.cpp"
  T.writeFile outName . addHeaderFooter . runM $ do
    p <- t
    t2c p
  callCommand $ "clang-format -i " <> outName
  where
    addHeaderFooter (st, s) =
      "#include \"prefix.cpp\"\n"
      <> initHeader st
      <> s
      <> (if disablePrinting then "" else "printf(\"results:\\n\");" <> printingSuffix st)
      <> "#include \"suffix.cpp\"\n"

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
    printingSuffix = concat . mapMaybe (go . mapSnd toCType)
      where
        go = if disableMatrixPrinting then step' else step
        step' t@(name, CDouble) = step t
        step' _ = Nothing

        step (name, (CStorage (CStorage CDouble))) = Just $ "printMat_(" <> name <> ");\n"
        step (name, (CStorage CDouble)) = Just $ "printArray_(" <> name <> ");\n"
        step (name, CDouble) = Just $ "printf(\"" <> name <> ": %f\\n\"," <> name <> ");\n"
        step _ = Nothing

freshLabel :: String -> M String
freshLabel n = do
  (k, m) <- get
  let name = n <> showT k
  put (k+1, m)
  return $ name

fresh :: String -> TensorType -> M String
fresh n t = do
  (k, m) <- get
  let name = n <> showT k
  put (k+1, (name, t) : m)
  return $ name

cdouble = TTAtom SFloat
cint = TTAtom SInt
cstorage x = TTStorage x
csparse x = TTSparse x

------- Begin Notation -------

-- Short operators for constructing expressions
type VectorGen = GenIV E (GenIV () E)
type MatrixGen = GenIV E (GenIV E (GenIV () E))
m :: String -> M MatrixGen
m v = do
  let file = matrixFile
  var <- Ident <$> fresh v (csparse (csparse cdouble))
  let gen = fmap (fmap singleton) $ fmap externGen (externGen $ var)
  return $ gen {initialize = Store var (Call "loadmtx" [Ident $ "\"" <> file <> "\""])}
v :: String -> M VectorGen
v v = do
  let file = vectorFile
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

--infixl 6 <+>
--(<+>) :: Add a => M a -> M a -> M a
--(<+>) = liftM2 add
infixl 7 <.>
(<.>) :: Mul a => M a -> M a -> M a
(<.>) = liftM2 mul
infix 2 <--
(<--) :: Storable a b c => M a -> M b -> M c
(<--) = liftM2 store

contractionM :: M (GenV UnitGen -> UnitGen)
contractionM = do
  acc <- Ident <$> fresh "acc" cdouble
  return $ contraction acc
sum1 x = contractionM <*> x
sum2 x = liftM fmap contractionM <*> x
sum3 x = do
  c <- contractionM
  (fmap (fmap c)) <$> x
repl1 x = repeat <$> int <*> x
repl2 x = do
  i <- int
  fmap (repeat i) <$> x

run mgen = compile $ do
  gen <- mgen
  return $ initialize gen :> (loopT gen)

egVV = run $ down <$> (vvar <-- v "u" <.> v"v")
egVVV = run $ down <$> (vvar <-- v "u" <.> v"v" <.> v"w")
egMM = run $ down2 <$> (mvar <-- m "A" <.> m"B")
egMMM = run $ down2 <$> (mvar <-- m "A" <.> m"B" <.> m"C")
egVdotV = run $ float <-- sum1 (v "u" <.> v "v")

egmul1 = run $ down <$> (vvar <-- sum2 (m "A" <.> repl1 (v "x"))) -- Mv
egmul2 = run $ down2 <$> (mvar <-- sum3 (repl2 (m "A") <.> repl1 (m "B"))) -- AB^t

------- Begin Config -------

disablePathCondition = False
disablePrinting = False
disableMatrixPrinting = False
matrixFile = "smallM.mtx"
--matrixFile = "cavity11/cavity11.mtx"
vectorFile = "smallV.mtx"
--vectorFile = "cavity11/cavity_ones.mtx"
