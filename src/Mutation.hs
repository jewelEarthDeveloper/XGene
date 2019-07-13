{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Rank2Types #-}
{-#  LANGUAGE TypeSynonymInstances #-}
{-#  LANGUAGE FlexibleInstances #-}

module Mutation (mutateCodeFile, writeMutants) where

import Language.Haskell.Exts (Annotated(..), Annotation(Ann), Decl(FunBind, PatBind, AnnPragma),
    Exp(App, Var, If, Lit), fromParseResult, GuardedRhs(GuardedRhs),
    Literal(Int, Char, Frac, String, PrimInt, PrimChar, PrimFloat, PrimDouble, PrimWord, PrimString),
    Match(Match), Module(Module), Name(Symbol, Ident), QName(UnQual), QOp(..),
    Pat(PVar), parseModule, Pretty(), prettyPrint, SrcSpan(..), srcSpanStart, srcSpanEnd,
    SrcSpanInfo(..), Stmt(Qualifier))
import Data.List (nub,(\\),permutations, subsequences, partition)
import Control.Monad (MonadPlus, mplus, mzero)
import Data.Generics (Typeable, Data, GenericM, mkMp, gmapMo,listify)
import Data.Maybe(isJust)
import System.FilePath (takeBaseName, combine )

data Mutant = Mutant { _mutant::String } deriving (Eq, Show)

data MuVar = MutatePatternMatch
    | MutateValues
    | MutateFunctions
    | MutateNegateIfElse
    | MutateNegateGuards
    | MutateOther String
    deriving (Eq, Show)

data Span = P !Int !Int !Int !Int deriving (Eq, Ord)

instance Show Span where
    show (P l1 c1 l2 c2) = show l1 ++ ':' : show c1 ++ '-' : show l2 ++ ':' : show c2

data MuOp = N  (Name_, Name_)
    | QN (QName_, QName_)
    | QO (QOp_, QOp_)
    | E  (Exp_, Exp_)
    | D  (Decl_, Decl_)
    | L  (Literal_, Literal_)
    | G  (GuardedRhs_, GuardedRhs_)
    deriving Eq

data Config = Config { muOp :: [FnOp] }  deriving Show

data FnOp = FnOp {_type :: FnType, _fns :: [String]} deriving (Eq, Show)

data FnType = FnSymbol | FnIdent deriving (Eq, Show)

class Mutable a where
  (==>) :: a -> a -> MuOp

type Name_ = Name SrcSpanInfo
instance Mutable Name_ where
  (==>) = (N .) . (,)

type QName_ = QName SrcSpanInfo
instance Mutable QName_ where
  (==>) = (QN .) . (,)

type QOp_ = QOp SrcSpanInfo
instance Mutable QOp_ where
  (==>) = (QO .) . (,)

type Exp_ = Exp SrcSpanInfo
instance Mutable Exp_ where
  (==>) = (E .) . (,)

type Decl_ = Decl SrcSpanInfo
instance Mutable Decl_ where
  (==>) = (D .) . (,)

type Literal_ = Literal SrcSpanInfo
instance Mutable Literal_ where
  (==>) = (L .) . (,)

type GuardedRhs_ = GuardedRhs SrcSpanInfo
instance Mutable GuardedRhs_ where
  (==>) = (G .) . (,)

type Module_ = Module SrcSpanInfo
type Annotation_ = Annotation SrcSpanInfo

--writeMutants::FilePath -> FilePath -> Int -> IO ()
writeMutants src dest max = do
    mutants <- take max <$> mutateCodeFile src
    let 
        outPathPre = repeat $ combine dest $ takeBaseName src
        outPathPost = map (flip (++) ".hs" . show) [1..max]
        outPaths = zipWith (++) outPathPre outPathPost
    sequence $ zipWith writeFile outPaths (map _mutant mutants)
    return ()

mutateCodeFile :: FilePath -> IO [Mutant]
mutateCodeFile filename = do
    f <- readFile filename
    let 
        mutants :: [Mutant]
        mutants = genMutantsForSrc defaultConfig f
    return mutants

defaultConfig :: Config
defaultConfig = Config {
    muOp = [
        FnOp {_type=FnIdent, _fns= ["pred", "id", "succ"]},
        FnOp {_type=FnIdent, _fns=  ["sum", "product", "maximum", "minimum", "head", "last"]},
        FnOp {_type=FnIdent, _fns=  ["quot", "rem", "div", "mod"]},
        FnOp {_type=FnSymbol, _fns= ["<", ">", "<=", ">=", "/=", "=="]},
        FnOp {_type=FnSymbol, _fns= ["&&", "||"]},
        FnOp {_type=FnSymbol, _fns= ["+", "-", "*", "/", "^","**","^^"]}] }

genMutantsForSrc :: Config -> String -> [Mutant] 
genMutantsForSrc config src = map (toMutant . apTh (prettyPrint . withAnn)) $ programMutants config ast
    where 
        origAst = getASTFromStr src
        (onlyAnn, noAnn) = splitAnnotations origAst
        ast = putDecl origAst noAnn
        withAnn mast = putDecl mast $ getDecl mast ++ onlyAnn
        apTh  f (a,b,c) = (a, b, f c)
        toMutant (m,s,str) = Mutant {_mutant = str }
        programMutants config ast = nub $ mutatesN (applicableOps config ast) ast
        getASTFromStr fname = fromParseResult $ parseModule fname
        
splitAnnotations :: Module_ -> ([Decl_], [Decl_])
splitAnnotations ast = partition fn $ getDecl ast
    where 
        fn x = (functionName x ++ pragmaName x) `elem` getAnnotatedTests ast

mutatesN :: [(MuVar,MuOp)] -> Module_ -> [(MuVar, Span, Module_)] 
mutatesN os ast =  concat [mutate op (MutateOther [], toSpan (0,0,0,0), ast)  | op <- os ]
    where
        toSpan (l1,c1,l2,c2) = P l1 c1 l2 c2
        mutate (v, op) (_v, _s, m) = map (v,toSpan $ getSpan op, ) $ once (mkMpMuOp op) m \\ [m]

getSpan :: MuOp -> (Int, Int, Int, Int)
getSpan m = (startLine, startCol, endLine, endCol)
    where 
        (endLine, endCol) = srcSpanEnd lspan
        (startLine, startCol) = srcSpanStart lspan
        getSpan' (N  (a,_)) = ann a
        getSpan' (QN (a,_)) = ann a
        getSpan' (QO (a,_)) = ann a
        getSpan' (E  (a,_)) = ann a
        getSpan' (D  (a,_)) = ann a
        getSpan' (L  (a,_)) = ann a
        getSpan' (G  (a,_)) = ann a
        lspan = srcInfoSpan $ getSpan' m

once :: MonadPlus m => GenericM m -> GenericM m
once f x = f x `mplus` gmapMo (once f) x
        
mkMpMuOp :: (MonadPlus m, Typeable a) => MuOp -> a -> m a
mkMpMuOp = apply $ mkMp . uncurry (~~>)

(~~>) :: (MonadPlus m, Eq a) => a -> a -> a -> m a
x ~~> y = \z -> if z == x then return y else mzero

applicableOps :: Config -> Module_ -> [(MuVar,MuOp)] 
applicableOps config ast = relevantOps ast opsList
    where 
        opsList = concatMap spread [
            (MutatePatternMatch, selectFnMatches ast),
            (MutateValues, selectLiteralOps ast),
            (MutateFunctions, selectFunctionOps (muOp config) ast),
            (MutateNegateIfElse, selectIfElseBoolNegOps ast),
            (MutateNegateGuards, selectGuardedBoolNegOps ast)]

relevantOps :: (Data a, Eq a) => a -> [(MuVar, MuOp)] -> [(MuVar, MuOp)]
relevantOps m oplst = filter (relevantOp m) $ filter (not . same . snd) oplst
    where
         relevantOp m' (_v, op) = isJust $ once (mkMpMuOp op) m'
         same = apply $ uncurry (==)

selectFnMatches :: Module_ -> [MuOp]
selectFnMatches m = selectValOps isFunct convert m
    where 
        isFunct :: Decl_ -> Bool
        isFunct FunBind{} = True
        isFunct _    = False
        convert (FunBind l ms) = map (FunBind l) $ filter (/= ms) (permutations ms ++ removeOneElem ms)
        convert _ = []
        removeOneElem [_] = []
        removeOneElem l = choose l (length l - 1)
        choose xs n = filter (\x -> length x == n) $ subsequences xs
        
selectValOps :: (Typeable b, Mutable b) => (b -> Bool) -> (b -> [b]) -> Module_ -> [MuOp]
selectValOps predicate f m = concat [ map (x ==>) (f x) |  x <-  listify predicate m ]

selectLiteralOps :: Module_ -> [MuOp]
selectLiteralOps m = selectLitOps m ++ selectBLitOps m

selectLitOps :: Module_ -> [MuOp]
selectLitOps m = selectValOps isLit convert m
    where 
        isLit :: Literal_ -> Bool
        isLit _ = True
        convert (Int l i _) = map (apX (Int l)) $ nub [i + 1, i - 1, 0, 1, (-1) ]
        convert (PrimInt l i _) = map (apX (PrimInt l)) $ nub [i + 1, i - 1, 0, 1, (-1)]
        convert (Char l c _) = map (apX (Char l)) [pred c, succ c]
        convert (PrimChar l c _) = map (apX (Char l)) [pred c, succ c]
        convert (Frac l f _) = map (apX (Frac l)) $ nub [f + 1.0, f - 1.0, 0.0, 1.1, (-1.0)]
        convert (PrimFloat l f _) = map (apX (PrimFloat l)) $ nub [f + 1.0, f - 1.0, 0.0, 1.0,(-1.0)]
        convert (PrimDouble l f _) = map (apX (PrimDouble l)) $ nub [f + 1.0, f - 1.0, 0.0, 1.0, (-1.0)]
        convert (String l _ _) = map (apX (String l)) $ nub ["", "Paul is a god", "\n", "\601"]
        convert (PrimString l _ _) = map (apX (PrimString l)) $ nub ["", "Paul is a god", "\n", "\601"]
        convert (PrimWord l i _) = map (apX (PrimWord l)) $ nub [i + 1, i - 1, 0, 1,(-1)]
        apX :: (t1 -> [a] -> t) -> t1 -> t
        apX fn i = fn i []

selectBLitOps :: Module_ -> [MuOp]
selectBLitOps m = selectValOps isLit convert m
    where
        isLit :: Name_ -> Bool
        isLit (Ident _l "True") = True
        isLit (Ident _l "False") = True
        isLit _ = False
        convert (Ident l "True") = [Ident l "False"]
        convert (Ident l "False") = [Ident l "True"]
        convert _ = []

selectFunctionOps :: [FnOp] -> Module_ -> [MuOp]
selectFunctionOps fo f = concatMap (selectIdentFnOps f) idents ++ concatMap (selectSymbolFnOps f) syms
    where 
        idents = map _fns $ filter (\a -> _type a == FnIdent) fo
        syms = map _fns $ filter (\a -> _type a == FnSymbol) fo

selectSymbolFnOps :: Module_ -> [String] -> [MuOp]
selectSymbolFnOps m s = selectValOps isBin convert m
    where 
        isBin :: Name_ -> Bool
        isBin (Symbol _l n) | n `elem` s = True
        isBin _ = False
        convert (Symbol l n) = map (Symbol l) $ filter (/= n) s
        convert _ = []

selectIdentFnOps :: Module_ -> [String] ->  [MuOp]
selectIdentFnOps m s = selectValOps isCommonFn convert m
    where 
        isCommonFn :: Exp_ -> Bool
        isCommonFn (Var _lv (UnQual _lu (Ident _l n))) | n `elem` s = True
        isCommonFn _ = False
        convert (Var lv_ (UnQual lu_ (Ident li_ n))) = map  (Var lv_ . UnQual lu_ . Ident li_) $ filter (/= n) s
        convert _ = []

selectIfElseBoolNegOps :: Module_ -> [MuOp]
selectIfElseBoolNegOps m = selectValOps isIf convert m
    where 
        isIf :: Exp_ -> Bool
        isIf If{} = True
        isIf _    = False
        convert (If l e1 e2 e3) = [If l e1 e3 e2]
        convert _ = []

selectGuardedBoolNegOps :: Module_ -> [MuOp]
selectGuardedBoolNegOps m = selectValOps isGuardedRhs convert m
    where 
        isGuardedRhs :: GuardedRhs_ -> Bool
        isGuardedRhs GuardedRhs{} = True
        convert (GuardedRhs l stmts expr) = [GuardedRhs l s expr | s <- once (mkMp boolNegate) stmts]
        boolNegate _e@(Qualifier _l (Var _lv (UnQual _lu (Ident _li "otherwise")))) = [] 
        boolNegate (Qualifier l expr) = [Qualifier l (App l_ (Var l_ (UnQual l_ (Ident l_ "not"))) expr)]
        boolNegate _x = [] 

l_ :: SrcSpanInfo
l_ = SrcSpanInfo (SrcSpan "" 0 0 0 0) []

functionName :: Decl_ -> String
functionName (FunBind _l (Match _ (Ident _li n) _ _ _ : _)) = n
functionName (FunBind _l (Match _ (Symbol _ls n) _ _ _ : _)) = n
functionName (PatBind _ (PVar _lpv (Ident _li n)) _ _)          = n
functionName _                                   = []

pragmaName :: Decl_ -> String
pragmaName (AnnPragma _ (Ann _l (Ident _li n) (Lit _ll (String _ls _t _)))) = n
pragmaName _                                                                                          = []

putDecl :: Module_ -> [Decl_] -> Module_
putDecl (Module a b c d _) decls = Module a b c d decls
putDecl m _                                  = m

getDecl :: Module_ -> [Decl_]
getDecl (Module _ _ _ _ decls) = decls
getDecl _ = []

apply :: (forall a. (Eq a, Typeable a, Show a, Pretty a) => (a,a) -> c) -> MuOp -> c
apply f (N  m) = f m
apply f (QN m) = f m
apply f (QO m) = f m
apply f (E  m) = f m
apply f (D  m) = f m
apply f (L  m) = f m
apply f (G  m) = f m

spread :: (a, [b]) -> [(a, b)]
spread (a,lst) = map (a,) lst

getAnnotatedTests :: Module_ -> [String]
getAnnotatedTests ast = concatMap (getAnn ast) ["Test","TestSupport"]

getAnn :: Module_ -> String -> [String]
getAnn m s =  [conv name | Ann _l name _exp <- listify isAnn m]
    where 
        isAnn :: Annotation_ -> Bool
        isAnn (Ann _l (Symbol _lsy _name) (Lit _ll (String _ls e _))) = e == s
        isAnn (Ann _l (Ident _lid _name) (Lit _ll (String _ls e _))) = e == s
        isAnn _ = False
        conv (Symbol _l n) = n
        conv (Ident _l n) = n