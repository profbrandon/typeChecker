
module Parser
  ( Parser.parse
  )
where

import Data.Char (isLower, isUpper)
import Text.Parsec (between, try, many, many1, manyTill, eof, choice, sepBy, sepBy1, parse, parserFail, unexpected, (<|>))
import Text.Parsec.Prim (getPosition)
import Text.Parsec.Pos (SourcePos)
import Text.Parsec.Char (char, alphaNum, letter, space, string, digit)
import Text.Parsec.String (Parser)

import Language.Patterns (Pat(..))
import Language.AbstractSyntax (Term(..), VContext(..), addPatterns, pushBinding)
import TypeChecker.Types (Type(..), TExpr(..))
import TypeChecker.Utils (nilmap)
import TypeChecker.UniversalQuantifiers.Utils (quantify')

parse = Text.Parsec.parse (expr nilmap) ""

expr :: VContext -> Parser Term
expr vctx = do t <- term vctx; app t vctx

term :: VContext -> Parser Term
term vctx = do
  white
  t0 <- (try true)
    <|> (try false)
    <|> (try num)
    <|> (try eunit)
    <|> (try $ pair vctx)
    <|> (try $ do char '('; white; t <- expr vctx; char ')'; white; return t)
    <|> (try $ record vctx)
    <|> (try $ fix vctx)
    <|> (try $ first vctx)
    <|> (try $ second vctx)
    <|> (try $ iszero vctx)
    <|> (try $ suc vctx)
    <|> (try $ prd vctx)
    <|> (try $ eleft vctx)
    <|> (try $ eright vctx)
    <|> (try $ lambda vctx)
    <|> (try $ letin vctx)
    <|> (try $ ccase vctx)
    <|> (try $ cond vctx)
    <|> (try $ var vctx)
  proj t0 vctx

ccase :: VContext -> Parser Term
ccase vctx = do
  pos <- getPosition
  string "case"; white
  e <- expr vctx; string "of"; white
  bs <- sepBy1 (branch vctx) (do char ';'; white)
  return $ Case e bs pos

branch :: VContext -> Parser (Pat, Term)
branch vctx = do
  p <- pat; white
  string "->"; white
  let vctx' = addPatterns vctx p
  e <- expr vctx'
  return (p, e)

eleft :: VContext -> Parser Term
eleft vctx = do
  pos <- getPosition
  string "Left"; white
  e <- expr vctx
  char ':'; white
  t <- typ; white
  return $ ELeft e t pos

eright :: VContext -> Parser Term
eright vctx = do
  pos <- getPosition
  string "Right"; white
  e <- expr vctx
  char ':'; white
  t <- typ; white
  return $ ERight e t pos

proj :: Term -> VContext -> Parser Term
proj t vctx = do
  pos <- getPosition
  choice [ do char '.'; white; s <- identifier; white; return $ Proj t s pos
         , do white; return t]

app :: Term -> VContext -> Parser Term
app t1 vctx = do
  pos <- getPosition
  choice [ do t2 <- term vctx; app (App t1 t2 pos) vctx
         , do white'; return t1 ]

lambda :: VContext -> Parser Term
lambda vctx = do
  pos <- getPosition
  char '\\';       white
  s <- identifier; white
  char ':';        white
  ty <- typ;
  let vctx' = pushBinding vctx (s, ty)
  char '.';        white
  t <- expr vctx'
  return $ Abs s ty t pos

letin :: VContext -> Parser Term
letin vctx = do
  pos <- getPosition
  string "let";    white
  p <- pat; white
  let vctx' = addPatterns vctx p
  char '=';        white
  t1 <- expr vctx
  string "in";     white
  t2 <- expr vctx'
  return $ Let p t1 t2 pos

cond :: VContext -> Parser Term
cond vctx = do
  pos <- getPosition
  string "if"; white
  t1 <- expr vctx
  string "then"; white
  t2 <- expr vctx
  string "else"; white
  t3 <- expr vctx
  return $ If t1 t2 t3 pos

pair :: VContext -> Parser Term
pair vctx = do
  pos <- getPosition
  char '('; white
  t1 <- expr vctx;
  char ','; white
  t2 <- expr vctx;
  char ')';
  return $ Pair t1 t2 pos

record :: VContext -> Parser Term
record vctx = do
  pos <- getPosition
  char '{'; white
  fs <- sepBy (field vctx) (do char ','; white)
  char '}'
  return $ Record fs pos

field :: VContext -> Parser (String, Term)
field vctx = do
  n <- identifier; white
  char '='; white
  t <- expr vctx;
  return (n, t)

fix :: VContext -> Parser Term
fix = funct "fix" Fix

first :: VContext -> Parser Term
first = funct "fst" Fst

second :: VContext -> Parser Term
second = funct "snd" Snd

iszero :: VContext -> Parser Term
iszero = funct "iszero" IsZero

suc :: VContext -> Parser Term
suc = funct "succ" Succ

prd :: VContext -> Parser Term
prd = funct "pred" Pred

var :: VContext -> Parser Term
var vctx = do
  pos <- getPosition
  n <- identifier; white
  case findBind vctx n of
    Nothing      -> parserFail $ "unbound variable \'" ++ n ++ "\'"
    Just (i,_,_) -> return $ Var i pos

true :: Parser Term
true = do
  pos <- getPosition
  string "True" 
  return $ Tru pos

false :: Parser Term
false = do
  pos <- getPosition
  string "False"
  return $ Fls pos

eunit :: Parser Term
eunit = do 
  pos <- getPosition
  char '('; white; char ')'
  return $ EUnit pos

num :: Parser Term 
num = do
  pos <- getPosition
  s <- many1 digit
  return $ num0 pos (read s :: Int)

num0 :: SourcePos -> Int -> Term
num0 pos 0 = Zero pos
num0 pos n = Succ t pos where t = num0 pos (n - 1)



-- Parsers for Types

typ :: Parser Type
typ = (do  t <- texpr; return $ quantify' t)
  <|> uq 
  <|> (try $ between (char '(') (char ')') typ)

uq :: Parser Type
uq = do
  string "forall"; white
  n <- identifier; white
  char '.'; white
  ty <- typ; white
  return $ Forall n ty

texpr :: Parser Type
texpr = do
  te <- (try bool) 
    <|> (try nat)
    <|> (try unit)
    <|> (try tpair)
    <|> (try tsum)
    <|> (try $ do char '('; white; Type t <- texpr; char ')'; white; return t)
    <|> (try trec)
    <|> (try tvar)
    <|> (try tname)
  te' <- arrow te
  return $ Type te'

arrow :: TExpr -> Parser TExpr
arrow t1 = do
  choice [ do string "->"; white; Type t2 <- texpr; return $ Arrow t1 t2
         , return t1]

tsum :: Parser TExpr
tsum = do
  char '('; white
  Type t1 <- texpr
  char '|'; white
  Type t2 <- texpr
  char ')'; white
  return $ Sum t1 t2

tvar :: Parser TExpr
tvar = do 
  n <- identifier; white
  if and $ map (isLower) n 
    then return $ TVar n
    else unexpected "type variables must be all lowercase"

tname :: Parser TExpr
tname = do
  n <- identifier; white
  if isUpper (head n)
    then return $ TName n
    else unexpected "type name must start with uppercase letter"

bool :: Parser TExpr
bool = do
  string "Bool"; white
  return Bool

nat :: Parser TExpr
nat = do
  string "Nat"; white
  return Nat

unit :: Parser TExpr
unit = do
  char '('; white; char ')'; white
  return Unit

tpair :: Parser TExpr
tpair = do
  char '('; white
  Type t1 <- texpr
  char ','; white
  Type t2 <- texpr
  char ')'; white
  return $ TPair t1 t2

trec :: Parser TExpr
trec = do
  char '{'; white
  fs <- sepBy tfield (do char ','; white)
  char '}'; white
  return $ TRec fs

tfield :: Parser (String, Type)
tfield = do
  n <- identifier; white
  char ':'; white
  ty <- typ;
  return (n, ty)



-- Parsers for Patterns

pat :: Parser Pat
pat = (try punit)
  <|> (try $ do char '('; white; p <- pat; char ')'; white; return p)
  <|> (try pnum)
  <|> (try pwild)
  <|> (try ptru)
  <|> (try pfls)
  <|> (try pleft)
  <|> (try pright)
  <|> (try pvar) 
  <|> (try ppair)
  <|> (try prec)

pleft :: Parser Pat
pleft = do
  string "Left"; white
  p <- pat;
  return $ PLeft p

pright :: Parser Pat
pright = do
  string "Right"; white
  p <- pat;
  return $ PRight p

pnum :: Parser Pat
pnum = do
  s <- many1 digit; white
  return $ pnum0 (read s :: Int)

pnum0 :: Int -> Pat
pnum0 0 = PZero
pnum0 n = PSucc p where p = pnum0 (n - 1) 

punit :: Parser Pat
punit = do
  char '('; white; char ')'; white
  return PUnit

pwild :: Parser Pat
pwild = do
  char '_'; white
  return PWild

ptru :: Parser Pat
ptru = do
  string "True"; white
  return PTru

pfls :: Parser Pat
pfls = do
  string "False"; white
  return PFls

pvar :: Parser Pat
pvar = do
  s <- identifier; white
  return $ PVar s

ppair :: Parser Pat
ppair = do
  char '(';  white
  p1 <- pat; white
  char ',';  white
  p2 <- pat; white
  char ')';  white
  return $ PPair p1 p2

prec :: Parser Pat
prec = do
  char '{'; white
  ps <- sepBy pfield (do char ','; white)
  char '}'; white
  return $ PRec ps

pfield :: Parser (String, Pat)
pfield = do
  n <- identifier; white
  char '=';        white
  p <- pat;        white
  return (n, p)



-- Auxiliary Functions

funct :: String -> (Term -> SourcePos -> Term) -> VContext -> Parser Term
funct s f vctx = do
  pos <- getPosition
  string s; white
  t <- expr vctx
  return $ f t pos

white :: Parser String
white = many space

white' :: Parser String
white' = white <|> manyTill space eof

identifier :: Parser String
identifier = do
  a <- letter
  s <- many alphaNum
  return $ a:s

-- Finds a binding in the present context
findBind :: VContext -> String -> Maybe (Int, String, Type)
findBind = findBind0 0

findBind0 :: Int -> VContext -> String -> Maybe (Int, String, Type)
findBind0 i ctx name =
  case ma of
    Nothing     -> Nothing
    Just (s, t) ->
      if s == name
        then Just (i, s, t)
        else findBind0 (i + 1) ctx name
  where ma = ctx i 
