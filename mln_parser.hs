-- Requires parsec, parsecTools and missingH
-- TODO support files with unweighted rules (and learn the weights, but start with the smoke example first)

import Text.ParserCombinators.Parsec hiding (spaces)
import Text.Parsec.Char hiding (spaces)
import Text.Parsec.Numbers
import Data.List
import Data.List.Utils
import System.Environment
import System.IO

data Predicate = Predicate String [String] deriving (Show)
data Rule = Rule Double [Predicate] deriving (Show)

-- We don't want the Super-Evil definition of spaces that includes newlines!!
spaces = many $ char ' '

identifier  = do
    c  <- (letter  <|> char '!' <|> char '*' )
    cs <- many alphaNum
    return (c:cs)

list = sepBy identifier commaSpace
    where
        commaSpace = do
            char ','
            spaces

bracketed_list = between (char '(') (char ')') list

statement = do
    predicate <- identifier
    arguments <- bracketed_list
    return $ Predicate predicate arguments

--comment = do
--    string "//"
--    many (noneOf "\n")
--    char '\n'
--    return ()

database = do
    statements <- endBy line (many newline)
    return statements
    where
        line = statement

parseDB :: String -> Either ParseError [Predicate]
parseDB input = parse database "error" input

rule = do
    weight <- parseFloat
    spaces
    statements <- disjunction
    return $ Rule weight statements

disjunction = statement `sepBy` orSymbol where
    orSymbol = do
        spaces
        char 'v'
        spaces
        return ()

prog = do
    predicates <- endBy statement (many newline)
    --string "="
    rules <- endBy rule (many newline)
    return (predicates, rules)

parseProg :: String -> Either ParseError ([Predicate], [Rule])
parseProg input = parse prog "(unknown)" input

parseRule :: String -> Either ParseError Rule
parseRule input = parse rule "(unknown)" input

-- hGetContents perversely adds a \r\n or \n to the file that linux can't see (WTF?!)
workaround_haskell_bullshit :: String -> String
workaround_haskell_bullshit input 
    | isSuffixOf "\r\n" input = init $ init input
    | isSuffixOf "\n" input = init $ input
    | otherwise = input

main :: IO ()
main = do 
    args <- getArgs
    let filename = (args !! 0)
    withFile filename ReadMode (\handle -> do
        broken_contents <- hGetContents handle
        let contents = workaround_haskell_bullshit broken_contents
        print $ prettyList $ map schemeAtom $ parseFile filename contents
        )

parseFile :: String -> String -> Either ParseError [Atom]
parseFile filename contents
    | isSuffixOf ".mln" filename =
        case parseProg $ workaround_haskell_bullshit contents of
            e@(Left _) -> e
            (Right (predicates, rules)) -> let
                    predicateAtoms = map convertPredicateDefinition predicates
                    ruleAtoms = map adaptRule rules
                in
                    Right (predicateAtoms++ruleAtoms)
    | isSuffixOf "evidence.db" filename =
        case parseDB $ workaround_haskell_bullshit contents of
            (Right statements) -> Right map convert_statement statements
            e@(Left _) -> e
    | isSuffixOf "query.db" filename =
        case parseDB $ workaround_haskell_bullshit contents of
            Right statements -> Right map convert_query statements
            e@(Left _) -> e


----------------- Output stuff to Scheme (Should be in a separate file).

data TruthValue = STV Float Float deriving (Show)
type Type = String
data Atom = Node Type String TruthValue | Link Type [Atom] TruthValue deriving (Show)

conceptTV = STV 0.01 0.01
predicateNodeTV = STV 0.01 0.01
trueTV = STV 1.0 1.0
queryTV = STV 0.0 0.0

concept :: String -> Atom
concept name = Node "ConceptNode" name conceptTV

convert_statement :: Predicate -> Atom
convert_statement statement = convertPredicate statement trueTV

convert_query :: Predicate -> Atom
convert_query query = convertPredicate query queryTV

convertPredicateDefinition definition = convertPredicate definition queryTV

convertPredicate :: Predicate -> TruthValue -> Atom
convertPredicate (Predicate relation names) tv = 
    if isPrefixOf "!" relation then
        Link "NotLink" [baseLink (tail relation) queryTV] tv
    else
        baseLink relation tv
    where
    arguments = map concept names
    baseLink predName evalTV = eval_link predName arguments evalTV

eval_link predName arguments evalTV =
    Link "EvaluationLink" [Node "PredicateNode" predName predicateNodeTV, Link "ListLink" arguments queryTV] evalTV

-- It can ignore the weight, or maybe convert it into a probability to start with
convertRule :: Rule -> Atom
convertRule (Rule weight predicates) =
    Link "OrLink" (map convert_query predicates) tv
    where
        tv = STV 0.5 0.5

--------- Better rule conversion (don't just use a disjunction/AndLink, do something more useful such as creating ImplicationLinks).
adaptRule :: Rule -> Atom
adaptRule r@(Rule weight predicates) =
    let
        (negated, true) = filterPredicates r
    in
        if length true == 1 && length negated == 0 then convert_query $ head true else
        if length true == 0 && length negated == 1 then convert_query $ head negated else -- it doesn't have to be Not A, it can just be A - and PLN will use a probability for it
        if length true == 1 && length negated == 1 then implication (convert_query $ head negated) (convert_query $ head true)
        else 
            Link "OrLink" (map convert_query predicates) tv
            where
                tv = STV 0.5 0.5

implication :: Atom -> Atom -> Atom
implication lhs rhs = Link "ImplicationLink" [lhs, rhs] queryTV

-- Filter a Rule into the negated predicates and the true predicates.
-- Remove the "!" from the name
filterPredicates :: Rule -> ([Predicate], [Predicate])
filterPredicates (Rule _ predicates) =
    (map negatePredicate $ filter (\p -> not $ truePredicate p) predicates,
     filter (truePredicate) predicates)

truePredicate :: Predicate -> Bool
truePredicate (Predicate relation _) = not $ isPrefixOf "!" relation

negatePredicate :: Predicate -> Predicate
negatePredicate p@(Predicate relation arguments)
    | truePredicate p = p
    | otherwise = (Predicate (tail relation) arguments)

-- OpenCog Scheme output
--data TruthValue = STV Float Float deriving (Show)
--type Type = String
--data Atom = Node Type String TruthValue | Link Type [Atom] TruthValue deriving (Show)

schemeTruthValue :: TruthValue -> String
schemeTruthValue (STV strength confidence) = "(stv "++show strength++" "++show confidence++")"

schemeAtom :: Atom -> String
schemeAtom (Node node_type name tv) = "("++node_type++" \""++name++"\" "++schemeTruthValue tv++")"
schemeAtom (Link link_type arguments tv) = "("++link_type++" "++str_args++" "++schemeTruthValue tv++")"
    where str_args = join " " $ map schemeAtom arguments -- join with spaces

prettyList :: [String] -> String
prettyList [] = ""
prettyList (x:xs) = x ++ "\n" ++ prettyList xs

