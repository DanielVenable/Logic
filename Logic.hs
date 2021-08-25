module Logic.Logic (
    PropositionalConstant (..),
    Proposition (..),
    evaluate,
    isConsistent,
    isValid,
    areEquivalent,
    isTautology,
    isSelfContradiction
) where

-- | A PropositionalConstant is just a capital letter for being a literal in a Proposition.
data PropositionalConstant =
    A | B | C | D | E | F | G | H | I | J | K | L | M |
    N | O | P | Q | R | S | T | U | V | W | X | Y | Z deriving (Show, Eq)

infix  1 :=
infix  2 :>
infixl 3 :|
infixl 4 :&

-- | 'Proposition a' represents a logical proposition with literals of type a. 
data Proposition a =
    -- | The 'Literal' function turns something into a simple 'Proposition'.
    Literal a |
    -- | 'Boolean' turns a 'Bool' into a 'Proposition'.
    Boolean Bool |
    -- | 'Not' negates a 'Proposition'
    Not (Proposition a) |
    -- | ':&' is the logical conjunction operator. It is true when both propositions are true.
    (Proposition a) :& (Proposition a) |
    -- | ':|' is the logical disjunction operator. It is true when one or both propositions are true.
    (Proposition a) :| (Proposition a) |
    -- | ':>' is the logical conditional operator. It is true when the first proposition is false or the second one is true
    (Proposition a) :> (Proposition a) |
    -- | ':&' is the logical equivalence operator. It is true when both propositions have the same truth value.
    (Proposition a) := (Proposition a) deriving Eq

instance Show a => Show (Proposition a) where
    show (Literal a) = show a
    show (Boolean a) = show a
    show (Not a) = '~' : showWithParens a
    show (a :& b) = showWithParens a ++ " · " ++ showWithParens b
    show (a :| b) = showWithParens a ++ " ∨ " ++ showWithParens b
    show (a :> b) = showWithParens a ++ " ⊃ " ++ showWithParens b
    show (a := b) = showWithParens a ++ " ≡ " ++ showWithParens b

showWithParens :: Show a => Proposition a -> String
showWithParens a@(Literal _) = show a
showWithParens a@(Boolean _) = show a
showWithParens a@(Not _)     = show a
showWithParens a = "(" ++ show a ++ ")"

-- | 'evaluate' takes a 'Proposition' and a function for coverting literals into booleans and tells whether the proposition is true.
evaluate :: Proposition a -> (a -> Bool) -> Bool
evaluate (Literal a) f = f a
evaluate (Boolean a) _ = a
evaluate (Not a) f = not $ evaluate a f
evaluate (a :& b) f = evaluate a f && evaluate b f
evaluate (a :| b) f = evaluate a f || evaluate b f
evaluate (a :> b) f = not (evaluate a f) || evaluate b f
evaluate (a := b) f = evaluate a f == evaluate b f

-- | 'isConsistent' determines whether a list of propositions is consistent.
isConsistent :: Eq a => [Proposition a] -> Bool
isConsistent propositions = addPropositions propositions [] [] []

-- | 'isValid' determines whether a logical argument is valid.
isValid :: Eq a => [Proposition a] -> Proposition a -> Bool
isValid premises conclusion = not $ isConsistent $ Not conclusion : premises

-- | 'areEquivalent' determines whether two propositions are equivalent.
areEquivalent :: Eq a => Proposition a -> Proposition a -> Bool
areEquivalent p1 p2 = isTautology (p1 := p2)

-- | 'isTautology' determines whether a proposition is a tautology (always true).
isTautology :: Eq a => Proposition a -> Bool
isTautology = isValid []

-- | 'isSelfContradiction' determines whether a proposition contradicts itself.
isSelfContradiction :: Eq a => Proposition a -> Bool
isSelfContradiction = not . isConsistent . (:[])

decompose :: Eq a => [a] -> [a] -> [Proposition a] -> Bool
decompose _ _ [] = True
decompose t f (Not (Not a):p) = addPropositions [a] t f p
decompose t f ((a :& b):p) = addPropositions [a, b] t f p
decompose t f ((a :| b):p) = addPropositions [a] t f p || addPropositions [b] t f p
decompose t f ((a :> b):p) = addPropositions [Not a] t f p || addPropositions [b] t f p
decompose t f ((a := b):p) = addPropositions [a, b] t f p || addPropositions [Not a, Not b] t f p
decompose t f (Not (a :& b):p) = addPropositions [Not a] t f p || addPropositions [Not b] t f p
decompose t f (Not (a :| b):p) = addPropositions [Not a, Not b] t f p
decompose t f (Not (a :> b):p) = addPropositions [a, Not b] t f p
decompose t f (Not (a := b):p) = addPropositions [a, Not b] t f p || addPropositions [Not a, b] t f p
decompose t f (Boolean True:p) = addPropositions [] t f p
decompose t f (Boolean False:p) = False
decompose t f (Not (Boolean False):p) = addPropositions [] t f p
decompose t f (Not (Boolean True):p) = False
decompose _ _ _ = error "cannot decompose a literal or it's negation."

addPropositions :: Eq a => [Proposition a] -> [a] -> [a] -> [Proposition a] -> Bool
addPropositions [] trues falses propositions = not (contradiction trues falses) && decompose trues falses propositions
addPropositions (Literal a:props) trues falses propositions =       addPropositions props (a:trues) falses propositions
addPropositions (Not (Literal a):props) trues falses propositions = addPropositions props trues (a:falses) propositions
addPropositions (a:props) trues falses propositions =               addPropositions props trues falses (a:propositions)

contradiction :: Eq a => [a] -> [a] -> Bool
contradiction (x:xs) y = (x `elem` y) || contradiction xs y
contradiction [] _ = False