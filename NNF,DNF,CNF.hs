module NNF_DNF_CNF where
import System.Win32 (COORD(y))

-- Задание бинарных логических конструкторов и их приоритета.
infixl 8 :/\
infixl 7 :\/
infixl 6 :->
infixl 5 :<-> 

-- Задание типа данных "Формула".
data Form = Var String | Top | Bot | Form :/\ Form | Form :\/ Form | Form :-> Form | Form :<-> Form | Neg Form
  deriving (Show, Eq)

-- Избавление от импликации и бикондиционала.
prime :: Form -> Form
prime (Var p) =  Var p
prime Top     =  Top
prime Bot     =  Bot
prime (Neg p) = Neg (prime p)
prime (p :/\ q) = prime p :/\ prime q
prime (p :\/ q) = prime p :\/ prime q
prime (p :-> q) = Neg (prime p) :\/ prime q
prime (p :<-> q) = prime (p :-> q) :/\ prime (q :-> p)

-- Применение законов Де-Моргана и снятия двойного отрицания (тут частичный паттерн-матчинг, так как импликации и бикондиционала у нас уже не будет к моменту
-- выполнения этой функции).
nnf :: Form -> Form
nnf (Var p) =  Var p
nnf Top     =  Top
nnf Bot     =  Bot
nnf (Neg (Neg p)) = nnf p
nnf (Neg (p :/\ q)) =  nnf (Neg p) :\/ nnf (Neg q)
nnf (Neg (p :\/ q)) = nnf (Neg p) :/\ nnf (Neg q)
nnf (p :/\ q) = nnf p :/\ nnf q
nnf (p :\/ q) = nnf p :\/ nnf q
nnf (Neg p) = Neg (nnf p)

-- Приведение к н.н.ф.
toNNF :: Form -> Form
toNNF = nnf . prime

-- Приведение к д.н.ф.
toDNF :: Form -> Form
toDNF = toDNF' . toNNF  where
    toDNF' :: Form -> Form
    toDNF' (p :/\ q) = toDNF' p `dist` toDNF' q
    toDNF' (p :\/ q) = toDNF' p :\/ toDNF' q
    toDNF' x         = x
    
    dist :: Form -> Form -> Form
    dist (e11 :\/ e12) e2 = (e11 `dist` e2) :\/ (e12 `dist` e2)
    dist e1 (e21 :\/ e22) = (e1 `dist` e21) :\/ (e1 `dist` e22)
    dist e1 e2            = e1 :/\ e2

-- Приведение к к.н.ф.
toCNF :: Form -> Form
toCNF = toCNF' . toNNF
  where
    toCNF' :: Form -> Form
    toCNF' (p :/\ q) = toCNF' p :/\ toCNF' q
    toCNF' (p :\/ q) = toCNF' p `dist` toCNF' q
    toCNF' x         = x
    
    dist :: Form -> Form -> Form
    dist (e11 :/\ e12) e2 = (e11 `dist` e2) :/\ (e12 `dist` e2)
    dist e1 (e21 :/\ e22) = (e1 `dist` e21) :/\ (e1 `dist` e22)
    dist e1 e2            = e1 :\/ e2

-- Для тестов

-- идемпотентность NNF

isNNF :: Form -> Bool 
isNNF x = toNNF (toNNF x) == toNNF x

-- идемпотентность DNF

isDNF :: Form -> Bool 
isDNF x = toDNF (toDNF x) == toDNF x

-- идемпотентность CNF

isCNF :: Form -> Bool 
isCNF x = toCNF (toCNF x) == toCNF x


