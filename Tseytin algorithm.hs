module TseitinAlgorithm where

-- Задание бинарных логических конструкторов и их приоритета.
infixl 8 :/\
infixl 7 :\/
infixl 6 :->
infixl 5 :<->

-- Задание типа данных "Формула"
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


-- Поиск подформул данной формулы
subForm :: Form -> [Form]
subForm (Var z) = [Var z]
subForm Top = [Top]
subForm Bot = [Bot]
subForm (x :/\ y) = (x :/\ y) : (subForm x ++ subForm y)
subForm (x :\/  y) = (x :\/  y) : (subForm x ++ subForm y)
subForm (x :->  y) = (x :->  y) : (subForm x ++ subForm y)
subForm (x :<->  y) = (x :<->  y) : (subForm x ++ subForm y)
subForm (Neg x) = Neg x : subForm x

--- Удаляем ненужные (тривиальные) подформулы
delVarBotTop :: [Form] -> [Form]
delVarBotTop [] = []
delVarBotTop (x:xs) = case x of
  Var z -> delVarBotTop xs
  Top   -> delVarBotTop xs
  Bot   -> delVarBotTop xs
  other -> x : delVarBotTop xs

--- Заводим новые переменные и ставим соответствующие эквивалентности (правый аргумент эквивалентности выбран новой переменной, так как при раборе формулы, всё, что стоит слева в эквивалентности, будет восприниматься как цельная формула, как и должно быть).
newVar :: [Form] -> [Form]
newVar xs = helper xs 0 where
    helper :: [Form] -> Int -> [Form]
    helper [] n = []
    helper (x:xs) n = (x :<-> Var ("a" ++ show n)) : helper xs (n+1)

--- Формирование списка исходных подформул (нетривиальных) с новыми переменными, которым они эквивалентны.
str1 :: Form -> [Form]
str1 = newVar . reverse . delVarBotTop . subForm

--- Один шаг замены подформул на новую переменную (тут частичный паттер-матчинг, неразобранные случам нам не встретятся при выполнении главной функции)
subsVar :: Form -> [Form] -> [Form]
subsVar (x :<-> Var y) [] = []
subsVar (x :<-> Var y) (z:zs) = case z of 
  fo :/\ fo' :<-> Var g  -> if fo == x then (Var y :/\ fo' :<-> Var g)  : subsVar (x :<-> Var y) zs else if fo' == x then (fo :/\ Var y :<-> Var g)  : subsVar (x :<-> Var y) zs else (fo :/\ fo' :<-> Var g)  : subsVar (x :<-> Var y) zs  
  fo :\/ fo' :<-> Var g  -> if fo == x then (Var y :\/ fo' :<-> Var g)  : subsVar (x :<-> Var y) zs else if fo' == x then (fo :\/ Var y :<-> Var g)  : subsVar (x :<-> Var y) zs else (fo :\/ fo' :<-> Var g)  : subsVar (x :<-> Var y) zs
  fo :-> fo' :<-> Var g  -> if fo == x then (Var y :-> fo' :<-> Var g)  : subsVar (x :<-> Var y) zs else if fo' == x then (fo :-> Var y :<-> Var g)  : subsVar (x :<-> Var y) zs else (fo :-> fo' :<-> Var g)  : subsVar (x :<-> Var y) zs
  fo :<-> fo' :<-> Var g -> if fo == x then (Var y :<-> fo' :<-> Var g) : subsVar (x :<-> Var y) zs else if fo' == x then (fo :<-> Var y :<-> Var g) : subsVar (x :<-> Var y) zs else (fo :<-> fo' :<-> Var g) : subsVar (x :<-> Var y) zs
  Neg fo :<-> Var g      -> if fo == x then (Neg (Var y) :<-> Var g)    : subsVar (x :<-> Var y) zs else (Neg fo :<-> Var g) :subsVar (x :<-> Var y) zs

--- Все шаги постопенной замены
subsVarMult :: [Form] -> [Form]
subsVarMult [] = []
subsVarMult (x:xs) = x : subsVar x (subsVarMult xs)

--- Список подформул с новыми переменными и всеми необходимыми заменами, элементы которого осталось привести к кнф и заделать в одну большую к.н.ф.

str2 :: Form -> [Form]
str2 = subsVarMult . str1

--- Приводим все элементы списка к к.н.ф.

allToCNF :: [Form] -> [Form]
allToCNF xs = map toCNF xs

--- Вычленяем самую старшую переменную (частичный паттен-матчинг)
getLastVar :: [Form] -> Form
getLastVar x = case last x of
  _ :<-> Var x -> Var x  

--- Итоговый алгоритм, инициализирующее значение foldr тут  это старшая переменна, всё так, как и должно быть. Так как на атомах он ничего делать не должен, эти случаи выписал отдельно, иначе напоремся на случай пустого списка в функции getLastVar.

tseytin :: Form -> Form
tseytin Bot = Bot
tseytin Top = Top
tseytin (Var y) = Var y
tseytin x = foldr (:/\)  (getLastVar (str2 x))  (allToCNF (str2 x))


