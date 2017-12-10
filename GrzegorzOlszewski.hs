{-# LANGUAGE Safe #-}

module GrzegorzOlszewski (typecheck, eval) where
import AST
import DataTypes
type Env a = [(Var,a)]
data Val p  = VInt Integer | VBool Bool | VUnit | VPair (Val p) (Val p) | VList [Val p] | VFunc (Env (Val p)) Var (Expr p)  deriving (Eq)    
type Error p = String 
data RunErr = RunErr
makeTIntPair :: Var -> (Var,Type)
makeTIntPair x = (x, TInt)
makeTArrowPair :: FunctionDef p -> (Var, Type )
makeTArrowPair (FunctionDef p name arg typeIn typeOut body) = (name,(TArrow typeIn typeOut))

env_type_func_init :: [FunctionDef p] -> [(Var, Type)]
env_type_func_init [] = []
env_type_func_init xs = map makeTArrowPair xs

env_type_init :: [Var] -> [(Var,Type)]
env_type_init [] = []
env_type_init (x:xs) = map makeTIntPair (x:xs)

check_funcs2 :: [FunctionDef p] -> [(Var,(Type))] ->Maybe (Error p)
check_funcs2 [] _ = Nothing
check_funcs2 ((FunctionDef p name arg typeIn typeOut body):xs) func = case (infer env body, check_funcs2 xs func) of
    (Right typeOut2, Nothing ) -> if typeOut == typeOut2 then Nothing else Just "Function types not congruent"
    _ -> Just "Function types are not congruent"
    where g = if typeIn==TUnit then [] else [(arg,typeIn)]
          env = g ++ func

makeVIntPair :: (Var,Integer) -> (Var, Val p)
makeVIntPair (var, int)= (var , (VInt int))

env_val_init :: [(Var,Integer)] -> [(Var,Val p)]
env_val_init [] = []
env_val_init (x:xs) = map makeVIntPair (x:xs)

typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p
typecheck funcs vars ex =
    if check_funcs2 funcs envFunc  == Nothing then
        case res of
            Left err -> Error (getData ex) err
            Right TInt -> Ok
            otherwise -> Error (getData ex) "The program returns different type than int "
    else Error (getData ex) "Function types are not congruent"
            where
                envInt = env_type_init vars
                envFunc = env_type_func_init funcs
                env = envInt ++ envFunc
                res = infer env ex

    
eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult
eval funcs xs ex = 
    case res of
        Left RunErr ->  RuntimeError
        Right (VInt val) -> (Value val)
        where 
            funcEnv = map (\(FunctionDef p name arg _ _ body)-> (name, VFunc funcEnv arg body))funcs
            intEnv = env_val_init xs
            env = funcEnv ++ intEnv
            res = evaluate env ex

check_if_arith_bin_op_type :: BinaryOperator -> Int

check_if_arith_bin_op_type op 
    -- return 1 if op is arithmetic operator
    | elem op [BAdd, BSub, BMul, BDiv, BMod] = 1
    -- return 2 if op is an operator that compares numbers
    | elem op [BEq, BNeq, BLt, BGt, BLe, BGe] = 2
    -- return 3 if op is logic operator
    | elem op [BAnd, BOr] = 3


infer ::Env Type -> Expr p -> Either (Error p) Type

infer env (ENum _ _) = Right TInt
infer  env (EBool _ _) = Right TBool
infer  env (EUnit _) = Right TUnit
infer  env (EPair _ ex1 ex2) = 
    case (infer  env ex1, infer  env ex2) of
        (Left err, _) -> Left err
        (_ , Left err) -> Left err
        (Right typ1, Right typ2) -> Right (TPair typ1 typ2)

infer  env (EFst _ e) = 
    case infer  env e of
        Left err -> Left err
        Right (TPair t _ ) -> Right t
        Right t2 -> Left $ "Exprected a pair got" ++ show t2

infer  env (ESnd _ e) = 
    case infer  env e of
        Left err -> Left err
        Right (TPair _ t ) -> Right t
        Right t2 -> Left $ "Exprected a pair got" ++ show t2

infer  env (ENil _ type1) =
    case type1 of
         (TList _)  -> Right type1
         _ -> Left $ "Expected a list got " ++ show type1
infer  env (ECons _ ex1 ex2) = 
    case infer  env ex1 of
        Left err  -> Left err
        Right t -> case infer  env ex2 of
            Left err -> Left err
            Right (TList t2) -> if t==t2 then Right (TList t) else Left $ "Expected tail of the same type as head, got " ++ show t2
            Right t3 -> Left $ "Expected tail of the same type as head, got " ++ show t3

infer env (EApp _ e1 e2) = 
    case infer env e1 of 
        Right (TArrow t2 t1) -> case infer env e2 of
            Left err -> Left err
            Right t3 -> if t2 == t3 then Right t1 else Left "Argument is different than input type."
        Left err -> Left err

infer env (EFn _ var t1 e1) =
    case infer env2 e1 of
        Left err -> Left err
        Right t2 -> Right (TArrow t1 t2)
        where env2 = [(var,t1)]++env



infer env (EMatchL _ ex1 ex2  (var1 ,var2, ex3  )) =
    case infer  env ex1 of 
        Left err -> Left err
        Right (TList t) -> case infer  env ex2 of
            Left err -> Left err
            Right t1 -> case infer  env2 ex3 of
                Left err -> Left err
                Right t2 -> if t1 == t2 then Right t1 else Left "Alternatives should have the same type." 
                where 
                    env1 = extendEnv var1 t env 
                    env2 = extendEnv var2 (TList t) env1
        Right otherwise -> Left "It has to be a list"
        
infer  env (EUnary _ UNeg e) =
    case infer  env e of 
        Left err -> Left err
        Right TInt -> Right TInt
        otherwise -> Left "Expression should have int type, has something different."
infer  env (EUnary _ UNot e) =
    case infer  env e of 
        Left err -> Left err
        Right TBool -> Right TBool
        otherwise -> Left "Expression should have bool type, has something different."


infer  env (EBinary _ op e1 e2) =
    case check_if_arith_bin_op_type op of
        1 -> case infer  env e1 of
            Left err -> Left err
            Right TInt -> case infer  env e2 of
                Left err -> Left err
                Right TInt -> Right TInt
                otherwise-> Left "Expression should have int type, has something different."
            otherwise -> Left "Expression should have int type, has something different."
        2 -> case infer  env e1 of
            Left err -> Left err
            Right TInt  -> case infer  env e2 of
                Left err -> Left err
                Right TInt -> Right TBool
                otherwise  -> Left "Expression should have int type, has something different."
            otherwise  -> Left "Expression should have int type, has something different."
        3 -> case infer  env e1 of
            Left err -> Left err
            Right TBool -> case infer  env e2 of
                Left err -> Left err
                Right TBool -> Right TBool
                otherwise-> Left  "Expression should have bool type, has something different."
            otherwise  ->  Left  "Expression should have bool type, has something different."
infer  env (EIf _ e1 e2 e3) =
    case infer  env e1 of
        Left err -> Left err
        Right TBool -> case infer  env e2 of
            Left err -> Left err
            Right t -> case infer  env e3 of
                Left err -> Left err
                Right t2 -> if t==t2 then Right t else Left "Different types."
        otherwise -> Left  "Expression should have bool type, has something different."
infer  gamma (EVar _ x) = 
    case lookup x gamma of
        Just y -> Right y
        Nothing -> Left "This variable doesnt exist in the environment."
infer  gamma (ELet _ var e1 e2) =
    case infer  gamma e1 of
        Left err -> Left err
        Right typ1 -> case infer  gamma1 e2 of
            Left err -> Left err
            Right typ2 -> Right typ2
            where
                gamma1 = extendEnv var typ1 gamma
        

extendEnv :: Eq k => k -> v -> [(k, v)] -> [(k, v)]
extendEnv key value [] = [(key,value)]
extendEnv key value assoc = (key,value):(filter ((key /=).fst) assoc)

check_if_arith_bin_op_val :: BinaryOperator -> Integer 
check_if_arith_bin_op_val op 
    -- return 1 if op is arithmetic operator
    | elem op [BAdd, BSub, BMul] = 1
    -- return 2 if op is arithmetic operator and second argument shouldn't be 0
    | elem op [BDiv,BMod] = 2
    -- return 3 if op is an operator that compares numbers
    | elem op [BEq, BNeq, BLt, BGt, BLe, BGe] = 3
    -- return 4 if op is logic operator
    | elem op [BAnd, BOr] = 4

get_op op (x:xs) = y where
    Just y = lookup op (x:xs)

evaluate :: Env (Val p) -> Expr p -> Either RunErr (Val p)

evaluate  env (ENum _ x) =  Right (VInt x)
evaluate  env (EBool _ x) =  Right (VBool x)
evaluate  env (EUnary p UNeg x) = Right (VInt (-e))
    where Right (VInt e) = evaluate  env x
evaluate  env (EPair p ex1 ex2) = 
    case (evaluate  env ex1, evaluate  env ex2) of
        (Left RunErr, _) -> Left RunErr
        (_, Left RunErr) -> Left RunErr
        (Right x1, Right x2) -> Right (VPair x1 x2)
evaluate  env (EUnit p) = Right VUnit

evaluate  env (ENil p _) = Right (VList [])
evaluate  env (ECons p ex1 ex2) = 
    case evaluate  env ex1 of
        Left RunErr -> Left RunErr
        Right head1 -> case evaluate  env ex2 of
            Left err -> Left err
            Right (VList tail1)-> Right (VList (head1:tail1)) where

evaluate  env (EFst p ex) = case evaluate  env ex of
    Left RunErr -> Left RunErr
    Right (VPair ex1 ex2) -> Right ex1
evaluate  env (ESnd p ex) = case evaluate  env ex of
    Left RunErr -> Left RunErr
    Right (VPair ex1 ex2) -> Right ex2
evaluate  env (EUnary p UNot x) =
    case evaluate  env x of
        Right (VBool True) -> Right (VBool False)
        Right (VBool False) -> Right (VBool True)

evaluate  env (EBinary p op ex1 ex2) = 
    case (check_if_arith_bin_op_val op) of
        1 -> case (evaluate  env ex1, evaluate  env ex2) of
            (Left RunErr, _) -> Left RunErr
            (_ , Left RunErr) -> Left RunErr
            (Right (VInt x1), Right (VInt x2)) -> Right (VInt (func x1 x2)) where
                func = get_op op [(BAdd, (+)), (BSub,(-)), (BMul,(*))]
        2 -> case (evaluate  env ex1, evaluate  env ex2) of
            (Left RunErr, _) -> Left RunErr
            (_ , Left RunErr) -> Left RunErr
            (_, Right (VInt 0)) -> Left RunErr
            (Right (VInt x1), Right (VInt x2)) -> Right (VInt (func x1 x2)) where
                func = get_op op [(BDiv, div), (BMod, mod)]
        3 -> case (evaluate  env ex1, evaluate  env ex2) of
            (Left RunErr, _) -> Left RunErr
            (_ , Left RunErr) -> Left RunErr
            (Right (VInt x1), Right (VInt x2)) -> Right (VBool (func x1 x2)) where
                func = get_op op [(BEq, (==)), (BNeq, (/=)), (BLt, (<)), (BGt, (>)), (BLe, (<=)), (BGe, (>=))]
        4 -> case (evaluate  env ex1, evaluate  env ex2) of
            (Left RunErr, _) -> Left RunErr
            (_ , Left RunErr) -> Left RunErr
            (Right (VBool x1), Right (VBool x2)) -> Right (VBool (func x1 x2)) where
                func = get_op op [(BAnd, (&&)), (BOr,(||))]  
                
evaluate  env (EIf p ex1 ex2 ex3) = 
    case evaluate  env ex1 of
        Left RunErr -> Left RunErr
        Right (VBool True) -> case evaluate  env ex2 of
            Left RunErr-> Left RunErr
            Right t -> Right t 
        Right (VBool False) -> case evaluate  env ex3 of
            Left RunErr -> Left RunErr
            Right t -> Right t

evaluate  env (EVar _ x) = 
    case lookup x env of
        Just y -> Right y
        Nothing -> Left RunErr

evaluate  env (ELet _ var e1 e2) = 
    case evaluate  env e1 of
        Left RunErr -> Left RunErr
        Right t -> case evaluate  env2 e2 of
            Left RunErr -> Left RunErr
            Right expr -> Right expr
            where env2 = extendEnv var t env

evaluate  env (EMatchL _ ex1 ex2 (var1, var2, ex3) ) =
    case evaluate  env ex1 of
        Left err -> Left err
        Right (VList t) -> case t of 
            [] ->  evaluate  env ex2
            (x:xs) -> evaluate  env2 ex3 where
                env1 = extendEnv var1  x env
                env2 = extendEnv var2 (VList xs) env1 

evaluate env (EFn _ var _ ex2) = 
    Right (VFunc env var ex2)

evaluate env (EApp _ ex1 ex2) = 
    case evaluate env ex1 of
        Right (VFunc env2 var1 ex3) -> case evaluate env ex2 of
            Left err -> Left err
            Right val -> evaluate (env2++[(var1,val)]) ex3
