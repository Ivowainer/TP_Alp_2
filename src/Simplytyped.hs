module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-----------------------
-- conversion
-----------------------

-- conversion a términos localmente sin nombres
{- Osea, dado \x:E. x y     ->     Bound 0  -}
conversion :: LamTerm -> Term
conversion t = conversor t []

conversor :: LamTerm -> [String] -> Term
conversor (LVar x) ent = 
  case elemIndex x ent of
    Nothing -> Free (Global x)
    Just i -> (Bound i)
conversor (LApp t1 t2) ent = (conversor t1 ent) :@: (conversor t2 ent)
conversor (LAbs x typ t) ent = Lam typ (conversor t (x:ent))
conversor (LLet var t1 t2) ent = 
  let
    t1' = conversor t1 ent
  in Let t1' (conversor t2 (var:ent))
{- !!!!!!!!!!!!!!!!!!!!!!!!!!!! CONSULTAR: \x:E . let x = t1 in x; en esta expresión se liga la variable  !!!!!!!!!!!!!!!!!!!!!!!!!!!! -}
conversor LZero _ = Zero
conversor (LSuc t) ent = Suc (conversor t ent)
conversor (LRec t1 t2 t3) ent = Rec (conversor t1 ent) (conversor t2 ent) (conversor t3 ent)

----------------------------
--- evaluador de términos
----------------------------

-- substituye una variable por un término en otro término
{- Cant. de abstracciones -> termino a sustituir -> termino donde se efectua la sustitución -}
sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)
sub i t (Let t1 t2)           = Let (sub i t t1) (sub (i + 1) t t2)
sub _ _ Zero                  = Zero
sub i t (Suc u)               = Suc (sub i t u)
sub i t (Rec u v w)           = Rec (sub i t u) (sub i t v) (sub i t w)

-- convierte un valor en el término equivalente
quote :: Value -> Term
quote (VLam t f) = Lam t f
quote (VNum NZero)    = Zero
quote (VNum (NSuc n)) = Suc (quote (VNum n))

-- evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value {- Type Term -}
eval nvs (Free x) = 
  case lookup x nvs of
    Just (v, _)   -> v
    Nothing       -> error "Variable libre no definida" {- CONSULTAR QUE HACER -} 
eval _ (Lam typ t) = VLam typ t
{- Evaluo el t1 -> evaluo t2 -> aplico el arg a la func. -}
eval nvs (t1 :@: t2) =
  case eval nvs t1 of
    VLam typ body -> {- \x:T.body -}
      let   v2 = eval nvs t2
            t' = sub 0 (quote v2) body {- realiza la sustitución sobre body con v2 (quote para pasar a term)  -}
      in eval nvs t'
eval nvs (Let t1 t2) =
  let
    v1 = eval nvs t1
    t' = sub 0 (quote v1) t2
  in eval nvs t'
eval _ Zero = VNum NZero
eval nvs (Suc t) =
  case eval nvs t of
    VNum n -> VNum (NSuc n)
    _      -> error "No se puede aplicar suc a algo que no es Nat"
eval nvs (Rec t1 t2 t3) =
  case eval nvs t3 of
    VNum NZero -> eval nvs t1 -- (E-RZero)
    VNum (NSuc n) ->
      let nro = quote (VNum n)  
      in eval nvs (t2 :@: Rec t1 t2 nro :@: nro) -- (t2 (R t1 t2 nro)) nro (E-RSucc)
    _ -> error "No se puede aplicar R si t3 no es Nat"
----------------------
--- type checkers
-----------------------

-- infiere el tipo de un término
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=)
  :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

-- infiere el tipo de un término a partir de un entorno local de variables y un entorno global
infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
infer' c e (Let t1 t2) = infer' c e t1 >>= \tt1 -> infer' (tt1 : c) e t2 >>= \tt2 -> ret tt2

infer' c e Zero = ret NatT

infer' c e (Suc t) = do
  tt <- infer' c e t
  if tt == NatT then ret NatT else matchError NatT tt

infer' c e (Rec t1 t2 t3) = do
  tt1 <- infer' c e t1
  tt2 <- infer' c e t2
  tt3 <- infer' c e t3
  let tt2_esperado = FunT tt1 (FunT NatT tt1)
  if tt2 == tt2_esperado
    then case tt3 of
           NatT -> ret tt1
           _    -> matchError NatT tt3
    else matchError tt2_esperado tt2
