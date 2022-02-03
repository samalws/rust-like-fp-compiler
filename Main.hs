import Prelude hiding (abs)
import Compiler.Types
import Compiler.HM
import Compiler.ANF

main = do
  let a = abs' $ abs' $ app (app (primVal "+") (evar 1)) (evar 1)
  let b = let' (abs' $ evar 0) $ app (app (evar 0) (evar 0)) (primInt 0)
  let c = app (primVal "+") (primInt 0)
  let p = putStrLn
  let f = p . show . annotateExpr
  let g = p . show . fmap exprVal . annotateExpr
  let r = runAnf
  g $ a
  g $ b
  f $ b
  g $ abs (Just intType) (evar 0)
  f $ abs (Just intType) $ app (evar 0) (primInt 0)
  g $ abs' $ app (evar 0) (primInt 0)
  p $ "sneed"
  g $ c
  p $ show $ r c
  f $ r c
  g $ r c
  g $ r $ r c
  p $ "chuck"
  p $ show a
  p $ show $ r a
  p $ show $ r $ r a
  g $ a
  g $ r a
  g $ r $ r a
  g $ r $ r $ r $ r a
  print $ (r $ r $ r $ r $ r $ r $ r a) == r a
