
import HOAS
import Term
import Eval
import Preprocess
import Lift
import Ex

import Text.Show.Pretty

main = do
  let hoas = recMulAdd' 7 5
  let stlc = fromHOAS hoas

  putStrLn "--------------------------------------------------------------------"
  let pre  = preprocess stlc
  pPrint pre

  putStrLn "--------------------------------------------------------------------"
  prog <- lambdaLift pre
  pPrint prog

  print $ evalPrg prog