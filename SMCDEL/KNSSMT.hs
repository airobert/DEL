module KNSSMT where
  --import Data.HasCacBDD hiding (Top,Bot)
  --import Data.HasCacBDD.Visuals
  import Math.SMT.Yices.Parser
  import Math.SMT.Yices.Syntax
  import Math.SMT.Yices.Pipe
  import Data.List
  import Control.Monad
  import DELLANG
  import HELP (alleq,apply,rtc)
  --import Data.List (sort,intercalate,(\\))
  --import System.IO (hPutStr, hGetContents, hClose)
  --import System.Process (runInteractiveCommand)
  --import HELP (alleq,apply,rtc)

  --import Data.List
  --import Control.Monad
  --import DELLANG

  -- you will need to change this path!
  yicesPath = "/Users/robertwhite/Projects/yices-1.0.40/bin/yices" -- your yices path



  int = VarT "int"
  nat = VarT "nat"
  bool = VarT "bool"
  real = VarT "real"

  true = LitB True
  false = LitB False

  boolSMTOf :: Form -> ExpY
  boolSMTOf Top           = true
  boolSMTOf Bot           = false
  boolSMTOf (PrpF (P n))  = VarE (show n)
  boolSMTOf (Neg forms)    = NOT (boolSMTOf forms)
  boolSMTOf (Conj forms)  = AND (map boolSMTOf forms)
  boolSMTOf (Disj forms)  = OR (map boolSMTOf forms)
  boolSMTOf (Xor [])      = false 
  boolSMTOf (Xor l)       = 
    let (b:bs) = map boolSMTOf l in 
    foldl myxor b bs
    where 
      myxor :: ExpY -> ExpY -> ExpY
      myxor s t  = (AND[OR[s, t], NOT (AND [s, t])])
 --  can we translate this as not equal ?
  boolSMTOf (Impl p1 p2)    = (boolSMTOf p1) :=> (boolSMTOf p2)
  boolSMTOf (Equi p1 p2)    = (boolSMTOf p1) :=  (boolSMTOf p2)
  boolSMTOf (Forall ps f) = 
    let ps' = map (\(P x) -> (show x, bool)) ps in 
    FORALL ps' (boolSMTOf f)
  boolSMTOf (Exists ps f) = 
    let ps' = map (\(P x) -> (show x, bool)) ps in 
    FORALL ps' (boolSMTOf f)
  boolSMTOf _             = error "boolSMTOf failed: Not a boolean formula."

-- not that the boolEval in SMCDEL is then going to be a call to Yices with assignment given
-- declaration from Prp to CmdY
  defs :: [Prp] -> [CmdY]
  defs sl = 
    map (\(P i) -> DEFINE (("p_" ++ (show i)), bool) Nothing) sl

  vars :: [Prp] -> [ExpY]
  vars sl =
    map (\(P i) -> VarE ("p_" ++ (show i))) sl


  boolEval :: [Prp] -> Form -> IO Bool 
  boolEval truths form = 
    do yp@(Just hin, Just hout, Nothing, p) <- createYicesPipe yicesPath [] 
      -- first, construct all the truth values as clauses
       let values = vars truths
       let values_declare = map ASSERT values
       -- also need to test if values are in def
       let props = propsInForm form 
       let def = defs props 
       let form_assert = [ASSERT (boolSMTOf form)]
       --yp@(Just hin, Just hout, Nothing, p) <- createYicesPipe yicesPath []
       runCmdsY yp (def ++ values_declare ++ form_assert) --
       check <- checkY yp
       print "-----def-------"
       print def 
       print "------values_declare----"
       print values_declare 
       print "-----form------"
       print form_assert
       return $
         case check of 
           Sat ss -> True
           UnSat _ -> False
           Unknown _ -> error "SMT gives an unknown as reply"
           otherwise -> error "SMT gives other replies"


  test_1 = 
    let p1 = PrpF (P 1) in 
    let p2 = PrpF (P 2) in 
    let p = Conj [p1, p2] in 
    let q = Impl p p2 in 
    q

  test_truth = do 
    result <- (boolEval [P 1, P 2] test_1)
    if result then print "yes!"
      else print "oh no!"

-- instead of BDD, we introduce a new datastructure for (propsitional variables, clauses)
type BddY = [CmdY]

data KnowStructY = KnS [Prp] BddY [(Agent,[Prp])] deriving (Eq,Show)
type KnState = [Prp]
type ScenarioY = (KnowStructY, KnState)



