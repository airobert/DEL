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
  boolSMTOf p@(PrpF (P n))  = VarE (name n)
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

  name :: Int -> String
  name x = "p_" ++ (show x)

  defs :: [Prp] -> [CmdY]
  defs sl = 
    map (\(P i) -> DEFINE ((name i), bool) Nothing) sl

  vars :: [Prp] -> [ExpY]
  vars sl =
    map (\(P i) -> VarE (name i)) sl


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
      else (print "oh no!")

  -- instead of BDD, we introduce a new datastructure for (propsitional variables, clauses)
  type BddY = [Form]

  data KnowStructY = KnS [Prp] BddY [(Agent,[Prp])] deriving (Show)
  type KnState = [Prp]
  type ScenarioY = (KnowStructY, KnState)



  -- this is the main function I need to change
  bddOf :: KnowStructY -> Form -> ExpY
  bddOf _   Top           = true
  bddOf _   Bot           = false
  bddOf _   p@(PrpF (P n))  = boolSMTOf p
  bddOf kns p@(Neg form)    = boolSMTOf p
  bddOf kns p@(Conj forms)  = boolSMTOf p
  bddOf kns p@(Disj forms)  = boolSMTOf p
  bddOf kns p@(Xor  forms)  = boolSMTOf p
  bddOf kns p@(Impl f g)    = boolSMTOf p
  bddOf kns p@(Equi f g)    = boolSMTOf p
  bddOf kns p@(Forall ps f) = boolSMTOf p
  bddOf kns p@(Exists ps f) = boolSMTOf p
  bddOf kns@(KnS allprops lawbdd obs) (K i form) =
    FORALL otherps (bddOf kns form) where
      otherps = map (\(P n) -> (name n, bool)) $ allprops \\ apply obs i
  bddOf kns (PubAnnounce form1 form2) = bddOf (pubAnnounce kns form1) form2


  pubAnnounce :: KnowStructY -> Form -> KnowStructY
  pubAnnounce kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
    --newlawbdd = con lawbdd (bddOf kns psi)
    newlawbdd = psi : (lawbdd)


  -- | Restrict a given variable to a given value
  restrict :: BddY -> (Int,Bool) -> BddY
  restrict b (n,bit) = 
    if bit then (VarE (name n)) : b
      else (NOT (VarE (name n))) : b

  -- intersection
  restrictState :: KnState -> [Prp] -> KnState
  restrictState s props = filter (`elem` props) s


  eval :: ScenarioY -> Form -> Bool
  eval _       Top           = True
  eval _       Bot           = False
  eval (_,s)   (PrpF p)      = p `elem` s
  eval (kns,s) (Neg form)    = not $ eval (kns,s) form
  eval (kns,s) (Conj forms)  = all (eval (kns,s)) forms
  eval (kns,s) (Disj forms)  = any (eval (kns,s)) forms
  eval (kns,s) (Xor  forms)  = odd $ length (filter id $ map (eval (kns,s)) forms)
  eval scn     (Impl f g)    = not (eval scn f) || eval scn g
  eval scn     (Equi f g)    = eval scn f == eval scn g
  eval scn     (Forall ps f) = eval scn (foldl singleForall f ps) where
    singleForall g p = Conj [ substit p Top g, substit p Bot g ]
  eval scn     (Exists ps f) = eval scn (foldl singleExists f ps) where
    singleExists g p = Disj [ substit p Top g, substit p Bot g ]
  eval (kns@(KnS _ _ obs),s) (K i form) = all (\s' -> eval (kns,s') form) theres where
    theres = filter (\s' ->  ((restrictState s' oi) := (restrictState s oi))) (statesOf kns)
    oi = apply obs i
  eval (kns,s) (PubAnnounce form1 form2) =
    -- I didn't change this part
    not (eval (kns, s) form1) || eval (pubAnnounce kns form1, s) form2



