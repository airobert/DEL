-- To run, simply type test_i where 0 < i < 9.
-- See the report.pdf file for more description.
-- Rober White, ILLC, UvA

module KNSSMT where
  import Math.SMT.Yices.Parser
  import Math.SMT.Yices.Syntax
  import Math.SMT.Yices.Pipe
  import Data.List
  import Control.Monad
  import DELLANG
  import HELP (alleq,apply,rtc)

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

  ex_1 = 
    let p1 = PrpF (P 1) in 
    let p2 = PrpF (P 2) in 
    let p = Conj [p1, p2] in 
    let q = Impl p p2 in 
    q

  test_truth = do 
    result <- (boolEval [P 1, P 2] ex_1)
    if result then print "yes! Boolean formulas passed test!"
      else (print "oh no! It failed!")


  -- instead of BDD, we introduce a new datastructure for (propsitional variables, clauses)
  type BddY = [Form]

  data KnowStructY = KnS [Prp] BddY [(Agent,[Prp])] deriving (Show)
  type KnState = [Prp]
  type ScenarioY = (KnowStructY, KnState)


  smtEval :: KnowStructY -> KnState -> Form -> IO Bool 
  smtEval kns@(KnS allprops lawbdd obs) state form = 
    do yp@(Just hin, Just hout, Nothing, p) <- createYicesPipe yicesPath [] 
       let def = defs allprops 
       let theta_assert = map (\x -> ASSERT (bddOf kns x)) lawbdd
       let state_assert = map ASSERT (vars state)
       let ex = ASSERT $ bddOf kns form
       --yp@(Just hin, Just hout, Nothing, p) <- createYicesPipe yicesPath []
       runCmdsY yp (def ++ theta_assert ++ state_assert) --
       print "-----def-------"
       print def 
       print "------theta_assert----"
       print theta_assert 
       print "-----state_assert------"
       print state_assert
       Sat ss <- checkY yp
       print "-----has to be true here (the following is a model)---"
       print ss 
       runCmdsY yp [ex]
       print "----now add the ex you want to test"
       print ex
       check <- checkY yp
       return $
         case check of 
           Sat ss -> True
           UnSat _ -> False
           Unknown _ -> error "SMT gives an unknown as reply"
           otherwise -> error "SMT gives other replies"


  -- this is the main function I need to change
  bddOf :: KnowStructY -> Form -> ExpY
  bddOf _   Top           = true
  bddOf _   Bot           = false
  bddOf _   p@(PrpF (P n))  = VarE (name n)
  bddOf kns p@(Neg forms)    = NOT (bddOf kns forms)
  bddOf kns p@(Conj forms)  = AND (map (bddOf kns) forms)
  bddOf kns p@(Disj forms)  = OR (map (bddOf kns) forms)
  bddOf kns p@(Xor  [])    = false
  bddOf kns p@(Xor  forms)  =     
    let (b:bs) = map (bddOf kns) forms in 
    foldl myxor b bs
    where 
      myxor :: ExpY -> ExpY -> ExpY
      myxor s t  = (AND[OR[s, t], NOT (AND [s, t])])
  bddOf kns p@(Impl p1 p2)    = (bddOf kns p1) :=> (bddOf kns p2)
  bddOf kns p@(Equi p1 p2)    = (bddOf kns p1) :=  (bddOf kns p2)
  bddOf kns p@(Forall ps f) = 
    let ps' = map (\(P x) -> (show x, bool)) ps in 
    FORALL ps' (bddOf kns f)
  bddOf kns p@(Exists ps f) = 
    let ps' = map (\(P x) -> (show x, bool)) ps in 
    FORALL ps' (bddOf kns f)
  bddOf kns@(KnS allprops lawbdd obs) (K i form) =
    FORALL otherps $ (AND ((map (bddOf kns) lawbdd))) :=> (bddOf kns form) where
      otherps = map (\(P n) -> (name n, bool)) $ allprops \\ apply obs i
  bddOf kns (PubAnnounce form1 form2) = bddOf (pubAnnounceY kns form1) form2


  pubAnnounceY :: KnowStructY -> Form -> KnowStructY
  pubAnnounceY kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
    --newlawbdd = con lawbdd (bddOf kns psi)
    newlawbdd = psi : (lawbdd)
  
  pubAnnounceOnScn :: ScenarioY -> Form -> IO ScenarioY
  pubAnnounceOnScn (kns,s) psi = 
    do 
      print "public announcement test"
      noconflict <- eval (kns,s) psi
      if noconflict then 
        return (pubAnnounceY kns psi,s)
        else error "Liar!"

  eval :: ScenarioY -> Form -> IO Bool
  eval (kns@(KnS allprops lawbdd obs),s) Top             = return True
  eval (kns@(KnS allprops lawbdd obs),s) Bot             = return False
  eval (kns@(KnS allprops lawbdd obs),s) (PrpF p)      = return $ p `elem` s
  eval (kns@(KnS allprops lawbdd obs),s) p@(Neg form)    = smtEval kns s p
  eval (kns@(KnS allprops lawbdd obs),s) p@(Conj forms)  = smtEval kns s p
  eval (kns@(KnS allprops lawbdd obs),s) p@(Disj forms)  = smtEval kns s p
  eval (kns@(KnS allprops lawbdd obs),s) p@(Xor  forms)  = smtEval kns s p
  eval (kns@(KnS allprops lawbdd obs),s) p@(Impl f g)    = smtEval kns s p
  eval (kns@(KnS allprops lawbdd obs),s) p@(Equi f g)    = smtEval kns s p
  eval (kns@(KnS allprops lawbdd obs),s) p@(Forall ps f) = smtEval kns s p
  eval (kns@(KnS allprops lawbdd obs),s) p@(Exists ps f) = smtEval kns s p
  eval (kns@(KnS allprops lawbdd obs),s) p@(K i form)    = smtEval kns s p
  eval (kns,s) (PubAnnounce form1 form2) = do
    -- Do two evaluations 
    print "***************< form1 test >****************"
    anno <-(eval (kns, s) form1) 
    if anno then 
      do
        print "***************< form 2 test >*************"
        anno2 <- (eval (pubAnnounceY kns form1, s) form2)
        if anno2 then 
          return True
          else return False 
      else error "Announcing something false"


  -- evaluation --------------
  --type BddY = [Form]
  --data KnowStructY = KnS [Prp] BddY [(Agent,[Prp])] deriving (Show)
  --type KnState = [Prp]
  --type ScenarioY = (KnowStructY, KnState)



  mudScnInitY :: Int  -> ScenarioY
  mudScnInitY n = ( KnS mudProps [Top] [ (show i, delete (P i) mudProps) | i <- [1..n] ], [P 1 .. P n] ) where mudProps = [P 1 .. P n]

  myMud3 :: ScenarioY
  myMud3 = mudScnInitY 3

  knows :: Int -> Form
  knows i = Disj [K (show i) (PrpF $ P i), K (show i) (Neg (PrpF $ P i))]
  -- test 1, Agent 1 know true : Success
  test_1 = eval myMud3 (K "1" Top)
  -- test 2, Agent 1 knows (either true or false) : 
  -- this gives unknown as reply 
  test_2 = eval myMud3 (knows 1)

  test_3 = bddOf (fst myMud3) (knows 1)

  nobodyknows :: Int -> Form
  nobodyknows n = Conj [ Neg $ knows i | i <- [1..n] ]
  -- print nobodyknows
  no3 = nobodyknows 3

  test_5 = bddOf (fst myMud3) no3
  -- this test passed !
  test_6 = eval myMud3 no3

  
  at_least :: Int -> Form
  at_least n = Disj (map PrpF [P 1 .. P n])

  test_8 = 
    do 
      mys <- pubAnnounceOnScn myMud3 (at_least 3)
      result <- eval mys (nobodyknows 3)
      if result then print "no one knows, test passed" else print "test failed"
  

  test_9 = 
    do 
      mys <- pubAnnounceOnScn myMud3 (at_least 3)
      result <- eval mys (PubAnnounce (PrpF(P 1)) (nobodyknows 3))
      if (not result) then print "no one knows, test passed" else print "test failed"
  













