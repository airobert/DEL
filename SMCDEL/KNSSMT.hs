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


  smtEval :: KnowStructY -> KnState -> Form -> IO Bool 
  smtEval kns@(KnS allprops lawbdd obs) state form = 
    do yp@(Just hin, Just hout, Nothing, p) <- createYicesPipe yicesPath [] 
       let def = defs allprops 
       let form_assert = map (\x -> ASSERT (bddOf kns x)) lawbdd
       let state_assert = map ASSERT (vars state)
       let ex = ASSERT $ bddOf kns form
       --yp@(Just hin, Just hout, Nothing, p) <- createYicesPipe yicesPath []
       runCmdsY yp (def ++ form_assert ++ state_assert) --
       print "-----def-------"
       print def 
       print "------form_assert----"
       print form_assert 
       print "-----state_assert------"
       print state_assert
       Sat ss <- checkY yp
       runCmdsY yp [ex]
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
    anno <-(eval (kns, s) form1) 
    if anno then 
      do
        anno2 <- (eval (pubAnnounce kns form1, s) form2)
        if anno2 then 
          return True
          else return False 
      else error "Announcing something false"




