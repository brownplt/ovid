-- Test suite ninja'd from Dave Herman's test suite for his Javascript parser.
module Test.JavascriptParser where

import Data.Generics
import Test.HUnit
import Text.ParserCombinators.Parsec(SourcePos,parse)
import Javascript.Syntax
import Javascript.Parser
import Javascript.PrettyPrint
import Javascript.Builder
import Misc


runParseExpression s =
  case parse parseExpression "test-tokens" s of
    (Left err) -> error ("parse error: " ++ show err)
    (Right e)  -> e

runParseStatement s =
  case parse parseStatement "test-tokens" s of
    (Left err) -> error ("parse error: " ++ show err)
    (Right e)  -> e

-- Note that due to the way the (gfoldl SourcePos) is defined, all SourcePos 
-- objects are geq to each other--which is exactly what we want.
assertSymExpr msg e1 e2 = assertBool msg (geq (runParseExpression e1) e2)
assertSymStmt msg s1 s2 = assertBool msg (geq (runParseStatement s1) s2)

opAdd = InfixExpr p OpAdd
opSub = InfixExpr p OpSub
opDiv = InfixExpr p OpDiv
opMul = InfixExpr p OpMul
num = NumLit p
str = StringLit p
(+:) = InfixExpr p OpAdd


precedenceTests = TestList (map TestCase tests) where
  tests =
    [assertSymExpr "higher precedence between lower" 
       "x - y * z + w"
       (InfixExpr p OpAdd 
          (InfixExpr p OpSub (vref "x") (InfixExpr p OpMul (vref "y") (vref "z")))
          (vref "w")),
     assertSymExpr "low, high, middle" "x < y * z + w"
       (InfixExpr p OpLT
          (vref "x")
          (InfixExpr p OpAdd
             (InfixExpr p OpMul (vref "y") (vref "z"))
             (vref "w"))),
     assertSymExpr "big example" "x + y * z / 3 - 21 + a.b.c * 6"
       (InfixExpr p OpAdd 
         (opSub
            (opAdd
               (vref "x")
               (opDiv (opMul (vref "y") (vref "z")) (num 3))) 
            (num 21)) 
         (opMul (((vref "a") `vdot` "b") `vdot` "c") (num 6))),
     assertSymExpr "low followed by two high"
       "x + y * z * n"
       (opAdd (vref "x") (opMul (opMul (vref "y") (vref "z")) (vref "n"))),
     assertSymExpr "two of same precedence"
       "y * z / 3"
       (opDiv (opMul (vref "y") (vref "z")) (num 3)),
     assertSymExpr "new with arguments"
       "new C(2,3)"
       (NewExpr p (vref "C") [num 2, num 3]),
     assertSymExpr "new with arguments then called"
       "new Function('return')()"
       (CallExpr p (NewExpr p (vref "Function") [str "return"]) [])]

forTests = TestList (map TestCase tests) where
  tests =
    [assertSymStmt "empty for loop"
       "for (;;) break;"
       (ForStmt p NoInit Nothing Nothing (BreakStmt p Nothing)),
     assertSymStmt "for-in loop"
       "for (var x in e) break;"
       (ForInStmt p (ForInVar (Id p "x")) (vref "e") (BreakStmt p Nothing))]

miscTests = TestList (map TestCase tests) where
  tests =
    [assertSymExpr "empty function expression" 
       "function() { return }"
       (FuncExpr p [] (BlockStmt p [ReturnStmt p Nothing])),
      assertSymExpr "unary function expression"
        "function(x) { return }"
        (FuncExpr p [Id p "x"] (BlockStmt p [ReturnStmt p Nothing])),
      assertSymExpr "binary function expression"
         "function(x,y) { return }"
         (FuncExpr p [Id p "x",Id p "y"] (BlockStmt p [ReturnStmt p Nothing])),
      assertSymExpr "ternary function expression"
         "function(x,y,z) { return }"
         (FuncExpr p [Id p "x",Id p "y",Id p "z"] 
            (BlockStmt p [ReturnStmt p Nothing])),
      assertSymExpr "empty object expression"
         "{ }"
         (ObjectLit p []),
      assertSymExpr "unary object expression"
         "{ a: 2 }"
         (ObjectLit p [(PropId p (Id p "a"),NumLit p 2)]),
      assertSymExpr "binary object expression"
         "{ a: 2, b: 3 }"
         (ObjectLit p [(PropId p (Id p "a"),NumLit p 2),
                       (PropId p (Id p "b"),NumLit p 3)]),
      assertSymExpr "ternary object expression"
         "{ a: 2, b: 3, c: 4 }"
         (ObjectLit p [(PropId p (Id p "a"),NumLit p 2),
                       (PropId p (Id p "b"),NumLit p 3),
                       (PropId p (Id p "c"),NumLit p 4)]),
      assertSymExpr "function literal in object"
         "{ f: function() { return }, a: 3 }"
         (ObjectLit p [(PropId p (Id p "f"),
                        FuncExpr p [] (BlockStmt p [ReturnStmt p Nothing])),
                       (PropId p (Id p "a"),NumLit p 3)]),
      assertSymExpr "nested braces"
         "function() { var s = {}; return }"
         (FuncExpr p [] (BlockStmt p 
                           [VarDeclStmt p [VarDecl p (Id p "s") 
                                             (Just (ObjectLit p []))],
                            ReturnStmt p Nothing])),
      assertSymExpr "nested brackets"
         "[ [1, 2, 3], [4, 5, 6], [7, 8] ]"
         (ArrayLit p
            [ArrayLit p [num 1, num 2, num 3],
             ArrayLit p [num 4, num 5, num 6],
             ArrayLit p [num 7, num 8]]),
      assertSymExpr "brackets don't throw off tokenizer state"
         "function() { var s = []; return }"
         (FuncExpr p []
            (BlockStmt p
               [VarDeclStmt p [VarDecl p (Id p "s") (Just $ ArrayLit p [])],
                ReturnStmt p Nothing])),
      assertSymStmt "var with empty array literal"
        "var x = [];"
        (VarDeclStmt p [VarDecl p (Id p "x") (Just $ ArrayLit p [])]),
      assertSymExpr "assignment expression"
         "x = foo(3)"
         (AssignExpr p OpAssign (vref "x") (CallExpr p (vref "foo") [num 3])),
      assertSymStmt "empty switch"
        "switch(x) { }"
        (SwitchStmt p (ParenExpr p (vref "x")) []),
      assertSymStmt "case clause with multiple statements"
        "switch (x) { case 1: foo(); bar(); break; case 2: break; }"
        (SwitchStmt p (ParenExpr p (vref "x"))
           [CaseClause p (ListExpr p [num 1]) 
              [ExprStmt p $ ListExpr p [CallExpr p (vref "foo") []],
               ExprStmt p $ ListExpr p [CallExpr p (vref "bar") []],
               BreakStmt p Nothing],
            CaseClause p (ListExpr p [num 2]) 
              [BreakStmt p Nothing]]),
      assertSymStmt "do-while loop"
        "do { foo() } while (true);"
        (DoWhileStmt p (BlockStmt p [ExprStmt p $
                                       ListExpr p [CallExpr p (vref "foo") []]])
           (ParenExpr p (BoolLit p True))),
      assertSymExpr "infix operators don't include unary operators 1"
         "2 ~ 3"
         (num 2),
      assertSymExpr "infix operators don't include unary operators 2"
         "2 ! 3"
         (num 2),
      assertSymExpr "ternary ? : is an `infix-operator-token?' 1"
         "x ? y : z"
         (CondExpr p (vref "x") (vref "y") (vref "z")),
      assertSymStmt "ternary ? : is an `infix-operator-token?' 2"
        "{ s = x ? y : z }"
        (BlockStmt p [ExprStmt p
                        (ListExpr p
                           [AssignExpr p OpAssign (vref "s")
                              (CondExpr p (vref "x") (vref "y") (vref "z"))])])]


exprTests = TestList (map TestCase tests) where
  tests =
    [assertSymExpr "function call with an adjacent operator" 
       "foo(2)+3"
       ((call (vref "foo") [number 2]) +: (number 3))]

       
                              
allTests = TestList [precedenceTests,forTests,miscTests,exprTests]

runAll = do
  (counts,messages) <- runTestText putTextToShowS allTests
  putStr $ "Test results:\n" ++ (messages "")
  putStr $ "\nSummary: " ++ show counts ++ "\n"


