{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module RawSyntax where

import Language.LBNF

bnfc [$lbnf|


comment "--" ;
comment "{-" "-}" ;

token Colon (':')+ ;
token Commas ','+ ;
token Cross ';'+ ;

token Natural digit+;
-- token Index (('0'|'1')+);
token Permutation '#' digit+;
token Arrow {"->"}|{"=>"};

position token Identifier ('!'|'['|']'|letter|'_'|'\'')(('*'|'['|']'|letter|digit|'-'|'_'|'\'')*) ;
position token Hole '?' ((letter|digit|'-'|'_'|'\'')*) ;

position token Sort ('#' | '*' (digit*)) ('|' (digit+))?;


EMulti.  Exp6 ::= "{" [Exp] "}" ;
EHole.   Exp6 ::= Hole ;
EVar.    Exp6 ::= AIdent ;
EVarI.   Exp6 ::= AIdent Natural;
ESet.    Exp6 ::= Sort ;
EParam.  Exp4 ::= Exp4 "!";
ESwap.   Exp4 ::= Exp4 Permutation;
EUp.     Exp4 ::= Exp4 "^";
-- EDestr.  Exp4 ::= Exp4 "%" Natural ;
EProj.   Exp4 ::= Exp4 "." AIdent ;
EExtr.   Exp4 ::= Exp4 "/" AIdent ;
EApp.    Exp3 ::= Exp3 Exp4 ;
EAppP.   Exp3 ::= Exp3 "@" Exp4 ;
EPi.     Exp2  ::= Exp3 Arrow Exp2 ;
ESigma.  Exp2  ::= Exp3 ";;" Exp2 ;
EAbs.    Exp2  ::= "\\" [Bind] Arrow Exp2 ;
EAnn.    Exp1 ::= Exp2 Colon Exp1 ;
EPair.   Exp  ::= Decl "," Exp ;

coercions Exp 6 ;
separator Exp ";" ;

Decl. Decl ::= AIdent "=" Exp1 ;
PDecl. Decl ::= "param" AIdent "=" Exp1 "ofErasedType" Exp2;
-- terminator Decl ";" ;

NoBind. Bind   ::= AIdent ; 
Bind.   Bind   ::= "(" AIdent Colon Exp ")" ;
AIdent. AIdent ::= Identifier ;

terminator Bind "" ;


|]
