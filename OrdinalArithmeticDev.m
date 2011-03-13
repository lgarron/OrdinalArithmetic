(* ::Package:: *)

(* ::Title:: *)
(*Ordinal Arithmetic Package Development Notebook*)


(* ::Subtitle:: *)
(*Lucas Garron*)
(*Started Mar 12, 2011*)


(* ::Section:: *)
(*Definitions*)


(* ::Subsection:: *)
(*TODO:*)
(*- OrdinalMinus*)
(*- OrdinalDivide*)
(*- Cardinal arithmetic: Subscript[\[Aleph], 0], etc. (how do we deal with operator ambiguity?)*)
(*- Fix TreeForm infinite recursion.*)


(* ::Subsection:: *)
(*Using ON as a short form for develepment because it's much easier to type than OrdinalNumber.*)
(*(Same for OrdinalAtom, OrdinalSum, OrdinalTimes, OrdinalPower.)*)
(*(Note: Plus, Product, and Power all start with P. Slightly annoying for naming abbreviations.)*)


ON=_Integer|\[Omega]|OA[_]|OS[ON__]|OT[ON__]|OP[ON__];

Remove[MakeOrdinal];
SetAttributes[MakeOrdinal,HoldAll]
MakeOrdinal[a_Integer]:=OA[a];
MakeOrdinal[\[Omega]]:=OA[\[Omega]];
MakeOrdinal[Plus[\[Alpha]:PatternSequence[_,__]]]:=ReleaseHold[Map[MakeOrdinal,(OS@@@(Hold@Hold[\[Alpha]])),{2}]];
MakeOrdinal[Times[\[Alpha]:PatternSequence[_,__]]]:=ReleaseHold[Map[MakeOrdinal,(OT@@@(Hold@Hold[\[Alpha]])),{2}]];
MakeOrdinal[Power[\[Alpha]_,\[Beta]_]]:=ReleaseHold[Map[MakeOrdinal,(OP@@@(Hold@Hold[\[Alpha],\[Beta]])),{2}]];
MO=MakeOrdinal;

Unprotect[OA,OS,OT,OP];
Format[\[Alpha]:OA[\[Alpha]1_]]:=Interpretation[\[Alpha]1,\[Alpha]];
Format[\[Alpha]:OS[\[Alpha]\[Alpha]__]]:=Interpretation[\[LeftAngleBracket]Row[{\[Alpha]\[Alpha]},"+"]\[RightAngleBracket],\[Alpha]];
Format[\[Alpha]:OT[\[Alpha]\[Alpha]__]]:=Interpretation[\[LeftAngleBracket]Row[{\[Alpha]\[Alpha]},"\[CenterDot]"]\[RightAngleBracket],\[Alpha]];
Format[\[Alpha]:OP[\[Alpha]m_,\[Alpha]e_]]:=Interpretation[\[LeftAngleBracket]\[Alpha]m^\[Alpha]e\[RightAngleBracket],\[Alpha]];
Protect[OA,OS,OT,OP];

CreateOrdinalSymbol=(Unprotect[#];#=.;#=#;Protect[#];)&;
CreateOrdinalSymbol/@{\[Omega],OA,OS,OT,OP};

ToTreeForm[\[Alpha]_]:=\[Alpha]/.{OS->"+",OT->"\[CenterDot]",OP->"^",\[Omega]->"\[Omega]",OA->Identity}//TreeForm;


(* NOTE: This doesn't necessarily recognize all unreduced expressions that are zero, if we introduce, say, minus. *)
Remove[OrdinalZeroQ];
OrdinalZeroQ[OA[\[Alpha]_Integer]]:=(\[Alpha]==0);
OrdinalZeroQ[OA[\[Omega]]]:=False;
OrdinalZeroQ[OS[\[Alpha]\[Alpha]__]]:=And@@(OrdinalZeroQ/@{\[Alpha]\[Alpha]});
OrdinalZeroQ[OT[\[Alpha]\[Alpha]__]]:=Or@@(OrdinalZeroQ/@{\[Alpha]\[Alpha]});
OrdinalZeroQ[OP[\[Alpha]m_,\[Alpha]e_]]:=OrdinalZeroQ[\[Alpha]m];

Remove[OrdinalEqual];
OrdinalEqual[\[Alpha]:ON,\[Alpha]:ON]:=True;


Remove[OrdinalLess];
OrdinalLess[OA[a_Integer],OA[b_Integer]]:=(a<b);
OrdinalLess[a:OA[_Integer],OP[OA[\[Omega]],\[Beta]:ON]]:=If[OrdinalZeroQ[\[Beta]],OrdinalLess[a,OA[1]],True];
OrdinalLess[a:OA[_Integer],OT[OA[\[Omega]],\[Beta]:ON]]:=If[OrdinalZeroQ[\[Beta]],OrdinalLess[a,OA[0]],True];
OrdinalLess[OT[\[Alpha]:ON,\[Beta]1:ON],OT[\[Alpha]:ON,\[Beta]2:ON]]:=OrdinalLess[\[Beta]1,\[Beta]2];
OrdinalLess[OP[OA[\[Omega]],\[Alpha]:ON],b:OA[_Integer]]:=If[OrdinalZeroQ[\[Alpha]],OrdinalLess[OA[1],b],False];
OrdinalLess[OP[\[Alpha]:ON,\[Beta]1:ON],OP[\[Alpha]:ON,\[Beta]2:ON]]:=OrdinalLess[\[Beta]1,\[Beta]2];
OrdinalLess[OA[\[Omega]],\[Beta]:ON]:=OrdinalLess[OP[OA[\[Omega]],OA[1]],\[Beta]];
OrdinalLess[\[Alpha]:ON,OA[\[Omega]]]:=OrdinalLess[\[Alpha],OP[OA[\[Omega]],OA[1]]];



Remove[OrdinalPlus];
OrdinalPlus[\[Alpha]\[Alpha]__]:=Module[{condensed=Pick[{\[Alpha]\[Alpha]},!OrdinalLess[##]&@@@Partition[{\[Alpha]\[Alpha]},2,1]~Join~{True}]},
(OS@@condensed)//.{
OS[\[Alpha]_]:>\[Alpha],
OS[x___,PatternSequence[\[Alpha]:ON,OA[0]],y___]:>OS[x,\[Alpha],y],
OS[x___,PatternSequence[OA[0],\[Beta]:ON],y___]:>OS[x,\[Beta],y],
OS[x___,PatternSequence[OA[a:_Integer],OA[b:_Integer]],y___]:>OS[x,OA[a+b],y],
OS[x___,PatternSequence[OT[\[Alpha]:ON,a:OA[_Integer]],OT[\[Alpha]:ON,b:OA[_Integer]]],y___]:>OS[x,OT[\[Alpha],OrdinalPlus[a,b]],y],
OS[x___,PatternSequence[OP[\[Alpha]:ON,a:OA[_Integer]],OP[\[Alpha]:ON,b:OA[_Integer]]],y___]:>OS[x,OP[\[Alpha],OrdinalPlus[a,b]],y],
OS[x___,PatternSequence[OP[\[Alpha]:ON,a:ON],OP[\[Alpha]:ON,b:ON]],y___]:>OS[x,OP[\[Alpha],OrdinalPlus[a,b]],y],
OS[x___,PatternSequence[Longest[\[Alpha]:Repeated[\[Alpha]1:ON,{2,\[Infinity]}]]],y___]:>OS[x,OT[\[Alpha]1,OA[Length[{\[Alpha]}]]],y]
}
];

Remove[OrdinalTimes];
OrdinalTimes[\[Alpha]:ON,OA[1]]:=\[Alpha]
OrdinalTimes[\[Alpha]:ON,\[Beta]:ON]:=If[OrdinalLess[\[Alpha],\[Beta]],\[Beta],OT[\[Alpha],\[Beta]]];
OrdinalTimes[\[Alpha]:(ON)..]:=Fold[OrdinalTimes,OA[0],{\[Alpha]}];

Remove[OrdinalPower];
OrdinalPower[OA[a_Integer],OA[b_Integer]]:=OA[a^b];
OrdinalPower[\[Alpha]:ON,\[Beta]:ON]:=OP[\[Alpha],\[Beta]];

Remove[OrdinalSimplify];
OrdinalSimplify[\[Alpha]_]:=(\[Alpha]/.{OS->OrdinalPlus,OT->OrdinalTimes,OP->OrdinalPower})
