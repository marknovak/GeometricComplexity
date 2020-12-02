(* ::Package:: *)

(* ::Subsection:: *)
(* Define Functional Responses - Count of prey eaten*)


(* ::Input::Initialization:: *)
H1 = a \[CapitalNu] P T;
R = (a \[CapitalNu] P T)/P;
H2 = (a \[CapitalNu] P T)/(1+a h \[CapitalNu]);
HV = (a \[CapitalNu] P T)/P^m;
AG = (a \[CapitalNu] P T)/(P+a h \[CapitalNu]);
BD = (a \[CapitalNu] P T)/(1+a h \[CapitalNu] + \[Gamma] (P-1));
CM = (a \[CapitalNu] P T)/((1+a h \[CapitalNu])(1+\[Gamma] (P-1)));
AA=(a \[CapitalNu] P T)/(P^m+a h \[CapitalNu]);


(* ::Subsection:: *)
(*Define Likelihood functions*)


(* ::Input::Initialization:: *)
PoislL[func_]:=-n func+Log[func] x/.{n->1}

lLH1Poiss[a_]:=PoislL[H1]
lLRPoiss[a_]:=PoislL[R]
lLHVPoiss[a_,m_]:=PoislL[HV]
lLAGPoiss[a_,h_]:=PoislL[AG]
lLH2Poiss[a_,h_]:=PoislL[H2]
lLBDPoiss[a_,h_,\[Gamma]_]:=PoislL[BD]
lLCMPoiss[a_,h_,\[Gamma]_]:=PoislL[CM]
lLAAPoiss[a_,h_,m_]:=PoislL[AA]


(* ::Subsection:: *)
(*Define functions to compute fisher matrix and expected fisher matrix*)


(* ::Input::Initialization:: *)
fisher[fun_,pars_]:=-D[Apply[fun,pars],{pars,2}]

EFisher[FisherMatrix_,func_,PDistE_,\[CapitalNu]DistE_]:=
Expectation[
Expectation[FisherMatrix,x\[Distributed] PoissonDistribution[func]],
{P\[Distributed]PDistE, \[CapitalNu]\[Distributed]\[CapitalNu]DistE}] 


(* ::Subsection:: *)
(*Define function for Determinant of Expected Fisher Matrix *)
(*given experimental design and min and max limits on expected count of prey eaten*)


(* ::Input::Initialization:: *)
DetEFisherTrunc[FisherMatrix_,func_,PDistE_,\[CapitalNu]DistE_,\[Lambda]min_,\[Lambda]max_,subs_]:=
Det[
Expectation[
Expectation[Boole[\[Lambda]min <= func<=\[Lambda]max]FisherMatrix,x\[Distributed] PoissonDistribution[func]]//.subs,
{P\[Distributed]PDistE, \[CapitalNu]\[Distributed]\[CapitalNu]DistE}] 
]


(* ::Subsection:: *)
(*Define functions to create experimental designs (prey and predator abundance levels)*)


(* ::Input::Initialization:: *)
logSpace[a_?Positive,b_?Positive,n_]:=Exp@Range[Log@a,Log@b,Log[b/a]/(n-1)]
log2Space[a_,b_,n_]:=2^Range[a,b,(b-a)/(n-1)]
logGRSpace[a_,b_,n_]:=Round[GoldenRatio^Range[a,b,(b-a)/(n-1)]]


(* ::Input::Initialization:: *)
PreyVals[n_,PreyMax_]:=logGRSpace[2,Log[GoldenRatio,PreyMax]+3,n];
PredVals[n_,PredMax_]:=logGRSpace[0,Log[GoldenRatio,PredMax]+1,n];



(* ::Subsection:: *)
(*Define master Geometric Complexity function w/ options*)


(* ::Input::Initialization:: *)
GeomComplexTrunc[
\[CapitalNu]values_,
Pvalues_,
ModelSetParNum_:1,
Tval_:1,
aMax_: 1000, 
NIntMethod_:"LocalAdaptive",
accgoal_:3,
maxRec_:500,
e_:10]:=
Module[
{\[CapitalNu]vals=\[CapitalNu]values,Pvals=Pvalues},
\[CapitalNu]probs=ConstantArray[1/Length[\[CapitalNu]vals],Length[\[CapitalNu]vals]];Pprobs=ConstantArray[1/Length[Pvals],Length[Pvals]];
\[CapitalNu]DistE=EmpiricalDistribution[\[CapitalNu]probs->\[CapitalNu]vals];
PDistE=EmpiricalDistribution[Pprobs->Pvals];
subs={T-> Tval};

P\[CapitalNu]rats=Sort[DeleteDuplicates[Join@@Outer[Divide,Pvals,\[CapitalNu]vals]]];
ParmRangeA={
{a,0,aMax},
DeleteDuplicates[Flatten[{{h},Sort[{0,P\[CapitalNu]rats,1,10^e},Less]}]],
DeleteDuplicates[Flatten[{{\[Gamma]},Sort[{0,1/Pvals,1,10^e},Less]}]],
DeleteDuplicates[Flatten[{{m},Sort[{0,P\[CapitalNu]rats,1,10},Less]}]]
};

Which[ModelSetParNum==1,

FisherH1Poiss=fisher[lLH1Poiss,{a}];
DetH1Trunc=DetEFisherTrunc[FisherH1Poiss,H1,PDistE,\[CapitalNu]DistE,0,Max[\[CapitalNu]vals],subs];

FisherRPoiss=fisher[lLRPoiss,{a}];
DetRTrunc=DetEFisherTrunc[FisherRPoiss,R,PDistE,\[CapitalNu]DistE,0,Max[\[CapitalNu]vals],subs];

NIntH1Trunc=Log[NIntegrate[Sqrt[DetH1Trunc],
ParmRangeA[[1]],
AccuracyGoal->accgoal,
Method->NIntMethod,
MaxRecursion->maxRec]];

NIntRTrunc=Log[NIntegrate[Sqrt[DetRTrunc],
ParmRangeA[[1]],
AccuracyGoal->accgoal,
Method->NIntMethod,
MaxRecursion->maxRec]];

{NIntH1Trunc,NIntRTrunc, 
NIntRTrunc/NIntH1Trunc}

, (* End of ModelSetParNum=1*)

ModelSetParNum==2,

FisherHVPoiss=fisher[lLHVPoiss,{a,m}];DetHVTrunc=DetEFisherTrunc[FisherHVPoiss,HV,PDistE,\[CapitalNu]DistE,0,Max[\[CapitalNu]vals],subs];

FisherH2Poiss=fisher[lLH2Poiss,{a, h}];
DetH2Trunc=DetEFisherTrunc[FisherH2Poiss,H2,PDistE,\[CapitalNu]DistE,0,Max[\[CapitalNu]vals],subs];

FisherAGPoiss=fisher[lLAGPoiss,{a, h}];
DetAGTrunc=DetEFisherTrunc[FisherAGPoiss,AG,PDistE,\[CapitalNu]DistE,0,Max[\[CapitalNu]vals],subs];


NIntHVTrunc=Log[NIntegrate[Sqrt[DetHVTrunc],
ParmRangeA[[1]],
ParmRangeA[[4]],
AccuracyGoal->accgoal,
Method->NIntMethod,
MaxRecursion->maxRec]];

NIntH2Trunc=Log[NIntegrate[Sqrt[DetH2Trunc],
ParmRangeA[[1]],
ParmRangeA[[2]],
AccuracyGoal->accgoal,
Method->NIntMethod,
MaxRecursion->maxRec]];

NIntAGTrunc=Log[NIntegrate[Sqrt[DetAGTrunc],
ParmRangeA[[1]],
ParmRangeA[[2]],
AccuracyGoal->accgoal,
Method->NIntMethod,
MaxRecursion->maxRec]];

{NIntHVTrunc, NIntH2Trunc, NIntAGTrunc, 
NIntHVTrunc/NIntH2Trunc,NIntAGTrunc/NIntH2Trunc}

, (* End of ModelSetParNum=2*)

ModelSetParNum==3,

FisherBDPoiss=fisher[lLBDPoiss,{a, h,\[Gamma]}];
DetBDTrunc=DetEFisherTrunc[FisherBDPoiss,BD,PDistE,\[CapitalNu]DistE,0,Max[\[CapitalNu]vals],subs];

FisherCMPoiss=fisher[lLCMPoiss,{a, h,\[Gamma]}];
DetCMTrunc=DetEFisherTrunc[FisherCMPoiss,CM,PDistE,\[CapitalNu]DistE,0,Max[\[CapitalNu]vals],subs];

FisherAAPoiss=fisher[lLAAPoiss,{a, h,m}];
DetAATrunc=DetEFisherTrunc[FisherAAPoiss,AA,PDistE,\[CapitalNu]DistE,0,Max[\[CapitalNu]vals],subs];

NIntBDTrunc=Log[NIntegrate[Sqrt[DetBDTrunc],
ParmRangeA[[1]],
ParmRangeA[[2]],
ParmRangeA[[3]],
AccuracyGoal->accgoal,
Method-> NIntMethod]];

NIntCMTrunc=Log[NIntegrate[Sqrt[DetCMTrunc],
ParmRangeA[[1]],
ParmRangeA[[2]],
ParmRangeA[[3]],
AccuracyGoal->accgoal,
Method->NIntMethod,
MaxRecursion->maxRec]];

NIntAATrunc=Log[NIntegrate[Sqrt[DetAATrunc],
ParmRangeA[[1]],
ParmRangeA[[2]],
ParmRangeA[[4]],
AccuracyGoal->accgoal,
Method->NIntMethod,
MaxRecursion->maxRec]];

{NIntBDTrunc,NIntCMTrunc,NIntAATrunc,
NIntCMTrunc/NIntBDTrunc,NIntAATrunc/NIntBDTrunc}

] (* End of ModelSetParNum=3*)
]


(* ::Subsection:: *)
(*Apply across designs*)


(* ::Input::Initialization:: *)
PreyMinLevels=5;
PreyMaxLevels=13;
PredMinLevels=2;
PredMaxLevels=8;


(* ::Input::Initialization:: *)
GeomCompP1var=
Flatten[
ParallelTable[
Flatten[{
Max[PreyVals[i,Fibonacci[i]]],
Max[PredVals[j,Fibonacci[j]]],
GeomComplexTrunc[PreyVals[i,Fibonacci[i]],PredVals[j,Fibonacci[j]],ModelSetParNum= 1]}],
{i, PreyMinLevels,PreyMaxLevels},{j,PredMinLevels,PredMaxLevels}
],
1];
Save["GeomCompP1var.txt",GeomCompP1var]


(* ::Input::Initialization:: *)
GeomCompP2var=
Flatten[
ParallelTable[
Flatten[{
Max[PreyVals[i,Fibonacci[i]]],
Max[PredVals[j,Fibonacci[j]]],
GeomComplexTrunc[PreyVals[i,Fibonacci[i]],PredVals[j,Fibonacci[j]],ModelSetParNum= 2]}],
{i, PreyMinLevels,PreyMaxLevels},{j,PredMinLevels,PredMaxLevels}
],
1];
Save["GeomCompP2var.txt",GeomCompP2var]


(* ::Input::Initialization:: *)
GeomCompP3var=
Flatten[
ParallelTable[
Flatten[{
Max[PreyVals[i,Fibonacci[i]]],
Max[PredVals[j,Fibonacci[j]]],
GeomComplexTrunc[PreyVals[i,Fibonacci[i]],PredVals[j,Fibonacci[j]],ModelSetParNum= 3]}],
{i, PreyMinLevels,PreyMaxLevels},{j,PredMinLevels,PredMaxLevels}
],
1];
Save["GeomCompP3var.txt",GeomCompP3var]


(* ::Input::Initialization:: *)
GeomCompP1fix=
Flatten[
ParallelTable[
Flatten[{
Length[PreyVals[i,Fibonacci[PreyMaxLevels]]],
Length[PredVals[j,Fibonacci[PredMaxLevels]]],
GeomComplexTrunc[PreyVals[i,Fibonacci[PreyMaxLevels]],PredVals[j,Fibonacci[PredMaxLevels]],ModelSetParNum= 1]}],
{i, PreyMinLevels,PreyMaxLevels},{j,PredMinLevels,PredMaxLevels}
],
1];
Save["GeomCompP1fix.txt",GeomCompP1fix]


(* ::Input::Initialization:: *)
GeomCompP2fix=
Flatten[
ParallelTable[
Flatten[{
Length[PreyVals[i,Fibonacci[PreyMaxLevels]]],
Length[PredVals[j,Fibonacci[PredMaxLevels]]],
GeomComplexTrunc[PreyVals[i,Fibonacci[PreyMaxLevels]],PredVals[j,Fibonacci[PredMaxLevels]],ModelSetParNum= 2]}],
{i, PreyMinLevels,PreyMaxLevels},{j,PredMinLevels,PredMaxLevels}
],
1];
Save["GeomCompP2fix.txt",GeomCompP2fix]


(* ::Input::Initialization:: *)
GeomCompP3fix=
Flatten[
ParallelTable[
Flatten[{
Length[PreyVals[i,Fibonacci[PreyMaxLevels]]],
Length[PredVals[j,Fibonacci[PredMaxLevels]]],
GeomComplexTrunc[PreyVals[i,Fibonacci[PreyMaxLevels]],PredVals[j,Fibonacci[PredMaxLevels]],ModelSetParNum= 3]}],
{i, PreyMinLevels,PreyMaxLevels},{j,PredMinLevels,PredMaxLevels}
],
1];
Save["GeomCompP3fix.txt",GeomCompP3fix]
