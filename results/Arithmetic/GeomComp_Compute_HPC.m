(* ::Package:: *)

(* ::Input::Initialization:: *)
Clear["Global`*"]

AbundSeries="Arithmetic";


fisher[fun_,pars_]:=-D[Apply[fun,pars],{pars,2}]
EFisher[FisherMatrix_,func_,PDistE_,\[CapitalNu]DistE_,subs_]:=
Expectation[
Expectation[
FisherMatrix/.subs,x\[Distributed] PoissonDistribution[func/.subs]],
{P\[Distributed]PDistE, \[CapitalNu]\[Distributed]\[CapitalNu]DistE}] 
SqrtDetEFlim[func_,Det_,\[CapitalNu]vals_,Pvals_,subs_,FminMult_,FmaxMult_]:=
Piecewise[
{{Sqrt[Det],
Max[func/.subs/.P-> Pvals/.\[CapitalNu]-> \[CapitalNu]vals]<=  Max[\[CapitalNu]vals]*FmaxMult && Min[func/.subs/.P-> Pvals/.\[CapitalNu]->{Max[\[CapitalNu]vals]}]>= 1 *FminMult 
}}];
SqrtDetEFlimSN1[func_,Det_,\[CapitalNu]vals_,Pvals_,subs_,FminMult_,FmaxMult_]:=
Piecewise[
{{Sqrt[Det],
Max[func/.subs/.P-> Pvals/.\[CapitalNu]-> \[CapitalNu]vals]<=  Max[\[CapitalNu]vals]*FmaxMult && Min[func/.subs/.P-> Pvals/.\[CapitalNu]->{Max[\[CapitalNu]vals]}]>= 1*FminMult   &&
d b Max[func/.subs/.P-> Pvals/.\[CapitalNu]->\[CapitalNu]vals] <= 1
}}];
SqrtDetEFlimSN2[func_,Det_,\[CapitalNu]vals_,Pvals_,subs_,FminMult_,FmaxMult_]:=
Piecewise[
{{Sqrt[Det],
Max[func/.subs/.P-> Pvals/.\[CapitalNu]-> \[CapitalNu]vals]<= Max[\[CapitalNu]vals]*FmaxMult && Min[func/.subs/.P-> Pvals/.\[CapitalNu]->{Max[\[CapitalNu]vals]}]>= 1 *FminMult  &&
 b Max[func/.subs/.P-> Pvals/.\[CapitalNu]->\[CapitalNu]vals]<=   1 
}}];
(* k=1 *)
H1 = a \[CapitalNu] P T; (* Holling Type I *)
LR = a \[CapitalNu] /P P T; (* Linear ratio-dependent *)
BWL1 = a Sqrt[\[CapitalNu] P] T; (* Barbier,Wojcik & Loreau 2021 *)

(*k=2*)
H2 = (a \[CapitalNu])/(1+a b \[CapitalNu]) P T; (* Holling Type II *)
MM = (a \[CapitalNu])/(b+\[CapitalNu]) P T; (* Michaelis-Menten *)
HV = a \[CapitalNu] /P^v P T; (* Hassell-Varley *)
R = a \[CapitalNu]^u P T; (* Rosenzweig '71 *)
AG = (a \[CapitalNu]/P)/(1+a b \[CapitalNu]/P) P T; (* Arditi-Ginzburg, Sutherland *)
GI =  1/b (1-Exp[-a \[CapitalNu]]) P T ;
GIA = 1/b (1-Exp[-a b \[CapitalNu]]) P T; (* Gause-Ivlev modified by Aldebert *)
GB = 1/b (1-Exp[-a \[CapitalNu] / P]) P T; (* Gutierrez & Baumgaertner 1984 *)

HT =1/b Tanh[a b \[CapitalNu]] P T; (* Jassby & Platt 1976 *)
HTb =1/b (Exp[2 a b \[CapitalNu] ]- 1)/(Exp[2 a b \[CapitalNu] ]+ 1) P T ; (* Alternative parameterization of Jassby & Platt 1976 *)
H3= (a \[CapitalNu]^2)/(1+a b \[CapitalNu]^2) P T; (* Holling Type III *)
AGK = (a (\[CapitalNu]/P)^2)/(1+a b (\[CapitalNu]/P)^2) P T; (* Kratina et al. 2008 *)
A1=Sqrt[(a \[CapitalNu])/(1+a b \[CapitalNu])]P T;(* Sqrt[(q c \[CapitalNu])/(d(1 + c h \[CapitalNu]))]P T *)  (* Abrams 1982 *)
A3=(a Sqrt[\[CapitalNu]])/(1+ a b Sqrt[\[CapitalNu]]) P T;(*Sqrt[\[CapitalNu]]/(2Sqrt[u \[Eta]]+ hSqrt[\[CapitalNu]]) P T *)(* Abrams 1982 *)
SH =  (a \[CapitalNu])/(b+(\[CapitalNu]^2) ) P T; (* Sokol & Howell 1987 *)
SHb = (a \[CapitalNu])/(1+a b (\[CapitalNu]^2) ) P T ; (* Holling-form Sokol & Howell 1987 *)


(*k=3*)
BD = (a \[CapitalNu])/(1+a b \[CapitalNu] + c (P-1)) P T; (* Beddington-DeAngelis *)
CM = (a \[CapitalNu])/(1+a b \[CapitalNu]+c (P-1)+a b c \[CapitalNu](P-1)) P T; (* Crowley-Martin *)
AA=(a \[CapitalNu]/P^v)/(1+a b \[CapitalNu]/P^v) P T; (* Arditi-Akcakaya *)
BWL2 = a \[CapitalNu]^u P^v T; (* Barbier,Wojcik & Loreau 2021 *)
H3R= (a \[CapitalNu]^u)/(1+a b \[CapitalNu]^u) P T; (* Holling Type III *)
A2=(a \[CapitalNu])/(1 + a b \[CapitalNu] + Sqrt[a \[CapitalNu] c(1+a b \[CapitalNu])]) P T; (* Abrams 1982 *)
S3= ((a \[CapitalNu])/(1+a b \[CapitalNu]))^u P T; (* new, generalized A1 *)
S3b= ((a \[CapitalNu])/(b+ \[CapitalNu]))^u P T; (* new, generalized A1 in MM form*)
HLB =(a \[CapitalNu]^2)/(1 + c \[CapitalNu] + a b \[CapitalNu]^2) P T; (* Hassell, Lawton & Beddington 1977 *)
HLBb =(a \[CapitalNu]^2)/(b + \[CapitalNu] + c \[CapitalNu]^2) P T; (* Michaelis-Mentend-form of Hassell, Lawton & Beddington 1977 *)

MH =(a \[CapitalNu])/(1 + a b \[CapitalNu] + c (\[CapitalNu]^2) ) P T;  (* Holling-form Monod-Haldane; Andrews 1968 *)
MHb =(a \[CapitalNu])/(b +  \[CapitalNu] + c (\[CapitalNu]^2) ) P T;  (* Monod-Haldane; Andrews 1968 *)
MHc =(a \[CapitalNu])/(b +  \[CapitalNu] + ((\[CapitalNu]^2)/c) ) P T;  (* original Monod-Haldane; Andrews 1968 *)
To =(a \[CapitalNu])/(1 + a b \[CapitalNu] + c (\[CapitalNu]^3) ) P T;  (* Tostowaryk '72 *)
FHM =(a \[CapitalNu] Exp[d \[CapitalNu]])/(1 + a b \[CapitalNu] Exp[d \[CapitalNu]] ) P T;  (* Fujii, Holling & Mace '86 *)
W = 1/b (1-Exp[-a \[CapitalNu] / P^v]) P T; (* Watt 1959 *)
TTA = (a \[CapitalNu])/(1 + a b \[CapitalNu] + c P - (1-Exp[- c P]) ) P T;  (* Tyutyunov, Titova & Arditi 2008 *)
 SBB=(a (\[CapitalNu]/P^v)^2)/(1+a b (\[CapitalNu]/P^v)^2) P T;   (* Schenk, Bersier & Bacher 2005 *)
SSS=  (2 a \[CapitalNu])/(1 + a (b + c) \[CapitalNu] + Sqrt[(1+a (b+c) \[CapitalNu]) (1+a (b+c+4 b c) \[CapitalNu])]) P T; (* Jeschke et al. 2002 using citardauq Formula *)


(*k=4*)
BDOR = (a \[CapitalNu]^u)/(1+a b \[CapitalNu]^u + c (P-1)) P T;  (* Okuyama & Ruyle 2011 *)
CMOR = (a \[CapitalNu]^u)/(1+a b \[CapitalNu]^u+c (P-1)+a b c \[CapitalNu]^u (P-1)) P T;  (* Okuyama & Ruyle 2011 *)
AAOR=(a \[CapitalNu]^u/P^v)/(1+a b \[CapitalNu]^u/P^v) P T;  (* Okuyama & Ruyle 2011 *)
SN1=(a \[CapitalNu])/(1+ a b \[CapitalNu] + c (P-1)+a b c (1-d) \[CapitalNu](P-1)) P T; (* Stouffer & Novak 2021 *)
SN2=(a \[CapitalNu] (1+c (1-d) (P-1)))/(1+ a b \[CapitalNu] + c (P-1)+a b c (1-d) \[CapitalNu](P-1)) P T; (* new, but see Stouffer & Novak 2021 *)




models = {
H1,LR,BWL1,     
H2,MM,HV,R,AG,GI, GIA, GB, HT,HTb, H3,AGK, A1, A3, SH,SHb,      
BD, CM, AA, BWL2, H3R, A2, S3,S3b,HLB,HLBb, MH,MHb, MHc,To, FHM,W, TTA, SBB,SSS,  
BDOR, CMOR, AAOR, SN1, SN2};
DumpSave["Models.mx",
{models,
H1,LR,BWL1,
H2,MM,HV,R,AG,GI, GIA, GB, HT,HTb, H3, AGK,A1, A3, SH,SHb, 
BD, CM, AA, BWL2, H3R, A2, S3,S3b,HLB, HLBb,MH,MHb, MHc,To, FHM,W, TTA,SBB,SSS,
BDOR, CMOR, AAOR, SN1, SN2}];


PoislL[func_]:=-n func+Log[func] x/.{n->1}

lLH1[a_]:=PoislL[H1]
lLLR[a_]:=PoislL[LR]
lLBWL1[a_]:=PoislL[BWL1]

lLH2[a_,b_]:=PoislL[H2]
lLMM[a_,b_]:=PoislL[MM]
lLHV[a_,v_]:=PoislL[HV]
lLR[a_,u_]:=PoislL[R]
lLAG[a_,b_]:=PoislL[AG]
lLGI[a_,b_]:=PoislL[GI]
lLGIA[a_,b_]:=PoislL[GIA]
lLGB[a_,b_]:=PoislL[GB]
lLHT[a_,b_]:=PoislL[HT]
lLHTb[a_,b_]:=PoislL[HTb]
lLH3[a_,b_]:=PoislL[H3]
lLAGK[a_,b_]:=PoislL[AGK]
lLA3[a_,b_]:=PoislL[A3]
lLA1[a_,b_]:=PoislL[A1]
lLSH[a_,b_]:=PoislL[SH]
lLSHb[a_,b_]:=PoislL[SHb]

lLBD[a_,b_,c_]:=PoislL[BD]
lLCM[a_,b_,c_]:=PoislL[CM]
lLAA[a_,b_,v_]:=PoislL[AA]
lLBWL2[a_,v_,u_]:=PoislL[BWL2]
lLH3R[a_,b_,u_]:=PoislL[H3R]
lLA2[a_,b_,c_]:=PoislL[A2]
lLHLB[a_,b_,c_]:=PoislL[HLB]
lLHLBb[a_,b_,c_]:=PoislL[HLBb]
lLMH[a_,b_,c_]:=PoislL[MH]
lLMHb[a_,b_,c_]:=PoislL[MHb]
lLMHc[a_,b_,c_]:=PoislL[MHc]
lLTo[a_,b_,c_]:=PoislL[To]
lLFHM[a_,b_,d_]:=PoislL[FHM]
lLW[a_,b_,v_]:=PoislL[W]
lLTTA[a_,b_,c_]:=PoislL[TTA]
lLSBB[a_,b_,v_]:=PoislL[SBB]
lLSSS[a_,b_,c_]:=PoislL[SSS]
lLS3[a_,b_,u_]:=PoislL[S3]
lLS3b[a_,b_,u_]:=PoislL[S3b]

lLBDOR[a_,b_,c_,u_]:=PoislL[BDOR]
lLCMOR[a_,b_,c_,u_]:=PoislL[CMOR]
lLAAOR[a_,b_,v_,u_]:=PoislL[AAOR]
lLSN1[a_,b_,c_,d_]:=PoislL[SN1]
lLSN2[a_,b_,c_,d_]:=PoislL[SN2]

ClearAll[GeomComplex]
GeomComplex[
\[CapitalNu]values_,
Pvalues_,
Model_]:=
Module[
{
\[CapitalNu]vals=\[CapitalNu]values,
Pvals=Pvalues,
Tval=1,
NIntMethod= {"LocalAdaptive","SingularityHandler"->Automatic},
minRec=150,
maxRec=500,
accgoal=3, 
precgoal=3,
FminMult=1,
FmaxMult=1
},
\[CapitalNu]probs=ConstantArray[1/Length[\[CapitalNu]vals],Length[\[CapitalNu]vals]];
Pprobs=ConstantArray[1/Length[Pvals],Length[Pvals]];
\[CapitalNu]DistE=EmpiricalDistribution[\[CapitalNu]probs->\[CapitalNu]vals];
PDistE=EmpiricalDistribution[Pprobs->Pvals];
subs={T-> Tval};

ParmRange={
{a,0,Infinity},
{b,0,Infinity},
{c,0,Infinity},
{v,0,1,Infinity},
{u,0,1,Infinity},
{d,-Infinity,-1,0,1,Infinity} 
};

Which[
Model=="H1",
DetH1=Det[EFisher[fisher[lLH1,{a}],H1,PDistE,\[CapitalNu]DistE,subs]];
NIntH1=
Log[
NIntegrate[
SqrtDetEFlim[H1,DetH1,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MaxRecursion->maxRec]]
,
Model=="LR",
DetLR=Det[EFisher[fisher[lLLR,{a}],LR,PDistE,\[CapitalNu]DistE,subs]];
NIntLR=
Log[
NIntegrate[
SqrtDetEFlim[LR,DetLR,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MaxRecursion->maxRec]]
, 
Model=="BWL1",
DetBWL1=Det[EFisher[fisher[lLBWL1,{a}],BWL1,PDistE,\[CapitalNu]DistE,subs]];
NIntBWL1=
Log[
NIntegrate[
SqrtDetEFlim[BWL1,DetBWL1,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MaxRecursion->maxRec]]
, 
Model=="H2",
DetH2=Det[EFisher[fisher[lLH2,{a, b}],H2,PDistE,\[CapitalNu]DistE,subs]];
NIntH2=
Log[
NIntegrate[
SqrtDetEFlim[H2,DetH2,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="MM",
DetMM=Det[EFisher[fisher[lLMM,{a, b}],MM,PDistE,\[CapitalNu]DistE,subs]];
NIntMM=
Log[
NIntegrate[
SqrtDetEFlim[MM,DetMM,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="HV",
DetHV=Det[EFisher[fisher[lLHV,{a,v}],HV,PDistE,\[CapitalNu]DistE,subs]];
NIntHV=
Log[
NIntegrate[
SqrtDetEFlim[HV,DetHV,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[4]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="R",
DetR=Det[EFisher[fisher[lLR,{a,u}],R,PDistE,\[CapitalNu]DistE,subs]];
NIntR=
Log[
NIntegrate[
SqrtDetEFlim[R,DetR,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[5]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion-> minRec,
MaxRecursion->maxRec]]
,
Model=="H3",
DetH3=Det[EFisher[fisher[lLH3,{a, b}],H3,PDistE,\[CapitalNu]DistE,subs]];
NIntH3=
Log[
NIntegrate[
SqrtDetEFlim[H3,DetH3,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="AG",
DetAG=Det[EFisher[fisher[lLAG,{a, b}],AG,PDistE,\[CapitalNu]DistE,subs]];
NIntAG=
Log[
NIntegrate[
SqrtDetEFlim[AG,DetAG,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="GI",
DetGI=Det[EFisher[fisher[lLGI,{a, b}],GI,PDistE,\[CapitalNu]DistE,subs]];
NIntGI=
Log[
NIntegrate[
SqrtDetEFlim[GI,DetGI,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->0,
MaxRecursion->maxRec]]
,
Model=="GIA",
DetGIA=Det[EFisher[fisher[lLGIA,{a, b}],GIA,PDistE,\[CapitalNu]DistE,subs]];
NIntGIA=
Log[
NIntegrate[
SqrtDetEFlim[GIA,DetGIA,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="GB",
DetGB=Det[EFisher[fisher[lLGB,{a, b}],GB,PDistE,\[CapitalNu]DistE,subs]];
NIntGB=
Log[
NIntegrate[
SqrtDetEFlim[GB,DetGB,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->0,
MaxRecursion->maxRec]]
,
Model=="HT",
DetHT=Det[EFisher[fisher[lLHT,{a, b}],HT,PDistE,\[CapitalNu]DistE,subs]];
NIntHT=
Log[
NIntegrate[
SqrtDetEFlim[HT,DetHT,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="HTb",
DetHTb=Det[EFisher[fisher[lLHTb,{a, b}],HTb,PDistE,\[CapitalNu]DistE,subs]];
NIntHTb=
Log[
NIntegrate[
SqrtDetEFlim[HTb,DetHTb,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="A3",
DetA3=Det[EFisher[fisher[lLA3,{a,b}],A3,PDistE,\[CapitalNu]DistE,subs]];
NIntA3=
Log[
NIntegrate[
SqrtDetEFlim[A3,DetA3,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="AGK",
DetAGK=Det[EFisher[fisher[lLAGK,{a, b}],AGK,PDistE,\[CapitalNu]DistE,subs]];
NIntAGK=
Log[
NIntegrate[
SqrtDetEFlim[AGK,DetAGK,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="A1",
DetA1=Det[EFisher[fisher[lLA1,{a,b}],A1,PDistE,\[CapitalNu]DistE,subs]];
NIntA1=
Log[
NIntegrate[
SqrtDetEFlim[A1,DetA1,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="SH",
DetSH=Det[EFisher[fisher[lLSH,{a,b}],SH,PDistE,\[CapitalNu]DistE,subs]];
NIntSH= 
Log[
NIntegrate[
SqrtDetEFlim[SH,DetSH,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec] ]
,
Model=="SHb",
DetSHb=Det[EFisher[fisher[lLSHb,{a,b}],SHb,PDistE,\[CapitalNu]DistE,subs]];
NIntSHb= 
Log[
NIntegrate[
SqrtDetEFlim[SHb,DetSHb,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec] ]
,
Model=="BD",
DetBD=Det[EFisher[fisher[lLBD,{a,b,c}],BD,PDistE,\[CapitalNu]DistE,subs]];
NIntBD=
Log[
NIntegrate[
SqrtDetEFlim[BD,DetBD,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method-> NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="CM",
DetCM=Det[EFisher[fisher[lLCM,{a,b,c}],CM,PDistE,\[CapitalNu]DistE,subs]];
NIntCM=
Log[
NIntegrate[
SqrtDetEFlim[CM,DetCM,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="AA",
DetAA=Det[EFisher[fisher[lLAA,{a,b,v}],AA,PDistE,\[CapitalNu]DistE,subs]];
NIntAA=
Log[
NIntegrate[
SqrtDetEFlim[AA,DetAA,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[4]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="BWL2",
DetBWL2=Det[EFisher[fisher[lLBWL2,{a,v,u}],BWL2,PDistE,\[CapitalNu]DistE,subs]];
NIntBWL2=
Log[
NIntegrate[
SqrtDetEFlim[BWL2,DetBWL2,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[4]],
ParmRange[[5]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="H3R",
DetH3R=Det[EFisher[fisher[lLH3R,{a,b,u}],H3R,PDistE,\[CapitalNu]DistE,subs]];
NIntH3R=
Log[
NIntegrate[
SqrtDetEFlim[H3R,DetH3R,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[5]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="A2",
DetA2=Det[EFisher[fisher[lLA2,{a,b,c}],A2,PDistE,\[CapitalNu]DistE,subs]];
NIntA2=
Log[
NIntegrate[
SqrtDetEFlim[A2,DetA2,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="HLB",
DetHLB=Det[EFisher[fisher[lLHLB,{a,b,c}],HLB,PDistE,\[CapitalNu]DistE,subs]];
NIntHLB=
Log[
NIntegrate[
SqrtDetEFlim[HLB,DetHLB,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="HLBb",
DetHLBb=Det[EFisher[fisher[lLHLBb,{a,b,c}],HLBb,PDistE,\[CapitalNu]DistE,subs]];
NIntHLBb=
Log[
NIntegrate[
SqrtDetEFlim[HLBb,DetHLBb,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="MH",
DetMH=Det[EFisher[fisher[lLMH,{a,b,c}],MH,PDistE,\[CapitalNu]DistE,subs]];
NIntMH=
Log[
NIntegrate[
SqrtDetEFlim[MH,DetMH,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="MHb",
DetMHb=Det[EFisher[fisher[lLMHb,{a,b,c}],MHb,PDistE,\[CapitalNu]DistE,subs]];
NIntMHb=
Log[
NIntegrate[
SqrtDetEFlim[MHb,DetMHb,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="MHc",
DetMHc=Det[EFisher[fisher[lLMHc,{a,b,c}],MHc,PDistE,\[CapitalNu]DistE,subs]];
NIntMHc=
Log[
NIntegrate[
SqrtDetEFlim[MHc,DetMHc,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="To",
DetTo=Det[EFisher[fisher[lLTo,{a,b,c}],To,PDistE,\[CapitalNu]DistE,subs]];
NIntTo=
Log[
NIntegrate[
SqrtDetEFlim[To,DetTo,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="FHM",
DetFHM=Det[EFisher[fisher[lLFHM,{a,b,d}],FHM,PDistE,\[CapitalNu]DistE,subs]];
NIntFHM=
Log[
NIntegrate[
SqrtDetEFlim[FHM,DetFHM,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[6]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="W",
DetW=Det[EFisher[fisher[lLW,{a, b,v}],W,PDistE,\[CapitalNu]DistE,subs]];
NIntW=
Log[
NIntegrate[
SqrtDetEFlim[W,DetW,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[4]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="TTA",
DetTTA=Det[EFisher[fisher[lLTTA,{a,b,c}],TTA,PDistE,\[CapitalNu]DistE,subs]];
NIntTTA=
Log[
NIntegrate[
SqrtDetEFlim[TTA,DetTTA,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="SBB",
DetSBB=Det[EFisher[fisher[lLSBB,{a,b,v}],SBB,PDistE,\[CapitalNu]DistE,subs]];
NIntSBB=
Log[
NIntegrate[
SqrtDetEFlim[SBB,DetSBB,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[4]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->minRec,
MaxRecursion->maxRec]]
,
Model=="SSS",
DetSSS=Det[EFisher[fisher[lLSSS,{a,b,c}],SSS,PDistE,\[CapitalNu]DistE,subs]];
NIntSSS=
Log[
NIntegrate[
SqrtDetEFlim[SSS,DetSSS,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion-> minRec,
MaxRecursion->maxRec]]
,
Model=="S3",
DetS3=Det[EFisher[fisher[lLS3,{a,b,u}],S3,PDistE,\[CapitalNu]DistE,subs]];
NIntS3=
Log[
NIntegrate[
SqrtDetEFlim[S3,DetS3,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[5]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion-> minRec,
MaxRecursion->maxRec]]
,
Model=="S3b",
DetS3b=Det[EFisher[fisher[lLS3b,{a,b,u}],S3b,PDistE,\[CapitalNu]DistE,subs]];
NIntS3b=
Log[
NIntegrate[
SqrtDetEFlim[S3b,DetS3b,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[5]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion-> minRec,
MaxRecursion->maxRec]]
,
Model=="BDOR",
DetBDOR=Det[EFisher[fisher[lLBDOR,{a,b,c,u}],BDOR,PDistE,\[CapitalNu]DistE,subs]];
NIntBDOR=
Log[
NIntegrate[
SqrtDetEFlim[BDOR,DetBDOR,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
ParmRange[[5]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method-> NIntMethod,
MinRecursion->300,
MaxRecursion->1000]]
,
Model=="CMOR",
DetCMOR=Det[EFisher[fisher[lLCMOR,{a,b,c,u}],CMOR,PDistE,\[CapitalNu]DistE,subs]];
NIntCMOR=
Log[
NIntegrate[
SqrtDetEFlim[CMOR,DetCMOR,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
ParmRange[[5]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->300,
MaxRecursion->1000]]
,
Model=="AAOR",
DetAAOR=Det[EFisher[fisher[lLAAOR,{a,b,v,u}],AAOR,PDistE,\[CapitalNu]DistE,subs]];
NIntAAOR=
Log[
NIntegrate[
SqrtDetEFlim[AAOR,DetAAOR,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[4]],
ParmRange[[5]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method->NIntMethod,
MinRecursion->300,
MaxRecursion->1000]]
,
Model=="SN1",
DetSN1=Det[EFisher[fisher[lLSN1,{a, b,c, d}],SN1,PDistE,\[CapitalNu]DistE,subs]];
NIntSN1=
Log[
NIntegrate[
SqrtDetEFlimSN1[SN1,DetSN1,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
ParmRange[[6]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method-> NIntMethod,
MinRecursion->300,
MaxRecursion->1000]]
,
Model=="SN2",
DetSN2=Det[EFisher[
fisher[lLSN2,{a, b,c, d}],SN2,PDistE,\[CapitalNu]DistE,subs]];
NIntSN2=
Log[
NIntegrate[
SqrtDetEFlimSN2[SN2,DetSN2,\[CapitalNu]vals,Pvals,subs,FminMult, FmaxMult], 
ParmRange[[1]],
ParmRange[[2]],
ParmRange[[3]],
ParmRange[[6]],
AccuracyGoal->accgoal,
PrecisionGoal->precgoal,
Method-> NIntMethod,
MinRecursion->300,
MaxRecursion->1000]]
] 
]
logGRSpace[a_,b_,n_]:=Round[GoldenRatio^Range[a,b,(b-a)/(n-1)]]

PreyVals[n_,PreyMax_,AbundSeries_]:=
Which[
AbundSeries=="GoldenRatio",
logGRSpace[2,Log[GoldenRatio,PreyMax]+3,n],
AbundSeries=="Arithmetic",
Round[Range[3,Max[logGRSpace[2,Log[GoldenRatio,PreyMax]+3,n]],(Max[logGRSpace[2,Log[GoldenRatio,PreyMax]+3,n]]-3)/(n-1)]]
]
PredVals[n_,PredMax_,AbundSeries_]:=
If[n==1,
{1}, (* If only a single level is requested, specify a single predator individual *)
Which[ (* Otherwise, determine predator levels according to GoldenRatio or Arithmetic series beginning with 1 predator individual *)
AbundSeries=="GoldenRatio",
logGRSpace[0,Log[GoldenRatio,PredMax]+1,n], 
AbundSeries=="Arithmetic",
Round[Range[1,Max[logGRSpace[0,Log[GoldenRatio,PredMax]+1,n]],(Max[logGRSpace[0,Log[GoldenRatio,PredMax]+1,n]]-1)/(n-1)]]
]]
PreyMinLevels=5;
PreyMaxLevelsVar=10; 
PreyMaxLevelsFix=10;
PredMinLevels=1;
PredMaxLevelsVar=5; 
PredMaxLevelsFix=4; 

VarDesigns=Table[
{PreyVals[i,Fibonacci[i],AbundSeries],
PredVals[j,Fibonacci[j],AbundSeries]},
{i, PreyMinLevels,PreyMaxLevelsVar},
{j,PredMinLevels,PredMaxLevelsVar}
];
TableForm[VarDesigns];
Export["DesignsVar.txt",TeXForm[VarDesigns]];
FixDesigns=Table[
{PreyVals[i,Fibonacci[PreyMaxLevelsFix],AbundSeries],
PredVals[j,Fibonacci[PredMaxLevelsFix],AbundSeries]},
{i, PreyMinLevels,PreyMaxLevelsFix},
{j,PredMinLevels,PredMaxLevelsFix}
];
TableForm[FixDesigns];
Export["DesignsFix.txt",TeXForm[FixDesigns]];
ClearAll[GeomComp];
GeomComp[
ModelAbb_,
Type_,
AbundSeries_]:=
Module[
{
(******* Be sure to match the following with exported designs above *******)
PreyMinLevels=5, 
PreyMaxLevelsVar=10,
PreyMaxLevelsFix=10,
PredMinLevels=1, 
PredMaxLevelsVar=5,
PredMaxLevelsFix=4
}
,
Which[
Type=="Var",
Flatten[
ParallelTable[
Flatten[{
Max[PreyVals[i,Fibonacci[i],AbundSeries]], (* Maximum prey level *)
Max[PredVals[j,Fibonacci[j],AbundSeries]], (* Maximum pred level *)
Length[PreyVals[i,Fibonacci[i],AbundSeries]], (* Number of prey levels *)
Length[PredVals[j,Fibonacci[j],AbundSeries]], (* Number of pred levels *)
GeomComplex[
PreyVals[i,Fibonacci[i],AbundSeries],
PredVals[j,Fibonacci[j],AbundSeries],
Model= ModelAbb]
}],
{i, PreyMinLevels,PreyMaxLevelsVar},
{j,PredMinLevels,PredMaxLevelsVar}
],
1]
,
Type=="Fix",
Flatten[
ParallelTable[
Flatten[{
Max[PreyVals[i,Fibonacci[PreyMaxLevelsFix],AbundSeries]], (* Maximum prey level *)
Max[PredVals[j,Fibonacci[PredMaxLevelsFix],AbundSeries]], (* Maximum pred level *)
Length[PreyVals[i,Fibonacci[PreyMaxLevelsFix],AbundSeries]], (* Number of prey levels *)
Length[PredVals[j,Fibonacci[PredMaxLevelsFix],AbundSeries]], (* Number of pred levels *)
GeomComplex[
PreyVals[i,Fibonacci[PreyMaxLevelsFix],AbundSeries],
PredVals[j,Fibonacci[PredMaxLevelsFix],AbundSeries],
Model= ModelAbb]
}],
{i, PreyMinLevels,PreyMaxLevelsFix},
{j,PredMinLevels,PredMaxLevelsFix}
],
1]
]
]
varH1=GeomComp[Model="H1",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k1varH1.txt"]; Save["k1varH1.txt",varH1]
 
fixH1=GeomComp[Model="H1",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k1fixH1.txt"]; Save["k1fixH1.txt",fixH1]


varLR=GeomComp[Model="LR",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k1varLR.txt"]; Save["k1varLR.txt",varLR]
fixLR=GeomComp[Model="LR",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k1fixLR.txt"]; Save["k1fixLR.txt",fixLR]


varBWL1=GeomComp[Model="BWL1",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k1varBWL1.txt"]; Save["k1varBWL1.txt",varBWL1]
 
fixBWL1=GeomComp[Model="BWL1",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k1fixBWL1.txt"]; Save["k1fixBWL1.txt",fixBWL1]


varH2=GeomComp[Model="H2",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varH2.txt"]; Save["k2varH2.txt",varH2]
fixH2=GeomComp[Model="H2",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixH2.txt"]; Save["k2fixH2.txt",fixH2]


varMM=GeomComp[Model="MM",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varMM.txt"]; Save["k2varMM.txt",varMM]
fixMM=GeomComp[Model="MM",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixMM.txt"]; Save["k2fixMM.txt",fixMM]


varHV=GeomComp[Model="HV",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varHV.txt"]; Save["k2varHV.txt",varHV]
fixHV=GeomComp[Model="HV",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixHV.txt"]; Save["k2fixHV.txt",fixHV]


varR=GeomComp[Model="R",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varR.txt"]; Save["k2varR.txt",varR]
fixR=GeomComp[Model="R",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixR.txt"]; Save["k2fixR.txt",fixR]


varAG=GeomComp[Model="AG",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varAG.txt"]; Save["k2varAG.txt",varAG]
fixAG=GeomComp[Model="AG",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixAG.txt"]; Save["k2fixAG.txt",fixAG]


varGI=GeomComp[Model="GI",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varGI.txt"]; Save["k2varGI.txt",varGI]
fixGI=GeomComp[Model="GI",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixGI.txt"]; Save["k2fixGI.txt",fixGI]


varGIA=GeomComp[Model="GIA",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varGIA.txt"]; Save["k2varGIA.txt",varGIA]
fixGIA=GeomComp[Model="GIA",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixGIA.txt"]; Save["k2fixGIA.txt",fixGIA]


varGB=GeomComp[Model="GB",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varGB.txt"]; Save["k2varGB.txt",varGB]
fixGB=GeomComp[Model="GB",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixGB.txt"]; Save["k2fixGB.txt",fixGB]


varHT=GeomComp[Model="HT",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varHT.txt"]; 
Save["k2varHT.txt",varHT]
fixHT=GeomComp[Model="HT",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixHT.txt"]; Save["k2fixHT.txt",fixHT]

varHTb=GeomComp[Model="HTb",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varHTb.txt"]; 
Save["k2varHTb.txt",varHTb]
fixHTb=GeomComp[Model="HTb",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixHTb.txt"]; Save["k2fixHTb.txt",fixHTb]


varH3=GeomComp[Model="H3",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varH3.txt"]; Save["k2varH3.txt",varH3]
fixH3=GeomComp[Model="H3",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixH3.txt"]; Save["k2fixH3.txt",fixH3]


varAGK=GeomComp[Model="AGK",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varAGK.txt"]; Save["k2varAGK.txt",varAGK]
fixAGK=GeomComp[Model="AGK",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixAGK.txt"]; Save["k2fixAGK.txt",fixAGK]


varA1=GeomComp[Model="A1",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varA1.txt"]; Save["k2varA1.txt",varA1]
fixA1=GeomComp[Model="A1",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixA1.txt"]; Save["k2fixA1.txt",fixA1]


varA3=GeomComp[Model="A3",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varA3.txt"]; Save["k2varA3.txt",varA3]
fixA3=GeomComp[Model="A3",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixA3.txt"]; Save["k2fixA3.txt",fixA3]


varSH=GeomComp[Model="SH",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varSH.txt"]; Save["k2varSH.txt",varSH]
fixSH=GeomComp[Model="SH",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixSH.txt"]; Save["k2fixSH.txt",fixSH]


varSHb=GeomComp[Model="SHb",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k2varSHb.txt"]; Save["k2varSHb.txt",varSHb]
fixSHb=GeomComp[Model="SHb",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k2fixSHb.txt"]; Save["k2fixSHb.txt",fixSHb]


varBD=GeomComp[Model="BD",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varBD.txt"]; Save["k3varBD.txt",varBD]
fixBD=GeomComp[Model="BD",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixBD.txt"]; Save["k3fixBD.txt",fixBD]


varCM=GeomComp[Model="CM",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varCM.txt"]; Save["k3varCM.txt",varCM]
fixCM=GeomComp[Model="CM",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixCM.txt"]; Save["k3fixCM.txt",fixCM]


varAA=GeomComp[Model="AA",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varAA.txt"]; Save["k3varAA.txt",varAA]
fixAA=GeomComp[Model="AA",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixAA.txt"]; Save["k3fixAA.txt",fixAA]


varBWL2=GeomComp[Model="BWL2",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varBWL2.txt"]; Save["k3varBWL2.txt",varBWL2]
fixBWL2=GeomComp[Model="BWL2",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixBWL2.txt"]; Save["k3fixBWL2.txt",fixBWL2]


varH3R=GeomComp[Model="H3R",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varH3R.txt"]; Save["k3varH3R.txt",varH3R]
fixH3R=GeomComp[Model="H3R",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixH3R.txt"]; Save["k3fixH3R.txt",fixH3R]


varA2=GeomComp[Model="A2",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varA2.txt"]; Save["k3varA2.txt",varA2]
fixA2=GeomComp[Model="A2",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixA2.txt"]; Save["k3fixA2.txt",fixA2]


varHLB=GeomComp[Model="HLB",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varHLB.txt"]; Save["k3varHLB.txt",varHLB]
fixHLB=GeomComp[Model="HLB",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixHLB.txt"]; Save["k3fixHLB.txt",fixHLB]


varHLBb=GeomComp[Model="HLBb",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varHLBb.txt"]; Save["k3varHLBb.txt",varHLBb]
fixHLBb=GeomComp[Model="HLBb",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixHLBb.txt"]; Save["k3fixHLBb.txt",fixHLBb]


varMH=GeomComp[Model="MH",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varMH.txt"]; Save["k3varMH.txt",varMH]
fixMH=GeomComp[Model="MH",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixMH.txt"]; Save["k3fixMH.txt",fixMH]


varMHb=GeomComp[Model="MHb",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varMHb.txt"]; Save["k3varMHb.txt",varMHb]
fixMHb=GeomComp[Model="MHb",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixMHb.txt"]; Save["k3fixMHb.txt",fixMHb]
DeleteFile::fdnfnd


varMHc=GeomComp[Model="MHc",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varMHc.txt"]; Save["k3varMHc.txt",varMHc]
DeleteFile::fdnfnd
fixMHc=GeomComp[Model="MHc",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixMHc.txt"]; Save["k3fixMHc.txt",fixMHc]
DeleteFile::fdnfnd


varT=GeomComp[Model="To",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varT.txt"]; Save["k3varT.txt",varT]
DeleteFile::fdnfnd
fixT=GeomComp[Model="To",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixT.txt"]; Save["k3fixT.txt",fixT]
DeleteFile::fdnfnd


varFHM=GeomComp[Model="FHM",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varFHM.txt"]; Save["k3varFHM.txt",varFHM]
DeleteFile::fdnfnd
fixFHM=GeomComp[Model="FHM",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixFHM.txt"]; Save["k3fixFHM.txt",fixFHM]
DeleteFile::fdnfnd


varW=GeomComp[Model="W",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varW.txt"]; Save["k3varW.txt",varW]
fixW=GeomComp[Model="W",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixW.txt"]; Save["k3fixW.txt",fixW]


varTTA=GeomComp[Model="TTA",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varTTA.txt"]; Save["k3varTTA.txt",varTTA]
fixTTA=GeomComp[Model="TTA",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixTTA.txt"]; Save["k3fixTTA.txt",fixTTA]


varSBB=GeomComp[Model="SBB",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varSBB.txt"]; Save["k3varSBB.txt",varSBB]
fixSBB=GeomComp[Model="SBB",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixSBB.txt"]; Save["k3fixSBB.txt",fixSBB]


varSSS=GeomComp[Model="SSS",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varSSS.txt"]; 
Save["k3varSSS.txt",varSSS]
fixSSS=GeomComp[Model="SSS",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixSSS.txt"]; 
Save["k3fixSSS.txt",fixSSS]


varS3=GeomComp[Model="S3",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varS3.txt"]; 
Save["k3varS3.txt",varS3]
fixS3=GeomComp[Model="S3",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixS3.txt"]; 
Save["k3fixS3.txt",fixS3]


varS3b=GeomComp[Model="S3b",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k3varS3b.txt"]; 
Save["k3varS3b.txt",varS3b]
DeleteFile::fdnfnd
fixS3b=GeomComp[Model="S3b",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k3fixS3b.txt"]; 
Save["k3fixS3b.txt",fixS3b]
DeleteFile::fdnfnd


varBDOR=GeomComp[Model="BDOR",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k4varBDOR.txt"]; Save["k4varBDOR.txt",varBDOR]
fixBDOR=GeomComp[Model="BDOR",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k4fixBDOR.txt"]; Save["k4fixBDOR.txt",fixBDOR]


varCMOR=GeomComp[Model="CMOR",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k4varCMOR.txt"]; Save["k4varCMOR.txt",varCMOR]
fixCMOR=GeomComp[Model="CMOR",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k4fixCMOR.txt"]; Save["k4fixCMOR.txt",fixCMOR]


varAAOR=GeomComp[Model="AAOR",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k4varAAOR.txt"]; Save["k4varAAOR.txt",varAAOR]
fixAAOR=GeomComp[Model="AAOR",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k4fixAAOR.txt"]; Save["k4fixAAOR.txt",fixAAOR]


varSN1=GeomComp[Model="SN1",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k4varSN1.txt"]; 
Save["k4varSN1.txt",varSN1]
$Aborted
DeleteFile::fdnfnd
fixSN1=GeomComp[Model="SN1",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k4fixSN1.txt"]; 
Save["k4fixSN1.txt",fixSN1]


varSN2=GeomComp[Model="SN2",Type="Var",AbundSeries=AbundSeries];
DeleteFile["k4varSN2.txt"]; 
Save["k4varSN2.txt",varSN2]
fixSN2=GeomComp[Model="SN2",Type="Fix",AbundSeries=AbundSeries];
DeleteFile["k4fixSN2.txt"]; 
Save["k4fixSN2.txt",fixSN2]
