(* ::Package:: *)

(***********************************************************
*				Risch-Norman-Bronstein Algorithm
*  Written by Sam Blake, 2007. 
*  References: 
*      Bronstein M, Symbolic Integration 1, Springer, 2005
*      Bronstein M, PMINT, INRIA, 2004 - 2005                                        
************************************************************)

(***********************************************************
*
* NOTE: IF YOU ARE RUNNING THIS PROGRAM IN VERSION 5 THEN
* COMMENT OUT THE Quiet[] AROUND Solve[] IN TryIntegral.
*
************************************************************)

BeginPackage["Pmint`"]

Pmint::usage="The poor man's integrator -- a \
Risch-Norman-Bronstein parallel integration heuristic.";

Begin["Private`"]

(* Parallel Integration Heuristic -- The Poor Mans Integrator *)
Pmint[f_,x_]:=Module[
{ff,tower,dtower,Dtower,li,lin,lout,q,L,thetas,dx,ls,fint,lc},
	ff=InternalRepresentation[f,x];
	tower=indets[ff,x];
	dtower=indets[D[ff,x],x];
	tower=Union[Select[Join[tower,dtower],!SameQ[D[#,x],0]&]];
	lout=Map[th[#]->tower[[#]]&,Range[Length[tower]]];
	lin=Map[tower[[#]]->th[#]&,Range[Length[tower]]];
	dtower=Map[D[#,x]&,tower];
	Dtower=Map[Cancel[dtower[[#]]//.lin]&,Range[Length[dtower]]];
	q=PolynomialLCM@@Map[Denominator[Cancel[Together[#]]]&,Dtower];
	L=Map[Cancel[q #]&,Dtower];
	thetas=Table[th[i],{i,1,Length[tower]}];
	ls=Flatten[Map[GetSpecials[#,lin]&,tower],1];
	fint=PmIntegrate[ff//.lin,{thetas,L/q},q,thetas,ls]//.lout;
	lc=Join[Cases[fint,A[_],{1,Infinity}],Cases[fint,B[_],{1,Infinity}]];
	fint=fint/.(#->0&/@lc);(* arbitrary constants => 0 *)
	fint/.{rischTan->Tan,rischLog->Log,rischExp->Exp,
		rischTanh->Tanh,rischErf->Erf,rischBesselJ->BesselJ}//Simplify
]

(* Convert trig functions to rischTan's (Note: we use rischTan
instead of Tan because 1/Tan is automatically converted to
Cot.), also convert Log and Exp into internal form so expressions
like Exp[x Log[x]] is not converted to x^x *)
InternalRepresentation[f_,x_]:=Module[{rules},
rules={Sin[T_]:>(2 rischTan[T/2])/(1 + rischTan[T/2]^2),
		Cos[T_]:>(1 - rischTan[T/2]^2)/(1+rischTan[T/2]^2),
		Csc[T_]:>(1 + rischTan[T/2]^2)/(2 rischTan[T/2]),
		Sec[T_]:>(1 + rischTan[T/2]^2)/(1-rischTan[T/2]^2),
		Tan[T_]:>rischTan[T],Cot[T_]:>1/rischTan[T],
		Exp[T_]:>rischExp[T],Log[T_]:>rischLog[T],
		a_^b_:>rischExp[b rischLog[a]]/;!FreeQ[b,x],
		Tanh[T_]:>rischTanh[T],Coth[T_]:>1/rischTanh[T],
		Sinh[T_]:>(2 rischTanh[T/2])/(1-rischTanh[T/2]^2),
		Cosh[T_]:>(rischTanh[T/2]^2+1)/(1-rischTanh[T/2]^2),
		Csch[T_]:>(1-rischTanh[T/2]^2)/(2 rischTanh[T/2]),
		Sech[T_]:>(1-rischTanh[T/2]^2)/(rischTanh[T/2]^2+1),
		Erf[T_]:>rischErf[T],BesselJ[T1_,T2_]:>rischBesselJ[T1,T2]};
FixedPoint[#//.rules&,f,20]//Cancel
]

(* find all variables/parameters in an expression *)
PureVariables[v_] := Select[Variables[ Level[v, {-1} ] ],
						Length[Attributes[#]]==0&];

(* An experimental implementation of Maple's indets function *)
indets[f_,var_]:=Module[{funs,powers,multargs},
	funs=Cases[f,g_[_],{0,Infinity}];
	multargs=Cases[f,h_[_,_]/;h=!=Power&&h=!=Plus&&h=!=Times,{0,Infinity}];
	powers=Cases[f,a_^h_/;!FreeQ[h,var],{0,Infinity}];
	Union[{var},powers,funs,multargs]
]

(* define the derivation of internal functions *)
Unprotect[D];
D[rischTan[T_],x_]:=D[T,x](1+rischTan[T]^2)
Derivative[1][rischTan][T_]:=(1+rischTan[T]^2)
D[rischLog[T_],x_]:=D[T,x]/T
Derivative[1][rischLog][T_]:=D[T,x]/T
D[rischExp[T_],x_]:=D[T,x]rischExp[T]
Derivative[1][rischExp][T_]:=rischExp[T]
D[rischTanh[T_],x_]:=D[T,x](1-rischTanh[T]^2)
Derivative[1][rischTanh][T_]:=(1-rischTanh[T]^2)
D[rischErf[T_],x_]:=(2/Sqrt[Pi])rischExp[-T^2]D[T,x]
Derivative[1][rischErf][T_]:=(2/Sqrt[Pi])rischExp[-T^2]
Protect[D];

(***** Total Derivation *****)
TotalDerivation[fun_,theta_,Dtower_]:=Module[{d=Thread[{Dtower,theta}]},
(Plus@@Map[First[#1] D[fun,Last[#1]]&,d])/.{E^a_:>rischExp[a],Log[a_]:>rischLog[a]}
]

(***** thetas *****)
th[i_]:=\[Theta][i]

(**** Primitive Polynomial ****)
primitive[p_,var_]:=If[
		FreeQ[p,var]||!FreeQ[Denominator[p],var],
		p,
		Collect[p/PolynomialGCD@@CoefficientList[p,var],var]
	]

(***** Splitting Factorisation *****)
SplitFactor[p_,theta_,Dtower_]:=Module[{si,x,q,c,hn,hs,S,qn,qs},
	If[And@@(FreeQ[p,#]&/@theta),Return[{1,p}]];
	x=Last[theta]; q=primitive[p,x]; c=Cancel[p/q];
	{hn,hs}=SplitFactor[c,theta,Dtower];
	S=Cancel[
		PolynomialGCD[q,TotalDerivation[q,theta,Dtower]]/
		PolynomialGCD[q,D[q,Last[theta]]]
	];
	If[Exponent[S,Last[theta]]==0,Return[{Expand[hn p],hs}]];
	{qn,qs}=SplitFactor[Cancel[q/S],theta,Dtower];
	{Expand[hn qn],Expand[S hs qs]}
]

(****** Deflation ******)
Deflation[p_,theta_]:=Module[{x,q,c},
	If[And@@(FreeQ[p,#]&/@theta),Return[p]];
	x=Last[theta]; q=primitive[p,x]; c=Cancel[p/q];
	PolynomialGCD[q,D[q,x]]*Deflation[c,theta]
]

(***** Enumerate Monomials *****)
EnumerateMonomials[vars_,d_]:=Module[{s},
	If[SameQ[Length[vars],0],Return[{1}]];
	s=EnumerateMonomials[Most[vars],d];
	Union[Flatten[{s,Table[Last[vars]^i EnumerateMonomials[vars,d-i],{i,1,d}]}]]
]

(***** myfactors  *****)
MyFactors[f_,ext_]:=Module[{result},
	If[SameQ[ext,I],
		result=FactorList[f,Extension->I],
		result=FactorList[f,Extension->Automatic]
	];
	If[SameQ[First[result],{1,1}],First/@Rest[result],result]
]

(***** Get Specials *****)
GetSpecials[f_,sb_]:=
Which[
	Head[f]===rischTan,
		{{1+(f/.sb)^2,False}},
	Head[f]===rischTanh,
		{{1+f/.sb,False},{1-f/.sb,False}},
	Head[f]===ProductLog,
		{{f/.sb,True}},
	True,
		{}
]

(***** PmIntegrate *****)
PmIntegrate[f_,d_,q_,vars_,ls_]:=Module[
	{fac,s,ff,df,facd,cden,deg,monomials,cand,lunk,sol},
	fac=SplitFactor[q,First[d],Last[d]];
	s=First[fac];
	Scan[If[Last[#],s=s First[#]]&,ls];
	ff=Cancel[Together[f]];df=Denominator[Together[f]];
	facd=SplitFactor[df,First[d],Last[d]];
	cden=s First[facd] Deflation[Last[facd],d];
	deg=1+degree[s]+Max[degree[Numerator[ff]],degree[Denominator[ff]]];
	monomials=EnumerateMonomials[vars,deg];
	cand=Sum[A[i] monomials[[i]],{i,1,Length[monomials]}]/cden;
	lunk=Table[A[i],{i,1,Length[monomials]}];
	sol=TryIntegral[f,d,q,vars,cand,lunk,First[facd],Last[facd],First[fac],ls,0];
	If[SameQ[sol,$Failed],
		sol=TryIntegral[f,d,q,vars,cand,lunk,First[facd],Last[facd],First[fac],ls,I]
	];
	If[SameQ[sol,$Failed],$Failed,sol]
]

(***** Degree *****)
degree[p_]:=Module[{vars,t},
	(* total degree, see Algebra, Lang p.118 *)
	vars=Join[PureVariables[p],Cases[p,A[_],{0,Infinity}],
		Cases[p,B[_],{0,Infinity}],Cases[p,\[Theta][_],{0,Infinity}]];
	Exponent[p//.(#->t&/@vars), t]
]

(***** Try Integral *****)
TryIntegral[f_,d_,q_,vars_,cand_,lunk_,L1_,L2_,L3_,ls_,K_]:=Module[
	{candlog,candidate,Dcandidate,numer,rhs,coefflst,sol},
	candlog=Union[Flatten[{MyFactors[L1,K],MyFactors[L2,K],MyFactors[L3,K],First/@ls}]];
	candidate=cand+Sum[B[i] rischLog[ candlog[[i]] ],{i,1,Length[candlog]}];
	Dcandidate=TotalDerivation[cand,First[d],Last[d]]+
		Sum[(B[i] TotalDerivation[candlog[[i]],First[d],Last[d]])/candlog[[i]],
		{i,1,Length[candlog]}];
	numer=Numerator[Cancel[Together[f-Dcandidate]]];
	rhs=Union[lunk,Table[B[i],{i,1,Length[candlog]}]];
	coefflst=Map[#==0&,Select[CoefficientArrays[numer,vars]//Flatten,!SameQ[#,0]&]];
	sol=Quiet[Solve[coefflst,rhs]];
	If[SameQ[sol,{}]&&FreeQ[sol,Solve],$Failed,candidate//.Flatten[sol]]
]

End[]
EndPackage[]
