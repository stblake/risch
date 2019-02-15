(*******************************************************************************
*				Risch Algorithm for Transcendental Functions
*
*	Written by Sam Blake in 2007
*
*	References: 
*			*	Symbolic Integration 1, Manuel Bronstein.
*
*			*	Algorithms for Computer Algebra, Geddes et al.
*
*			*	Indefinite and Definite Integration, Kelly Roach, 
*					1992 Mathematica Conference.
*
*			*	Fast Reduction of the Risch Differential Equation,
*					Manuel Bronstein, Journal of Symbolic Computation.
*
*			*	The Problem of Integration in Finite Terms, Robert Risch,				
*					Transactions of the American Mathematical Society.
*
*			*   The Risch Differential Equation Problem, J. H. Davenport,
*					SIAM, Vol. 15, No. 4, November 1986.
*
*			*	Simplification of Real Elementary Functions, Manuel Bronstein,
*					IBM Research Division, T. J. Watson Research Center,
*					Yorktown Heights, NY 10598
*
*			*	Algebraic Properties of the Elementary Functions of Analysis,
*					Robert H. Risch, American Journal of Mathematics, Vol. 101,
*					No. 4, pp. 743-759.
*
*			*	Algebraic Factoring and Rational Function Integration, 
*					B. M. Trager, ACM Symposium on Symbolic and Algebraic 
*					Computation, 1976,
*
*			*	Symbolic Integration towards Practicle Algorithms, Manuel Bronstein,
*					IBM Research Division, T. J. Watson Research Center,
*					Yorktown Heights, NY 10598 			
*
*******************************************************************************)

(* BeginPackage["Risch`"]; *)

<<RischUtilities.m;

Risch::usage = "Risch[f,x] uses the Risch/Bronstein algorithm to find the \
indefinite integral of f wrt x. At present we require f to be a rational or \
transcendental function.";

(* Begin["`Private`"] *)

(*******************************
*
* Main Call to Risch Algorithm
*
********************************)
Risch[0, x_]:= 0;
Risch[expr_, x_]:= expr x /; FreeQ[expr, x];

Risch[f_, x_]:= Module[
	{integrand, res, X, internal, theta, tower, Dtower, solution, result},
	Info["Enter transcendental Risch integration algorithm"];
  	(* External call to the Risch integration algorithm *)
  	RischTrace[Risch, {f, x}, "In"];
  	(* Try look-up for some integrals which we don't handle too well,
  	specifically trig integrals and some integrals with symbolic parameters *)
  	res = RischTable[f, x];
  	If[FreeQ[res, RischTable], Return[res]];
  	(* Convert the input to internal form, from here on Log => rischLog and
  	Exp => rischExp *)
  	{integrand, X} = InputConvert[f, x];
  	(* all parameters in the integrand are assumed to be positive *)
	RischParams[integrand, X];	
  	(* determine the structure of integrand *)
  	{internal, theta, tower, Dtower, {}} = RischStructure[integrand, X];
  	(* call internal integration routine *)
  	solution = RischInternal[internal, theta, tower, Dtower];
  	If[Head[solution]===List, solution = First[solution]];
  	(* is soluton elementary? *)
  	If[SameQ[solution, $Failed], Return[ HoldForm[Risch[f, x]] ]];
  	(* convert to external form *)
  	result = OutputConvert[f, solution, theta, tower, x];
  	(* Clear assumptions on parameters *)
  	ClearAll /@ PureVariables[integrand];
  	RischTrace[Risch, result, "Out"];
  	result
];

(* special call for trig rational functions *)
Risch[f_, x_]:= Module[{arg, dx, res},
	Info["Use Euler substitution on trig rational."];
   	arg = Cases[f, #[arg_. x] :> arg, {0, Infinity}] & /@ {Sin, Cos, Tan, Cot, Sec, Csc};
   	arg = First @ Union @ Flatten @ arg;

   	res = (f*dx) //. {Tan[arg x] -> -((2 Risch`sub)/(-1 + Risch`sub^2)),
   	  Sin[arg x] -> (2*Risch`sub)/(Risch`sub^2 + 1), 
      Cos[arg x] -> (1 - Risch`sub^2)/(1 + Risch`sub^2), 
      Tan[arg x] -> (-2 Risch`sub)/(-1 + Risch`sub^2), 
      Csc[arg x] -> (1 + Risch`sub^2)/(2 Risch`sub), 
      Sec[arg x] -> (1 + Risch`sub^2)/(1 - Risch`sub^2), 
      Cot[arg x] -> (-1 + Risch`sub^2)/(-2 Risch`sub), 
      dx -> 2/(arg (1 + Risch`sub^2))};
	
	Info["Integrand becomes ", res /. Risch`sub -> "t"];
   	ReplaceAll[Risch[Cancel[res], Risch`sub], Risch`sub -> Tan[arg x/2]]
] /; TrigRationalQ[f, x];

(*special call for hyperbolic rational functions*)
Risch[f_, x_]:= Module[{arg, dx, res},
	Info["Use Euler substitution on hyperbolic rational."];
    arg = Cases[f, #[arg_. x] :> arg, {0, Infinity}] & /@ {Sinh, Cosh, Tanh, Coth, Csch, Sech};
    arg = First@Union@Flatten@arg;
    
    res = (f*dx) /. {Tanh[arg x] -> (2 Risch`sub)/(1 + Risch`sub^2),
    	    Sinh[arg x] -> (2*Risch`sub)/(1 - Risch`sub^2),
       		Cosh[arg x] -> (1 + Risch`sub^2)/(1 - Risch`sub^2),
       		Tanh[arg x] -> (2 Risch`sub)/(1 + Risch`sub^2),
       		Csch[arg x] -> (1 - Risch`sub^2)/(2*Risch`sub),
       		Sech[arg x] -> (1 - Risch`sub^2)/(1 + Risch`sub^2),
       		Coth[arg x] -> (1 + Risch`sub^2)/(2*Risch`sub),
       		dx -> 2/(arg (1 - Risch`sub^2))};
    
    Info["Integrand becomes ", res /. Risch`sub -> "t"];   		
    ReplaceAll[Risch[Cancel[res], Risch`sub], Risch`sub -> Tanh[arg x/2]]
] /; HyperbolicRationalQ[f, x];

(**********************************
*
* Internal call to Risch algorithm
*
**********************************)
Options[RischInternal]:= {"RecursiveCall" -> False, "ExtendThetas" -> True};

RischInternal[0, intheta_, intower_, inDtower_, OptionsPattern[]]:= {0, intheta, intower, inDtower};
  
RischInternal[integrand_, itheta_, itower_, iDtower_, OptionsPattern[]]:= Module[
	{recursive,extendtheta, theta, tower, Dtower,
	fp,fs,fn,rationalsoln,simplePart,reducedPart,
	polyPart,logPart,polysoln,logsoln,rep,res},
	
	(* Main Algorithm *)
	RischTrace[RischInternal, {integrand, itheta, itower, iDtower}, "In"];
	recursive = OptionValue["RecursiveCall"];
	extendtheta = OptionValue["ExtendThetas"];
	If[recursive,
		{theta,tower,Dtower} = UpdateExtensionField[integrand, itheta, itower, iDtower],
		{theta,tower,Dtower} = {itheta, itower, iDtower}
	];
	(* Canonical representation *)
	{fp, fs, fn} = CanonicalRepresentation[integrand, theta, tower, Dtower];
	(* rational part *)
	{rationalsoln, simplePart, reducedPart} = HermiteReduction[fn, theta, Dtower];
	polyPart = Simplify[fp + fs];
	logPart = Together[simplePart + reducedPart];
	(* polynomial part *)
	polysoln = RischPolynomial[polyPart, theta, tower, Dtower, extendtheta];
	If[SameQ[polysoln, $Failed], Return[$Failed]];
	(* logarithmic part *)
	If[logPart =!= 0,
		logsoln = PureLogPart[logPart, theta, tower, Dtower, extendtheta],
		logsoln = 0
	];
	If[SameQ[logsoln, $Failed], Return[$Failed] ];
	res = rationalsoln + polysoln + logsoln;
	RischTrace[RischInternal, res, "Out"];
	If[recursive,
		rep = Thread[itower -> itheta];
		{res //. rep, theta, tower, Dtower},
		res
	]
];

(*******************************************
*
* Integration of polynomials
*
********************************************)
RischPolynomial[polyPart_, theta_, tower_, Dtower_, extendtheta_]:= Module[
  	{b, res, out},
  	(* Integration of transcendental polynomials *)
  	RischTrace[RischPolynomial, polyPart, "In"];
  	Info["Integrating the polynomial ", polyPart];
  	If[Apply[And, FreeQ[polyPart, #]& /@ theta], Return[polyPart*First[theta]] ];
  	Which[
   		SameQ[Head[Last[tower]], rischLog], 
   			out = RischLogarithmicPolynomial[polyPart, theta, tower, Dtower, extendtheta];
   			{res, b} = If[out === $Failed, {$Failed, False}, out];
   			If[Not[b],
    			Message[RischLogarithmicPolynomial::warning];
    			res = $Failed
    		],
   		SameQ[Head[Last[tower]], rischExp],
   			res = RischExponentialPolynomial[polyPart, theta, tower, Dtower, extendtheta],
   		SameQ[Length[theta], 1],
   			res = RischBasePolynomial[polyPart // Together, theta, tower, Dtower, extendtheta],
   		True,
   		res = $Failed
   	];
   	Info["The polynomial part is ", res];
  	RischTrace[RischPolynomial, res, "Out"];
  	res
];

RischBasePolynomial[p_, theta_, tower_, Dtower_, extendtheta_]:= Module[
{x = First[theta], n, d, poly, rat, res},
	RischTrace[RischBasePolynomial,{p, theta, tower, Dtower, extendtheta}, "In"];
	{n,d} = PolynomialQuotientRemainder[Numerator[p],Denominator[p],x];
	poly = rischpoly[n, x];
	rat = First[ RischInternal[d, theta, tower, Dtower, {"RecursiveCall" -> True, "ExtendThetas" -> extendtheta}] ];
	res = poly + rat;
	RischTrace[RischBasePolynomial, res, "Out"];
	res
];

rischpoly[0, x_] := 0;
rischpoly[a_: 1, x_] := a x /; FreeQ[a, x];
rischpoly[a_. x_^n_., x_] := a x^(n + 1)/(n + 1) /; n =!= -1 && FreeQ[{a, n}, x];
rischpoly[a_ + b_, x_] := rischpoly[a, x] + rischpoly[b, x];
rischpoly[a_./x_, x_] := a rischLog[x] /; FreeQ[a, x];

(****************************************
*
* Integration of algebraic functions
*
****************************************)
RischAlgebraic[integrand_, x_] := Module[{linearAlgebraic, quadraticAlgebraic},
  	(* Work in progress *)
  	Print["Integration of algebraic functions are not yet implemented!"];
  	Return[$Failed]
];

(****************************************
*
* Integration of special functions
*
*****************************************)
RischSpecialExtension[integrand_, x_] := Module[{},
  	(* Work to do here, mainly in structure theorem implementation *)
  	Print["Integration failed, integral may be elementary."];
  	$Failed
];

(***************************************************
*
* Hermite reduction - quadratic version
*
****************************************************)
HermiteReduction[0,theta_, Dtower_]:={0, 0, 0};

HermiteReduction[f_,theta_,Dtower_]:=Module[
	{fp, fs, fn, a, d, dsqf, dlist, dseq, g = 0, v, u, b, c, q, r, result},
	RischTrace[HermiteReduction,{f, theta, Dtower}, "In"];
	(* Hermite Reduction - quadratic version, reference: Symbolic Integration, Bronstein p. 139 *)
	{a, d} = {Numerator[f], Denominator[f]};
	dsqf = First/@Squarefree[d,Last[theta]];
	If[Length[dsqf] === 1,
		Info["Hermite reduction yields ",
			HoldForm[Integrate[f, #1]]& [First[theta]] ];
		RischTrace[HermiteReduction,{f, theta, Dtower}, "Out"];
		Return[ {0, f, 0} ]
	];
	Do[
		If[Exponent[dsqf[[i]], Last[theta]] > 0,
			v = dsqf[[i]];
			u = Cancel[d/v^i];
			Do[
				{b, c} = ExtendedEuclidean[u TotalDerivation[v,theta,Dtower], v, -Cancel[a/j], Last[theta]];
				g = g + Cancel[b/v^j];
				a = Expand[-j c-u TotalDerivation[b, theta, Dtower]]
			,{j,i-1,1,-1}
			];
			d = u v
		]
	,{i,2,Length[dsqf]}
	];
	q = PolynomialQuotient[a,Expand[u v],Last[theta]];
	r = PolynomialRemainder[a,Expand[u v],Last[theta]];
	result = {g, Cancel[r/(u v)], Cancel[q]};
	Info["Hermite reduction yields ", 
		HoldForm[ Integrate[f, #1] ]& [First[theta]] == g + 
		HoldForm[ Integrate[#1, #2] ]& [result[[2]] + result[[3]], First[theta]] ];
	RischTrace[HermiteReduction, result, "Out"];
	result
];

(***********************************************************************
*
* Lazard-Rothstein-Trager-Rioboo algorithm
*
************************************************************************)
PureLogPart[a_ + b_, theta_, tower_, Dtower_, extend_] := 
	PureLogPart[a, theta, tower, Dtower, extend] + PureLogPart[b, theta, tower, Dtower, extend];

PureLogPart::warning = "Integral not elementary -- roots of resultant \ 
polynomial are non constant.";	

PureLogPart[f_, intheta_, intower_, inDtower_, extend_] := Module[
	{theta, tower, Dtower, d, p, res, r, R, n, s, kD, S, M, A, w, 
   	EEA, newarg, sbar, evals, remaining, naivepart, Result = 0},
  	RischTrace[PureLogPart, {f, intheta, intower, inDtower}, "In"];
  	Info["Integrate the logarithmic part with the L-R-T-R algorithm ", f];
  	(* Lazard-Rioboo-Rothstein-Trager resultant algorithm *)
  	(* reduces a simple rational function with no polynomial part to a sum
	of logarithms *)
  	(* Bronstein p. 153 *)
  	(* update the extension field if required *)
  	{theta, tower, Dtower} = UpdateExtensionField[f, intheta, intower, inDtower];
  	d = Denominator[f];
  	Which[
   		Exponent[TotalDerivation[d, theta, Dtower], Last[theta]] <= Exponent[d, Last[theta]],
   			res = SubResultant[d, Expand[Numerator[f] - rischZ TotalDerivation[d, theta, Dtower]], Last[theta]];
   			r = Cancel[Together[Resultant[d, Expand[Numerator[f] - rischZ TotalDerivation[d, theta, Dtower]], Last[theta]]]];
   			(* allow for algebraic numbers to be present *)
   			If[Cases[r, xx_. cc_^n_?(!IntegerQ[#] &), {0, Infinity}] =!= {},
    			r = Cancel[Factor[Numerator[r], Extension -> Automatic]/Factor[Denominator[r], Extension -> Automatic]]
    		],
   		True,
   			res = SubResultant[Expand[Numerator[f] - rischZ TotalDerivation[d, theta, Dtower]], d, Last[theta]];
   			r = Cancel[Together[Resultant[Expand[Numerator[f] - rischZ TotalDerivation[d, theta, Dtower]], d, Last[theta]]]
	];
   	(* allow for algebraic numbers to be present *)
   	If[Cases[r, xx_. cc_^n_?(!IntegerQ[#] &), {0, Infinity}] =!= {},
    	r = Cancel[Factor[Numerator[r], Extension -> Automatic]/Factor[Denominator[r], Extension -> Automatic]]]
   	];(* end if *)
  	kD = kappaD[r, Flatten[{theta, rischZ}], Flatten[{Dtower, 1}]];
  	{n, s} = SplitSquarefreeFactor[r, Flatten[{theta, rischZ}], Flatten[{Dtower, kD}]];
  	S = {};
  	Do[
   		If[Exponent[Part[s, i], rischZ] > 0,
     		If[i == Exponent[d, Last[theta]],
      			(* make S monic wrt Last[theta] *)
      			w = lc[Expand[d], Last[theta]];
      			EEA = ExtendedEuclidean[w, Part[s, i], 1, rischZ];
      			newarg = primitive[Cancel[Together[PolynomialRemainder[Part[EEA, 1] d, Part[s, i], rischZ]]], theta, Last[theta]];
      			AppendTo[S, newarg],(* else *)
      			Do[
       				If[Exponent[res[[m]], Last[theta]] == i,
         					M = m;
         					sbar = Part[res, m]
         			];(* end if *)
       			, {m, 2, Length[res] - 1}
       			];(* end do *)
      			A = Power @@@ Squarefree[lc[sbar, Last[theta]], Last[theta]];
      			Do[
       				sbar = sbar/(PolynomialGCD[Part[A, j], Part[s, i], rischZ, Extension -> Automatic]^j)
       			, {j, 1, Length[A]}
       			];
      			(* make S monic wrt Last[theta] *)
      			w = lc[Cancel[Together[sbar]], Last[theta]];
      			EEA = ExtendedEuclidean[w, Part[s, i], 1, rischZ];
      			sbar = primitive[Cancel[Together[PolynomialRemainder[Part[EEA, 1] sbar, Part[s, i], rischZ]]], theta, Last[theta]];
      			AppendTo[S, sbar]
      		](* end if *)
     	];(* end if *)
   	, {i, 1, Length[s]}
   	];
  	(* remove constant polynomials from RootSum expression *)
  	evals = Select[s, !PossibleZeroQ[D[#, rischZ]] &];

  	(* RootSum exrpession for result *)
  	Which[
   		Head[Last[tower]] === rischExp,
   			Do[
    				Result = Result + rischLogPartE[Part[evals, i], Part[S, i], Last[theta], Last[tower]]
    			, {i, 1, Length[evals]}
    		],
   		True(* log theta or rational *),
   			Do[
    				Result = Result + rischLogPartL[Part[evals, i], Part[S, i], Last[theta], Last[tower]]
    			, {i, 1, Length[evals]}
    		]
   	];
   	
   	If[!FreeQ[Result, Indeterminate | _DirectedInfinity],
   		Result = RischNaive[f, theta, Dtower]
   	];
   	
  	If[!FreeQ[Result, "NaiveSolution"],
  		Result = Result /. "NaiveSolution" -> 0;
   		remaining = f - TotalDerivation[Result //. {rischExp -> Exp, rischLog -> Log},theta, Dtower];
   		naivepart = RischNaive[remaining, theta, Dtower];
   		Result = (Result + naivepart) //. {Exp -> rischExp, Log -> rischLog};
   	];
  	(* Check if the integral is elementary? *)
  	If[FreeQ[Simplify[Times @@ n], Last[theta]] && FreeQ[Simplify[Times @@ n], rischZ],
   		(* integral elementary *)
   		Info["The logarithmic part is ", Result];
   		RischTrace[PureLogPart, Result, "Out"];
   		Result,
   		(* integral not elementary *)
   		Message[PureLogPart::warning];
   		RischTrace[PureLogPart, Result, "Out"];
   		$Failed
   	]
];

(*****************************************************
*
* Naive form of log part of integral
*
******************************************************)
RischNaive[int_, theta_, Dtower_] := Module[
	{expr = Together[int], numf, denf, Ddenf, z, res},
  	RischTrace[RischNaive, {int, theta, Dtower}, "In"];
  	(* return naive result *)
  	Ddenf = TotalDerivation[Denominator[expr], theta, Dtower];
  	{numf, denf, Ddenf} = {Numerator[expr], Denominator[expr], Ddenf} //. Last[theta] -> z;
  	res = RootSum[Function[#1, #2], Function[#1, (#3/#4) Log[#5 - z]]] &[z, denf, numf, Ddenf, Last[theta]];
  	If[Factor[denf] =!= denf, res = ToRadicals[res]];
  	RischTrace[RischNaive, res, "Out"];
  	res
];

(*********************************************************
*
* Construction of logarithmic terms
*
**********************************************************)
(* terms for exponential extensions *)
rischLogPartE[r_, v_, theta_, tower_] := Module[
  	{extension, rfac, exparg, result, e, term, root, roots},
  	RischTrace[rischLogPartE, {r, v, theta, tower}, "In"];
  	extension = Quiet[Re[rischZ /. Solve[r == 0, rischZ]]];
  	If[And @@ (FreeQ[extension, #] & /@ {Re, Log, Root, E, Sin, Cos}) &&
  		PureVariables[extension] === {}(* may need more here... *),
   		rfac = TimeConstrained[
     			Power @@@ Quiet[FactorList[r, Extension -> extension]],
     			0.5,
     			Power @@@ Quiet[FactorList[r, Extension -> Automatic]]
     	],(* else *)
   		rfac = Power @@@ Quiet[FactorList[r, Extension -> Automatic]]
   	];
  	If[Or @@ (! FreeQ[rfac, #] & /@ {Sin, Cos, Tan, Pi, Root, RootSum}) || ! FreeQ[rfac, (-1)^n_Rational],
   		rfac = Power @@@ Quiet[FactorList[r, Extension -> Automatic]]
   	];
  	If[! FreeQ[rfac, Root] || ! FreeQ[rfac, RootSum],
   		rfac = {r}
   	];
  	rfac = rfac /. {rischLog -> Log, rischExp -> Exp};
  	exparg = tower /.rischExp[arg_] :> arg;
  	result = 0;
  	Do[
   		e = Exponent[rfac[[i]], rischZ];
   		Which[
    		e == 0,
    			term = 0,
    		e == 1,
    			root = First[rischZ /.Solve[rfac[[i]] == 0, rischZ]];
    			term = -root Exponent[v, theta] exparg + root rischLog[primitive[v /.rischZ :> root, theta]],
    		e == 2,
    			roots = rischZ /.Solve[rfac[[i]] == 0, rischZ];
    			term = rischQuadraticExpTerm[v, roots, exparg, theta] +
      			rischQuadraticLog[rfac[[i]], roots, v, theta],
    		e > 2,
    			term = "NaiveSolution"
    	];
   		result = result + term
   	, {i, 1, Length[rfac]}
   	];
   	
  	RischTrace[rischLogPartE, result, "Out"];
  	result
];

(* terms for rational of logarithmic extensions *)
rischLogPartL[r_, v_, theta_, tower_] := Module[
  	{rfac, extension, exparg, result, e, term, root, roots},
  	RischTrace[rischLogPartL, {r, v, theta, tower}, "In"];
  	(* construct elegant form of logarithms for LRTR *)
  	extension = TimeConstrained[ComplexExpand[Re[rischZ /. Solve[r == 0, rischZ]]], 1];
	  If[MatchQ[extension, _Solve|$Aborted], Return["NaiveSolution"]];
  	Which[
   		BiQuadraticQ[r, rischZ],
   			rfac = FactorBiQuadratic[r, rischZ],
   		Or @@ (!FreeQ[extension, #] & /@ {Root, Sin, Cos, Log, E}) || PureVariables[extension] =!= {},
   			rfac = Power @@@ Quiet[FactorList[r, Extension -> Automatic]],
   		True,
   			rfac = TimeConstrained[
     			Power @@@ Quiet[FactorList[r, Extension -> extension]],
     			0.5,
     			Power @@@ Quiet[FactorList[r, Extension -> Automatic]]
     			]
   	];
  	If[Or @@ (! FreeQ[rfac, #] & /@ {Sin, Cos, Tan, Pi, Root, Log, E}) || !FreeQ[rfac, (-1)^n_Rational],
   		rfac = Power @@@ Quiet[FactorList[r, Extension -> Automatic]]
   	];
  	If[! FreeQ[rfac, Root] || ! FreeQ[rfac, RootSum],
   		rfac = {r}
   	];
  	exparg = tower /. rischExp[arg_] :> arg;
  	result = 0;
  	Do[
   		e = Exponent[rfac[[i]], rischZ];
   		Which[
    			e == 0,
    				term = 0,
    			e == 1,
    				root = First[rischZ /. Solve[rfac[[i]] == 0, rischZ]];
    				term = root*rischLog[Simplify[primitive[v /. rischZ :> root, theta]]],
    			e == 2,
    				roots = rischZ /. Solve[rfac[[i]] == 0, rischZ];
    				term = rischQuadraticLog[rfac[[i]], roots, v, theta],
    			e > 2,
    				(* Here is it probably better to return naive term if no other
    				terms in the solution, or if there are other terms then return
    				Risch[integrand - D[partialsolution],x] *)		
    				term = "NaiveSolution"
    	];
   		result = result + term
   	, {i, 1, Length[rfac]}
   	];
   	
   	(* condition for problems caused in Risch[ (2 + Tan[x]^2)/(1 + (x + Tan[x])^2), x] *)
   	If[term === Indeterminate, result = "NaiveSolution"];
   	
  	RischTrace[rischLogPartL, result, "Out"];
  	result
];

rischQuadraticExpTerm[v_, roots_, exparg_, theta_] :=
 	Which[
  		Length[roots] == 1,
  			-First[roots] Exponent[v, theta] exparg,
  		Length[roots] == 2,
  			Expand[-First[roots] Exponent[v, theta] exparg - Last[roots] Exponent[v, theta] exparg]
];

rischQuadraticLog[r_, rts_, v_, theta_] := Module[{a, b, c, del, roots, result, S1, S2},
  	RischTrace[rischQuadraticLog, {r, rts, v, theta}, "In"];
  	(* r = a z^2 + b z + c *)
  	roots = FullSimplify /@ rts;
  	a = Coefficient[r, rischZ, 2];
  	b = Coefficient[r, rischZ, 1];
  	c = Coefficient[r, rischZ, 0];
  	del = b^2 - 4*a*c;
  	Which[
   		(* del = 0: 1 root => single log term *)
   		del === 0,
   			result = First[roots] rischLog[Simplify[primitive[v /. rischZ -> First[roots], theta]]],
   		SameQ[Sign[del], 1] || ComplexExpand[Im[del]] =!= 0,
   			(* the second condition above fixes Risch[Tan[x] Tan[x+1],x] *)
   			(* del > 0: 2 real roots => 2 log terms*)
   			result = First[roots] rischLog[Simplify[primitive[v /. rischZ -> First[roots], theta]]] +
     			Last[roots] rischLog[Simplify[primitive[v /. rischZ -> Last[roots], theta]]],
     	SameQ[Sign[del], -1],
   			(* del < 0: logs + atans *)
   			result = LogToReal[r, v, theta],
   		True,
   			result = "NaiveSolution"
   	];
  	RischTrace[rischQuadraticLog, result, "Out"];
  	result
];

(******************************************************
*
* Integration of logarithmic polynomials
*
*******************************************************)
RischLogarithmicPolynomial::warning = "Integral not elementary -- \
non-elementary recursive integration or introduction of new logarithms.";

RischLogarithmicPolynomial[p_, theta_, tower_, Dtower_, extendtheta_]:=Catch[Module[
	{P = ExpandNumeratorDenominator[p], result, iszero, remaining},
	result = IntegratePrimitivePolynomial[P, theta, tower, Dtower, extendtheta];
	If[Not@Last[result], Throw[result]];
	iszero = ExpandNumeratorDenominator @ Simplify @ Together @ Expand[P - TotalDerivation[First @ result, theta, Dtower]];
	If[iszero=!=0,
		remaining = RischInternal[iszero, theta, tower, Dtower, "ExtendThetas" -> True, "RecursiveCall" -> True];
		If[remaining===$Failed, Throw[$Failed]];
		result = First[result] + First[remaining]
	];
	{result, True}
]];

IntegratePrimitivePolynomial[0, theta_, tower_, Dtower_, extendtheta_]:= {0, True};

IntegratePrimitivePolynomial[logpoly_, theta_, tower_, Dtower_, extendtheta_]:= Module[
  	{A0, p0, infield, b, c, m, q0, q, beta, res},
  	RischTrace[IntegratePrimitivePolynomial, {logpoly, theta, tower}, "In"];
  	If[FreeQ[logpoly, Last[theta]],
   		Return[{0, True}]
   	];
  	infield = LimitedIntegrate[Simplify @ lc[logpoly, Last[theta]], theta, tower, Dtower];
  	If[infield === $Failed, Return[{0, False}], {b, c} = infield];
  	m = Exponent[logpoly, Last[theta]];
  	q0 = c Last[theta]^(m + 1)/(m + 1) + b Last[theta]^m;
  	(* we do need to use Simplify below, try Risch[Log[x] Log[2 x] Log[3 x], x] *)
  	{q, beta} = IntegratePrimitivePolynomial[
  			Simplify[Together[logpoly - TotalDerivation[q0, theta, Dtower]]], 
    		theta, tower, Dtower, extendtheta
    	];
  	res = {Expand[q + q0], beta};
  	RischTrace[IntegratePrimitivePolynomial, res, "Out"];
  	res
];

(********************************************************
*
* Limited integration - recursive integration version
*
*********************************************************)
LimitedIntegrate[expr_, theta_, tower_, Dtower_] := Module[
  	{iexpr, t = Last[theta], a, c, bool, res, result},
  	RischTrace[LimitedIntegrate, expr, "In"];
  	(* Limited integrate -- recursive integration version. *)
  	Info["Recursively integrating ", expr];
  	iexpr = RischInternal[expr, theta, tower, Dtower, "ExtendThetas" -> False, "RecursiveCall" -> True];
  	(* We use structure theorems on result. e.g. Risch[x^2 Log[1-x]^2, x] fails without! *)
  	If[iexpr === $Failed, Return[$Failed]];
  	{bool, res} = MatchLogs[First[iexpr], theta, tower, Dtower];
  	If[bool === False (* !FreeQ[res, rischLog | rischExp | ArcTan] *), 
  		Info["Recursive integration introduced new logarithms.", iexpr];
  		RischTrace[LimitedIntegrate, $Failed, "Out"];
  		Return[$Failed]
  	];
  	result = {Simplify[res - Coefficient[res, t] t], Coefficient[res, t]};
  	RischTrace[LimitedIntegrate, result, "Out"];
  	result
];

(*********************************************************
*
* Integration of exponential polynomials
*
**********************************************************)
RischExponentialPolynomial[p_, theta_, tower_, Dtower_, extendtheta_] := Catch[Module[
   	{poly = p, degMax, degMin, coeff, A0, nonthetaterm, result, rde, intA0},
   	RischTrace[RischExponentialPolynomial, {p, theta, tower, Dtower}, "In"];
   	(* Integration of exponential polynomials. Given
   
   		P = a_n Theta^n + a_ {n-1} Theta^{n-1} + ... + a_ 0
   
   	where a_ {i} are in k and Theta' = f' Theta, then differentiating gives us
   
   	P' = (a_ {n}' + n f' a_n) Theta^n + (a_ {n-1}' + (n-1) f' a_ {n-1}) Theta^{n-1} +
   			... + (a_ {1}' + f' a_ {1}) Theta + a_ {0}.
   
   	The following algorithm is based on how P acts under differentiation. *)
   	degMax = Exponent[poly, Last[theta]];
   	degMin = Exponent[poly, Last[theta], Min];
   	nonthetaterm = 0; result = 0;
   	(* solve a Risch DE for each power. *)
   	Do[
    	coeff = Coefficient[poly, Last[theta], n];
    	If[SameQ[n, 0] || SameQ[coeff, 0], Continue[]];
    	rde = RischDE[n (Last[Dtower]/Last[theta]), Cancel[coeff], theta, tower, Dtower];
    	If[SameQ[rde, $Failed],
     		RischTrace[RischExponentialPolynomial, $Failed, "Out"];
     		Throw[$Failed],
     		nonthetaterm = nonthetaterm + coeff Last[theta]^n;
     		result = result + rde*Last[theta]^n
     	]
    , {n, degMin, degMax}
   	];
   	(* Integration of the theta^0 term. *)
   	A0 = Together[Cancel[Expand[poly - nonthetaterm]]];
   	If[! SameQ[A0, 0],
    	(* new logarithms are permitted *)
    	intA0 = RischInternal[A0, theta, tower, Dtower, "ExtendThetas" -> extendtheta, "RecursiveCall" -> True];
    	If[SameQ[intA0, $Failed], Throw[$Failed]];
    	result = result + First[intA0]
    ];
   	RischTrace[RischExponentialPolynomial, result, "Out"];
   	Throw[result]
]];

(******************************************************************
*
* The Risch Differential Equation
*
*******************************************************************)
RischDE::warning = "Integral not elementary - Risch DE: y' + `1` y = `2` has no \
solution.";

RischDE[f_, g_, inTheta_, inTower_, inDtower_] := Catch[Module[
   	{theta, tower, Dtower, q, fbar, gbar, rischden, a, b, c, den, n, 
    beta, num, result},
   	RischTrace[RischDE, {f, g, inTheta, inTower, inDtower}, "In"];
   	Info["Solve the Risch DE: ", "y'" + f"y" == g];
   	(* Solve the Risch differential equation using Davenport's weak normalisation, 
   	Bronstein's fast reduction for computing the denominator and Rothstein's
   	special polynomial differential equation algorithm. *)
   	(* update the extension field *)
   	{theta, tower, Dtower} = UpdateExtensionField[{f, g}, inTheta, inTower, inDtower];
   	(* Test if f is weakly normalised wrt x, otherwise adding an appropriate 
   	logarithmic derivative to f makes it weakly normalised.  *)
   	q = WeakNormalizer[Together[f], theta, Dtower];
   	fbar = Cancel[Together[f - TotalDerivation[q, theta, Dtower]/q]];
   	gbar = Cancel[Together[q*g]];
   	(* If fbar and gbar are constant then trivial solution *)
   	Which[
    		MatchQ[gbar, 0] && And @@ (FreeQ[fbar, #] & /@ theta),
    			Throw[0],
    		And @@ (FreeQ[fbar, #] & /@ theta) && And @@ (FreeQ[gbar, #] & /@ theta),
    			Throw[g/f]
    ];
   (* Compute the denominator of the solution. *)
   rischden = RDENormalDenominator[fbar, gbar, theta, Dtower];
   If[rischden === $Failed,
    		Message[RischDE::warning, f, g];
    		RischTrace[RischDE, $Failed, "Out"];
    		Throw[$Failed],
    		{a, b, c, den} = rischden;
    		(* We need this cancellation, try Risch[Exp[1/(x^2-1)]/(x-1)^2, x] *)
    		{a, b, c} = {Cancel[a], Cancel[b], Cancel[c]};
    ];
   	(* Bound the degree of the solution's numerator. *)
   	Which[
    		Head[Last[tower]] === rischLog,
    			n = PolyDEPrimitiveCase[a, b, c, theta, tower, Dtower],
    		Head[Last[tower]] === rischExp,
    			{a, b, c, n, beta} = PolyDEExponentialCase[a, b, c, theta, tower, Dtower],
    		True,
    			n = PolyDEBaseCase[a, b, c, theta]
    ];

   	If[n < 0,
    	Message[RischDE::warning, f, g];
    	RischTrace[RischDE, $Failed, "Out"];
    	Throw[$Failed]
    ];
   	(* Solve the polynomial form of the DE *)
   	num = SPDE[a, b, c, n, theta, tower, Dtower];
   	(* return solution *)
   	Which[
    	num === $Failed, 
    		Message[RischDE::warning, f, g];
    		result = $Failed,
    	Head[Last[tower]] === rischLog,
    		result = num/(den q) // Cancel,
    	Head[Last[tower]] === rischExp,
    		result = Expand[Cancel[(num/(den*q))]]*Last[theta]^beta,
    	True,
    		result = num/(den q)
    ];
    Info["Solution to the RDE is ", result];
   	RischTrace[RischDE, result, "Out"];
   	Throw[result]
]];

(******************************************************
*
* Weak normalisation
*
*******************************************************)
WeakNormalizer[f_, theta_, Dtower_] := Module[
	{dn, ds, g, dstar, d1, Dd1, a, b , res, roots, PIR, result, Risch`z},
  	RischTrace[WeakNormalizer, {f, theta, Dtower}, "In"];
  	(* Weak normalisation, reference: Symbolic Integration 1, Bronstein p .183 *)
  	(* Given a derivation D on k[t] and f in k (t), return q in k[t] such that
  	f - Dq/q is weakly normalised with respect to t. *)
  	{dn, ds} = SplitFactor[Denominator[f], theta, Dtower];
  	g = PolynomialGCD[dn, D[dn, Last[theta]] ];
  	dstar = Cancel[dn/g];
  	d1 = Cancel[dstar/PolynomialGCD[dstar, g]];
  	Dd1 = TotalDerivation[d1, theta, Dtower];
  	{a, b} = ExtendedEuclidean[Cancel[Denominator[f]/d1], d1, Numerator[f], Last[theta]];
  	res = Resultant[a - Risch`z Dd1, d1, Last[theta]];
  	roots = Risch`z /. Solve[res == 0, Risch`z];
  	PIR = Select[roots, IntegerQ[#] && Sign[#] == 1 &];
  	result = Product[PolynomialGCD[a - PIR[[i]]*Dd1, d1]^PIR[[i]], {i, 1, Length[PIR]}];
  	RischTrace[WeakNormalizer, result, "Out"];
  	result
];

(*******************************************************
*
* Normal part of the denominator
*
********************************************************)
RDENormalDenominator[f_, g_, theta_, Dtower_] := Module[
	{dn, ds, en, es, p, num, den, h, result},
  	RischTrace[RDENormalDenominator, {f, g, theta, Dtower}, "In"];
  	(* Normal part of the denominator, reference: Symbolic Integration 1, Bronstein p .185 *)
  	(* Given a derivation D on k[t] and f,g in k (t) with f weakly normalised wrt t, return either
  	no solution, in which case the equation Dy + f*y == g has no solution in k (t), or the 
  	quadruplet (a,b,c,h) such that a,h in k[t], b,c in k<t>, 
  	and for any solution y in k (t) of Dy + f*y == g, q = y*h in k<t> satisfies a*Dq + b*q = c. *)
  	{dn, ds} = SplitFactor[Denominator[f], theta, Dtower];
  	{en, es} = SplitFactor[Denominator[g], theta, Dtower];
  	p = PolynomialGCD[dn, en];
  	num = PolynomialGCD[en, D[en, Last[theta]]];
  	den = PolynomialGCD[p, D[p, Last[theta]]];
  	h = Cancel[num/den];
  	If[PolynomialRemainder[dn*h^2, en, Last[theta]] =!= 0,
   		(* Risch DE has no solutions *)
   		result = $Failed,
   		(* return normal part of the denominator *)
   		result = {dn*h, dn*h*f - dn*TotalDerivation[h, theta, Dtower], dn*h^2*g, h}
   	];
  	RischTrace[RDENormalDenominator, result, "Out"];
  	result
];

(**********************************************************
*
* Degree bound -- base case
*
**********************************************************)
PolyDEBaseCase[A_, B_, C_, theta_] := Module[{degA, degB, degC, a, b, r, res},
  	RischTrace[PolyDEBaseCase, {A, B, C, theta}, "In"];
  	(* Given A,B,C in K[x],return n such that deg (Q)<=n and Q satisfies A Q'+B Q==C. *)
  	(* bound the degree of the solution in k[theta] *)
  	degA = Exponent[A, Last[theta]];
  	degB = Exponent[B, Last[theta]];
  	degC = Exponent[C, Last[theta]];
  	Which[
   		degA < degB + 1,
   			res = degC - degB,
   		degA > degB + 1,
   			res = Max[0, degC - degA + 1],
   		degA == degB + 1,
   			a = lc[A, Last[theta]];
   			b = lc[B, Last[theta]];
   			r = Cancel[-b/a];
   			If[IntegerQ[r],
    			res = Max[r, degC - degB],
    			res = degC - degB
    		]
   	];
  	RischTrace[PolyDEBaseCase, res, "Out"];
  	res
];

(******************************************************
*
* Degree bound -- logarithmic case
*
******************************************************)
PolyDEPrimitiveCase[A_, B_, C_, theta_, tower_, Dtower_] := Catch[Module[
   	{degA, degB, degC, a, b, int, alpha, struct, J, H, n, r},
   	RischTrace[PolyDEPrimitiveCase, {A, B, C, theta, tower, Dtower}, "In"];
   	(* Given A,B,C in k[theta], with A!=0 safisfying A Q' + B Q = C, 
   	where theta is primitive. Return Q in k[theta] satisfying the above DE. *)
   	degA = Exponent[A, Last[theta]];
   	degB = Exponent[B, Last[theta]];
   	degC = Exponent[C, Last[theta]];
   	Which[
    	degA == degB && degB != 0,
    		a = lc[A, Last[theta]];
    		b = lc[B, Last[theta]];
    		int = RischInternal[b/a, theta, tower, Dtower, "ExtendThetas" -> True, "RecursiveCall" -> True];
    	 	If[int === $Failed,
     			RischTrace[PolyDEPrimitiveCase, $Failed, "Out"];
     			Throw[$Failed]
     		];
    		struct = IsStructureExtended[rischExp[-int], theta, tower];(* simple cancellation cases *)
    		If[!First[struct],
     			alpha = Last[struct];
     			H = PolyDEPrimitiveCase[alpha*A, TotalDerivation[alpha, theta, Dtower]*A + alpha*B, C, theta, tower];
     			If[H === $Failed,
      				RischTrace[PolyDEPrimitiveCase, $Failed, "Out"];
      				Throw[$Failed]
      			];
     			RischTrace[PolyDEPrimitiveCase, alpha H, "Out"];
     			Throw[alpha*H]
     		];
    		RischTrace[PolyDEPrimitiveCase, degC - degB, "Out"];
    		Throw[degC - degB],
    	degA < degB,
    		RischTrace[PolyDEPrimitiveCase, degC - degB, "Out"];
    		Throw[degC - degB],
    	degA > degB + 1,
    		RischTrace[PolyDEPrimitiveCase, Max[0, degC - degA + 1], "Out"];
    		Throw[Max[0, degC - degA + 1]],
    	degA == degB + 1,
    		a = lc[A, Last[theta]];
    		b = lc[B, Last[theta]];
    		J = RischInternal[b/a, theta, tower, Dtower, "ExtendThetas" -> True, "RecursiveCall" -> True];
    		If[J === $Failed,
     			RischTrace[PolyDEPrimitiveCase, $Failed, "Out"];
     			Throw[$Failed],
     			J = First[J]
     		];
    		If[!FreeQ[J, Last[theta]] && FreeQ[Denominator[J], Last[theta]],
     			J = -J;
     			r = Coefficient[J, Last[theta]];
     			If[IntegerQ[r],
      				RischTrace[PolyDEPrimitiveCase, Max[r, degC - degB], "Out"];
      				Throw[Max[r, degC - degB]],
      				RischTrace[PolyDEPrimitiveCase, degC - degB, "Out"];
      				Throw[degC - degB]
      			],
     			RischTrace[PolyDEPrimitiveCase, degC - degB, "Out"];
     			Throw[degC - degB]
     		]
    	]
]];

(*****************************************************
*
* Degree bound -- exponential case
*
******************************************************)
PolyDEExponentialCase[C1_, C2_, C3_, theta_, tower_, Dtower_] := Module[
  	{A = C1, B = C2, C = C3, nb, nc, rem, n, b, m, eta, degA, degB, degC, a, H, alpha, beta, res},
  	RischTrace[PolyDEExponentialCase, {C1, C2, C3, theta, tower, Dtower}];
  	(*Given A in k[theta] aith A (0)!=0,B,C in k[theta,theta^-1],
  	where theta is exponential and A,B,C satisfy A Q'+B Q = C. 
  	Return either $Failed in which case there is no solution in k[theta],
  	or {m,b} such that m is a bound on the degree of Q and.*)
  	(*Find a lower bound on the order of 0 at Q*)
  	nb = OrderFunction[B, Last[theta], Last[theta]];
  	nc = OrderFunction[C, Last[theta], Last[theta]];
  	If[MatchQ[nb, 0],
   		rem = Remainder[-B/A, Last[theta], Last[theta]];
   		n = ParametricLogarithmicDerivative[rem, theta, tower, Dtower];
   		If[n === $Failed,
    			b = Min[0, nc],
    			b = Min[0, First[n], nc]
    	],
   		b = Min[0, nc - Min[0, nb]]
   	];
  	m = Max[0, -nb, b - nc];
  	(*Convert equation to one in k[theta]*)
  	eta = Last[tower] /. rischExp[arg_] :> arg;
  	B = (b*TotalDerivation[eta, theta, Dtower]*A + B)*Last[theta]^m;
  	A = A*Last[theta]^m;
  	C = C*Last[theta]^(m - b);
  	(*At this point A,B,C in k[theta],and if H in k[theta] satisfies 
  	A H'+B H=C,then Q=H*theta^b is a solution to the original DE*)
  	(*Find a bound on deg (H) and solve the polynomial equation*)
  	degA = Exponent[A, Last[theta]];
  	degB = Exponent[B, Last[theta]];
  	degC = Exponent[C, Last[theta]];
  	Which[
   		degA < degB,
   			m = degC - degB,
   		degA > degB,
   			m = Max[0, degC - degA],
   		degA == degB,
   			alpha = lc[A, Last[theta]];
   			beta = lc[B, Last[theta]];
   			n = ParametricLogarithmicDerivative[-beta/alpha, theta, tower, Dtower];
   			If[n === $Failed,
    				m = degC - degB,
    				m = Max[0, First[n], degC - degB]
    		]
   	];
  	res = {A, Expand[B], Expand[C], m, b};
  	RischTrace[PolyDEExponentialCase, res, "Out"];
  	res
];

(**********************************************************
*
* Rothstein's SPDE algorithm
*
**********************************************************)
SPDE[c1_, c2_, c3_, n_, theta_, tower_, Dtower_] := Catch[Module[
  	{A = c1, B = c2, C = c3, G, res1, Q, etheta, etower, H, m, 
    b, c, derivation, solution, qr, r, bc, Z, res},
   	RischTrace[SPDE, {c1, c2, c3, n, theta, tower, Dtower}, "In"];
   	(* Rothstein's special polynomial differential equation algorithm
   	for solving A Q' + B Q = C, with a degree bound n on the solution Q in 
   	k[theta] and A,B,C in k[theta] *)
   	If[C == 0,
    	RischTrace[SPDE, 0, "Out"];
    	Throw[0]
    ];
   	G = PolynomialGCD[A, B];
   	If[PolynomialRemainder[C, G, Last[theta]] =!= 0,
    	RischTrace[SPDE, $Failed, "Out"];	
    	Throw[$Failed]
    ];
   	A = Cancel[A/G];
   	B = Cancel[B/G];
   	C = Cancel[C/G];
   	Which[
    		MatchQ[B, 0],
    			res1 = RischInternal[C, theta, tower, Dtower, "ExtendThetas" -> True, "RecursiveCall" -> True];
    			If[res1 == $Failed, 
    				RischTrace[SPDE, $Failed, "Out"]; 
     				Throw[$Failed]
     			];
    			Q = First[res1];
    			If[Exponent[Q, Last[theta]] <= n,
     				RischTrace[SPDE, Q, "Out"];
     				Throw[Q],
     				RischTrace[SPDE, $Failed, "Out"];
     				Throw[$Failed]
     			],
    		Exponent[A, Last[theta]] > 0,
    			bc = Simplify/@ExtendedEuclidean[B, A, C, Last[theta]];
    			{qr, r} = PolynomialQuotientRemainder[First[bc], A, Last[theta]];
    			Z = B*qr + Last[bc];
    			If[Exponent[r, Last[theta]] > n, 
     				RischTrace[SPDE, $Failed, "Out"]; 
     				Throw[$Failed]
     			];
    			H = SPDE[A, B + TotalDerivation[A, theta, Dtower],Simplify[Z - TotalDerivation[r, theta, Dtower]],
    					n - Exponent[A, Last[theta]], theta, tower, Dtower];
      					(* I am not sure how one can avoid using Simplify here, 
      					given that we are only simplifying rational expressions 
      					it should be fairly fast... *)	
    			If[H === $Failed, 
    				RischTrace[SPDE, $Failed, "Out"]; 
     				Throw[$Failed]
     			];
    			If[Exponent[H, Last[theta]] > n,
     				RischTrace[SPDE, $Failed, "Out"];
     				Throw[$Failed] 
     			];(* may be a problem here! *)
    			Throw[Simplify[A*H + r]],
    		Exponent[A, Last[theta]] == 0 && Exponent[B, Last[theta]] > 0,
    			m = Exponent[C, Last[theta]] - Exponent[B, Last[theta]];
    			If[m < 0 || m > n, 
    				RischTrace[SPDE, $Failed, "Out"]; 
     				Throw[$Failed]
     			];
    			b = lc[B, Last[theta]];
    			c = lc[C, Last[theta]];
    			H = SPDE[A, B,Simplify[C - (c/b)*B*Last[theta]^m - A*TotalDerivation[(c/b) Last[theta]^m, theta, Dtower]],
      				m - 1, theta, tower, Dtower];
      				(* MUST use Simplify, try example in Davenport's 1986 RDE paper *)
    			If[H === $Failed, 
    				RischTrace[SPDE, $Failed, "Out"]; 
     				Throw[$Failed]
     			];
    			res = (c/b) Last[theta]^m + Simplify[H];
    			RischTrace[SPDE, res, "Out"];
    			Throw[res],
    		Exponent[A, Last[theta]] == 0 && Exponent[B, Last[theta]] == 0,
    			(* ParametricDE is only required for the exponential and non-trivial primitive cases *)
    			res = CancelPolyDE[A, B, C, n, theta, tower, Dtower];
    			RischTrace[SPDE, res, "Out"];
    			Throw[res]
    ]
]];

(**********************************************************
*
* Base case solution to polynomial DE
*
**********************************************************)
PolyDE[a_, b_, c_, x_] := Catch[Module[
   	{alpha, beta, gamma, pi, ypi, new, res},
   	(* a fast algorithm to solve a y'[x] + b y[x] = c, where a,b,c are polynomials. *)
   	(* Depending on the degrees of a,b,c we reduce the RHS of the DE until c = 0 
   	(or a=0 or b=0 in which case the solution is trivial) *)
   	RischTrace[PolyDE, {a, b, c}, "In"];
   	If[a === 0,
    	Throw[c/b]
    ];
   	If[b === 0,
    	Throw[First[RischInternal[c/a, {x}, {x}, {1}, "RecursiveCall" -> True, "ExtendThetas" -> False]]]
    ];
   	If[c === 0,
    	Throw[0]
    ];
   	{alpha, beta, gamma} = Exponent[#, x] & /@ {a, b, c};
   	Which[
    	alpha - 1 > beta,
    			pi = Max[gamma - alpha + 1, 0];
    			If[pi < 0, Throw[$Failed]];
    			If[alpha === 0,
     			ypi = lc[c, x]/lc[b, x],
     			ypi = lc[c, x]/(pi lc[a, x])
     			],
    	alpha - 1 === beta,
    			(* there are problems with this case: Try
    			 PolyDE[x^4,-x^2-2x^3,x^2+x^3,x]*)
    			pi = gamma - beta;
    			If[pi < 0 || pi lc[a, x] + lc[b, x] == 0, Throw[$Failed]];
    			ypi = lc[c, x]/(pi lc[a, x] + lc[b, x]),
    	alpha - 1 < beta,
    			pi = gamma - beta;
    			If[pi < 0, Throw[$Failed]];
    			ypi = lc[c, x]/lc[b, x]
   	];
   	new = ypi x^pi;
   	res = new + PolyDE[a, b, Expand[c - D[new, x] a - new b], x];
   	RischTrace[PolyDE, res, "Out"];
   	res
]];

(**********************************************
*
* Cancellation cases
*
***********************************************)
CancelPolyDE[A_, B_, C_, n_, theta_, tower_, Dtower_] := Catch[Module[{},
   	Which[
    	Head[Last[tower]] === rischLog,
    		Throw[CancelPolyDEPrimitiveCase[A, B, C, n, theta, tower, Dtower] ],
    	Head[Last[tower]] === rischExp,
    		Throw[ CancelPolyDEExponentialCase[A, B, C, n, theta, tower, Dtower] ],
    	Length[theta] == 1,
    		Throw[PolyDE[A, B, C, First[theta]]]
    ]
]];

(***************************************************
*
* Primitive cancellation case
*
****************************************************)
CancelPolyDEPrimitiveCase[a_, b_, C_, n_, theta_, tower_, Dtower_] := Catch[Module[
   	{int, alpha, struct, q, Q, m, c, r, H},
   	RischTrace[CancelPolyDEPrimitiveCase, {a, b, C, n, theta, tower, Dtower}, "In"];
   	(* Given a, b in k with a!=0 C in k[theta] and n in Z. Return either no 
   	solution of Q in k[theta] such that deg (Q) n and a*Q'+b*Q=C. *)
   	If[n < 0, 
    	RischTrace[CancelPolyDEPrimitiveCase, $Failed, "Out"]; 
    	Throw[$Failed]
   	];
   	If[C == 0, 
   		RischTrace[CancelPolyDEPrimitiveCase, 0, "Out"]; 
    	Throw[0]
    ];
   	int = RischInternal[b/a, theta, tower, Dtower, "ExtendThetas" -> True, "RecursiveCall" -> True];
   	If[int === $Failed,
    	RischTrace[CancelPolyDEPrimitiveCase, $Failed, "Out"];
    	Throw[$Failed]
    ];
   	struct = IsStructureExtended[rischExp[-int], Most[theta], Most[tower]];
   	If[First[struct],
    	alpha = Last[struct];
    	(*alpha not in k*)
    	RischTrace[CancelPolyDEPrimitiveCase, $Failed, "Out"];
    	Throw[$Failed],
    	q = RischInternal[C/(a*alpha), theta, tower, Dtower, "ExtendThetas" -> False, "RecursiveCall" -> True];
    	Q = Cancel[alpha*q];
    	If[q === $Failed, 
     		RischTrace[CancelPolyDEPrimitiveCase, $Failed, "Out"]; 
     		Throw[$Failed]
     	];
    	(*q not in k[theta]*)
    	If[Exponent[Q, Last[theta]] <= n,
     		RischTrace[CancelPolyDEPrimitiveCase, Q, "Out"];
     		Throw[Q],
     		RischTrace[CancelPolyDEPrimitiveCase, $Failed, "Out"];
     		Throw[$Failed]
     	]
    ];
   	m = Exponent[C, Last[theta]];
   	If[m > n, 
   		RischTrace[CancelPolyDEPrimitiveCase, $Failed, "Out"]; 
    	Throw[$Failed]
    ];
   	c = lc[C, Last[theta]];
   	(*solve rde for r in k*)
   	r = RischDE[b/a, c/a, Most[theta], Most[tower], Most[Dtower]];
   	If[r === $Failed, 
    	RischTrace[CancelPolyDEPrimitiveCase, $Failed, "Out"]; 
    	Throw[$Failed]
    ];
   	(*recursion*)
   	H = CancelPolyDE[a, b, Simplify[C - b*r*Last[theta]^m - a*TotalDerivation[r*Last[theta]^m, tower, Dtower]],
     		m - 1, theta, tower, Dtower];
   	If[H === $Failed, 
    	RischTrace[CancelPolyDEPrimitiveCase, $Failed, "Out"]; 
    	Throw[$Failed]
    ];
   	RischTrace[CancelPolyDEPrimitiveCase, r*Last[theta]^m + H, "Out"];
   	Throw[r*Last[theta]^m + H]
]];

(*********************************************************
*
* Exponential cancellation case
*
*********************************************************)
CancelPolyDEExponentialCase[a_, b_, C_, n_, theta_, tower_, Dtower_] :=Catch[Module[
   	{int, alpha, q, Q, m, c, Deta, r, H},
   	RischTrace[CancelPolyDEExponentialCase, {a, b, C, n, theta, tower, Dtower}, "In"];
   	(* Given a,b in k (a!=0), C in k[theta] and n in Z. Return either $Failed 
   	in which case the DE has no solution, or Q in k[theta] such that deg (Q)<=n 
   	and a Q' + b Q = C. *)
   	If[C == 0,
    	RischTrace[CancelPolyDEExponentialCase, 0, "In"];
    	Throw[0]
    ];
   	If[n < 0,
    	RischTrace[CancelPolyDEExponentialCase, $Failed, "In"];
    	Throw[$Failed]
    ];
   	(* write rischExp[-Risch[b/a, x]] as beta*Last[theta]^m *)
   	int = ParametricLogarithmicDerivative[-b/a, theta, tower, Dtower];
   	If[int =!= $Failed,
    	If[First[int] >= 0,
     		alpha = RischInternal[b/a, theta, tower, Dtower, "ExtendThetas" -> True, "RecursiveCall" -> True];
     		If[alpha === $Failed,
      			RischTrace[CancelPolyDEExponentialCase, $Failed, "In"];
      			Throw[$Failed]
      		];
     		alpha = Last[IsStructureExtended[rischExp[-First[alpha]], theta, tower]];
     		If[!First[alpha], Throw[$Failed]];
     		(* line above assumes result lies in tower *)
     		q = RischInternal[C/(a*alpha), theta, tower, Dtower, "ExtendThetas" -> False, "RecursiveCall" -> True];
     		If[q === $Failed,
      			RischTrace[CancelPolyDEExponentialCase, $Failed, "In"];
      			Throw[$Failed]
      		];
     		Q = alpha*q;
     		If[Exponent[Q, Last[theta]] > n,
      			RischTrace[CancelPolyDEExponentialCase, $Failed, "In"];
      			Throw[$Failed]
      		];
     		Throw[Q]
     	]
    ];
   	m = Exponent[C, Last[theta]];
   	If[m > n,
    	RischTrace[CancelPolyDEExponentialCase, $Failed, "In"];
    	Throw[$Failed]
    ];
   	c = lc[C, Last[theta]];
   	Deta = Last[Dtower]/Last[theta];
   	(* solve rde over k *)
   	r = RischDE[(b/a) + m*Deta, c/a, Most[theta], Most[tower], Most[Dtower]];
   	If[r === $Failed,
    	RischTrace[CancelPolyDEExponentialCase, $Failed, "In"];
    	Throw[$Failed]
    ];
   	(* recursion *)
   	H = CancelPolyDE[a, b, Simplify[C - c*Last[theta]^m], m - 1, theta, tower, Dtower];
   	If[H === $Failed,
    	RischTrace[CancelPolyDEExponentialCase, $Failed, "In"];
    	Throw[$Failed]
    ];
   	RischTrace[CancelPolyDEExponentialCase, r*Last[theta]^m + H, "In"];
   	Throw[r*Last[theta]^m + H]
]];

(**************************************************************
*
*
* Risch structure theorems
*
*
***************************************************************)
RischStructure[f_, x_] := Catch[Module[
	{integrand, logList, expList, algTranNums, params, 
    linExp, alphas, ptower, cptower, tower, Dtower, thetas, 
    argument, fail, ncp, testelem, reps, result},
   	(* Implementation of Risch structure theorem for log-exp functions *)
   	(*  Input: f (integrand), x (variable of integration)
   		Output: integrand, thetas, tower, derivation of tower, constant field over Q *)   
   	RischTrace[RischStructure, {f, x}, "In"];
   	integrand = PreprocessExponents[f, x];
   	integrand = StructureFast[integrand, x];
   	(* collect all the logarithms and exponentials in the integrand *)
   	{logList, expList} = StructureLogExpCollect[integrand, x];
   	(* base case? *)
   	If[SameQ[logList, {}] && SameQ[expList, {}],
    	RischTrace[RischStructure, {integrand, {x}, {x}, {1}, {}}, "Out"];
    	Throw[{integrand, {x}, {x}, {1}, {}}]
    ];
   	(* all parameters in the integrand *)
   	params = DeleteCases[PureVariables[f], x];
   	(* collect all the algebraic and transcendental numbers in the integrand *)
   	algTranNums = {}(* StructureAlgTrans[integrand,x] *);
   	(* all transcendental/algebraics over Q *)
   	alphas = Join[params, algTranNums];
   	(* define the preliminary form of the tower. *)
   	ptower = UnsortedUnion[Join[
   		{x}, 
   		Sort[expList, ByteCount[#1] <= ByteCount[#2] &], 
      	Sort[logList, ByteCount[#1] <= ByteCount[#2] &]
   	]];
   	(* make a canonical ordering of the list *)
   	cptower = StructureCanonicalRepresentation[ptower];
   	(* define the theta's, tower and the tower derivation *)
  	thetas = Join[{x}, Table[theta[n], {n, 1, Length[cptower] - 1}]];
   	reps = Thread[cptower -> thetas];
   	Dtower = StructureDerivation[cptower, thetas, x, reps];
   	(* Apply the structure theorems *)
   	result = StructureEliminate[integrand, thetas, cptower, Dtower, algTranNums, reps];
   	(* we use Cancel[] so we don't get confused on Risch[Sec[x] // TrigToExp, x] and
   	many other related integrals. SamB 12/2008 *)
   	(* In fact, Cancel[] is not sufficient, we need Simplify[] try 
   	Risch[1/(b/E^(m x) + a E^(m x)), x] *)
   	integrand = ExpandNumeratorDenominator[Simplify[First[result] //. reps]];
   	RischTrace[RischStructure, Join[{integrand}, Rest[result]], "Out"];
   	Info["Integrand is ", integrand];
   	Info["Introduce the namings ", Thread[Rest[ result[[2]] ] == Rest[ result[[3]] ]]];
   	Join[{integrand}, Rest[result]]
]];

StructureEliminate[expr_, inthetas_, intower_, inDtower_, nums_, inreps_] := Catch[Module[
   	{integrand = expr, thetas, tower, Dtower, reps = inreps, 
    testtower = intower, test, state, result, res, new, replacements},
   	RischTrace[StructureEliminate, {integrand, inthetas, intower, inDtower}, "In"];
   	(* apply Risch structure theorems to tower to remove any algebraic dependencies between 
   	the thetas and update the integrand as required *)
   	{thetas, tower, Dtower} = {inthetas[[1 ;; 2]], intower[[1 ;; 2]], inDtower[[1 ;; 2]]};
   	(* case of one transcendental extension *)
   	If[SameQ[Length[inthetas], 2],
    	RischTrace[StructureEliminate, {integrand, thetas, tower, Dtower, {}}, "Out"];
    	Throw[{integrand, thetas, tower, Dtower, {}}]
    ];
   	(* test for algebraic dependicies *)
   	Do[
    	state = False;
    	test = testtower[[n]];
    	Which[
     		SameQ[Head[test], rischLog],
     			result = LogStructure[test, thetas, tower, Dtower, nums, reps];
     			If[!SameQ[result, $Failed],
      				{state, new, thetas, tower, Dtower, nums} = result;
      				testtower = testtower //. test :> new,
      				Continue[]
      			];
     			If[state,
      				integrand = integrand //. test :> new
      			],
     		SameQ[Head[test], rischExp],
     			result = ExpStructure[test, thetas, tower, Dtower, nums, reps];
     			If[!SameQ[result, $Failed],
      				{state, new, thetas, tower, Dtower, nums} = result;
      				testtower = testtower //. test :> new,
      				Continue[]
      			];
     			If[state,
      				integrand = integrand //. test :> new
      			],
     		True,
     			RischTrace[StructureEliminate, $Failed, "Out"];
     			Throw[$Failed]
		]
    , {n, 3, Length[intower]}
    ];
    replacements = Thread[tower -> thetas];
   	res = {integrand //. replacements, thetas, tower, Dtower //. replacements, {}};
   	RischTrace[StructureEliminate, res, "Out"];
   	Throw[res]
]];

StructureCanonicalRepresentation[prelim_]:= Module[{tower = prelim},
  	(* Check that theta_i does not occur in any theta_j (1<j<i). 
  	If so then we must swap theta_i with theta_j *)
  	Do[
   		Do[
    		If[Cases[tower[[j]], tower[[i]], {0, Infinity}] =!= {},
     			tower = Swap[tower, i, j]
     		]
    	, {j, 1, i}
    	]
   	, {i, 1, Length[tower]}
   	];
  	tower
];

ConstantSystem[M_, U_, theta_, tower_, Dtower_]:= Module[{k, A, u, m, j, i, R, Rm},
  	RischTrace[ConstantSystem, {M, U, theta, tower, Dtower}, "In"];
  	(* Constant System. Reference: Symbolic Integration 1, Bronstein, p. 225 *)
  	(* Given a differential field (K,D) with constant field C, 
  	a matrix A and vector u with coefficients in K, 
  	return a a matrix B with coefficients in C and a vector V such that 
	either v has coefficients in C, in which case the solutions in C of 
	Ax=u are exactly all the solutions of Bx=v, or v has a non constant coefficient, 
	in which case Ax=u has no constant solution. *)
  	A = RowReduce[Transpose[Join[Transpose[M], {U}]]];
  	u = Last[Transpose[A]];
  	m = Length[A];
  	A = Transpose[Most[Transpose[A]]];
  	k = 1;(* this is just a recursion limit *)
  	While[!MatrixOfConstants[A, First[theta]] && k < 30, k++;
  		(* j --> minimal index of A such that the jth column of A is not constant *)
   		j = MinColNonConstIndex[A, First[theta]];
   		(* i --> any index such that a_ {i,j} not in constant field of M *)
   		i = RowNonConstIndex[A, First[theta]];
   		(* R --> ith row of A *)
   		AppendTo[A, (Map[TotalDerivation[#, theta, tower] &, A[[i]] ])/TotalDerivation[A[[i, j]], theta, tower] ];
   		AppendTo[ u, TotalDerivation[Part[u, i], theta, tower] ];
   		Do[
    			A[[s]] = A[[s]] - A[[s, j]]*Last[A];
    			u[[s]] = u[[s]] - A[[s, j]]*Last[u]
    	, {s, 1, m}
    	]
   	];
  	RischTrace[ConstantSystem, {A, u}, "Out"];
  	{A, u}
];

LogStructure[test_, inthetas_, intower_, inDtower_, innums_, reps_]:= Catch[Module[
   	{thetas = inthetas, tower = intower, Dtower = inDtower, nums = innums,
    arg, eqnrhs, exps, logs, n, eqnlhs, smallreps, sol, rhs, c, 
    Dnewtheta, newtheta, newtower, res},
   	RischTrace[LogStructure, {test, thetas, tower, Dtower, nums}, "In"];
   	(* Implementation of equation 9.8 from Bronstein. *)
   	(* With a in Kstar and t = log (a), i.e. Dt = Da/a. 
   	If (9.8) has a solution r_i in Q then it provides v in K such that 
   	Dv = Da/a, hence c = t - v in Cons_D (K (t)) and 
   	K (t) = C (c)(t_ 1,...,t_n). Otherwise, Da/a is the the derivative of an element of K,
   	so t is a monomial over K having the same constant field. *)
   	arg = test /. rischLog[a_] :> a;
   	smallreps = Thread[tower -> thetas];
   	(* rhs of equation 9.8 *)
   	eqnrhs = Cancel[TotalDerivation[arg, thetas, Dtower]/arg] //. reps;
   	(* determine equations 9.6 and 9.7 *)
   	{exps, logs} = findlogexp[tower];
  	(* lhs of equation 9.8 *)
   	{n, eqnlhs} = buildlhs[exps, logs, thetas, Dtower];
   	eqnlhs = eqnlhs //. reps;
   	(* solve lhs = rhs for the unknown Risch`r[_]'s *)
   	sol = structuresolve[eqnlhs, eqnrhs, thetas, n];
   	(* heuristic for stopping Log[a x] turning into
   		Log[a] + Log[x], when a < 0. Without this change we get the
   		following solution
   		In[111]:= Risch[Log[Log[1/x^3] + Log[x]]/(x (Log[1/x^3] + Log[x])), x]
		Out[111]= 1/2 I \[Pi] Log[-2 Log[x]] + 1/2 Log[2] Log[-2 Log[x]] - 
	 		1/4 Log[-2 Log[x]]^2 + 1/2 (-I \[Pi] - Log[2]) Log[Log[x]] *)
	(* Using DeleteCases[sol, 0] wass motivated by
		Risch[(9 E^x^9 x^9+(1/x^5)^Log[x] Log[1/x^5]-5 (1/x^5)^Log[x] Log[x])/x,x] *)
   	If[Length[DeleteCases[sol, 0]] === 1 || Cases[sol, _?Negative]=!={}, sol = $Failed];
   	(* are solution (s) rational? *)
   	If[SameQ[sol, $Failed],
    	Dtower = Join[Dtower, {Cancel[TotalDerivation[test, thetas, Dtower] //. reps]}];
    	thetas = Join[thetas, {theta[Length[thetas]]}];
    	tower = Join[tower, {test //. smallreps}];
    	res = {False, test, thetas, tower, Dtower, nums};
    	RischTrace[LogStructure, res, "Out"];
    	Throw[ res ]
    ];
   	(* solutions are rational => algebraically dependent *)
   	rhs = buildnewlogtheta[sol, tower, thetas];
   	(* determine constant of integration *)
   	c = structureconstantlog[test, rhs, thetas, tower];
   	(* determine new theta *)
   	newtheta = c + rhs;
   	newtower = tower //. test -> newtheta;
   	res = {True, newtheta, thetas, newtower, Dtower, nums};
   	RischTrace[LogStructure, res, "Out"];
   	res
]];

buildlhs[exps_, logs_, thetas_, Dtower_] := Module[{pt1, pt2, res},
  	RischTrace[buildlhs, {exps, logs, thetas, Dtower}, "In"];
  	(* log terms *)
  	pt1 = Map[Risch`r[#] TotalDerivation[logs[[#]], thetas, Dtower]/logs[[#]] &, Range[Length[logs]]];
  	(* exp terms *)
  	pt2 = Map[Risch`r[# + Length[logs]] TotalDerivation[exps[[#]], thetas, Dtower] &, Range[Length[exps]]];
  	res = {Length[#], Total[#]} & /@ {Join[pt1, pt2]} // Flatten;
  	RischTrace[buildlhs, res, "Out"];
  	res
];

buildnewlogtheta[sol_, tower_, thetas_] := Module[
  	{exps, logs, pt1, pt2, res},
  	RischTrace[buildnewtheta, {sol, tower}, "In"];
  	exps = Select[tower, SameQ[Head[#], rischExp] &];
  	logs = Select[tower, SameQ[Head[#], rischLog] &];
  	(* log terms *)
  	pt1 = Map[sol[[#]] logs[[#]] &, Range[Length[logs]]];
  	(* exp terms *)
  	pt2 = Map[sol[[# + Length[logs]]] exps[[#]] &, Range[Length[exps]]];
  	res = Total[pt1] + Total[pt2];
  	RischTrace[buildnewtheta, res, "Out"];
  	res
];

ExpStructure[test_, inthetas_, intower_, inDtower_, nums_, reps_] := Catch[Module[
   	{thetas = inthetas, tower = intower, Dtower = inDtower, arg,
    eqnrhs, exps, logs, n, eqnlhs, sol, res, rhs, c},
   	RischTrace[ExpStructure, {test, thetas, tower, Dtower}, "In"];
   	(* Implementation of equation 9.9 from Bronstein. *)
   	(* With b in K and t = exp (b), i.e. Dt/t = Db. If (9.9) has a solution r_i in Q
   	then it provides a nonzero integer e and u in Kstar such that eDb = Du/u, hence c = (t^e)/u in
   	Const_D (K (t)) and K (t) is algebraic over C (c)(t_ 1,...,t_n) since t^e = cu. Otherwise, Db is not the
    logarithmic derivative of a K-radical, so t is a monomial over K having the same constant field. *)
   	arg = test /. rischExp[a_] :> a;
   	(* rhs of equation 9.8 *)
   	eqnrhs = Cancel[TotalDerivation[arg, thetas, Dtower]] //. reps;
   	(* determine equations 9.6 and 9.7 *)
   	{exps, logs} = findlogexp[tower];
   	(* lhs of equation 9.9 *)
   	{n, eqnlhs} = buildlhs[exps, logs, thetas, Dtower];
   	eqnlhs = eqnlhs //. reps;
   	(* solve lhs = rhs for the unknown Risch`r[_]'s *)
   	sol = structuresolve[eqnlhs, eqnrhs, thetas, n];
   	(* are solution (s) rational? *)
   	If[SameQ[sol, $Failed],
    	Dtower = Join[Dtower, {Cancel[TotalDerivation[test, thetas, Dtower] //. reps]}];
    	thetas = Join[thetas, {theta[Length[thetas]]}];
    	tower = Join[tower, {rischExp[arg //. reps]}];
    	res = {False, test, thetas, tower, Dtower, nums};
    	RischTrace[ExpStructure, res, "Out"];
    	Throw[{False, test, thetas, tower, Dtower, nums}]
    ];
   	(* solutions are rational => algebraically dependent *)
   	rhs = buildnewexptheta[sol, tower, thetas];
   	(* determine constant of integration *)
   	c = structureconstantexp[test, rhs, thetas, tower];
   	(* determine new theta *)
   	res = {True, c rhs, thetas, tower, Dtower, nums};
   	RischTrace[ExpStructure, res, "Out"];
   	Throw[res]
]];

buildnewexptheta[sol_, tower_, thetas_] := Module[{res, exps, logs, pt1, pt2},
  	RischTrace[buildnewexptheta, {sol, tower, thetas}, "In"];
  	exps = Select[tower, SameQ[Head[#], rischExp] &];
  	logs = Select[tower, SameQ[Head[#], rischLog] &];
  	(* log terms *)
  	logs = logs /. rischLog[a_] :> a;
  	pt1 = Map[logs[[#]]^sol[[#]] &, Range[Length[logs]]];
  	(* exp terms *)
  	pt2 = Map[exps[[#]]^sol[[Length[logs] + #]] &, Range[Length[exps]]];
  	res = Times @@ Join[pt1, pt2];
  	RischTrace[buildnewexptheta, res, "Out"];
  	res
];

faststructuresolve[eqnlhs_, eqnrhs_, inthetas_, n_] := Quiet[Module[{ls, lhs, rhs, vars, soln, res},
   (* a fast heuristic for solving systems of equations arising from structure theorems. *)
   RischTrace[faststructuresolve, {eqnlhs, eqnrhs}, "In"];
   ls = Thread[inthetas -> RandomInteger[{25, 45}, Length[inthetas]]];
   {lhs, rhs} = {eqnlhs, eqnrhs} /. ls;
   vars = Table[Risch`r[i], {i, 1, n}];
   soln = Quiet[vars /. Solve[lhs == rhs, vars] // Flatten];
   (* rational solution? *)
   Which[
    	SameQ[soln, {}],
    		res = $Failed,
    	And @@ (RationalQ /@ soln) && Union[soln] =!= {0,1}, (* second condition is experimental! *)
    		res = soln,
    	True,
    		res = $Failed
    ];
   	RischTrace[faststructuresolve, res, "Out"];
   	res
]];

structuresolve[eqnlhs_, eqnrhs_, inthetas_, n_] := Quiet[Module[
   	{hsol, thetas, lhs, rhs, plhs, prhs, eqns, res, vars, soln},
   	RischTrace[structuresolve, {eqnlhs, eqnrhs}, "In"];
   	thetas = Union[Join[{First[inthetas]}, Cases[{eqnlhs, eqnrhs}, theta[a_], {0, Infinity}]]];
   	(* cross multiply and cancel terms *)
   	{lhs, rhs} = {Together[eqnlhs], Together[eqnrhs]};
   	plhs = Expand[Numerator[lhs] Denominator[rhs]];
   	prhs = Expand[Numerator[rhs] Denominator[lhs]];
   	(* build system of equations *)
   	plhs = CoefficientArrays[plhs - prhs, thetas] // Normal // Flatten;
   	prhs = Table[0, {Length[plhs]}];
   	eqns = Thread[plhs == prhs];
   	(* solve the system of equations. This would be faster if we used LinearSolve... *)
   	vars = Table[Risch`r[i], {i, 1, n}];
   	soln = Quiet[vars /. Solve[eqns, vars] // Flatten];
   	(* rational solution? *)
   	Which[
    	SameQ[soln, {}],
    		res = $Failed,
    	Apply[And, RationalQ /@ soln] && Union[soln] =!= {0,1}, (* second condition is experimental! *)
    		res = soln,
    	True,
    		res = $Failed
    ];
   	RischTrace[structuresolve, res, "Out"];
   	res
]];

structureconstantlog[test_, rhs_, thetas_, tower_] := Module[{reps, c},
  	RischTrace[structureconstantlog, {test, rhs, thetas, tower}, "In"];
  	reps = Thread[thetas -> tower];
  	c = (test - rhs) //. reps /. {rischLog -> Log, rischExp -> Exp};
  	(* Of course, the following line will fail if 49/100 is a 
  	pole of test or rhs, but this will do for now... *)
  	(* We do need FullSimplify here, try 
  	RischStructure[x + rischLog[x] + 4 rischLog[rischLog[x]] + rischLog[2 rischLog[x]],x] *)
  	c = FullSimplify[c /. First[thetas] -> 49/100];
  	(* c is in the constant field of integrand. *)
  	RischTrace[structureconstantlog, c, "Out"];
  	c
];

structureconstantexp[test_, rhs_, thetas_, tower_] := Module[{reps, c},
  	RischTrace[structureconstantexp, {test, rhs, thetas, tower}, "In"];
  	reps = Thread[thetas -> tower];
  	c = (test/rhs) //. reps /. {rischLog -> Log, rischExp -> Exp};
  	(* Of course, the following line will fail if 51/100 is a 
  	pole of test or rhs, but this will do for now... *)
	  (* Added Simplify[] on 10/9/2008 to fix the zero simplification 
	  bug for the input:
	  a = ((1/z)^-z/Exp[z])
	  b = Exp[z (-Log[1/z]-1)]
      With[{expr=InputConvert[a-b,z]},RischStructure[expr,z]]
      %[[1,1]] *)
  	c = FullSimplify[c /. First[thetas] -> 51/100];
  	(* c is in the constant field of integrand. *)
  	RischTrace[structureconstantexp, c, "Out"];
  	c
];

ParametricLogarithmicDerivative[f_, thetas_, tower_, Dtower_]:= Catch[Module[
  	{exps, logs, n, eqnlhs, reps, sol, rhs, c, newtheta, newtower, res},
  	RischTrace[ParametricLogarithmicDerivative, {f, thetas, tower, Dtower}, "In"];
  	(* Solve the parametric logarithmic derivative problem using the 
  	structure theorem approach. See Bronstein p .250 onwards *)
  	reps = Thread[tower -> thetas];
  	(* rhs of equation 9.8 *)
  	(* determine equations 9.6 and 9.7 *)
  	{exps, logs} = findlogexp[tower];
  	(* lhs of equation 9.8 *)
  	{n, eqnlhs} = buildlhs[exps, logs, thetas, Dtower];
  	eqnlhs = eqnlhs //. reps;
  	(* solve lhs = rhs for the unknown Risch`r[_]'s *)
  	sol = structuresolve[eqnlhs, f, thetas, n];
  	(* are solution (s) rational? *)
  	If[SameQ[sol, $Failed],
  	 	RischTrace[ParametricLogarithmicDerivative, $Failed, "Out"];
   		Throw[$Failed]
   	];
  	(* solutions are rational => algebraically dependent *)
  	rhs = buildnewexptheta[sol, tower, thetas];
  	(* determine constant of integration *)
  	c = structureconstantlog[f, rhs, thetas, tower];
  	(* determine new theta *)
  	newtheta = c + rhs;
  	newtower = tower //. f -> newtheta;
  	res = Join[sol, {rhs}];
  	RischTrace[ParametricLogarithmicDerivative, res, "Out"];
  	Throw[res]
]];

IsStructureExtended[$Failed, thetas_, tower_] := {True};

IsStructureExtended[0, thetas_, tower_] := {False, 0};

IsStructureExtended[expr_, thetas_, tower_] := Module[{reps, fun, lst, res},
  	(* Checking to see of the structure of expr is contained within the given tower.
  	If the structure is extended then we return False, 
  	otherwise we return expr expressed using the thetas. *)
  	RischTrace[IsStructureExtended, {expr, thetas, tower}, "In"];
  	If[PolynomialQ[expr, First[thetas]] || IsIntegrandRational[expr, First[thetas]],
   		RischTrace[IsStructureExtended, {True}, "Out"];
   		Return[{False, expr}]
   	];
  	reps = Thread[Rest[thetas] -> Rest[tower]];
  	fun = TrigToExp[expr] //. reps;
  	(* call structure theorems *)
 	lst = RischStructure[fun, First[thetas]];
  	(* need to check that the new thetas match the old... *)
  	Which[
   	lst[[3]] === tower,
   		res = {False, First[lst]},
   	Complement[lst[[3]], tower] =!= {},
   		res = {True},
   	True,
   		res = {False, First[lst]}
   	];
  	RischTrace[IsStructureExtended, res, "Out"];
  	res
];

(*
End[];
EndPackage[]
*)

