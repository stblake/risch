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

(* BeginPackage["RischUtilities`"]; *)

RischTrace::usage="Debugging the Risch algorithm."
comma::usage=""
RischTable::usage="Table lookup for some integrals which Risch cannot handle."
PolyPseudoDivide::usage="Polynomial pseudo-division."
primitive::usage="Returns the primitive polynomial."
PrimitiveArg::usage=""
monic::usage=""
logMonic::usage=""
ExtendedEuclidean::usage="Extended Euclidean algorithm."
Squarefree::usage="Squarefree factorisation algorithm."
SubResultant::usage="Subresultant polynomial remainder sequence."
TotalDerivation::usage="Returns the total derivation is a differential field."
kappaD::usage=""
SplitFactor::usage="Splitting factorisation algorithm."
SplitSquarefreeFactor::usage="Splitting squarefree factorisation algorithm."
CanonicalRepresentation::usage=""
Remainder::usage=""
ValueAtInfinity::usage=""
OrderFunction::usage=""
RischParams::usage=""
myTrigToExp::usage="May well be a relic from a time when the structure theorem \
implementation was not what it is today."
InputConvert::usage=""
OutputConvert::usage=""
CompleteFactor::usage=""
BiQuadraticQ::usage=""
FactorBiQuadratic::usage=""
MatchLogs::usage=""
PreprocessExponents::usage=""
joinexponents::usage=""
allExprs::usage=""
UnsortedUnion::usage=""
DependOnTheta::usage=""
PureVariables::usage=""
theta::usage=""
StructureFast::usage=""
StructureLogExpCollect::usage=""
StructureAlgTrans::usage=""
Swap::usage=""
StructureDerivation::usage=""
findlogexp::usage=""
RationalQ::usage=""
MatrixOfConstants::usage=""
MinColNonConstIndex::usage=""
RowNonConstIndex::usage=""
TrigQ::usage=""
HypQ::usage=""
LogExpQ::usage=""
AlgebraicQ::usage="AlgebraicQ[expr_, x_] Determines if expr contains algebraic functions."
ExpandNumeratorDenominator::usage="ExpandNumeratorDenominator[expr_] Expands numerator and denominator of expr."
TrigRationalQ::usage="TrigRationalQ[f_,x_] tests if f is a rational function in terms \
of trigonometric functions(excluding tangents and cotangents)."
HyperbolicRationalQ::usage="HyperbolicRationalQ[f_, x_] tests if f is a rational function in terms \
of hyperbolic functions(excluding tanh's and coth's)."

(* Begin["`Private`"] *)

(************************
*
*	Misc
*
************************)

Unprotect[Log];
Log /: Log[rischExp[e_]]:= e;
Protect[Log];
rischLog[1]:= 0;(*
rischLog[rischExp[x_]]:= x;
rischExp[rischLog[x_]]:= x; *)
(* The conditions placed on the rule below is motivated by 
Risch[(2 (-1 + x Log[x]) Log[E^x/Log[x]])/(x Log[x]), x] *)(*
rischLog[a_ rischExp[x_]] := rischLog[a] + x /; Variables[Denominator[a]] === {}; (* experimental *)
*)
(* The inverse of CoefficientList *)
ToPolynomial[p_, x_] := Total[Map[p[[#]] x^(# - 1) &, Range[Length[p]]]]

(* Debugging code *)

RischTrace[msg_, val_, "In"] := 
 If[rischDebug, Print["Enter ", ToString[msg], ": ", val]]

RischTrace[msg_, val_, "Out"] := 
 If[rischDebug, Print["Exit ", ToString[msg], ": ", val]]

Info[s__]:= If[RischInfo === True, Module[{e},
    e = If[Head[#] =!= String, HoldForm[#] /. {rischLog -> Log, rischExp -> Exp}, #] & /@ {s};
    (* Print @ Style[TraditionalForm @ Text @ Row[e], 14, ScriptLevel -> 0] *)
    Print[Row[e]];
  ]
];

(* Coefficient of largest power *)
lc = If[!FreeQ[#1, #2], Coefficient[#1, #2^Exponent[#1, #2]], #1] &;

(* Define all the parameters in the integrand to be positive *)
RischParams[expr_, x_] := Map[(# /: Sign[#] = 1) &, DeleteCases[PureVariables[expr], x]]

TrigQ[f_, x_]:= !FreeQ[f, (Sin | Cos | Tan | Sec | Csc | Cot)[a_] /; ! FreeQ[a, x]]

HypQ[f_, x_]:= !FreeQ[f, (Sinh | Cosh | Tanh | Sech | Csch | Coth)[a_] /; !FreeQ[a, x]]

LogExpQ[f_, x_]:= !FreeQ[f, (rischLog | rischExp)[a_] /; !FreeQ[a, x]]

AlgebraicQ[fun_, x_]:= Cases[fun, p_^n_Rational /; ! FreeQ[p, x], {1, Infinity}] =!= {};

IsIntegrandRational[integrand_, x_] := Module[{singleFrac=Together[integrand]},
  	If[IsIntegrandPolynomial[Numerator[singleFrac], x] &&
  		IsIntegrandPolynomial[Denominator[singleFrac], x] &&
    	!FreeQ[Denominator[singleFrac], x] && !AlgebraicQ[integrand, x],
   			True,
   			False,
   			False
 	]
];

ExpandNumeratorDenominator[p_]:=Expand[Numerator[p]]/Expand[Denominator[p]]

TrigRationalQ[f_, x_] := Module[{coeff, s, c, F},
	
	coeff = Cases[f, (Sin | Cos | Tan | Cot | Sec | Csc)[a_. x] :> a /; FreeQ[a, x], {0, Infinity}];
	
	If[Length[DeleteDuplicates[coeff]] =!= 1, Return[False]];
	
  	F = Cancel[f /. {Sin[a_. x] -> s, Cos[a_. x] -> c, 
  			Csc[a_. x] -> 1/s, Sec[a_. x] -> 1/c, Tan[a_. x] -> s/c, Cot[a_. x] -> c/s}];

  	If[FreeQ[F, x] && Or @@ (!FreeQ[Denominator[F], #] & /@ {s, c}) && 
    	PolynomialQ[Denominator[F], {s, c}] && 
    	(PolynomialQ[Numerator[F], {s, c}] || Or @@ (FreeQ[Numerator[F], #] & /@ {s, c})) && 
    	FreeQ[F, (Log|Exp)[_]],
   			True,
   			False
	]
];

HyperbolicRationalQ[f_, x_] := Module[{coeff, s, c, F},
	
	coeff = Cases[f, (Sinh | Cosh | Tanh | Coth | Sech | Csch)[a_. x] :> a /; FreeQ[a, x], {0, Infinity}];
	If[Length[DeleteDuplicates[coeff]] =!= 1, Return[False]];
	
	F = Cancel[f /. {Sinh[a_. x] -> s, Cosh[a_. x] -> c, Csch[a_. x] -> 1/s, 
				Sech[a_. x] -> 1/c, Tanh[a_. x] -> s/c, Cot[a_. x] -> c/s}];

   	If[FreeQ[F, x] && Or @@ (! FreeQ[Denominator[F], #] & /@ {s, c}) &&
    	PolynomialQ[Denominator[F], {s, c}] &&
     	(PolynomialQ[Numerator[F], {s, c}] || Or @@ (FreeQ[Numerator[F], #] & /@ {s, c})) && 
     	FreeQ[F, (Log|Exp)[_]],
    		True,
    		False
    ]
];

(************************
*
*	Table Lookup
*
************************)

(* a couple of table entries used when certain parameters are symbolic *)
RischTable[x_^n_., x_] := x^(n + 1)/(n + 1) /; FreeQ[n, x] && n =!= -1;
RischTable[(a_. x_ + b_.)^n_., x_] :=
	(a x + b)^(n + 1)/(a (n + 1)) /;FreeQ[{a, b, n}, x] && n =!= -1;

(************************
*
*	Algebraics
*
************************)

(* Polynomial pseudo-division *)
PolyPseudoDivide[a_, b_, var_] := Module[
	{A = a, B = b, x = var, w, n, Q, R, deg, T, res},
	(* Reference: Symbolic Integration, Bronstein, p.9 *)
  	(* Given an integral domain D and A,B in D[x] with B != 0, return 
  	the pseudo quotient and pseudo remainder of A,B *)
  	RischTrace[PolyPseudoDivide, {a, b, var}, "In"];
  	w = lc[B, x];
  	n = Exponent[A, x] - Exponent[B, x] + 1;
  	Q = 0; R = A;
  	deg = Exponent[R, x] - Exponent[B, x];
  	While[R =!= 0 && deg >= 0,
   		T = lc[R, x] x^deg;
   		n = n - 1;
   		Q = Expand[w Q + T];
   		R = Expand[w R - T B];
   		deg = Exponent[R, x] - Exponent[B, x];
   	];
  	res = Flatten[{w^n Q, w^n R}];
  	RischTrace[PolyPseudoDivide, res, "Out"];
  	res
];

(* Primitive polynomial *)
primitive[p_, theta_, var_] := If[
	FreeQ[p, var] || !FreeQ[Denominator[p], var] || !NumberQ[#], 
		p, 
    	Collect[p/#, var]] &[PolynomialGCD @@ CoefficientList[p, var]
];

primitive[p_, var_] := If[
	FreeQ[p, var] || !FreeQ[Denominator[p], var] || !NumberQ[#], 
		p, 
    	Collect[p/#, var]] &[ PolynomialGCD @@ CoefficientList[p, var]
];

PrimitiveArg[f_, theta_, var_] := f /. rischLog[arg_] :> rischLog[primitive[arg, theta, var]];

(* Monic polynomial *)
monic[p_, var_] := If[FreeQ[p, var], 1, Collect[Expand[p/lc[p, var]], var]];

logMonic[p_, theta_, var_] := Which[
  								FreeQ[p, var],
  										1,
  								FreeQ[lc[p, var], theta],
  										p,
  								True,
  										Collect[Expand[p/lc[p, var]], var]
  						];

(* Extended Euclidean algorithm *)
ExtendedEuclidean[a_, b_, c_, x_] := Module[{g, t, s, q, r, res},
  	(* Reference: Symbolic Integration, Bronstein, p.14 *)
	(* Given a Euclidean domain D and a,b,c in D with c in (a,b), return
	s,t in D such that s*a + t*b = c *)
  	RischTrace[ExtendedEuclidean, {a, b, c, x}, "In"];
  	{g, {t, s}} = PolynomialExtendedGCD[a, b, x];
  	q = PolynomialQuotient[c, g, x];
  	{t, s} = q {t, s};
  	{q, r} = PolynomialQuotientRemainder[t, b, x];
  	res = {r, Together[s + q a]};
  	RischTrace[ExtendedEuclidean, res, "Out"];
  	res
];

(* Squarefree factorisation *)
Squarefree[a_, var_] := Catch[Module[{A = a, c, S, Sstar, Sneg, k = 1, Y},
   	(* Reference: Symbolic Integration, Bronstein, p.29 *)
   	(* Given a unique factorisation domain D of characteristic 0 and A in
	D[x], return A_1,...,A_m in D[x] such that A = Product[A_{k}^k,{k,1,m}] is a 
   	squarefree factorisation of A. *)
   	RischTrace[Squarefree, {a, var}, "In"];
   	c = PolynomialGCD @@ CoefficientList[A, var];
   	S = Cancel[A/c];
   	Sneg = PolynomialGCD[S, D[S, var]];
   	Sstar = Cancel[S/Sneg];
   	If[SameQ[Exponent[Sneg, var], 0],
    	RischTrace[Squarefree, A, "Out"];
    	Throw[{{A, 1}}]
    ];
   	A = Reap[
    	While[Exponent[Sneg, var] > 0,
       		Y = Expand[PolynomialGCD[Sstar, Sneg]];
       		A = Sow[{Cancel[Sstar/Y], k}];
       		Sstar = Y;
       		Sneg = Cancel[Sneg/Y];
       		k++
       	];
      	If[k > 1, Sow[{Sstar, k}]]
   	][[2, 1]];
   	A[[1]] = {c Sneg A[[1, 1]], 1};
   	RischTrace[Squarefree, A, "Out"];
   	Throw[A]
]];

(* Subresultant polynomial remainder sequence. *)
SubResultant[a_, b_, var_] := Module[{A = a, B = b, x = var, R, i, gamma, 
	delta, beta, rnew, r, Q, c, s, ply, Rem, k, res},
  	RischTrace[SubResultant, {a, b, var}, "In"];
  	(* Reference: Symbolic Integration, Bronstein, p.24 *)
  	(* Given an integral domain D and A,B in D[x] with B != 0 and deg(A) >= deg(B),
  	return resultant(A,B) and the subresultant polynomial remainder sequence of A and B. *)
	R = Join[{A}, {B}];
  	i = 2;
  	gamma = {-1};
  	delta = {Exponent[A, x] - Exponent[B, x]};
  	beta = {(-1)^(delta + 1)};
  	r = {lc[R[[i]], x]};
  	While[Not[SameQ[R[[i]], 0]] && i < 20,
   		AppendTo[r, lc[R[[i]], x]];
   		Rem = Last[PolyPseudoDivide[R[[i - 1]], R[[i]], x]];
   		R = Flatten[Join[R,  {Cancel[Rem/beta[[i - 1]]]}   ]];
   		If[R[[i + 1]] == 0, Break[]];
   		i = i + 1;
   		gamma = Flatten[Join[gamma, {(-r[[i - 1]])^delta[[i - 2]] gamma[[i - 2]]^(1 - delta[[i - 2]])}]];
   		delta = Flatten[Join[delta, {Exponent[R[[i - 1]], x] - Exponent[R[[i]], x]}]];
   		beta = Flatten[Join[beta, {-r[[i - 1]] gamma[[i - 1]]^delta[[i - 1]]}]];
   	];
  	k = i - 1;
  	If[Exponent[R[[k + 1]], x] > 0, Return[ Join[{0}, R] ]];
  	If[Exponent[R[[k]], x] == 1, Return[ Join[{R[[k]]}, R] ]];
  	s = 1;
  	c = 1;
  	Do[
   		If[OddQ[Exponent[R[[j]], x]] && OddQ[Exponent[R[[j + 1]], x]],
    		s = -s;
    	];
   		c = c (beta[[j]]/r[[j]]^(1 + delta[[j]]))^Exponent[R[[j + 1]], x] r[[j]]^(Exponent[R[[j]], x] - Exponent[R[[j + 2]], x])
   	, {j, 1, k - 1}];
  	res = Join[{s c R[[k + 1]]^Exponent[R[[k]], x]}, R];
  	RischTrace[SubResultant, res, "Out"];
  	res
];

(* Total derivation *)
Unprotect[Derivative];
Derivative[1][rischExp][f_] := rischExp[f];
Derivative[1][rischLog][f_] := 1/f;
Protect[Derivative];

Unprotect[D];
D[rischExp[f_], x_] := D[f, x] rischExp[f];
D[rischLog[f_], x_] := D[f, x]/f;
Protect[D];

(* linearity property of the total derivation *)
TotalDerivation[a_ + b_, intheta_, inDtower_] := TotalDerivation[a, intheta, inDtower] + TotalDerivation[b, intheta, inDtower];

TotalDerivation[fun_, intheta_, inDtower_] := Module[{theta, Dtower, result, kD},
  	RischTrace[TotalDerivation, {fun, intheta, inDtower}, "In"];
  	(* Total derivative of fun wrt the tower of extensions. *)
  	If[Length[intheta] == 1,
   		(* Rational Case *)
   		result = D[fun, First[intheta]];
   		RischTrace[TotalDerivation, result, "In"];
   		Return[result]
   	];
  	(* Cull the extensions if appropriate *)
  	{theta, Dtower} = UpdateExtensionField[fun, intheta, inDtower];
  	(* case where no thetas remain *)
  	If[Length[theta] == 1,
   		result = D[fun, First[theta]];
   		RischTrace[TotalDerivation, result, "In"];
   		Return[result]
   	];
  	(* Differentiation with thetas present *)
  	result = 0;
  	Do[
   		result = result + Dtower[[i]] D[fun, theta[[i]]];
   		, {i, 1, Length[theta]}
   	];
  	result = Collect[Expand[result], Last[theta]];
  	RischTrace[TotalDerivation, result, "Out"];
  	result
];

kappaD[fun_, theta_, Dtower_] := ToPolynomial[
  	Map[
  		TotalDerivation[#, Most[theta], Most[Dtower]] &, 
    	CoefficientList[fun, Last[theta] ]
    ] // Expand, Last[theta]
];
    
(* Splitting factorisation *)
SplitFactor[p_, theta_, Dtower_] := Module[{S, Qn, Qs, res},
  	RischTrace[SplitFactor, {p, theta, Dtower}, "In"];
  	(* Reference: Symbolic Integration, Bronstein, p.100 *)
  	(* Given a derivation D on k[t] and p in k[t], return (p_n,p_s) in k[t]^2 such that
  	p = p_n*p_s is special, and each squarefree factor of p_n is normal *)
  	S = Cancel[PolynomialGCD[p, TotalDerivation[p, theta, Dtower]]/PolynomialGCD[p, D[p, Last[theta]]]]; (* exact division *)
  	If[Exponent[S, Last[theta]] === 0, Return[{p, 1}]];
  	{Qn, Qs} = SplitFactor[Cancel[p/S], theta, Dtower]; (* exact division *)
  	res = Expand[{Qn, S Qs}];
  	RischTrace[SplitFactor, res, "Out"];
  	res
];

(* Splitting squarefree factorisation *)
SplitSquarefreeFactor[p_, theta_, tower_] := Module[{Plist, term, P, S = {}, n = {}},
  	RischTrace[SplitSquarefreeFactor, {p, theta, tower}, "In"];
  	(* Reference: Symbolic Integration, Bronstein, p.102 *)
  	(* Given a derivation D on k[t] and p in k[t], return (N_1,...,N_m)
  	and (S_1,...,S_m) in k[t]^m such that p=(N_1*N_{2}^2*...*N_{m}^m)(S_{1}*S_{2}^2*...*S_{m}^m)
  	is a splitting factorisation of p and the N_i and S_i are squarefree and coprime *)
  	P = First /@ Squarefree[p, Last[theta]];
  	Do[
   		AppendTo[S, 
   			Expand@PolynomialGCD[Part[P, i], Collect[TotalDerivation[Part[P, i], theta, tower], Last[theta]]]
   		];
   		AppendTo[n, Cancel[Part[P, i]/Part[S, i]]]
   	, {i, 1, Length[P]}];
  	RischTrace[SplitSquarefreeFactor, {n, S}, "Out"];
  	{n, S}
];

(* Canonical representation *)
CanonicalRepresentation[f_, theta_, tower_, Dtower_] := Module[
	{tf, a, b, c, d, q, r, dn, ds, res},
  	RischTrace[CanonicalRepresentation, {f, theta, Dtower}, "In"];
  	(* Reference: Symbolic Integration, Bronstein, p.103 *)
  	(* Example in Bronstein p. 140 *)
  	(* canonical representation returns (f_p,f_s,f_n), where f_p is the polynomial part
  	of f, f_s is the special part of f, and f_n is the normal part of f. *)
  	(* Updating the extension field motivated by
  		Risch[((-1+x Log[x]) Log[E^x/Log[x]])/(x Log[x]),x] *)
  	(* {theta,tower,Dtower} = UpdateExtensionField[f, itheta, itower, iDtower]; *)
  	tf = Together[f];
  	{a, d} = {Numerator[tf], Denominator[tf]};
  	(* The use of Together[] (above) was motivated by the following integral
  	Risch[(1 - 5 x^3 + Log[x] (x - 5 x^4 - 15 x^3 Log[E^x Log[x]]))/(x Log[x]), x] *)
  	{q, r} = PolynomialQuotientRemainder[Expand @ a, Expand @ d, Last[theta]];
  	{dn, ds} = SplitFactor[d, theta, Dtower];
  	{b, c} = ExtendedEuclidean[dn, ds, r, Last[theta]];
  	res = {Together[q], Cancel[b/ds], Cancel[c/dn]};
  	RischTrace[CanonicalRepresentation, res, "Out"];
  	res
];

Remainder[x_, a_, var_] := Quiet[Module[{X, b, c, res},
   	RischTrace[Remainder, {x, a, var}, "In"];
   	(* Reference: Symbolic Integration, Bronstein, p.115 *)
   	(* example at p.190 *)
   	X = Cancel[x];
   	{b, c} = ExtendedEuclidean[a, Denominator[X], 1, var];
   	res = PolynomialRemainder[Expand[Numerator[X] c], a, var];
   	RischTrace[Remainder, res, "Out"];
   	res
]];

ValueAtInfinity[f_, var_] := Module[{a, b, res},
  	RischTrace[ValueAtInfinity, {f, var}, "In"];
  	(* Value at infinity, Bronstein p. 118 *)
  	If[f === 0, Return[0]];
  	a = Numerator[f];
  	b = Denominator[f];
  	If[Exponent[b, var] > Exponent[a, var], 0];
  	res = Cancel[lc[a, var]/lc[b, var]];
  	RischTrace[ValueAtInfinity, res, "Out"];
  	res
];

OrderFunction[0, a_, toptheta_] := 0;

OrderFunction[x_, a_, toptheta_] := Catch[Module[{n},
   	RischTrace[OrderFunction, {x, a, toptheta}, "In"];
   	(* The Order Function, reference: Symbolic Integration, Bronstein, p.107 *)
   	(*v_{a}(0) = Infinity, for x in D\{0}, v_{a}(x) = max(n in N such that a^n divides x)*)
   	If[a == 0, Throw[Infinity]];
   	Which[
   		FreeQ[Denominator[x], toptheta],
    		n = 0;
    		While[PolynomialRemainder[x, a^n, toptheta] === 0, n++];
    		RischTrace[OrderFunction, n - 1, "Out"];
    		Throw[n - 1],
    	True,
    		Throw[OrderFunction[Numerator[x], a, toptheta] - OrderFunction[Denominator[x], a, toptheta]]
    ]
]];

(* Rioboo conversion *)
LogToReal[R_, S_, theta_] := Module[
	{x, y, rRe, rIm, sRe, sIm, roots, log, atan, a, b, a1,
   	b1, a2, b2, root, logarg, logterm, atanterm, result},
  	RischTrace[LogToReal, {R, S, theta}, "In"];
  	rRe = ComplexExpand[Re[R /. rischZ -> x + I y]];
  	rIm = ComplexExpand[Im[R /. rischZ -> x + I y]];
  	sRe = ComplexExpand[Re[S /. rischZ -> x + I y]];
  	sIm = ComplexExpand[Im[S /. rischZ -> x + I y]];
  	(*both sRe and sIm are at most quadratic polynomials*)
  	roots = {x, y} /. Solve[rRe == 0 && rIm == 0, {x, y}];
  	result = 0;
  	Which[
  		Length[roots] == 1,
   			If[SameQ[Sign[Last[roots]], 1],
    			logarg = (sRe /. {x -> First[roots], y -> Last[roots]})^2 + (sIm /. {x -> First[roots], y -> Last[roots]})^2;
    			logterm = First[roots] rischLog[primitive[Together[logarg], theta]];
    			atanterm = Last[roots] Quiet[(LogToAtan[sRe, sIm, theta] /. {x -> First[roots], y -> Last[roots]})];
    			result = Simplify[logterm] + Simplify[atanterm]],
   		True, 
   			Do[
   				root = roots[[rt]];
    			If[SameQ[Sign[Last[root]], 1],
     				logarg = (sRe /. {x -> First[root], y -> Last[root]})^2 + (sIm /. {x -> First[root], y -> Last[root]})^2;
     				logterm = First[root] rischLog[primitive[Together[logarg], theta]];
     				atanterm = Last[root] Quiet[(LogToAtan[sRe, sIm, theta] /. {x -> First[root], y -> Last[root]})];
     				result = result + Simplify[logterm] + Simplify[atanterm]
     			],
    		{rt, 1, Length[roots]}]
   	];
  	RischTrace[LogToReal, result, "Out"];
  	result
];

LogToAtan[a_, b_, var_] := Quiet[Catch[Module[{A = a, B = b, d, c, g, res},
   	RischTrace[LogToAtan, {a, b, var}, "In"];
    (* Rioboo Conversion, reference: Symbolic Integration, Bronstein, p.107 *)
    (* Given a field K of characteristic 0 such that Sqrt[-1] is not in K and
    A,B in K[x] with B!=0, return a sum f of arctangents of polynomials in K[x]
    such that D[f,x] = D[I Log[(a + I B)/(A - I B)],x] *)
    If[Mod[A, B] == 0 || PolynomialMod[A, B] == 0,
     	RischTrace[LogToAtan, {a, b, var}, "Out"];
     	Throw[2 ArcTan[A/B]]
    ];
    If[Exponent[A, var] < Exponent[B, var],
     	RischTrace[LogToAtan, HoldForm[LogToAtan[-B, A, var]], "Out"];
     	Throw[LogToAtan[-B, A, var]]
    ];
    {d, c} = ExtendedEuclidean[B, -A, PolynomialGCD[A, B], var];
    g = PolynomialGCD[A, B];
    res = 2 ArcTan[Simplify[(A d + B c)/g]] + LogToAtan[d, c, var];
    RischTrace[LogToAtan, res, "Out"];
    Throw[res]
]]];

(**************************
*
* I/O conversions
*
***************************)
myTrigToExp[f_] := Module[{F},
	RischTrace[myTrigToExp, f, "In"];
  	F = f //. {
  			Sin :> rischSin, Cos :> rischCos, Sinh :> rischSinh,
     		Cosh :> rischCosh, Tan :> rischTan, Tanh :> rischTanh,
     		Csc[arg_] :> 1/rischSin[arg], Cot[arg_] :> 1/rischTan[arg], 
     		Sec[arg_] :> 1/rischCos[arg], Csch[arg_] :> 1/rischSinh[arg], 
     		Coth[arg_] :> 1/rischTanh[arg], Sech[arg_] :> 1/rischCosh[arg]
     	};
  	F = F //. {
  			rischSin[arg_] :> (I/2) ((1 - rischExp[I arg]^2)/rischExp[I arg]), 
     		rischCos[arg_] :> (1/2) ((1 + rischExp[I arg]^2)/rischExp[I arg]),
     		rischTan[arg_] :> I (1 - rischExp[I arg]^2)/(1 + rischExp[I arg]^2),
     		rischSinh[arg_] :> ((-1 + rischExp[arg]^2)/rischExp[arg])/2,
     		rischCosh[arg_] :> (1 + rischExp[arg]^2)/rischExp[arg]/2,
     		rischTanh[arg_] :> (-1 + rischExp[arg]^2)/(1 + rischExp[arg]^2)};
  	RischTrace[myTrigToExp, F, "Out"];
  	F
];

InputConvert[f_, var_] := Module[{integrand},
  	RischTrace[InputConvert, {f, var}, "In"];
  	integrand = TrigToExp[myTrigToExp[f]] //. {Log :> rischLog, Exp :> rischExp, E^a_ :> rischExp[a]};
  	(* we use the following rule because Exp[x Log[x]] gets automatically converted to x^x, 
  	which we do not want for our structure theorems. For example Risch[(1 + Log[x]) x^x, x] *)
  	integrand = integrand /. a_^b_ :> rischExp[b rischLog[a]] /; ! FreeQ[b, var] && a =!= E;
  	integrand = integrand /. rischLog[e_] :> rischLog[Cancel[e]];
  	integrand = ExpandNumeratorDenominator[ Together[integrand] ];
  	RischTrace[InputConvert, {integrand, var}, "Out"];
  	{integrand, var}
];

OutputConvert[integrand_, result_, theta_, tower_, var_] := Module[{solution, reps},
  	RischTrace[OutputConvert, {integrand, result}, "In"];
  	(* remove theta notation *)
  	reps = Thread[theta -> tower];
  	solution = result //. reps;
  	(*Convert back out of our internal log form *)
  	solution = solution //. {rischLog -> Log, rischExp -> Exp};
  	(* write as trigs if possible *)
  	solution = solution /. c1_. Log[-I + Exp[I a_. var]] + c2_. Log[I + Exp[I a_. var]] :> 
    	c2 Log[Sec[a var] + Tan[a var]] /; FreeQ[a, var] && c1 === -c2 && Sign[c2] === 1;

  	If[TrigQ[integrand, First[tower]], 
   		solution = FixedPoint[ExpToTrig, solution]
   	];

  	solution = solution //. a_. Cosh[X_] + a_. Sinh[X_] :> a*Exp[X];
  	solution = solution /. -I var + Log[-1 + Cos[2 a_. var] + I Sin[2 a_. var]] :> 
     	Log[Sin[a var]] /; FreeQ[a, var];
  	solution = solution /. I var - Log[1 + Cos[2 a_. var] + I Sin[2 a_. var]] :> 
     	Log[Cos[a var]] /; FreeQ[a, var];
  	(* back to original variable *)
  	solution = solution /. rischVar -> var;
  	RischTrace[OutputConvert, solution, "Out"];
  	solution
];

(********************************
*
* Splitting factorisation
*
*********************************)
CompleteFactor[f_, x_] := Module[{res},
  	RischTrace[CompleteFactor, {f, x}, "In"];
  	res = Factor[f, Extension -> Re[x /. Solve[f == 0, x]]];
  	RischTrace[CompleteFactor, res, "Out"];
  	res
];

(**************************************
*
* Factoring the biquadratic
*
***************************************)
BiQuadraticQ[poly_, var_] := 
	SameQ[Exponent[poly, var], 4] && 
	And @@ Map[SameQ[Coefficient[poly, var, #], 0] &, {1, 3}] && 
	!SameQ[Coefficient[poly, var, 2], 0]

FactorBiQuadratic[poly_, var_] := Module[{a, b, c, root1, root2, poly1, poly2},
  	RischTrace[FactorBiQuadratic, {poly, var}, "In"];
  	{a, b, c} = Reverse[Select[CoefficientList[poly, var], ! SameQ[#, 0] &]];
  	root1 = Simplify[(-b + Sqrt[b^2 - 4 a c])/(2 a)];
  	root2 = Simplify[(-b - Sqrt[b^2 - 4 a c])/(2 a)];
  	(*
  	Commented out to stop naive for for Risch[1/(x^4 - 4 x^2 + 6), x]
  	
  	If[Im[root1] != 0 || Im[root2] != 0,
   		RischTrace[FactorBiQuadratic, poly, "Out"];
   		Return[{poly}]
   	];*)
  	poly1 = (var^2 - root1);
  	poly2 = (var^2 - root2);
  	RischTrace[FactorBiQuadratic, {poly1, poly2}, "Out"];
  	{poly1, poly2}
];

(*******************************************************
*
* Use structure theorems to match new logarithms 
*
********************************************************)
MatchLogs[0, theta_, tower_, Dtower_]:= {True, 0};

MatchLogs[expr_, theta_, tower_, Dtower_]:= Catch[Module[
	{log, res, reps, rreps, ourtower, struct1, struct2, newtower, newexpr, result,
	bag, thetheta, newreps, newexprarg, A, B, arg, n, out, thelog, logarg, const},
  	RischTrace[MatchLogs, {expr, theta, tower, Dtower}, "In"];
  	
  	(* use log structure theorem to remove algebraic dependencies. *)
  	reps = Thread[theta -> tower];
  	rreps = Thread[tower -> theta];
  	(* expr is of the form A*theta + B, where A,B are in K(x,..., \[Theta]_{n-1}). *)
  	res = expr //. reps;
  	(* Use of Simplify[] motivated by Risch[(5 E^x (x + 1) Log[E^x x + 1]^4)/(E^x x + 1), x] *)
  	res = Expand[ res //. rischLog[a_] :> rischLog[Numerator[a]] - rischLog[Denominator[a]] ];
  	res = Expand[ res //. rischLog[a_ b_] :> rischLog[a] + rischLog[b] /; !Negative[a] && !Negative[b] ];
  	log = Cases[res, rischLog[_], {0, Infinity}];
  	log = log //. reps;
  	If[log === {}, Throw[{True, expr //. rreps}]];
  	
  	(* the following 3 lines are motivated by Risch[(4 Log[Log[x]^2])/(x Log[x]), x] *)
	log = If[MatchQ[#, n_ rischLog[e_] /; Variables[n] === {}], # /. n_ rischLog[e_] :> rischLog[e^n], #]& /@ log;
	ourtower = tower //. reps;
  	If[Complement[log, ourtower] === {}, Throw[{True, res //. rreps}] ];
  	
  	(* Construct extension field for the new expr with the tower extensions and 
  	check if the inclusion of expr has introduced new logarithmic extensions. This
  	can be more tricky than one would initially think, as the original tower may
  	be a little problematic, for example {x, t1 = Log[x], t2 = Log[t1^2]} and expr = 4 Log[Log[x]]. *)
  	struct1 = RischStructure[res + Total[tower] //. reps, First[theta]];
	struct2 = RischStructure[res - Total[tower] //. reps, First[theta]];

	newexpr = Expand @ Simplify[(First[struct1] + First[struct2])/2]; (* res == expr *)
	(*
	Print["old expr ", expr];
	Print["new expr ", newexpr];
	Print["new tower I: ", struct1[[3]]];
	Print["new tower II: ", struct2[[3]]];
	Print["old tower ", tower];
	Print["nice old tower ", tower//makenice];
	*)
	(* the following is motivated by Risch[(4 Log[Log[x]^2])/(x Log[x]), x] *)
	If[ struct1[[3]] === struct2[[3]],
		If[struct1[[3]] === tower, Throw[{True, newexpr}]]; (* easy case ;-) *)
		
		newreps = Thread[ struct1[[2]] -> struct1[[3]] ];
		newtower = DeleteDuplicates[ Join[ struct1[[3]], struct2[[3]] ] ];
		
    	If[Complement[newtower, makenice[tower]] === {},
    		(* here there exists a member of the tower rischLog[a t] and we're
    		testing rischLog[t] or vice versa. So we need to rearrange and solve 
    		for expr.... (or rischLog[a^b] and b*rischLog[a]) *)
    		
    		(* Test the tower for the rule:
    			log(a^n) = n*log(a) *)
    		bag = Select[tower, !SameQ[# /. First[$logrules], #] &];
    		If[bag =!= {},
    			{A, B, arg} = Last @ Cases[expr, A_. rischLog[a_] + B_. :> {A, B, a //. reps}, {0, Infinity}];
    			newexprarg = Last @ Cases[newexpr //. newreps, rischLog[a_] :> a, {0, Infinity}];
    			If[newexprarg =!= arg, Throw[{False, expr}] ];
    			n = First @ Cases[First[bag], rischLog[e_^n_] :> n, {0, Infinity}];
    			thetheta = First @ Extract[theta, Position[tower, First[bag]] ];
    			out = (A/n)*thetheta + B;
    			Throw[{True, out}]
    		];

    		(* Test the tower for the rule:
    			log(a/b) = log(a) - log(b) *)
    		bag = Select[tower, !SameQ[# /. $logrules[[3]], #] &];
    		If[bag =!= {},
    			thelog = Last[bag] /. rischLog[a_/b_] :> {rischLog[a], rischLog[b]} //. reps;
				{A, B, arg} = Last @ Cases[expr, A_. rischLog[a_] + B_. :> {A, B, a //. reps}, {0, Infinity}];
				Which[
					thelog[[1,1]] === arg,
						thetheta = First @ Extract[theta, Position[tower, First[bag]] ];
						out = A*(thetheta + Last[thelog]) + B //. $logrules //. rreps;
						Throw[{True, out /. rischLog -> Log}],
					thelog[[2,1]] === arg,
						thetheta = First @ Extract[theta, Position[tower, Last[bag]] ];
						out = A*(First[thelog] - thetheta) + B //. $logrules //. rreps;
						Throw[{True, out /. rischLog -> Log}]
				]
    		];
    		
    		(* Test the tower for the rule:
    			log(a*b) = log(a) + log(b) *)
    		bag = Select[tower, !SameQ[# /. $logrules[[2]], #] &];
    		If[bag =!= {},
    			thelog = Apply[List, Last[bag] /. $logrules[[2]] ] //. reps;
				{A, B, arg} = Last @ Cases[expr, A_. rischLog[a_] + B_. :> {A, B, a //. reps}, {0, Infinity}];
				Which[
					thelog[[1,1]] === arg,
						thetheta = First @ Extract[theta, Position[tower, First[bag]] ];
						out = A*(thetheta - Last[thelog]) + B //. $logrules //. rreps;
						Throw[{True, out /. rischLog -> Log}],
					thelog[[2,1]] === arg,
						thetheta = First @ Extract[theta, Position[tower, Last[bag]] ];
						out = A*(thetheta - First[thelog]) + B //. $logrules //. rreps;
						Throw[{True, out /. rischLog -> Log}],
					True,
						Throw[{False, expr}]
				]
    		];

    		(* New logarithm introduced? Most likely.... *)
    		Throw[{False, expr}],
    		(* ELSE *)
    		logarg = log[[1,1]];
    		bag = Select[makenice[tower], If[Head[#]===rischLog, PureVariables[Cancel[logarg/First[#]]]=== {}] &];
    		If[bag =!= {},
    			const = Cancel[ logarg/bag[[1,1]] ];
    			{A, B, arg} = Last @ Cases[expr, A_. rischLog[a_] + B_. :> {A, B, a //. reps}, {0, Infinity}];
    			If[MemberQ[tower, First[bag]],
    				thetheta = First @ Extract[theta, Position[tower, Last[bag]] ];
    				Print["UNCHECKED HEURISTIC"];
    				Throw[{True, B + A*const*thetheta}](* need to check... *)
    			];
    			(* modify expr and recursively call MatchLogs(and cross your fingers) *)
    			Throw @ MatchLogs[B + A*Last[bag], theta, tower, Dtower]
    		];
    		(* New logs probably introduced *)
    		Throw[{False, expr}]
    	],
    	(* ELSE Cancellation has occured between the original tower and expr, so expr
    	must be algebraically dependent to the tower. Determine this dependency... *)
    	Print["!!!"];
	];
    
  	RischTrace[MatchLogs, result, "Out"];
  	result
]];

makenice[l_List]:= l /. {rischLog[a_/b_] :> Sequence[rischLog[a], rischLog[b], rischLog[a/b]],
						rischLog[a_ b_] :> Sequence[rischLog[a], rischLog[b], rischLog[a b]],
						rischLog[a_^n_] :> Sequence[rischLog[a], rischLog[a^n]]};
						
$logrules := {rischLog[a_^n_] :> n rischLog[a], 
	rischLog[a_ b_] :> rischLog[a] + rischLog[b],
	rischLog[a_/b_] :> rischLog[a] - rischLog[b],
	rischLog[rischExp[e_]] :> e};

(*****************************************
*
* Code related to the structure theorems
*
******************************************)
PreprocessExponents[integrand_, x_] := Catch[Module[{result = integrand, e, l, reps},
   	RischTrace[PreprocessExponents, {integrand, x}, "In"];
   	(* find algebraic relationships between powers like 2^x,4^x,32^x etc. 
   	This means we can find integrals like Risch[2^x/(4^x - 2^x + 1),x] *)
   	e = Union[Cases[integrand, rischExp[x rischLog[a_]] :> a /; FreeQ[a, x], {0, Infinity}]];
   	If[e === {} || Length[e] === 1,
    	RischTrace[PreprocessExponents, integrand, "Out"];
    	Throw[integrand]
    ];
   	l = Thread[{e, FactorInteger[e]}];
   	reps = rischExp[x rischLog[#1]] -> joinexponents[#2, x] & @@@ l;
   	result = integrand //. reps;
   	RischTrace[PreprocessExponents, result, "Out"];
   	(* return the modified integrand *)
   	Throw[result]
]];

joinexponents[lst_, x_] := Times @@ (rischExp[x rischLog[#1]]^#2 & @@@ lst);

allExprs[f_] := Join[
			PureVariables[f], 
			Cases[f, Tan[_], {1, Infinity}], 
  			Cases[f, Log[_], {1, Infinity}], Cases[f, Exp[_], {1, Infinity}], 
  			Cases[f, ArcTan[_], {1, Infinity}]
  		];

UnsortedUnion[l_List]:= Tally[l][[All, 1]];

DependOnTheta[fun_, theta_, intower_] := Catch[Module[{thetas},
   	(* want to check if any thetas in fun depend on the specific theta \we input. *)
   	thetas = Cases[fun, Subscript[\[Theta], _], {0, Infinity}];
   	If[thetas === {}, 
   		Throw[False]
   	];
   	Do[
    	If[!FreeQ[intower[[i]], theta], 
    		Throw[True]
    	]
    , {i, 1, Length[intower]}
    ];
   	Throw[False]
]];

UpdateExtensionField[fun_, intheta_, inDtower_] := Module[{theta, Dtower},
  	theta = {First[intheta]};
  	Dtower = {1};
  	Do[
   		If[!FreeQ[fun, Part[intheta, i]],
    		AppendTo[theta, Part[intheta, i]];
    		AppendTo[Dtower, Part[inDtower, i]]
    	]
   , {i, 2, Length[intheta]}
   ];
  	{theta, Dtower}
];

UpdateExtensionField[fun_, intheta_, intower_, inDtower_]:= Module[{theta, tower, Dtower},
  	theta = {First[intheta]};
  	tower = {First[intower]};
  	Dtower = {1};
  	Do[
   		If[!FreeQ[fun, Part[intheta, i]] || DependOnTheta[fun, Part[intheta, i], intower],
    		AppendTo[theta, Part[intheta, i]];
    		AppendTo[tower, Part[intower, i]];
    		AppendTo[Dtower, Part[inDtower, i]]
    	]
   	, {i, 2, Length[intheta]}
   	];
  	{theta, tower, Dtower}
];

PureVariables[v_]:= Select[Variables[ Level[v, {-1} ] ], Length[Attributes[#]] == 0 &];

theta[n_] := Subscript[\[Theta], n];

StructureFast[f_, x_] := (f /. {
		Log[arg_] :> rischLog[arg], Exp[arg_] :> rischExp[arg]
	}) //. {
		(* Removed the rule below so we get a correct solution for Risch[-Tan[x] x^5 + 5 Log[x^12 Cos[x]] x^4 + 12 x^4, x] *)
		(*c_. rischLog[a_] :> c rischLog[Numerator[a]] - c rischLog[Denominator[a]] /; !FreeQ[Numerator[a], x] && !FreeQ[Denominator[a], x],*)
   		(* rischLog[a_ b_] :> rischLog[a] + rischLog[b] /; FreeQ[a, x], *)
   		rischExp[a_ b_] :> rischExp[b]^a /; FreeQ[a, x] && !FreeQ[b, x] && IntegerQ[a],
   		rischExp[a_ b_] :> rischExp[I b]^Im[a] /; FreeQ[a, x] && !FreeQ[b, x] && Im[a] =!= 0 && Re[a] === 0 && IntegerQ[Im[a]],
   		rischLog[arg_] :> Log[arg] /; FreeQ[arg, x],
   		rischExp[arg_] :> Exp[arg] /; FreeQ[arg, x]
   	};

StructureLogExpCollect[f_, x_] := Union /@ {
		Cases[f, rischLog[arg_] /; ! FreeQ[arg, x], {0, Infinity}],
   		Cases[f, rischExp[arg_] /; ! FreeQ[arg, x], {0, Infinity}]
   	};

StructureAlgTrans[f_, x_] := Union[Flatten[{
    Cases[f, c_ /; FreeQ[c, x] && Head[c] =!= Rational && Head[c] =!= Integer, {1, Infinity}],
    Cases[f, rischLog[c_] /; FreeQ[c, x], {1, Infinity}],
    Cases[f, rischExp[c_] /; FreeQ[c, x], {1, Infinity}]
}]];

Swap[lst_List, p1_Integer, p2_Integer]:= Module[{res = lst}, 
	res[[p1]] = lst[[p2]]; res[[p2]] = lst[[p1]]; 
  	res
];

StructureDerivation[tower_, thetas_, var_, reps_] := Module[{res},
  	RischTrace[StructureDerivation, {tower, thetas, var, reps}, "In"];
  	res = Reap[Sow[D[#, var] //. reps] & /@ tower] // Last // Flatten;
  	RischTrace[StructureDerivation, res, "Out"];
  	res
];

findlogexp[tower_] := Module[{exps, logs},
  	RischTrace[findlogexp, tower, "In"];
  	exps = Cases[tower, rischExp[a_] :> a, {0, Infinity}];
  	logs = Cases[tower, rischLog[a_] :> a, {0, Infinity}];
  	RischTrace[findlogexp, {exps, logs}, "Out"];
  	{exps, logs}
];

RationalQ[n_] := Or @@ {Head[n] === Rational, Head[n] === Integer};

MatrixOfConstants[M_, var_]:= (Length[#] == 1 && First[#]) &[ Union[Map[FreeQ[Cancel[#], var] &, Flatten[M]]] ];

MinColNonConstIndex[A_, var_]:= Catch[If[! MatrixOfConstants[#, var], Throw[Position[Transpose[A], #] // Flatten // First]] & /@ Transpose[A]];

RowNonConstIndex[A_, var_] := Catch[If[! FreeQ[#, var], Throw[Position[A, #] // Flatten // First]] & /@ A];

(*
End[];
EndPackage[];
*)
