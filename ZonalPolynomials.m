(*  ZonalPolynomials -- calculation of zonal polynomials
 *  Copyright (C) 2018  Christoph Koutschan
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version, see http://www.gnu.org/licenses/
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *)


(* The function rho. Can be written as Rho or with the greek letter. *)
\[Rho] = Rho;
Rho[lam_List] := Total[MapIndexed[#1 * (#1 - #2[[1]])&, lam]];

(* Whether partition lam is (strictly) greater than partition mu, in lexicographical order *)
PartitionGreater[lam_List, mu_List] :=
  MatchQ[#1 - #2 & @@ PadRight[{lam, mu}], {(0) ..., a_ /; a > 0, ___}];

(* Whether partition lam is greater than or equal to partition mu, in lexicographical order *)
PartitionGreaterEqual[lam_List, mu_List] :=
  MatchQ[#1 - #2 & @@ PadRight[{lam, mu}], {(0) ...} | {(0) ..., a_ /; a > 0, ___}];

(* Define the coefficients c_{kappa,lambda} of zonal polynomials recursively. *)
(* The diagonal coefficients c_{kappa,kappa} are computed with the "vertical" recursion. *)
ZonalCoefficient[kap_List, kap_List] := ZonalCoefficient[kap, kap] =
  (Multinomial @@ kap) - Total[ZonalCoefficient[#, kap]& /@
    With[{p = IntegerPartitions[Total[kap]]}, Take[p, Position[p, kap][[1, 1]] - 1]]
  ];
(* Once the diagonal coefficient c_{kappa,kappa} is known, *)
(* the coefficients c_{kappa,lambda} in the same row can be computed recursively. *)
ZonalCoefficient[kap_List, lam_List] := ZonalCoefficient[kap, lam] =
Module[{mus, sum},
  If[Min[FoldList[Plus, 0, Total[PadRight[{kap, -lam}]]]] < 0, Return[0]];
  mus = Flatten[Table[
    {Sort[DeleteCases[ReplacePart[lam, {i -> lam[[i]] + t, j -> lam[[j]] - t}], 0], Greater],
      ((lam[[i]] + t) - (lam[[j]] - t))},
    {j, Length[lam]}, {i, j - 1}, {t, lam[[j]]}], 2];
  (* Often the same mu appears several times. *)
  (* We first accumulate their possible contributions *)
  (* and then perform the necessary checks only once. *)
  sum = Total[With[{mu = #[[1, 1]]},
    If[PartitionGreaterEqual[kap, mu], Total[Last /@ #] * ZonalCoefficient[kap, mu], 0]]& /@
    SplitBy[SortBy[mus, First], First]];
  Return[If[sum != 0, sum / (Rho[kap] - Rho[lam]), 0]];
];

(* Generates a table with all zonal polynomials coefficients c_{kappa,lambda}, *)
(* where kappa and lambda are partitions of n. Hence the rows and columns *)
(* of this matrix are indexed by IntegerPartitions[n]. *)
ZonalCoefficientTable[n_Integer] :=
Module[{c, part = IntegerPartitions[n], rk, mus, sum, pos, tab = {}},
  MapIndexed[Function[{kap, p},
    pos = p[[1]];
    If[kap === {n}, c[{n}] = 1, c[kap] = Multinomial @@ kap - Total[#[[pos]]& /@ tab]];
    rk = Rho[kap];
    Function[{lam},
      c[lam] = If[Min[FoldList[Plus, 0, Total[PadRight[{kap, -lam}]]]] < 0,
        0
      ,
        mus = Flatten[Table[
          {Sort[ReplacePart[lam, {i -> lam[[i]] + t, j -> lam[[j]] - t}], Greater],
            lam[[i]] - lam[[j]] + 2 t},
          {j, 2, Length[lam]}, {i, j - 1}, {t, lam[[j]]}], 2];
        sum = Total[
          With[{mu = DeleteCases[#[[1, 1]], 0]}, 
            If[PartitionGreaterEqual[kap, mu], Total[Last /@ #] * c[mu], 0]
          ]& /@
          SplitBy[SortBy[mus, First], First]
        ];
        If[sum != 0, sum/(rk - Rho[lam]), 0]
      ];
    ] /@ Drop[part, pos];
    AppendTo[tab, Join[Table[0, {pos - 1}], c /@ Drop[part, pos - 1]]];
  ], part];
  Return[tab];
];

(* Gives the symmetric monomial function indexed by the partition lam, *)
(* in the variables y = {y1, y2, ..., ym}. *)
SymmetricMonomial[lam_List, y_List] := 
  If[Length[lam] > Length[y], 0,
    Total[(Times @@ (y^#))& /@ Permutations[PadRight[lam, Length[y]]]]
  ];

(* Gives the zonal polynomial indexed by the partition lambda, *)
(* in terms of the monomial symmetric functions. Example: *)
(* ZonalPolynomial[{3, 2}] yields (48/7)*M[3, 2] + (176/21)*M[2, 2, 1] + *)
(* (32/7)*M[3, 1, 1] + (64/7)*M[2, 1, 1, 1] + (80/7)*M[1, 1, 1, 1, 1] *)
ZonalPolynomial[lam_List] := 
  Total[(ZonalCoefficient[lam, #] * (M @@ #))& /@ 
    With[{p = IntegerPartitions[Total[lam]]}, Drop[p, Position[p, lam][[1, 1]] - 1]]
  ];

(* Gives the zonal polynomial indexed by the partition lambda, *)
(* as a symmetric polynomial in the variables y. Example: *)
(* ZonalPolynomial[{2,1}, {a,b,c}] yields *)
(* (18/5)*a*b*c + (12/5)*(a^2*b + a*b^2 + a^2*c + b^2*c + a*c^2 + b*c^2). *)
ZonalPolynomial[lam_List, y_List] := ZonalPolynomial[lam] /. M[p__] :> SymmetricMonomial[{p}, y];

(* Requires the HolonomicFunctions package *)
LaplaceBeltrami[y_List] := 
  ToOrePolynomial[
    Sum[(y[[i]]^2) ** Der[y[[i]]]^2 +
      Sum[If[i == j, 0, y[[i]]^2/(y[[i]] - y[[j]])] ** Der[y[[i]]], {j, Length[y]}],
    {i, Length[y]}]
  ];

(* Gives a symbolic expression (rational function in n) for the *)
(* for the zonal coefficient c_{kappa,lambda} in the upper left corner. *)
(* The partitions kappa and lambda must be of the form {n-i, pi}, *)
(* where pi is a partition of i and where n is symbolic. Example: *)
(* ZonalCoefficientN[{n-3,2,1},{n-4,2,2}] gives *)
(* (4*(-3 + n)*(-1 + n)*n*(39 - 18*n + 2*n^2))/(5*(-11 + 2*n)*(-7 + 2*n)) *)
ZonalCoefficientN[kap_List, kap_List] := ZonalCoefficientN[kap, kap] =
Module[{p},
  p = Flatten[Table[Prepend[#, n - i]& /@ IntegerPartitions[i], {i, 0, n - kap[[1]]}], 1];
  p = Take[p, Position[p, kap][[1, 1]] - 1];
  Return[Factor[FunctionExpand[Multinomial @@ kap] - Total[ZonalCoefficientN[#, kap]& /@ p]]];
];
ZonalCoefficientN[kap_List, lam_List] := ZonalCoefficientN[kap, lam] =
Module[{mus, sum},
  mus = Flatten[Table[
    {Sort[DeleteCases[ReplacePart[lam, {i -> lam[[i]] + t, j -> lam[[j]] - t}], 0], Greater],
      ((lam[[i]] + t) - (lam[[j]] - t))},
    {j, Length[lam]}, {i, j - 1}, {t, lam[[j]]}], 2];
  (* Often the same mu appears several times. *)
  (* We first accumulate their possible contributions *)
  (* and then perform the necessary checks only once. *)
  sum = Total[With[{mu = #[[1, 1]]}, 
    If[PartitionGreaterEqual[kap, mu], Total[Last /@ #] * ZonalCoefficientN[kap, mu], 0]]& /@
    SplitBy[SortBy[mus, First], First]];
  Return[If[sum =!= 0, Factor[sum / (Rho[kap] - Rho[lam])], 0]];
];
