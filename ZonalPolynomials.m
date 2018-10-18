\[Rho] = Rho; 
Rho[lam_] := Total[MapIndexed[#1 * (#1 - #2[[1]])&, lam]];

pgr[lam_, mu_] :=
  MatchQ[#1 - #2 & @@ PadRight[{lam, mu}], {(0) ..., a_ /; a > 0, ___}];
pgeq[lam_, mu_] :=
  MatchQ[#1 - #2 & @@ PadRight[{lam, mu}], {(0) ...} | {(0) ..., a_ /; a > 0, ___}];

myc[kap_, kap_] := myc[kap, kap] =
  (Multinomial @@ kap) - Total[myc[#, kap] & /@
    With[{p = IntegerPartitions[Total[kap]]}, Take[p, Position[p, kap][[1, 1]] - 1]]
  ];

myc[kap_, lam_] := myc[kap, lam] =
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
    If[pgeq[kap, mu], Total[Last /@ #] * myc[kap, mu], 0]]& /@
    SplitBy[SortBy[mus, First], First]];
  Return[If[sum != 0, sum / (Rho[kap] - Rho[lam]), 0]];
];

TableC[n_] :=
Module[{c, part = IntegerPartitions[n], rk, mus, sum, pos, tab = {}},
  MapIndexed[Function[{kap, p},
    pos = p[[1]];
    If[kap === {n}, c[{n}] = 1, c[kap] = Multinomial @@ kap - Total[#[[pos]] & /@ tab]];
    rk = Rho[kap];
    Function[{lam},
       mus = Flatten[Table[
       {Sort[ReplacePart[lam, {i -> lam[[i]] + t, j -> lam[[j]] - t}], Greater],
         lam[[i]] - lam[[j]] + 2 t},
       {j, 2, Length[lam]}, {i, j - 1}, {t, lam[[j]]}], 2];
       sum = Total[
         With[{mu = DeleteCases[#[[1, 1]], 0]}, 
           If[pgeq[kap, mu], Total[Last /@ #] * c[mu], 0]
         ]& /@
         SplitBy[SortBy[mus, First], First]
       ];
       c[lam] = If[sum != 0, sum/(rk - Rho[lam]), 0];
    ] /@ Drop[part, pos];
    AppendTo[tab, Join[Table[0, {pos - 1}], c /@ Drop[part, pos - 1]]];
  ], part];
  Return[tab];
];

SymMon[lam_, y_] := 
  If[Length[lam] > Length[y], 0,
    Total[(Times @@ (y^#))& /@ Permutations[PadRight[lam, Length[y]]]]
  ];
ZonalC[lam_] := 
  Total[(myc[lam, #] * (Sym @@ #))& /@ 
    With[{p = IntegerPartitions[Total[lam]]}, Drop[p, Position[p, lam][[1, 1]] - 1]]
  ];
ZonalC[lam_, y_] := ZonalC[lam] /. Sym[p__] :> SymMon[{p}, y];

(* Requires the HolonomicFunctions package *)
LaplaceBeltrami[y_List] := 
  ToOrePolynomial[
    Sum[(y[[i]]^2) ** Der[y[[i]]]^2 +
      Sum[If[i == j, 0, y[[i]]^2/(y[[i]] - y[[j]])] ** Der[y[[i]]], {j, Length[y]}],
    {i, Length[y]}]
  ];


mycn[kap_, kap_] := mycn[kap, kap] =
Module[{p},
  p = Flatten[Table[Prepend[#, n - i]& /@ IntegerPartitions[i], {i, 0, n - kap[[1]]}], 1];
  p = Take[p, Position[p, kap][[1, 1]] - 1];
  Return[Factor[FunctionExpand[Multinomial @@ kap] - Total[mycn[#, kap] & /@ p]]];
];
mycn[kap_, lam_] := mycn[kap, lam] =
Module[{mus, sum},
  mus = Flatten[Table[
    {Sort[DeleteCases[ReplacePart[lam, {i -> lam[[i]] + t, j -> lam[[j]] - t}], 0], Greater],
      ((lam[[i]] + t) - (lam[[j]] - t))},
    {j, Length[lam]}, {i, j - 1}, {t, lam[[j]]}], 2];
  (* Often the same mu appears several times. *)
  (* We first accumulate their possible contributions *)
  (* and then perform the necessary checks only once. *)
  sum = Total[With[{mu = #[[1, 1]]}, 
    If[pgeq[kap, mu], Total[Last /@ #] * mycn[kap, mu], 0]]& /@
    SplitBy[SortBy[mus, First], First]];
  Return[If[sum =!= 0, Factor[sum / (Rho[kap] - Rho[lam])], 0]];
];