(* ::Package:: *)

MZonal[partition_,variables_]:=Module[
{p=partition,v=variables,m=Length[partition],
n=Length[variables],test,\[Xi],list,temp},
If[n<m,Return[0],
    (list=Permutations[v,{m}];
     temp=Map[MapThread[Power,{#,p}]&,list];
     temp=Apply[Plus,Map[Apply[Times,#]&,temp]];
     temp=temp/ACal[p]//Expand;
     Return[temp]
    )
  ]
];


CZonal[partition_,variables_]:=Module[
{p=partition,v=variables,n=Apply[Plus,partition],table,
position,\[Xi]},
table=IntegerPartitions[n];
position=Position[table,p][[1,1]];
table=table[[position;;]];
Sum[Coeff[p,table[[\[Xi]]]]*MZonal[table[[\[Xi]]],v],{\[Xi],1,Length[table]}]
];


Coeff[\[Kappa]_,\[Lambda]_]:=Module[
{n=Apply[Plus,\[Kappa]],list,list1,list2,list3,p\[Kappa],p\[Lambda],return,\[Rho],\[Xi],
t,pt,table},
table=IntegerPartitions[n];
If[\[Kappa]===\[Lambda]&&Length[\[Kappa]]===1,return=1,
If[\[Kappa]===\[Lambda],(t=Position[table,\[Lambda]][[1,1]];
          pt=Apply[Multinomial,\[Kappa]];
           return=pt-Sum[Coeff[table[[\[Xi]]],\[Lambda]],{\[Xi],1,t-1}];
          ),
(list=SumVariable[\[Kappa],\[Lambda]];
list2=Map[(#-\[Lambda])&,list];
list3=Map[Cases[#,Except[0]]&,list];
list3=Map[Sort,list3];
list3=Map[Reverse,list3];
\[Rho]=RHO[\[Kappa]]-RHO[\[Lambda]];
pt=Abs[list2];
t=Map[Apply[Plus,#]&,pt];
pt=Map[Flatten[Position[#,x_/;TrueQ[x!=0]]]&,pt];
pt=Map[\[Lambda][[#]]&,pt];
pt=Map[Apply[Subtract,#]&,pt];
pt=pt+t;
list2=pt/\[Rho];
return=Sum[list2[[\[Xi]]]Coeff[\[Kappa],list3[[\[Xi]]]],{\[Xi],1,Length[list3]}];)]
];
return
];


RHO[partition_]:=Sum[partition[[i]](partition[[i]]-i),{i,1,Length[partition]}]


AddZeros[list1_,list2_]:=Module[
{L1=list1,L2=list2,m=Length[list1],n=Length[list2],l,table},
l=Abs[m-n];
table=ConstantArray[0,l];
If[m>n,L2=Join[L2,table],L1=Join[L1,table]];
{L1,L2}
]


SumVariable[\[Kappa]_,\[Lambda]_]:=Module[
{n=Apply[Plus,\[Kappa]],m=Length[\[Lambda]],table1,table2,
table3,table4,table5,positiontable,\[Xi]},
table1=IntegerPartitions[n];
table2=Tuples[Table[\[Xi],{\[Xi],0,n}],m];
table3=Map[Apply[Plus,#]&,table2];
positiontable=Flatten[Position[table3,n]];
table2=table2[[positiontable]];
table3=Map[(#-\[Lambda])&,table2];
table4=Pick[table3,Map[Count[#,x_/;x!=0]==2&,table3]];
table5=Map[SelectFirst[#,#!=0&]&,table4];
positiontable=Position[table5,_?(#>0&)]//Flatten;
table4=table4[[positiontable]];
table3=Map[(#+\[Lambda])&,table4];
table2=Map[Cases[#,x_/;x>0]&,table3];
table2=Map[Sort[#,#1>#2&]&,table2];
table2=Map[Position[table1,#][[1,1]]&,table2];
n=Position[table1,\[Kappa]][[1,1]];
m=Position[table1,\[Lambda]][[1,1]];
positiontable=Flatten[Position[table2,_?(m>#>=n &)]];
table2=table3[[positiontable]]
];


ACal[p_List]:=Module[
{q=DeleteDuplicates[p],m},
m=Map[Count[p,#]&,q];
m=Map[Factorial,m];
Apply[Times,m]
];


PartitionPochhammer[a_,p_List]:=Module[
{l=Length[p],i},
Product[Pochhammer[a-(i-1)/2,p[[i]]],{i,1,l}]
];


HypergeometricPFQMatrix[a_List,b_List,Y_]:=
Sum[Sum[Product[,]/Product[],{m,1,Length[IntegerPartitions[n]]}],{n,0,Infinity}]
