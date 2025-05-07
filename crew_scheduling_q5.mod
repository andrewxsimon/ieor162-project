# crew_scheduling_return.mod
# Crew scheduling with return-to-base for captains and first officers

set C;               # captains
set P;               # first officers
set F;               # flights

param origin{F}, symbolic;
param dest{F},   symbolic;
param dep{F},    >= 0;
param arr{F},    >= 0;

param capPos0{C}, symbolic;
param foPos0{P},   symbolic;
param capCost{F, C} >= 0;
param foCost{F, P} >= 0;

param bigM := 1440;

var xC{f in F, c in C} binary;
var xP{f in F, p in P} binary;
var usedC{c in C}    binary;
var usedP{p in P}    binary;
var startC{c in C}   >= 0;
var endC{c in C}     >= 0;
var startP{p in P}   >= 0;
var endP{p in P}     >= 0;

minimize TotalCost:
    sum {f in F, c in C} capCost[f,c] * xC[f,c]
  + sum {f in F, p in P} foCost[f,p] * xP[f,p]
;

# Assignment
s.t. OneCap {f in F}: sum {c in C} xC[f,c] = 1;
s.t. OneFO  {f in F}: sum {p in P} xP[f,p] = 1;

# Used flags
s.t. DefUsedC1 {c in C}: sum {f in F} xC[f,c] <= card(F) * usedC[c];
s.t. DefUsedC2 {c in C}: sum {f in F} xC[f,c] >= usedC[c];
s.t. DefUsedP1 {p in P}: sum {f in F} xP[f,p] <= card(F) * usedP[p];
s.t. DefUsedP2 {p in P}: sum {f in F} xP[f,p] >= usedP[p];

# 60-min briefing
s.t. NoOverlapC {c in C, f1 in F, f2 in F: f1 < f2
      and not (arr[f1] + 60 <= dep[f2] or arr[f2] + 60 <= dep[f1])}:
    xC[f1,c] + xC[f2,c] <= 1;
s.t. NoOverlapP {p in P, f1 in F, f2 in F: f1 < f2
      and not (arr[f1] + 60 <= dep[f2] or arr[f2] + 60 <= dep[f1])}:
    xP[f1,p] + xP[f2,p] <= 1;

# Connectivity
param isHomeC{c in C, f in F} binary := if origin[f] = capPos0[c] then 1 else 0;
param isHomeP{p in P, f in F} binary := if origin[f] = foPos0[p]  then 1 else 0;

s.t. ConnC {c in C, f in F}:
    sum {g in F: dest[g] = origin[f] and arr[g] + 60 <= dep[f]} xC[g,c]
  + isHomeC[c,f]
  >= xC[f,c];

s.t. ConnP {p in P, f in F}:
    sum {g in F: dest[g] = origin[f] and arr[g] + 60 <= dep[f]} xP[g,p]
  + isHomeP[p,f]
  >= xP[f,p];

# Duty limits
s.t. StartLinkC {c in C, f in F}: startC[c] <= dep[f] + bigM * (1 - xC[f,c]);
s.t. EndLinkC   {c in C, f in F}: endC[c]   >= arr[f] - bigM * (1 - xC[f,c]);
s.t. RegCap    {c in C}: endC[c] - startC[c] <= 480 * usedC[c];

s.t. StartLinkP {p in P, f in F}: startP[p] <= dep[f] + bigM * (1 - xP[f,p]);
s.t. EndLinkP   {p in P, f in F}: endP[p]   >= arr[f] - bigM * (1 - xP[f,p]);
s.t. RegFO     {p in P}: endP[p] - startP[p] <= 480 * usedP[p];

# Return-to-base: last-flight markers
var lC{c in C, f in F} binary;
var lP{p in P, f in F} binary;

# Exactly one last flight if used
s.t. LastFlightCountC {c in C}: sum {f in F} lC[c,f] = usedC[c];
s.t. LastFlightCountP {p in P}: sum {f in F} lP[p,f] = usedP[p];

# Last flight must end at home
s.t. LastFlightDestC {c in C, f in F: dest[f] != capPos0[c]}:
    lC[c,f] = 0;
s.t. LastFlightDestP {p in P, f in F: dest[f] != foPos0[p]}:
    lP[p,f] = 0;

# Link last-flight to assignment
s.t. LastLinkC {c in C, f in F}: lC[c,f] <= xC[f,c];
s.t. LastLinkP {p in P, f in F}: lP[p,f] <= xP[f,p];

end;