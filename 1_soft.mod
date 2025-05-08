############################
# airplane_assignment.mod  #
############################

set A;            # airplanes
set F;            # flights

##### Parameters #####

# Flight data
param origin{F}, symbolic;    # origin airport code
param dest  {F}, symbolic;    # destination airport code
param dep   {F}, >= 0;        # departure time in minutes
param arr   {F}, >= 0;        # arrival  time in minutes

# Plane data
param pos0  {A}, symbolic;    # each plane’s starting airport
param lease {A} >= 0;         # leasing revenue if plane is unused
param rev   {F,A} >= 0;       # revenue of assigning plane a to flight f
param cost  {F,A} >= 0;       # cost   of assigning plane a to flight f

##### Decision Variables #####

var x{f in F, a in A} binary;  # 1 if flight f is flown by plane a
var z{a in A, f in F} binary;  # 1 if flight f is the *first* flight for plane a
var y{a in A}         binary;  # 1 if plane a is leased out (not used)

##### Objective #####

maximize Profit:
    sum {f in F, a in A} (rev[f,a] - cost[f,a]) * x[f,a]
  + sum {a in A} lease[a] * y[a]
;

##### Core Constraints #####

# 1) Every flight is flown exactly once
s.t. AssignOnce {f in F}:
    sum {a in A} x[f,a] = 1
;

# 2) A plane is either used or leased, not both
s.t. LeaseOrUse {a in A}:
    sum {f in F} x[f,a] <= card(F) * (1 - y[a])
;

# 3) No time overlap: any two flights that overlap (even at the same 
#    airport) cannot be on the same plane
s.t. NoOverlap {a in A, f1 in F, f2 in F: f1 < f2
      and not (arr[f1] + 60 <= dep[f2] 
               or arr[f2] + 60 <= dep[f1])}:
  x[f1,a] + x[f2,a] <= 1
;

# 4) Turnaround: if dest[f1]=origin[f2], still need 60 min gap
s.t. Turnaround {a in A, f1 in F, f2 in F:
      f1 != f2
    and dest[f1] = origin[f2]
    and arr[f1] + 60 > dep[f2]}:
  x[f1,a] + x[f2,a] <= 1
;

