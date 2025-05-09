############################
# airplane_assignment.mod  #
############################

set A;            # airplanes
set F;            # flights
set CONN within F cross F;

##### Parameters #####

# Flight data
param origin{F}, symbolic;    # origin airport code
param dest  {F}, symbolic;    # destination airport code
param dep   {F}, >= 0;        # departure time in minutes
param arr   {F}, >= 0;        # arrival  time in minutes
param Reach {A,F} binary;

# Plane data
param pos0  {A}, symbolic;    # each plane’s starting airport
param lease {A} >= 0;         # leasing revenue if plane is unused
param rev   {F,A} >= 0;       # revenue of assigning plane a to flight f
param cost  {F,A} >= 0;       # cost   of assigning plane a to flight f

##### Decision Variables #####

var x {f in F, a in A: Reach[a,f] = 1} binary;  # 1 if flight f is flown by plane a
var z {a in A, f in F: Reach[a,f] = 1} binary;  # 1 if flight f is the *first* flight for plane a
var y{a in A}         binary;  # 1 if plane a is leased out (not used)

##### Objective #####

maximize Profit:
    sum {a in A, f in F: Reach[a,f]=1}
      (rev[f,a] - cost[f,a]) * x[f,a]
  + sum {a in A} lease[a] * y[a]
;

##### Core Constraints #####

# 8) 
s.t. Connectivity {a in A, f in F: Reach[a,f]=1}:
    sum {g in F: Reach[a,g]=1 and (g,f) in CONN} x[g,a]
        + z[a,f]
 >= x[f,a];

# 1) 
s.t. AssignOnce {f in F}:
    sum {a in A: Reach[a,f]=1} x[f,a] = 1
;

# 2) 
s.t. LeaseOrUse {a in A}:
    sum {f in F: Reach[a,f]=1} x[f,a] <= card(F)*(1-y[a])
;

# 3) 
s.t. NoOverlap {a in A, f1 in F, f2 in F
      : Reach[a,f1] = 1
     and Reach[a,f2] = 1
     and f1 < f2
     and not (arr[f1] <= dep[f2]
              or arr[f2] <= dep[f1])}:
    x[f1,a] + x[f2,a] <= 1
;

# 4) 
s.t. Turnaround {a in A, f1 in F, f2 in F
      : Reach[a,f1] = 1
     and Reach[a,f2] = 1
     and f1 <> f2
     and dest[f1] = origin[f2]
     and arr[f1] + 60 > dep[f2]}:
    x[f1,a] + x[f2,a] <= 1
;


# 5) 
s.t. FirstFlightCount {a in A}:
    sum {f in F: Reach[a,f] = 1} z[a,f] = 1 - y[a]
;

# 6) 
s.t. FirstFlightOrigin {a in A, f in F: Reach[a,f]=1 and origin[f] != pos0[a]}:
    z[a,f] = 0
;

# 7) 
s.t. FirstFlightLink {a in A, f in F: Reach[a,f]=1}:
    z[a,f] <= x[f,a]
;
# 9) Each non-rented aircraft must make at least one flight back to the original airport
s.t. ReturnHome {a in A}:
    sum {f in F: dest[f] = pos0[a]} x[f,a] >= 1 - y[a];


