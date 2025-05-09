set A;            # airplanes
set F;            # flights
set Airports;     # airports



##### Parameters #####

# Flight data
param origin {F} symbolic;    # origin airport code
param dest   {F} symbolic;    # destination airport code
param dep    {F} >= 0;        # departure time in minutes
param arr    {F} >= 0;        # arrival time in minutes

# Generate CONN dynamically
set CONN within {F,F} := {(f,g) in F cross F: dest[f] = origin[g] and arr[f] + 60 <= dep[g]};

# Plane data
param pos0   {A} symbolic;    # each plane’s starting airport
param lease  {A} >= 0;        # leasing revenue if plane is unused
param rev    {F,A} >= 0;      # revenue of assigning plane a to flight f
param cost   {F,A} >= 0;      # cost of assigning plane a to flight f

##### Decision Variables #####

var x {f in F, a in A} binary;  # 1 if flight f is flown by plane a
var z {a in A, f in F, g in F: (f,g) in CONN} binary;  # 1 if plane a flies flight f then g
var y {a in A} binary;          # 1 if plane a is leased out (not used)

##### Objective #####

maximize Profit:
    sum {f in F, a in A} (rev[f,a] - cost[f,a]) * x[f,a]
  + sum {a in A} lease[a] * y[a];

##### Core Constraints #####

# 1) Every flight is flown at most once
s.t. AssignOnce {f in F}:
    sum {a in A} x[f,a] <= 1;

# 2) A plane is either used or leased, not both
s.t. LeaseOrUse {a in A}:
    sum {f in F} x[f,a] + y[a] <= 1;

# 3) Initial position: first flight must depart from pos0
s.t. InitialFlow {a in A, f in F: origin[f] != pos0[a]}:
    x[f,a] <= 0;

# 4) Flow balance: number of arrivals equals departures at each airport
s.t. FlowBalance {a in A, k in Airports}:
    sum {f in F: dest[f] = k} x[f,a] = sum {g in F: origin[g] = k} x[g,a];

# 5) Connection: ensure valid flight connections
s.t. Connection {a in A, f in F}:
    sum {g in F: (f,g) in CONN} z[a,f,g] = sum {g in F: (f,g) in CONN} x[g,a];

# 6) Connection consistency: z implies x for both flights
s.t. ConnectionConsistency {a in A, f in F, g in F: (f,g) in CONN}:
    z[a,f,g] <= x[f,a];

s.t. ConnectionConsistency2 {a in A, f in F, g in F: (f,g) in CONN}:
    z[a,f,g] <= x[g,a];
    
# 7) Each non-rented aircraft must make at least one flight back to the original airport
s.t. ReturnHome {a in A}:
    sum {f in F: dest[f] = pos0[a]} x[f,a] >= 1 - y[a];