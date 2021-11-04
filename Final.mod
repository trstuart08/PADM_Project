param n_suppliers;
param n_trucks; #1 LDD and 5 HCV
param n_property; # wt and volume for supplier and truck
param n_trips; # number of trips

# all sets definition
set suppliers:= 1..n_suppliers;
set trips:=1..n_trips;
set truck:=1..n_trucks;
set property := 1..n_property;
set ARCS := {i in suppliers, j in suppliers : i == j} ; 

#parameters definition
param distance {suppliers,suppliers};
param FCT {truck};
param VC {truck};
param S;
param demand {suppliers,property};
param teff;
param capacity {truck,property};
param tripCost {trips};
param max_dist;
param profit;


#Variables definition
var X{suppliers,suppliers,trips,truck} >= 0 <=1 ; #%(decimal between 0 and 1 of load from supplier to supplier in trip d in truck t
var Y{trips,truck} binary ; #to caputure if truck t is run in trip d if X >0
var Z{suppliers,suppliers,trips,truck} binary ; #indicate movement from supplier to supplier on trip d in truck t
var R{suppliers,trips,truck} >=0 integer ; # rank of supplier in trip d for a truck t

#These variables are only for ease of visualization and calculation
var truckeff{trips,truck} ; # efficiency of supplier in trip d for a truck t
var suppload{suppliers,property};# load from a supplier s in terms or property p  
var A; #Distance wise truck maintainance cost
var B; #variable costs

#objective function
minimize total_costs : ( (sum {d in trips, t in truck}  tripCost[d]*Y[d,t]) + A + B ) * profit ;  

#constraints
subject to 

#0 X is 0 when i == j , no load from supplier i to j when i == j
const_0 {(i,j) in ARCS, d in trips, t in truck} : X[i,j,d,t] = 0 ;

#1 Y to be made 1 if any X > 0
const_1 {i in suppliers,j in suppliers, d in trips, t in truck} : Y[d,t] >= X[i,j,d,t] ; 

#2 Z to be made 1 if any X > 0
const_2 {i in suppliers,j in suppliers, d in trips, t in truck } : Z[i,j,d,t] >= X[i,j,d,t] ; 

#3 For all suppliers i , total percentage of load for supplier i for a week should be >= 1 
const_3 {i in suppliers} : sum{j in suppliers, d in trips, t in truck} X[i,j,d,t] >= 1 ;

#4 The capacity of truck occupied by all suppliers (to all other suppliers) in a trip should
#be less than equal to total capacity of property p for every d in trips and truck t
const_4 {d in trips, t in truck, p in property} : sum{i in suppliers} ( sum{ j in suppliers } X[i,j,d,t] * demand[i,p] ) <= teff * capacity[t,p] ;

#5 truck should not run more than max km in a week. 
const_5 {t in truck} : sum { i in suppliers,j in suppliers, d in trips } Z[i,j,d,t] * distance[i,j] <= max_dist ;

#6 sub tour elimination in each trip d and truck t
# such if there is a path from supplier i to j, the rank of j is greater than i
const_6 {i in suppliers,j in suppliers, d in trips, t in truck : j >= 2} : R[j,d,t] >= R[i,d,t] + 1 - n_suppliers * ( 1 - Z[i,j,d,t] ) ;

#7 Rank R initialization for every trip in d and truck in t
const_7 {d in trips , t in truck} : R[1,d,t] = 1 ; 

#8 vehicle moves from the warehouse , therefore Z [i,j,d,t] where i == 1 should always be true 
const_8 {i in suppliers , d in trips ,  t in truck : i = 1} : sum{j in suppliers} Z[i,j,d,t] = 1 ;

#9 Balancing constraint (from reference 2) for every supplier h except warehouse,  incoming leg is equal to outgoing legs (whatever comes in goes out)
const_9 {h in suppliers, d in trips, t in truck : h != 1} : sum{i in suppliers} Z[i,h,d,t] = sum{j in suppliers} Z[h,j,d,t] ;  

#Below constraints is to show the some calculated variables from the model

#1 show truck efficiencies (max % of each property p) for every truck t and trip d
show_1 { d in trips, t in truck, p in property} : sum{i in suppliers , j in suppliers} X[i,j,d,t] * demand[i,p] / capacity[t,p] <= truckeff[d,t] ;

#2 The suppload[i,p] is equal to the amount of demand of supplier i that is fullfilled by
# movement of load from i to all suppliers j in all trips d in all trucks t    
show_2 {i in suppliers, p in property} : sum{j in suppliers, d in trips,t in truck} X[i,j,d,t] * demand[i,p]  <= suppload[i,p] ; 

#3 The cost A is net fixed cost related to all trucks used in all trips 
# (The total distance is calculated for each trip d and truck t, and then divided by the average speed to get total hour/trip
# Each hour per trip has a fixed cost related which is multiplied.  
show_3 : sum {i in suppliers,j in suppliers,d in trips, t in truck} Z[i,j,d,t] * distance[i,j] * FCT[t] / S = A ;

# 4The cost B total of is the variable cost of truck t in all trips covering all the distacnes 
#between supplier i and supplier j, which is calculated by multiplying the cost of running truck
#t per km and the distance covered from all suppliers i to all suppliers j.  
show_4 : sum {i in suppliers,j in suppliers, d in trips, t in truck} VC[t] * Z[i,j,d,t] * distance[i,j] = B;



