range allnode = 1..45;
range nfnode = 37..41;
range cnode = 38..41;
range pnode = 37..37;
range chain_type = 1..5;
//range num = 1..20;

float multiplier = 2;
float update_msg_cost = 4;

{string} Feature_Model = { "f1", "f2", "f3", "f4", "f5", "f6" };
{string} phy_feature = { "src", "f3", "f5", "f6", "sink" };
{string} impact_feature = { "f2", "f3", "f5", "f6" };
{string} VNF = ...;
{string} resource = ...;

float Bandwidth[allnode][allnode] = ...;
float cnode_Capacity[cnode][resource] = ...;
float pnode_Capacity[pnode] = ...;
float node_using_cost[nfnode] = ...;
float resource_using_cost[nfnode][resource] = ...;
float feature_failure_cost[chain_type][Feature_Model] = ...;
float resource_demand[VNF][resource] = ...;
float rps[VNF] = ...;

int f_net_influence[impact_feature][phy_feature][phy_feature] = ...;
int hoplimit = 18;

tuple CFC {
	int src;
	int sink;
	int type;
	float demand;
}
{CFC} cfc = ...;

//tuple PATH {
//	int start;
//	int end;
//}
//{PATH} path = { <s, e> | s, e in allnode : Bandwidth[s][e] > 0 };


//float resource_impact[Feature_Model][Feature_Model][resource] = ...;
//float network_impact[Feature_Model][Feature_Model][Feature_Model] = ...;


dvar int f_choice[cfc][Feature_Model] in 0..1;
dvar int used[nfnode] in 0..1;
//dvar int req[cfc][phy_feature] in 0..1;
dvar int allocate[cfc][phy_feature][allnode] in 0..1;
dvar int instance_count[cnode][VNF];
//dvar int flow[cfc][phy_feature][phy_feature][path] in 0..1;
dvar int n_choice[cfc][allnode][phy_feature][phy_feature] in 0..1;

constraint feature;
constraint type2;
constraint type3;
constraint type4;
constraint type5;
constraint srcnode;
constraint sinknode;
constraint alloc;
constraint node_use;
constraint demand_of_rps;
constraint demand_of_resource;
constraint nodechoice;
//constraint pathchoice;
constraint network;


minimize 
    sum( i in cfc, j in Feature_Model ) (1 - f_choice[i][j]) * feature_failure_cost[i.type][j] +    // CF
    sum( n in nfnode ) used[n] * node_using_cost[n] +    // CR
    sum( n in allnode, c in cfc, p in phy_feature, q in phy_feature ) n_choice[c][n][p][q] * update_msg_cost;    // CU

subject to {
	feature = forall( i in cfc ) {
	    f_choice[i]["f1"] == f_choice[i]["f2"] + f_choice[i]["f3"] + f_choice[i]["f4"];
        f_choice[i]["f4"] == f_choice[i]["f6"] + f_choice[i]["f5"];
	}
	type2 = forall( i in cfc : i.type == 2 ) {
		f_choice[i]["f2"] == 0;
//		f_choice[i]["f4"] == 0;
	}
	type3 = forall( i in cfc : i.type == 3 ) {
		f_choice[i]["f2"] == 0;
//		f_choice[i]["f3"] == 0;
//		f_choice[i]["f6"] == 0;
	}
	type4 = forall( i in cfc : i.type == 4 ) {
		f_choice[i]["f2"] == 0;
//		f_choice[i]["f3"] == 0;
	}
	type5 = forall( i in cfc : i.type == 5 ) {
		f_choice[i]["f2"] == 0;
		f_choice[i]["f3"] == 0;
		f_choice[i]["f5"] == 0;
	}
	srcnode = forall( c in cfc ) {
		allocate[c]["src"][c.src] == 1;
	}
	sinknode = forall( c in cfc ) {
		allocate[c]["sink"][c.sink] == 1;
	}
	alloc = forall( c in cfc, p in phy_feature : p != "src" && p != "sink") {
	    sum( i in nfnode ) allocate[c][p][i] == f_choice[c][p];
	}
	node_use = forall( i in nfnode, j in cfc, p in phy_feature ) {
		used[i] >= allocate[j][p][i];
	}
	demand_of_rps = {
		forall( i in cnode, v in VNF ) {
			instance_count[i][v] * rps[v] >= sum( c in cfc, p in phy_feature ) allocate[c][p][i] * c.demand * multiplier;
		}
		forall( i in pnode ) {
			pnode_Capacity[i] >= sum( c in cfc, p in phy_feature ) allocate[c][p][i] * c.demand * multiplier;
		}
	}
	demand_of_resource = forall( i in cnode, re in resource ) {
		cnode_Capacity[i][re] >= sum( v in VNF ) resource_demand[v][re] * instance_count[i][v];
	}
	nodechoice = 
		forall( n in allnode, c in cfc, im in impact_feature, p in phy_feature, q in phy_feature : 
				f_net_influence[im][p][q] == 1 ) {
			n_choice[c][n][p][q] >= allocate[c][p][n] * f_choice[c][im];
	}
//	network = 
//		forall( n in allnode, c in cfc, p in phy_feature, q in phy_feature, im in impact_feature : f_net_influence[im][p][q] > 0) {
//			sum( m in allnode : Bandwidth[m][n] > 0 ) n_choice[c][m][p][q] == 
//			f_choice[c][im] * (1 - allocate[c][p][n] - allocate[c][q][n] + n_choice[c][n][p][q]);
//	}
//	pathchoice = {
//		forall( c in cfc, p in phy_feature, q in phy_feature, im in impact_feature ) {
//			sum( l in path ) flow[c][p][q][l] >= ( f_net_influence[im][p][q] > 0? 1: 0 ) * f_choice[c][im];
// 		}			
// 		forall( c in cfc, p in phy_feature, q in phy_feature ) {
//			sum( l in path ) flow[c][p][q][l] <= 
//			sum( im in impact_feature ) ( f_net_influence[im][p][q] > 0? 1: 0 ) * f_choice[c][im] * hoplimit;
//		}	
//	}	
//	network = {
//		forall( c in cfc, p in phy_feature, q in phy_feature, n in allnode ) {
//			sum( m in allnode : Bandwidth[m][n] > 0 ) flow[c][p][q][<n, m>] == 2 - allocate[c][p][n] - allocate[c][q][n];
//		}
//	}
}
  

           

// 最大求解时间 100s
execute PARAMS {
	cplex.tilim = 1000;
}	
