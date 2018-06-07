range allnode = 1..45;
range nfnode = 41..45;
range commonnode = 1..40;
range cnode = 42..45;
range pnode = 41..41;
range chain_type = 1..5;

float multiplier = 1;
float update_msg_cost = 0.2;
float init_cost = 0.4;

{string} Feature_Model = { "f1", "f2", "f3", "f4", "f5", "f6" };
{string} phy_feature = { "src", "f3", "f5", "f6", "sink" };
{string} vnf_feature = { "f3", "f5", "f6" };
{string} pnf_feature = { "f3" };
{string} impact_feature = { "f2", "f3", "f5", "f6" };
//string VNF[nf_feature] = ...;
{string} resource = ...;

//float Conectivity[allnode][allnode] = ...;
float Bandwidth[allnode][allnode] = ...;

float cnode_Capacity[cnode][resource] = ...;
float pnode_Capacity[pnode] = ...;
float node_using_cost[nfnode] = ...;
//float resource_using_cost[nfnode][resource] = ...;
float feature_failure_cost[chain_type][Feature_Model] = ...;
float resource_demand[vnf_feature][resource] = ...;
float rps[vnf_feature] = ...;
//float f_rs_influence[nf_feature][nf_feature] = ...;
float prop[phy_feature] = ...;
float f_net_influence[impact_feature][phy_feature][phy_feature] = ...;

int hoplimit = 18;
//h_s = 10000;
//s_r = 10000;
//s_e = 10000;
float r_r = 8000;
float n_r = 16000;

tuple CFC {
	int src;
	int sink;
	int type;
	float demand;
}
{CFC} new_cfc = ...;
{CFC} former_cfc = ...;
{CFC} cfc = new_cfc union former_cfc;    // 取并集

tuple PATH {
	int start;
	int end;
}
{PATH} path = { <s, e> | s, e in allnode : Bandwidth[s][e] > 0 };    // 因为双向, 所以不能硬性规定 s 与 e 的大小关系

tuple REQ {
	int src;
	int sink;
	int type;
	float demand;
	string r1;
	string r2;
}
{REQ} req = { <c.src, c.sink, c.type, c.demand, p, q> | c in cfc, p, q in phy_feature };
{REQ} former_req = { <c.src, c.sink, c.type, c.demand, p, q> | c in former_cfc, p, q in phy_feature };

int former_flow[former_req][path] = ...;

dvar int f_choice[cfc][Feature_Model] in 0..1;
dvar int used[nfnode] in 0..1;
//dvar int req[cfc][phy_feature] in 0..1;
dvar int allocate[cfc][phy_feature][allnode] in 0..1;
dvar int instance_count[cnode][vnf_feature] in 0..maxint;
dvar int flow[req][path] in 0..1;
dvar int flow_active[cfc][phy_feature][phy_feature] in 0..1;
//dvar int n_choice[cfc][allnode][phy_feature][phy_feature] in 0..1;
//dvar float rs_demand[cfc][nf_feature] in 0..infinity;
//dvar float net_demand[cfc][phy_feature][phy_feature] in 0..infinity;
dvar int flow_update[req][path] in 0..1;

dvar float CR;
dvar float CI;
dvar float CF;
dvar float CU;

constraint feature;
constraint type2;
constraint type3;
constraint type4;
constraint type5;
constraint srcnode;
constraint sinknode;
constraint alloclimit;
constraint alloc;
constraint node_use;
constraint demand_of_rps;
constraint demand_of_resource;
//constraint nodechoice;
constraint pathchoice;
constraint network;
constraint demand_of_network;
constraint update;

constraint cost;

minimize CF + CR + CU;

subject to {
	feature = forall( i in cfc ) {
	    f_choice[i]["f1"] == f_choice[i]["f2"] + f_choice[i]["f3"] + f_choice[i]["f4"];
        f_choice[i]["f4"] == f_choice[i]["f6"] + f_choice[i]["f5"];
	}
	type2 = forall( i in cfc : i.type == 2 ) {
		f_choice[i]["f2"] == 0;
		f_choice[i]["f4"] == 0;
	}
	type3 = forall( i in cfc : i.type == 3 ) {
		f_choice[i]["f2"] == 0;
		f_choice[i]["f3"] == 0;
		f_choice[i]["f6"] == 0;
	}
	type4 = forall( i in cfc : i.type == 4 ) {
		f_choice[i]["f2"] == 0;
		f_choice[i]["f3"] == 0;
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
	alloclimit = {
		forall( c in cfc, n in allnode : n not in cnode ) {
			allocate[c]["f5"][n] == 0;
			allocate[c]["f6"][n] == 0;
		}
		forall( c in cfc, n in allnode : n not in nfnode ) {
			allocate[c]["f3"][n] == 0;
		}
	}
	alloc = forall( c in cfc, p in vnf_feature ) {
	    sum( i in nfnode ) allocate[c][p][i] == f_choice[c][p];
	}
	node_use = forall( i in nfnode, c in cfc, p in vnf_feature ) {
		used[i] >= allocate[c][p][i];
	}
	demand_of_rps = {	
		forall( i in cnode, v in vnf_feature ) {
			instance_count[i][v] * rps[v] >= sum( c in cfc ) allocate[c][v][i] * c.demand * multiplier;
//			(instance_count[i][v] - 1) * rps[v] <= sum( c in cfc ) allocate[c][v][i] * prop[v] * c.demand * multiplier;
		}
		forall( i in pnode ) {
			pnode_Capacity[i] >= sum( c in cfc, p in pnf_feature ) allocate[c][p][i] * c.demand * multiplier;
		}
	}
	demand_of_resource = forall( i in cnode, re in resource ) {
		cnode_Capacity[i][re] >= sum( v in vnf_feature ) resource_demand[v][re] * instance_count[i][v];
	}
//	nodechoice = 
//		forall( n in allnode, c in cfc, im in impact_feature, p in phy_feature, q in phy_feature : 
//				f_net_influence[im][p][q] == 1 ) {
//			n_choice[c][n][p][q] >= allocate[c][p][n] * f_choice[c][im];
//	}
//	network = 
//		forall( n in allnode, c in cfc, p in phy_feature, q in phy_feature, im in impact_feature : f_net_influence[im][p][q] > 0) {
//			sum( m in allnode : Bandwidth[m][n] > 0 ) n_choice[c][m][p][q] == 
//			f_choice[c][im] * (1 - allocate[c][p][n] - allocate[c][q][n] + n_choice[c][n][p][q]);
//	}
	pathchoice = {
		forall( c in cfc, p, q in phy_feature, im in impact_feature ) {
			sum( l in path ) flow[<c.src, c.sink, c.type, c.demand, p, q>][l] >= ( f_net_influence[im][p][q] > 0? 1: 0 ) * f_choice[c][im];
 		}			
 		forall( c in cfc, p, q in phy_feature ) {
			sum( l in path ) flow[<c.src, c.sink, c.type, c.demand, p, q>][l] <= 
			sum( im in impact_feature ) ( f_net_influence[im][p][q] > 0? 1: 0 ) * f_choice[c][im] * hoplimit;
		}	
	}		
	network = {
		forall( c in cfc, im in impact_feature, p, q in phy_feature : f_net_influence[im][p][q] > 0 ) {
			flow_active[c][p][q] >= f_choice[c][im];		
		}
		forall( c in cfc, p, q in phy_feature, n in allnode ) {
			(sum( m in allnode : Bandwidth[m][n] > 0 ) flow[<c.src, c.sink, c.type, c.demand, p, q>][<m, n>]) + allocate[c][p][n] <= 
			(sum( k in allnode : Bandwidth[n][k] > 0 ) flow[<c.src, c.sink, c.type, c.demand, p, q>][<n, k>]) + allocate[c][q][n] + 
			(1 - flow_active[c][p][q]);
			(sum( k in allnode : Bandwidth[n][k] > 0 ) flow[<c.src, c.sink, c.type, c.demand, p, q>][<n, k>]) + allocate[c][q][n] <= 
			(sum( m in allnode : Bandwidth[m][n] > 0 ) flow[<c.src, c.sink, c.type, c.demand, p, q>][<m, n>]) + allocate[c][p][n] + 
			(1 - flow_active[c][p][q]);
			(sum( m in allnode : Bandwidth[m][n] > 0 ) flow[<c.src, c.sink, c.type, c.demand, p, q>][<m, n>]) + allocate[c][p][n] <= 1;
			(sum( k in allnode : Bandwidth[n][k] > 0 ) flow[<c.src, c.sink, c.type, c.demand, p, q>][<n, k>]) + allocate[c][q][n] <= 1;
		}
	}
	demand_of_network = {
		forall( <m, n> in path : m in cnode || n in cnode ) {
			sum( c in cfc, p, q in phy_feature ) flow[<c.src, c.sink, c.type, c.demand, p, q>][<m, n>] * prop[p] * c.demand <= n_r;
		}
		forall( <m, n> in path : m in commonnode && n in commonnode ) {
			sum( c in cfc, p, q in phy_feature ) flow[<c.src, c.sink, c.type, c.demand, p, q>][<m, n>] * prop[p] * c.demand <= r_r;
		}
	}
//	network = {
//		forall( c in cfc, p in phy_feature, q in phy_feature, n in allnode ) {
//			(sum( m in allnode : Bandwidth[m][n] > 0 ) flow[c][p][q][<m, n>]) + allocate[c][p][n] + 
//				(1 - sum( im in impact_feature ) f_choice[c][im] * f_net_influence[im][p][q]) == 
//			(sum( l in allnode : Bandwidth[n][l] > 0 ) flow[c][p][q][<n, l>]) + allocate[c][q][n] + 
//				(1 - sum( im in impact_feature ) f_choice[c][im] * f_net_influence[im][p][q]);
//		}
//	}		
	update = {
		forall( r in former_req, l in path ) {
			flow_update[r][l] == flow[r][l] * (1 - former_flow[r][l]);
		}
		forall( r in req, l in path : <r.src, r.sink, r.type, r.demand> in new_cfc ) {
			flow_update[r][l] == flow[r][l];
		}
	}	
	cost = {
		CF == sum( c in cfc, j in Feature_Model ) (1 - f_choice[c][j]) * feature_failure_cost[c.type][j];    // CF
	    CR == sum( n in nfnode ) used[n] * node_using_cost[n];    // CR
	    CI == sum( i in cnode, v in vnf_feature ) instance_count[i][v] * init_cost;    // CI
	    CU == sum( l in path, r in req ) flow_update[r][l] * update_msg_cost;    // CU	
	}
}	

//execute {
//	for(var m in nfnode) {
//		for(var n in commomnode) {
//			if(Bandwidth[m][n] > 0) {
//				Bandwidth[m][n] = n_r;	
//				Bandwidth[n][m] = n_r;
//			}	
//		}		
//	}
//	for(var m in commomnode) {
//		for(var n in commomnode) {
//			if(Bandwidth[m][n] > 0) {
//				Bandwidth[m][n] = r_r;	
//			}		
//		}		
//	}	
//}

execute PARAMS { cplex.tilim = 100; }


