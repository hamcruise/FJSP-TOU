int nbProcess = ...;
int nbJobs = ...;
int nbMchs = ...;
range Mchs = 1..nbMchs; 
range Opss = 1..nbProcess; 
range Jobs = 1..nbJobs; 
range Pos = 1..nbProcess*nbJobs; 
//range Pos2 = 1..nbProcess*nbJobs-1; 

int Process1[Jobs] = ...;
int pidle[Mchs] = ...;
int EnergyS[Mchs] = ...;
int TB[Mchs] = ...;
int x[Mchs][Jobs][Opss] = ...;
int ptime[Mchs][Jobs][Opss] = ...;
float power1[Mchs][Jobs][Opss] = ...;
int P = 10;// common power
//int N = 3; //max count of offs
//int bM = 9999;
int T = 120*3;

int mspan=...;
int pm_s[m in Mchs]=mspan-(nbMchs-m)*ftoi(round(mspan/nbMchs));  //start time of preventive maintenance
execute {
  pm_s[1]=4;
  pm_s[nbMchs]=mspan;
}
int pm_e[m in Mchs]=pm_s[m]+4;//end time of preventive maintenance

//int T = sum(j in Jobs,o in Opss) max(m in Mchs)ptime[m][j][o];
int a = 0;
range Times = 0..T-1; 
range Times1 = 0..T-2;
range Times2 = 1..T-1; 
 
int days=5*3;

//range hrs=1..24*days-1;

int horizon=days*24; 

int p[1..24]=[26,26,27,26,26,29,36,46,44,39,53,47,42,42,40,39,48,67,78,80,81,73,63,48];

int ep[1..horizon];

execute {
for(var h=1;h<=24;h++)
    for(var d=0;d<=days-1;d++)
        ep[d*24+h]=p[h];
//writeln("ep",ep);
}


tuple Operation {
  key int j; // Job id
  key int o;  // Operation id
} {Operation} Ops;
execute {
for(var j in Jobs) for(var o in Opss) Ops.add(j,o);
}	

tuple Mode {
  key int j; 
  key int o; 
  key int m; 
  int pt; //processing time
  int po; //power      
} {Mode} Modes;


execute {
  for(var o in Opss) for(var m in Mchs) for(var j in Jobs)
    if (ptime[m][j][o] > 0)
      ptime[m][j][o] =Opl.ftoi(Opl.round(ptime[m][j][o]/10));
 // writeln("ptime",ptime);    
}

execute {
for(var o in Ops) for(var m in Mchs) 
	if(x[m][o.j][o.o]==1)
   	   Modes.add(o.j, o.o, m,ptime[m][o.j][o.o],10*power1[m][o.j][o.o]); 
}	

execute  { cplex.tilim = 60; cplex.epagap=1e-20; cplex.epgap=1e-20;
}

int OOPairs[Ops][Ops];


execute {
  for(var o in Ops) for(var q in Ops){ 
    OOPairs[o][q]=0;
    if (o != q){
    for(var m in Mchs){ 
      if(x[m][o.j][o.o]==1 && x[m][q.j][q.o]==1){
        OOPairs[o][q]=1;
        break;    
      }
    }      
    if(a>0) OOPairs.add(o.j, o.o, q.j, q.o);    	
  }          
  }	    
}

// Position of last operation of job j
int jlast[j in Jobs] = max(o in Ops: o.j==j) o.o;
//dvar boolean W[Ops][Mchs][Times];
dvar boolean W[Modes][Times];
dvar boolean F[Mchs][Times];
dvar boolean L[Times];
dvar float+ cmax;
dexpr float energy_common=sum(t in Times) P*ep[t+1]*L[t]/10;
dexpr float energy_prod=sum(md in Modes, r,t in Times: r >=t && r <= t+md.pt-1) md.po*ep[r+1]*W[md][t]/10;
dexpr float energy_idle=sum(m in Mchs, t in Times) pidle[m]*ep[t+1]*L[t]/10-sum(md in Modes, r,t in Times: r >=t && r <= t+md.pt-1) pidle[md.m]*ep[r+1]*W[md][t]/10;
dexpr float energy_total=energy_common+energy_prod + energy_idle;
//minimize cmax;
//minimize staticLex(cmax, energy_total);
minimize 1000000*cmax + energy_total;
subject to {
//  forall (o in Ops: o.o==jlast[o.j]) sum(t in Times, md in Modes: md.j==o.j && md.o==o.o && t <= T-md.pt)W[md][t]*(t+md.pt) <= cmax;
  forall (o1, o2 in Ops: o1.j==o2.j && o1.o+1==o2.o) sum(t in Times, md1 in Modes: md1.j==o1.j && md1.o==o1.o && t <= T-md1.pt)W[md1][t]*(t+md1.pt) <= sum(t in Times, md2 in Modes: md2.j==o2.j && md2.o==o2.o && t <= T-md2.pt)W[md2][t]*t;
  forall (o in Ops) sum(t in Times, md in Modes: md.j==o.j && md.o==o.o && t <= T-md.pt)W[md][t] == 1;
  forall (m in Mchs, t in Times) sum(md in Modes, r in Times: md.m==m && r>=t-md.pt+1 && r <=t) W[md][r] <= 1;

  forall (t in Times1) L[t] >= L[t+1];
  forall (md in Modes, r,t in Times:r==t+md.pt-1) L[r] >= W[md][t];
  cmax == sum(t in Times) L[t];
  forall (o in Ops) sum(t in Times, md in Modes: md.j==o.j && md.o==o.o && t >= pm_s[md.m]-md.pt+1 && t <= pm_e[md.m]-1)W[md][t] == 0;  
} 

execute {
writeln("makespan        = ", cmax);
writeln("energy_common   = ", energy_common);
writeln("energy_prod     = ", energy_prod);
writeln("energy_idle     = ", energy_idle);
writeln("energy_total    = ", energy_total);

  writeln("m"+"\t"+"j"+"\t"+"o"+"\t"+"pw"+"\t" +"pt"+"\t" +"s"+"\t"+"e");
  for(var md in Modes) for(var t in Times)
    if (W[md][t] == 1)
	  writeln(md.m+"\t"+md.j+"\t"+md.o+"\t"+md.po+"\t"+md.pt+"\t"+t+"\t"+(t+md.pt));
}
