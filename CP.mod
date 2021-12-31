//HourlyA is slow due to the production energy price calculation.
//The most efficient one: if the duration of the task a[i] is known (say, D[i]), 
//you could pre-compute a piecewise linear function C[i](t) that gives the cost of task when started at a date t, 
//that is the sum of the cost function (known) between t and t+D[i]. 
//then use startEval(a[i],C[i]) as cost to minimize. 
using CP;
int nbProcess = ...;
int nbJobs = ...;
int nbMchs = ...;
range Mchs = 1..nbMchs; 
range Opss = 1..nbProcess; 
range Jobs = 1..nbJobs; 

int Process1[Jobs] = ...;
int pidle[Mchs] = ...;
int EnergyS[Mchs] = ...;
int TB[Mchs] = ...;
int x[Mchs][Jobs][Opss] = ...;
int ptime[Mchs][Jobs][Opss] = ...;
float power1[Mchs][Jobs][Opss] = ...;
int P = 10;// common power
int mspan=36;
int pm_s[m in Mchs]=mspan-(nbMchs-m)*ftoi(round(mspan/nbMchs));  //start time of preventive maintenance
execute {
  pm_s[1]=4;
  pm_s[nbMchs]=mspan;
}
int pm_e[m in Mchs]=pm_s[m]+4;//end time of preventive maintenance
execute {
writeln ("m","\t", "down_s","\t","down_e");
for (var m in Mchs) 
 writeln (m,"\t",pm_s[m],"\t", pm_e[m]);
}

stepFunction fDown[m in Mchs]=stepwise {100->pm_s[m]; 0->pm_e[m]; 100};
//dvar interval decoration size 9  intensity fDown;

execute {
for(var o in Opss) for(var m in Mchs) for(var j in Jobs) 
	if(ptime[m][j][o]>0)
   	   ptime[m][j][o]=Opl.ftoi(Opl.round(ptime[m][j][o]/10));  // /10
//writeln(ptime);
}	

//############## Dynamic Energy Price Related ##############
int days=5*3;
range hrs=0..24*days-2;
int horizon=days*24;  
int p[0..23]=[26,26,27,26,26,29,36,46,44,39,53,47,42,42,40,39,48,67,78,80,81,73,63,48];
int ep[0..horizon-1];
execute {
for(var h=0;h<=23;h++)
	for(var d=0;d<=days-1;d++)
		ep[d*24+h]=p[h];	
//writeln("ep",ep);
}
//pwlFunction EnergyPrice = piecewise(h in hrs) { ep[h+1]- ep[h]-> h+1; 0}(0,ep[0]); 
//execute{writeln(EnergyPrice)};

int cumEndingAtT[0..horizon-1];
execute {
for(var h=0;h<=horizon-1;h++)
	for(var t=1;t<=h;t++)
		cumEndingAtT[h]+=ep[t-1];	
//writeln("cumEndingAtT",cumEndingAtT);
}
pwlFunction FcumEndingAtT = piecewise(h in hrs) { cumEndingAtT[h+1]- cumEndingAtT[h]-> h+1; 0}(0,cumEndingAtT[0]); 
// ########################################################

tuple Operation {
  key int id; 
  key int jobId; // Job id
  key int opId;  // Operation id
} {Operation} Ops;
execute {
var k=1;
for(var j in Jobs) for(var o in Opss) Ops.add(k++,j,o);
}	

tuple Mode {
  key int id; 
  key int mch; 
  int pt; //processing time
  int po; //power      
} {Mode} Modes;
execute {
for(var o in Ops) for(var m in Mchs) 
	if(x[m][o.jobId][o.opId]==1)
   	   Modes.add(o.id,m,ptime[m][o.jobId][o.opId],10*power1[m][o.jobId][o.opId]); 
}	

//############## Dynamic Energy Price Related for Speedy Computation##############
tuple tcumEStartingAtT {
  key int id; 
  key int m;
  key int t;
  int e; // sum of energy price when oper id on machine m starts at time t  
} {tcumEStartingAtT} cumEStartingAtT;
int t0Price[Mchs][1..max(md in Modes) md.id];

execute {
var sumPrice=0;
for(var o in Ops) for(var m in Mchs) 
	if(x[m][o.jobId][o.opId]==1)
		for(var t in hrs) if(t<=24*days-ptime[m][o.jobId][o.opId]-1) {
			for(var h=t; h<=t+ptime[m][o.jobId][o.opId]-1; h++) sumPrice+=ep[h];
   	   	   	cumEStartingAtT.add(o.id,m,t,sumPrice);
   	   	   	if(t==0) t0Price[m][o.id]=sumPrice;
   	   	   	sumPrice=0;	
        }        	   	   		
//writeln(t0Price);
//writeln(cumEStartingAtT);
}
pwlFunction CumPrice[md in Modes] = 
	piecewise(c1,c2 in cumEStartingAtT: c1!=c2 && c1.id==c2.id && c1.m==c2.m && c1.t+1 ==c2.t && md.mch==c1.m && md.id==c1.id) 
	{ c2.e - c1.e -> c1.t+1; 0}(0, t0Price[md.mch][md.id]);
		
// ########################################################



// Position of last operation of job j
int jlast[j in Jobs] = max(o in Ops: o.jobId==j) o.opId;
dvar interval ops[Ops] in 0..240 ; 
dvar interval modes[md in Modes] optional size md.pt intensity fDown[md.mch];
dvar interval makespan in 0..240;
dvar sequence seqMchs[m in Mchs] 
 in  all(md in Modes: md.mch == m) modes[md];
	 	           
dexpr int cmax=  max(j in Jobs, o in Ops: o.opId==jlast[j]) endOf(ops[o]);

//calculate the common energy from time 0 and cmax 
dexpr float energy_common= P*endEval(makespan, FcumEndingAtT)/10;
dexpr float energy_prod=sum(md in Modes) startEval(modes[md], CumPrice[md])*md.po/10;
dexpr float energy_idle_in_prod=sum(md in Modes) startEval(modes[md], CumPrice[md])*pidle[md.mch]/10;
dexpr float energy_idle=(sum(m in Mchs) endEval(makespan, FcumEndingAtT)*pidle[m]/10) - energy_idle_in_prod; 
dexpr float energy_total=energy_common + energy_prod + energy_idle;

execute {
  cp.param.TimeLimit = 5;
  cp.param.Workers = 4;
  cp.param.LogVerbosity=21;  
  cp.param.TemporalRelaxation = "On";
  cp.param.NoOverlapInferenceLevel = "Extended"  
}

minimize staticLex(cmax, energy_total);
//minimize  energy_total;
subject to {

  startOf(makespan)==0;
  endOf(makespan)==cmax;
  		   	      
  forall (j in Jobs, o1 in Ops, o2 in Ops: o1.jobId==j && o2.jobId==j && o2.opId==1+o1.opId)
    endBeforeStart(ops[o1],ops[o2]);
  forall (o in Ops)
    alternative(ops[o], all(md in Modes: md.id==o.id) modes[md]);
  forall (m in Mchs)
    noOverlap(seqMchs[m]);
  forall (md in Modes)
    presenceOf(modes[md])*lengthOf(modes[md])==sizeOf(modes[md]);
 
 //md in Modes] optional size md.pt 
}
execute {
writeln("makespan        = ", cmax);
writeln("energy_common   = ", energy_common);
writeln("energy_prod     = ", energy_prod);
writeln("energy_idle     = ", energy_idle);
writeln("energy_total    = ", energy_total);

writeln("m"+"\t"+"j"+"\t"+"o" +"\t"+ "pw" +"\t"+ "pt"+"\t"+ "s"+"\t"+ "e");
for (var md in Modes) for(var o in Ops) 
  if(modes[md].present && md.id==o.id)  
    writeln(md.mch + "\t" + o.jobId +"\t"+ o.opId +"\t"+ md.po +"\t" + md.pt  
    +"\t"+ modes[md].start  +"\t"+ modes[md].end);
}