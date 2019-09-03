#this is the code to an outbreak simulation on a network
#the spread of EVD is assumed stochastic as per best guesses from literature and dependent on demographic factors
#vaccines are administered according to a set vaccination policy
#actors in the simulation choose to adhere to vaccination policy, or reject it, based on a social weighted replicator function
library(igraph)
library(matrixStats)
library(data.table)
library(rowr)
library(msir)

#small helper; accepts a graph and returns average dergee
avg.degree=function(x){
  sum(degree.distribution(x)*c(1:length(degree.distribution(x))))}

#small helper; accepts an average serial interval and returns a generated serial interval in days
serial.interval=function(int){
  round(rgamma(1,int,1))}

#small helper; accepts an average infection duration and returns a generated infection duration in days
infection.duration=function(int){
  round(rgamma(1,int,1))}

#small helper; accepts an average infection duration and returns a modified generated infection duration in days to reflect case isolation
short.infection.duration=function(int){
  dur=int
  round(rgamma(1,dur,1))}

#small helper; accepts an average mortality rate and returns a generated mortality rate
mortality.rate=function(int){
  runif(1,0.6,0.7)}

#large helper; accepts a number of households h and average household size a and returns a graph;
create.world=function(h,a){
  pop.size=0 #place holder for population size, roughly h*a
  num.houses=h #total number of households  
  avg.size.houses=a #average household size
  rewire.prob=0.9 #probability of a node being selected for rewire during the second stage
  households=c() #placeholder for list of household sizes, used in social generation
  world=graph.empty(directed = FALSE)
  
  #generate houses
  for(i in 1:num.houses){
    size.house=rpois(1,avg.size.houses)
    household=graph.lattice(size.house,nei=2,circular=TRUE) %>% set_vertex_attr("label", value = c((pop.size+1):(pop.size+size.house)))
    world=world+household
    pop.size=pop.size+size.house
    households=append(households,pop.size)
  }
  rewire.size=ceiling(pop.size*rewire.prob)
  new.edges=matrix(c(sample(pop.size, rewire.size),sample(pop.size, rewire.size)),rewire.size,2)
  
  #connect houses using E-R
  world=world+edge(new.edges)
  
  world=simplify(world) #dedupe and unloop
  isolates=which(colSums(as_adj(world, sparse=FALSE))==0)
  world=delete.vertices(world,isolates) #remove singletons
  households=unique(households[which(households %in% V(world))])  #match household list to final population 
  return(list(world,households)) 
}

#large helper; accepts a community graph and returns a state matrix
create.state=function(world,households){
  parameters=11 #1Influence, 2Institutional, 3Vaccination, 4Behavioural, 5S, 6E, 7I, 8Rd, 9Rr, 10Rv, 11Dur
  pop.size=length(V(world))
  state=matrix(NA, length(V(world)), parameters)
  colnames(state)=c("Inf", "Inst", "Vac", "Beh", "S", "E", "I", "Rd", "Rr", "Rv", "Dur")
  
  #0 is no trust, 1 is complete trust
  #randomly select all infleunces, 
  state[,1]=replicate(pop.size,runif(1,0,1))#sample(c(0.25,0.5,0.75,0.9),pop.size,replace=TRUE, prob=c(0.25,0.25,0.25,0.25))
  #assign institutional trust based on household
  start=1
  for(i in 1:length(households)){
    value1=sample(c(0.225,0.45,0.675,0.9),1,replace=TRUE, prob=c(0.15,0.3,0.3,0.25)) #c(0.1,0.1,0.3,0.5); c(0.15,0.3,0.3,0.25); c(0.25,0.25,0.25,0.25)
    value2=sample(c(0.225,0.45,0.675,0.9),1,replace=TRUE, prob=c(0.15,0.15,0.2,0.5)) #c(0.05,0.05,0.1,0.8); c(0.15,0.15,0.2,0.5); c(0.4,0.3,0.2,0.1)
    state[start:households[i],2]=value1
    state[start:households[i],3]=value2
    start=households[i]+1
  }
  #assign all other states around households
  state[,4]=state[,2]+runif(pop.size,-0.1,0.1)
  state[,2]=state[,2]+runif(pop.size,-0.05,0.05) 
  state[,3]=state[,3]+runif(pop.size,-0.05,0.05)
  state[,5]=1 #susceptibles, initally all
  state[,6]=0 #exposed, initially none
  state[,7]=0 #infectious, initially none
  state[,8]=0 #removed by death, initially none
  state[,9]=0 #removed by recovery, initally none
  state[,10]=0 #removed by vaccination, initially none****
  state[,11]=0 #duration remaining in compartment
  return(state)
}

#small helper; accepts a state, duration, current stock and initial stock and returns vaccine stock available; defines production delay internally
vaccine.stock=function(state,duration,stock,init.stock,delay){
  if(duration<=delay){stock=init.stock-sum(state[,10])}
  else{stock=1000}
  return(stock)
}

#large helper; accepts a state matrix,world, and stock and returns a vaccinated state matrix
ring=function(state,world,stock){
  #indices of eligibles
  iden.prob=0.8 #chance of a case being found
  cases=sample(which(state[,7]==1),floor(length(which(state[,7]==1))*iden.prob))
  #create an adjacency matrix, must be non spare for multiplication, resultant is non symetric, cols are good only
  adj=as_adj(world, sparse=FALSE)
  #deal with single case scenario
  if(length(cases)==1){
    possible.eligible.index=which(adj[1,]==1)
    possible.eligible.index=possible.eligible.index[which(state[possible.eligible.index,5]==1)]
  }
  #deal with multi case scenario
  else{
    possible.eligible.index=unlist(apply(adj[cases,],1,function(x){which(x==1)}))
    possible.eligible.index=append(possible.eligible.index,unlist(apply((adj%*%adj)[cases,],1,function(x){which(x!=0)})))
    possible.eligible.index=sort(unique(possible.eligible.index))
    possible.eligible.index=possible.eligible.index[which(state[possible.eligible.index,5]==1)]
  }
  vax.prob=runif(1,0,1) #probability of accepting a vaccine based on vaccine trust
  vax.list=possible.eligible.index[which(state[possible.eligible.index,3]>=vax.prob)]
  max.effort=length(vax.list)
  vax.list=sort(sample(vax.list,min(max.effort,stock)))
  state[vax.list, c(5,10,11)]=matrix(rep(c(0,1,0),length(vax.list)),length(vax.list),3,byrow=TRUE)
  
  return(state)
}

#large helper; accepts a state matrix and stock and returns a vaccinated state matrix
mass=function(state,world,stock){
  effort=min(20,stock) #average number of vaccines attempted to be administered per day
  vax.prob=runif(1,0,1)
  eligible.list=which(state[,5]==1 & state[,3]>=vax.prob)
  if(length(eligible.list)==0){return(state)}
  vax.list=sample(eligible.list,effort, replace=TRUE) #randomly sample from the population of eligibles
  vax.list=sort(unique(vax.list))
  state[vax.list, c(5,10,11)]=matrix(rep(c(0,1,0),length(vax.list)),length(vax.list),3,byrow=TRUE)
  
  return(state)
}

#small helper; accepts a state matrix and returns (un)vaccinated state matrix
none=function(nodes,world,stock){
  return(nodes)}

#large helper; accepts a state matrix and returns reset exposed nodes with serial intervals
expose=function(world, state, ser, trans){
  r=1 #small placeholder to further modify transmission dynamics
  inf.prob=0.6 #probability of infection transmission given behaviour of node, beh < inf.prob -> infection
  infections=sum(state[,7])
  target.number=ceiling((r/inf.prob)*infections)
  adj=as_adj(world, sparse=FALSE)
  possible.exposures.index=which(state[,5]==1) 
  
  number.infected.nei=colSums(state[,7]*adj)
  burials=rep(0,length(state[,11]))
  burials[(which(state[,11]==1))]=1
  number.dead.nei=colSums((state[,8]*burials*adj))
  number.dead.nei[which(number.dead.nei>0)]=1
  number.dead.nei[which(number.dead.nei<=0)]=0
  
  possible.exposures.index=possible.exposures.index[which(state[possible.exposures.index,4]<runif(1,0,inf.prob))]
  demog=(1-unname(state[possible.exposures.index,4]))*number.infected.nei[possible.exposures.index]
  if(sum(demog)==0){return(list(state[,c(5,6,11)],0))}
  demog.stand=demog/sum(demog)
  target=min(length(which(demog.stand!=0)),target.number)
  if(length(possible.exposures.index)==1){return(list(state[,c(5,6,11)],0))}
  new.exposures=sample(possible.exposures.index, target, prob=demog.stand)
  
  funeral.exposures=which(number.dead.nei>0)
  funeral.exposures=funeral.exposures[which(state[funeral.exposures,5]==1)]
  funeral.exposures=funeral.exposures[which(state[funeral.exposures,4]<0.3)]
  
  new.exposures=unique(append(new.exposures,funeral.exposures))
  
  new.exposures=sort(new.exposures)
  output=state[,c(5,6,11)]
  output[new.exposures,]=t(replicate(length(new.exposures),c(0,1,serial.interval(ser))))
  repro.num=length(new.exposures)/sum(state[,7])
  output=list(output,repro.num)
  #print(length(funeral.exposures))
  return(output) 
}

test.vec=c()
#large helper; accepts a world and state matrix and returns update vector
update.behaviour=function(world,state){
  output=list()
  size=length(state[,4])
  outbreak.prop=sum(state[,c(7,8,9,10)])/size
  kappa=25 #sensitivity; larger values -> more sensitive 18 is reasonable also 25
  alpha=0.05 #linear shift between 0 and 1; closer to 1 -> slower reaction time I think that 0.05 is most reasonable
  threshold=1/(1+exp(-kappa*(outbreak.prop-alpha))) #sigmoid function
  del=0.1 #percent of neighbours average that is adopted
  adj=as_adj(world,sparse=FALSE)
  inst.input=state[,2]
  vac.input=state[,3]
  beh.input=state[,4]
  eligible=which(state[,7]!=1 & state[,8]!=1 & state[,10]!=1) #to update, nodes must not be infected, vaccinated, or dead
  healthy.nei=which(colSums(state[,5]*adj)!=0)
  
  healthy.nei.average.age=rep(0,size)
  healthy.nei.average.inst=rep(0,size)
  healthy.nei.average.vac=rep(0,size)
  healthy.nei.average.beh=rep(0,size)
  
  if(length(healthy.nei)==1){
    healthy.nei.average.age[healthy.nei]=sum(state[healthy.nei,1]*adj[,healthy.nei])/sum(adj[,healthy.nei])+0.05
    healthy.nei.average.inst[healthy.nei]=sum(state[healthy.nei,2]*adj[,healthy.nei])/sum(adj[,healthy.nei])
    healthy.nei.average.vac[healthy.nei]=sum(state[healthy.nei,3]*adj[,healthy.nei])/sum(adj[,healthy.nei])
    healthy.nei.average.beh[healthy.nei]=sum(state[healthy.nei,4]*adj[,healthy.nei])/sum(adj[,healthy.nei])
  }
  if(length(healthy.nei)>1){
    healthy.nei.average.age[healthy.nei]=colSums(state[healthy.nei,1]*adj[,healthy.nei])/colSums(adj[,healthy.nei])+0.05*length(healthy.nei)
    healthy.nei.average.inst[healthy.nei]=colSums(state[healthy.nei,2]*adj[,healthy.nei])/colSums(adj[,healthy.nei])
    healthy.nei.average.vac[healthy.nei]=colSums(state[healthy.nei,3]*adj[,healthy.nei])/colSums(adj[,healthy.nei])
    healthy.nei.average.beh[healthy.nei]=colSums(state[healthy.nei,4]*adj[,healthy.nei])/colSums(adj[,healthy.nei])
  }
  
  ### institutional trust section
  sick.nei=colSums(state[,7]*adj+state[,8]*adj+state[,9]*adj)
  inst.diff=state[,2]-healthy.nei.average.inst 
  updates=which(inst.diff<threshold & mean(state[,1])<=healthy.nei.average.age) ##which(inst.diff<threshold)
  inst.del=(state[updates,2]+healthy.nei.average.inst[updates])/2-state[updates,2]
  output[[1]]=inst.input
  output[[1]][updates]=inst.input[updates]-del*inst.del+0.01*sick.nei[updates]
  
  ### vaccine setion
  vacc.nei=colSums(state[,10]*adj)
  vac.diff=state[,3]-healthy.nei.average.vac
  updates=which(vac.diff<threshold & mean(state[,1])<=healthy.nei.average.age)
  vac.del=(state[updates,3]+healthy.nei.average.vac[updates])/2-state[updates,3]
  output[[2]]=vac.input
  output[[2]][updates]=vac.input[updates]-del*vac.del+0.01*vacc.nei[updates]
  
  ### behaviour section
  dead.nei=colSums(state[,8]*adj)
  beh.diff=state[,4]-healthy.nei.average.beh
  updates=which(beh.diff<threshold & mean(state[,1])<=healthy.nei.average.age)
  beh.del=(state[updates,4]+healthy.nei.average.beh[updates])/2-state[updates,4]
  output[[3]]=beh.input
  output[[3]][updates]=beh.input[updates]-del*beh.del+0.01*dead.nei[updates]
  
  output[[1]][which(output[[1]]>1)]=1
  output[[1]][which(output[[1]]<0)]=0
  
  output[[2]][which(output[[2]]>1)]=1
  output[[2]][which(output[[2]]<0)]=0
  
  output[[3]][which(output[[3]]>1)]=1
  output[[3]][which(output[[3]]<0)]=0
  
  
  return(output)
}

#large helper; accepts a results data matrix and outputs important information
display=function(results,inst.trust,vac.trust,beh.trust,epi.curve.history,repro.history.complete){
  #first tabulate all results
  d=results
  test=repro.history.complete
  cc=round(mean(d[,1]),3)
  cc.lower=round(mean(d[,1])-sd(d[,1])/length(d[,1])*1.96, 3)
  cc.upper=round(mean(d[,1])+sd(d[,1])/length(d[,1])*1.96,3)
  deg=round(mean(d[,2]),3)
  size=mean(d[,3])
  
  inf=round(mean(d[,4]),3)
  inf.lower=round(mean(d[,4])-sd(d[,4])*1.96/length(d[,4]),3)
  inf.upper=round(mean(d[,4])+sd(d[,4])*1.96/length(d[,4]),3)
  cfr=round(mean(d[,5]),3)
  dur=round(mean(d[,6]),3)
  vacs=round(mean(d[,7]),3)
  vacs.lower=round(mean(d[,7])-sd(d[,7])*1.96/length(d[,7]),3)
  vacs.upper=round(mean(d[,7])+sd(d[,7])*1.96/length(d[,7]),3)
  unef=round(mean(d[,8]),3)
  r.list=unname(unlist(repro.history.complete[1:10,-1]))
  r=10*round(mean(r.list),3)
  r.lower=round(r-1.96*sd(r.list)/length(r.list),3)
  r.upper=round(r+1.96*sd(r.list)/length(r.list),3)
  r.unity=min(which(predict(loess(10*rowMeans(repro.history.complete[,-1]) ~ seq(1:length(10*rowMeans(repro.history.complete[,-1]))), span=0.17))<=1))
  
  control.start=mean(d[,9])
  stockout.time=mean(d[,10])
  restock.time=mean(d[,11])
  
  #then display them nicely
  cat("Population Information:",fill=TRUE)
  cat("Average Cluster Coefficient",cc,sep=": ",fill=TRUE)
  cat("Cluster Coefficient Confidence Interval",paste("[",paste(cc.lower,cc.upper,sep=","),"]"),sep=": ",fill=TRUE)
  cat("Average Degree",deg,sep=": ",fill=TRUE)
  cat("Average Population Size",size, sep=": ", fill=TRUE)
  cat("================================",fill=TRUE)
  cat("Demographic Information:",fill=TRUE)
  cat("Institutional Trust",fill=TRUE)
  print(round(inst.trust,3))
  cat(fill=TRUE)
  cat("Vaccination Trust",fill=TRUE)
  print(round(vac.trust,3))
  cat(fill=TRUE)
  cat("Behaviour",fill=TRUE)
  print(round(beh.trust,3))
  cat("================================",fill=TRUE)
  cat("Outbreak Information:",fill=TRUE)
  cat("Average Proportion Infected", inf, sep=": ", fill=TRUE)
  cat("Proportion Infected Confidence Interval",paste("[",paste(inf.lower,inf.upper,sep=","),"]"),sep=": ",fill=TRUE)
  cat("Average Proportion Vaccined", vacs, sep=": ", fill=TRUE)
  cat("Proportion Vaccined Confidence Interval",paste("[",paste(vacs.lower,vacs.upper,sep=","),"]"),sep=": ",fill=TRUE)
  cat("Average Proportion Unaffected", unef, sep=": ", fill=TRUE)
  cat("Average Case Fatality Rate", cfr, sep=": ", fill=TRUE)
  cat("Average Total Duration in Days", dur, sep=": ", fill=TRUE)
  cat("Average Basic Reproduction Number", r, sep=": ", fill=TRUE)
  cat("Basic Reproduction Number Confidence Interval",paste("[",paste(r.lower,r.upper,sep=","),"]"),sep=": ",fill=TRUE)
  cat("Day Reproduction Number Reaches Unity:",r.unity,fill=TRUE)
  
  par(mfrow=c(1,2),xpd=FALSE)
  suppressWarnings(plot.epi.curve(epi.curve.history,control.start,stockout.time,restock.time))
  num.runs=length(d[,1])
  
  suppressWarnings(plot.repro(repro.history.complete))
}

#large helper; accpets a list of epi cruves and returns a plot of their average with confidence limits
plot.epi.curve=function(history,control.start,stockout.time,restock.time){
  
  max.runtime=max(sapply(history,length))/2 
  num.runs=length(sapply(history,length))
  results=matrix(0,max.runtime,num.runs+1)
  results[,1]=1:max.runtime
  results[,(1:num.runs)+1]=sapply(history,function(x){c(x[,2],rep(0,max.runtime-length(x[,2])))})
  averages=rowMeans(results[,(1:num.runs)+1])
  lowers=rowMeans(results[,(1:num.runs)+1])-1.96*rowSds(results[,(1:num.runs)+1])/num.runs
  uppers=rowMeans(results[,(1:num.runs)+1])+1.96*rowSds(results[,(1:num.runs)+1])/num.runs 
  
  index=1:max.runtime
  average.model=loess(averages ~ index, span=0.07)
  lower.model=loess(lowers ~ index, span=0.07)
  upper.model=loess(uppers ~ index, span=0.07)
  smooth.average=predict(average.model)
  smooth.lower=predict(lower.model)
  smooth.upper=predict(upper.model)
  
  l=loess.sd(averages ~ index, span=0.07, nsigma = 1.96)
  plot(l$x, l$y,type='l', ylim = c(0,max(l$upper)),
       main=paste("Average Epidemic Curve of",num.runs,"Outbreaks"),ylab="Prevalent Cases",xlab="Day of Outbreak",cex.lab=1.5, cex.axis=1.5, cex.main=1.5)
  #polygon(c(index,rev(index)),
  #        c(l$lower,rev(l$upper)),col = "grey75", border = FALSE)
  #lines(l$y,col='red',lwd=2)

  abline(v=control.start,lty=3)
  abline(v=stockout.time,lty=3,col='red')
  if(control.start!=stockout.time){
    rect(stockout.time,-5,restock.time-stockout.time+control.start,max(smooth.upper)+5,col = rgb(0.5,0.0,0.0,1/4))
  }
}

#small helper; graphs repro curve
plot.repro=function(repro.history.complete){
  repro.history.complete=as.matrix(repro.history.complete)
  num.runs=length(repro.history.complete[1,-1])
  averages=10*rowMeans(repro.history.complete[,-1])
  lowers=10*rowMeans(repro.history.complete[,-1])-1.96*(rowSds(repro.history.complete[,-1])) # /length(repro.history.complete[1,-1])
  uppers=10*rowMeans(repro.history.complete[,-1])+1.96*(rowSds(repro.history.complete[,-1])) #/length(repro.history.complete[1,-1])
  
  index=1:length(averages)
  repro.model=loess(averages ~ index, span=0.17)
  lower.model=loess(lowers ~ index, span=0.17)
  upper.model=loess(uppers ~ index, span=0.17)
  smooth.lower=predict(lower.model)
  smooth.upper=predict(upper.model)
  smooth.repro=predict(repro.model)
  
  plot(smooth.repro, type = "l", ylim = c(0,max(smooth.upper)+1),
       main=paste("Average Reproduction Number of",num.runs,"Outbreaks"),ylab="Reproduction Number",xlab="Day of Outbreak",cex.lab=1.5, cex.axis=1.5, cex.main=1.5)
  #polygon(c(index,rev(index)),
   #       c(smooth.lower,rev(smooth.upper)),col = "grey75", border = FALSE)
  #lines(smooth.repro,col='red',lwd=2)
  abline(v=min(which(smooth.repro<=1)),lty=3)
  abline(1,0,lty=3)
}

#main function; accepts a community graph, an initial state, and a vaccination strategy and returns a vector of results
outbreak=function(world, state, strat, game){
  #set up some important values
  mort=mortality.rate()
  ser=10 #avergae serial interval in days
  infdur=10 #average infectious duration in days 
  short.infdur=4
  eff=0.99 #vaccine efficacy, assumed constant all or nothing model
  trans=0.8 #lowest likely probability of infection given contact
  threshold=30 #number of cases required before vaccination begins 15 in most simulations
  primaries=3 #number of primary index cases to seed outbreak SHOULD BE LOWER THAN THRESHOLD
  control.limit=0 #number of cases allowed remaining for outbreak to "end" MUST BE LOWER THAN PRIMARIES
  init.stock=10000 #quantity of vaccines available until 30 days pass, lag DEFINED ABOVE inside stock function
  delay=30
  stockout=0 #counter to keep track of day when first stockout occurs
  stockout.date=0
  
  infected.nodes=0
  vaccinated.nodes=0
  dead.nodes=c()
  recovered.nodes=0
  epi.curve=matrix(0,1,2)
  
  test.vec=c()
  
  #seed the initial outbreak with index cases
  index.cases=sample(length(V(world)),primaries)
  state[index.cases,c(5,7,11)]=matrix(replicate(primaries,c(0,1,serial.interval(ser))),primaries,3,byrow=TRUE)
  control.duration=0
  duration=0
  infected.nodes=primaries
  epi.curve=rbind(epi.curve,c(duration,infected.nodes))
  repro.history=c()
  
  #begin outbreak without any control until detection threshold reached
  while(infected.nodes<threshold & sum(state[,6],state[,7])>control.limit){
    #expose nodes according to transmission protocol
    if(sum(state[,5])!=0 & sum(state[,7]!=0)){
      pre=sum(state[,5])
      exposures=expose(world,state,ser,trans)
      state[,c(5,6,11)]=exposures[[1]][,c(1,2,3)]
      ####repro
      post=sum(state[,5])
      infected.nodes=infected.nodes+(pre-post) 
    }
    #move nodes from exposed to infected
    moving.to.infected=sum(state[,6]==1 & state[,11]==0)
    if(moving.to.infected>0){
      state[(state[,6]==1 & state[,11]==0),c(6,7,11)]=matrix(replicate(moving.to.infected,c(0,1,infection.duration(infdur))),
                                                             moving.to.infected,3,byrow=TRUE)
    }
    #move nodes from infected to removed
    moving.to.removed=sum(state[,7]==1 & state[,11]==0)
    if(moving.to.removed>0){
      state[(state[,7]==1 & state[,11]==0),c(7,8,9,11)]= matrix(replicate(moving.to.removed,c(0,sample(0:1,2,prob=(c((1-mort),mort))),3)),
                                                                moving.to.removed,4,byrow=TRUE)
    }
    recovered.nodes=sum(state[,c(8,9)])
    #decrease waiting time and increase clock time
    state[,11]=state[,11]-1 #duration will then act as negative clock for those removed 
    repro.history=rbind(repro.history,exposures[[2]])
    duration=duration+1
    infectious.nodes=sum(state[,7])
    epi.curve=rbind(epi.curve,c(duration,infectious.nodes))
  }
  #administer vaccines until outbreak controlled
  while(sum(state[,6],state[,7])>control.limit){
    #determine vaccine effort available
    stock=vaccine.stock(state,control.duration,stock,init.stock,delay)
    #pass eligible nodes to the vaccination function
    if(stock>=0){state=eval(call(strat,state,world,stock))}
    if(stock==0 && stockout==0){
      stockout.date=duration
      stockout=1
      }
    #expose nodes according to transmission protocol
    if(sum(state[,5])!=0 & sum(state[,7]!=0)){
      pre=sum(state[,5])
      exposures=expose(world,state,ser,trans)
      state[,c(5,6,11)]=exposures[[1]][,c(1,2,3)]
      ####repro
      post=sum(state[,5])
      infected.nodes=infected.nodes+(pre-post) 
    }
    
    #move nodes from exposed to infected using health behaviour to calculate infectious duration
    moving.to.infected.long=sum(state[,6]==1 & state[,11]==0 & state[,2]<=0.3)
    if(moving.to.infected.long>0){
      state[(state[,6]==1 & state[,11]==0 & state[,2]<=0.3),c(6,7,11)]=matrix(replicate(moving.to.infected.long,c(0,1,infection.duration(infdur))),
                                                             moving.to.infected.long,3,byrow=TRUE)
    }
    
    moving.to.infected.short=sum(state[,6]==1 & state[,11]==0 & state[,2]>0.3)
    if(moving.to.infected.short>0){
      state[(state[,6]==1 & state[,11]==0 & state[,2]>0.3),c(6,7,11)]=matrix(replicate(moving.to.infected.short,c(0,1,short.infection.duration(short.infdur))),
                                                             moving.to.infected.short,3,byrow=TRUE)
    }
    
    #move nodes from infected to removed
    moving.to.removed=sum(state[,7]==1 & state[,11]==0)
    if(moving.to.removed>0){
      state[(state[,7]==1 & state[,11]==0),c(7,8,9,11)]= matrix(replicate(moving.to.removed,c(0,sample(0:1,2,prob=(c((1-mort),(mort)))),3)),
                                                                moving.to.removed,4,byrow=TRUE)
    }
    recovered.nodes=sum(state[,c(8,9)])
    #if the outbreak has been going on a long enough time, evaluate strategies
    if(game){
      updates=update.behaviour(world,state)
      state[,2]=updates[[1]] #update list of nodes institutional trust
      state[,3]=updates[[2]] #update list of nodes vaccine trust
      state[,4]=updates[[3]] #update list of nodes health practice behaviour
      test.vec=cbind(test.vec,state[,2])
      #fitness function and replicator will go here eventually
    }
    #decrease waiting time and increase clock time
    state[,11]=state[,11]-1 #as above
    repro.history=rbind(repro.history,exposures[[2]])
    control.duration=control.duration+1
    duration=duration+1
    infectious.nodes=sum(state[,7])
    epi.curve=rbind(epi.curve,c(duration,infectious.nodes))
    #epi.curve=rbind(epi.curve,c(duration,infected.nodes-recovered.nodes))
  }
  if(stockout.date==0){stockout.date=duration-control.duration}
  stock.status=c(duration-control.duration, stockout.date, stockout.date+delay)
  output=list(state,epi.curve,repro.history,stock.status,test.vec)
  return(output)
}

#main function; accepts a desired population size, a number of iterations, and a strategy and returns interesting stuff
simulate=function(size,reps=2,strat="none",game=FALSE){
  #initialise a few things just for progress tracking
  
  if(game){
    cat("Now Running",reps,"Simulations of",size,"People WITH Social Dynamics and Vaccination Strategy:",strat,fill=TRUE)
  }
  if(!game){
    cat("Now Running",reps,"Simulations of",size,"People WITHOUT Social Dynamics and Vaccination Strategy:",strat,fill=TRUE)
  }
  t0=proc.time()
  pb=txtProgressBar(min = 0, max = reps, style = 3)
  
  #initialise the results matrix and begin the simulation loop
  results=matrix(NA, nrow=reps,ncol=11)
  epi.curve.history=list()
  repro.history.complete=NULL
  
  names=c("25%","50%","75%","100%")
  inst.start=matrix(0,reps,4)
  colnames(inst.start)=names
  vac.start=matrix(0,reps,4)
  colnames(vac.start)=names
  beh.start=matrix(0,reps,4)
  colnames(beh.start)=names
  
  inst.end=matrix(0,reps,4)
  colnames(inst.end)=names
  vac.end=matrix(0,reps,4)
  colnames(vac.end)=names
  beh.end=matrix(0,reps,4)
  colnames(beh.end)=names
  
  for(k in 1:reps){
    #create the world and extract some basic network properties for tracking
    h=ceiling(size/3.5)
    world.list=create.world(h,3.5) #house size should be fixed at 3.5 to maintain desired properties
    world=world.list[[1]]
    state=create.state(world,world.list[[2]])
    results[k,1]=transitivity(world) #cluster coef
    results[k,2]=avg.degree(world) #average degree
    results[k,3]=length(V(world)) #initial population size
    
    inst.start[k,1]=length(state[(which(state[,2]<=0.25)),2])/length(state[,2])
    inst.start[k,2]=length(state[(which(0.25<state[,2] & state[,2]<=0.5)),2])/length(state[,2])
    inst.start[k,3]=length(state[(which(0.5<state[,2] & state[,2]<=0.75)),2])/length(state[,2])
    inst.start[k,4]=length(state[(which(state[,2]>0.75)),2])/length(state[,2])
    
    vac.start[k,1]=length(state[(which(state[,3]<=0.25)),3])/length(state[,3])
    vac.start[k,2]=length(state[(which(0.25<state[,3] & state[,3]<=0.5)),3])/length(state[,3])
    vac.start[k,3]=length(state[(which(0.5<state[,3] & state[,3]<=0.75)),3])/length(state[,3])
    vac.start[k,4]=length(state[(which(state[,3]>0.75)),3])/length(state[,3])
    
    beh.start[k,1]=length(state[(which(state[,4]<=0.25)),4])/length(state[,4])
    beh.start[k,2]=length(state[(which(0.25<state[,4] & state[,4]<=0.5)),4])/length(state[,4])
    beh.start[k,3]=length(state[(which(0.5<state[,4] & state[,4]<=0.75)),4])/length(state[,4])
    beh.start[k,4]=length(state[(which(state[,4]>0.75)),4])/length(state[,4])
    
    #the main outbreak function, runs until the outbreak has been controlled
    output=outbreak(world, state, strat, game)
    state=output[[1]]
    
    results[k,4]=sum(state[,c(7,8,9)])/length(state[,5]) #final outbreak size
    results[k,5]=sum(state[,8])/sum(state[,c(8,9)]) #case fatality rate
    results[k,6]=length(output[[2]][,1]) #outbreak control duration
    results[k,7]=sum(state[,10])/length(state[,10]) #vaccines administered
    results[k,8]=sum(state[,5])/length(state[,5]) #number unaffected
    results[k,9]=output[[4]][1]
    results[k,10]=output[[4]][2]
    results[k,11]=output[[4]][3]
    
    inst.end[k,1]=length(state[(which(state[,2]<=0.25)),2])/length(state[,2])
    inst.end[k,2]=length(state[(which(0.25<state[,2] & state[,2]<=0.5)),2])/length(state[,2])
    inst.end[k,3]=length(state[(which(0.5<state[,2] & state[,2]<=0.75)),2])/length(state[,2])
    inst.end[k,4]=length(state[(which(state[,2]>0.75)),2])/length(state[,2])
    
    vac.end[k,1]=length(state[(which(state[,3]<=0.25)),3])/length(state[,3])
    vac.end[k,2]=length(state[(which(0.25<state[,3] & state[,3]<=0.5)),3])/length(state[,3])
    vac.end[k,3]=length(state[(which(0.5<state[,3] & state[,3]<=0.75)),3])/length(state[,3])
    vac.end[k,4]=length(state[(which(state[,3]>0.75)),3])/length(state[,3])
    
    beh.end[k,1]=length(state[(which(state[,4]<=0.25)),4])/length(state[,4])
    beh.end[k,2]=length(state[(which(0.25<state[,4] & state[,4]<=0.5)),4])/length(state[,4])
    beh.end[k,3]=length(state[(which(0.5<state[,4] & state[,4]<=0.75)),4])/length(state[,4])
    beh.end[k,4]=length(state[(which(state[,4]>0.75)),4])/length(state[,4])
    
    epi.curve.history[[k]]=output[[2]]
    if(k==1){repro.history.complete=matrix(0,length(output[[3]]),1)}
    repro.history.complete=cbind.fill(repro.history.complete,output[[3]],fill=0)
    setTxtProgressBar(pb, k) #display progress just for monitoring 
  }
  inst.start.mean=colMeans(inst.start)
  vac.start.mean=colMeans(vac.start)
  beh.start.mean=colMeans(beh.start)
  
  inst.end.mean=colMeans(inst.end)
  vac.end.mean=colMeans(vac.end)
  beh.end.mean=colMeans(beh.end)
  
  inst.trust=rbind(inst.start.mean,inst.end.mean)
  row.names(inst.trust)=c("Initial","Final")
  vac.trust=rbind(vac.start.mean,vac.end.mean)
  row.names(vac.trust)=c("Initial","Final")
  beh.trust=rbind(beh.start.mean,beh.end.mean)
  row.names(beh.trust)=c("Initial","Final")
  
  close(pb)

  display(results,inst.trust,vac.trust,beh.trust,epi.curve.history,repro.history.complete)
  run.time=unname(proc.time()[1]-t0[1])
  cat(fill=TRUE)
  cat("Run Time",run.time,sep=": ",fill=TRUE)
  return(list(results,inst.trust,vac.trust,beh.trust,epi.curve.history,repro.history.complete, output[[5]],state))
}

#small helper to convert outputted types to displayed types, useful for checking results
redisplay=function(output){
  display(output[[1]],output[[2]],output[[3]],output[[4]],output[[5]],output[[6]])
}




