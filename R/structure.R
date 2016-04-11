# edmsyn, a package that synthesizes educational data
# Copyright (C) 2015  Hoang-Trieu Trinh
# 
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.


# a minor change
#=======================+
# Sub-Routine functions |
#=======================+

#' @export
class.context <- function(x){
  print("context")
}

#' @export
print.context <- function(x){
  cat("Activated information in the context:\n")
  print(names(x))
}

#' @export
class.default <- function(x){
  print("default")
}

#' @export
print.init <- function(x){
  for(i in 1:length(names(x))){
    cat(paste0(names(x)[[i]],'\n'))
    print(get(names(x)[[i]],envir=x))
  }
}

to.str <- function(x, max){
  if (max<10) r <- toString(x)
  else
    r <- (paste0(paste(sapply(1:log(max,10),function(x)"0"),collapse=""),x))
  return(paste0("0",r))
}

# return which candidate is most likely to produce target
which.closest <- function(target, candidates){
  ref <- STRUCTURE[[target]]$tell
  which.max(
    sapply(candidates, function(c){
      sum(sapply(c,function(x){x %in% ref}))
    }))
}

# return if the value of a node and an info propagated to this node is compatible
compat <- function(val,tel){ 
  if (class(tel) == "min") return(all(tel <= val))
  if (class(tel) == "max") return(all(tel >= val))
  if (class(tel) == "numeric") return(max(abs(val-tel)) < 1e-10)
  else return(identical(val,tel))
}

#===========+
# STRUCTURE |
#===========+
 
#' @importFrom CDM sim.din
#' @importFrom CDM din
#' @importFrom stats optim
#' @importFrom MASS ginv
#' @importFrom HMM initHMM
#' @importFrom HMM baumWelch
assemble.structure <- function(){
  #================+
  # Core functions |
  #================+
  genQUniform <- function(concepts, perItem) {
    c <- combn(concepts,perItem)
    items <- ncol(c)
    Q = matrix(0,items,concepts)
    for (i in 1:items)
      Q[i,c[,i]] <- 1
    return(Q)
  }
  genQMax <- function(concepts, maxPerItem) {
    Q <- NULL
    for (i in 1:maxPerItem)
      Q <- rbind(Q,genQUniform(concepts,i))
    return(Q)
  }
  genQRand <- function(items, concepts) {
    sampleFrom <- NULL
    replace <- TRUE
    #------------CISAC--------------------------------------
    if (is.null(sampleFrom)) {
      if (is.null(concepts))
        stop("Input Insufficiency")
      else
        sampleFrom <- genQMax(concepts,concepts)
    }
    else{
      if (!is.null(concepts) & concepts != ncol(sampleFrom))
        stop("Input Conflict")
    }

    #------------GENERATING---------------------------------
    Q <- as.matrix(sampleFrom[sample(x = 1:nrow(sampleFrom),
                                     size = items,
                                     replace = replace),])
    if (items == 1) Q <- t(Q)
    return(Q)
  }
  maxCombn <- function(n){cbind(rep(0,n),t(genQMax(n,n)))}
  randGen <- function(P) {
    r <- matrix(sapply(P,
                  function(i) {
                    sample(0:1, 1, prob = c(max(1 - i,0),min(i,1)))
                  }),
           nrow(P),
           ncol(P))
    return(r)
  }
  depth <- function(root, poks) {
    level <- 1
    items <- nrow(poks)
    poks_ <- poks
    while (rowSums(poks_)[root] > 0) {
      level = level + 1
      poks_ = poks_ %*% poks
      if (level == items) break
    }
    return(level)
  }
  PToOdds <- function(p) p/(1-p)
  OddsToP <- function(o) {
    r <- o/(1+o)
    r[is.na(r)] <- 1
    return(r)
  }
  binaryHMMLearn <- function(R){
    time <- length(R)
    observe <- as.character(R)

    learn <- NULL
    while(class(learn) != "list"){
      # Initizalizing
      states <- c("0","1")
      symbols <- c("0","1")
      pi <- runif(1,0,1) # p(z_1 = 0)
      pi <- c(pi,1-pi)
      A <- c(runif(1,0,1),0) # Transition prob
      A <- matrix(c(A,1-A),2,2) # A[i,j] = p(zn+1=j-1|zn=i-1)
      E <- runif(2,0,1) # Emission prob
      E <- matrix(c(E,1-E),2,2) # E[i,j] = p(x=j-1|z=i-1)
      hmm <- initHMM(states, symbols, pi, A, E)
      learn <- try(baumWelch(hmm = hmm, observation = observe)$hmm,TRUE)
    }
    names(learn$startProbs) <- NULL
    returns <- list(learn$startProbs[2],learn$transProbs[1,2],
                    learn$emissionProbs[2,1],learn$emissionProbs[1,2])
    names(returns) <- c("probInitS","L","slip","guess")
    return(returns)
  }
  nmfLearn <- function(R, concepts, func){
    Q <- genQRand(nrow(R), concepts)
    S <- matrix(0,concepts, ncol(R))

    space <- genQMax(concepts,concepts)
    space <- space[sample(1:nrow(space)),]
    space0 <- cbind( t(space), rep(0,concepts) )

    learnS <- function(){
      ref <- R[,iS]
      predict <- func(Q = Q, S = space0)
      distance <- colSums((predict - ref)^2)
      best <- which.min(distance)[1]
      space0[,best]
    }

    learnQ <- function(){
      ref <- R[iQ,]
      predict <- func(Q = space, S = S)
      distance <- colSums((t(predict) - ref)^2)
      best <- which.min(distance)[1]
      t(space[best,])
    }


    hault <- 0
    threshold <- max(nrow(Q), ncol(S))
    permS <- sample(ncol(S))
    permQ <- sample(nrow(Q))

    for (i in 1:1000){
      idS <- (i-1) %% ncol(S) + 1
      idQ <- (i-1) %% nrow(Q) + 1
      if (idS == 1) permS <- sample(ncol(S))
      if (idQ == 1) permQ <- sample(nrow(Q))
      iS <- permS[idS]
      iQ <- permQ[idQ]

      lS <- learnS()
      lQ <- learnQ()

      progress = any(S[,iS]!=lS) | any(Q[iQ,]!=lQ)
      if (progress == TRUE) hault <- 0
      else hault <- hault + 1
      if (hault == threshold) break

      S[,iS] <- learnS()
      Q[iQ,] <- learnQ()
    }

    returns <- list(Q, S)
    names(returns) <- c("Q","S")
    return(returns)
  }
  QSAvgGenR2 <- function(Q, S){
    (Q/rowSums(Q))%*%(S^2)
  }

  expGen <- function(st.exp, it.exp) {
    dif <- it.exp
    abi <- st.exp
    dif[dif == 1] <- 2
    abi[abi == 1] <- 2
    difOdd <- PToOdds(dif)
    abiOdd <- PToOdds(abi)
    POdd <- difOdd %*% t(abiOdd)
    P <- OddsToP(POdd)
    P[which(difOdd < 0),] <- 1
    P[,which(abiOdd < 0)] <- 1
    list(R=randGen(P = P))
  }
  logitGen <- function(dis, dif, abi){
    t <- abi
    a <- -dis
    b <- dis*dif
    u <- rep(1,length(t))
    list(R=randGen(1/(1+exp(a%*%t(t)+b%*%t(u)))))
  }
  dinaGen <- function(Q,M,slip,guess) {
    R  <- t(sim.din(
      q.matrix = Q,
      guess = guess,
      slip = slip,
      rule = "DINA",
      alpha = t(M)
    )$dat)
    rownames(R) <- NULL
    list(R=R, Q=Q)
  }
  dinoGen <- function(Q,M,slip,guess) {
    R  <- t(sim.din(
      q.matrix = Q,
      guess = guess,
      slip = slip,
      rule = "DINO",
      alpha = t(M)
    )$dat)
    rownames(R) <- NULL
    list(R=R,Q=Q)
  }
  QMConGen <- function(Q, M){
    list(R=(0 + !(Q%*%(1-M))), concepts = nrow(M))
  }
  QMDisGen <- function(Q, M){
    list(R = (1 - !(Q%*%M)), concepts = nrow(M))
  }
  QMComGen <- function(Q, M){
    list(R=randGen((Q/rowSums(Q)) %*% M), concepts = nrow(M))
  }
  QSLinAvgGen<- function(Q,S){
    list(R=randGen(sqrt(QSAvgGenR2(Q = Q,S = S))), concepts = nrow(S))
  }
  Get.Ks.State <- function(Node,PO,State)
  {
    if(sum(PO[,Node])==0) {res = 0} else
    {res = max(State[which(PO[,Node]==1)])}
    level = depth(Node,PO)
    return(runif(1,res,res+((1-res)/level)))
  }
  Gen.Synthetic.POKS <- function(St.Var,Students,State,PO, alpha.c, alpha.p, p.min)
  {
    Items = nrow(PO)
    
    #for student variance we use (x+1/2)^4
    Student.Variance = pnorm(rnorm(Students,0,St.Var))
    Student.Variance = (Student.Variance+1/2)^4
    State.Org <- State
    
    if(St.Var>0.3)
      St.Var = 0.3
    if(St.Var<0)
      St.Var = 0

    R = matrix(-1,Students,Items)
    for(i in 1:Students)
    {
      State <- State.Org*Student.Variance[i]
      #Gen OR.t
      OR.t = matrix(0.5,Items,Items)
      OR.t[which(t(PO)==1)] <- runif(sum(PO),0.8-St.Var,1)
      OR.t <- PToOdds(OR.t)
      #Gen OR.f
      OR.f = matrix(0.5,Items,Items)
      OR.f[which(t(PO)==1)] <- runif(sum(PO),0,0.2+St.Var)
      OR.f <- PToOdds(OR.f)
      #Create Samples
      for(it in 1:ncol(R))
      {
        R[i,it] <- sample(0:1,size = 1,prob = c(1- OddsToP(State[it]),OddsToP(State[it])))
        #Odds.temp.state[k] <- ks.update(i,RG[j,i],ks$state,ks)[k]
        if(R[i,it]==1)
        {
          for(k in which(PO[it,]==1)){
            State[k] <- State[k]*OR.t[k,it]
          }
        }else{
          for(k in which(PO[,it]==1)){
            State[k] <- State[k]*OR.f[k,it]
          }
        }                   
      }
    }
    res <- list(R = t(R), alpha.c = alpha.c, alpha.p = alpha.p, p.min = p.min)
    return(res)
  }
  Gen.Synthetic.POKS.OR <- function(St.Var,Students,State, OR.t, OR.f, PO, alpha.c, alpha.p, p.min)
  {
    Items = nrow(PO)
    
    #for student variance we use (x+1/2)^4
    Student.Variance = pnorm(rnorm(Students,0,St.Var))
    Student.Variance = (Student.Variance+1/2)^4
    State.Org <- State
    
    if(St.Var>0.3)
      St.Var = 0.3
    if(St.Var<0)
      St.Var = 0
    
    R = matrix(-1,Students,Items)
    for(i in 1:Students)
    {
      State <- State.Org*Student.Variance[i]
      #Create Samples
      for(it in 1:ncol(R))
      {
        R[i,it] <- sample(0:1,size = 1,prob = c(1- OddsToP(State[it]),OddsToP(State[it])))
        #Odds.temp.state[k] <- ks.update(i,RG[j,i],ks$state,ks)[k]
        if(R[i,it]==1)
        {
          for(k in which(PO[it,]==1)){
            State[k] <- State[k]*OR.t[k,it]
          }
        }else{
          for(k in which(PO[,it]==1)){
            State[k] <- State[k]*OR.f[k,it]
          }
        }                   
      }
    }
    res <- list(R = t(R), alpha.c = alpha.c, alpha.p = alpha.p, p.min = p.min)
    return(res)
  }
  poksGen <- function(students, poks, successRate, alpha.c, alpha.p, p.min){
    items <- nrow(poks)
    poks_ <- poks
    R <- matrix(-1,items,students)

    #Initiate result for root nodes and their children
    while (any(poks_ == 1)) {
      root <- intersect(which(rowSums(poks_) != 0),
                        which(colSums(poks_) == 0))[1]
      # Root: at least one child and no parents

      difficulty = depth(root, poks)
      R[root,which(R[root,] < 0)] <-
        sample(
          0:1,-sum(R[root,which(R[root,] < 0)]),
          prob = c(1 - 1 / difficulty, 1 / difficulty),
          replace = TRUE
        )
      R[which(poks_[root,] == 1),which(R[root,] == 1)] <- 1
      poks_[root,] <- 0
    }

    # Initiate the rest
    while (any(R < 0)) {
      root = which(rowSums(R < 0) > 0)[1]
      R[root,which(R[root,] < 0)] <-
        sample(0:1,-sum(R[root,which(R[root,] < 0)]),
               prob = c(1 - successRate, successRate),
               replace = TRUE)
    }

    # 2-generation Incremental fitting the successRate param
    tol <- 0.01
    count <- 0
    twoSteps <- poks %*% poks
    while (abs(mean(R) - successRate) > tol) {
      flip <- mean(R) < successRate
      choose = sample(which(R != flip))[1]
      item <- row(R)[choose]
      student <- col(R)[choose]
      R[item,student] <- flip
      copy <- twoSteps
      if (flip == 0)
        copy <- t(copy)
      follows <- which(copy[item,] > 0)
      R[follows,student] <- flip
      count <- count + 1
      if (count > 5000) break
    }

    list(R=R, alpha.c = alpha.c, alpha.p = alpha.p, p.min = p.min)
  }
  skillBktGen <- function(initS, L, slip, guess, time, order, perItem){
    items <- nrow(initS)
    concepts <- items
    students <- ncol(L)
    Q <- diag(items)
    model = "dina"

    learn <- function(state, trans) {
      newState <- randGen(P = trans)
      newState[state == 1] <- 1
      return(newState)
    }

    R <- array(0,dim = c(items,students,time))
    RPerItem <- matrix(0,time,students)
    M <- array(0,dim = c(concepts,students,time))
    M[,,1] <- initS

    Q.ori <- Q
    slip.ori <- slip
    guess.ori <- guess

    for (i in 1:time) {
      if (perItem == TRUE) {
        Q <- t(as.matrix(Q.ori[order[i],]))
        slip <- slip.ori[order[i],]
        guess <- guess.ori[order[i],]
      }
      if (model == "nmf.com")
        r <- QMComGen(Q = Q,S = M[,,i])
      else{
        r <- NULL
        Mi <- M[,,i]
        for (j in 1:students){
          Mij <- as.matrix(Mi[,j])
          if (model == "dina")
            r_ <- dinaGen(
              Q = Q,M = Mij, slip = slip[j],guess = guess[j]
            )$R
          else
            r_ <- dinoGen(
              Q = Q,M = Mij, slip = slip[j],guess = guess[j]
            )$R
          r <- cbind(r,r_)
        }
      }
      if (perItem == TRUE)
        RPerItem[i,] <- r
      else
        R[,,i] <- r
      if (i < time)
        M[,,(i + 1)] <- learn(state = M[,,i], trans = L)
    }

    if (perItem == TRUE)
      R <- RPerItem
    if (perItem == FALSE)
      order <- NULL
    list(R=R, order = order)
  }
  qBktGen <- function(initS, L, slip, guess, time, order, perItem, Q, model){
    items <- nrow(Q)
    concepts <- ncol(Q)
    students <- ncol(initS)

    learn <- function(state, trans) {
      newState <- randGen(P = trans)
      newState[state == 1] <- 1
      return(newState)
    }

    R <- array(0,dim = c(items,students,time))
    RPerItem <- matrix(0,time,students)
    M <- array(0,dim = c(concepts,students,time))
    M[,,1] <- initS

    Q.ori <- Q
    slip.ori <- slip
    guess.ori <- guess

    for (i in 1:time) {
      if (perItem == TRUE) {
        Q <- t(as.matrix(Q.ori[order[i],]))
        slip <- slip.ori[order[i],]
        guess <- guess.ori[order[i],]
      }
      if (model == "nmf.com")
        r <- QMComGen(Q = Q,S = M[,,i])
      else{
        r <- NULL
        Mi <- M[,,i]
        for (j in 1:students){
          Mij <- as.matrix(Mi[,j])
          if (model == "dina")
            r_ <- dinaGen(
              Q = Q,M = Mij, slip = slip[j],guess = guess[j]
            )$R
          else
            r_ <- dinoGen(
              Q = Q,M = Mij, slip = slip[j],guess = guess[j]
            )$R
          r <- cbind(r,r_)
        }
      }
      if (perItem == TRUE)
        RPerItem[i,] <- r
      else
        R[,,i] <- r
      if (i < time)
        M[,,(i + 1)] <- learn(state = M[,,i], trans = L)
    }

    if (perItem == TRUE)
      R <- RPerItem
    if (perItem == FALSE)
      order <- NULL
    list(R=R, order = order)
  }
  po2State <- function(PO){
    Items <- nrow(PO)
    Get.Ks.State <- function(Node,PO,State)
    {
      if(sum(PO[,Node])==0) {res = 0} else
      {res = max(State[which(PO[,Node]==1)])}
      level = depth(Node,PO)
      return(runif(1,res,res+((1-res)/level)))
    }
    State = rep(0,Items)
    for (j in 1:Items){
      State[j] = Get.Ks.State(j,PO,State)
    }
    State <- PToOdds(State)
  }
  stVarPo2Ort <- function(stVar, PO){
    Items <- nrow(PO)
    OR.t = matrix(0.5,Items,Items)
    OR.t[which(t(PO)==1)] <- runif(sum(PO),0.8-stVar,1)
    OR.t <- PToOdds(OR.t)
  }
  stVarPo2Orf <- function(stVar, PO){
    Items <- nrow(PO)
    OR.f = matrix(0.5,Items,Items)
    OR.f[which(t(PO)==1)] <- runif(sum(PO),0,0.2+stVar)
    OR.f <- PToOdds(OR.f)
  }
  genPoks <- function(items, minTrees, maxTrees, minDepth, maxDepth,
                      density, minItemPerTree, maxItemPerTree, trans) {
    treeSizes <- NULL
    treeDepths <- NULL
    #-------------CISAC------------------------------------------------------
    if (!is.null(treeSizes) &
        !is.null(treeDepths) &
        length(treeSizes) != length(treeDepths))
      stop("Cannot reach 'po' due to conflict at lower level parameters")
    if (minDepth + 1 > maxItemPerTree)
      stop("Cannot reach 'po' due to conflict at lower level parameters")
    if (items < minTrees * minItemPerTree |
        items > maxTrees * maxItemPerTree)
      stop("Cannot reach 'po' due to conflict at lower level parameters")

    #-------------GENERATING-------------------------------------------------

    trees <- length(treeSizes)
    if (is.null(treeSizes)) {
      # pick a number of trees
      lowerTrees <- max(minTrees,ceiling(items / maxItemPerTree))
      upperTrees <-
        min(maxTrees,floor(items / max(minDepth + 1,minItemPerTree)))
      if (lowerTrees > upperTrees)
        stop("Cannot reach 'po' due to conflict at lower level parameters")
      if (!is.null(treeDepths)) {
        if (length(treeDepths) < lowerTrees |
            length(treeDepths) > upperTrees)
          stop("Cannot reach 'po' due to conflict at lower level parameters")
        else
          trees <- length(treeDepths)
      }
      else{
        if (lowerTrees == upperTrees)
          trees <- lowerTrees
        else
          trees <- sample(lowerTrees:upperTrees,1)
      }

      # get the numbers of item on each tree
      sampleTree <- function(itemsLeft, x) {
        if (x == 1)
          return(itemsLeft)

        lower <- itemsLeft - maxItemPerTree * (x - 1)
        upper <-
          itemsLeft - max(minDepth + 1,minItemPerTree) * (x - 1)
        if (lower > maxItemPerTree)
          stop("Cannot reach 'po' due to conflict at lower level parameters")
        if (upper < minItemPerTree)
          stop("Cannot reach 'po' due to conflict at lower level parameters")

        upper <- min(upper,maxItemPerTree)
        if (upper < minDepth)
          stop("Cannot reach 'po' due to conflict at lower level parameters")
        lower <- max(lower,minItemPerTree,minDepth + 1)
        if (!is.null(treeDepths))
          lower <- max(lower, treeDepths[trees - x + 1] + 1)


        if (lower > upper)
          stop("Cannot reach 'po' due to conflict at lower level parameters")
        if (lower == upper)
          sampleResult <- lower
        else
          sampleResult <- sample(x = lower:upper,1)

        c(sampleResult,c(sampleTree(itemsLeft - sampleResult,x - 1)))
      }

      #permute to remove bias from ordered sampling
      perm <- sample(trees)
      treeSizes <- sampleTree(items,trees)[perm]
      if (!is.null(treeDepths))
        treeDepths <- treeDepths[perm]
    }

    if (!is.null(treeDepths)) {
      if (sum((treeDepths + 1) > treeSizes) > 0)
        stop("Cannot reach 'po' due to conflict at lower level parameters")
    }
    else{
      treeDepths <- numeric(trees)
      for (i in 1:trees) {
        upperDepth <- min(maxDepth, treeSizes[i] - 1)
        if (minDepth == upperDepth)
          treeDepths[i] <- minDepth
        else
          if (treeSizes[i] == 1)
            treeDepths[i] <- 0
          else
            treeDepths[i] <- sample(max(minDepth,1):upperDepth,1)
      }
    }
    
    #permute to remove bias from ordered samling
    perm <- sample(items)
    poks <- matrix(0,items,items)
    subtrees <- list()
    densFail <- FALSE

    sampleLevel <- function(itemsLeft,x) {
      if (x == 1)
        return(itemsLeft)
      lower <- 1
      upper <- itemsLeft - (x - 1)
      if (lower == upper)
        sampleResult <- lower
      else
        sampleResult <- sample(lower:upper,1)
      c(sampleResult,c(sampleLevel(itemsLeft - sampleResult,x - 1)))
    }

    for (i in 1:trees) {
      size.i <- treeSizes[i]
      levels <- treeDepths[i] + 1
      levelSizes <-
        sampleLevel(size.i,levels)[sample(levels)]
      # Skeleton
      accumLvl <- cumsum(levelSizes)

      up_down <- function(node) {
        atLevel <- sum(accumLvl < node) + 1
        result <- sapply(1:size.i, function(x) {
          xAtLvl <- sum(accumLvl < x) + 1
          if (xAtLvl == atLevel + 1 | xAtLvl == atLevel - 1)
            return(TRUE)
          else
            return(FALSE)
        })
      }

      mark <- rep(TRUE, size.i)
      mark[sample(size.i,1)] <- FALSE

      while (sum(mark) != 0) {
        pickFrom <- c(1:size.i)[!mark]
        if (length(pickFrom) == 1)
          begin <- pickFrom[1]
        else
          begin <- sample(pickFrom,1)
        avail <- (up_down(begin) & mark)
        if (sum(avail) == 0) next
        pickFrom <- c(1:size.i)[avail]
        if (length(pickFrom) == 1)
          end <- pickFrom[1]
        else
          end <- sample(pickFrom,1)
        mark[end] <- FALSE
        poks[perm[min(begin,end)],perm[max(begin,end)]] <- 1
      }

      if (size.i != 1){
        groundLvl <- c(0,accumLvl)
        if (trans == FALSE){
          pNow <- (size.i-1)/sum((c(1,levelSizes)*c(levelSizes,1))[2:levels])
          if (pNow < 1){
            p <- (density - pNow)/(1-pNow)
            if (p > 0){
              # Add random arc
              for (j in 1:(levels-1))
                for (k in 1:levelSizes[j])
                  for (m in 1:levelSizes[j+1]){
                    begin <- perm[groundLvl[j]+k]
                    end <- perm[groundLvl[j+1]+m]
                    if (poks[begin,end] == 0)
                      poks[begin,end] <- sample(0:1,1,prob = c(1-p,p))
                  }
            }
          }
        }
        else{
          pNow <- 2/(size.i)
          if (pNow < 1){
            p <- (density - pNow)/(1-pNow)
            if (p > 0){
              for (j in 1:(levels-1))
                for (k in 1:levelSizes[j]){
                  begin <- perm[groundLvl[j]+k]
                  for (end in perm[(groundLvl[j+1]+1):size.i])
                  if (poks[begin,end] == 0)
                    poks[begin,end] <- sample(0:1,1,prob = c(1-p,p))
                }
            }
          }
        }
      }
      # ###############
      perm <- perm[(size.i + 1):length(perm)]
    }

    colnames(poks) <- as.character(1:items)
    rownames(poks) <- colnames(poks)
    return(poks)
  }

  nmfComLearn <- function(R, concepts){
    QSComGen <- function(Q, S){
      R <- (Q/rowSums(Q)) %*% S
      R[R >= 0.5] <- 1
      R[R < 0.5] <- 0
      return(R)
    }
    learn <- nmfLearn(R, concepts = concepts, func = QSComGen)
    Q <- learn$Q
    S <- learn$S
    conceptsDiff <- sapply(1:concepts,function(x){1-mean(S[x,])})
    list(Q = Q, M = S, concept.exp = conceptsDiff)
  }
  nmfConLearn <- function(R, concepts){
    QSConGen <- function(Q, S){
      return(0 + !(Q%*%(1-S)))
    }
    learn <- nmfLearn(R, concepts = concepts, func = QSConGen)
    Q <- learn$Q
    S <- learn$S

    conceptsDiff <- sapply(1:concepts,function(x){1-mean(S[x,])})
    list(Q = Q, M = S, concept.exp = conceptsDiff)
  }
  nmfDisLearn <- function(R, concepts){
    QSDisGen <- function(Q, S){
      return(1-!(Q%*%S))
    }
    learn <- nmfLearn(R, concepts = concepts, func = QSDisGen)
    Q <- learn$Q
    S <- learn$S

    conceptsDiff <- sapply(1:concepts,function(x){1-mean(S[x,])})
    list(Q = Q, M = S, concept.exp = conceptsDiff)
  }
  linAvgLearn <- function(R, concepts){
    Q <- genQRand(nrow(R), concepts)
    S <- matrix(0,concepts, ncol(R))
    space <- genQMax(concepts,concepts)
    space <- space[sample(1:nrow(space)),]

    learnQ <- function(){
      ref <- R[iQ,]
      predict <- QSAvgGenR2(Q = space, S = S)
      distance <- colSums((t(predict) - ref)^2)
      best <- which.min(distance)[1]
      t(space[best,])
    }

    learnS <- function(){
      ref <- R[,iS]
      Qn <- Q/rowSums(Q)
      # least square est of S squared
      # Qn %*% S2 ~ R^2 = R
      S2 <- ginv(Qn) %*% ref
      #clipping works because the surface is convex
      S2[S2 > 1] <- 1
      S2[S2 < 0] <- 0
      return(sqrt(S2))
    }

    hault <- 0
    threshold <- max(nrow(Q), ncol(S))
    permS <- sample(ncol(S))
    permQ <- sample(nrow(Q))

    for (i in 1:1000){
      idS <- (i-1) %% ncol(S) + 1
      idQ <- (i-1) %% nrow(Q) + 1
      if (idS == 1) permS <- sample(ncol(S))
      if (idQ == 1) permQ <- sample(nrow(Q))
      iS <- permS[idS]
      iQ <- permQ[idQ]

      lS <- learnS()
      lQ <- learnQ()

      progress = any(S[,iS]!=lS) | any(Q[iQ,]!=lQ)
      if (progress == TRUE) hault <- 0
      else hault <- hault + 1
      if (hault == threshold) break

      S[,iS] <- learnS()
      Q[iQ,] <- learnQ()
    }

    list(Q = Q, S = S)
  }
  dinaLearn <- function(R, Q){
    learn <- din(data = t(R), q.matrix = Q, rule = "DINA", progress = FALSE)
    concepts <- ncol(Q)

    s <- learn$pattern$mle.est
    S <- sapply(s, function(x){
      sapply(1:concepts, function(y){
        as.numeric(substring(x,y,y))
      })
    })
    slip <- learn$slip$est
    guess <- learn$guess$est
    skillSpace <- t(learn$attribute.patt.splitted)
    skillDist <- learn$attribute.patt$class.prob

    list(Q = Q, M = S, skill.space = skillSpace, skill.dist = skillDist, slip = slip, guess = guess)
  }
  dinoLearn <- function(R, Q){
    learn <- din(data = t(R), q.matrix = Q, rule = "DINO", progress = FALSE)
    concepts <- ncol(Q)

    s <- learn$pattern$mle.est
    S <- sapply(s, function(x){
      sapply(1:concepts, function(y){
        as.numeric(substring(x,y,y))
      })
    })
    slip <- learn$slip$est
    guess <- learn$guess$est
    skillSpace <- t(learn$attribute.patt.splitted)
    skillDist <- learn$attribute.patt$class.prob

    list(Q = Q, M = S, skill.space = skillSpace, skill.dist = skillDist, slip = slip, guess = guess)
  }
  ks.init <- function(raw, alpha.c, alpha.p, p.min) {
    student.var <- var(rowMeans(raw))
    raw <- t(raw)
    s.less.na <- colSums(!is.na(raw))
    raw.sum <- colSums(raw, na.rm=T)
    p <- (raw.sum+1)/(s.less.na+2)
    odds <- p/(1-p)
    ans.cp.t <- replace(raw, is.na(raw), 0) # answers for crossprod computations of success
    ans.cp.f <- round(replace(!raw, is.na(raw), 0)) # answers for crossprod computations of failures
    ft <- array(c(crossprod(ans.cp.t,ans.cp.t), # frequency table of TT, TF, FT, and FF
                  # f11, f21, f12, f22
                  crossprod(ans.cp.t,ans.cp.f),
                  crossprod(ans.cp.f,ans.cp.t),
                  crossprod(ans.cp.f,ans.cp.f)),
                c(ncol(ans.cp.t), ncol(ans.cp.t), 4)) + 1 # Laplace correction of + 1
    condp.t <- (ft[,,1]) / (ft[,,1]+ft[,,3]) # P(row|col)
    condp.f <- (ft[,,2]) / (ft[,,2]+ft[,,4]) # P(row|!col)
    odds.t <- PToOdds(condp.t)
    odds.f <- PToOdds(condp.f)
    state=odds
    # or <- list(t=odds.t/odds, f=odds.f/odds) # something to try (doesn't get exactly same result)
    # Start computing interaction test based on approximation of SE of log.odds.ratio : \sqrt(\sum_i 1/n_i)
    log.odds.ratio <- log((ft[,,1] * ft[,,4])/(ft[,,2] * ft[,,3]))
    log.odds.se <- sqrt((1/ft[,,1] + 1/ft[,,2] + 1/ft[,,3] + 1/ft[,,4]))
    log.odds.p <- 2 * pnorm(- abs(log.odds.ratio) / log.odds.se) # two-tail test for a normal distribution
    # log.odds.interaction is a matrix of the pairs that passed the interaction test
    log.odds.interaction <- (log.odds.p < alpha.c)
    m.rel <- log.odds.interaction
    diag(m.rel) <- F
    # Compute P(B=1|A=1)
    a1 <- (ft[,,1]+ft[,,3])-2             # substract Laplace correction
    b1a1 <- (ft[,,1])-1                   # substract Laplace correction
    # apply binom.test to slots that passed the interaction test
    p.b1a1.v <- apply(cbind(b1a1[m.rel], a1[m.rel]),
                      1,              # by row
                      function(n.k) pbinom(n.k[1], n.k[2], p.min))
    # p.b1a1.v is a vector and now we need a matrix
    p.b1a1 <- matrix(F, ncol(m.rel), ncol(m.rel))
    # Why is this '>' here and below??  Should be corrected by inverting the ratio.
    p.b1a1[m.rel] <- p.b1a1.v > alpha.p                 # matrix is re-indexed by m
    # Repeat for p.a0b0 (P(A=0|B=0)
    # Compute P(A=0|B=0)
    a0 <- (ft[,,4]+ft[,,3])-2           # substract Laplace correction
    a0b0 <- (ft[,,4])-1                 # substract Laplace correction
    p.a0b0.v <- apply(cbind(a0b0[m.rel], a0[m.rel]),
                      1,              # by row
                      function(n.k) pbinom(n.k[1], n.k[2], p.min))
    # p.a0b0.v is a vector and now we need a matrix
    p.a0b0 <- matrix(F, ncol(m.rel), ncol(m.rel))
    p.a0b0[m.rel] <- p.a0b0.v  > alpha.p               # matrix is re-indexed by m
    # The relation matrix is the combination of both tests (given that the interaction test is
    # already taken into account) and we put it in integer format for backward compatibility.
    # Transpose is also for backward compatibility
    m.rel <- t(round(p.a0b0 & p.b1a1))
    # note: variation qui devrait en theorie etre meilleure mais, en fait, n'apporte aucune difference
    # condp.t <- t(apply(raw,2,function(c) (colSumsRobust(raw[c==1,])+(2*p))/(raw.sum+2) )) # Kononenko (1991) citant Chestnik (1990)
    or <- list(t=t(m.rel) * odds.t/odds,      # We only retain odds ratios of links and in the next
               # instructions we set the others to 1 such that it has
               # not influence in the computation of new evidence
               f=m.rel * odds.f/odds)
    or$t[or$t==0] <- 1                # neutral evidence effect
    or$f[or$f==0] <- 1                # neutral evidence effect
    nlinks = colSums(m.rel, na.rm=T) + rowSums(m.rel, na.rm=T)
    log.nlinks = 0.6931472 / (log((nlinks+1)) + 0.6931472) # 0.6931472 is the entropy of 0.5
    list(student.var = student.var, avg.success = mean(raw), state = state, or.t = or$t, or.f = or$f, po = m.rel,
         alpha.c = alpha.c, alpha.p = alpha.p, p.min = p.min)
  }
  irt2plLearn <- function(R){

    t <- rnorm(ncol(R))
    a <- rnorm(nrow(R)) # a = -discrimination
    b <- rnorm(nrow(R)) # b = discrimination * difficulty
    p <- c(t,a,b) # collective parameter

    sigmoid <- function(param){
      t <- param[1:ncol(R)]
      a <- param[(ncol(R)+1):(ncol(R)+nrow(R))]
      b <- param[(ncol(R)+nrow(R)+1):length(param)]
      linear <- a%*%t(t) + b%*%t(rep(1,ncol(R)))
      return(1/(1+exp(linear)))
    }

    cost <- function(param){
      s <- sigmoid(param = param)
      y1 <- log(s)
      y0 <- log(1-s)
      return(-sum(R*y1+(1-R)*y0))
    }

    grad <- function(param){
      s <- sigmoid(param = param)
      ga <- colSums(t(s - R)*t)
      gb <- rowSums(s-R)
      gt <- colSums((s-R)*a)
      return(c(gt,ga,gb))
    }

    learn <- optim(p, cost, grad)

    t <- learn$par[1:ncol(R)]
    a <- learn$par[(ncol(R)+1):(ncol(R)+nrow(R))]
    b <- learn$par[(ncol(R)+nrow(R)+1):length(learn$par)]

    abi <- t
    dis <- -a
    dif <- b / dis

    list(dis = dis, dif = dif, abi = abi)
  }
  expLearn <- function(R){
    stexp <- colMeans(R)
    itexp <- rowMeans(R)
    list (st.exp = stexp, it.exp = itexp)
  }
  bktPerItemLearn <- function(R, order){
    if (is.null(order)) order = rep(1,nrow(R))
    items <- max(order)
    students <- ncol(R)
    probInitS <- matrix(0,items,students)
    L <- matrix(0,items, students)
    slip <- matrix(0,items, students)
    guess <- matrix(0,items, students)

    for (i in 1:items){
      Ri <- R[which(order == i),]
      for (j in 1:students){
        learn <- binaryHMMLearn(Ri[,j])
        probInitS[i,j] <- learn$probInitS
        L[i,j] <- learn$L
        slip[i,j] <- learn$slip
        guess[i,j] <- learn$guess
      }
    }
    list(S = probInitS, L = L, bkt.slip = slip, bkt.guess = guess,
         time = nrow(R), order = order, per.item = TRUE, Q = diag(items))
  }
  bktPerTestLearn <- function(R){
    items <- dim(R)[1]
    students <- dim(R)[2]
    probInitS <- matrix(0,items,students)
    L <- matrix(0,items, students)
    slip <- matrix(0,items, students)
    guess <- matrix(0,items, students)
    for (i in 1:items){
      for (j in 1:students){
        cat(paste0("\tItem ",to.str(i,items)," Student ", to.str(j,students),"\n"))
        learn <- binaryHMMLearn(R[i,j,])
        probInitS[i,j] <- learn$probInitS
        L[i,j] <- learn$L
        slip[i,j] <- learn$slip
        guess[i,j] <- learn$guess
      }
    }
    list(S = probInitS, L = L, bkt.slip = slip, bkt.guess = guess,
         time = dim(R)[3], order = NULL, per.item = FALSE, Q = diag(items))
  }
  bktBinLearn <- function(R, order){
    r <- NULL #return this
    if (length(dim(R)) == 2) return(bktPerItemLearn(R, order))
    else return(bktPerTestLearn(R))
  }

  #======================+
  # Channeling functions |
  #======================+

  #----------+
  # Upstream |
  #----------+

  stexp.itexp.2.exp <- function(x){expGen(x[[1]], x[[2]])}
  dis.dif.abi.2.irt <- function(x){logitGen(x[[1]],x[[2]],x[[3]])}
  Q.M.slip.guess.2.dina <- function(x){dinaGen(x[[1]],x[[2]],x[[3]],x[[4]])}
  Q.M.slip.guess.2.dino <- function(x){dinoGen(x[[1]],x[[2]],x[[3]],x[[4]])}
  Q.M.2.nmf.con <- function(x){QMConGen(x[[1]],x[[2]])}
  Q.M.2.nmf.dis <- function(x){QMDisGen(x[[1]],x[[2]])}
  Q.M.2.nmf.com <- function(x){QMComGen(x[[1]],x[[2]])}
  Q.S.2.lin.avg <- function(x){QSLinAvgGen(x[[1]],x[[2]])}
  stvar.stu.state.or.po.2.poks <- function(x){
    Gen.Synthetic.POKS.OR(x[[1]],x[[2]],x[[3]],x[[4]],x[[5]],x[[6]],x[[7]],x[[8]],x[[9]])}
  stvar.stu.state.po.2.poks <- function(x){
    Gen.Synthetic.POKS(x[[1]],x[[2]],x[[3]],x[[4]],x[[5]],x[[6]],x[[7]])}
  st.po.avg.2.poks <- function(x){poksGen(x[[1]],x[[2]],x[[3]],x[[4]],x[[5]],x[[6]])}
  S.L.slip.guess.time.order.peritem.2.bkt <- function(x){
    skillBktGen(x[[1]],x[[2]],x[[3]],x[[4]],x[[5]],x[[6]],x[[7]])}
  S.L.slip.guess.time.order.peritem.Q.mod.2.bkt <- function(x){
    qBktGen(x[[1]],x[[2]],x[[3]],x[[4]],x[[5]],x[[6]],x[[7]],x[[8]],x[[9]])}
  time.items.2.order <- function(x){(1:x[[1]] - 1) %% x[[2]] + 1}
  po.2.state <- function(x){po2State(x[[1]])}
  stvar.po.2.or.t <- function(x){stVarPo2Ort(x[[1]],x[[2]])}
  stvar.po.2.or.f <- function(x){stVarPo2Orf(x[[1]],x[[2]])}
  items.tree.depth.dens.per.2.po <- function(x){
    genPoks(x[[1]],x[[2]],x[[3]],x[[4]],x[[5]],x[[6]],x[[7]],x[[8]],x[[9]])}
  items.concepts.2.Q <- function(x){genQRand(x[[1]],x[[2]])}
  rn <- function(x) {runif(x[[1]],0,1)}
  rmn <- function(x) {
    matrix(runif(x[[1]]*x[[2]],0,1),x[[1]],x[[2]])
  }
  mean.n.2.vec <- function(x){
    m <- x[[1]]
    n <- x[[2]]
    sapply(1:n, function(x){
      i <- n-x+1
      r <- runif(1,max(i*m-(i-1),0),min(i*m,1))
      m <<- (i*m - r)/(i-1)
      return(r)
    })
  }
  mean.n.var.2.vec <- function(x){
    m <- x[[1]]
    n <- x[[2]]
    v <- x[[3]]
    if (v == 0) v <- 1e-100
    s <- m*(1-m)/v - 1
    if (s < 0) {
      warning('Cannot achieve the specified variance')
      return(mean.n.2.vec(list(m,n)))
    }
    rbeta(n, s*m, s - s*m)
  }
  rmean.n.cvar.2.mat <- function(x){
    n <- x[[2]]
    v <- x[[3]]
    if (v == 0) v <- 1e-100
    t(sapply(x[[1]], function(m){
      s <- m*(1-m)/v - 1
      if (s < 0) {
        warning('Cannot achieve the specified variance')
        return(mean.n.2.vec(list(m,n)))
      }
      rbeta(n, s*m, s - s*m)
    }))
  }
  con.size.2.skspace <- function(x){
    concepts <- x[[1]]
    size <- x[[2]]
    twoC <- 2^concepts
    if (size > twoC) stop("skill.space.size cannot be larger than 2^concepts")
    maxCombn(concepts)[,sample(twoC,size)]
  }
  stu.skspace.skdist.2.M <- function(x){
    x[[2]][,sample(1:length(x[[3]]),size=x[[1]],prob = x[[3]],replace=TRUE)]
  }
  stu.conexp.2.M<- function(x){
    conexp <- x[[2]]
    sapply(1:x[[1]], function(dum){
      sapply(conexp, function(p){
        sample(0:1,1,prob=c(1-p,p))
      })
    })
  }

  #------------+
  # Downstream |
  #------------+

  exp.2.stexp.itexp <- function(x){expLearn(x[[1]])}
  irt.2.dis.dif.abi <- function(x){irt2plLearn(x[[1]])}
  dina.2.Q.M.space.slip.guess <- function(x){dinaLearn(x[[1]],x[[2]])}
  dino.2.Q.M.space.slip.guess <- function(x){dinoLearn(x[[1]],x[[2]])}
  nmf.con.2.Q.M.conexp <- function(x){nmfConLearn(x[[1]],x[[2]])}
  nmf.dis.2.Q.M.conexp <- function(x){nmfDisLearn(x[[1]],x[[2]])}
  nmf.com.2.Q.M.conexp <- function(x){nmfComLearn(x[[1]],x[[2]])}
  lin.avg.2.Q.S <- function(x){linAvgLearn(x[[1]],x[[2]])}
  poks.learn <- function(x){ks.init(x[[1]],x[[2]],x[[3]],x[[4]])}
  bkt.bin.learn <- function(x){bktBinLearn(x[[1]],x[[2]])}

  order.2.time.items <- function(x){list(length(x),max(x))}
  n.row.col <- function(x){list(nrow(x),ncol(x))}
  n.row.col.rmean <- function(x){list(nrow(x),ncol(x),rowMeans(x))}
  length.l <- function(x){list(length(x))}
  mean.length <- function(x){list(mean(x),length(x))}
  mean.length.var <- function(x){list(mean(x),length(x),var(x))}
  n.row.col.cvar.rmean <- function(x){list(nrow(x),ncol(x),var(colMeans(x)),rowMeans(x))}
  skspsize.min.con <- function(x){
    r <- ceiling(log(x,2))
    class(r) <- "min"
    list(r)
  }
  max.bound.min <- function(x){
    r <- x
    class(r) <- "max"
    list(r)
  }

  #===================================================================================
  # Definition of node.i has the following syntax:
  # node.i <- list(S, L, fS, fL)
  # Where S is a set of nodes that can be infered from node.i
  # and L = list(set.of.nodes.1, set.of.nodes.2, ...)
  # set.of.nodes.k is a minimal set of nodes that can sufficiently generate node.i
  # and fS is a function that maps from node.i to S
  # and fL is a list of functions that map respective sets in L to node.i
  #
  # e.g.
  # state. <- list(c("items"), list(c("po","items")), fS, fL)
  # then node state can be generated from po and items by fL
  # and items can be infered from state by fS
  #===================================================================================

  #------------+
  # root nodes |
  #------------+

  # root nodes to prevent conflicts and detect insufficiency
  root. <- list(NULL, list(NULL), NULL, list(NULL))
  items. <- root.
  students. <- root.
  concepts. <- root.
  default.vals. <- root.

  # root nodes with predefined default values initialized only when needed
  root.factory <- function(name){
    list(NULL, list(c("default.vals")), NULL, list(function(x){x[[1]][[name]]}))
  }
  trans. <-            root.factory("trans")
  bkt.guess.st.var. <- root.factory("bkt.guess.st.var")
  bkt.slip.st.var. <-  root.factory("bkt.slip.st.var")
  S.st.var. <-         root.factory("S.st.var")
  L.st.var. <-         root.factory("L.st.var")
  abi.mean. <-         root.factory("abi.mean")
  abi.sd. <-           root.factory("abi.sd")
  alpha.c. <-          root.factory("alpha.c")
  alpha.p. <-          root.factory("alpha.p")
  p.min. <-            root.factory("p.min")
  bkt.mod. <-          root.factory("bkt.mod")
  min.ntree. <-        root.factory("min.ntree")
  min.depth. <-        root.factory("min.depth")
  min.it.per.tree. <-  root.factory("min.it.per.tree")
  density. <-          root.factory("density")
  per.item. <-         root.factory("per.item")
  avg.success. <-      root.factory("avg.success")
  student.var. <-      root.factory("student.var")
  time. <-             root.factory("time")

  #--------------------------------------------------------------------------+
  # leaf nodes, correspond to a dataset in regard of the respective model    |
  # Third entries in the below leaf nodes are supposed to be learn functions |
  #--------------------------------------------------------------------------+

  exp. <- list(c("st.exp","it.exp"), list(c("st.exp","it.exp")),
               exp.2.stexp.itexp, list(stexp.itexp.2.exp))
  irt. <- list(c("dis","dif","abi"), list(c("dis","dif","abi")),
               irt.2.dis.dif.abi, list(dis.dif.abi.2.irt))
  dina. <- list(c("Q","M","skill.space","skill.dist","slip","guess"), list(c("Q","M","slip","guess")),
                dina.2.Q.M.space.slip.guess, list(Q.M.slip.guess.2.dina))
  dino. <- list(c("Q","M","skill.space","skill.dist","slip","guess"), list(c("Q","M","slip","guess")),
                dino.2.Q.M.space.slip.guess, list(Q.M.slip.guess.2.dino))
  nmf.con. <- list(c("Q","M","concept.exp"), list(c("Q","M")),
                   nmf.con.2.Q.M.conexp, list(Q.M.2.nmf.con))
  nmf.dis. <- list(c("Q","M","concept.exp"), list(c("Q","M")),
                   nmf.dis.2.Q.M.conexp, list(Q.M.2.nmf.dis))
  nmf.com. <- list(c("Q","M","concept.exp"), list(c("Q","M")),
                   nmf.com.2.Q.M.conexp, list(Q.M.2.nmf.com))
  lin.avg. <- list(c("Q","S"), list(c("Q","S")),
                   lin.avg.2.Q.S, list(Q.S.2.lin.avg))
  poks. <- list(c("student.var","avg.success","state","or.t","or.f","po","alpha.c","alpha.p","p.min"),
               list(c("student.var", "students", "state", "or.t","or.f","po","alpha.c","alpha.p","p.min")
                    ,c("student.var", "students", "state", "po", "alpha.c", "alpha.p", "p.min")
                    ,c("students","po","avg.success","alpha.c","alpha.p","p.min")
                    ),
               poks.learn, list(stvar.stu.state.or.po.2.poks
                                ,stvar.stu.state.po.2.poks
                                ,st.po.avg.2.poks
                                ))
  bkt. <- list(c("S","L","bkt.slip","bkt.guess","time","order","per.item","Q"),
               list(c("S","L","bkt.slip","bkt.guess","time","order","per.item"),
                    c("S","L","bkt.slip","bkt.guess","time","order","per.item","Q","bkt.mod")),
               bkt.bin.learn, list(S.L.slip.guess.time.order.peritem.2.bkt,
                                   S.L.slip.guess.time.order.peritem.Q.mod.2.bkt))

  #--------------------+
  # Intermediate nodes |
  #--------------------+

  bkt.slip.it.exp. <- list(c("items"), list(c("items")),
                           length.l, list(rn))
  bkt.guess.it.exp. <- list(c("items"), list(c("items")),
                            length.l, list(rn))
  S.con.exp. <- list(c("concepts"), list(c("concepts")), length.l, list(rn))
  L.con.exp. <- list(c("concepts"), list(c("concepts")), length.l, list(rn))
  skill.space. <- list(c("concepts","skill.space.size"), list(c("concepts","skill.space.size")),
                       n.row.col, list(con.size.2.skspace))

  skill.space.size. <- list(c("concepts"), list(c("concepts")), skspsize.min.con,
                            list(function(x){2^x[[1]]}))
  skill.dist. <- list(c("skill.space.size"),list(c("skill.space.size")),
                      length.l, list(function(x){rep(1/x[[1]],x[[1]])}))
  concept.exp. <- list(c("concepts"),list(c("concepts")),length.l,list(rn))
  st.exp. <- list(c("avg.success","students","student.var"),
                  list(c("avg.success","students","student.var")),
                  mean.length.var, list(mean.n.var.2.vec))
  it.exp. <- list(c("avg.success","items"), list(c("avg.success","items")),
                  mean.length, list(mean.n.2.vec))
  max.ntree. <- list(c("min.ntree"), list(c("items")),
                     max.bound.min, list(function(x){x[[1]]}))
  max.depth. <- list(c("min.depth"), list(c("items")),
                     max.bound.min, list(function(x) {x[[1]]-1}))
  max.it.per.tree. <- list(c("min.it.per.tree"), list(c("items")),
                           max.bound.min, list(function(x) {x[[1]]}))

  dis. <- list(c("items"), list(c("items")),
               length.l, list(rn))
  dif. <- list(c("items"), list(c("items")),
               length.l, list(rn))
  abi. <- list(c("students","abi.mean","abi.sd"),
               list(c("students"),c("students","abi.mean","abi.sd")),
               function(x){list(length(x), mean(x), sd(x))},
               list(rn,function(x){rnorm(x[[1]],mean=x[[2]],sd=x[[3]])}))
  state. <- list(c("items"), list(c("po")),
                 length.l, list(po.2.state))
  or.t. <- list(c("items","items"), list(c("student.var","po")),
                n.row.col, list(stvar.po.2.or.t))
  or.f. <- list(c("items","items"), list(c("student.var","po")),
                n.row.col, list(stvar.po.2.or.f))
  po. <- list(c("items","items"), list(c("items","min.ntree","max.ntree",
                                         "min.depth","max.depth","density",
                                         "min.it.per.tree","max.it.per.tree","trans")),
              function(x){list(nrow(x),ncol(x))},
              list(items.tree.depth.dens.per.2.po))
  slip. <- list(c("items"), list(c("items")),
                length, list(rn))
  guess. <- list(c("items"), list(c("items")),
                 length, list(rn))
  Q. <- list(c("items","concepts"), list(c("items","concepts")),
             n.row.col, list(items.concepts.2.Q))
  S. <- list(c("concepts","students","S.st.var","S.con.exp"),
             list(c("concepts","students"),c("S.con.exp","students","S.st.var")),
             n.row.col.cvar.rmean, list(rmn, rmean.n.cvar.2.mat))
  M. <- list(c("concepts","students","concept.exp"),
             list(c("S"),c("students","skill.space","skill.dist"),
                  c("students","concept.exp")),
             n.row.col.rmean, list(function(x){round(x[[1]])},
                                   stu.skspace.skdist.2.M,
                                   stu.conexp.2.M))
  L. <- list(c("concepts","students","L.st.var","L.con.exp"),
             list(c("concepts","students"),c("L.con.exp","students","L.st.var")),
             n.row.col.cvar.rmean, list(rmn, rmean.n.cvar.2.mat))
  bkt.slip. <- list(c("items","students","bkt.slip.st.var","bkt.slip.it.exp"),
                    list(c("items","students"),c("bkt.slip.it.exp","students","bkt.slip.st.var")),
                    n.row.col.cvar.rmean, list(rmn, rmean.n.cvar.2.mat))
  bkt.guess. <- list(c("items","students","bkt.guess.st.var","bkt.guess.it.exp"),
                     list(c("items","students"),c("bkt.guess.it.exp","students","bkt.guess.st.var")),
                     n.row.col.cvar.rmean, list(rmn, rmean.n.cvar.2.mat))
  order. <- list(c("time","items"), list(c("time","items")),
                 order.2.time.items, list(time.items.2.order))
  
  # Assemble all nodes into a single structure named 'r'
  all.nodes <- as.list(environment())
  all.names <- names(all.nodes)
  r <- new.env()
  for (i in 1:length(all.names)) {
    name.i <- all.names[i]
    l <- nchar(name.i)
    dot <- substr(name.i,l,l)
    if (dot == ".") {
      node.i <- all.nodes[[i]]
      names(node.i) <- c('tell','gen','f.tell','f.gen')
      assign(substr(name.i,1,l-1), node.i, envir = r)
    }
  }
  return(r)
}

# Context structure
# 
# This constant is the structure of every context, it contains all the necessary
# information that the package operates on.
# 
# @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
# @seealso \code{assemble.structure}
# @export
STRUCTURE.ORIGINAL <- assemble.structure()
STRUCTURE <- STRUCTURE.ORIGINAL

#===========+
# CONSTANTS |
#===========+

#' A character vector of names of all available models
#' 
#' @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
#'
#' @export
ALL.MODELS <- c("exp", "irt", "poks", "dina", "dino",
                #"lin.pes",
                "lin.avg","nmf.con", "nmf.dis", "nmf.com", "bkt")

#' List of parameters to be kept for each model in the synthesize process
#' 
#' @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
#' 
#' @export
KEEP <- list(exp = c("avg.success","it.exp","student.var"),
             irt = c("dis","dif","abi.mean","abi.sd"),
             poks = c("po","student.var","state","alpha.c","alpha.p","p.min"),
             dina = c("Q","skill.space","skill.dist","slip","guess"),
             dino = c("Q","skill.space","skill.dist","slip","guess"),
             lin.avg = c("Q", "S.st.var", "S.con.exp"),
             nmf.con = c("Q", "concept.exp"),
             nmf.dis = c("Q", "concept.exp"),
             nmf.com = c("Q", "concept.exp"),
             bkt = c("S.st.var","S.con.exp","L.st.var","L.con.exp",
                     "bkt.slip.st.var","bkt.slip.it.exp",
                     "bkt.guess.st.var","bkt.guess.it.exp",
                     "time","order","per.item","Q"))

# @export
DEFINITE <- c("items","students","concepts","time","skill.space.size")

# @export
BOUND.CLASSES <- c("min", "max")

# @export
INTEGER <- c(DEFINITE,
             "min.ntree","max.ntree","min.depth","max.depth",
             "min.it.per.tree","max.it.per.tree")

#=====================+
# OPERATING FUNCTIONS |
#=====================+

#-----------------------------------------------------------------------------+
# argument pars stands for a list of all parameters across all models         |
# It is meant to be produced and updated by the function pars()               |
# down.stream(), and up.stream() are general purpose functions                |
# that will be used as building blocks for functions at user-interface level  |
#-----------------------------------------------------------------------------+

#-----------------------------------------------------------------------------+
# down.stream() propagates all obtainable info through type-1 connection      |
# in the STRUCTURE, also checks for conflicts.                                |
# up.stream() propagates info through type-2 connection in the STRUCTURE,     |
# the propagation is tailored so that a specified target can be calculated    |
#-----------------------------------------------------------------------------+
 
# Propagate information downwards
#
# This function takes the available parameters and try to learn all
# possible parameters at lower level, simultaneously check for conflicts
#
# param pars an object of \code{context} class describes all available information in current context
# return a new \code{context} object obtained from the input
# author Hoang-Trieu Trinh
# details
# This function use breadth-first scheme to propagate information in
# the structure, using the learning functions indicated in 3rd element
# of each node inside \code{STRUCTURE} to learn the corresponding values of
# nodes indicated in the 1st element
# export
down.stream <- function(pars){
  curr <- names(pars)[which(sapply(pars,is.null) == 0)]
  
  # breadth-first propagating
  while(length(curr) > 0){
    new <- NULL
    for (i in 1:length(curr)){
      var.name <- curr[i]
      var.val <- pars[[var.name]]
      child.names <- edmtree.fetch(var.name)$tell #STRUCTURE[[var.name]][[1]]
      if (is.null(child.names)) next
      child.val <- get(var.name, envir = STRUCTURE)$f.tell(var.val) #STRUCTURE[[var.name]][[3]](var.val)

      child.not.null <- which(sapply(child.val, function(x){is.null(x)})==0)
      child.names <- child.names[child.not.null]
      child.val <- child.val[child.not.null]
      
      for (j in 1:length(child.names)){
        child.j.val <- pars[[child.names[j]]]
        if (!is.null(child.j.val) &
            ((child.names[j] %in% DEFINITE) |
             (class(child.val[[j]]) %in% BOUND.CLASSES))){
          if (!suppressWarnings(compat(child.j.val,child.val[[j]]))){
            if (class(child.val[[j]]) %in% BOUND.CLASSES)
              stop(paste0("'", child.names[j],"' violates bound suggested by '",var.name,"'"))
            else
              stop(paste0("'", child.names[j],"' receives different values at once"))
          }
        }
        else
          if (all(class(child.val[[j]]) != BOUND.CLASSES))
            pars[[child.names[j]]] <- child.val[[j]]
      }
      child.not.bound <-
        which(sapply(child.val,
                     function(x){class(x) %in% BOUND.CLASSES}) == 0)
      new <- c(new, child.names[child.not.bound])
    }
    curr <- unique(new)
  }
  pars
}

# Propagate information upwards
#
# This function takes the available parameters and generate higher
# level parameters in a tailored direction so that a specified
# target can be reached, also detects conflicts due to inactivated but required default values.
#
# param target a character string indicates the target's name
# param pars an object of \code{context} class describes all available information in current context
# param progress a boolean value indicates if the generating process should be printed
# return a new \code{context} object obtained from the input, if the target cannot be reach,
# the old \code{context} object is returned
# author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
# details
# This function runs a recursive search for available information at lower level
# nodes in the structure that has been provided by the input. Whenever there is
# more than two ways to generate a parameter, the function chooses the one that
# requires inputs that is more likely to be learned directly from the target.
# seealso \code{which.closest}
# export
up.stream <- function(target, pars, target.base = TRUE, progress = FALSE){
  miss <- NULL
  input <- names(pars)[which(sapply(pars,is.null) == 0)]
  new.pars <- pars
  trace <- list(NULL)
  track <- list(NULL)
  fill <- FALSE

  check.track <- function(node.name){

    if (!is.null(new.pars[[node.name]])) return(TRUE)
    gen.methods <- edmtree.fetch(node.name)$gen #STRUCTURE[[node.name]]$gen
    if (is.null(unlist(gen.methods))) {
      if (is.null(miss)) miss <<- node.name
      return(FALSE)
    }

    or. <- sapply(gen.methods, function(x){
      prod(sapply(x,check.track)) # products are equivalent to AND-gate.
    })

    avail <- which(or. == 1)
    if (length(avail) == 0) {
      if (is.null(miss)) miss <<- node.name
      return(FALSE)
    }
    if (length(avail) == 1) pick <- avail
    else { 
      # criterion: 
        # pick the most usage first, 
        # available second, 
        # the most likely to be learned from target last
      if (target.base == FALSE | (target.base == TRUE & node.name == target)){
        ratio.avail <- rep(0,length(avail))
        ratio.usage <- ratio.avail
        for (i in 1:length(avail)){
          gen.med.i <- gen.methods[[avail[i]]]
          ratio.avail[i] <- sum(sapply(gen.med.i, function(x){
            x %in% input
          }))/length(gen.med.i)
          ratio.usage[i] <- sum(sapply(input, function(x){
            x %in% gen.med.i
          }))/length(input)
        }
        max.usage <- max(ratio.usage)
        ratio.avail <- ratio.avail * (ratio.usage == max.usage)
        max.avail <- max(ratio.avail)
        avail <- avail[ratio.avail == max.avail]
      }
      if (length(avail) == 1) pick <- avail
      else 
        pick <- avail[which.closest(target, gen.methods[avail])]
    }

    track[[node.name]] <<- pick
    return(TRUE)
  }
  follow <- function(node.name){
    node <- get(node.name, envir=STRUCTURE) #STRUCTURE[[node.name]]
    pick <- track[[node.name]]
    if (!is.null(pick)){ #which means, node already has a value
      gen.method <- node$gen[[pick]]
      if (identical(gen.method,"default.vals"))
        new.pars[[node.name]] <<- node$f.gen[[1]](list(new.pars$default.vals))
      else {
        dummy <- sapply(gen.method, follow) # this is a dummy variable 
        if (fill == TRUE & is.null(new.pars[[node.name]])){
          arg <- new.pars[gen.method] 
          names(arg) <- NULL # to avoid redundant args in the next function call 
          new.pars[[node.name]] <<- node$f.gen[[pick]](arg)
        }
      }
      if (fill == TRUE) trace[[node.name]] <<- gen.method # if fill==TRUE trace[]
    }
    return(NULL)
  }

  success <- check.track(target)
  if (success == FALSE)
    stop(paste0("Cannot reach '", target,"' since '", miss, "' is missing"))
    
  else{
    dummy <- follow(target)
    new.pars <- down.stream(new.pars)
    fill <- TRUE
    dummy <- follow(target)
    if (progress == TRUE & length(trace) > 1){
      print.trace <- function(node){
        if (is.null(trace[[names(node)]])) return(NULL)
        cat(paste0("Generate ",names(node)," from ", node,"\n"))
        child <- trace[names(node)]
        trace[[names(node)]] <<- NULL
        for (i in 1:length(child[[1]])){
          print.trace(trace[child[[1]][i]])
        }
      }
      print.trace(trace[target])
    }
    return(new.pars)
  }
}

#-------------------------------+
# User Interface's sub-routines |
#-------------------------------+

# Analyse a partial order knowledge structure
# 
# This function analyzes and return all the connected components of a partial order knowledge structure
# 
# param po the POK structure to be analyzed
# return a list with two components \code{ks} and \code{comp}, 
# being the original \code{po} and analyzed connected components of \code{po} 
# respectively, each component of \code{comp} is itself a list with two components 
# \code{matrix} and \code{level.sizes}, being the corresponding subgraph of 
# \code{po} and a vector indicates the number of items on each level of depth.
# author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
# export
dissect <- function(po){
  n <- nrow(po)
  temp <- po
  po.sym <- (po+t(po)) > 0
  temp.sym <- po.sym
  r <- list(po)
  r.sym <- list(po.sym)
  if (n==1) return(list(ks = po, comp = list(list(matrix = po, level.sizes = 1))))
  if (n > 2)
  for (i in 1:(n-2)){
    temp <- temp %*% po
    temp.sym <- temp.sym %*% po.sym
    r <- append(r, list(temp))
    r.sym <- append(r.sym, list(temp.sym))
  }
  s.cy <- matrix(0, n, n) # same.cycle
  s.co <- diag(n) # same.component
  for (i in 1:(n-1)){
    for (j in 1:(n-1))
      s.cy <- s.cy + (r[[i]] * t(r[[j]]))
    s.co <- s.co + r.sym[[i]]
  }
  s.cy <- 0 + (s.cy > 0)
  if (any(s.cy == 1)) stop("Loop detected in the graph")
  s.co <- 0 + (s.co > 0)
  s.co <- unique.matrix(s.co)
  
  root <- which(colSums(po) == 0)
  leaf <- which(rowSums(po) == 0)
  comp <- list()
  
  for (i in 1:nrow(s.co)){
    nodes.i <- which(s.co[i,] == 1)
    root.i <- intersect(root, nodes.i)
    leaf.i <- intersect(leaf, nodes.i)
    root.tell <- rep(-1,n)
    leaf.tell <- rep(-1,n)
    root.tell[root.i] <- 0
    leaf.tell[leaf.i] <- 0
    for (j in 1:(n-1)){
      fil <- r[[j]][root.i,]
      if (is.null(nrow(fil))) fil <- t(as.matrix(fil))
      reach <- which(colSums(fil) > 0)
      if (length(reach) == 0) break 
      root.tell[reach] <- j
    }
    depth.i <- max(root.tell)
    for (j in 1:(n-1)){
      reach <- which(rowSums(as.matrix(r[[j]][,leaf.i])) > 0)
      if (length(reach) == 0) break 
      leaf.tell[reach] <- j
    }
    leaf.tell <- depth.i - leaf.tell
    
    lvl.i <- rep(-1,n)
    skeleton <- which(leaf.tell == root.tell)
    lvl.i[skeleton] <- leaf.tell[skeleton]
    while (sum(lvl.i[nodes.i] == -1) != 0) {
      for (j in 1:n)
        if (!(j %in% skeleton) & (j %in% nodes.i)){
          ske.par <- intersect(skeleton, which(po[,j] == 1))
          ske.chi <- intersect(skeleton, which(po[j,] == 1))
          par.tell <- integer()
          chi.tell <- integer()
          if (length(ske.par) > 0) par.tell <- lvl.i[ske.par] + 1
          if (length(ske.chi) > 0) chi.tell <- lvl.i[ske.chi] - 1
          lvl.i[j] <- round(mean(append(par.tell, chi.tell)))
          if (!is.na(lvl.i[j])) skeleton <- append(skeleton,j)
          else lvl.i[j] <- -1
        }
    }
    new.order <- integer()
    lvlSizes <- integer()
    for (j in 0:depth.i){
      new.order <- append(new.order, which(lvl.i == j))
      lvlSizes <- append(lvlSizes, sum(lvl.i == j))
    }
    mat <- as.matrix(po[new.order, new.order])
    rownames(mat) <- new.order
    colnames(mat) <- new.order
    comp <- append(comp, list(list(matrix = mat, level.sizes = lvlSizes)))
  }
  
  list(ks = po, comp = comp)
}

#' Vizualize POK structure
#' 
#' @param po the dependency matrix of POKS to be vizualized
#' @return a list with two components \code{ks} and \code{comp}, 
#' being the original \code{po} and analyzed connected components of \code{po} 
#' respectively, each component of \code{comp} is itself a list with two components 
#' \code{matrix} and \code{level.sizes}, being the corresponding subgraph of 
#' \code{po} and a vector indicates the number of items on each level of depth.
#' @examples
#' # Example: Vizualising Partial Order structure
#' # Declare a context where there are 15 students and 20 items
#' p <- pars(students = 15, items = 20)
#' # Add information that the Partial Order Structure should have depth of 3, two connected components and no transitive links
#' p <- pars(p, min.depth = 3, max.depth = 3, min.ntree = 2, max.ntree = 2, trans = FALSE)
#' # Generate data to calculate the `po` parameter
#' poks.data <- gen("poks", p)
#' # Visualise the Partial Order Structure
#' v <- viz(poks.data$po)
#' # Print the analysed structure
#' print(v)
#' @author Hoang-Trieu trinh, \email{thtrieu@@apcs.vn}
#' @seealso \code{plotmat}
#' @importFrom diagram plotmat
#' @export
viz <- function(po){
  po <- dissect(po)
  n <- length(po$comp)
  n.row <- floor(sqrt(n))
  n.col <- ceiling(n/n.row)
  par(mfrow = c(n.row, n.col))
  for (i in 1:n){
    comp.i <- po$comp[[i]]
    plotmat(t(comp.i$matrix),
            pos = comp.i$level.sizes,
            lwd = 0.1,
            arr.type = "triangle",
            curve = 0,
            box.size = 0.03,
            box.type = "round",
            endhead = TRUE,
            arr.pos = 0.85,
            shadow.size = 0,
            cex.txt = 0)
  }
  return(po)
}

INITIALS <- new.env()
asin <- function(node.name, val){
  assign(node.name, val, envir = INITIALS)
}
asin('student.var', 1/12)
asin('avg.success', 0.5)
asin('time', 50L)
asin('S.st.var', 1/12)
asin('L.st.var', 1/12)
asin('bkt.slip.st.var', 1/12)
asin('bkt.guess.st.var', 1/12)
asin('min.ntree', 1L)
asin('min.depth', 0L)
asin('min.it.per.tree', 1L)
asin('per.item', FALSE)
asin('bkt.mod', 'dina')
asin('density', 0.5)
asin('alpha.c', 0.25)
asin('alpha.p', 0.25)
asin('p.min', 0.5)
asin('abi.mean', 0)
asin('abi.sd', 1)
asin('trans', FALSE)

#=======================================+
# Environment containing initial values |
#=======================================+

#' Create an R environment that contains default values for root parameters
#' 
#' @param student.var variance of student expected success rate
#' @param avg.success mean value of the response matrix
#' @param time the number of time steps for sequential data
#' @param S.st.var variance of student expected success rates of the skill matrix
#' @param L.st.var variance of student expected success rates of Learning Transition matrix
#' @param bkt.guess.st.var variance of expected values of students in Guess vector of BKT model
#' @param bkt.slip.st.var variance of expected values of students in Slip vector of BKT model
#' @param min.ntree minimum number of connected components of the partial order structure of items
#' @param min.depth minimum depth of the connected components of the partial order structure of items
#' @param min.it.per.tree minimum number of items per each connected component of the partial order structure
#' @param per.item a boolean value indicates if the students can improve after taking each item
#' @param bkt.mod a character string indicates which model governs the generating process for sequential data
#' @param density a real value between 0 and 1, indicates the connection density of the partial order structure of items
#' @param alpha.c parameter for learning by POKS model, see reference
#' @param alpha.p parameter for learning by POKS model, see reference
#' @param p.min p-value for interaction test while constructing POK structure
#' @param abi.mean mean value of the student abilities vector
#' @param abi.sd standard deviation of the student abilities vector
#' @param trans a boolean value indicates if transitive links are allowed in the partial order structure of items
#' @return an environment containing all default values of the specified parameters
#' @examples
#' # Example: 
#' # Declare a context where there are 15 students and 20 items
#' p <- pars(students = 15, items = 20)
#' # Add information that the Partial Order Structure should have depth of 3, two connected components and no transitive links
#' p <- pars(p, min.depth = 3, max.depth = 3, min.ntree = 2, max.ntree = 2, trans = FALSE)
#' # Generate data to calculate the `po` parameter
#' poks.data <- gen("poks", p)
#' # Visualise the Partial Order Structure
#' v <- viz(poks.data$po)
#' # Print the analysed structure
#' print(v)
#' @author Hoang-Trieu trinh, \email{thtrieu@@apcs.vn}
#' @export
default <- function(student.var = NULL, avg.success = NULL, time = NULL,
                 S.st.var = NULL, L.st.var = NULL,
                 bkt.slip.st.var = NULL, bkt.guess.st.var = NULL,
                 min.ntree = NULL, min.depth = NULL, min.it.per.tree = NULL,
                 per.item = NULL, bkt.mod = NULL, density = NULL,
                 alpha.c = NULL, alpha.p = NULL, p.min = NULL,
                 abi.mean = NULL, abi.sd = NULL, trans = NULL, ...){
  built.ins <- as.list(environment())
  calls <- names(as.list(match.call()))
  calls <- calls[2:length(calls)] # eliminate the name 'default'
  dots <- list(...)
  dots.names <- names(dots)
  if (length(dots.names) != length(unique(dots.names)))
    stop('Repeating arguments found')
  all.val <- append(built.ins,dots)
  calls.val <- all.val[calls]
  
  r <- INITIALS
  if (length(calls.val) > 0)
    for(i in 1:length(calls.val))
      if (calls[[i]] %in% names(STRUCTURE)){
        if (!is.null(calls.val[[i]])) # some of calls.val is NULL, ignore them
          assign(calls[[i]],calls.val[[i]], envir = r)
      }
      else
        stop("'",calls[[i]],"' is not found in current tree")
  
  class(r) <- 'default'
  return(r)
}

#' @export
keep <- function(model){
  KEEP[[model]]
}

#==========================+
# USER INTERFACE FUNCTIONS |
#==========================+

#' Create or update a context
#'
#' This function allows user assemble a new context or update an available context
#'
#' @param old.pars an object of \code{context} class describe the context that needed to be updated,
#' leave this parameter \code{NULL} if a new context is needed.
#' @param default.vals an environment contains default values for some parameters in the context, by default it is initialized by function \code{default}
#' @param dis a vector of discrimination values for each item
#' @param dif a vector of difficulty values for each item
#' @param abi a vector of ability values for each student
#' @param abi.mean mean value of parameter \code{abi}
#' @param abi.sd standard deviation of parameter \code{abi}
#' @param st.exp a vector of expected success rates for each student
#' @param it.exp a vector of expected success rates for each item
#' @param items number of items
#' @param concepts number of concepts
#' @param students number of students
#' @param state parameter for generating data from POKS model
#' @param po dependency matrix of a partial order knowledge structure among items
#' @param or.t parameter for generating data from POKS model
#' @param or.f parameter for generating data from POKS model
#' @param student.var variance of student expected success rate
#' @param avg.success mean value of the response matrix
#' @param min.ntree minimum number of connected components of \code{po}
#' @param max.ntree maximum number of connected components of \code{po}
#' @param trans a boolean value indicates if transitive links are allowed in \code{po}
#' @param min.depth minimum depth of the connected components of \code{po}
#' @param max.depth maximum depth of the connected components of \code{po}
#' @param density a real value between 0 and 1, indicates the connection density of \code{po}
#' @param min.it.per.tree minimum number of items per each connected component of \code{po}
#' @param max.it.per.tree maxinum number of items per each connected component of \code{po} 
#' @param alpha.c parameter for learning by POKS model, see reference
#' @param alpha.p parameter for learning by POKS model, see reference
#' @param p.min p-value for interaction test while constructing POK structure
#' @param slip a vector of slip factor for each item
#' @param guess a vector of guess factor for each item
#' @param per.item a boolean value indicates if the students can improve after taking each item
#' @param order a vector indicates in which order did the students take the test in case \code{per.item} is set to be \code{TRUE}
#' @param Q Q-matrix with size \code{items} times \code{concepts}
#' @param S Skill matrix with size \code{concepts} times \code{students}
#' @param M Skill mastery matrix with size\code{concepts} times \code{students}
#' @param L Learn matrix indicates the transition probabilities for \code{M} matrix
#' @param bkt.mod a character string indicates which model governs the generating process for sequential data
#' @param S.st.var variance of student expected success rates of matrix \code{S}
#' @param S.con.exp a vector of expected success rate for each concept in matrix \code{S}
#' @param L.st.var variance of student expected success rates of matrix \code{L}
#' @param L.con.exp a vector of expected success rate for each concept in matrix \code{L}
#' @param skill.space.size size of the skill space
#' @param skill.space a matrix with size \code{concepts} times \code{skill.space.size}
#' @param skill.dist a vector of length \code{skill.space.size} that sums to one, indicates the probability of each skill pattern in \code{skill.space.size}
#' @param concept.exp a vector of expected mastery rate for each concept
#' @param bkt.slip a matrix of size \code{items} times \code{students} indicates slip factor for each combination of one item and one student
#' @param bkt.guess a matrix of size \code{items} times \code{students} indicates slip factor for each combination of one item and one student
#' @param time the number of time steps for sequential data
#' @param bkt.slip.it.exp a vector of expected value for each item in \code{bkt.slip}
#' @param bkt.slip.st.var variance of expected values of students in \code{bkt.slip}
#' @param bkt.guess.it.exp a vector of expected value for each item in \code{bkt.guess}
#' @param bkt.guess.st.var variance of expected values of students in \code{bkt.guess}
#' @param irt a list with one component \code{R} being the response matrix, use in case of IRT model
#' @param exp a list with one component \code{R} being the response matrix, use in case of expected model
#' @param dina a list with two components \code{R} and \code{Q}, being the response matrix and Q matrix respectively, use in case of DINA model
#' @param dino a list with two components \code{R} and \code{Q}, being the response matrix and Q matrix respectively, use in case of DINO model
#' @param nmf.con a list with two components \code{R} and \code{concepts}, being the response matrix and number of concepts, use in case of NMF CONJUNCTIVE model
#' @param nmf.dis a list with two components \code{R} and \code{concepts}, being the response matrix and number of concepts, use in case of NMF DISJUNCTIVE model
#' @param nmf.com a list with two components \code{R} and \code{concepts}, being the response matrix and number of concepts, use in case of NMF COMPENSATORY model
#' @param lin.avg a list with two components \code{R} and \code{concepts}, being the response matrix and number of concepts, use in case of LINEAR AVERAGE model
#' @param poks a list with four components \code{R}, \code{alpha.p}, \code{alpha.c}, \code{p.min}, use in case of POKS model
#' @param bkt a list with two components \code{R} and \code{order}, being the response matrix and its corresponding \code{order} vector (in case student improvement is allowed between taking two items), use in case of sequential data
#' @return an object of \code{context} class describes the updated or newly assembled context
#' @examples
#' # Declare a context where there are 15 students and 20 items
#' p <- pars(students = 15, items = 20)
#' class(p)
#' # See all parameters inside p
#' names(p)
#' # See the currently available parameters in p
#' print(p)
#' @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
#' @details
#' This function takes in a set of parameters that the user input and assembles them
#' into a \code{context} object, also checks for some simple types of potential conflicts
#' @seealso \code{init}
#' @export

pars <- function(old.pars = NULL,
                 default.vals = default(),
                 dis = NULL, dif = NULL, abi = NULL,
                 abi.mean = NULL, abi.sd = NULL,
                 st.exp = NULL, it.exp = NULL,
                 items = NULL, concepts = NULL, students = NULL,
                 state = NULL, po = NULL, or.t = NULL, or.f = NULL,
                 student.var = NULL, avg.success = NULL,
                 min.ntree = NULL, max.ntree = NULL, trans = NULL,
                 min.depth = NULL, max.depth = NULL, density = NULL,
                 min.it.per.tree = NULL, max.it.per.tree = NULL,
                 alpha.c= NULL, alpha.p= NULL, p.min= NULL,
                 slip = NULL, guess = NULL, per.item = NULL, order = NULL,
                 Q = NULL, S = NULL, M = NULL, L = NULL, bkt.mod = NULL,
                 S.st.var = NULL, S.con.exp = NULL,
                 L.st.var = NULL, L.con.exp = NULL,
                 skill.space.size = NULL, skill.space = NULL,
                 skill.dist = NULL, concept.exp = NULL,
                 bkt.slip = NULL, bkt.guess = NULL, time = NULL,
                 bkt.slip.it.exp = NULL, bkt.slip.st.var = NULL,
                 bkt.guess.it.exp = NULL, bkt.guess.st.var = NULL,
                 irt = NULL, exp = NULL, dina = NULL, dino = NULL,
                 nmf.con = NULL, nmf.dis = NULL, nmf.com = NULL,
                 lin.avg = NULL, poks = NULL, bkt = NULL, ...){
  new.pars <- NULL #return this.
  
  # Deal with the dots
  built.ins <- as.list(environment())
  calls <- names(as.list(match.call()))
  calls <- calls[2:length(calls)] # eliminate the name 'pars'
  dots <- list(...)
  dots.names <- names(dots)
  if (length(dots.names) != length(unique(dots.names)))
    stop('Repeating arguments found')
  all.val <- append(built.ins,dots)
  calls.val <- all.val[calls]
  
  if (!is.null(old.pars)) { # if this is an updating
    if (!identical(class(old.pars),c("context")))
      stop("'old.pars' must be an object of the 'context' class")
    new.pars <- old.pars
    update <- calls.val[2:length(calls.val)] # first component is $old.pars
    new.pars[names(update)] <- update # note that something in update can be NULL
  }
  else new.pars <- calls.val # if this is a brand new context
  
  new.pars <- new.pars[which(sapply(new.pars,is.null) == 0)] # eliminate the NULLs
  if (is.null(new.pars$default.vals)) new.pars$default.vals = default() # user accidentally delete default.vals
  
  # Make sure integers are integers
  sapply(INTEGER, function(x){
    if (!is.null(new.pars[[x]]))
      new.pars[[x]] <<- as.integer(new.pars[[x]])
  })
  
  # Infer all other obtainable info
  class(new.pars) <- c("context")
  down.stream(new.pars)
}

#' Get a parameter from the current context
#'
#' This function generates (if needed) the required target from a context
#'
#' @param target a character string indicates the target's name
#' @param pars an object of \code{context} class describes the given context
#' @param progress a boolean value indicates if the generating process should be printed or not
#' @return if success, a list with two components
#' \item{value}{value of the target}
#' \item{context}{the corresponding context}
#' if not success, NULL
#' @examples
#' # Declare a context
#' p <- pars(students = 20, items = 15)
#' # Regular way to access information inside a context
#' p$students # returns 20
#' # get.par is a alternative
#' get.par("students", p)
#' # However, it is not trivial to generate a skill mastery matrix from p
#' p$M # NULL returned
#' # get.par can do this
#' M <- get.par("M", p, progress = True)
#' print(M)
#' @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
#' @seealso \code{gen}
#' @export
get.par <- function(target, pars, progress = FALSE){
  g <- up.stream(target, pars, FALSE, progress)
  if (!is.null(g)) {
    ret <- list(g[[target]], g)
    names(ret) <- c("value", "context")
    return(ret)
  }
  else return(NULL)
}

#' Generate data for a model
#'
#' This function generates a context with a specified data unit activated
#'
#' @param model a character string indicates which model governs the generating process.
#' @param pars a context
#' @param n numer of runs
#' @param progress a boolean value indicates if the generating steps should be printed or not.
#' @return a context with its data unit activated
#' @examples
#' # Defind a context
#' p <- pars(students = 20, items = 15)
#' # Generate data from p by POKS model (Partial Order Knowledge Structure model) twice
#' poks.data <- gen("poks", p, n = 2, progress = TRUE)
#' # poks.data is a list of two contexts (since we generated data twice)
#' poks.data
#' # To access to the generated data, access to poks component
#' poks.data[[1]]$poks 
#' @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
#' @seealso \code{get.par}
#' @export
gen <- function(model, pars, n = 1, progress = FALSE){

  if (!(model %in% ALL.MODELS))
    stop(paste0("Model '",model,"' is not available"))
  if (!identical(class(pars),c("context")))
    stop(paste0("'pars' is of an invalid class"))

  r <-
    sapply(1:n,function(x){
      if (x > 1) progress <- FALSE
      trial <- up.stream(model, pars, TRUE, progress)
      if (is.null(trial))
        stop(paste0("Insufficient information to generate '",model,"'"))
      list(trial)
    })

  if (n > 1) return(r) else return(r[[1]])
}

#' Generate data for a set of models and contexts
#'
#'
#' @param model a character string indicates which model governs the learning process.
#' @param pars a context or a list of contexts
#' @param multiply a boolean value indicates in which way should \code{models} and \code{pars} be matched. If \code{TRUE}, each of the models is matched with every contexts in \code{pars}. Otherwise, they are matched element-wise.
#' if \code{TRUE} the generating process will be performed on every possible combination from \code{models} and \code{pars},
#' if \code{FALSE} each model will be matched with its respective context in the same order specified in \code{models} and \code{pars},
#' in other words, set \code{multiply} to \code{FALSE} will make \code{gen.apply} does the exact same thing to \code{mapply(gen,models,pars)}
#' @param n number of runs for each generation
#' @param progress a boolean value indicates if the generating steps should be printed or not.
#' @return a matrix with each entry is a context or a list of contexts, depending on the format indicated by \code{multiply}
#' @examples 
#' # Suppose p1 and p2 are two different contexts
#' dat.1 <- gen.apply(ALL.MODELS, list(p1, p2), multiply = TRUE, n = 5)
#' dat.2 <- gen.apply(ALL.MODELS, list(p1, p2), multiply = FALSE, n = 5)
#' @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
#' @seealso \code{gen}, \code{mapply}, \code{sapply}
#' @export
gen.apply <- function(models, pars, multiply = TRUE, n = 1, progress = FALSE){

  result <- NULL #return this
  if (identical(class(pars),c("context"))) pars <- list(pars)
  else if (class(pars) != "list") stop(paste0("Invalid type of argument pars"))

  # name all the contexts
  if (is.null(names(pars)))
    names(pars) <- sapply(1:length(pars), function(x){
      paste0("p",to.str(x,length(pars)))
    })
  else{
    anony.context <- which(names(pars) == "")
    num.ac <- length(anony.context)
    names(pars)[anony.context] <- sapply(1:num.ac, function(x){
      paste0("p",to.str(x,num.ac))
    })
  }
  
  if (multiply == FALSE){
    suppressWarnings(
      result <- as.matrix(mapply(function(x,y){
        gen(x, y, n = n, progress)
      },models, pars))
    )
    rownames(result) <- sapply(1:n, function(x){to.str(x,n)})
    suppressWarnings(
      colnames(result) <- mapply(function(x,y){
        paste(x,y,sep=".")
      }, models, names(pars))
    )
  } else {
    result <- as.matrix(sapply(models,function(x){
      sapply(1:length(pars), function(y){
        if (y > 1) progress <- FALSE
        list(gen(x, pars[[y]], n = n, progress))
      })
    }))
    if (length(pars) == 1) result <- t(result)
    colnames(result) <- models
    rownames(result) <- names(pars)
  }

  t(result)
}

#' Learn the most probable context for a given data
#'
#' @param model a character string indicates which model governs the learning process.
#' @param data a list contains data that needs to be synthesized, first component is the response matrix, the other components are additional information that the specified model requires.
#' @return the most probable context corresponds to \code{data} under the assumptions made by \code{model}
#' @examples
#' # Let us make up some data to learn
#' p <- pars(students = 20, concepts = 4, items = 15)
#' poks.data <- gen("poks", p)
#' # Notice that the generated data is in component poks,
#' # together with other hyper-parameters for learning by POKS model.
#' poks.data$poks
#' # Assume we want to learn with DINA (Deterministic Input Noisy And) model
#' # then poks.data$poks is not relevant anymore, instead we need a Q-matrix
#' # For demonstration, let's just make it up
#' Q <- get.par("Q", p)$value
#' R <- poks.data$poks$R
#' dina_dat <- list(R=R, Q=Q)
#' # Now learn from poks.data
#' learned.poks <- learn("dina", data = dina_dat)
#' # learned.poks is a context with learned parameters
#' class(learned.poks) # returns "context"
#' @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
#' @export
learn <- function(model, data){

  if (!(model %in% ALL.MODELS))
    stop(paste0("Model '",model,"' is not available"))

  cat(paste0("Learning by '",model,"' ...\n"))

  learned.p <- pars()
  learned.p[[model]] <- data
  down.stream(learned.p)
}

#' Generate synthetic data
#' 
#' This function synthesize a given data under the assumptions of a given model
#'
#' @param model a character string indicates which model governs the synthesizing process.
#' @param data a list contains data that needs to be synthesized, first component 
#' is the response matrix, the other components are additional information that the
#' specified model requires.
#' @param keep.pars a character string vector contains names of the parameters to be
#'  kept after learning the most probable context from \code{data},
#' by default this parameter is set by values indicated in vector \code{KEEP}.
#' @param students number of students in the synthetic data, by default this number is kept.
#' @param n number of synthetic dataset(s) to generate.
#' @param progress a boolean value indicates if the generating steps should be printed or not.
#' @return a list with two components, first component is identical to argument \code{data}, second is a context or a list of contexts that have been generated.
#' @examples
#' # Let us make up some data to synthesize
#' dina.data <- gen('dina', pars(students = 20, concepts = 4, items = 5))$dina
#' dina.syn <- syn('dina', data = dina.data, students = 50, n = 10)
#' @author Hoang-Trieu Trinh, \email{thtrieu@@apcs.vn}
#' @details 
#' This function is essentially a wrapper of function \code{learn} and \code{gen}, 
#' where in between it eliminates all parameters that are not indicated in \code{keep.pars} in the learned context.
#' you are also given the option of changing the number of students.
#' @seealso \code{learn}, \code{gen}, \code{KEEP}
#' @export
syn <- function(model, data, keep.pars = keep(model),
                students = ncol(data$R), n = 1, progress = FALSE){
  learned.pars <- learn(model,data)
  filtered.pars <- pars(students = students)
  filtered.pars[keep.pars] <- learned.pars[keep.pars]
  filtered.pars <- down.stream(filtered.pars)
  list(data = data, synthetic = gen(model, filtered.pars, n = n, progress))
}

#' @export
edmtree.fetch <- function(node.name){
  if (!(node.name %in% names(STRUCTURE)))
    stop(paste0("'",node.name,"' is not found in current tree"))
  get(node.name, envir = STRUCTURE) #STRUCTURE[[node.name]]
}

#' @export
edmtree.remove <- function(node.name){
  temp = get(node.name, envir = STRUCTURE) #STRUCTURE[[node.name]]
  if (is.null(temp))
    stop(paste0("'",node.name,"' is not found in current tree"))
  else assign(node.name, NULL, envir=STRUCTURE) #STRUCTURE[[node.name]] <<- NULL
  temp
}

# @export
edmtree.check.root < function(node.name, node.val){
  # root. <- list(NULL, list(NULL), NULL, list(NULL))
  # list(NULL, list(c("default.vals")), NULL, list(function(x){x[[1]][[name]]}))
}

# @export
edmtree.check <- function(node.name, node.val) {
  
  # First check if node.name is root by looking at
  # whether tell or f.tell is NULL
  # If yes, both tell and f.tell is forced to NULL
  # Next, check if it is without default, by looking at 
  # whether gen or f.gen is list(NULL)
  # If yes, both gen and f.gen are corced to list(NULL) and node.val is returned
  # Else, i.e. it is root but with default initialisation, proceed like normal
  root <- FALSE
  if (is.null(node.val$tell) || is.null(node.val$f.tell)){ 
    message(paste0("'",node.name,"' appears to be a root node"))
    root <- TRUE
    if (!is.null(node.val$tell)){
      warning('tell is not NULL, automatically set it to NULL')
      node.val$tell <- NULL
    }
    if (!is.null(node.val$f.tell)){
      warning('f.tell is not NULL, automatically set it to NULL')
      node.val$f.tell <- NULL
    }
    if ((node.val$gen == list(NULL)) || (node.val$f.gen == list(NULL))){
      message(paste0("'",node.name,"' appears to have no default initialization"))
      if (node.val$gen != list(NULL)){
        warning('gen is not list(NULL), automatically set it to list(NULL)')
        node.val$gen <- list(NULL)
      }
      if (node.val$f.gen != list(NULL)){
        warning('f.gen is not list(NULL), automatically set it to list(NULL)')
        node.val$f.gen <- list(NULL)
      }
      return(node.val)
    } else {
      # This is when node is a root with default value
      # Case 1. this default value does not rely on any run-time value
      if (node.val$gen == "default.vals" || identical(node.val$gen, list('default.vals'))){
        node.val$gen <- list("default.vals")
        func <- class(node.val$f.gen) == "function"
        lfun <- class(node.val$f.gen) == "list" && node.val$f.gen[[1]] == "func"
        # Case 1a. this default value is calculated from other default values,
        # note that being calculated from a node X's default value is different from 
        # calculated from X's run-time value
        # this is unnecessary since a function of pre-defined constants is also a pre-defined constant
        # edmsyn allows it anyway, with a warning ofcourse.
        if (func || lfunc){
          warning("'",node.name,"' appears to have a default value that relies on other current default values")
          warning("default value of '",node.name,"' is calculated now and will not change in the future")
          if (lfunc && length(node.val$f.gen) > 1){
            warning("f.gen of '",node.name,"' has more than one component, only the first one is taken")
            node.val$f.gen <- node.val$f.gen[[1]]
          }
          if (length(formals(node.val$f.gen)) != 1)
            stop("f.gen of '",node.name,"' must have one argument being the value of default()")
          node.default <- node.val$f.gen(default())
        # Case 1b. this default value is a constant
        # which is the case for all base roots with default values.
        } else {
          message("'",node.name,"' appears to have a constant default value")
          node.default <- node.val$f.gen
        }
        asin(node.name, node.default)
        node.val$f.gen <- list(function(x){x[[1]][[node.name]]})
      # Case 2. This default value does rely on some run-time values
      # This case is NOT ALLOWED
      } else {
        stop("'",node.name,"' appears to have a default value that relies on one or more run-time values")
      }
    }
  }
  
  names.struct <- names(STRUCTURE)
  check.avail <- function(s){
    for (i in 1:length(s)) 
      if (!(s[i] %in% names.struct)) 
        stop(paste0("'",s[i],"' is not found in current tree"))
  }
  
  if (!root){
    if (class(node.val$tell) != 'character') stop('tell must be a set of node names')
    check.avail(node.val$tell)
    
    # down stream regulariser
    if (class(node.val$f.tell) != 'function') stop('f.tell must be a function')
    if (length(formals(node.val$f.tell)) != 1) stop('f.tell have one argument')
    f <- node.val$f.tell
    new.f.tell <- function(l){ 
      # A function wrapper to better debug the output size of f.tell at run-time,
      # Any error inside this scope is run-time error,
      # and thus, must announce the node.name to the user.
      f.tell.r <- f(l)
      if (class(f.tell.r) != 'list') 
        if (length(node.val$tell) == 1){
          warning(paste0("node '",node.name,"' : f.tell did not return a list, coerced to list of length 1"))
          f.tell.r <- list(f.tell.r)
        }
        else {
          stop(paste0("node '",node.name,"' : f.tell did not return a list as expected"))
        }
        
      if (length(f.tell.r) != length(node.val$tell))
        stop(paste0("node '",node.name,"' : f.tell did not return a list with length ",
                    length(node.val$tell)," (size of tell) as expected"))
      return(f.tell.r)
    }
    node.val$f.tell <- new.f.tell
  }
  
  if (class(node.val$gen) != 'list') stop('gen must be a list')
  for (i in 1:length(node.val$gen)){
    gen.i <- node.val$gen[[i]]
    if (class(gen.i) != 'character') stop('gen must be a list of character sets')
    check.avail(gen.i)
  }
  
  if (class(node.val$f.gen) != 'list') stop('f.gen must be a list')
  # up stream regulariser
  f.gen.copy <- node.val$f.gen # to avoid infinite recursion
  for (i in 1:length(node.val$f.gen)){
    f.gen.i <- node.val$f.gen[[i]]
    if (class(f.gen.i) != 'function') stop('f.gen must be a list of functions')
    if (length(formals(f.gen.i)) != length(node.val$gen[[i]])) 
      stop(paste0("number of arguments of f.gen[[",i,"]] must match the size of gen[[",i,"]]"))
  }
  gen.len <- length(f.gen.copy)
  fix.gen <- function(l){ 
    if (l > gen.len) return() # recursion base
    node.val$f.gen[[l]] <<- function(x){ do.call(f.gen.copy[[l]],x) }
    fix.gen(l+1)
    # recursion creates a sequence of different enviroments
    # to trap the values of l, 
    # because otherwise - when a loop is used with l being the iterator, 
    # then l will always == gen.len at runtime
  }
  fix.gen(1)
  
  return(node.val)
}

#' @export
edmtree.add <- function(node.name, tell = NULL, gen = list(NULL), 
                        f.tell = NULL, f.gen = list(NULL)){
  if (node.name %in% names(STRUCTURE)) {
    warning("'",node.name,"' is already in the tree, replacement is used instead of addition")
    edmtree.replace(node.name, tell, gen, f.tell, f.gen)
  }
  else {
    node.val <- list(tell, gen, f.tell, f.gen)
    names(node.val) <- c('tell', 'gen', 'f.tell', 'f.gen')
    assign(node.name, edmtree.check(node.name, node.val), envir=STRUCTURE)
    #STRUCTURE[[node.name]] <<- edmtree.check(node.name, node.val)
    #edmtree.fetch(node.name)
  }
}

#' @export
edmtree.replace <- function(node.name, tell = NULL, gen = NULL, 
                           f.tell = NULL, f.gen = NULL){
  node.val <- edmtree.fetch(node.name)
  if (!is.null(tell)) node.val$tell <- tell
  if (!is.null(gen)) node.val$gen <- gen
  if (!is.null(f.tell)) node.val$f.tell <- f.tell
  if (!is.null(f.gen)) node.val$f.gen <- f.gen
  assign(node.name, edmtree.check(node.name, node.val), envir=STRUCTURE)
  #STRUCTURE[[node.name]] <<- edmtree.check(node.name, node.val)
  #edmtree.fetch(node.name)
}

#' @export
edmtree.clear <- function(){
  rm(list=names(STRUCTURE), envir=STRUCTURE)
}

#' @export
edmtree.dump <- function(){
  return(STRUCTURE)
}

#' @export
edmtree.load <- function(tree = NULL){
  if (is.null(tree)) new.tree <- STRUCTURE.ORIGINAL
  edmtree.clear()
  for (i in names(new.tree))
    assign(i, get(i, envir = new.tree), envir = STRUCTURE)
}