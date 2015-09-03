#=======================+
# Sub-Routine functions |
#=======================+


#' @export
print.context <- function(x){
  cat("Activated units in the context:\n")
  print(names(x)[which(sapply(x,is.null)==0)])
}

#' @export
toStr <- function(x, max){
  if (max<10) r <- toString(x)
  else
    r <- (paste0(paste(sapply(1:log(max,10),function(x)"0"),collapse=""),x))
  return(paste0("0",r))
}

#' @export
which.closest <- function(target, candidates){
  ref <- STRUCTURE[[target]][[1]]
  which.max(
    sapply(candidates, function(c){
      sum(sapply(c,function(x){x %in% ref}))
    }))
}

#' @export
compat <- function(val,tel){
  if (class(tel) == "min") return(all(tel <= val))
  if (class(tel) == "max") return(all(tel >= val))
  if (class(tel) == "numeric") return(max(abs(val-tel)) < 1e-10)
  else return(identical(val,tel))
}

#===========+
# STRUCTURE |
#===========+

#' This function is the shit.
#'
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
    matrix(sapply(P,
                  function(i) {
                    sample(0:1, 1, prob = c(1 - i,i))
                  }),
           nrow(P),
           ncol(P))
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
  OddsToP <- function(o) o/(1+o)
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
  #QSLinPesGen <- function(Q,S){P<-sapply(1:ncol(S),function(s){sapply(1:nrow(Q),function(i){min((Q[i,]*S[,s])[(Q[i,])>0])})});list(R=randGen(P=P),concepts=nrow(S))}
  QSLinAvgGen<- function(Q,S){
    list(R=randGen(sqrt(QSAvgGenR2(Q = Q,S = S))), concepts = nrow(S))
  }
  Gen.Synthetic.POKS <- function(St.Var, Students, State, OR.t, OR.f, PO, alpha.c, alpha.p, p.min){
    PO <- PO$ks
    Items <- length(State)
    if(St.Var>0.3) stVar <- 0.3
    if(St.Var<0) stVar <- 0
    R = matrix(-1,Students,Items)
    for(i in 1:Students)
    {
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

    list(R=t(R), alpha.c = alpha.c, alpha.p = alpha.p, p.min = p.min)
  }
  poksGen <- function(students, poks, successRate, alpha.c, alpha.p, p.min){
    poks <- poks$ks
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
    PO <- PO$ks
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
    PO <- PO$ks
    Items <- nrow(PO)
    OR.t = matrix(0.5,Items,Items)
    OR.t[which(t(PO)==1)] <- runif(sum(PO),0.8-stVar,1)
    OR.t <- PToOdds(OR.t)
  }
  stVarPo2Orf <- function(stVar, PO){
    PO <- PO$ks
    Items <- nrow(PO)
    OR.f = matrix(0.5,Items,Items)
    OR.f[which(t(PO)==1)] <- runif(sum(PO),0,0.2+stVar)
    OR.f <- PToOdds(OR.f)
  }
  genPoks <- function(items, minTrees, maxTrees, minDepth, maxDepth,
                      density, minItemPerTree, maxItemPerTree) {
    treeSizes <- NULL
    treeDepths <- NULL
    #-------------CISAC------------------------------------------------------
    if (!is.null(treeSizes) &
        !is.null(treeDepths) &
        length(treeSizes) != length(treeDepths))
      stop("Input Conflict")
    if (minDepth + 1 > maxItemPerTree)
      stop("Requirements cannot be satisfied")
    if (items < minTrees * minItemPerTree |
        items > maxTrees * maxItemPerTree)
      stop("Requirements cannot be satisfied")

    #-------------GENERATING-------------------------------------------------

    trees <- length(treeSizes)
    if (is.null(treeSizes)) {
      # pick a number of trees
      lowerTrees <- max(minTrees,ceiling(items / maxItemPerTree))
      upperTrees <-
        min(maxTrees,floor(items / max(minDepth + 1,minItemPerTree)))
      if (lowerTrees > upperTrees)
        stop("Requirements cannot be satisfied")
      if (!is.null(treeDepths)) {
        if (length(treeDepths) < lowerTrees |
            length(treeDepths) > upperTrees)
          stop("Requirements cannot be satisfied")
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
          stop("Requirements cannot be satisfied")
        if (upper < minItemPerTree)
          stop("Requirements cannot be satisfied")

        upper <- min(upper,maxItemPerTree)
        if (upper < minDepth)
          stop("Requirements cannot be satisfied")
        lower <- max(lower,minItemPerTree,minDepth + 1)
        if (!is.null(treeDepths))
          lower <- max(lower, treeDepths[trees - x + 1] + 1)


        if (lower > upper)
          stop("Requirements cannot be satisfied")
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
        stop("Requirements cannot be satisfied")
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
        pNow <- (size.i-1)/sum((c(1,levelSizes)*c(levelSizes,1))[2:levels])
        if (pNow < 1){
          p <- (density - pNow)/(1-pNow)
          if (p < 0) densFail <- TRUE
          else{
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
      # ###############
      list.i <- perm[1:size.i]
      tree.i <- as.matrix(poks[list.i,list.i])
      colnames(tree.i) <- as.character(list.i)
      rownames(tree.i) <- as.character(list.i)
      tree.i <- list(tree.i, levelSizes)
      names(tree.i) <- c("matrix","level.sizes")
      subtrees <- append(subtrees,list(tree.i))

      perm <- perm[(size.i + 1):length(perm)]
    }

    colnames(poks) <- as.character(1:items)
    rownames(poks) <- colnames(poks)

    list(ks = poks, comp = subtrees)
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
    #  or <- list(t=odds.t/odds, f=odds.f/odds) # something to try (doesn't get exactly same result)
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
    list(student.var = student.var, avg.success = mean(raw), state = state, or.t = odds.t, or.f = odds.f, po = list(ks = m.rel, comp = NULL),
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
        cat(paste0("\tItem ",toStr(i,items)," Student ", toStr(j,students),"\n"))
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
  #Q.S.2.lin.pes <- function(x){QSLinPesGen(x[[1]],x[[2]])}
  Q.S.2.lin.avg <- function(x){QSLinAvgGen(x[[1]],x[[2]])}
  stvar.stu.state.or.po.2.poks <- function(x){
    Gen.Synthetic.POKS(x[[1]],x[[2]],x[[3]],x[[4]],x[[5]],x[[6]],x[[7]],x[[8]],x[[9]])}
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
    genPoks(x[[1]],x[[2]],x[[3]],x[[4]],x[[5]],x[[6]],x[[7]],x[[8]])}
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
    if (v == 0) v <- 1e-10
    s <- m*(1-m)/v - 1
    if (s < 0) s <- 0
    rbeta(n, s*m, s - s*m)
  }
  rmean.n.cvar.2.mat <- function(x){
    n <- x[[2]]
    v <- x[[3]]
    if (v == 0) v <- 1e-10
    t(sapply(x[[1]], function(m){
      s <- m*(1-m)/v - 1
      if (s < 0) s <- 0
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
  # node.i <- list(S, L, fs, fl)
  # Where S is a set of nodes that can be infered from node.i
  # and L = list(set.of.nodes.1, set.of.nodes.2, ...)
  # set.of.nodes.k is a minimal set of nodes that can sufficiently generate node.i
  # and fs is a function that maps from node.i to S
  # and fl is a list of functions that map respective sets in L to node.i
  #
  # e.g.
  # state. <- list(c("items"), list(c("po","items")), fs, fl)
  # then node state can be generated from po and items by fs
  # and items can be infered from state by fl
  #===================================================================================

  #------------+
  # root nodes |
  #------------+

  # root nodes to prevent conflicts and detect insufficiency
  root. <- list(NULL, list(NULL), NULL, list(NULL))
  items. <- root.
  students. <- root.
  concepts. <- root.
  init.vals. <- root.

  # root nodes with predefined default values initialized only when needed
  bkt.guess.st.var. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["bkt.guess.st.var"]]}))
  bkt.slip.st.var. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["bkt.slip.st.var"]]}))
  S.st.var. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["S.st.var"]]}))
  L.st.var. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["L.st.var"]]}))
  abi.mean. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["abi.mean"]]}))
  abi.sd. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["abi.sd"]]}))
  alpha.c. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["alpha.c"]]}))
  alpha.p. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["alpha.p"]]}))
  p.min. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["p.min"]]}))
  bkt.mod. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["bkt.mod"]]}))
  min.ntree. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["min.ntree"]]}))
  min.depth. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["min.depth"]]}))
  min.it.per.tree. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["min.it.per.tree"]]}))
  density. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["density"]]}))
  per.item. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["per.item"]]}))
  avg.success. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["avg.success"]]}))
  student.var. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["student.var"]]}))
  time. <- list(NULL, list(c("init.vals")), NULL, list(function(x){x[[1]][["time"]]}))

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
  #lin.pes. <- list(NULL, list(c("Q","S")), NULL, list(Q.S.2.lin.pes))
  lin.avg. <- list(c("Q","S"), list(c("Q","S")),
                   lin.avg.2.Q.S, list(Q.S.2.lin.avg))
  poks.<- list(c("student.var","avg.success","state","or.t","or.f","po","alpha.c","alpha.p","p.min"),
               list(c("student.var", "students", "state", "or.t","or.f","po","alpha.c","alpha.p","p.min"),
                    c("students","po","avg.success","alpha.c","alpha.p","p.min")),
               poks.learn, list(stvar.stu.state.or.po.2.poks,
                                st.po.avg.2.poks))
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
                                         "min.it.per.tree","max.it.per.tree")),
              function(x){list(nrow(x$ks),ncol(x$ks))},
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
                     list(c("items","students"),c("blt.guess.it.exp","students","bkt.guess.st.var")),
                     n.row.col.cvar.rmean, list(rmn, rmean.n.cvar.2.mat))
  order. <- list(c("time","items"), list(c("time","items")),
                 order.2.time.items, list(time.items.2.order))
  r <-
    list(exp = exp., irt = irt., poks = poks., dina = dina.,
         dino = dino., nmf.con = nmf.con.,
         nmf.com = nmf.com., nmf.dis = nmf.dis.,
         #lin.pes
         lin.avg = lin.avg., bkt = bkt., abi.mean = abi.mean., abi.sd = abi.sd.,
         dis = dis., dif = dif., abi = abi., st.exp = st.exp., it.exp = it.exp.,
         state = state., avg.success = avg.success.,
         student.var = student.var., po = po., or.t = or.t., or.f = or.f.,
         alpha.p = alpha.p., alpha.c = alpha.c., p.min = p.min.,
         items = items., students = students., concepts = concepts.,
         slip = slip., guess = guess.,
         Q = Q., S = S., M = M., L = L.,
         S.st.var = S.st.var., S.con.exp = S.con.exp.,
         L.st.var = L.st.var., L.con.exp = L.con.exp.,
         skill.space.size = skill.space.size., skill.space = skill.space.,
         skill.dist = skill.dist., concept.exp = concept.exp.,
         bkt.slip = bkt.slip., bkt.guess = bkt.guess.,
         bkt.slip.it.exp = bkt.slip.it.exp., bkt.slip.st.var = bkt.slip.st.var.,
         bkt.guess.it.exp = bkt.guess.it.exp., bkt.guess.st.var = bkt.guess.st.var.,
         time = time., bkt.mod = bkt.mod.,
         per.item = per.item., order = order.,
         min.ntree = min.ntree., max.ntree = max.ntree., min.depth = min.depth.,
         max.depth = max.depth., min.it.per.tree = min.it.per.tree.,
         max.it.per.tree = max.it.per.tree., density = density.,
         init.vals = init.vals.)
  sapply(1:length(r), function(x){names(r[[x]]) <<- c("tell","gen","f.tell","f.gen")})
  return(r)
}

#' @export
STRUCTURE <- assemble.structure()

#===========+
# CONSTANTS |
#===========+

#' @export
ALL.MODELS <- c("exp", "irt", "poks", "dina", "dino",
                #"lin.pes",
                "lin.avg","nmf.con", "nmf.dis", "nmf.com", "bkt")

#' @export
KEEP <- list(exp = c("avg.success","it.exp","student.var"),
             irt = c("dis","dif","abi.mean","abi.sd"),
             poks = c("po","avg.success","alpha.c","alpha.p","p.min"),
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

#' @export
INTEGER <- c("items","students","concepts","time","skill.space.size",
             "min.ntree","max.ntree","min.depth","max.depth",
             "min.it.per.tree","max.it.per.tree")

#' @export
DEFINITE <- c("items","students","concepts","time",
              "skill.space.size", "avg.success")

#' @export
BOUND.CLASSES <- c("min", "max")

#=====================+
# OPERATING FUNCTIONS |
#=====================+

#-----------------------------------------------------------------------------+
# argument pars stands for a list of all parameters across all models         |
# It is meant to be produced and updated by the function pars()               |
# down.stream(), and upstream() are general purpose functions                 |
# that will be used as building blocks for functions at user-interface level  |
#-----------------------------------------------------------------------------+

#-----------------------------------------------------------------------------+
# down.stream() propagates all obtainable info through type-1 connection      |
# in the STRUCTURE, also checks for conflicts.                                |
# up.stream() propagates info through type-2 connection in the STRUCTURE,     |
# the propagation is tailored so that a specified target can be calculated    |
#-----------------------------------------------------------------------------+

#' Propagate information downwards
#'
#' This function takes the available parameters and try to learn all
#' possible parameters at lower level, simultaneously check for conflicts
#'
#' @param pars an object of \code{context} class describes all available information in current context
#' @return a new \code{context} object obtained from the input
#' @author Hoang-Trieu Trinh
#' @details
#' This function use breadth-first scheme to propagate information in
#' the STRUCTURE, using the learning functions indicated in 3rd element
#' of each node inside STRUCTURE to learn the corresponding values of
#' nodes indicated in the 1st element
#' @export
down.stream <- function(pars){
  curr <- names(pars)[which(sapply(pars,is.null) == 0)]

  # breadth-first propagating
  while(length(curr) > 0){
    new <- NULL
    for (i in 1:length(curr)){
      var.name <- curr[i]
      var.val <- pars[[var.name]]
      child.names <- STRUCTURE[[var.name]][[1]]
      if (is.null(child.names)) next
      child.val <- STRUCTURE[[var.name]][[3]](var.val)

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

#' Propagate information upwards
#'
#' This function takes the available parameters and generate higher
#' level parameters in a tailored direction so that a specified
#' target can be reach
#'
#' @param target a character string indicates the target's name
#' @param pars an object of \code{context} class describes all available information in current context
#' @param progress a boolean value indicates if the generating process should be printed
#' @return a new \code{context} object obtained from the input, if the target cannot be reach,
#' the old \code{context} object is returned
#' @author Hoang-Trieu Trinh
#' @details
#' This function runs a recursive search for available information at lower level
#' nodes in the STRUCTURE that has been provided by the input. Whenever there is
#' more than two ways to generate a parameter, the function chooses the one that
#' requires inputs that is more likely to be learned directly from the target.
#' @seealso \code{which.closest}
#' @export
up.stream <- function(target, pars, progress = FALSE){

  miss <- NULL
  new.pars <- pars
  trace <- list(NULL)
  track <- list(NULL)
  fill <- FALSE

  check.track <- function(node.name){

    if (!is.null(new.pars[[node.name]])) return(TRUE)
    gen.methods <- STRUCTURE[[node.name]]$gen
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
    else pick <- avail[which.closest(target, gen.methods[avail])]

    track[[node.name]] <<- pick
    trace[[node.name]] <<- gen.methods[[pick]]
    return(TRUE)
  }
  follow <- function(node.name){
    node <- STRUCTURE[[node.name]]
    pick <- track[[node.name]]
    if (!is.null(pick)){ #which means, node already has a value
      gen.method <- node$gen[[pick]]
      if (identical(gen.method,"init.vals"))
        new.pars[[node.name]] <<- node$f.gen[[1]](list(new.pars$init.vals))
      else {
        dummy <- sapply(gen.method, follow)
        if (fill == TRUE)
          new.pars[[node.name]] <<- node$f.gen[[pick]](new.pars[gen.method])
      }
    }
    return(NULL)
  }

  success <- check.track(target)
  if (success == FALSE){
    message(paste0("Cannot reach '", target,"' since '", miss, "' is missing"))
    return(pars)
  }
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

#' @export
keep <- function(model){
  KEEP[[model]]
}

#' This function is so lame I cant take it
#'
#' @importFrom diagram plotmat
#' @export
viz <- function(po){
  n <- length(po$comp)
  n.row <- floor(sqrt(n))
  n.col <- ceiling(n/n.row)
  par(mfrow = c(n.row, n.col))
  for (i in 1:n){
    comp.i <- po$comp[[i]]
    plotmat(comp.i$matrix,
            pos = comp.i$level.sizes,
            lwd = 0.1,
            arr.type = "triangle",
            curve = 0,
            box.size = 0.04,
            box.type = "round",
            endhead = TRUE,
            arr.pos = 0.85,
            shadow.size = 0,
            cex.txt = 0)
  }
}

#' @export
init <- function(student.var = 1/12, avg.success = 0.5, time = 50,
                 S.st.var = 1/12, L.st.var = 1/12,
                 bkt.slip.st.var = 1/12, bkt.guess.st.var = 1/12,
                 min.ntree = 1, min.depth = 0, min.it.per.tree = 1,
                 per.item = FALSE, bkt.mod = "dina", density = 0.5,
                 alpha.c = 0.25, alpha.p = 0.25, p.min = 0.5,
                 abi.mean = 0, abi.sd = 1){
  as.list(environment())
}

#==========================+
# USER INTERFACE FUNCTIONS |
#==========================+

#' Create or update a context
#'
#' This function allows user input a set of parameters to a new or available context
#'
#' @param old.pars an object of \code{context} class describe the context that needed to be updated,
#' leave this parameter if the user need a new context.
#' @return an object of \code{context} class describe the updated or new context
#' @author Hoang-Trieu Trinh
#' @details
#' This function takes in a set of parameters that the user input and assemble them
#' into a \code{context} object, it uses the \code{down.stream} function to check for conflicts
#' @seealso \code{down.stream}
#' @export

pars <- function(old.pars = NULL,
                 init.vals = init(),
                 dis = NULL, dif = NULL, abi = NULL,
                 abi.mean = NULL, abi.sd = NULL,
                 st.exp = NULL, it.exp = NULL,
                 items = NULL, concepts = NULL, students = NULL,
                 state = NULL, po = NULL, or.t = NULL, or.f = NULL,
                 student.var = NULL, avg.success = NULL,
                 min.ntree = NULL, max.ntree = NULL,
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
                 lin.pes = NULL, lin.avg = NULL, poks = NULL, bkt = NULL){
  new.pars <- NULL #return this.
  if (!is.null(old.pars)) {
    if (!identical(class(old.pars),c("context","list")))
      stop("'old.pars' is not an object of the 'context' class")
    new.pars <- old.pars
    update <- as.list(environment())
    update <- update[3:length(update)]
    update <- update[which(sapply(update,is.null) == 0)]
    new.pars[names(update)] <- update
  }
  else {
    new.pars <- as.list(environment())
    sapply(INTEGER, function(x){
      if (!is.null(new.pars[[x]]))
        new.pars[[x]] <<- as.integer(new.pars[[x]])
    })
    new.pars <- new.pars[3:length(new.pars)]
    class(new.pars) <- c("context",class(new.pars))
  }
  if (class(new.pars$po) == "matrix")
    new.pars$po <- list(ks = new.pars$po, comp = NULL)
  down.stream(new.pars)
}

#' Get a parameter from the current context
#'
#' This function generate (if needed) the required target from a context
#'
#' @param target a character string indicates the target's name
#' @param pars an object of \code{context} class describes the given context
#' @param progress a boolean value indicates if the generating process should be printed or not
#' @return if success, a list with two components
#' \item{value}{value of the target}
#' \item{context}{the corresponding context}
#' if not success, NULL
#' @author Hoang-Trieu Trinh
#' @details
#' This function uses \code{up.stream} function to obtain target's value and context
#' @seealso \code{up.stream}
#' @export
get.par <- function(target, pars, progress = FALSE){
  g <- up.stream(target, pars, progress)
  if (!is.null(g)) {
    ret <- list(g[[target]], g)
    names(ret) <- c("value", "context")
    return(ret)
  }
  else return(NULL)
}

#' Generate data for a model
#'
#' This function does something
#'
#' @param model a param
#' @param pars another param
#' @param n another param
#' @param progress another one
#' @return whatever it is
#' @author Hoang-Trieu Trinh
#' @details more detail huh?
#' @seealso what?
#' @export
gen <- function(model, pars, n = 1, progress = FALSE){

  if (!(model %in% ALL.MODELS))
    stop(paste0("Model '",model,"' is not available"))
  if (!identical(class(pars),c("context","list")))
    stop(paste0("'pars' is of an invalid class"))

  r <-
    sapply(1:n,function(x){
      if (x > 1) progress <- FALSE
      trial <- up.stream(model, pars, progress)
      if (is.null(trial))
        stop(paste0("Insufficient information to generate '",model,"'"))
      list(trial)
    })

  if (n > 1) return(r) else return(r[[1]])
}

#' Generate data for a set of models
#'
#' This function does something
#'
#' @param model a param
#' @param pars another param
#' @param n another param
#' @param progress another one
#' @return whatever it is
#' @author Hoang-Trieu Trinh
#' @details more detail huh?
#' @seealso what?
#' @export
gen.apply <- function(models, pars, multiply = TRUE, n = 1, progress = FALSE){

  result <- NULL #return this
  if (identical(class(pars),c("context","list"))) pars <- list(pars)
  else if (class(pars) != "list") stop(paste0("'pars' is of an invalid class"))

  # name all the contexts
  if (is.null(names(pars)))
    names(pars) <- sapply(1:length(pars), function(x){
      paste0("p",toStr(x,length(pars)))
    })
  else{
    anony.context <- which(names(pars) == "")
    num.ac <- length(anony.context)
    names(pars)[anony.context] <- sapply(1:num.ac, function(x){
      paste0("p",toStr(x,num.ac))
    })
  }

  if (multiply == FALSE){
    suppressWarnings(
      result <- as.matrix(mapply(function(x,y){
        gen(x, y, n = n, progress)
      },models, pars))
    )
    if (length(pars) == 1) result <- t(result)
    rownames(result) <- sapply(1:n, function(x){toStr(x,n)})
    suppressWarnings(
      colnames(result) <- mapply(function(x,y){
        paste(x,y,sep=".")
      }, models, names(pars))
    )
  } else {
    result <- as.matrix(sapply(models,function(x){
      sapply(pars, function(y){
        list(gen(x, y, n = n, progress))
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
#' This function does something
#'
#' @param model a param
#' @param pars another param
#' @param n another param
#' @param progress another one
#' @return whatever it is
#' @author Hoang-Trieu Trinh
#' @details more detail huh?
#' @seealso what?
#' @export
learn <- function(model, data){

  if (!(model %in% ALL.MODELS))
    stop(paste0("Model '",model,"' is not available"))

  cat(paste0("Learning by '",model,"' ...\n"))

  learned.p <- pars()
  learned.p[[model]] <- data
  down.stream(learned.p)
}

#' Generate synthetic data from a given data
#' This function does something
#'
#' @param model a param
#' @param pars another param
#' @param n another param
#' @param progress another one
#' @return whatever it is
#' @author Hoang-Trieu Trinh
#' @details more detail huh?
#' @seealso what?
#' @export
syn <- function(model, data, keep.pars = keep(model),
                students = ncol(data$R), n = 1, progress = FALSE){
  learned.pars <- learn(model,data)
  filtered.pars <- pars(students = students)
  filtered.pars[keep.pars] <- learned.pars[keep.pars]
  filtered.pars <- down.stream(filtered.pars)
  list(data = data, synthetic = gen(model, filtered.pars, n = n, progress))
}
