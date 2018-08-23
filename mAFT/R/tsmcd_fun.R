# these two function is for internal use only, so no need to export it

lmres <- function(Y, X, delta) {

  o <- order(Y)
  Y1 <- Y[o]
  X1 <- X[o, ]
  delta1 <- delta[o]


  Wn1 <- delta1
  n1 <- length(Y)
  Wn1[1] <- delta1[1]/n1
  tt <- 1
  for (i in 2:n1) {

    j <- i - 1
    tt <- tt * ((n1 - j)/(n1 - j + 1))^delta1[j]


    Wn1[i] <- delta1[i]/(n1 - i + 1) * tt
  }

  W <- sqrt(Wn1)
  Y2 <- W * Y1
  X2 <- W * X1
  id <- which(Wn1 > 0)

  if (length(id) >= dim(X)[2]) {
    Y3 <- Y2[id]
    X3 <- X2[id, ]
    W3 <- W[id]
    X3 <- as.matrix(X3)
    lmr <- lm(Y3 ~ W3 + X3 - 1)
    return(list(length(Y) * sum((lmr$residuals)^2), lmr$coefficients,
                sqrt(length(Y)) * Y3, sqrt(length(Y)) * X3, sqrt(length(Y)) *
                  W3))
  }
  if (length(id) < dim(X)[2])
    return(NULL)
}

cumcp <- function(Y, X, delta) {
  p <- dim(X)[2]
  n <- dim(X)[1]
  cp <- rep(0, n)
  delta1 <- which(delta > 0)
  n1 <- length(which(delta > 0))
  if (n1 > 2 * p) {
    for (i in delta1[p + 1]:delta1[n1 - p]) cp[i] <- lmres(Y[1:i],
                                                           X[1:i, ], delta[1:i])[[1]] + lmres(Y[(i + 1):n], X[(i + 1):n,
                                                                                                              ], delta[(i + 1):n])[[1]]
    cpm <- min(cp[which(cp > 0)])
    return(which(cp == cpm))

  } else return(0)

}


#' Two stage multiple change points detection for AFT model.
#'
#' This function first formulate the threshold problem as a group model selection
#' problem so that a concave 2-norm group selection method can be applied
#' using the \code{\link[grpreg]{grpreg}} in R packages \pkg{grpreg}, and then finalized via a refining method.
#'
#' @param Y the censored logarithm of the failure time
#' @param X design matrix without intercept
#' @param delta the censoring indicator
#' @param c ceiling(c*sqrt(length(Y))) is the length of each segments in spliting stage.
#' @return Returns an object with
#' @return \item{cp}{the change points}
#' @return \item{coef}{the estimated coefficients}
#' @return \item{sigma}{the variance of error}
#' @return \item{residuals}{the residuals}
#' @return \item{Yn}{weighted Y by Kaplan-Meier weight}
#' @return \item{Xn}{weighted Xn by Kaplan-Meier weight}
#' @export TSMCP
#' @import grpreg lars plus
#' @seealso grpreg
#' @references Jialiang Li, Baisuo Jin (2018) Multi-threshold Accelerate Failure Time Model. \emph{The Annals of Statistics}, in press.
#' @note here Y, X and delta need be re-sorted firstly by the thresholding variable



TSMCP <- function(Y, X, delta, c) {
  n <- length(Y)
  p <- dim(X)[2]
  id1 <- which(delta == 1)
  n1 <- length(id1)
  m <- ceiling(c * sqrt(n1))
  q <- floor(n1/m)

  x <- NULL
  y <- NULL
  de <- NULL


  tt <- lmres(Y[1:id1[n1 - (q - 1) * m]], X[1:id1[n1 - (q - 1) * m],
                                            ], delta[1:id1[n1 - (q - 1) * m]])

  y[[1]] <- tt[[3]]
  x[[1]] <- cbind(tt[[5]], tt[[4]])


  for (i in 2:(q - 1)) {
    tt <- lmres(Y[id1[n1 - (q - i + 1) * m + 1]:id1[n1 - (q - i) *
                                                      m]], X[id1[n1 - (q - i + 1) * m + 1]:id1[n1 - (q - i) * m],
                                                             ], delta[id1[n1 - (q - i + 1) * m + 1]:id1[n1 - (q - i) * m]])

    y[[i]] <- tt[[3]]
    x[[i]] <- cbind(tt[[5]], tt[[4]])
  }

  i <- q
  tt <- lmres(Y[id1[n1 - (q - i + 1) * m + 1]:n], X[id1[n1 - (q - i +
                                                                1) * m + 1]:n, ], delta[id1[n1 - (q - i + 1) * m + 1]:n])

  y[[i]] <- tt[[3]]
  x[[i]] <- cbind(tt[[5]], tt[[4]])


  K_temp <- matrix(0, nrow = q, ncol = q, byrow = TRUE)
  for (i in 1:q) K_temp[i, 1:i] <- rep(1, i)

  X_temp1 <- lapply(1:length(x), function(j, mat, list) kronecker(K_temp[j,
                                                                         , drop = FALSE], x[[j]]), mat = K_temp, list = x)
  Xn <- do.call("rbind", X_temp1)


  Yn <- NULL
  for (i in 1:q) {
    Yn <- c(Yn, y[[i]])
  }




  group <- kronecker(c(1:q), rep(1, p + 1))
  fit <- grpreg(Xn, Yn, group, penalty = "grSCAD")
  mcp.coef <- grpreg::select(fit, "BIC")$beta[-1]

  mcp.coef.s <- sum(abs(mcp.coef))

  mcp.coef.v.m <- abs(matrix(c(mcp.coef), q, (p + 1), byrow = T))
  mcp.coef.m <- c(apply(mcp.coef.v.m, 1, max))

  mcp.cp <- which(mcp.coef.m != 0)

  if (q > 10) {
    if (length(mcp.cp) > 1) {
      for (i in 2:length(mcp.cp)) {
        if (mcp.cp[i] - mcp.cp[i - 1] == 1)
          mcp.cp[i] <- 0
      }
    }


    mcp.cp1 <- mcp.cp[mcp.cp > 1 & mcp.cp < q]

    d1 <- length(mcp.cp1)

    if (d1 == 0) {
      mcpcss.cp <- NULL
      adcpcss.cp <- mcpcss.cp
    }

    if (d1 >= 1) {

      mcpcss.cp <- NULL


      for (i in 1:d1) {
        t <- mcp.cp1[i]
        id <- c(id1[n1 - (q - t + 2) * m + 1]:id1[n1 - (q - t -
                                                          1) * m])
        cp.t <- cumcp(Y[id], X[id, ], delta[id])[[1]]
        if (cp.t > 0)
          mcpcss.cp <- c(mcpcss.cp, cp.t + id1[n1 - (q - t + 2) *
                                                 m + 1] - 1)
      }

      id2 <- c(mcpcss.cp, n)
      tt1 <- NULL
      tt1 <- c(tt1, table(delta[1:mcpcss.cp[1]])[2])
      for (i in 2:length(id2)) {
        tt1 <- c(tt1, table(delta[(id2[i - 1] + 1):id2[i]])[2])
      }
      tt2 <- which(tt1 < p + 2)
      tt2[which(tt2 == length(id2))] <- length(id2) - 1
      if (length(tt2) > 0) {
        mcpcss.cp <- mcpcss.cp[-tt2]
      }

      tt <- which(abs(diff(mcpcss.cp)) < 2 * m)
      if (length(tt) > 0)
        mcpcss.cp <- mcpcss.cp[-tt]
    }

  }


  if (q <= 10) {



    mcp.cp1 <- mcp.cp[mcp.cp > 1 & mcp.cp < q]

    d1 <- length(mcp.cp1)

    if (d1 == 0) {
      mcpcss.cp <- NULL
      adcpcss.cp <- mcpcss.cp
    }

    if (d1 >= 1) {

      mcpcss.cp <- NULL


      for (i in 1:d1) {
        t <- mcp.cp1[i]
        if (t == 2) {
          id <- c(1:id1[n1 - (q - t - 1) * m])
          cp.t <- cumcp(Y[id], X[id, ], delta[id])[[1]]
          if (cp.t > 0)
            mcpcss.cp <- c(mcpcss.cp, cp.t)
        }
        if (t == q) {
          id <- c(id1[n1 - (q - t + 2) * m + 1]:n)
          cp.t <- cumcp(Y[id], X[id, ], delta[id])[[1]]
          if (cp.t > 0)
            mcpcss.cp <- c(mcpcss.cp, cp.t + id1[n1 - (q - t +
                                                         2) * m + 1] - 1)
        }

        if (t < q & t > 2) {
          id <- c(id1[n1 - (q - t + 2) * m + 1]:id1[n1 - (q - t -
                                                            1) * m])
          cp.t <- cumcp(Y[id], X[id, ], delta[id])[[1]]
          if (cp.t > 0)
            mcpcss.cp <- c(mcpcss.cp, cp.t + id1[n1 - (q - t +
                                                         2) * m + 1] - 1)
        }


      }

      id2 <- c(mcpcss.cp, n)
      tt1 <- NULL
      tt1 <- c(tt1, table(delta[1:mcpcss.cp[1]])[2])
      for (i in 2:length(id2)) {
        tt1 <- c(tt1, table(delta[(id2[i - 1] + 1):id2[i]])[2])
      }
      tt2 <- which(tt1 < p + 2)
      tt2[which(tt2 == length(id2))] <- length(id2) - 1
      if (length(tt2) > 0) {
        mcpcss.cp <- mcpcss.cp[-tt2]
      }


      tt <- which(abs(diff(mcpcss.cp)) < 2 * m)
      if (length(tt) > 0)
        mcpcss.cp <- mcpcss.cp[-tt]

    }

  }




  if (length(mcpcss.cp) >= 1 && mcpcss.cp[1] != 0) {
    id2 <- c(mcpcss.cp, n)
    x <- NULL
    y <- NULL
    de <- NULL

    tt <- lmres(Y[1:mcpcss.cp[1]], X[1:mcpcss.cp[1], ], delta[1:mcpcss.cp[1]])
    y[[1]] <- tt[[3]]
    x[[1]] <- cbind(tt[[5]], tt[[4]])


    for (i in 2:length(id2)) {
      tt <- lmres(Y[(id2[i - 1] + 1):id2[i]], X[(id2[i - 1] + 1):id2[i],
                                                ], delta[(id2[i - 1] + 1):id2[i]])

      y[[i]] <- tt[[3]]
      x[[i]] <- cbind(tt[[5]], tt[[4]])
    }



    K_temp <- matrix(0, nrow = length(id2), ncol = length(id2), byrow = TRUE)
    for (i in 1:length(id2)) K_temp[i, 1:i] <- rep(1, i)

    X_temp1 <- lapply(1:length(x), function(j, mat, list) kronecker(K_temp[j,
                                                                           , drop = FALSE], x[[j]]), mat = K_temp, list = x)
    Xn <- do.call("rbind", X_temp1)


    Yn <- NULL
    for (i in 1:length(id2)) {
      Yn <- c(Yn, y[[i]])
    }

    object <- plus(Xn, Yn, method = "scad", gamma = 2.4, intercept = F,
                   normalize = F, eps = 1e-30)
    # step 1 estimate coef using BIC.
    bic <- log(dim(Xn)[1]) * object$dim + dim(Xn)[1] * log(as.vector((1 -
                                                                        object$r.square) * sum(Yn^2))/length(Yn))
    step.bic <- which.min(bic)

    mcp.coef <- coef(object, lam = object$lam[step.bic])

    ep <- (Yn - Xn %*% mcp.coef)
    sigmaep <- sum(ep^2)/length(Y)

    mcp.coef.v.m <- matrix(c(mcp.coef), length(id2), p + 1, byrow = T)
    mcp.coef.m <- c(apply(abs(mcp.coef.v.m), 1, max))
    mcp.m.id <- which(mcp.coef.m == 0)
    if (length(mcp.m.id) > 0) {
      mcp.coef <- c(t(mcp.coef.v.m[-mcp.m.id, ]))
      mcpcss.cp <- mcpcss.cp[-c(mcp.m.id - 1)]
    }
  }


  if (mcpcss.cp == 0 || length(mcpcss.cp) == 0) {
    id2 <- c(mcpcss.cp, n)
    x <- NULL
    y <- NULL
    de <- NULL


    tt <- lmres(Y, X, delta)

    Yn <- tt[[3]]
    Xn <- cbind(tt[[5]], tt[[4]])


    object <- plus(Xn, Yn, method = "scad", gamma = 2.4, intercept = F,
                   normalize = F, eps = 1e-30)
    # step 1 estimate coef using BIC.
    bic <- log(dim(Xn)[1]) * object$dim + dim(Xn)[1] * log(as.vector((1 -
                                                                        object$r.square) * sum(Yn^2))/length(Yn))
    step.bic <- which.min(bic)

    mcp.coef <- coef(object, lam = object$lam[step.bic])

    ep <- (Yn - Xn %*% mcp.coef)
    sigmaep <- sum(ep^2)/length(Y)

    mcp.coef.v.m <- matrix(c(mcp.coef), length(id2), p + 1, byrow = T)
    mcp.coef.m <- c(apply(abs(mcp.coef.v.m), 1, max))
    mcp.m.id <- which(mcp.coef.m == 0)
    if (length(mcp.m.id) > 0) {
      mcp.coef <- c(t(mcp.coef.v.m[-mcp.m.id, ]))
      mcpcss.cp <- mcpcss.cp[-c(mcp.m.id - 1)]
    }

  }

  return(list(cp = mcpcss.cp, coef = mcp.coef, sigma = sigmaep, residuals = ep,
              Yn = Yn, Xn = Xn))
}




