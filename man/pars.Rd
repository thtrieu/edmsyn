% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/structure.R
\name{pars}
\alias{pars}
\title{Create or update a context}
\usage{
pars(old.pars = NULL, default.vals = default(), dis = NULL, dif = NULL,
  abi = NULL, abi.mean = NULL, abi.sd = NULL, st.exp = NULL,
  it.exp = NULL, items = NULL, concepts = NULL, students = NULL,
  state = NULL, po = NULL, or.t = NULL, or.f = NULL,
  student.var = NULL, avg.success = NULL, min.ntree = NULL,
  max.ntree = NULL, trans = NULL, min.depth = NULL, max.depth = NULL,
  density = NULL, min.it.per.tree = NULL, max.it.per.tree = NULL,
  alpha.c = NULL, alpha.p = NULL, p.min = NULL, slip = NULL,
  guess = NULL, per.item = NULL, order = NULL, Q = NULL, S = NULL,
  M = NULL, L = NULL, bkt.mod = NULL, S.st.var = NULL,
  S.con.exp = NULL, L.st.var = NULL, L.con.exp = NULL,
  skill.space.size = NULL, skill.space = NULL, skill.dist = NULL,
  concept.exp = NULL, bkt.slip = NULL, bkt.guess = NULL, time = NULL,
  bkt.slip.it.exp = NULL, bkt.slip.st.var = NULL, bkt.guess.it.exp = NULL,
  bkt.guess.st.var = NULL, irt = NULL, exp = NULL, dina = NULL,
  dino = NULL, nmf.con = NULL, nmf.dis = NULL, nmf.com = NULL,
  lin.avg = NULL, poks = NULL, bkt = NULL, ...)
}
\arguments{
\item{old.pars}{an object of \code{context} class describe the context that needed to be updated,
leave this parameter \code{NULL} if a new context is needed.}

\item{default.vals}{an environment contains default values for some parameters in the context, by default it is initialized by function \code{default}}

\item{dis}{a vector of discrimination values for each item}

\item{dif}{a vector of difficulty values for each item}

\item{abi}{a vector of ability values for each student}

\item{abi.mean}{mean value of parameter \code{abi}}

\item{abi.sd}{standard deviation of parameter \code{abi}}

\item{st.exp}{a vector of expected success rates for each student}

\item{it.exp}{a vector of expected success rates for each item}

\item{items}{number of items}

\item{concepts}{number of concepts}

\item{students}{number of students}

\item{state}{parameter for generating data from POKS model}

\item{po}{dependency matrix of a partial order knowledge structure among items}

\item{or.t}{parameter for generating data from POKS model}

\item{or.f}{parameter for generating data from POKS model}

\item{student.var}{variance of student expected success rate}

\item{avg.success}{mean value of the response matrix}

\item{min.ntree}{minimum number of connected components of \code{po}}

\item{max.ntree}{maximum number of connected components of \code{po}}

\item{trans}{a boolean value indicates if transitive links are allowed in \code{po}}

\item{min.depth}{minimum depth of the connected components of \code{po}}

\item{max.depth}{maximum depth of the connected components of \code{po}}

\item{density}{a real value between 0 and 1, indicates the connection density of \code{po}}

\item{min.it.per.tree}{minimum number of items per each connected component of \code{po}}

\item{max.it.per.tree}{maxinum number of items per each connected component of \code{po}}

\item{alpha.c}{parameter for learning by POKS model, see reference}

\item{alpha.p}{parameter for learning by POKS model, see reference}

\item{p.min}{p-value for interaction test while constructing POK structure}

\item{slip}{a vector of slip factor for each item}

\item{guess}{a vector of guess factor for each item}

\item{per.item}{a boolean value indicates if the students can improve after taking each item}

\item{order}{a vector indicates in which order did the students take the test in case \code{per.item} is set to be \code{TRUE}}

\item{Q}{Q-matrix with size \code{items} times \code{concepts}}

\item{S}{Skill matrix with size \code{concepts} times \code{students}}

\item{M}{Skill mastery matrix with size\code{concepts} times \code{students}}

\item{L}{Learn matrix indicates the transition probabilities for \code{M} matrix}

\item{bkt.mod}{a character string indicates which model governs the generating process for sequential data}

\item{S.st.var}{variance of student expected success rates of matrix \code{S}}

\item{S.con.exp}{a vector of expected success rate for each concept in matrix \code{S}}

\item{L.st.var}{variance of student expected success rates of matrix \code{L}}

\item{L.con.exp}{a vector of expected success rate for each concept in matrix \code{L}}

\item{skill.space.size}{size of the skill space}

\item{skill.space}{a matrix with size \code{concepts} times \code{skill.space.size}}

\item{skill.dist}{a vector of length \code{skill.space.size} that sums to one, indicates the probability of each skill pattern in \code{skill.space.size}}

\item{concept.exp}{a vector of expected mastery rate for each concept}

\item{bkt.slip}{a matrix of size \code{items} times \code{students} indicates slip factor for each combination of one item and one student}

\item{bkt.guess}{a matrix of size \code{items} times \code{students} indicates slip factor for each combination of one item and one student}

\item{time}{the number of time steps for sequential data}

\item{bkt.slip.it.exp}{a vector of expected value for each item in \code{bkt.slip}}

\item{bkt.slip.st.var}{variance of expected values of students in \code{bkt.slip}}

\item{bkt.guess.it.exp}{a vector of expected value for each item in \code{bkt.guess}}

\item{bkt.guess.st.var}{variance of expected values of students in \code{bkt.guess}}

\item{irt}{a list with one component \code{R} being the response matrix, use in case of IRT model}

\item{exp}{a list with one component \code{R} being the response matrix, use in case of expected model}

\item{dina}{a list with two components \code{R} and \code{Q}, being the response matrix and Q matrix respectively, use in case of DINA model}

\item{dino}{a list with two components \code{R} and \code{Q}, being the response matrix and Q matrix respectively, use in case of DINO model}

\item{nmf.con}{a list with two components \code{R} and \code{concepts}, being the response matrix and number of concepts, use in case of NMF CONJUNCTIVE model}

\item{nmf.dis}{a list with two components \code{R} and \code{concepts}, being the response matrix and number of concepts, use in case of NMF DISJUNCTIVE model}

\item{nmf.com}{a list with two components \code{R} and \code{concepts}, being the response matrix and number of concepts, use in case of NMF COMPENSATORY model}

\item{lin.avg}{a list with two components \code{R} and \code{concepts}, being the response matrix and number of concepts, use in case of LINEAR AVERAGE model}

\item{poks}{a list with four components \code{R}, \code{alpha.p}, \code{alpha.c}, \code{p.min}, use in case of POKS model}

\item{bkt}{a list with two components \code{R} and \code{order}, being the response matrix and its corresponding \code{order} vector (in case student improvement is allowed between taking two items), use in case of sequential data}
}
\value{
an object of \code{context} class describes the updated or newly assembled context
}
\description{
This function allows user assemble a new context or update an available context
}
\details{
This function takes in a set of parameters that the user input and assembles them
into a \code{context} object, also checks for some simple types of potential conflicts
}
\examples{
# Declare a context where there are 15 students and 20 items
p <- pars(students = 15, items = 20)
class(p)
# See all parameters inside p
names(p)
# See the currently available parameters in p
print(p)
}
\author{
Hoang-Trieu Trinh, \email{thtrieu@apcs.vn}
}
\seealso{
\code{init}
}

