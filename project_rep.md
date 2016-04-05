The paper proposes a cost model for analyzing memory efficiency of algorithms written in a
functional language. It describes an implementation of the language. The paper claims to show
that some algorithms written in their standard form (in the functional language described)
without any attention paid to memory allocations can be as asymptotically efficient as cache
efficient algorithms.
To understand the objective of the paper, we need to understand what cache efficient
algorithms are. When algorithms are defined, it is assumed that the cost of accessing the
memory is uniform. This is not true in the practical implementation of modern computer
systems in general. Computers now employ two levels of memory for Random Access:- the
RAM and the cache. The access time for RAM and the cache are significantly different, and
hence a naive estimation of memory efficiency fails. A better model is hence used that takes
into account this difference. In this model, the time taken for copying memory from RAM to
cache (from which the processor finally accesses it) is factored as a unit cost.
However in practice, movements of objects from RAM to cache is a computationally expen-
sive process. The designer has to factor memory management as a part of the algorithm itself.
The paper relies upon the fact that it is an experimentally proven fact that there exist certain
memory-allocation strategies that allow for purely functional programs to be cache efficient.
The paper proposes cost dynamics for the model. It defines the method for computing cost
in the model by approximating the movements of objects from RAM to cache. The paper
then defines an abstract machine on which is used to validate the claims made in evaluation dynamics.
The most intriguing part seems to be the fact that the
authors have not timed anything experimentally, yet they claim to deliver fascinating results;
namely, allow for analysis of algorithms implemented in a high-level language to be I/O efficient while
abstracting the memory management from the programmer. The setting used is call-by-value functional
using recursive data types and get provable bounds on cache complexity.

Question! ?? 
We have tried to investigate the claims made by the paper, namely the Storage Model, Evaluation Dynamics and
  "Reading and Allocation Judgments" defined by the paper
and how they provide a basis of assessing the correctness and cache complexity of the programs.
   The paper proposes 6 evaluation judgments and 6 reading and allocation judgments. The evaluation
judgments are of the form : SIGMA @ e DOWN ARROW N R SIGMA @ L. We have tried to understand the functioning
 and the logic behind these judgment forms and what led the author to write them as they are, as well as how
 they lead to a successful approximation. Finally, how does this approximation stack against the I/O model mentioned in the paper. 

    Our approach to study the evaluation dynamics was to read the relevant bits of the paper to build an intuitive but 
  informal understanding of the evaluation dynamics, as suggested by the paper.  The next step was to try and build
 a redex model of the language suggested as well as implementation of the cost dynamics. To do this we  developed
the PCF language mentioned by the paper. We then tried to implement the evaluation dynamics as well as the 'reading and  allocation' judgments.
 Our methods helped us understand that the author has tried to account for all possible costs when proposing the 
 Cost Dynamics while minimizing the amount of unnecessary accesses to the RAM by mantaining a set of objects called ROOTS. At any step in the evaluation judgments, the author
takes care of allocating the stack frames as well as accounting for all other allocations as necessary.
  
The author also takes care to have the bounds of the cache properly accounted and has mechanism necessary for eviction when necessary.
 These conditions being when the cache is filled to the set capacity. 
    Finally, the costs accounted for each allocation, deallocation and read is carefully accounted and added to get the results. The paper then
   proposes an abstract machine on which he proves that the cost incurred for each computation is indeed asymtopically equal to 
   the cost determined by the evaluation dynamics. Since every transaction from the RAM to the cache and vice versa are recorded and the paper
   designates costs based upon the same assumptions as the IO model we can agree that the algorithms written in this model will be as efficient as those written in I/O based model. We will try to implement a C program to try and validate the claim if possible.
