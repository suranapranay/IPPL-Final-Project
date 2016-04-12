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


The paper raised the following questions - How are the authors able to prove the bounds on costs? How do
the evalutaion dynamics work and help in calculation the cost. Why were the memory allocation strategies chosen as they were. Why do these dynamics lead to successful approximation of cache complexity of an algorithm. 
To elaborate, The paper proposes six evaluation judgments and a few auxiliary reading and allocation judgments to manage the memory. The evaluation
judgments are of the form : SIGMA @ e DOWN ARROW N R SIGMA @ L. 
This form means that when an expression is evaluated with respect to a memory store sigma and roots R, the cost of the evaluation is n, and the result is stored at location L.
 Our approach to study the evaluation dynamics was to read the relevant bits of the paper to build an intuitive but 
  informal understanding of the evaluation dynamics, as suggested by the paper.  The next step was building  
 a redex model of the language suggested as well as implementation of the cost dynamics. To do this we  developed
the PCF language mentioned by the paper. We then implemented the evaluation dynamics as well as the 'reading and  allocation' judgments.

With the implementation of the redex model, we could understand the subtleties of the evaluation dynamics and the decisions made by the author
while writing them. The basis of the evaluation dynamics is the fact that if we can account for every single cost of movement of data from the RAM to the cache and from the cache to the RAM, we will have a good approximate on the cost of evaluation.  Furthermore, if we can automate the memory management as opposed to letting the programmer handle it, we can have a definite accounting of the movement of data between the two levels of memory.

The authors track all the transaction of the memory by classifying them as Read and Allocation transactions. A read cost is added when the program accesses data not available in the cache and has to be copied from the RAM. An allocation cost is added to the total cost when a new object is created in the allocation cache.
For each expression, the rules allocate a stack frame (even though they are never read). A root set which is a subset of the allocation cache is
mantained and all objects in the nursery which are transitively reacheable from the roots are considered 'live'. When the number of live objects reaches the maximum size of the nursery, the oldest live objects are evicted from the nursery before an allocation can happen. This cost of movement is also accounted for. 
The total cost of all the above scenarios is the cost assigned by the Evaluation dynamics to the program and since all possible costs were accounted in the evaluation dynamics, the predictions are considered at most a constant less than actual execution but of the same order.

The authors do not explain the reason behind accounting only live objects when making the decision for eviction. The nursery can be filled with objects that are not live. We say this because should the nursery only have live objects, there would be no need to keep track of a root set. This would mean that the nursery can extend indefinitely, but that is not true in a real computer.
Thus, to conclude, the paper presents convincing model for analyzing algorithms in systems where there are two memories, it seems to present an ideal case and does not seem to explain the reasoning behind the live objects and root set.
