/*
This is a formalization of Partition Symmetry Reduction, in Promela,
for the Spin model checker, as presented in Figure 2 of the paper:

Barbosa, R., Fonseca, A., & Araujo, F. (2021). Reductions and
abstractions for formal verification of distributed round-based
algorithms. Software Quality Journal, 29(3), 705-731.

The application is a model of Herlihy's n-process wait-free consensus
protocol specified in Figures 8 and 9 of the paper:

Herlihy, M. (1991). Wait-free synchronization. ACM Transactions on
Programming Languages and Systems (TOPLAS), 13(1), 124-149.
*/

#define n 4

byte r;

inline compare_and_swap(r, old, new, result) {
    atomic {
        previous = r;
        if
        :: previous == old -> r = new
        :: else -> skip
        fi;
        result = previous
    }
}

byte ghost;

proctype Process(byte input) {
    byte previous, first, decision;
    compare_and_swap(r, 0, input, first);
    if
    :: first == 0 -> decision = input
    :: else -> decision = first
    fi;
    ghost = decision;
    assert(ghost == decision)
}

// process initialization using Partition Symmetry Reduction
init {
    byte partition[n];  // holds the current partition
    byte v, i = 1;      // i points to the partition's end
    byte count;         // counts processes in each group
    partition[0] = n;   // the initial partition is just [n]
    atomic {
        do
        :: partition[0] != 1 ->  // if more partitions exist
           v = 1;                // compute the next partition
           do
           :: partition[i-1] == 1 ->
              i--;               // index of last element > 1
              v++                // elements to be updated
           :: else -> break
           od;
           partition[i-1]--;     // update partition elements
           do
           :: partition[i-1] < v ->
              v = v - partition[i-1];
              partition[i] = partition[i-1];
              i++
           :: else -> break
           od;
           i++;
           partition[i-1] = v
        :: true ->               // use the current partition
           v = i;                // begin with highest value
           count = 0;
           do
           :: count < partition[v-1] ->
              run Process(v);    // start and count processes
              count++            // in group that has value v
           :: else ->
              v--;
              count = 0;
              if
              :: v == 0 -> break // end with lowest value
              :: else -> skip
              fi
           od;
           assert(_nr_pr == n+1);
           break
        od
    }
}

/*
// default process initialization, without any reduction
init {
    byte v, i;
    atomic {
        for(i : 1 .. n) {
            select(v : 1 .. n);
            run Process(v)
        }
    }
}
*/

/*
Herlihy's wait-free consensus for n processes.

For 4 processes the verification yields:

$ spin -a partition_symmetry_reduction.pml 
$ gcc pan.c -o pan
$ ./pan

State-vector 56 byte, depth reached 51, errors: 0
   487445 states, stored
   343164 states, matched
   830609 transitions (= stored+matched)
   265106 atomic steps
hash conflicts:      2718 (resolved)

Stats on memory usage (in Megabytes):
   39.049	equivalent memory usage for states (stored*(State-vector + overhead))
   29.589	actual memory usage for states (compression: 75.78%)

Observations:

- The main cause for the complexity of the verification is the select statement in
the init process.

- If we have 4 processes then we have only a few combinations that may be fully
enumerated. Otherwise we have 4^4 = 256 initial states.

Using the init with the Partition Symmetry Reduction:

State-vector 64 byte, depth reached 100, errors: 0
    10882 states, stored
     7361 states, matched
    18243 transitions (= stored+matched)
     5909 atomic steps
hash conflicts:         8 (resolved)

Stats on memory usage (in Megabytes):
    0.955	equivalent memory usage for states (stored*(State-vector + overhead))
    0.870	actual memory usage for states (compression: 91.14%)
    
Observations:
- nearly two orders of magnitude less memory
- nearly duplicates the number of processes
*/
