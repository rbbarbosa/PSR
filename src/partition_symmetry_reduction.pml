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

byte partition[n];   // holds the current partition
byte p_end;          // points to the partition's end
byte tmp, count;     // temporary variables

// the initial partition is just [n,0,0,...,0]
inline init_partition() {
    for(tmp in partition) {
        partition[tmp] = 0
    }
    partition[0] = n;
    p_end = 1   // the initial partition contains a single element
}

// evaluates if the current partition is the last possible one
#define last_partition() (partition[0] == 1)

// computes the next partition in lexicographic order
inline next_partition() {
    tmp = 1;
    do
    :: partition[p_end-1] == 1 ->
       p_end--;             // index of last element > 1
       tmp++                // elements to be updated
    :: else -> break
    od;
    partition[p_end-1]--;   // update partition elements
    do
    :: partition[p_end-1] < tmp ->
       tmp = tmp - partition[p_end-1];
       partition[p_end] = partition[p_end-1];
       p_end++
    :: else -> break
    od;
    p_end++;
    partition[p_end-1] = tmp
}

// transforms the current partition into an array of usable values
inline select_partition(values) {
    count = partition[p_end-1];
    tmp = 0;
    do
    :: count > 0 ->
       count--;
       values[tmp] = p_end;
       tmp++
    :: else ->
       p_end--;   // ToDo: consider using another variable instead
       if
       :: p_end == 0 -> break
       :: else -> count = partition[p_end-1]
       fi
    od
}

inline print(array) {   // debug
    for(tmp in array) {
        printf("[%d]", array[tmp]);
    }
    printf("\n");
}

// process initialization using Partition Symmetry Reduction
init {
    byte values[n];
    byte i;
    init_partition();
    atomic {
        do
        :: !last_partition() ->
           print(partition);
           next_partition();
        :: true ->
           print(partition)
           select_partition(values);
           print(values)
           break
        od;
        for(i : 1 .. n) {
            run Process(values[i-1])
        }
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
