/*
This is a model of Herlihy's n-process wait-free consensus
protocol specified in Figures 8 and 9 of the paper:

Herlihy, M. (1991). Wait-free synchronization. ACM Transactions on
Programming Languages and Systems (TOPLAS), 13(1), 124-149.
*/

#include "psr.pml"

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

/*
// default process initialization, without any reduction
init {
    byte value, i;
    atomic {
        for(i : 1 .. n) {
            select(value : 1 .. n);
            run Process(value)
        }
    }
}
*/

// process initialization using Partition Symmetry Reduction
init {
    byte values[n];
    byte i;
    init_partition(n);
    atomic {
        do
        :: !last_partition() ->
           next_partition()
        :: true ->
           select_partition(values);
           break
        od;
        for(i : 1 .. n) {
            run Process(values[i-1])
        }
    }
}

/*
Herlihy's wait-free consensus for n processes.

For 4 processes the verification yields:

$ spin -a example.pml
$ gcc -O2 pan.c -o pan
$ ./pan

(Spin Version 6.5.2 -- 13 October 2022)
	+ Partial Order Reduction

Full statespace search for:
	never claim         	- (none specified)
	assertion violations	+
	acceptance   cycles 	- (not selected)
	invalid end states	+

State-vector 64 byte, depth reached 103, errors: 0
    10960 states, stored
     7378 states, matched
    18338 transitions (= stored+matched)
     5924 atomic steps
hash conflicts:         4 (resolved)

Stats on memory usage (in Megabytes):
    0.962	equivalent memory usage for states (stored*(State-vector + overhead))
    0.967	actual memory usage for states
  128.000	memory used for hash table (-w24)
    0.534	memory used for DFS stack (-m10000)
  129.413	total actual memory usage


unreached in proctype Process
	(0 of 19 states)
unreached in init
	(0 of 71 states)

pan: elapsed time 0.01 seconds
    
Observations:
- nearly two orders of magnitude less memory used
- nearly duplicates the feasible number of processes
*/
