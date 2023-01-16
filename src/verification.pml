/*
Correctness properties:

1. all partitions are unique
   - non-deterministically select any two partitions and check that they differ
   - partitions are sorted, so checking for differences is simple

2. the total number of partitions equals the theoretical partition function p(n)
   - generate and cound all partitions and check that total == p(n)
*/

#include "psr.pml"

#define n 15

inline check_total(total) {
    if
    :: n == 1 -> assert(total == 1)
    :: n == 2 -> assert(total == 2)
    :: n == 3 -> assert(total == 3)
    :: n == 4 -> assert(total == 5)
    :: n == 5 -> assert(total == 7)
    :: n == 6 -> assert(total == 11)
    :: n == 7 -> assert(total == 15)
    :: n == 8 -> assert(total == 22)
    :: n == 9 -> assert(total == 30)
    :: n == 10 -> assert(total == 42)
    :: n == 11 -> assert(total == 56)
    :: n == 12 -> assert(total == 77)
    :: n == 13 -> assert(total == 101)
    :: n == 14 -> assert(total == 135)
    :: n == 15 -> assert(total == 176)
    :: n == 16 -> assert(total == 231)
    :: n == 17 -> assert(total == 297)
    :: n == 18 -> assert(total == 385)
    :: n == 19 -> assert(total == 490)
    :: n == 20 -> assert(total == 627)
    :: else -> assert(false)
    fi
}

init {
    byte part1[n], part2[n];
    byte i;
    short sum;

    init_partition(n);
    select_partition(part1);
    next_partition();
    select_partition(part2);
    // non-deterministically select any two partitions
    do
    :: !last_partition() ->
       next_partition();
       select_partition(part1)
    :: !last_partition() ->
       next_partition();
       select_partition(part2)
    :: true -> break
    od;

    // check that both partitions are sorted in descending order
    for(i : 0 .. n-2) {
       assert(part1[i] <= part1[i+1] && part2[i] <= part2[i+1])
    }
    // check that the two partitions are different
    bool different = false;
    for(i : 0 .. n-1) {
       if
       :: part1[i] != part2[i] -> different = true
       :: else -> skip
       fi
    };
    assert(different);   // check that the partitions are different
    
    // count the total number of partitions
    reset_partition();
    sum = 1;
    do
    :: !last_partition() ->
       next_partition();
       sum++
    :: else -> break
    od;
    check_total(sum)   // check that the total == p(n)
}

/*
Verification results for n = 15

$ spin -a verification.pml
$ gcc pan.c -O2 -o pan
$ ./pan -m100000

(Spin Version 6.5.2 -- 13 October 2022)
	+ Partial Order Reduction

Full statespace search for:
	never claim         	- (none specified)
	assertion violations	+
	acceptance   cycles 	- (not selected)
	invalid end states	+

State-vector 64 byte, depth reached 12146, errors: 0
 62501171 states, stored
    60206 states, matched
 62561377 transitions (= stored+matched)
        0 atomic steps
hash conflicts:  13782973 (resolved)

Stats on memory usage (in Megabytes):
 5483.730	equivalent memory usage for states (stored*(State-vector + overhead))
 5363.501	actual memory usage for states (compression: 97.81%)
         	state-vector as stored = 62 byte + 28 byte overhead
  512.000	memory used for hash table (-w26)
    5.341	memory used for DFS stack (-m100000)
    2.982	memory lost to fragmentation
 5877.860	total actual memory usage


unreached in init
	./psr.pml:56, state 21, "p_curr = (p_curr+1)"
	./psr.pml:58, state 23, "tmp = (tmp-1)"
	./psr.pml:31, state 36, "tmp = (tmp+1)"
	./psr.pml:38, state 45, "partition[p_end] = partition[(p_end-1)]"
	./psr.pml:39, state 46, "p_end = (p_end+1)"
	verification.pml:38, state 274, "assert(0)"
	(6 of 278 states)

pan: elapsed time 49.1 seconds
pan: rate   1272418 states/second
*/
