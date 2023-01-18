/*
Correctness properties:

1. the total number of partitions equals the theoretical partition function p(n)
   - generate and cound all partitions and check that total == p(n)

2. the sum of partition elements equals n
   - along with 1., invert the values back into a partition and...
   - ...check that the sum of elements equals n

3. all partitions are unique
   - non-deterministically select any two partitions and check that they differ
   - partitions are sorted, so checking for differences is simple
*/

#include "psr.pml"

#define n 19

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

inline print(array) {
    for(tmp in array) {
        printf("[%d]", array[tmp]);
    }
    printf("\n");
}

inline check_sum(values, inversion) {
   for(i in inversion) {   // invert the values back into a partition
      c = 0;
      for(j in values) {
         if
         :: values[j] == i+1 -> c++
         :: else -> skip
         fi
      }
      inversion[i] = c
   }
   c = 0;   // compute the sum of elements in the partition
   for(i in inversion) {
      c = c + inversion[i];
   }
   assert(c == n)   // the sum of partition elements equals n
}

init {
    byte part1[n], part2[n];
    byte i, j, c;
    short sum;

    init_partition(n);
    // count the total number of partitions
    sum = 1;
    do
    :: !last_partition() ->
       select_partition(part1);
       check_sum(part1, part2);   // check that the sum equals n
       next_partition();
       sum++
    :: else -> break
    od;
    select_partition(part1);
    check_sum(part1, part2);   // check that the sum equals n
    check_total(sum);   // check that the total == p(n)

    // check that all partitions are unique
    reset_partition();
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
    assert(different)   // check that the partitions are different
}

/*
Verification results for n = 19

$ spin -a verification.pml
$ gcc pan.c -O2 -o pan
$ ./pan -m1000000

(Spin Version 6.5.2 -- 13 October 2022)
	+ Partial Order Reduction

Full statespace search for:
	never claim         	- (none specified)
	assertion violations	+
	acceptance   cycles 	- (not selected)
	invalid end states	+

State-vector 80 byte, depth reached 629644, errors: 0
 45283601 states, stored
   475314 states, matched
 45758915 transitions (= stored+matched)
        0 atomic steps
hash conflicts:  11186243 (resolved)

Stats on memory usage (in Megabytes):
 4664.067	equivalent memory usage for states (stored*(State-vector + overhead))
 4265.160	actual memory usage for states (compression: 91.45%)
         	state-vector as stored = 71 byte + 28 byte overhead
  512.000	memory used for hash table (-w26)
   53.406	memory used for DFS stack (-m1000000)
    2.687	memory lost to fragmentation
 4827.879	total actual memory usage


unreached in init
	verification.pml:42, state 196, "assert(0)"
	verification.pml:57, state 220, "p_curr = (p_curr+1)"
	verification.pml:59, state 222, "tmp = (tmp-1)"
	verification.pml:32, state 235, "tmp = (tmp+1)"
	verification.pml:39, state 244, "partition[p_end] = partition[(p_end-1)]"
	verification.pml:40, state 245, "p_end = (p_end+1)"
	(6 of 390 states)

pan: elapsed time 35.8 seconds
pan: rate 1265258.5 states/second
*/
