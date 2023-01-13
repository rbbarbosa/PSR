/*
This is a formalization of Partition Symmetry Reduction, in
Promela, for the Spin model checker, presented in:

Barbosa, R., Fonseca, A., & Araujo, F. (2021). Reductions and
abstractions for formal verification of distributed round-based
algorithms. Software Quality Journal, 29(3), 705-731.
*/

/* declares all necessary variables and resets the partition */
#define init_partition(n) byte partition[n], p_end, tmp, count; \
                          reset_partition();

// the first partition is just [n,0,0,...,0]
inline reset_partition() {
    for(tmp in partition) {
        partition[tmp] = 0
    }
    partition[0] = tmp;
    p_end = 1
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

// creates an array of usable values from the current partition
inline select_partition(values) {
    count = 0;
    tmp = 0;
    do
    :: count < partition[p_end-1] ->
       count++;               // count the members of each group
       values[tmp] = p_end;   // and give them the correct value
       tmp++
    :: else ->
       p_end--;
       if
       :: p_end == 0 -> break
       :: else -> count = 0
       fi
    od;
    for(tmp in partition) {
        if
        :: partition[tmp] == 0 -> break
        :: else -> p_end++
        fi
    }
}
