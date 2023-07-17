/*
This is a model of a voter for sensor values.

$ spin -a voter.pml
$ gcc pan.c -O2 -o pan
$ ./pan -a
*/

//#include "psr.pml"

#define n 3

mtype = {sensor_msg, voter_msg}

chan q = [4] of {mtype, bool, short};

short ghost_values[n];
bool ghost_self_checks[n];

proctype Sensor(byte input; byte id) {
    short sensor_value;
    bool self_check_ok = false;
    if
    :: true ->
       self_check_ok = true;
       sensor_value = input
    :: true ->
       self_check_ok = false;
       sensor_value = -1
    fi;
    ghost_values[id] = sensor_value;
    ghost_self_checks[id] = self_check_ok;
    if
    :: true -> skip
    :: true -> end_failed: (false)
    fi;
    q ! sensor_msg, self_check_ok, sensor_value
}

active proctype Voter() {
    short read[n];
    short voter_result
    bool sensor_self_check;
    byte count_values = 0;
    do
    :: q ? sensor_msg, sensor_self_check, read[count_values];
       if
       :: sensor_self_check -> count_values++
       :: else -> skip
       fi
    :: count_values == n -> break
    od;
    voter_result = read[0];
    byte i = 0;
    short max, min;
    do
    :: i < count_values ->
       if
       :: read[i] < min -> min = read[i]
       :: read[i] > max -> max = read[i]
       :: else -> skip
       fi;
       i++
    :: else -> break
    od;
    i = 0;
    do
    :: i < count_values ->
       if
       :: min < read[i] && read[i] < max ->
          voter_result = read[i]
       :: else -> skip
       fi;
       i++
    :: else -> break
    od;
    q ! voter_msg, true, voter_result
}

short ghost_voter_output = -1;

active proctype Controller() {
    short voter_output = -1;
    q ? voter_msg, true, voter_output;
recv:
    ghost_voter_output = voter_output
}

init {
    byte value, i;
    atomic {
        for(i : 1 .. n) {
            select(value : 1 .. 30);
            run Sensor(value, i-1)
        }
    }
}

/*init {
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
            run Sensor(values[i-1])
        }
    }
}*/
