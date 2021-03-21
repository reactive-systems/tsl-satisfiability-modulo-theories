#!/bin/bash

#
# This function takes a timeout (in seconds), a baspath and filepattern and
# and outfile and then performs benchmarking
#
messure () {
    
    # Read the function arguments (yes this is another reason bash is ugly)
    local timeout=$1
    local basepath=$2 
    local outfile=$3
    
    # Remove the outgoing csv file and (re)initialize it
    rm -f $outfile 
    echo "Name,Spot,Result,Time" > $outfile

    # Iterate over all files mesure the time (with timeout) and write
    # Result into CSV file
    for file in $basepath*.tsl
    do
        timeBefore=`date +%s%N`
        out=`timeout $timeout ./tslsat $file` 
        out=${out//[$'\t\r\n']}
        timeAfter=`date +%s%N`
        diff=$(((timeAfter-timeBefore)/1000000))
        spotTO="TO"
        sat="TO"
        if [ "$out" = "SPOT-TOSPOT FINISHEDSAT" ] 
        then
            spotTO="-"
            sat="SAT"
        fi 
        if [ "$out" = "SPOT-TOSPOT FINISHEDUNSAT" ] 
        then
            spotTO="-"
            sat="UNSAT"
        fi 
        if [ "$out" = "SPOT-TOSPOT FINISHEDLTL-UNSAT" ] 
        then
            spotTO="-"
            sat="LTL-UNSAT"
        fi 
        if [ "$out" = "SPOT-TOSPOT FINISHED" ] 
        then
            spotTO="-"
        fi
        if [ "$out" = "SPOT FINISHEDSAT" ] 
        then
            spotTO="OPT"
            sat="SAT"
        fi 
        if [ "$out" = "SPOT FINISHEDLTL-UNSAT" ] 
        then
            spotTO="OPT"
            sat="LTL-UNSAT"
        fi
        if [ "$out" = "SPOT FINISHEDUNSAT" ] 
        then
            spotTO="OPT"
            sat="UNSAT"
        fi
        if [ "$out" = "SPOT FINISHED" ] 
        then
            spotTO="OPT"
        fi 

        echo "${file##*/},$spotTO,$sat,$diff ms" >> $outfile
        echo "${file##*/},$spotTO,$sat,$diff ms"
    done
}

#
# The messurements
#
mkdir -p results 

make
messure 30 benchmarks/fuzzed/ results/fuzzed.csv
messure 30 benchmarks/syntroids/ results/syntroids.csv
messure 30 benchmarks/tests/ results/tests.csv
messure 60 benchmarks/scalability/ results/scalability.csv
messure 1200 benchmarks/story/ results/story.csv
