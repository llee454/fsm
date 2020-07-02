#!/usr/bin/env bash
#
# Builds the Ice Storm tool chain test module.
# coq_makefile -Q ../Kami/ Kami -Q ../coq-record-update/src/ RecordUpdate -Q . IceStomTest IceStormTest.v > Makefile
#
# Note: you may have to manually remove the CustomExtract import from CustomExtract.hs

make && \
cd ../Kami && ./fixHaskell.sh ../FSM && cd ../FSM && \
cp CustomExtract.bak CustomExtract.hs && \
ghc -O2 --make -i../Kami -i../Kami/Compiler ../Kami/Compiler/CompAction.hs && \
../Kami/Compiler/CompAction > System.sv && \

#yosys -p "synth_ice40 -blif System.blif" System.sv && \
#arachne-pnr -d 8k -p System.pcf System.blif -o System.asc && \
#icepack System.asc System.bin && \

#env VERILATOR_ROOT=/home/ubuntu/objs/verilator/verilator verilator --error-limit 10000000 --top-module system -Wno-CMPCONST -Wno-WIDTH --cc System.sv --trace --trace-underscore -Wno-fatal --exe System.cpp
#cd obj_dir
#env VERILATOR_ROOT=/home/ubuntu/objs/verilator/verilator make -f Vsystem.mk Vsystem
#./Vsystem
#cd ..

echo "done"
