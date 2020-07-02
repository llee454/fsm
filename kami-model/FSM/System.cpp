#include "verilated.h"
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <getopt.h>
#include "verilated_vcd_c.h"

#include "Vsystem.h"

int main(int argc, char ** argv, char **env) {
  Verilated::commandArgs(argc, argv);
  Verilated::traceEverOn(true);

  Vsystem* system = new Vsystem;
  VerilatedVcdC* tfp = new VerilatedVcdC;
  system->trace(tfp,99);
  tfp->open("trace.vcd");

  vluint64_t main_time = 0;

  int result = 0;
  uint32_t timeout = 40;

  bool finished;
  uint64_t numBlockBytes = (1<<20)-1;

  finished = false;

  while(!Verilated::gotFinish() && main_time < timeout && !finished){
    printf("MainTime = %lu\n", main_time);

    system->CLK = 1;
    system->eval();
    tfp->dump(main_time++);
    system->CLK = 0;
    system->eval();
    tfp->dump(main_time++);

    fflush(stdout);
  }

  if (main_time >= timeout) {
    fprintf(stdout, "Timeout Reached\n");
    result=0;
  }

  system->final();
  tfp->close();
  delete system;
  delete tfp;
  return result;
}
