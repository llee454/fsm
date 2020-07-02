module _design(
  input logic getInputReady$_return,
  input logic[0:0] getInput$_return,

  output logic getInputReady$_enable,
  output logic getInput$_enable,
  output logic sendOutput$_enable,
  output logic sendOutput$_argument,

  input CLK,
  input RESET
);
  logic[1:0] state;

  logic[1:0] state$0;
  logic getInputReady$_enable$0;
  logic getInput$_enable$0;
  logic sendOutput$_enable$0;
  logic sendOutput$_argument$0;
  logic getInputReady$_enable$1;
  logic tmp$3;
  logic tmp$4;
  logic tmp$5;
  logic getInput$_enable$1;
  logic[0:0] tmp$6;
  logic[1:0] tmp$7;
  logic[1:0] state$1;
  logic[1:0] tmp$14;
  logic sendOutput$_argument$1;
  logic sendOutput$_enable$1;




  assign state$0 = state;
  assign getInputReady$_enable$0 = 1'b0;
  assign getInput$_enable$0 = 1'b0;
  assign sendOutput$_enable$0 = 1'b0;
  assign sendOutput$_argument$0 = 1'b0;
  assign getInputReady$_enable$1 = 1'b1;
  assign tmp$3 = getInputReady$_return;
  assign tmp$4 = (1'b1 & tmp$3 & 1'b1);
  assign tmp$5 = (1'b1 & ( ~ tmp$3) & 1'b1);
  assign getInput$_enable$1 = tmp$4;
  assign tmp$6 = getInput$_return;
  assign tmp$7 = state$0;
  assign state$1 = (tmp$4 ? (((tmp$7 == 2'b00) ? ((tmp$6 == 1'b0) ? 2'b00 : 2'b01) : 2'b00) | ((tmp$7 == 2'b01) ? ((tmp$6 == 1'b0) ? 2'b10 : 2'b00) : 2'b00) | ((tmp$7 == 2'b10) ? ((tmp$6 == 1'b0) ? 2'b01 : 2'b10) : 2'b00) | 2'b00) : state$0);
  assign tmp$14 = state$1;
  assign sendOutput$_argument$1 = (tmp$14 == 2'b00);
  assign sendOutput$_enable$1 = 1'b1;
  assign getInputReady$_enable = (getInputReady$_enable$0 | getInputReady$_enable$1 | 1'b0);
  assign getInput$_enable = (getInput$_enable$0 | getInput$_enable$1 | 1'b0);
  assign sendOutput$_enable = (sendOutput$_enable$0 | sendOutput$_enable$1 | 1'b0);
  assign sendOutput$_argument = (((sendOutput$_enable$0 ? (sendOutput$_argument$0 ? 1'b1 : 1'b0) : 1'b0) | (sendOutput$_enable$1 ? (sendOutput$_argument$1 ? 1'b1 : 1'b0) : 1'b0) | 1'b0) == 1'b1);




  always @(posedge CLK) begin
    if(RESET) begin
      state <= 2'b00;
    end
    else begin
      state <= state$1;
    end
  end
endmodule

module system(
  input logic getInputReady$_return,
  input logic[0:0] getInput$_return,

  output logic getInputReady$_enable,
  output logic getInput$_enable,
  output logic sendOutput$_enable,
  output logic sendOutput$_argument,

  input CLK,
  input RESET
);
  _design _designInst(.CLK(CLK), .RESET(RESET), .getInputReady$_return(getInputReady$_return), .getInput$_return(getInput$_return), .getInputReady$_enable(getInputReady$_enable), .getInput$_enable(getInput$_enable), .sendOutput$_enable(sendOutput$_enable), .sendOutput$_argument(sendOutput$_argument));
endmodule

