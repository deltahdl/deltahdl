interface ifc; int data = 8; endinterface
module sub; int x = 5; endmodule
module top;
  sub u();
  ifc i0();
  int \my-var  = 3;
  for (genvar i = 0; i < 2; i++) begin : g
    int y = 10 + i;
  end
  initial #1 $probe;
endmodule
