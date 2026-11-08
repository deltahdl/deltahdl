class C; endclass
module subdef; endmodule
module top;
  longint l; shortint s;
  C c = new;
  subdef u();
  initial #1 $probe;
endmodule
