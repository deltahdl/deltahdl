`timescale 1ns / 1ns
module a;
  initial $display("a0");
  initial #5 $display("a %0d", $time);
endmodule
module b;
  initial #0 $display("b0");
  initial #1 $display("b %0d", $time);
endmodule
module chk;
  initial #3 $display("chk");
endmodule
bind b chk c();
