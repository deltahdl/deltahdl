`timescale 1ns/1ns
class C;
  int val;
  task wait_for_nine(); wait (val == 9); $display("saw %0d at %0t", val, $time); endtask
endclass
module top;
  C c = new;
  initial begin
    fork c.wait_for_nine(); join_none
    #4 $probe;
    #1 $display("sv val=%0d at %0t", c.val, $time);
  end
endmodule
