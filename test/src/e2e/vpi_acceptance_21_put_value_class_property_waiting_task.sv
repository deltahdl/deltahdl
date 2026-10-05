// §38.34 x §37.33 x §9.4.1 (printed page 1125, 1045) of IEEE 1800-2023: a value
// put on a class object's property is seen by a class task blocked in wait() on
// it, in the same time step. The library
// vpi_acceptance_21_put_value_class_property_waiting_task.c, built beside the
// run and named by
// vpi_acceptance_21_put_value_class_property_waiting_task.args, is the VPI
// application under test (#4338).
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
