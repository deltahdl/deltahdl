// §37.31 detail 2 (printed page 1042), §38.15, §38.34 of IEEE 1800-2023:
// get/put on a var handle from a class defn is an error; through the class obj
// it works. The library vpi_acceptance_22_put_value_classdefn_var_illegal.c,
// built beside the run and named by
// vpi_acceptance_22_put_value_classdefn_var_illegal.args, is the VPI
// application under test (#4338).
module top;
  class C; int val = 4; endclass
  C c = new;
  initial begin
    #1 $probe;
    $display("sv val=%0d", c.val);
  end
endmodule
