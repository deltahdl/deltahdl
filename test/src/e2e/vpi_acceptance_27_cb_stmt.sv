// §38.36.1.1-§38.36.1.3, Table 38-6 (printed page 1136-1137) of IEEE 1800-2023:
// a module-wide cbStmt places a callback before every statement: the block
// once, each assignment, the delay control. The library
// vpi_acceptance_27_cb_stmt.c, built beside the run and named by
// vpi_acceptance_27_cb_stmt.args, is the VPI application under test (#4338).
module top;
  int a, b, c;
  initial begin
    a = 1;
    b = 2;
    #1 c = 3;
  end
endmodule
