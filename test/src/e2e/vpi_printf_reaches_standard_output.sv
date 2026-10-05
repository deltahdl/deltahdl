// §38.30 (vpi_printf), §38.41 (vpi_vprintf) and §38.27 (vpi_mcd_printf, whose
// channel 1 is the tool's output channel) have a PLI application's text
// written to the output channel of the tool, where $display writes. The
// library vpi_printf_reaches_standard_output.c, built beside the run and
// named by vpi_printf_reaches_standard_output.args, prints from its startup
// routine and from the calltf of the $probe it registers.
module t;
  initial begin
    $display("disp 0");
    #1 $probe;
    $display("disp 1");
  end
endmodule
