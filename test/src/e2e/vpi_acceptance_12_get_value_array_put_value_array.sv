// §38.16, §38.35 (printed page 1106, 1128) of IEEE 1800-2023: array values read
// into one buffer and written back with vpiNoDelay. The library
// vpi_acceptance_12_get_value_array_put_value_array.c, built beside the run and
// named by vpi_acceptance_12_get_value_array_put_value_array.args, is the VPI
// application under test (#4338).
module top;
  int arr[4] = '{1, 2, 3, 4};
  initial begin
    #1 $probe;
    $display("sv %0d %0d %0d %0d", arr[0], arr[1], arr[2], arr[3]);
  end
endmodule
