// §38.37.1 (printed page 1141) of IEEE 1800-2023: vpiTimeFunc returns a 64-bit
// time put with vpiTimeVal; vpiSizedSignedFunc is signed at the sizetf width,
// vpiSizedFunc unsigned. The library
// vpi_acceptance_31_systf_time_signed_funcs.c, built beside the run and named
// by vpi_acceptance_31_systf_time_signed_funcs.args, is the VPI application
// under test (#4338).
module top;
  time t;
  initial begin
    t = $user_time();
    $display("time %0d", t);
    $display("signed %0d unsigned %0d", $user_s8(), $user_u8());
  end
endmodule
