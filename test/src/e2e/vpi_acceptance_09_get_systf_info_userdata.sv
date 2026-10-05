// §38.12, §38.33, §38.14 (printed page 1098, 1125, 1100) of IEEE 1800-2023:
// vpi_get_systf_info gives tfname, type and user_data of the call;
// vpi_put_userdata/vpi_get_userdata attach data per call instance. The library
// vpi_acceptance_09_get_systf_info_userdata.c, built beside the run and named
// by vpi_acceptance_09_get_systf_info_userdata.args, is the VPI application
// under test (#4338).
module top;
  initial begin
    repeat (2) $probe;
    $probe;
  end
endmodule
