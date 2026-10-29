// §3.12 (printed page 55): an implementation may report a compile-time error
// at any time before simulation starts. In a plain run, the stray character
// after the module is reported as a syntax error, the run fails with status 1,
// and the module's display is never reached, as it is in
// compile_time_error_free_design_simulates.sv.
module compile_time_syntax_error_not_simulated;
  initial $display("ran");
endmodule
    %
