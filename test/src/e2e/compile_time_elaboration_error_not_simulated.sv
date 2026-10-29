// §3.12 (printed page 55): an implementation may report a compile-time error
// at any time before simulation starts. In a plain run, one that would go on
// to simulate, the undeclared name the first initial procedure writes is
// reported, the run fails with status 1, and the second procedure's display is
// never reached. compile_time_error_free_design_simulates.sv declares the name.
module compile_time_elaboration_error_not_simulated;
  initial undeclared_x = 1;
  initial $display("ran");
endmodule
