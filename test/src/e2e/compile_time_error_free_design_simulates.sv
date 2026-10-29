// §3.12 (printed page 55): the design of
// compile_time_elaboration_error_not_simulated.sv and
// compile_time_syntax_error_not_simulated.sv with no compile-time error: the
// name the first initial procedure writes is declared and nothing follows the
// module, so the run simulates it and its display is reached.
module compile_time_error_free_design_simulates;
  int x;
  initial x = 1;
  initial $display("ran");
endmodule
