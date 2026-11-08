package dump_ast_pkg;
  localparam int P = 1;
  typedef logic [3:0] nibble_t;
endpackage

module dump_ast_module_and_package(input logic i, output logic o);
  assign o = i;
endmodule

module dump_ast_top;
  logic i = 1, o;
  dump_ast_module_and_package u(.i(i), .o(o));
  initial #1 $display("o=%0d", o);
endmodule
