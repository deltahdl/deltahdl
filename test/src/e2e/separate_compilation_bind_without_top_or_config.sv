// §33.5.4 (printed page 944): the binding invocation is given the top-level
// cells or the config to bind, and one given neither has nothing to root the
// design at, so it is refused with status 1.
module sc_leaf;
  initial $display("leaf ran");
endmodule

module sc_top;
  sc_leaf u();
endmodule
