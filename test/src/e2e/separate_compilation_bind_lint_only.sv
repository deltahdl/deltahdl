// A bound design is treated as one elaborated from source: --lint-only stops
// the run after the bind, so sc_leaf's $display never runs and the output is
// empty.
module sc_leaf;
  initial $display("leaf ran");
endmodule

module sc_top;
  sc_leaf u();
endmodule
