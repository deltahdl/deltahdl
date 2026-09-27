// §33.5.4 (printed page 944): the binding invocation needs only the
// top-level cells, here named by --top, and descends through the precompiled
// cells from there: sc_top instantiates sc_leaf, which runs.
module sc_leaf;
  initial $display("leaf ran");
endmodule

module sc_top;
  sc_leaf u();
endmodule
