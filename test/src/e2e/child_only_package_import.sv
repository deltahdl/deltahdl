// §26.3 makes the identifiers of a package visible without a package name
// qualifier within the scope that writes the import, and the scope here is
// `child`. `top` imports nothing, so the child's own import is the only thing
// that can make VAL visible to the $display, and a run that binds the import
// for the top module alone prints "VAL=0".
// The instantiating module is written last, because a run that names no top
// module elaborates the last module of the source (src/main.cpp).
package pkg;
  parameter int VAL = 77;
endpackage

module child;
  import pkg::VAL;

  initial $display("VAL=%0d", VAL);
endmodule

module top;
  child u1();
endmodule
