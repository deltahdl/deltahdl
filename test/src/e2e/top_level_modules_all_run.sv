// §23.3.1: "Top-level modules are modules that are included in the
// SystemVerilog source text, but do not appear in any module instantiation
// statement ... A top-level module is implicitly instantiated once". Neither
// a nor b instantiates the other, so both are top-level modules and every
// initial procedure of each runs. With no --top the command line took the
// last module in the source for the one top, and a's initials never ran.
//
// §23.11: "The bind_instantiation is effectively a complete module, interface,
// program, or checker instantiation statement", so chk, which the bind alone
// names, is no top-level module and runs once, bound into b.
`timescale 1ns / 1ns
module a;
  initial $display("a0");
  initial #5 $display("a %0d", $time);
endmodule
module b;
  initial #0 $display("b0");
  initial #1 $display("b %0d", $time);
endmodule
module chk;
  initial #3 $display("chk");
endmodule
bind b chk c();
