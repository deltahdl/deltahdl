// §33.5.3 (printed page 944): the tool that does the binding is told the
// top-level module or modules of the design, so two --top options root the
// bound design at both cells. sc_two_tops_b waits a step, so its line comes
// after sc_two_tops_a's.
//
// separate_compilation_bind_two_tops.before compiles this file into the
// library `two_lib` and writes it to two.lib; the .args file loads two.lib and
// names both modules.
module sc_two_tops_a;
  initial $display("top a ran");
endmodule

module sc_two_tops_b;
  initial #1 $display("top b ran");
endmodule
