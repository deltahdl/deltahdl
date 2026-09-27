// --vcd opens the same 4-state dump §21.7.1 has $dumpfile and $dumpvars open,
// with no $dumpvars awaited, so the whole design is recorded from time 0. The
// dump is rooted at the top-level instance --top names: this file has two
// top-level modules, --top selects vcd_option_top, and only its scope and its
// variable appear in the file.
module vcd_option_top;
  logic a = 0;
  initial begin
    #1 a = 1;
    #1 $finish;
  end
endmodule

module vcd_option_other;
  logic b = 1;
endmodule
