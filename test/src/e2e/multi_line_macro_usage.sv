// IEEE 1800-2023 §22.5.1: the actual arguments of a macro usage are enclosed
// in parentheses and separated by commas, and the clause places them on no
// particular line, so a usage whose argument list is still open at the end of
// a line continues on the next one and is one usage: `report is expanded with
// its second argument written on the line after its first, `sum with its two
// operands on two lines, `report again with a second argument that is a
// concatenation opened on one line and closed on the next, as UVM's
// uvm_misc.svh writes one; and §22.13 has `__LINE__ expand to the current
// input line number, which for an argument of a usage read as one construct
// is the line the usage opened on, 24, not the line the argument stands on.
module multi_line_macro_usage;
  `define report(id, msg) begin id_s = id; msg_s = msg; $display("%s: %s", id_s, msg_s); end
  `define sum(a, b) (a + b)
  string id_s, msg_s;
  int total;
  initial begin
    `report("split",
            "the second argument stands on the line after the first")
    total = `sum(40,
                 2);
    $display("sum of operands on two lines: %0d", total);
    `report("concat", {"the argument is a concatenation ",
                       "closed on the next line"})
    $display("line the usage opened on: %0d", `sum(`__LINE__,
                                                   0));
  end
endmodule
