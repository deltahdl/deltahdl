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
