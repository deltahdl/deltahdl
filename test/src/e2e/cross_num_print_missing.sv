module t;
  bit x, y;
  covergroup cg;
    a: coverpoint x;
    b: coverpoint y;
    ab: cross a, b { option.cross_num_print_missing = 2; }
  endgroup
  cg c = new;
  initial begin
    x = 0; y = 0; c.sample();
    $display("done");
  end
endmodule
