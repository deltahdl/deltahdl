// §19.7, Table 19-1: the coverage report at the end of the run lists as many
// of a cross's missing cross bins as its cross_num_print_missing asks for.
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
