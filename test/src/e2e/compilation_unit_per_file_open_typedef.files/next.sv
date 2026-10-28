} s_t;
module m;
  s_t v;
  initial begin
    v.a = 7;
    $display("%0d", v.a);
    $finish;
  end
endmodule
