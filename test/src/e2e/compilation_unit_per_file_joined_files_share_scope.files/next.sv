  t v = `W;
  initial begin
    $display("%0d %0d", $bits(v), v);
    $finish;
  end
endmodule
