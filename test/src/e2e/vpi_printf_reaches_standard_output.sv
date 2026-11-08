module t;
  initial begin
    $display("disp 0");
    #1 $probe;
    $display("disp 1");
  end
endmodule
