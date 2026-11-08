module top;
  class C; int val = 4; endclass
  C c = new;
  initial begin
    #1 $probe;
    $display("sv val=%0d", c.val);
  end
endmodule
