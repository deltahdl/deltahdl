module named_event;
  event e;
  int i = 0;

  // Test 1: delayed trigger (should work)
  always @(e) begin
    i = i + 1;
  end
  initial begin
    #1 ->e;
    #1 $display("i = %0d", i);
  end
endmodule
