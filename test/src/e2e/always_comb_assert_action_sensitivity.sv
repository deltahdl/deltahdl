module always_comb_assert_action_sensitivity;
  logic en = 1'b1;
  logic [7:0] a = 8'd10;
  logic [7:0] y;

  always_comb begin
    y = 8'd99;
    assert (en) y = a + 8'd3;
  end

  initial begin
    #10;
    $display("y after a = 10 is %0d", y);
    a = 8'd20;
    #10;
    $display("y after a = 20 is %0d", y);
    $finish;
  end
endmodule
