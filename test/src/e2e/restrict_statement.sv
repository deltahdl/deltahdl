module restrict_statement;
  logic clk = 0;
  logic ctr = 0;
  logic [7:0] a = 8'd12, b = 8'd5, y = 8'd0;
  int adds = 0, subs = 0;
  always #5 clk = ~clk;

  always @(posedge clk) begin
    y = ctr ? a - b : a + b;
    if (ctr) subs++;
    else adds++;
    $display("ctr %0d at %0d: y = %0d", ctr, $time, y);
  end

  property addition;
    @(posedge clk) ctr == '0;
  endproperty

  restrict property (@(posedge clk) ctr == '0);
  named_restriction: restrict property (addition);
  temporal_restriction: restrict property (@(posedge clk) ctr |=> !ctr);
  assumed: assume property (@(posedge clk) ctr == '0);

  initial begin
    #20 ctr = 1;
    #20 ctr = 0;
    #10 $display("adds %0d subs %0d", adds, subs);
    $finish;
  end
endmodule
