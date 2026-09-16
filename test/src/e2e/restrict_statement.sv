// §16.14.4 Restrict statement: a restrict property statement constrains
// the state space for formal verification and has the semantics of assume
// property there, but in contrast to that statement it is not verified in
// simulation and has no action block, so a test case in which its property
// does not hold is not an error. clk rises at 5, 15, 25, 35 and 45. The
// clause's ALU adds when the control bit ctr is 0 and subtracts when it is
// 1, and the clause's restriction, restrict property (@(posedge clk) ctr
// == '0), constrains a formal proof to the addition; ctr is high across
// the ticks of 25 and 35, so the ALU subtracts at those two ticks and adds
// at the other three, and the restriction reports nothing, neither at
// those ticks nor at the end of the run, whatever its form: the clause's,
// the instance of the named property addition and the temporal property
// ctr |=> !ctr, which the tick of 35 would fail. assumed assumes the same
// property as the clause's restriction with no action block, so the tool
// calls $error at 25 and 35, which is the difference between the two
// statements in simulation.
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
