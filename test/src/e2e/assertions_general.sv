module assertions_general;
  logic clk = 1'b0;
  logic en = 1'b1;
  logic req = 1'b0;
  logic ack = 1'b0;
  int passes = 0;
  int fails = 0;

  always #5 clk = ~clk;

  always_ff @(posedge clk) ack <= req;

  sequence req_then_ack;
    @(posedge clk) req ##1 ack;
  endsequence

  property req_only_when_enabled;
    @(posedge clk) !req || en;
  endproperty

  assert property (req_only_when_enabled)
    passes = passes + 1;
  else begin
    fails = fails + 1;
    $display("concurrent: req while disabled at %0d", $time);
  end

  initial begin
    wait (req_then_ack.triggered);
    $display("sequence: req then ack matched at %0d", $time);
  end

  initial begin
    #10 req = 1'b1;
    #10 req = 1'b0;
    #10 en = 1'b0;
    req = 1'b1;
    #10 req = 1'b0;
    #6;
    assert (passes == 4) $display("immediate: %0d ticks held", passes);
    else $display("immediate: %0d ticks held, expected 4", passes);
    assert (fails == 0) $display("immediate: no tick failed");
    else $display("immediate: %0d tick failed", fails);
    $finish;
  end
endmodule
