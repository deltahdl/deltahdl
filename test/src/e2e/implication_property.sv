module implication_property;
  logic clk = 0;
  int tick = 1;
  logic req, gnt, ack, done, late;
  int over_pass = 0, over_fail = 0;
  int non_pass = 0, non_fail = 0;
  int every_pass = 0, every_fail = 0;
  int one_pass = 0, one_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign req = tick inside {1, 2, 4};
  assign gnt = tick inside {1, 4};
  assign ack = tick inside {2, 3};
  assign done = tick inside {2, 3};
  assign late = tick inside {2};

  overlapped: assert property (@(posedge clk) req |-> gnt)
    over_pass++; else over_fail++;

  nonoverlapped: assert property (@(posedge clk) req |=> gnt)
    begin
      non_pass++;
      if ($time == 40) $display("req |=> gnt passes at the end of the run");
    end else non_fail++;

  every_match: assert property (@(posedge clk) (req ##[1:2] ack) |-> done)
    begin
      every_pass++;
      if ($time == 40)
        $display("(req ##[1:2] ack) |-> done passes at the end of the run");
    end else every_fail++;

  one_fails: assert property (@(posedge clk) (req ##[1:2] ack) |-> late)
    begin
      one_pass++;
      if ($time == 40)
        $display("(req ##[1:2] ack) |-> late passes at the end of the run");
    end else one_fail++;

  initial begin
    #40;
    $display("req |-> gnt passes %0d fails %0d", over_pass, over_fail);
    $display("req |=> gnt passes %0d fails %0d at ticks", non_pass, non_fail);
    $display("(req ##[1:2] ack) |-> done passes %0d fails %0d at ticks",
             every_pass, every_fail);
    $display("(req ##[1:2] ack) |-> late passes %0d fails %0d at ticks",
             one_pass, one_fail);
    $finish;
  end
endmodule
