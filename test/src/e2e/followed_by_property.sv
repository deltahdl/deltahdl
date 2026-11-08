module followed_by_property;
  logic clk = 0;
  int tick = 1;
  logic req, gnt, done, rst;
  int over_pass = 0, over_fail = 0;
  int non_pass = 0, non_fail = 0;
  int win_pass = 0, win_fail = 0;
  int dual_pass = 0, dual_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign req = tick inside {1, 2, 4};
  assign gnt = tick inside {1, 4};
  assign done = tick inside {3};
  assign rst = tick inside {2};

  overlapped: assert property (@(posedge clk) req #-# gnt)
    over_pass++; else over_fail++;

  nonoverlapped: assert property (@(posedge clk) req #=# gnt)
    non_pass++; else begin
      non_fail++;
      if ($time == 40) $display("req #=# gnt fails at the end of the run");
    end

  windowed: assert property (@(posedge clk) ##[0:5] done #-# !rst)
    win_pass++; else begin
      win_fail++;
      if ($time == 40)
        $display("##[0:5] done #-# !rst fails at the end of the run");
    end

  dual: assert property (@(posedge clk) not (req |-> not gnt))
    dual_pass++; else dual_fail++;

  initial begin
    #40;
    $display("req #-# gnt passes %0d fails %0d", over_pass, over_fail);
    $display("req #=# gnt passes %0d fails %0d at ticks", non_pass, non_fail);
    $display("##[0:5] done #-# !rst passes %0d fails %0d at ticks", win_pass,
             win_fail);
    $display("not (req |-> not gnt) passes %0d fails %0d", dual_pass,
             dual_fail);
    $finish;
  end
endmodule
