module abort_property;
  logic clk = 0;
  int tick = 1;
  logic go, get, put, stop, flag, both, nv;
  logic stop_async = 0;
  int sync_pass = 0, sync_fail = 0;
  int async_pass = 0, async_fail = 0;
  int sa_pass = 0, sa_fail = 0;
  int accept_pass = 0, accept_fail = 0;
  int nested_pass = 0, nested_fail = 0;
  int not_pass = 0, not_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign go = tick inside {1};
  assign get = tick inside {2, 3};
  assign put = tick inside {4, 6};
  assign stop = tick inside {5};
  assign flag = tick inside {2};
  assign both = tick inside {3};
  assign nv = 0;

  initial begin
    #47 stop_async = 1;
    #2 stop_async = 0;
  end

  sync_stop: assert property
    (@(posedge clk) go ##1 get[*2] |-> sync_reject_on(stop) put[->2])
    sync_pass++; else sync_fail++;

  async_stop: assert property
    (@(posedge clk) go ##1 get[*2] |-> reject_on(stop_async) put[->2])
    async_pass++; else async_fail++;

  sync_async: assert property
    (@(posedge clk) go ##1 get[*2] |-> sync_reject_on(stop_async) put[->2])
    sa_pass++; else sa_fail++;

  accepts: assert property (@(posedge clk) sync_accept_on(flag) nv)
    accept_pass++; else accept_fail++;

  nested: assert property
    (@(posedge clk) sync_accept_on(both) sync_reject_on(both) nv)
    nested_pass++; else nested_fail++;

  negated: assert property (@(posedge clk) not (sync_accept_on(flag) nv))
    not_pass++; else not_fail++;

  initial begin
    #80;
    $display("sync_reject_on(stop) passes %0d fails %0d", sync_pass,
             sync_fail);
    $display("reject_on(stop_async) passes %0d fails %0d", async_pass,
             async_fail);
    $display("sync_reject_on(stop_async) passes %0d fails %0d", sa_pass,
             sa_fail);
    $display("sync_accept_on(flag) nv passes %0d fails %0d", accept_pass,
             accept_fail);
    $display("sync_accept_on(both) sync_reject_on(both) nv passes %0d fails %0d",
             nested_pass, nested_fail);
    $display("not (sync_accept_on(flag) nv) passes %0d fails %0d", not_pass,
             not_fail);
    $finish;
  end
endmodule
