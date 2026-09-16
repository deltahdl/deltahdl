// §16.12.19 Local variable formal arguments in property declarations: the
// rules of §16.8.2 apply to a named property, so a formal designated local
// is a local variable of the instance, a new copy of it initialized from the
// actual when the attempt begins; its direction is input, written or
// inferred, and inout and output are illegal. The assertions below run over
// eight ticks, clk rising at 5, 15, ..., 75 so that tick n is at 10n - 5: c
// is high at 1 and 4, data is 5 at 1 and 2, 9 at 3 to 5 and 2 from 6, and
// do1 is 5 at 3, 2 at 6 and 0 elsewhere.
//
// local_input is p_local, whose lv is a local variable formal of direction
// input, and inferred is p_inferred, whose lv is the same with the direction
// left to be inferred: each attempt after c compares do1 two ticks later
// with data as it stood at c's tick, 5 from 1 and 9 from 4, so the attempt
// from 1 holds at 3 and the one from 4 fails at 6, where do1 is 2. live is
// p_live, whose v is not local, so it reads data as it stands at the
// comparison, 9 at 3 and 2 at 6: the attempt from 1 fails at 3 and the one
// from 4 holds at 6. The six attempts with c low hold at their tick.
module local_property_formals;
  logic clk = 0;
  int tick = 1;
  logic c;
  int data, do1;
  int local_pass = 0, local_fail = 0;
  int inferred_pass = 0, inferred_fail = 0;
  int live_pass = 0, live_fail = 0;
  string local_fails = "", inferred_fails = "", live_fails = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign c = tick inside {1, 4};
  assign data = (tick <= 2) ? 5 : (tick <= 5) ? 9 : 2;
  assign do1 = (tick == 3) ? 5 : (tick == 6) ? 2 : 0;

  property p_local(local input int lv);
    @(posedge clk) c |-> ##2 (do1 == lv);
  endproperty

  property p_inferred(local int lv);
    @(posedge clk) c |-> ##2 (do1 == lv);
  endproperty

  property p_live(int v);
    @(posedge clk) c |-> ##2 (do1 == v);
  endproperty

  local_input: assert property (p_local(data))
    local_pass++;
    else begin
      local_fail++;
      local_fails = $sformatf("%s %0d", local_fails, $time);
    end

  inferred: assert property (p_inferred(data))
    inferred_pass++;
    else begin
      inferred_fail++;
      inferred_fails = $sformatf("%s %0d", inferred_fails, $time);
    end

  live: assert property (p_live(data))
    live_pass++;
    else begin
      live_fail++;
      live_fails = $sformatf("%s %0d", live_fails, $time);
    end

  initial begin
    #80;
    $display("p_local(data), lv local input, passes %0d fails %0d at%s",
             local_pass, local_fail, local_fails);
    $display("p_inferred(data), lv local, passes %0d fails %0d at%s",
             inferred_pass, inferred_fail, inferred_fails);
    $display("p_live(data), v not local, passes %0d fails %0d at%s",
             live_pass, live_fail, live_fails);
    $finish;
  end
endmodule
