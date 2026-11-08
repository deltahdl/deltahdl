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
