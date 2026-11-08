module until_property;
  logic clk = 0;
  int tick = 1;
  logic a, b, c;
  int weak_pass = 0, weak_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int with_a_pass = 0, with_a_fail = 0;
  int with_c_pass = 0, with_c_fail = 0;
  int swith_pass = 0, swith_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 2, 4};
  assign b = tick inside {3};
  assign c = tick inside {1, 2, 3, 4};

  weak_until: assert property (@(posedge clk) a until b)
    begin
      weak_pass++;
      if ($time == 40) $display("a until b passes at the end of the run");
    end else weak_fail++;

  strong_until: assert property (@(posedge clk) a s_until b)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("a s_until b fails at the end of the run");
    end

  with_a: assert property (@(posedge clk) a until_with b)
    begin
      with_a_pass++;
      if ($time == 40) $display("a until_with b passes at the end of the run");
    end else with_a_fail++;

  with_c: assert property (@(posedge clk) c until_with b)
    begin
      with_c_pass++;
      if ($time == 40) $display("c until_with b passes at the end of the run");
    end else with_c_fail++;

  strong_with: assert property (@(posedge clk) c s_until_with b)
    swith_pass++; else begin
      swith_fail++;
      if ($time == 40)
        $display("c s_until_with b fails at the end of the run");
    end

  initial begin
    #40;
    $display("a until b passes %0d fails %0d at ticks", weak_pass, weak_fail);
    $display("a s_until b passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("a until_with b passes %0d fails %0d at ticks", with_a_pass,
             with_a_fail);
    $display("c until_with b passes %0d fails %0d at ticks", with_c_pass,
             with_c_fail);
    $display("c s_until_with b passes %0d fails %0d at ticks", swith_pass,
             swith_fail);
    $finish;
  end
endmodule
