module throughout_condition;
  logic mclk = 0;
  int tick = 1;
  logic burst_mode, irdy, trdy;
  string ends = "";
  always #5 mclk = ~mclk;
  always #10 tick = tick + 1;

  assign burst_mode = tick inside {1, 9, 10, 11, 12, 13, 14, 15, 26, 27, 28};
  assign irdy = tick inside {1, 2, 12, 13, 14, 15, 16, 26, 27, 28};
  assign trdy = tick inside {1, 2, 3, 11, 12, 13, 14, 15, 16, 17, 25, 26, 27, 28};

  sequence burst_rule1;
    @(posedge mclk)
      $fell(burst_mode) ##0
      ((!burst_mode) throughout (##2 ((trdy==0)&&(irdy==0)) [*7]));
  endsequence

  initial forever begin
    wait (burst_rule1.triggered);
    ends = $sformatf("%s %0d", ends, tick);
    @(posedge mclk);
  end

  initial begin
    #290;
    $display("burst_rule1 ends at ticks%s", ends);
    $finish;
  end
endmodule
