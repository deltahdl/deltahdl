module within_sequence;
  logic mclk = 0;
  int tick = 1;
  logic irdy, trdy;
  string inside_ends = "";
  string coincident_ends = "";
  string early_ends = "";
  string late_ends = "";
  always #5 mclk = ~mclk;
  always #10 tick = tick + 1;

  assign irdy = tick inside {1, 2, 12, 13, 14};
  assign trdy = tick inside {1, 2, 3, 11, 12, 13, 14};

  sequence trdy_low_inside;
    @(posedge mclk) !trdy[*7] within ($fell(irdy) ##1 !irdy[*8]);
  endsequence

  sequence irdy_low_coincident;
    @(posedge mclk) !irdy[*9] within ($fell(irdy) ##1 !irdy[*8]);
  endsequence

  sequence irdy_fall_early;
    @(posedge mclk) (irdy ##1 !irdy) within ($fell(irdy) ##1 !irdy[*8]);
  endsequence

  sequence trdy_rise_late;
    @(posedge mclk)
      (!trdy ##1 trdy ##1 trdy) within ($fell(irdy) ##1 !irdy[*8]);
  endsequence

  initial forever begin
    wait (trdy_low_inside.triggered);
    inside_ends = $sformatf("%s %0d", inside_ends, tick);
    @(posedge mclk);
  end
  initial forever begin
    wait (irdy_low_coincident.triggered);
    coincident_ends = $sformatf("%s %0d", coincident_ends, tick);
    @(posedge mclk);
  end
  initial forever begin
    wait (irdy_fall_early.triggered);
    early_ends = $sformatf("%s %0d", early_ends, tick);
    @(posedge mclk);
  end
  initial forever begin
    wait (trdy_rise_late.triggered);
    late_ends = $sformatf("%s %0d", late_ends, tick);
    @(posedge mclk);
  end

  initial begin
    #150;
    $display("!trdy[*7] within ($fell(irdy) ##1 !irdy[*8]) ends at ticks%s",
             inside_ends);
    $display("!irdy[*9] within ($fell(irdy) ##1 !irdy[*8]) ends at ticks%s",
             coincident_ends);
    $display("(irdy ##1 !irdy) within ($fell(irdy) ##1 !irdy[*8]) ends at ticks%s",
             early_ends);
    $display("(!trdy ##1 trdy ##1 trdy) within ($fell(irdy) ##1 !irdy[*8]) ends at ticks%s",
             late_ends);
    $finish;
  end
endmodule
