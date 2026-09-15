// §16.9.9 Conditions over sequences: `exp throughout seq` abbreviates
// `(exp)[*0:$] intersect seq`, matching along an interval of consecutive
// ticks where seq matches along it and exp is true at each of its ticks. The
// clause's burst_rule1 is run below through Figure 16-12 and then Figure
// 16-13, mclk rising at 5, 15, 25, ... so that tick n is at 10n - 5, the tick
// counter counting straight through, each figure a round of fourteen ticks.
//
// In both rounds burst_mode is high at tick 1 of the round and falls at 2,
// irdy is high at 1 and 2 and from 12, and trdy at 1 to 3 and from 11, so
// (trdy==0) && (irdy==0) holds at 4 to 10, the seven ticks the sequence
// needs from two ticks after the fall. The evaluation attempt from tick 2
// needs burst_mode low from 2 through 10: in round one burst_mode is high
// again from 9, so the attempt fails there and the sequence never ends; in
// round two, ticks 15 to 28, burst_mode stays low through 11 of the round,
// so the sequence ends at 10 of the round, tick 24.
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
