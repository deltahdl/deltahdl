// §16.9.10 Sequence contained within another sequence: `seq1 within seq2`
// abbreviates `(1[*0:$] ##1 seq1 ##1 1[*0:$]) intersect seq2`, matching along
// an interval seq2 matches along where seq1 matches along a subinterval of
// it: seq1's match starts no earlier than seq2's and ends no later. The
// sequences below run over Figure 16-13's trace, mclk rising at 5, 15, 25,
// ... so that tick n is at 10n - 5, the tick counter counting straight
// through: irdy is high at ticks 1 and 2 and from 12, trdy at 1 to 3 and
// from 11, so $fell(irdy) ##1 !irdy[*8] matches from 3 to 11.
//
// The clause's !trdy[*7] within ($fell(irdy) ##1 !irdy[*8]) matches from 3 to
// 11, !trdy[*7] holding from 4 to 10 inside, and ends at 11; !irdy[*9]
// within the same matches from 3 to 11 as the outer does, and ends at 11;
// (irdy ##1 !irdy) within it does not match, irdy ##1 !irdy matching from 2
// to 3 alone, before the outer begins; and (!trdy ##1 trdy ##1 trdy) within
// it does not match either, the inner matching from 10 to 12 alone, after
// the outer ends.
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
