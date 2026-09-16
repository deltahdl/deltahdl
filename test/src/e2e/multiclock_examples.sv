// §16.13.4 Examples of multiclock specifications: the clause's s1 and s2,
// unclocked sequences, its mult_s, a sequence over three clocks that
// instantiates them under two of them, and the properties it builds from
// them: mult_p1, the multiclock sequence as a property; mult_p2, the named
// multiclock sequence as a property; mult_p3, the multiclock implication
// whose consequent is on the third clock; mult_p6, the implication whose
// antecedent and consequent are the named multiclock sequence; mult_p7,
// the overlapped implication with clock flow, a, b and c on clk; and
// mult_p8, if-else with clock flow, a, b, c, e and the constant 1 on clk.
// clk rises at 5, 15, ..., 75 so that tick n of it is at 10n - 5, the tick
// counter counting through; clk1 rises at 12, 27, 45, 57 and 72, reading
// the counter as 2, 3, 5, 6 and 8, and clk2 at 8, 25, 38, 55, 70 and 78,
// reading 1, 3, 4, 6, 7 and 8. a is high at 1 and 2, b at 3 and 5, c at 3,
// 4 and 6, d at 6 and 7, e at 3 and f at 4.
//
// mult_s from 5 reads a at 5, then on clk1 a at 12 and b at 27, then on
// clk2 c at 38 and d at 55, where it matches; from 15 it reads a at 27 and
// fails; and from every later tick of clk it fails at a. mult_p1 and
// mult_p2 are that sequence as a property, and read the same. mult_p3's
// antecedent, a then s1 on clk1, matches at 27 from 5, and s2 on clk2 is
// read at 38 and 55, where it holds; the antecedent from 15 fails at 27
// and the six others at their tick, so every attempt holds. mult_p6's
// antecedent matches at 55 from 5, and the consequent, mult_s again, begins
// at the tick of clk after, 65, where a is low, so it fails; the seven
// others hold. mult_p7's antecedent matches at 25 from 15, c is read
// there, on clk, and d at 27, on clk1, where it is low, so it fails; the
// seven others hold. mult_p8 reads c at 25, high, and its then-branch
// reads d at 27, on clk1, where it is low, so it fails as mult_p7 does.
module multiclock_examples;
  logic clk = 0;
  logic clk1 = 0;
  logic clk2 = 0;
  int tick = 1;
  logic a, b, c, d, e, f;
  int s_pass = 0, s_fail = 0;
  int p1_pass = 0, p1_fail = 0;
  int p2_pass = 0, p2_fail = 0;
  int p3_pass = 0, p3_fail = 0;
  int p6_pass = 0, p6_fail = 0;
  int p7_pass = 0, p7_fail = 0;
  int p8_pass = 0, p8_fail = 0;
  string s_at = "", p1_at = "", p2_at = "", p3_at = "", p6_at = "", p7_at = "",
         p8_at = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;
  initial begin
    #12 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #10 clk1 = 1;
    #5 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #6 clk1 = 0;
  end
  initial begin
    #8 clk2 = 1;
    #8 clk2 = 0;
    #9 clk2 = 1;
    #7 clk2 = 0;
    #6 clk2 = 1;
    #8 clk2 = 0;
    #9 clk2 = 1;
    #7 clk2 = 0;
    #8 clk2 = 1;
    #4 clk2 = 0;
    #4 clk2 = 1;
    #1 clk2 = 0;
  end

  assign a = tick inside {1, 2};
  assign b = tick inside {3, 5};
  assign c = tick inside {3, 4, 6};
  assign d = tick inside {6, 7};
  assign e = tick inside {3};
  assign f = tick inside {4};

  sequence s1;
    a ##1 b; // unclocked sequence
  endsequence
  sequence s2;
    c ##1 d; // unclocked sequence
  endsequence

  sequence mult_s;
    @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;
  endsequence

  property mult_p1;
    @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;
  endproperty

  property mult_p2;
    mult_s;
  endproperty

  property mult_p3;
    @(posedge clk) a ##1 @(posedge clk1) s1 |=> @(posedge clk2) s2;
  endproperty

  property mult_p6;
    mult_s |=> mult_s;
  endproperty

  property mult_p7;
    @(posedge clk) a ##1 b |-> c ##1 @(posedge clk1) d;
  endproperty

  property mult_p8;
    @(posedge clk) a ##1 b |->
      if (c)
        (1 |=> @(posedge clk1) d)
      else
        e ##1 @(posedge clk2) f ;
  endproperty

  as_s: assert property (mult_s)
    s_pass++;
    else begin
      s_fail++;
      s_at = $sformatf("%s %0d", s_at, $time);
    end

  as_p1: assert property (mult_p1)
    p1_pass++;
    else begin
      p1_fail++;
      p1_at = $sformatf("%s %0d", p1_at, $time);
    end

  as_p2: assert property (mult_p2)
    p2_pass++;
    else begin
      p2_fail++;
      p2_at = $sformatf("%s %0d", p2_at, $time);
    end

  as_p3: assert property (mult_p3)
    p3_pass++;
    else begin
      p3_fail++;
      p3_at = $sformatf("%s %0d", p3_at, $time);
    end

  as_p6: assert property (mult_p6)
    p6_pass++;
    else begin
      p6_fail++;
      p6_at = $sformatf("%s %0d", p6_at, $time);
    end

  as_p7: assert property (mult_p7)
    p7_pass++;
    else begin
      p7_fail++;
      p7_at = $sformatf("%s %0d", p7_at, $time);
    end

  as_p8: assert property (mult_p8)
    p8_pass++;
    else begin
      p8_fail++;
      p8_at = $sformatf("%s %0d", p8_at, $time);
    end

  initial begin
    #80;
    $display("mult_s passes %0d fails %0d at%s", s_pass, s_fail, s_at);
    $display("mult_p1 passes %0d fails %0d at%s", p1_pass, p1_fail, p1_at);
    $display("mult_p2 passes %0d fails %0d at%s", p2_pass, p2_fail, p2_at);
    $display("mult_p3 passes %0d fails %0d at%s", p3_pass, p3_fail, p3_at);
    $display("mult_p6 passes %0d fails %0d at%s", p6_pass, p6_fail, p6_at);
    $display("mult_p7 passes %0d fails %0d at%s", p7_pass, p7_fail, p7_at);
    $display("mult_p8 passes %0d fails %0d at%s", p8_pass, p8_fail, p8_at);
    $finish;
  end
endmodule
