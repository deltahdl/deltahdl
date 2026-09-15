// §16.10 Local variables: a named sequence declares local variables with an
// explicit data type, a new copy of each created at the beginning of every
// evaluation attempt and its initialization assignment performed then, in
// declaration order, one's expression reading the locals declared before it
// as assigned; a local is assigned at the end point of a subsequence by a
// match item written after it in parentheses, the items performed in order
// at each nonempty match, may be reassigned later, accumulates when its
// assignment is attached to a repeated operand or counts with an
// increment, and, passed as an entire actual argument to an untyped formal
// of a named sequence, is bound to the formal, an assignment to which is
// read in the instantiating context after the instance matches. The clause's
// sequences run below, clk rising at 5, 15, 25, ... so that tick n is at
// 10n - 5, the tick counter counting straight through, and each process
// records the ticks its sequence reaches an end point at.
//
// data_check captures data_in where a falls and compares data_out with it
// where b next holds: a is high at tick 1, data_in is 7 at 2, b is high at 5
// with data_out 7, so it ends at 5; a is high at 11, data_in is 3 at 12 and
// b is high at 15 with data_out 4, so it does not end there; and a is high at
// 62, data_in is 9 at 63 and b is high at 64 with data_out 9, so it ends at
// 64. rep_v sums data over four matches of r: r is high at 21, 23, 25 and 27
// with data 1, 2, 3 and 4, rb at 28 and rc at 29 with r_out 10, so it ends at
// 29. count_a_cycles counts the ticks p stays high from its rise against
// MAX, 3: p is high from 31 to 33 and low at 34, so it ends at 34 with x 3;
// p is high from 41 to 45, so x reaches 5 and it does not end. init_order
// initializes v from data_in and w from v: a is high at 51 with data_in 4,
// and data_out is 5 at 52, so it ends at 52. seq2 hands its v1 to
// sub_seq2's untyped formal lv, which is assigned data_in where a falls: c
// is high at 61, and do1 is 9 at 65, where seq2 reads v1 as assigned, so it
// ends at 65.
module local_variables;
  localparam int MAX = 3;
  logic clk = 0;
  int tick = 1;
  logic a, b, c, r, rb, rc, p;
  int data_in, data_out, do1, data, r_out;
  string check_ends = "";
  string rep_ends = "";
  string count_ends = "";
  string init_ends = "";
  string seq2_ends = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 11, 51, 62};
  assign b = tick inside {5, 15, 64};
  assign c = tick inside {61};
  assign r = tick inside {21, 23, 25, 27};
  assign rb = tick inside {28};
  assign rc = tick inside {29};
  assign p = tick inside {31, 32, 33, 41, 42, 43, 44, 45};
  always_comb case (tick)
    2: data_in = 7;
    12: data_in = 3;
    51: data_in = 4;
    63: data_in = 9;
    default: data_in = 0;
  endcase
  always_comb case (tick)
    5: data_out = 7;
    15: data_out = 4;
    52: data_out = 5;
    64: data_out = 9;
    default: data_out = 0;
  endcase
  always_comb case (tick)
    21: data = 1;
    23: data = 2;
    25: data = 3;
    27: data = 4;
    default: data = 0;
  endcase
  assign r_out = tick == 29 ? 10 : 0;
  assign do1 = tick == 65 ? 9 : 0;

  sequence data_check;
    int x;
    @(posedge clk) a ##1 (!a, x = data_in) ##1 !b[*0:$] ##1 b && (data_out == x);
  endsequence

  sequence rep_v;
    int x = 0;
    @(posedge clk) (r[->1], x += data)[*4] ##1 rb ##1 rc && (r_out == x);
  endsequence

  sequence count_a_cycles;
    int x;
    @(posedge clk) ($rose(p), x = 1) ##1 (p, x++)[*0:$] ##1 !p && (x <= MAX);
  endsequence

  sequence init_order;
    int u, v = data_in, w = v + 1;
    @(posedge clk) a ##1 (data_out == w);
  endsequence

  sequence sub_seq2(lv);
    (a ##1 !a, lv = data_in) ##1 !b[*0:$] ##1 b && (data_out == lv);
  endsequence

  sequence seq2;
    int v1;
    @(posedge clk) c ##1 sub_seq2(v1) ##1 (do1 == v1);
  endsequence

  initial forever begin
    wait (data_check.triggered);
    check_ends = $sformatf("%s %0d", check_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (rep_v.triggered);
    rep_ends = $sformatf("%s %0d", rep_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (count_a_cycles.triggered);
    count_ends = $sformatf("%s %0d", count_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (init_order.triggered);
    init_ends = $sformatf("%s %0d", init_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (seq2.triggered);
    seq2_ends = $sformatf("%s %0d", seq2_ends, tick);
    @(posedge clk);
  end

  initial begin
    #700;
    $display("data_check ends at ticks%s", check_ends);
    $display("rep_v ends at ticks%s", rep_ends);
    $display("count_a_cycles ends at ticks%s", count_ends);
    $display("init_order ends at ticks%s", init_ends);
    $display("seq2 ends at ticks%s", seq2_ends);
    $finish;
  end
endmodule
