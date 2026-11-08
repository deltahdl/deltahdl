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
