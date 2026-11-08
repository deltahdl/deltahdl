module case_property;
  logic clk = 0;
  int tick = 1;
  logic [1:0] delay;
  logic [1:0] sel_x = 2'bxx;
  logic a = 1;
  logic b;
  int decode_pass = 0, decode_fail = 0;
  int linear_pass = 0, linear_fail = 0;
  int nodef_pass = 0, nodef_fail = 0;
  int nested_pass = 0, nested_fail = 0;
  int exact_pass = 0, exact_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign delay = (tick - 1) / 2;
  assign b = tick inside {2, 3, 4, 8};

  decode: assert property (@(posedge clk)
    case (delay)
      2'd0: a && b;
      2'd1: a ##1 b;
      2'd2: a ##2 b;
      default: 0;
    endcase) decode_pass++; else decode_fail++;

  linear: assert property (@(posedge clk)
    case (delay)
      default: 0;
      2'd0, 2'd1: b;
      2'd1: !b;
      2'd2, 2'd3: !b;
    endcase) linear_pass++; else linear_fail++;

  no_default: assert property (@(posedge clk)
    case (delay)
      2'd0: b;
      2'd3: !b;
    endcase) nodef_pass++; else nodef_fail++;

  nested: assert property (@(posedge clk)
    case (delay[1])
      1'b0: case (delay[0])
              1'b0: b;
              default !b;
            endcase;
      default: a;
    endcase) nested_pass++; else nested_fail++;

  exact: assert property (@(posedge clk)
    case (sel_x)
      2'b00: 0;
      2'bxx: 1;
      default: 0;
    endcase) exact_pass++; else exact_fail++;

  initial begin
    #80;
    $display("decode passes %0d fails %0d", decode_pass, decode_fail);
    $display("linear passes %0d fails %0d", linear_pass, linear_fail);
    $display("no_default passes %0d fails %0d", nodef_pass, nodef_fail);
    $display("nested passes %0d fails %0d", nested_pass, nested_fail);
    $display("exact passes %0d fails %0d", exact_pass, exact_fail);
    $finish;
  end
endmodule
