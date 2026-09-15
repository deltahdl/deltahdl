// §16.12.16 Case: `case ( expression_or_dist ) property_case_item {
// property_case_item } endcase` is a multiway decision, the case expression
// compared with each item's expressions in order by §12.5's rules; the
// first item matching is the property statement evaluated and the search
// ends there, the default item ignored in the search and evaluated where
// every comparison fails, and with no default and no match none of the
// items is evaluated and the evaluation succeeds, vacuously. The
// assertions below run over eight ticks, clk rising at 5, 15, ..., 75 so
// that tick n is at 10n - 5, the tick counter counting through: delay is 0
// at ticks 1 and 2, 1 at 3 and 4, 2 at 5 and 6 and 3 at 7 and 8, a is high
// throughout, b at 2, 3, 4 and 8, and sel_x is 2'bxx throughout.
//
// decode is the clause's decoding of a variable delay, the item taking
// delay's value at the attempt's tick and its sequence running from it:
// `a && b` at 1 and 2, `a ##1 b` from 3 and 4, `a ##2 b` from 5 and 6 and
// the default, 0, at 7 and 8, so 2, 3 and 6 pass and the other five fail.
// linear has an item repeating 2'd1 that would invert the verdicts at 3
// and 4 if the search ran on past the first match, and a default written
// first that would take every tick if it were not ignored in the search:
// b holds at 2, 3 and 4 and !b at 5, 6 and 7, six passes. no_default has
// no item for delay 1 or 2 and no default, so the four attempts from 3 to
// 6 succeed vacuously beside b at 2 and !b at 7. nested selects an inner
// case by delay's high bit, the inner by its low bit: b at 1 and 2, !b at
// 3 and 4, then a. exact compares sel_x with 2'bxx by case equality, which
// an x matches, so its item holds at every tick where 2'b00 never does.
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
