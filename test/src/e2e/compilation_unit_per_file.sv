// §3.12.1 (printed page 56): with --compilation-unit-per-file each file is a
// compilation unit of its own. The macro this file defines does not reach
// second.sv, so child's seen is 0; this file's t is 4 bits wide and
// second.sv's t is 8, each module reading its own unit's; and split_head.sv
// ends inside module split, so its unit extends through split_tail.sv, whose
// endmodule completes it, and its k is read through the instance.
`define W 8
typedef logic [3:0] t;
module top;
  localparam int AW = $bits(t);
  child c();
  split s();
  initial begin
    $display("%0d %0d %0d %0d", AW, c.bw, c.seen, s.k);
    $finish;
  end
endmodule
