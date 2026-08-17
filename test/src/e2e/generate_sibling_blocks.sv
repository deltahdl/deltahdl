// IEEE 1800-2023 §27.4: a named loop generate block "is a declaration of an
// array of generate block instances", and "the index values in this array are
// the values assumed by the genvar during elaboration". Two sibling blocks
// written over one genvar are therefore two distinct arrays. §27.4 also rules
// that a generate block, "like all generate blocks, comprises a separate scope
// and a new level of hierarchy when it is instantiated", so the v declared in
// blk_a is a different object from the v declared in blk_b. A name built from
// the genvar rather than the block gives both of them one name, and whichever
// block is elaborated second wins every read.
//
// Reusing one genvar across the two loops is what makes that collision
// reachable, and it is legal: §27.4 rules only that "it is not possible to have
// two nested loop generate constructs that use the same genvar", and these are
// siblings. The standard's own mod_c example writes two sibling loops over i,
// and the error it marks there is the repeated block name a, not the genvar.
//
// The genvar runs 4 to 5 rather than 0 to 1 so that its value is never the
// ordinal of the instance the iteration creates, which are 0 and 1. A name
// built from the ordinal instead of the index would read correctly for a loop
// starting at zero and prove nothing.
module generate_sibling_blocks;
  logic [7:0] out [0:3];

  genvar i;

  generate
    for (i = 4; i < 6; i = i + 1) begin : blk_a
      logic [7:0] v;
      initial begin
        v = 10 + i;
        #1 out[i - 4] = v;
      end
    end

    for (i = 4; i < 6; i = i + 1) begin : blk_b
      logic [7:0] v;
      initial begin
        v = 20 + i;
        #1 out[i - 2] = v;
      end
    end
  endgenerate

  // Every block writes its own v at time 0 and copies it out at time 1, so the
  // four writes are complete before any of them is read back. Reading at time
  // 2 keeps the printed line independent of the order the four processes run
  // in, which nothing here fixes.
  initial begin
    #2;
    $display("%0d %0d %0d %0d", out[0], out[1], out[2], out[3]);
  end
endmodule
