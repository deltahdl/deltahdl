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

  initial begin
    #2;
    $display("%0d %0d %0d %0d", out[0], out[1], out[2], out[3]);
  end
endmodule
