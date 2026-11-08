module nested_generate_block_net;
  generate
    if (1) begin : b
      logic w;

      if (1) begin : a
        initial w = 1'b1;
      end

      initial begin
        #1;
        $display("%0d", w);
      end
    end
  endgenerate
endmodule
