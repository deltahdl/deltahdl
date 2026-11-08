primitive udp_inv (y, a);
  output y;
  input a;
  table
       0 : 1 ;
       1 : 0 ;
  endtable
endprimitive

module udp_generate;
  logic [2:1] d;
  wire [2:1] y;

  genvar bit_pos;

  generate
    for (bit_pos = 1; bit_pos < 3; bit_pos = bit_pos + 1) begin : inv_bit
      udp_inv g (y[bit_pos], d[bit_pos]);
    end
  endgenerate

  initial begin
    d = 2'b10;
    #1;
    $display("d=10 y=%b", y);

    d = 2'b01;
    #1;
    $display("d=01 y=%b", y);
  end
endmodule
