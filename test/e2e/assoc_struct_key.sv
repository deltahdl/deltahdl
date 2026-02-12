module assoc_struct_key;
  typedef struct packed { logic [7:0] a; logic [7:0] b; } key_t;
  int data[key_t];

  initial begin
    key_t k1, k2;
    k1 = '{a: 8'd1, b: 8'd2};
    k2 = '{a: 8'd3, b: 8'd4};
    data[k1] = 100;
    data[k2] = 200;
    $display("%0d", data[k1]);
    $display("%0d", data[k2]);
    $display("%0d", data.size());
  end
endmodule
