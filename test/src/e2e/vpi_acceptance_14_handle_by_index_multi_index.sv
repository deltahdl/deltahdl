module top;
  int m[2][3];
  logic [7:0] v = 8'b0010_0000;
  int arr[2:4] = '{22, 33, 44};
  initial begin
    for (int i = 0; i < 2; i++) for (int j = 0; j < 3; j++) m[i][j] = i * 10 + j;
    #1 $probe;
  end
endmodule
