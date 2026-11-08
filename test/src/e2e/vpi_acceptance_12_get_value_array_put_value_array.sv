module top;
  int arr[4] = '{1, 2, 3, 4};
  initial begin
    #1 $probe;
    $display("sv %0d %0d %0d %0d", arr[0], arr[1], arr[2], arr[3]);
  end
endmodule
