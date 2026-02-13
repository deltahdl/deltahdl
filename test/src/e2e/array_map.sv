module array_map;
  int arr[4] = '{1, 2, 3, 4};
  int result[$];
  initial begin
    result = arr.map() with (item * 2);
    $display("%0d %0d %0d %0d", result[0], result[1], result[2], result[3]);
  end
endmodule
