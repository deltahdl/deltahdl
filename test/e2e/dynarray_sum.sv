module dynarray_sum;
  byte b[] = '{1, 2, 3, 4};
  int y;

  initial begin
    y = b.sum;
    $display("%0d", y);
  end
endmodule
