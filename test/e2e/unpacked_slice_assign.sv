module unpacked_slice_assign;
  bit arr_a [7:0];
  bit arr_b [7:0];

  initial begin
    arr_a = '{1, 1, 1, 1, 1, 1, 1, 1};
    arr_b = '{0, 0, 0, 0, 0, 0, 0, 0};
    arr_b[5:3] = arr_a[2:0];
    $display("%0b%0b%0b%0b_%0b%0b%0b%0b",
      arr_b[7], arr_b[6], arr_b[5], arr_b[4],
      arr_b[3], arr_b[2], arr_b[1], arr_b[0]);
  end
endmodule
