// §38.19, §38.20 (printed page 1112) of IEEE 1800-2023: element or row by
// index; full selection by multi-index; out-of-range index gives NULL; declared
// ranges [2:4] honoured. The library
// vpi_acceptance_14_handle_by_index_multi_index.c, built beside the run and
// named by vpi_acceptance_14_handle_by_index_multi_index.args, is the VPI
// application under test (#4338).
module top;
  int m[2][3];
  logic [7:0] v = 8'b0010_0000;
  int arr[2:4] = '{22, 33, 44};
  initial begin
    for (int i = 0; i < 2; i++) for (int j = 0; j < 3; j++) m[i][j] = i * 10 + j;
    #1 $probe;
  end
endmodule
