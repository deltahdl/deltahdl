module assoc_arg;
  int tab[int];

  function automatic int read_sum(int aa[int]);
    return aa[1] + aa[2] + aa[3];
  endfunction

  initial begin
    tab[1] = 10;
    tab[2] = 20;
    tab[3] = 30;
    $display("%0d", read_sum(tab));
    // Verify original is unmodified (by-value copy).
    $display("%0d", tab[1]);
  end
endmodule
