module assoc_event;
  int tab[int] = '{1: 0};

  always @(tab[1]) $display("%0d", tab[1]);

  initial begin
    #1 tab[1] = 5;
    #1 tab[1] = 9;
    #1 $finish;
  end
endmodule
