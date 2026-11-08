module shortreal_display;
  shortreal s;
  initial begin
    s = 3.4e38;
    $display("%g", s);
  end
endmodule
