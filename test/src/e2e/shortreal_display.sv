// A shortreal is a C float (1800-2023 6.12), so 3.4e38 is stored as the
// nearest single-precision value and %g prints it to six significant digits.
// Reading those 32 bits back as a double instead gives a subnormal near 1e-314,
// a magnitude this line cannot print for any correct shortreal.
module shortreal_display;
  shortreal s;
  initial begin
    s = 3.4e38;
    $display("%g", s);
  end
endmodule
