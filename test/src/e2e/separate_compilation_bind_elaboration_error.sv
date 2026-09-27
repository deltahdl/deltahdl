// A precompile only parses, so a cell whose body refers to an undeclared
// identifier is compiled into the library, and the error is reported when the
// bind elaborates it; the run exits 1.
module sc_bad;
  initial undeclared_x = 1;
endmodule
