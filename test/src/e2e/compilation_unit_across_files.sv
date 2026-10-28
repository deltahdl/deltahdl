// §3.12.1 (printed page 56): without --compilation-unit-per-file every file on
// the command line is one compilation unit, and what an earlier file declares
// is visible in the files after it by the normal rules. later.sv's module
// reads this file's compilation-unit variable g, calls its function f and
// sizes v by its parameter W, so it prints 5, 3 and 8.
int g = 5;
function int f();
  return 3;
endfunction
localparam int W = 8;
