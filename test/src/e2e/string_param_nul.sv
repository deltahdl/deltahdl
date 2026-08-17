// §6.16: "A string variable shall not contain the special character "\0".
// Assigning the value 0 to a string character shall be ignored." So S holds the
// two characters "ab", and §6.16.1's count of them is 2 wherever it is asked.
//
// The two displays are the point of the case. N is folded by the elaborator and
// S.len() is evaluated by the simulator, and the same expression giving two
// different numbers is the defect this case exists to catch. Printing only one
// of them would leave the other free to drift.
module string_param_nul;
  parameter string S = "a\0b";
  localparam int N = S.len();
  initial begin
    $display("%0d", N);
    $display("%0d", S.len());
    $display("%s", S);
  end
endmodule
