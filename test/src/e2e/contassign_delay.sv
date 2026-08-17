// IEEE 1800-2023 §10.3.3: "A delay given to a continuous assignment shall
// specify the time duration between a right-hand operand value change and the
// assignment made to the left-hand side". §28.16 measures the same interval for
// a net delay, "from any driver on the net changing value to the time when the
// net value is updated and propagated further".
//
// Both operands of the right-hand side change in one time step here, at t=9,
// and the single delay of 6 still separates that change from the update to y.
// §10.3.2 evaluates the whole right-hand side whenever an operand changes, so
// the value that arrives is 8'h3C & 8'h7A whichever operand is reacted to.
module contassign_delay;
  logic [7:0] a;
  logic [7:0] b;
  wire [7:0] y;

  assign #6 y = a & b;

  initial begin
    a = 8'hF0;
    b = 8'hCC;
    #9;
    a = 8'h3C;
    b = 8'h7A;

    // §4.7 leaves the order of active events within one region free, so neither
    // read stands at the change instant (t=9) or at the expiry instant (t=15).
    // t=11 is strictly inside the delay, t=18 strictly after it, and no other
    // event of this design stands at either time.
    #2;
    $display("held y=%h", y);
    #7;
    $display("propagated y=%h", y);
  end
endmodule
