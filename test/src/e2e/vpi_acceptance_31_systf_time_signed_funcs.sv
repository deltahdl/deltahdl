module top;
  time t;
  initial begin
    t = $user_time();
    $display("time %0d", t);
    $display("signed %0d unsigned %0d", $user_s8(), $user_u8());
  end
endmodule
