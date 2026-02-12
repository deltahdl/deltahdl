module top;
  string map[byte];
  byte ix;
  int rc;

  initial begin
    map[42] = "hello";
    rc = map.first(ix);
    $display("%0d", rc);
    $display("%0d", ix);
  end
endmodule
