module expect_statement;
  logic clk = 0;
  logic a = 0, b = 0, c = 0;
  int data = 0;
  always #5 clk = ~clk;
  always @(posedge clk) data <= data + 1;

  task automatic wait_for(integer value, output bit success);
    expect (@(posedge clk) ##[1:10] data == value) success = 1;
      else success = 0;
  endtask

  initial begin
    bit ok;
    #20;
    expect (@(posedge clk) a ##1 b ##1 c)
      $display("a ##1 b ##1 c matched at %0d", $time);
      else $display("a ##1 b ##1 c failed at %0d", $time);
    $display("ABC at %0d", $time);
    expect (@(posedge clk) a ##1 b ##1 c)
      $display("a ##1 b ##1 c matched at %0d", $time);
      else $display("a ##1 b ##1 c failed at %0d", $time);
    expect (@(posedge clk) c);
    wait_for(9, ok);
    $display("wait_for 9: ok=%0d at %0d", ok, $time);
    wait_for(30, ok);
    $display("wait_for 30: ok=%0d at %0d", ok, $time);
    $finish;
  end

  initial begin
    #22 a = 1;
    #10 b = 1;
    #10 c = 1;
    #5 a = 0;
    #10 c = 0;
  end
endmodule
