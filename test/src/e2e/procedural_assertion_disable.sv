module procedural_assertion_disable;
  logic clk = 0;
  logic a = 1, b = 1;
  int go = 0, go2 = 0;
  logic clear_b2 = 0;
  always #5 clk = ~clk;

  default clocking @(posedge clk); endclocking

  always @(go) begin : b1
    a1: assert property (const'(a)) $display("a1 passed at %0d", $time);
    else $display("a1 failed at %0d", $time);
    a2: assert property (const'(b)) $display("a2 passed at %0d", $time);
    else $display("a2 failed at %0d", $time);
    if (go == 2) disable a1;
    else begin
      #1 disable a1;
    end
  end

  always @(go2) begin : b2
    a3: assert property (const'(a)) $display("a3 passed at %0d", $time);
    else $display("a3 failed at %0d", $time);
    a4: assert property (const'(b)) $display("a4 passed at %0d", $time);
    else $display("a4 failed at %0d", $time);
  end

  always @(clear_b2) begin : b3
    disable b2;
  end

  initial begin
    #10 go = 1;
    #10 go = 2;
    #10 go2 = 1;
    clear_b2 = 1;
    #10 go2 = 2;
    #1 clear_b2 = 0;
    #9 $finish;
  end
endmodule
