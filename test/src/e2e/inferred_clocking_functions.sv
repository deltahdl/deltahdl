module inferred_clocking_functions;
  logic a = 1, b = 1, c = 0, d = 0, rst1 = 0, clk1 = 0, clk2 = 0;
  logic rst = 0;
  int rst_seen = 0;
  always #5 clk1 = ~clk1;
  initial begin
    #3;
    forever #10 clk2 = ~clk2;
  end

  default clocking @(negedge clk1); endclocking
  default disable iff rst1;

  property p_triggers(start_event, end_event, form, clk = $inferred_clock,
                      rst = $inferred_disable);
    @clk disable iff (rst) (start_event ##0 end_event[->1]) |=> form;
  endproperty

  a1: assert property (p_triggers(a, b, c))
    $display("a1 passed at %0d", $time);
  else $display("a1 failed at %0d", $time);
  a1_explicit: assert property (@(negedge clk1) disable iff (rst1)
                                (a ##0 b[->1]) |=> c)
    $display("a1_explicit passed at %0d", $time);
  else $display("a1_explicit failed at %0d", $time);

  a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0))
    $display("a2 passed at %0d", $time);
  else $display("a2 failed at %0d", $time);
  a2_explicit: assert property (@(posedge clk1) disable iff (1'b0)
                                (a ##0 b[->1]) |=> c)
    $display("a2_explicit passed at %0d", $time);
  else $display("a2_explicit failed at %0d", $time);

  always @(posedge clk2 or posedge rst) begin
    if (rst) rst_seen++;
    else begin
      a3: assert property (p_triggers(a, b, c))
        $display("a3 passed at %0d", $time);
      else $display("a3 failed at %0d", $time);
      a3_explicit: assert property (@(posedge clk2) disable iff (rst1)
                                    (a ##0 b[->1]) |=> c)
        $display("a3_explicit passed at %0d", $time);
      else $display("a3_explicit failed at %0d", $time);
    end
  end

  initial begin
    #12 c = 1;
    #16 c = 0;
    #8 rst1 = 1;
    #6 rst1 = 0;
    #6 $finish;
  end
endmodule
