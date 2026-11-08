module cover_statement;
  logic clk = 0;
  logic req = 0, ack = 0, rst = 0;
  int implied_hits = 0, acked_hits = 0, reactive_hits = 0;
  int matched_hits = 0, marker = 0;
  always #5 clk = ~clk;
  always @(posedge clk) marker = $time;

  implied: cover property (@(posedge clk) disable iff (rst) req |=> ack)
    implied_hits++;
  acked: cover property (@(posedge clk) ack) begin
    acked_hits++;
    if (marker == $time) reactive_hits++;
  end
  requested: cover property (@(posedge clk) req);
  matched: cover sequence (@(posedge clk) disable iff (rst) req ##[1:2] ack)
    matched_hits++;

  initial begin
    #10 req = 1;
    #10 req = 0; ack = 1;
    #20 ack = 0; req = 1;
    #10 req = 0; ack = 1;
    #12 rst = 1;
    #6 rst = 0;
    #2 ack = 0; req = 1;
    #10 req = 0;
    #10 $display("implied: pass statement ran %0d times", implied_hits);
    $display("acked: pass statement ran %0d times, %0d in the Reactive region",
             acked_hits, reactive_hits);
    $display("matched: pass statement ran %0d times", matched_hits);
    $finish;
  end
endmodule
