module typed_sequence_formals;
  logic clk = 0;
  logic [7:0] v = 0;
  logic w = 0;
  parameter my_delay = 2;
  string s1_ends = "";
  string s2_ends = "";
  string ev_ends = "";
  string ev2_ends = "";
  string delay_ends = "";
  always #5 clk = ~clk;

  sequence s1(x, y);
    x ##1 y;
  endsequence

  sequence s2(bit x, y);
    x ##1 y;
  endsequence

  sequence s1_inst;
    @(posedge clk) s1(v, w);
  endsequence

  sequence s2_inst;
    @(posedge clk) s2(v, w);
  endsequence

  sequence event_arg_example(event ev);
    @(ev) v == 2 ##1 v == 1;
  endsequence

  sequence ev_inst;
    event_arg_example(posedge clk);
  endsequence

  sequence event_arg_example2(reg sig);
    @(posedge sig) v == 2 ##1 v == 1;
  endsequence

  sequence ev2_inst;
    event_arg_example2(clk);
  endsequence

  sequence delay_arg_example(shortint delay1, delay2);
    v == 2 ##delay1 w ##delay2 v == 0;
  endsequence

  sequence delay_inst;
    @(posedge clk) delay_arg_example(my_delay, my_delay - 1);
  endsequence

  initial forever begin
    wait (s1_inst.triggered);
    s1_ends = $sformatf("%s %0d", s1_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (s2_inst.triggered);
    s2_ends = $sformatf("%s %0d", s2_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (ev_inst.triggered);
    ev_ends = $sformatf("%s %0d", ev_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (ev2_inst.triggered);
    ev2_ends = $sformatf("%s %0d", ev2_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (delay_inst.triggered);
    delay_ends = $sformatf("%s %0d", delay_ends, $time);
    @(posedge clk);
  end

  initial begin
    #10 v = 8'h02;
    #10 v = 8'h01;
    w = 1;
    #10 v = 0;
    #10 w = 0;
    #30;
    $display("s1(v, w), x untyped, ends at%s", s1_ends);
    $display("s2(v, w), x a bit, ends at%s", s2_ends);
    $display("event_arg_example(posedge clk) ends at%s", ev_ends);
    $display("event_arg_example2(clk) ends at%s", ev2_ends);
    $display("delay_arg_example(my_delay, my_delay - 1) ends at%s", delay_ends);
    $finish;
  end
endmodule
