module sequences;
  logic clk = 0;
  logic req = 0;
  logic gnt = 0;
  string one = "";
  string two = "";
  string zero = "";
  string window = "";
  string extended = "";
  string open = "";
  always #5 clk = ~clk;

  sequence req_gnt_1;
    @(posedge clk) req ##1 gnt;
  endsequence

  sequence req_gnt_2;
    @(posedge clk) req ##2 gnt;
  endsequence

  sequence req_gnt_0;
    @(posedge clk) req ##0 gnt;
  endsequence

  sequence req_gnt_window;
    @(posedge clk) req ##[2:4] gnt;
  endsequence

  sequence req_gnt_extended;
    @(posedge clk) req ##1 gnt ##2 1'b1;
  endsequence

  sequence req_gnt_open;
    @(posedge clk) req ##[3:$] gnt;
  endsequence

  initial forever begin
    wait (req_gnt_1.triggered);
    one = $sformatf("%s %0d", one, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (req_gnt_2.triggered);
    two = $sformatf("%s %0d", two, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (req_gnt_0.triggered);
    zero = $sformatf("%s %0d", zero, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (req_gnt_window.triggered);
    window = $sformatf("%s %0d", window, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (req_gnt_extended.triggered);
    extended = $sformatf("%s %0d", extended, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (req_gnt_open.triggered);
    open = $sformatf("%s %0d", open, $time);
    @(posedge clk);
  end

  initial begin
    #10 req = 1;
    #10 req = 0;
    gnt = 1;
    #10 gnt = 0;
    #10 req = 1;
    gnt = 1;
    #10 req = 0;
    #30 gnt = 0;
    #20;
    $display("req ##1 gnt ends at%s", one);
    $display("req ##2 gnt ends at%s", two);
    $display("req ##0 gnt ends at%s", zero);
    $display("req ##[2:4] gnt ends at%s", window);
    $display("req ##1 gnt ##2 `true ends at%s", extended);
    $display("req ##[3:$] gnt ends at%s", open);
    $finish;
  end
endmodule
