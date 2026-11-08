module assertion_kinds;
  logic clk = 1'b0;
  logic ok = 1'b1;
  int concurrent_assert_fails = 0;
  int concurrent_assume_fails = 0;
  int concurrent_cover_hits = 0;
  int immediate_assert_fails = 0;
  int immediate_assume_fails = 0;
  int immediate_cover_hits = 0;
  time concurrent_assert_fail_time = 0;
  time immediate_assert_fail_time = 0;

  always #5 clk = ~clk;

  assert property (@(posedge clk) ok)
  else begin
    concurrent_assert_fails = concurrent_assert_fails + 1;
    concurrent_assert_fail_time = $time;
  end

  assume property (@(posedge clk) ok)
  else concurrent_assume_fails = concurrent_assume_fails + 1;

  cover property (@(posedge clk) !ok)
    concurrent_cover_hits = concurrent_cover_hits + 1;

  restrict property (@(posedge clk) ok);

  always @(ok) begin
    assert (ok)
    else begin
      if (immediate_assert_fails == 0) immediate_assert_fail_time = $time;
      immediate_assert_fails = immediate_assert_fails + 1;
    end
    assume (ok)
    else immediate_assume_fails = immediate_assume_fails + 1;
    cover (!ok) immediate_cover_hits = immediate_cover_hits + 1;
  end

  initial begin
    #12 ok = 1'b0;
    #1 ok = 1'b1;
    #9 ok = 1'b0;
    #6 ok = 1'b1;
    #12;
    $display("concurrent assert: failed %0d time, at %0d",
             concurrent_assert_fails, concurrent_assert_fail_time);
    $display("concurrent assume: failed %0d time", concurrent_assume_fails);
    $display("concurrent cover: hit %0d time", concurrent_cover_hits);
    $display("immediate assert: failed %0d times, first at %0d",
             immediate_assert_fails, immediate_assert_fail_time);
    $display("immediate assume: failed %0d times", immediate_assume_fails);
    $display("immediate cover: hit %0d times", immediate_cover_hits);
    $finish;
  end
endmodule
