module immediate_assertions;
  logic [7:0] v;
  logic f;
  logic flag = 1'b0;
  int count = 0;
  time t;
  event failed;

  initial begin
    @(failed);
    $display("event: fail statement triggered failed at %0d", $time);
  end

  initial begin
    v = 8'd0;
    assert (v) $display("0 passes"); else $display("0 fails");
    v = 8'bx;
    assert (v) $display("x passes"); else $display("x fails");
    v = 8'bz;
    assert (v) $display("z passes"); else $display("z fails");
    v = 8'd2;
    assert (v) $display("2 passes"); else $display("2 fails");

    assert (v == 8'd2);
    assert (v == 8'd0) else $display("no pass statement: v is not 0");
    assert (v == 8'd0);
    assume (v == 8'd0) else $display("assume: v is not 0");
    cover_two: cover (v == 8'd2) $display("cover: v is 2");
    cover_never: cover (v == 8'd9) $display("cover: v is 9");

    for (int i = 1; i >= 0; i = i - 1) begin
      f = (i == 1);
      assert_f: assert (f) $info("passed in %m"); else $info("failed in %m");
    end

    #10 assert (v == 8'd0)
    else begin
      t = $time;
      #5 $error("assert failed at time %0t", t);
    end

    assert (v == 8'd0) count = count + 1; else -> failed;
    #1;
    assert (v == 8'd0) else flag = 1'b1;
    $display("flag after the fail statement is %0d", flag);

    $assertoff;
    assert (v == 8'd0) $display("checked while off: passed");
    else $display("checked while off: failed");
    $asserton;
    assert (v == 8'd0) $display("checked after on: passed");
    else $display("checked after on: failed");
    $finish;
  end
endmodule
