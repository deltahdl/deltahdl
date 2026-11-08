module deferred_assertion_reporting;
  int a = 1;
  event go;
  event go2;

  task automatic note(input string what);
    $display("%s", what);
  endtask

  function void set_a_1;
    a = 1;
  endfunction

  task fire_go2;
    -> go2;
  endtask

  always_comb begin : b1
    a1: assert #0 (a == 1) note("a1: a is 1"); else note("a1: a is not 1");
    f1: assert final (a == 1) note("f1: a is 1"); else note("f1: a is not 1");
  end

  initial begin
    #5;
    ->> go;
    assert #0 (1) note("flushed: an observed report that is never executed");
    assert final (1) note("flushed: a final report that is never executed");
    assert #0 (0);
    @(go);
    $display("at 5: resumed at the flush point, the three reports cleared");

    #5;
    assert #0 (1) note("at 10: matured, reported before the process resumes");
    assert final (1) note("flushed: a final report pending across the resume");
    cover #0 (1) fire_go2();
    @(go2);
    $display("at 10: resumed after go2 was triggered in the Reactive region");

    #10;
    a = 2;
    cover #0 (1) set_a_1();

    #5;
    assert #0 (a == 5);
    #1 $finish;
  end
endmodule
