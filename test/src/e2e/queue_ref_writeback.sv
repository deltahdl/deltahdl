module queue_ref_writeback;
  int q[$];

  function automatic void set_ref(ref int v);
    v = 99;
  endfunction

  initial begin
    q.push_back(10);
    q.push_back(20);
    q.push_back(30);

    // Pass q[1] by ref, set to 99.
    set_ref(q[1]);
    $display("%0d", q[0]);
    $display("%0d", q[1]);
    $display("%0d", q[2]);
  end
endmodule
