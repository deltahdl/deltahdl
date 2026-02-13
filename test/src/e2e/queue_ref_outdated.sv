module queue_ref_outdated;
  int q[$];

  function automatic void del_and_set(ref int v);
    q.delete(1);
    v = 99;
  endfunction

  initial begin
    q.push_back(10);
    q.push_back(20);
    q.push_back(30);

    // Ref to q[1] becomes outdated when q.delete(1) removes it.
    del_and_set(q[1]);
    $display("%0d", q.size());
    $display("%0d", q[0]);
    $display("%0d", q[1]);
  end
endmodule
