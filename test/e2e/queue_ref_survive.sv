module queue_ref_survive;
  int q[$];

  function automatic void push_and_set(ref int v);
    q.push_front(5);
    v = 99;
  endfunction

  initial begin
    q.push_back(10);
    q.push_back(20);
    q.push_back(30);

    // Ref to q[1] (val=20) survives push_front; element shifts to index 2.
    push_and_set(q[1]);
    $display("%0d", q.size());
    $display("%0d", q[0]);
    $display("%0d", q[1]);
    $display("%0d", q[2]);
    $display("%0d", q[3]);
  end
endmodule
