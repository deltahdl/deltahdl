module queue_ref_event;
  int q[$];
  int b;

  function automatic void set_ref(ref int v);
    v = 99;
  endfunction

  always_comb b = q[1];

  initial begin
    q.push_back(10);
    q.push_back(20);
    #1 set_ref(q[1]);
    #1 $display("%0d", b);
  end
endmodule
