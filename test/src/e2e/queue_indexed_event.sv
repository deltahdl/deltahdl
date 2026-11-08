module queue_indexed_event;
  int q[$];
  int b;

  always_comb b = q[1];

  initial begin
    q.push_back(10);
    q.push_back(20);
    #1 q[1] = 99;
    #1 $display("%0d", b);
  end
endmodule
