module cross_array;
  int fixed_a[4] = '{10, 20, 30, 40};
  int dyn[];
  int q[$];

  initial begin
    // Fixed → Dynamic: resize dyn to match.
    dyn = fixed_a;
    $display("%0d %0d %0d %0d", dyn[0], dyn[1], dyn[2], dyn[3]);
    $display("%0d", dyn.size());

    // Fixed → Queue: populate queue.
    q = fixed_a;
    $display("%0d %0d %0d %0d", q[0], q[1], q[2], q[3]);
    $display("%0d", q.size());

    // Dynamic → Queue.
    dyn = new[2];
    dyn[0] = 100;
    dyn[1] = 200;
    q = dyn;
    $display("%0d %0d", q[0], q[1]);
    $display("%0d", q.size());
  end
endmodule
