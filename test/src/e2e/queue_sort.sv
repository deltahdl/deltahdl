module queue_sort;
  int q[$];

  initial begin
    q.push_back(30);
    q.push_back(10);
    q.push_back(40);
    q.push_back(20);

    q.sort();
    $display("%0d", q[0]);
    $display("%0d", q[1]);
    $display("%0d", q[2]);
    $display("%0d", q[3]);

    q.rsort();
    $display("%0d", q[0]);
    $display("%0d", q[1]);
    $display("%0d", q[2]);
    $display("%0d", q[3]);
  end
endmodule
