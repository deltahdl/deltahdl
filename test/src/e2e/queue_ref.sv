module queue_ref;
  int q[$];

  initial begin
    q.push_back(10);
    q.push_back(20);
    q.push_back(30);

    $display("%0d", q.size());
    $display("%0d", q[0]);
    $display("%0d", q[1]);
    $display("%0d", q[2]);

    $display("%0d", q.pop_front());
    $display("%0d", q.size());
    $display("%0d", q[0]);

    q.insert(0, 5);
    $display("%0d", q[0]);
    $display("%0d", q.size());
  end
endmodule
