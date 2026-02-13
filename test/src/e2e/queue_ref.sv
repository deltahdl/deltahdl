module queue_ref;
  int q[$];

  initial begin
    q.push_back(10);
    q.push_back(20);
    q.push_back(30);

    // Queue size and element access.
    $display("%0d", q.size());
    $display("%0d", q[0]);
    $display("%0d", q[1]);
    $display("%0d", q[2]);

    // pop_front returns the removed element.
    $display("%0d", q.pop_front());
    $display("%0d", q.size());
    $display("%0d", q[0]);

    // insert at position 0.
    q.insert(0, 5);
    $display("%0d", q[0]);
    $display("%0d", q.size());
  end
endmodule
