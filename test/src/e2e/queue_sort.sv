module queue_sort;
  int q[$];

  initial begin
    q.push_back(30);
    q.push_back(10);
    q.push_back(40);
    q.push_back(20);

    // §7.12.2: sort() puts the elements in ascending order. §7.12 Syntax 7-5
    // makes the argument list optional, so this call is `q.sort` with an empty
    // one.
    q.sort();
    $display("%0d", q[0]);
    $display("%0d", q[1]);
    $display("%0d", q[2]);
    $display("%0d", q[3]);

    // §7.12.2: rsort() puts them in descending order.
    q.rsort();
    $display("%0d", q[0]);
    $display("%0d", q[1]);
    $display("%0d", q[2]);
    $display("%0d", q[3]);
  end
endmodule
