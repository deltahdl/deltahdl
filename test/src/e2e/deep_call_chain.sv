// §13.3 puts no limit on how many tasks a task may enable and §13.4 lets a
// function call itself, so a design's call chain is as deep as it writes it.
// The chain here nests one class method call per level through an automatic
// function, a class task and an if statement, deeper than UVM's run_test
// reaches before its root object exists, and reads the depth back.
class node;
  int depth;
  function new(int d);
    depth = d;
  endfunction
  function int count_down();
    node next;
    if (depth == 0) return 0;
    next = new(depth - 1);
    return 1 + next.count_down();
  endfunction
  task climb(input int n, output int sum);
    int below;
    if (n == 0) begin
      sum = 0;
      return;
    end
    climb(n - 1, below);
    sum = below + 1;
  endtask
endclass

function automatic int spine(int n);
  if (n == 0) return 0;
  return 1 + spine(n - 1);
endfunction

module top;
  initial begin
    node root;
    int total;
    root = new(600);
    $display("methods: %0d", root.count_down());
    root.climb(600, total);
    $display("tasks: %0d", total);
    $display("functions: %0d", spine(3000));
  end
endmodule
