class Sorted;
  rand int A[];
  int k = 100;
  constraint c1 { A.size inside {[1:10]}; }
  constraint c2 { foreach (A[k]) (k < A.size - 1) -> A[k + 1] > A[k]; }
endclass

class Fixed;
  rand int A[];
  constraint each { foreach (A[i]) A[i] == i * 3; }
endclass

class Stepped;
  rand int B[4];
  int off = 2;
  constraint range { foreach (B[i]) B[i] inside {[0:99]}; }
  constraint step { foreach (B[i]) (i >= off) -> B[i] == B[i - off] + 1; }
endclass

module foreach_iterative_constraints;
  int sized = 0, ascending = 0, sizes_seen = 0, stepped = 0, ok = 0;
  bit seen[11];
  initial begin
    static Sorted s = new;
    static Fixed f = new;
    static Stepped p = new;
    repeat (128) begin
      void'(s.randomize());
      if (s.A.size() >= 1 && s.A.size() <= 10) begin
        sized++;
        seen[s.A.size()] = 1;
      end
      ok = 1;
      for (int i = 1; i < s.A.size(); i++)
        if (s.A[i] <= s.A[i - 1]) ok = 0;
      if (ok) ascending++;
    end
    for (int n = 1; n <= 10; n++)
      if (seen[n]) sizes_seen++;
    f.A = new[5];
    void'(f.randomize());
    repeat (64) begin
      void'(p.randomize());
      if (p.B[2] == p.B[0] + 1 && p.B[3] == p.B[1] + 1) stepped++;
    end
    $display("sized 1 to 10: %0d of 128, ascending: %0d of 128", sized,
             ascending);
    $display("sizes drawn: %0d of 10, k: %0d", sizes_seen, s.k);
    $display("size kept: %0d, elements: %0d %0d %0d %0d %0d", f.A.size(),
             f.A[0], f.A[1], f.A[2], f.A[3], f.A[4]);
    $display("stepped: %0d of 64", stepped);
    $finish;
  end
endmodule
