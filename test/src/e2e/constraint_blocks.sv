class Item;
  rand bit [7:0] lo;
  rand bit [7:0] hi;
  bit [7:0] limit = 100;
  constraint range { lo >= 10; lo <= 20; }
  constraint order { hi > lo; hi < limit; }
  constraint spacing { (hi - lo) % 4 == 0; }
endclass

class Other;
  rand bit [3:0] n;
  constraint range { n inside {[4:6]}; }
endclass

module constraint_blocks;
  int in_range = 0, ordered = 0, spaced = 0, under_limit = 0;
  int escaped = 0, still_ordered = 0, still_spaced = 0, other_in_range = 0;
  initial begin
    static Item it = new;
    static Other ot = new;
    repeat (64) begin
      void'(it.randomize());
      if (it.lo >= 10 && it.lo <= 20) in_range++;
      if (it.hi > it.lo && it.hi < 100) ordered++;
      if ((it.hi - it.lo) % 4 == 0) spaced++;
    end
    $display("every block holds at once: range %0d, order %0d, spacing %0d of 64",
             in_range, ordered, spaced);
    it.limit = 30;
    repeat (64) begin
      void'(it.randomize());
      if (it.hi > it.lo && it.hi < 30) under_limit++;
    end
    $display("the state variable's current value bounds hi: %0d of 64",
             under_limit);
    it.range.constraint_mode(0);
    repeat (64) begin
      void'(it.randomize());
      if (it.lo < 10 || it.lo > 20) escaped++;
      if (it.hi > it.lo && it.hi < 30) still_ordered++;
      if ((it.hi - it.lo) % 4 == 0) still_spaced++;
    end
    $display("with range off by name lo escapes 10 to 20: %0d, order %0d and spacing %0d of 64 still hold",
             escaped > 0, still_ordered, still_spaced);
    repeat (16) begin
      void'(ot.randomize());
      if (ot.n >= 4 && ot.n <= 6) other_in_range++;
    end
    $display("another class's block named range is its own: %0d of 16",
             other_in_range);
    $finish;
  end
endmodule
