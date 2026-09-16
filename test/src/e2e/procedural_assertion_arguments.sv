// §16.14.6.1 Arguments to procedural concurrent assertions: a procedural
// concurrent assertion saves the value of its const expressions and of its
// automatic variables at the time the evaluation attempt is placed in the
// procedural assertion queue, and the attempt uses the saved values, where
// a static variable is sampled in the Preponed region; the same holds of
// the variables of its action block, which the values reach as inputs; a
// matured instance holding temporal expressions keeps its saved values for
// the whole of its evaluation, the procedure's later execution affecting
// nothing of it; and a conditional around the assertion reads the current
// values, not the sampled ones. clk rises at 5, 15, 25 and 35, foo holds
// the even bits of 0 to 10 and bar the bits 0 to 4, and the run ends at
// 40.
//
// The clause's a1 to a3 loop over the static i, ten instances per tick:
// a1 reads the sampled i, 0 at the first tick, so foo[0] && bar[0] passes
// ten times, and 10 after, so foo[10] && bar[10] fails ten times a tick; a2
// reads const'(i) against the sampled i, so at the first tick foo[i] &&
// bar[0] passes for the five even i and after it foo[i] && bar[10] fails
// for every i; a3 reads const'(i) twice, so foo[i] && bar[i] passes for i
// in 0, 2 and 4 and fails for the seven others at every tick. The clause's
// a4 to a6 loop over the automatic j, whose immediate value is saved as
// const'(j)'s is, so all three count as a3 does. The clause's a7, foo[k]
// |=> bar[k] ##1 (w == 1'b1), is queued twice at 15, where act is 1, for k
// of 0 and 1: the instance of 1 holds vacuously at 15, foo[1] being 0, and
// the instance of 0 keeps its k while bar[0] is read at 25 and w, 1 from
// 30, at 35, where it passes. The clause's a8 loops over the static n, four
// instances a tick, its failures reporting const'(n), the instance's own,
// and $sampled(n), 0 at the first tick and 4 after. The clause's a9 is
// queued when en is 1 as assigned in the procedure, at 15, and a10 when
// $sampled(en) is 1, one tick later.
module procedural_assertion_arguments;
  logic clk = 0;
  logic [10:0] foo = 11'b10101010101, bar = 11'b00000011111;
  logic w = 0, act = 0, en = 0;
  int i, n, cyc = 0;
  int a1_pass = 0, a1_fail = 0, a2_pass = 0, a2_fail = 0;
  int a3_pass = 0, a3_fail = 0, a4_pass = 0, a4_fail = 0;
  int a5_pass = 0, a5_fail = 0, a6_pass = 0, a6_fail = 0;
  int a7_pass = 0, a7_fail = 0, a7_first = 0, a7_last = 0;
  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc++;
    en = (cyc == 2);
    if (en) begin
      a9: assert property (1) $display("a9 evaluated at %0d", $time);
    end
    if ($sampled(en)) begin
      a10: assert property (1) $display("a10 evaluated at %0d", $time);
    end
  end

  always @(posedge clk) begin
    for (i = 0; i < 10; i++) begin
      a1: assert property (foo[i] && bar[i]) a1_pass++; else a1_fail++;
      a2: assert property (foo[const'(i)] && bar[i]) a2_pass++;
      else a2_fail++;
      a3: assert property (foo[const'(i)] && bar[const'(i)]) a3_pass++;
      else a3_fail++;
    end
  end

  always @(posedge clk) begin
    for (int j = 0; j < 10; j++) begin
      a4: assert property (foo[j] && bar[j]) a4_pass++; else a4_fail++;
      a5: assert property (foo[const'(j)] && bar[j]) a5_pass++;
      else a5_fail++;
      a6: assert property (foo[const'(j)] && bar[const'(j)]) a6_pass++;
      else a6_fail++;
    end
  end

  always @(posedge clk) begin : procedural_block_1
    if (act == 1) begin
      for (int k = 0; k < 2; k++) begin
        a7: assume property (foo[k] |=> bar[k] ##1 (w == 1'b1)) begin
          a7_pass++;
          if (a7_pass == 1) a7_first = $time;
          else a7_last = $time;
        end else a7_fail++;
      end
    end
  end

  always @(posedge clk) begin
    for (n = 0; n < 4; n++) begin
      a8: assert property (foo[const'(n)] && bar[n]) else
        $display("a8 failed for const n=%0d and n=%0d", const'(n),
                 $sampled(n));
    end
  end

  initial begin
    #12 act = 1;
    #6 act = 0;
    #12 w = 1;
    #10 $display("a1 passes %0d fails %0d", a1_pass, a1_fail);
    $display("a2 passes %0d fails %0d", a2_pass, a2_fail);
    $display("a3 passes %0d fails %0d", a3_pass, a3_fail);
    $display("a4 passes %0d fails %0d", a4_pass, a4_fail);
    $display("a5 passes %0d fails %0d", a5_pass, a5_fail);
    $display("a6 passes %0d fails %0d", a6_pass, a6_fail);
    $display("a7 passes %0d fails %0d, at %0d and %0d", a7_pass, a7_fail,
             a7_first, a7_last);
    $finish;
  end
endmodule
