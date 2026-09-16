// §16.14 Concurrent assertions: a property on its own is never evaluated
// and is checked through an assertion statement, one of assert property,
// assume property, cover property, cover sequence and restrict property,
// which may stand in an always or initial procedure, a module, an
// interface, a program, a generate block or a checker; a statement may be
// named, and its name is a level of the hierarchical name its action block
// reports, while an unnamed statement creates no scope. clk rises at 5,
// 15, ..., 105, and each of the signals a to j is low across one tick, a at
// 15, b at 25 and so on to j at 105, so that each statement below fails or
// is covered at a tick of its own and reports %m there. The declared
// property idle is never instantiated, so nothing evaluates it. The
// statement in the always procedure takes the procedure's clock; a
// statement in an initial procedure, on a clock of its own, is §16.14.6's.
interface bus_if(input logic clk, input logic f);
  if_named: assert property (@(posedge clk) f)
    else $display("%m failed at %0d", $time);
endinterface

checker chk(input logic clk, input logic g);
  chk_named: assert property (@(posedge clk) g)
    else $display("%m failed at %0d", $time);
endchecker

module concurrent_assertion_statements;
  logic clk = 0;
  logic a = 1, b = 1, c = 1, d = 1, e = 1, f = 1, g = 1, h = 1, i = 1;
  logic j = 1;
  always #5 clk = ~clk;

  bus_if bus(clk, f);
  chk u_chk(clk, g);

  property idle;
    @(posedge clk) 0;
  endproperty

  m_named: assert property (@(posedge clk) a)
    else $display("%m failed at %0d", $time);
  assert property (@(posedge clk) b)
    else $display("%m unnamed failed at %0d", $time);
  m_assume: assume property (@(posedge clk) c)
    else $display("%m failed at %0d", $time);
  m_cover_seq: cover sequence (@(posedge clk) h ##1 !h)
    $display("%m covered at %0d", $time);
  m_cover: cover property (@(posedge clk) !i)
    $display("%m covered at %0d", $time);
  m_restrict: restrict property (@(posedge clk) a);

  generate
    if (1) begin : gen
      g_named: assert property (@(posedge clk) d)
        else $display("%m failed at %0d", $time);
    end
  endgenerate

  always @(posedge clk) begin : proc
    p_named: assert property (e)
      else $display("%m failed at %0d", $time);
  end

  program prog;
    pr_named: assert property (@(posedge clk) j)
      else $display("%m failed at %0d", $time);
  endprogram

  initial begin
    #10 a = 0;
    #10 a = 1; b = 0;
    #10 b = 1; c = 0;
    #10 c = 1; d = 0;
    #10 d = 1; e = 0;
    #10 e = 1; f = 0;
    #10 f = 1; g = 0;
    #10 g = 1; h = 0;
    #10 h = 1; i = 0;
    #10 i = 1; j = 0;
    #10 j = 1;
    $finish;
  end
endmodule
