#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BuiltinMethodElaboration, ArraySizeMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [];\n"
             "  int s;\n"
             "  initial s = arr.size();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArraySizeNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [];\n"
             "  int s;\n"
             "  initial s = arr.size;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, QueuePushBackOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  initial begin\n"
             "    q.push_back(42);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, DynArraySizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int dyn [];\n"
             "  int sz;\n"
             "  initial sz = dyn.size();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, StringLenOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  string s;\n"
             "  int n;\n"
             "  initial n = s.len();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, EnumNumOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  int n;\n"
             "  initial n = c.num();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, MethodWithDefaultArgNoParensOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  color_e n;\n"
             "  initial n = c.next;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, MethodNoParensInExpressionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [];\n"
             "  int r;\n"
             "  initial r = arr.size + 1;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, DynArraySizeNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int dyn [];\n"
             "  int sz;\n"
             "  initial sz = dyn.size;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, AssocNumNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int assoc [string];\n"
             "  int n;\n"
             "  initial n = assoc.num;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, StringLenNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  string s;\n"
             "  int n;\n"
             "  initial n = s.len;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ImplicitVariableWithParenthesesIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  string s = \"ab\";\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = q.min()[0];\n"
      "    x = s.toupper()[1];\n"
      "    x = q.unique().size();\n"
      "    x = q.unique().size;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

constexpr std::string_view kParenthesesRequired =
    "a built-in method call used as an implicit variable shall include its "
    "parentheses";

constexpr std::string_view kParentheses = "^";

std::string WithParenthesesAs(std::string source, std::string_view written) {
  for (std::size_t at = source.find(kParentheses); at != std::string::npos;
       at = source.find(kParentheses, at)) {
    source.replace(at, kParentheses.size(), written);
  }
  return source;
}

void ExpectParenthesesRequired(const std::string& source) {
  ElabFixture kept;
  ElaborateSrc(WithParenthesesAs(source, "()"), kept);
  EXPECT_FALSE(kept.diag.HasErrors());
  ElabFixture omitted;
  ElaborateSrc(WithParenthesesAs(source, ""), omitted);
  const std::vector<uint32_t> kLines = LinesHolding(source, kParentheses);
  EXPECT_EQ(omitted.diag.ErrorCount(), kLines.size());
  for (uint32_t line : kLines) {
    EXPECT_TRUE(ReportedError(omitted.diag.Diagnostics(), kParenthesesRequired,
                              line, "5.13"))
        << line;
  }
}

TEST(BuiltinMethodElaboration, ImplicitVariableWithoutParenthesesIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  string s = \"ab\";\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = q.min[0];\n"
      "    x = s.toupper[1];\n"
      "    x = q.unique.size();\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 7u, 8u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kParenthesesRequired, line, "5.13"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(BuiltinMethodElaboration, ImplicitVariableOfEachTypesMethodsIsJudged) {
  ExpectParenthesesRequired(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  typedef struct {int a; string t;} st_t;\n"
      "  class C; int v; endclass\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  int d[] = '{3, 1};\n"
      "  int aa[string] = '{\"x\": 1};\n"
      "  int fx[4];\n"
      "  st_t qs[$];\n"
      "  C qc[$];\n"
      "  string ss[$];\n"
      "  string s = \"ab\";\n"
      "  color_e c;\n"
      "  event ev;\n"
      "  int x;\n"
      "  string t;\n"
      "  initial begin\n"
      "    x = q.max^[0];\n"
      "    x = q.unique_index^.size();\n"
      "    x = q.sum^[3:0];\n"
      "    x = q.size^[0];\n"
      "    x = q.pop_front^[1];\n"
      "    x = qs.pop_back^.a;\n"
      "    x = qc.pop_front^.v;\n"
      "    x = ss.pop_front^.len();\n"
      "    x = d.min^[0];\n"
      "    x = d.unique^.size();\n"
      "    x = d.size^[0];\n"
      "    x = aa.max^[0];\n"
      "    x = aa.unique^.size();\n"
      "    x = aa.num^[0];\n"
      "    x = fx.min^[0];\n"
      "    x = fx.unique^.size();\n"
      "    x = fx.xor^[0];\n"
      "    x = s.tolower^.len();\n"
      "    x = s.len^[0];\n"
      "    x = s.atoi^[0];\n"
      "    t = c.next^.name();\n"
      "    x = c.last^[0];\n"
      "    x = c.num^[0];\n"
      "    x = q.unique().min^[0];\n"
      "    x = s.toupper().tolower^[0];\n"
      "    x = q.find() with (item > 1).min^[0];\n"
      "    x = q.max^ with (item)[0];\n"
      "    x = q.map^ with (item + 1).size();\n"
      "    x = q.find^ with (item > 1).size();\n"
      "    x = q.unique^.size;\n"
      "    x = ev.triggered^[0];\n"
      "  end\n"
      "endmodule\n");
}

TEST(BuiltinMethodElaboration, ImplicitVariableOfEachReceiverIsJudged) {
  ExpectParenthesesRequired(
      "package p;\n"
      "  typedef int iq_t[$];\n"
      "  int q[$];\n"
      "  class K; static int q[$]; iq_t t; endclass\n"
      "endpackage\n"
      "typedef string text_t;\n"
      "interface ifc; int q[$]; endinterface\n"
      "module sub; int q[$]; endmodule\n"
      "module m(ifc i);\n"
      "  import p::*;\n"
      "  typedef struct {iq_t a; text_t t;} st_t;\n"
      "  typedef enum {RED, GREEN} color_e;\n"
      "  class B; iq_t bq; endclass\n"
      "  class C extends B;\n"
      "    typedef int own_t[$];\n"
      "    own_t oq;\n"
      "    C next;\n"
      "    function iq_t getq(); return bq; endfunction\n"
      "    static function string name(); return \"c\"; endfunction\n"
      "    function int f();\n"
      "      return bq.min^[0] + this.oq.min^[0]\n"
      "          + super.bq.max^[0] + getq().sum^[0];\n"
      "    endfunction\n"
      "  endclass\n"
      "  iq_t tq, table_[2];\n"
      "  st_t st;\n"
      "  C c = new;\n"
      "  K k = new;\n"
      "  sub u();\n"
      "  virtual ifc v;\n"
      "  parameter string P = \"ab\";\n"
      "  text_t ts;\n"
      "  int qq[$][$];\n"
      "  string ws[$];\n"
      "  int x;\n"
      "  function automatic iq_t fq(); return tq; endfunction\n"
      "  function automatic text_t ft(int a); return ts; endfunction\n"
      "  initial begin\n"
      "    x = tq.min^[0];\n"
      "    x = table_[1].min^[0];\n"
      "    x = tq[0:1].min^[0];\n"
      "    x = st.a.min^[0];\n"
      "    x = st.t.len^[0];\n"
      "    x = c.bq.min^[0];\n"
      "    x = c.next.oq.min^[0];\n"
      "    x = c.getq().min^[0];\n"
      "    x = C::name().len^[0];\n"
      "    x = p::q.min^[0];\n"
      "    x = p::K::q.min^[0];\n"
      "    x = K::q.min^[0];\n"
      "    x = k.t.min^[0];\n"
      "    x = u.q.min^[0];\n"
      "    x = i.q.min^[0];\n"
      "    x = v.q.min^[0];\n"
      "    x = P.len^[0];\n"
      "    x = ts.len^[0];\n"
      "    x = qq.min() with (item.size()).min^[0];\n"
      "    x = qq[0].min^[0];\n"
      "    x = qq.pop_front().min^[0];\n"
      "    x = fq().min^[0];\n"
      "    x = ft(1).len^[0];\n"
      "    x = RED.next^[0];\n"
      "    tq = ws.find_index() with (item.len^[0]);\n"
      "    tq = ws.find_index(w) with (w.len^[0]);\n"
      "    tq = ws.find_index() with (item.index^[0]);\n"
      "  end\n"
      "endmodule\n"
      "module top; ifc i(); m u(i); endmodule\n");
}

TEST(BuiltinMethodElaboration, ImplicitVariableInEachPlaceIsJudged) {
  ExpectParenthesesRequired(
      "int uq[$];\n"
      "int ux = uq.size^[0];\n"
      "function automatic int uf(); return uq.min^[0]; endfunction\n"
      "class UC;\n"
      "  string s;\n"
      "  int x = s.len^[0];\n"
      "  rand int r;\n"
      "  constraint c { r > s.len^[0]; if (r > 1) r != s.len^[1]; }\n"
      "  function new(int a = uq.size^[0]); x = uq.min^[0]; endfunction\n"
      "  extern function int out();\n"
      "  extern task tout();\n"
      "  class N; string t; function int f(); return t.len^[0]; endfunction\n"
      "  endclass\n"
      "endclass\n"
      "function int UC::out(); return s.len^[0]; endfunction\n"
      "task UC::tout(); x = s.len^[0]; endtask\n"
      "package p;\n"
      "  int pq[$];\n"
      "  int px = pq.size^[0];\n"
      "  function automatic int pf(); return pq.min^[0]; endfunction\n"
      "  class PC; function int f(); return pq.min^[0]; endfunction endclass\n"
      "endpackage\n"
      "interface ifc; int q[$]; initial $display(q.min^[0]); endinterface\n"
      "program prg; int q[$]; initial $display(q.min^[0]); endprogram\n"
      "checker chk(logic clk, logic a);\n"
      "  string s = \"ab\";\n"
      "  always_comb assert (s.len^[0]);\n"
      "endchecker\n"
      "module sub(input logic a); endmodule\n"
      "module m(input logic clk);\n"
      "  int q[$];\n"
      "  string s;\n"
      "  int x = q.size^[0];\n"
      "  wire [3:0] w;\n"
      "  assign w = q.size^[3:0];\n"
      "  assign #(q.size^[1]) w = 1;\n"
      "  and g(w[0], q.size^[0], 1'b1);\n"
      "  sub u(.a(q.size^[0]));\n"
      "  let l(a) = a + q.size^[0];\n"
      "  assert property (@(posedge clk) s.len^[0]);\n"
      "  property pr; @(posedge clk) s.len^[0] |-> s.len^[1]; endproperty\n"
      "  sequence sq; @(posedge clk) s.len^[0] ##1 s.len^[1]; endsequence\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint s.len^[0] iff (s.len^[1]);\n"
      "  endgroup\n"
      "  if (1) begin : b\n"
      "    string gs;\n"
      "    initial $display(gs.len^[0]);\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin string cs; initial $display(cs.len^[0]); end\n"
      "  endcase\n"
      "  for (genvar i = 0; i < 1; i++) begin : f\n"
      "    always @(s.len^[0]) $display(q.min^[0]);\n"
      "  end\n"
      "  int y;\n"
      "  always_comb y = q.size^[0];\n"
      "  final $display(q.min^[0]);\n"
      "  task t(string a, int d = q.size^[0]);\n"
      "    $display(a.len^[0]);\n"
      "  endtask\n"
      "  UC o;\n"
      "  initial begin : blk\n"
      "    static string z = \"ab\";\n"
      "    automatic int i = z.len^[0];\n"
      "    if (z.len^[0]) x = 1;\n"
      "    for (string n = \"ab\"; n.len^[0]; n = \"\") x = 1;\n"
      "    while (z.len^[4]) x = 1;\n"
      "    case (z.len^[0]) z.len^[1]: x = 2; endcase\n"
      "    foreach (q[j]) x = z.len^[0];\n"
      "    fork x = z.len^[0]; join\n"
      "    q[z.len^[0]] = 1;\n"
      "    x = o.randomize() with { r > s.len^[0]; };\n"
      "    x = (z.len^[0] ? z.len^[1] : z.len^[2]) + {z.len^[3]};\n"
      "    uf2(z.len^[0]);\n"
      "    #(z.len^[0]) x = 1;\n"
      "    @(z.len^[0]) x = 1;\n"
      "    wait (z.len^[0]);\n"
      "    assert (z.len^[0]);\n"
      "  end\n"
      "  function void uf2(int a); endfunction\n"
      "endmodule\n");
}

TEST(BuiltinMethodElaboration, ImplicitVariableOfEachHandlesMethodsIsJudged) {
  ExpectParenthesesRequired(
      "module m;\n"
      "  class C;\n"
      "    rand int r;\n"
      "    randc bit [1:0] rc;\n"
      "    constraint k {r > 0;}\n"
      "  endclass\n"
      "  C c = new;\n"
      "  process p;\n"
      "  std::process sp;\n"
      "  mailbox #(int) mb = new;\n"
      "  semaphore sm = new(1);\n"
      "  string s;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = c.randomize^[0];\n"
      "    x = c.get_randstate^.len();\n"
      "    x = c.r.rand_mode^[0];\n"
      "    x = c.rc.rand_mode^[0];\n"
      "    x = c.k.constraint_mode^[0];\n"
      "    s = p.status^.name();\n"
      "    x = p.get_randstate^.len();\n"
      "    s = sp.status^.name();\n"
      "    x = mb.num^[0];\n"
      "    x = sm.try_get^[0];\n"
      "  end\n"
      "endmodule\n");
}

TEST(BuiltinMethodElaboration, ImplicitVariableOfEachFurtherReceiverIsJudged) {
  ExpectParenthesesRequired(
      "package p;\n"
      "  typedef int iq_t[$];\n"
      "  iq_t pq;\n"
      "  class K;\n"
      "    typedef string kt_t;\n"
      "    class L; typedef int lq_t[$]; static lq_t q; endclass\n"
      "  endclass\n"
      "endpackage\n"
      "int uq[$];\n"
      "class UK; static int q[$]; endclass\n"
      "module m #(parameter string PB[2] = '{\"a\", \"b\"});\n"
      "  import p::pq;\n"
      "  import \"DPI-C\" function string dstr();\n"
      "  typedef enum {RED, GREEN} color_e;\n"
      "  parameter type T = int;\n"
      "  parameter string PA[2] = '{\"a\", \"b\"};\n"
      "  struct {struct {int a[$];} in; string n; color_e c; color_e [1:0] p;} "
      "ns;\n"
      "  color_e [1:0] pc;\n"
      "  var type(pq) tr;\n"
      "  p::K::kt_t kt;\n"
      "  p::K::L::lq_t lq;\n"
      "  string ts;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = pq.min^[0];\n"
      "    x = $unit::uq.min^[0];\n"
      "    x = $unit::UK::q.min^[0];\n"
      "    x = PB[1].len^[0];\n"
      "    x = dstr().len^[0];\n"
      "    x = PA[0].len^[0];\n"
      "    x = ns.in.a.min^[0];\n"
      "    x = ns.n.len^[0];\n"
      "    x = ns.c.name^.len();\n"
      "    x = pc[1].name^.len() + ns.p[0].name^.len();\n"
      "    x = tr.min^[0];\n"
      "    x = kt.len^[0];\n"
      "    x = lq.min^[0];\n"
      "    x = p::K::L::q.min^[0];\n"
      "    x = string'(x).len^[0];\n"
      "    x = p::iq_t'(tr).min^[0];\n"
      "    x = (x ? tr : pq).min^[0];\n"
      "    x = {ts, \"a\"}.len^[0];\n"
      "    x = {2{ts}}.len^[0];\n"
      "    x = $sformatf(\"%0d\", x).len^[0];\n"
      "  end\n"
      "endmodule\n");
}

TEST(BuiltinMethodElaboration, ImplicitVariableInEachFurtherPlaceIsJudged) {
  ExpectParenthesesRequired(
      "interface ifc;\n"
      "  int q[$];\n"
      "  modport mp(input .a(q.size^[0]));\n"
      "endinterface\n"
      "module sub #(parameter int P = 1)(input logic a); string s; endmodule\n"
      "module m(input logic clk, input logic clk2);\n"
      "  parameter string PS = \"ab\";\n"
      "  int q[$], arr[3], x, y, z;\n"
      "  string s;\n"
      "  logic [1:0][PS.len^[1]:0] v;\n"
      "  sub u[PS.len^[1]:0](.a(1'b1));\n"
      "  sub w(.a(1'b1));\n"
      "  defparam w.P = PS.len^[0];\n"
      "  bind sub chk b(.a(s.len^[0]));\n"
      "  if (0) begin end else begin\n"
      "    initial $display(s.len^[0]);\n"
      "    bind sub chk b3(.a(s.len^[0]));\n"
      "  end\n"
      "  module inner; string t; initial $display(t.len^[0]); endmodule\n"
      "  inner in();\n"
      "  clocking cb @(posedge clk);\n"
      "    input c = s.len^[0];\n"
      "  endclocking\n"
      "  property pf(string a, untyped b);\n"
      "    int n;\n"
      "    @(posedge clk) (1, n = a.len^[0]) |-> a.len^[1] && b;\n"
      "  endproperty\n"
      "  property pl;\n"
      "    int n = s.len^[0];\n"
      "    @(posedge clk) n;\n"
      "  endproperty\n"
      "  property pc;\n"
      "    @(posedge clk) case (x) 1, s.len^[0]: 1; default: 0; endcase\n"
      "  endproperty\n"
      "  sequence mc;\n"
      "    @(posedge clk) s.len^[0] ##1 @(posedge clk2) s.len^[1];\n"
      "  endsequence\n"
      "  initial cover sequence (@(posedge clk) s.len^[0] ##1 1);\n"
      "  covergroup cg @(posedge clk);\n"
      "    option.weight = s.len^[0];\n"
      "    a: coverpoint x {\n"
      "      bins b1 = {[0:s.len^[0]]} iff (s.len^[1]);\n"
      "      bins b2[] = {[0:7]} with (item > s.len^[0]);\n"
      "      bins b3 = (0, [1:s.len^[0]] => 2[*1:PS.len^[1]]);\n"
      "    }\n"
      "    b: coverpoint y;\n"
      "    ab: cross a, b iff (s.len^[0]) {\n"
      "      function CrossQueueType f(); string l; x = l.len^[0]; "
      "endfunction\n"
      "      bins c1 = binsof(a) intersect {[0:s.len^[0]]} && binsof(b);\n"
      "      ignore_bins c2 = binsof(a) with (a > s.len^[0]);\n"
      "    }\n"
      "  endgroup\n"
      "  class C;\n"
      "    string t;\n"
      "    rand int r, ra[2];\n"
      "    constraint k {\n"
      "      r dist {[0:t.len^[0]] := t.len^[1], 9 :/ 1};\n"
      "      foreach (ra[i]) ra[i] > t.len^[0];\n"
      "    }\n"
      "    covergroup cc; coverpoint r iff (t.len^[0]); endgroup\n"
      "    function new(); cc = new; endfunction\n"
      "  endclass\n"
      "  C c = new;\n"
      "  initial begin\n"
      "    for (x = 0; x < s.len^[0]; x++) y = 1;\n"
      "    x = y inside {[0:s.len^[0]]};\n"
      "    x = {<<{q with [0:s.len^[0]]}};\n"
      "    x = randomize(x) with {x > s.len^[0];};\n"
      "    x = std::randomize(x) with {x > s.len^[0];};\n"
      "    x = c.randomize with {r > t.len^[0];};\n"
      "  end\n"
      "endmodule\n"
      "module chk(input logic a); endmodule\n"
      "bind m chk b2(.a(s.len^[0]));\n");
}

TEST(BuiltinMethodElaboration, MembersOfABaseScopedThroughItselfAreNotJudged) {
  ElabFixture f;
  ElaborateSrc(
      "class T; int q[$]; endclass\n"
      "class A extends B::T; endclass\n"
      "class B extends A::T; endclass\n"
      "module m;\n"
      "  A a;\n"
      "  int x;\n"
      "  initial x = a.q.size[0];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kParenthesesRequired, 7, "5.13"));
}

TEST(BuiltinMethodElaboration, AWithClauseOnNoMethodCallNamesNoIterator) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int q[$], x;\n"
      "  function int fn(int v); return v; endfunction\n"
      "  initial x = fn(x) with (item.size[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a with clause follows only an array method call or a randomize call", 4,
      "A.8.2"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kParenthesesRequired, 4, "5.13"));
}

TEST(BuiltinMethodElaboration, ReceiversOfNoKnownTypeAreNotJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  import p::nothing;\n"
      "  typedef int iq_t[$];\n"
      "  class A extends A; endclass\n"
      "  typedef class Y;\n"
      "  typedef Y yt;\n"
      "  class Y extends yt; endclass\n"
      "  Y y;\n"
      "  class D #(type T = int) extends T; endclass\n"
      "  class R; rand int r; endclass\n"
      "  D #(R) dr;\n"
      "  R r = new;\n"
      "  mailbox mb;\n"
      "  semaphore sm;\n"
      "  string ws[$];\n"
      "  typedef enum {RED, GREEN} color_e;\n"
      "  color_e [1:0] pc;\n"
      "  bind m.u chk b(.a(1'b1));\n"
      "  A a;\n"
      "  int q[$], v;\n"
      "  event ev;\n"
      "  string s;\n"
      "  sequence sq(logic c); @(posedge c) 1; endsequence\n"
      "  initial begin\n"
      "    v = nopkg::q.size[0];\n"
      "    v = this.q.min[0];\n"
      "    v = super.q.min[0];\n"
      "    v = iq_t::q.min[0];\n"
      "    v = a.q.size[0];\n"
      "    v = y.q.size[0];\n"
      "    v = ev.len[0];\n"
      "    v = dr.q.size[0];\n"
      "    v = r.r.size[0];\n"
      "    v = r.status[0];\n"
      "    v = mb.get_randstate[0];\n"
      "    v = mb.try_get[0];\n"
      "    v = sm.num[0];\n"
      "    v = {ws}.len[0];\n"
      "    v = pc.name[0];\n"
      "    v = v[0].size[0];\n"
      "    v = q.sum() with (item).len[0];\n"
      "    v = $time().len[0];\n"
      "    v = {v, v}.len[0];\n"
      "    v = int'(v).len[0];\n"
      "    v = 5'(v).len[0];\n"
      "    v = sq(v).len[0] + $typename(v).size[0];\n"
      "    v = nothing.size[0];\n"
      "    v = v.find() with (item.size[0]);\n"
      "    v = A::B::q.size[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line = 1; line < 50; ++line) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kParenthesesRequired, line, "5.13"))
        << line;
  }
}

TEST(BuiltinMethodElaboration, MembersNamedAsBuiltinMethodsAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p; int size[$]; endpackage\n"
      "interface ifc; int size[$]; endinterface\n"
      "module sub; int min[$]; endmodule\n"
      "module m(ifc i);\n"
      "  typedef struct {int size[2]; string name; int min[$];} st_t;\n"
      "  class C #(type T = int);\n"
      "    int size[$]; C next; C last; string name; T len;\n"
      "    function int f(); return size[0] + this.size[1]; endfunction\n"
      "  endclass\n"
      "  st_t st, sts[2];\n"
      "  C#(int) c;\n"
      "  sub u();\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = st.size[0] + st.min[0] + st.name.len() + sts[1].size[0];\n"
      "    x = c.size[0] + c.next.size[0] + c.last.name.len() + c.len[0];\n"
      "    x = u.min[0] + i.size[0] + p::size[0];\n"
      "  end\n"
      "endmodule\n"
      "module top; ifc i(); m u(i); endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BuiltinMethodElaboration, BareCallThatIsNoImplicitVariableIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$], d[], aa[string], x, r[$];\n"
      "  string s;\n"
      "  typedef enum {RED, GREEN} color_e;\n"
      "  color_e c;\n"
      "  initial begin\n"
      "    x = q.size + d.size + aa.num + s.len + q[q.size - 1];\n"
      "    x = s.toupper().len + q.unique().size + c.next().num;\n"
      "    r = q.unique;\n"
      "    r = q.find with (item > 1);\n"
      "    s = c.next().name;\n"
      "    r = q.unique().find with (item > 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
