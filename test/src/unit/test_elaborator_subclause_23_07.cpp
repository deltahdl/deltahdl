#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(DottedNameElaboration, StructDataObjectIsMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [7:0] result;\n"
      "  initial result = s.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, UnionDataObjectIsMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } u_t;\n"
      "  u_t u;\n"
      "  logic [7:0] result;\n"
      "  initial result = u.a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, ClassDataObjectIsMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C;\n"
      "    int val;\n"
      "  endclass\n"
      "  C obj;\n"
      "  int result;\n"
      "  initial begin\n"
      "    obj = new;\n"
      "    result = obj.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, NestedStructMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; } inner_t;\n"
      "  typedef struct packed { inner_t sub; } outer_t;\n"
      "  outer_t o;\n"
      "  logic [7:0] result;\n"
      "  initial result = o.sub.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, InterfacePortIsMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_if;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module sub(simple_if vif);\n"
      "  logic [7:0] r;\n"
      "  initial r = vif.data;\n"
      "endmodule\n"
      "module t;\n"
      "  simple_if intf();\n"
      "  sub u(intf);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, InterfaceInstanceScopeIsHierarchicalName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_if;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module t;\n"
      "  simple_if intf();\n"
      "  logic [7:0] result;\n"
      "  initial result = intf.data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, InstanceScopeIsHierarchicalName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial result = c1.sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, MultiLevelScopeIsHierarchicalName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  logic [7:0] data;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module t;\n"
      "  mid m1();\n"
      "  logic [7:0] result;\n"
      "  initial result = m1.l1.data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, MemberSelectAndHierarchicalNameCoexist) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  typedef struct packed { logic [7:0] x; } s_t;\n"
      "  s_t s;\n"
      "  logic [7:0] r1, r2;\n"
      "  initial begin\n"
      "    r1 = s.x;\n"
      "    r2 = c1.sig;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, UnresolvedFirstComponentTreatedAsHierarchical) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = unknown_scope.sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'unknown_scope' resolves to no declaration", 3,
      "23.8"));
}

TEST(DottedNameElaboration, ImportedScopeNameTreatedAsHierarchical) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  function automatic int f();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  int result;\n"
      "  initial result = f.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(DottedNameElaboration, StructMemberSelectAsAssignmentTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;\n"
      "  pair_t s;\n"
      "  initial s.x = 8'h12;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, HierarchicalNameAsAssignmentTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  initial c1.sig = 8'h34;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, SelectThroughAnIntegralOrRealVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  real r;\n"
      "  logic [7:0] v [2];\n"
      "  shortreal sr;\n"
      "  realtime rt;\n"
      "  initial begin\n"
      "    x.run();\n"
      "    $display(r.h);\n"
      "    v[0].go();\n"
      "    $display(sr.h, rt.h);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* noun = "built-in method of the integral or real value";
  for (int line : {8, 9, 10, 11}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), noun, line, "23.7"))
        << line;
  }
}

TEST(DottedNameElaboration, RandModeOfARandomIntegralPropertyIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class c;\n"
      "  rand int x;\n"
      "  function void off(); x.rand_mode(0); endfunction\n"
      "endclass\n"
      "module top;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, SelectOfAnUndeclaredStructMemberIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int i; int j; } st;\n"
      "  st s;\n"
      "  int x;\n"
      "  initial x = s.zz;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'st' has no member named 'zz'", 5,
                            "23.7"));
}

TEST(DottedNameElaboration, SelectOfAnUndeclaredNestedMemberIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union { int a; shortint b; } u_t;\n"
      "  typedef struct { struct { int k; } n; u_t u; } st;\n"
      "  st s [2];\n"
      "  int x, y;\n"
      "  initial x = s[1].n.zz;\n"
      "  initial y = s[0].u.c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the structure of 'n' has no member named 'zz'", 6,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "union 'u_t' has no member named 'c'", 7, "23.7"));
}

TEST(DottedNameElaboration, SelectsOfDeclaredStructMembersAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef struct { int i; } pt;\n"
      "  pt v;\n"
      "endpackage\n"
      "module m;\n"
      "  typedef union { int a; shortint b; } u_t;\n"
      "  typedef struct { int i; struct { int k; } n; u_t u; } st;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } ps;\n"
      "  st s [2];\n"
      "  ps [1:0] pa;\n"
      "  int w, x, y, z;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    w = p::v.i;\n"
      "    x = s[0].i;\n"
      "    y = s[1].n.k;\n"
      "    z = s[0].u.b;\n"
      "    q = pa[1].a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, GenerateBlockSelectReadsTheBlocksTypedef) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  typedef struct { int k; } st;\n"
      "  if (1) begin : g\n"
      "    typedef struct { int a, b; } pair_t;\n"
      "    st s;\n"
      "    function int f(pair_t p);\n"
      "      return p.a + p.b;\n"
      "    endfunction\n"
      "    int x;\n"
      "    initial x = s.zz;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'st' has no member named 'zz'", 11,
                            "23.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "structure 'pair_t' has no member named 'b'", 8,
                             "23.7"));
}

TEST(DottedNameElaboration, SubroutineAndBlockSelectsReadTheirOwnTypedefs) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  function int f();\n"
      "    typedef struct { int a, b; } pair_t;\n"
      "    pair_t p;\n"
      "    return p.b;\n"
      "  endfunction\n"
      "  function int g();\n"
      "    typedef struct { int k; } q_t;\n"
      "    q_t q;\n"
      "    begin\n"
      "      q_t r;\n"
      "      return q.zz + r.yy;\n"
      "    end\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial begin\n"
      "    typedef struct { int k; } s_t;\n"
      "    s_t s;\n"
      "    x = s.ww;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "structure 'pair_t' has no member named 'b'", 6,
                             "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'q_t' has no member named 'zz'", 13,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'q_t' has no member named 'yy'", 13,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 's_t' has no member named 'ww'", 20,
                            "23.7"));
}

TEST(DottedNameElaboration, ClassMemberAndRandModeOfAStructAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class k;\n"
      "  int v;\n"
      "endclass\n"
      "class j;\n"
      "  k h;\n"
      "endclass\n"
      "module m;\n"
      "  typedef struct { int i; } r_t;\n"
      "  class c;\n"
      "    typedef struct { int i; } q_t;\n"
      "    rand r_t r;\n"
      "    q_t q;\n"
      "    function void off(); r.rand_mode(0); endfunction\n"
      "    function int get(); return q.i; endfunction\n"
      "  endclass\n"
      "  typedef struct { int i; k h; } st;\n"
      "  st s;\n"
      "  j g;\n"
      "  int x, y;\n"
      "  initial x = s.h.v;\n"
      "  initial y = g.h.v;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, AMemberOfAPropertyAHandleHoldsIsJudged) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int x; string s; typedef enum {A, B} e_t; e_t e; endclass\n"
      "module top;\n"
      "  C h = new;\n"
      "  initial begin\n"
      "    h.x.foo();\n"
      "    h.s.foo();\n"
      "    h.e.foo();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "built-in method of the integral or real value", 5,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "built-in method of the string", 6, "6.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "built-in method of the enumeration", 7, "6.19.5"));
}

TEST(DottedNameElaboration, ABuiltInMethodOfAPropertyAHandleHoldsIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p; string s = \"ab\"; endpackage\n"
      "module top;\n"
      "  typedef enum {A, B} e_t;\n"
      "  class C; rand int x; string s; e_t e; int q [$]; endclass\n"
      "  C h = new;\n"
      "  initial begin\n"
      "    void'(h.s.len());\n"
      "    void'(h.e.name());\n"
      "    void'(h.q.size());\n"
      "    h.x.rand_mode(0);\n"
      "    void'(p::s.len());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, AMemberOfAnUndeclaredPropertyIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int x; endclass\n"
      "module top;\n"
      "  C h = new;\n"
      "  initial h.nope.foo();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'C' has no member named 'nope'", 4, "8.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 1U);
}

TEST(DottedNameElaboration, AMemberOfAStdMethodsIntResultIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  mailbox mb = new; semaphore sm = new(1);\n"
      "  initial begin\n"
      "    void'(mb.num().foo());\n"
      "    void'(sm.try_get().foo());\n"
      "  end\n"
      "endmodule\n",
      f);
  for (int line : {4, 5}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "built-in method of the integral or real value",
                              line, "23.7"))
        << line;
  }
}

TEST(DottedNameElaboration, AMemberOfAClasssBuiltInMethodResultIsJudged) {
  ElabFixture f;
  ElaborateSrc(
      "class K; endclass\n"
      "module top;\n"
      "  K k = new;\n"
      "  initial begin\n"
      "    void'(k.randomize().foo());\n"
      "    void'(k.get_randstate().foo());\n"
      "    void'(k.nope().foo());\n"
      "    void'(k.get_randstate().len());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "built-in method of the integral or real value", 5,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "built-in method of the string", 6, "6.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'K' has no member named 'nope'", 7, "8.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 3U);
}

TEST(DottedNameElaboration, AMemberOfASystemFunctionsResultIsJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int n = 5; int x;\n"
      "  initial begin\n"
      "    x = $clog2(8).foo;\n"
      "    void'($sformatf(\"%0d\", n).foo());\n"
      "    x = $sformatf(\"ab\")[0].foo;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "built-in method of the integral or real value", 4,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "built-in method of the string", 5, "6.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "built-in method of the integral or real value", 6,
                            "23.7"));
}

TEST(DottedNameElaboration, AMemberOfASystemFunctionsResultIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { int a; } s_t;\n"
      "  int n = 5; int x; s_t st;\n"
      "  initial begin\n"
      "    x = $sformatf(\"%0d\", n).len();\n"
      "    x = $typename(n).len();\n"
      "    x = $sampled(st).a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, AMemberAStructurePropertyLacksIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { int a; } s_t;\n"
      "  class C; s_t st; typedef struct { int b; } l_t; l_t ls; endclass\n"
      "  C h = new; int x;\n"
      "  initial begin\n"
      "    h.st.foo();\n"
      "    x = h.st.nope;\n"
      "    x = h.ls.nope;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 's_t' has no member named 'foo'", 6,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 's_t' has no member named 'nope'", 7,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the structure of 'ls' has no member named 'nope'",
                            8, "23.7"));
}

TEST(DottedNameElaboration, AMemberOfAStructurePropertyIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { int a; } s_t;\n"
      "  class C;\n"
      "    s_t st; typedef struct { int b; } l_t; l_t ls;\n"
      "    class N; int c; endclass\n"
      "    N n;\n"
      "  endclass\n"
      "  C h = new; int x;\n"
      "  initial x = h.st.a + h.ls.b + h.n.c;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, AMemberOfAnUndeclaredStructMemberIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { int a; } s_t;\n"
      "  s_t s; int x;\n"
      "  initial x = s.nope.y;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 's_t' has no member named 'nope'", 4,
                            "23.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 1U);
}

uint32_t LineOf(const std::string& src, std::string_view text) {
  std::string_view before(src.data(), src.find(text));
  return static_cast<uint32_t>(std::count(before.begin(), before.end(), '\n') +
                               1);
}

std::string ParameterSelectDesign(const std::string& context,
                                  const std::string& expr) {
  std::string body = context;
  body.replace(body.find('@'), 1, expr);
  return "module t;\n"
         "  typedef struct { int k; } n_t;\n"
         "  typedef struct { int a; n_t n; } s_t;\n"
         "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
         "  typedef union packed { logic [7:0] w; logic [7:0] v; } pu_t;\n"
         "  typedef union { int i; int j; } uu_t;\n"
         "  parameter s_t P = '{a: 1, n: '{k: 2}};\n"
         "  parameter ps_t PS = 8'h12;\n"
         "  parameter pu_t PU = 8'h3;\n"
         "  parameter uu_t UU = '{i: 4};\n"
         "  parameter s_t A [2] = '{'{a: 1, n: '{k: 2}}, '{a: 3, n: '{k: "
         "4}}};\n" +
         body + "endmodule\n";
}

constexpr const char* kParameterSelectContexts[] = {
    "  parameter int Q = @;\n", "  localparam int Q = @;\n",
    "  logic [@:0] q;\n", "  if (@) begin : g\n  end\n",
    "  int n;\n  initial n = @;\n"};

void ExpectReportedInEveryContext(const std::string& expr,
                                  const std::string& message,
                                  const char* subclause) {
  for (const char* context : kParameterSelectContexts) {
    SCOPED_TRACE(context);
    ElabFixture f;
    std::string src = ParameterSelectDesign(context, expr);
    ElaborateSrc(src, f, "t");
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, LineOf(src, expr),
                              subclause));
  }
}

TEST(ParameterMemberSelects, DISABLED_AnUnpackedStructuresMissingMember) {
  ExpectReportedInEveryContext(
      "P.zz", "structure 's_t' has no member named 'zz'", "23.7");
}

TEST(ParameterMemberSelects, DISABLED_ANestedStructuresMissingMember) {
  ExpectReportedInEveryContext(
      "P.n.zz", "structure 'n_t' has no member named 'zz'", "23.7");
}

TEST(ParameterMemberSelects, DISABLED_APackedStructuresMissingMember) {
  ExpectReportedInEveryContext(
      "PS.zz", "structure 'ps_t' has no member named 'zz'", "23.7");
}

TEST(ParameterMemberSelects, DISABLED_APackedUnionsMissingMember) {
  ExpectReportedInEveryContext("PU.zz", "union 'pu_t' has no member named 'zz'",
                               "23.7");
}

TEST(ParameterMemberSelects, DISABLED_AnUnpackedUnionsMissingMember) {
  ExpectReportedInEveryContext("UU.zz", "union 'uu_t' has no member named 'zz'",
                               "23.7");
}

TEST(ParameterMemberSelects, DISABLED_AnArrayElementsMissingMember) {
  ExpectReportedInEveryContext(
      "A[0].zz", "structure 's_t' has no member named 'zz'", "23.7");
}

TEST(ParameterMemberSelects, DISABLED_AMemberSelectOfTheArrayItself) {
  ExpectReportedInEveryContext(
      "A.a", "'a' is not a built-in method of the fixed-size array 'A'",
      "7.12");
}

TEST(ParameterMemberSelects, DeclaredMembersAreAcceptedInEveryContext) {
  for (const char* expr :
       {"P.a", "P.n.k", "PS.lo", "PU.w", "UU.i", "A[0].a", "A[1].n.k"}) {
    for (const char* context : kParameterSelectContexts) {
      SCOPED_TRACE(std::string(expr) + " in " + context);
      ElabFixture f;
      ElaborateSrc(ParameterSelectDesign(context, expr), f, "t");
      EXPECT_FALSE(f.has_errors);
    }
  }
}

constexpr const char* kStructParameter =
    "  typedef struct { int a; } s_t;\n"
    "  parameter s_t P = '{a: 1};\n";

std::string ParameterInAPlace(const std::string& place,
                              const std::string& member) {
  std::string decl = kStructParameter;
  if (place == "interface") {
    return "interface ifc;\n" + decl + "  localparam int Q = P." + member +
           ";\nendinterface\nmodule t;\n  ifc i();\nendmodule\n";
  }
  if (place == "program") {
    return "program prg;\n" + decl + "  localparam int Q = P." + member +
           ";\nendprogram\nmodule t;\n  prg p();\nendmodule\n";
  }
  if (place == "generate block") {
    return "module t;\n  if (1) begin : g\n" + decl +
           "  localparam int Q = P." + member + ";\n  end\nendmodule\n";
  }
  if (place == "package") {
    return "package pk;\n" + decl +
           "endpackage\nmodule t;\n  localparam int Q = pk::P." + member +
           ";\nendmodule\n";
  }
  if (place == "unit scoped") {
    return decl + "module t;\n  localparam int Q = $unit::P." + member +
           ";\nendmodule\n";
  }
  if (place == "unit bare") {
    return decl + "module t;\n  localparam int Q = P." + member +
           ";\nendmodule\n";
  }
  return "module t;\n  class C;\n" + decl +
         "  endclass\n  localparam int Q = C::P." + member + ";\nendmodule\n";
}

void ExpectMissingMemberReportedIn(const std::string& place) {
  ElabFixture f;
  std::string src = ParameterInAPlace(place, "zz");
  ElaborateSrc(src, f, "t");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 's_t' has no member named 'zz'",
                            LineOf(src, "zz"), "23.7"));
}

TEST(ParameterMemberSelectPlaces, DISABLED_AnInterfacesParameter) {
  ExpectMissingMemberReportedIn("interface");
}

TEST(ParameterMemberSelectPlaces, DISABLED_AProgramsParameter) {
  ExpectMissingMemberReportedIn("program");
}

TEST(ParameterMemberSelectPlaces, DISABLED_AGenerateBlocksParameter) {
  ExpectMissingMemberReportedIn("generate block");
}

TEST(ParameterMemberSelectPlaces, DISABLED_APackagesParameter) {
  ExpectMissingMemberReportedIn("package");
}

TEST(ParameterMemberSelectPlaces, DISABLED_AUnitParameterThroughUnitScope) {
  ExpectMissingMemberReportedIn("unit scoped");
}

TEST(ParameterMemberSelectPlaces, DISABLED_AUnitParameterByItsBareName) {
  ExpectMissingMemberReportedIn("unit bare");
}

TEST(ParameterMemberSelectPlaces, DISABLED_AClasssParameter) {
  ExpectMissingMemberReportedIn("class");
}

TEST(ParameterMemberSelectPlaces, ADeclaredMemberIsAcceptedInEveryPlace) {
  for (const char* place : {"interface", "program", "generate block", "package",
                            "unit scoped", "unit bare", "class"}) {
    SCOPED_TRACE(place);
    ElabFixture f;
    ElaborateSrc(ParameterInAPlace(place, "a"), f, "t");
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(DottedNameMemberSelects, DISABLED_APackageSubroutineStructsMissingMember) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n  typedef struct { int a; } st;\n"
      "  function int g();\n    st s;\n    return s.zz;\n  endfunction\n"
      "endpackage\nmodule t;\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'st' has no member named 'zz'", 5,
                            "23.7"));
}

TEST(DottedNameMemberSelects, DISABLED_AnInterfacePortsMissingMember) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n  logic a;\nendinterface\n"
      "module m(ifc p);\n  logic r;\n  initial r = p.nosuch;\nendmodule\n"
      "module t;\n  ifc i();\n  m u(i);\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface 'ifc' has no member named 'nosuch'", 6,
                            "23.7"));
}

TEST(DottedNameMemberSelects, AnInterfacePortsDeclaredMemberIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n  logic a;\nendinterface\n"
      "module m(ifc p);\n  logic r;\n  initial r = p.a;\nendmodule\n"
      "module t;\n  ifc i();\n  m u(i);\nendmodule\n",
      f, "t");
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameMemberSelects, DISABLED_ACovergroupObjectsMissingMember) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n  logic clk;\n  covergroup cg @(posedge clk);\n"
      "    coverpoint clk;\n  endgroup\n  cg c = new;\n  int r;\n"
      "  initial r = c.nosuch;\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "covergroup 'cg' has no member named 'nosuch'", 8,
                            "23.7"));
}

TEST(DottedNameMemberSelects, ACovergroupObjectsMethodIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n  logic clk;\n  covergroup cg @(posedge clk);\n"
      "    coverpoint clk;\n  endgroup\n  cg c = new;\n  real r;\n"
      "  initial r = c.get_coverage();\nendmodule\n",
      f, "t");
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameMemberSelects, DISABLED_AScopeDeclaredAfterAnImportedName) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n  struct { int x; } s2;\nendpackage\n"
      "module t;\n  import p::*;\n  initial s2.x = 1;\n  int s2;\n"
      "endmodule\n",
      f, "t");
  const std::vector<Diagnostic>& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "declaration of 's2' follows a reference resolved "
                            "through a wildcard package import",
                            7, "26.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(DottedNameMemberSelects, DISABLED_AnImportedFunctionsMissingMember) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n  function void f();\n    static int x;\n  endfunction\n"
      "endpackage\nmodule t;\n  import p::f;\n  int r;\n"
      "  initial r = f.nosuch;\nendmodule\n",
      f, "t");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "hierarchical reference 'p::f.nosuch' is unresolved: "
                    "'nosuch' is not declared in function 'f'",
                    9, "23.7"));
}

}  // namespace
