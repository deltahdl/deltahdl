#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>

#include "elaborator/nettype_uses.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

// --- What a resolution function may do with its argument (§6.6.7) ---

// The function shall neither write any part of its driver array nor resize it.
TEST(NettypeElaboration, ResolutionFunctionWritingItsDriverArrayRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    d[0] = 4'h0;\n"
      "    return d[1];\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' writes to or resizes "
                            "its driver array 'd'",
                            3, "6.6.7"));
}

TEST(NettypeElaboration, ResolutionFunctionResizingItsDriverArrayRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    logic [3:0] r = d[0];\n"
      "    d.delete();\n"
      "    return r;\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' writes to or resizes "
                            "its driver array 'd'",
                            4, "6.6.7"));
}

// The function shall have no side effects, and a write to a variable it does
// not declare is one: the count would depend on how often the simulator
// resolves the net. The write is reported whether it is an increment or one
// name of a concatenation on an assignment's left side.
TEST(NettypeElaboration, ResolutionFunctionWritingAModuleVariableRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int calls;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    logic [3:0] r = '0;\n"
      "    calls++;\n"
      "    {r, calls} = {r, calls};\n"
      "    foreach (d[i]) r |= d[i];\n"
      "    return r;\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' has a side effect: it "
                            "writes 'calls'",
                            5, "6.6.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' has a side effect: it "
                            "writes 'calls'",
                            6, "6.6.7"));
}

// The counterpart, the clause's own Tsum: it writes its local result through
// the function's name and a member of it, inside a foreach over the drivers,
// and reads the driver array alone. None of that is a write the rule forbids.
TEST(NettypeElaboration, ResolutionFunctionWritingOnlyItsOwnResultAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function automatic T Tsum(input T driver[]);\n"
      "    real acc;\n"
      "    acc = 0.0;\n"
      "    Tsum.field1 = 0.0;\n"
      "    foreach (driver[i]) Tsum.field1 += driver[i].field1;\n"
      "  endfunction\n"
      "  nettype T wTsum with Tsum;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A nonblocking assignment and a decrement write as an assignment and an
// increment do, so either one to a module variable is a side effect.
TEST(NettypeElaboration,
     ResolutionFunctionNonblockingOrDecrementWriteRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int calls;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    calls <= 1;\n"
      "    --calls;\n"
      "    return d[0];\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4U, 5U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "resolution function 'res' has a side effect: "
                              "it writes 'calls'",
                              line, "6.6.7"));
  }
}

// A call written as a statement writes nothing the rule names unless it is
// one of the methods that change an array in place: a system task, a plain or
// a package-scoped subroutine, and a method of another name all pass.
TEST(NettypeElaboration, ResolutionFunctionCallingWithoutWritingAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "package p;\n"
      "  function automatic void note(logic [3:0] v);\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  class C;\n"
      "    function void peek();\n"
      "    endfunction\n"
      "  endclass\n"
      "  function automatic void note(logic [3:0] v);\n"
      "  endfunction\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    C c = new;\n"
      "    $display(\"%h\", d[0]);\n"
      "    note(d[0]);\n"
      "    p::note(d[0]);\n"
      "    c.peek();\n"
      "    return d[0];\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A function with no argument has no driver array whose writes the body could
// be judged by; the count of its arguments is what is reported.
TEST(NettypeElaboration, ResolutionFunctionWithoutAnArgumentReportsItsCount) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  function logic res();\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  nettype logic nt with res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall take a single input argument", 5, "6.6.7"));
}

// A write through a package, a class scope, `$unit` or `$root` reaches
// something outside the function whatever the function declares, so each one
// is a side effect, named as it is written. The local `u` does not hide
// `$unit::u`.
TEST(NettypeElaboration, ResolutionFunctionWritingThroughAScopeRejected) {
  ElabFixture f;
  Elaborate(
      "package p;\n"
      "  int calls;\n"
      "  int q[$];\n"
      "endpackage\n"
      "int u;\n"
      "module m;\n"
      "  class C;\n"
      "    static int n;\n"
      "  endclass\n"
      "  int calls;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    int u;\n"
      "    p::calls = 1;\n"
      "    C::n++;\n"
      "    p::q.delete();\n"
      "    $unit::u = 1;\n"
      "    $root.m.calls[0] = 1'b1;\n"
      "    return d[0];\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string> kWrites[] = {{13, "p::calls"},
                                                      {14, "C::n"},
                                                      {15, "p::q"},
                                                      {16, "$unit::u"},
                                                      {17, "$root.m.calls"}};
  for (const auto& [line, name] : kWrites) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "resolution function 'res' has a side effect: "
                              "it writes '" +
                                  name + "'",
                              line, "6.6.7"));
  }
}

// --- Where a nettype may be named (§6.6.7) ---

// A nettype may be used only to declare a net, so it is refused as the type of
// a variable written with `var` or declared in a procedural block, of a
// structure member at any depth, of a function's return or a subroutine's
// argument, of a parameter in the body or the header, and of a cast. A net
// declared with it, a member of a package's type of the same name and a size
// cast are no such uses.
TEST(NettypeElaboration, NettypeNamedAsTheTypeOfAnythingButANetRejected) {
  ElabFixture f;
  ElaborateSrc(
      "nettype logic [3:0] cu_nt;\n"
      "package p;\n"
      "  typedef logic [3:0] nt;\n"
      "endpackage\n"
      "module top #(parameter cu_nt Q = 0, parameter int W = 1);\n"
      "  nettype logic [3:0] nt;\n"
      "  nt w;\n"
      "  var nt v;\n"
      "  typedef struct { int k; nt m; p::nt o; struct { nt n; } s; } s_t;\n"
      "  function nt f(nt a, int c); return a; endfunction\n"
      "  parameter nt P = 0;\n"
      "  parameter int R = 0;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    nt b;\n"
      "    s_t q;\n"
      "    x = nt'(x);\n"
      "    x = 4'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  struct NettypeUse {
    uint32_t line;
    std::string_view nettype;
    std::string_view use;
  };
  const NettypeUse kUses[] = {{5, "cu_nt", "parameter 'Q'"},
                              {8, "nt", "variable 'v'"},
                              {9, "nt", "member 'm'"},
                              {9, "nt", "member 'n'"},
                              {10, "nt", "the return of function 'f'"},
                              {10, "nt", "argument 'a' of 'f'"},
                              {11, "nt", "parameter 'P'"},
                              {15, "nt", "variable 'b'"},
                              {17, "nt", "a cast"}};
  for (const NettypeUse& u : kUses) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("nettype '{}' may declare only a net, and is named here "
                    "as the type of {}",
                    u.nettype, u.use),
        u.line, "6.6.7"));
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "type of member 'o'", 9, "6.6.7"));
  for (uint32_t line : {7U, 12U, 16U, 18U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "may declare only a net",
                               line, "6.6.7"));
  }
}

// A module-scope declaration written with `const` or a lifetime is a data
// declaration, so naming a nettype in one declares a variable, as `var` does.
// Inside a class the nettype is refused as a property's type, through a
// method, a typedef and a nested class alike, while a property of another
// type is accepted.
TEST(NettypeElaboration, NettypeNamedInAConstStaticOrClassDeclarationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  nettype logic [3:0] nt;\n"
      "  static nt s;\n"
      "  const nt c = 0;\n"
      "  class C;\n"
      "    nt p;\n"
      "    int i;\n"
      "    typedef struct { nt m; } t;\n"
      "    function nt get(nt a); return a; endfunction\n"
      "    class D;\n"
      "      nt q;\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kUses[] = {
      {3, "variable 's'"},
      {4, "variable 'c'"},
      {6, "property 'p'"},
      {8, "member 'm'"},
      {9, "the return of function 'get'"},
      {9, "argument 'a' of 'get'"},
      {11, "property 'q'"}};
  for (const auto& [line, use] : kUses) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("nettype 'nt' may declare only a net, and is named here "
                    "as the type of {}",
                    use),
        line, "6.6.7"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "may declare only a net", 7,
                             "6.6.7"));
}

// The compilation unit and a package are scopes no module's elaboration
// reaches, and a nettype is held to nets in them as in a module: refused as a
// structure member's, a variable's, a function's return, a class property's
// and a parameter's type, while a net declared with it, and a variable of
// another type, are accepted. Each scope is judged by the nettypes it declares.
TEST(NettypeElaboration, NettypeNamedAtUnitOrPackageScopeRejected) {
  ElabFixture f;
  ElaborateSrc(
      "nettype logic [3:0] nt;\n"
      "typedef struct { nt m; } s_t;\n"
      "var nt v;\n"
      "nt w;\n"
      "var int i;\n"
      "function nt f(); return 0; endfunction\n"
      "class C;\n"
      "  nt p;\n"
      "endclass\n"
      "package q;\n"
      "  nettype logic [1:0] pn;\n"
      "  const pn c = 0;\n"
      "  parameter pn P = 0;\n"
      "endpackage\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  const std::pair<uint32_t, std::string_view> kUses[] = {
      {2,
       "nettype 'nt' may declare only a net, and is named here as the "
       "type of member 'm'"},
      {3,
       "nettype 'nt' may declare only a net, and is named here as the "
       "type of variable 'v'"},
      {6,
       "nettype 'nt' may declare only a net, and is named here as the "
       "type of the return of function 'f'"},
      {8,
       "nettype 'nt' may declare only a net, and is named here as the "
       "type of property 'p'"},
      {12,
       "nettype 'pn' may declare only a net, and is named here as the "
       "type of variable 'c'"},
      {13,
       "nettype 'pn' may declare only a net, and is named here as the "
       "type of parameter 'P'"}};
  for (const auto& [line, message] : kUses) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "6.6.7"));
  }
  for (uint32_t line : {4U, 5U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "may declare only a net",
                               line, "6.6.7"));
  }
}

// --- A nettype's type or source named through a package (§6.6.7) ---

// A.2.2.1 lets a nettype's data type be written through a package, and the
// name means the type that package declares and no same-named one elsewhere:
// P's T is a structure of a real, which §6.6.7 admits, though the compilation
// unit declares a class T, which it would not (#7596).
TEST(NettypeElaboration, NettypeOfAPackageTypeIsJudgedAsThePackagesType) {
  ElabFixture f;
  Elaborate(
      "class T;\n"
      "endclass\n"
      "package P;\n"
      "  typedef struct { real r; } T;\n"
      "endpackage\n"
      "module m;\n"
      "  nettype P::T n;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The same reading rejects what the package declares: P's C is a class and
// P's DA a dynamic array, neither of which §6.6.7 admits, though nothing else
// in the design is named C or DA (#7596).
TEST(NettypeElaboration, NettypeOfAPackageClassOrDynamicArrayRejected) {
  ElabFixture f;
  Elaborate(
      "package P;\n"
      "  class C;\n"
      "  endclass\n"
      "  typedef real DA[];\n"
      "endpackage\n"
      "module m;\n"
      "  nettype P::C nc;\n"
      "  nettype P::DA nd;\n"
      "endmodule\n",
      f);
  for (const auto& [name, line] :
       {std::pair<std::string_view, int>{"nc", 7}, {"nd", 8}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::format("data type of user-defined nettype "
                                          "'{}' is not a legal nettype data "
                                          "type",
                                          name),
                              line, "6.6.7"));
  }
}

// A.2.1.3's renaming form may name its source through a package, and the new
// name is that package's nettype: pnt resolves through P's pres, though the
// module declares an nt of its own resolved by mres, and under §6.22.6 pnt
// matches P's nt alone, so a pass switch joining a net of pnt to one of the
// module's nt joins two different nettypes, which §28.8 reports (#7597).
TEST(NettypeElaboration, NettypeRenamingAPackagesNettypeIsThatNettype) {
  ElabFixture f;
  auto* design = Elaborate(
      "package P;\n"
      "  function automatic logic pres(input logic d[]);\n"
      "    return d[0] & d[1];\n"
      "  endfunction\n"
      "  nettype logic nt with pres;\n"
      "endpackage\n"
      "module m;\n"
      "  function automatic logic mres(input logic d[]);\n"
      "    return d[0] | d[1];\n"
      "  endfunction\n"
      "  nettype logic nt with mres;\n"
      "  nettype P::nt pnt;\n"
      "  pnt n;\n"
      "  nt w;\n"
      "  tran sw(n, w);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirNet* net = FindNet(design, "m", "n");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->resolve_func, "P::pres");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot connect different user-defined nettypes "
                            "('pnt' and 'nt')",
                            15, "28.8"));
}

// A package's declarations see each other by their bare names, so P's nt2,
// renaming P's nt, resolves through P's pres, as a module's nettype renaming
// nt2 through P does; P's tn, declared over P's typedef T, is a nettype of its
// own, with no resolution function (#7597).
TEST(NettypeElaboration, NettypeRenamingWithinAPackageIsReachedThroughIt) {
  ElabFixture f;
  auto* design = Elaborate(
      "package P;\n"
      "  function automatic logic pres(input logic d[]);\n"
      "    return d[0] & d[1];\n"
      "  endfunction\n"
      "  typedef logic T;\n"
      "  nettype logic nt with pres;\n"
      "  nettype nt nt2;\n"
      "  nettype T tn;\n"
      "endpackage\n"
      "module m;\n"
      "  nettype P::nt2 a2;\n"
      "  nettype P::tn atn;\n"
      "  a2 n;\n"
      "  atn w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirNet* n = FindNet(design, "m", "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->resolve_func, "P::pres");
  const RtlirNet* w = FindNet(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_user_nettype);
  EXPECT_EQ(w->resolve_func, "");
}

// A declaration naming a package's nettype through the package declares a net
// of that nettype: r is a net of P's rnt, and the real it carries is the
// nettype's data type, which §6.7.1's rule for a built-in net's data type does
// not judge (#7600).
TEST(NettypeElaboration, NetOfAPackageScopedNettypeIsANetOfThatNettype) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package P;\n"
      "  nettype real rnt;\n"
      "endpackage\n"
      "module m;\n"
      "  P::rnt r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirNet* net = FindNet(design, "m", "r");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_user_nettype);
  EXPECT_EQ(net->nettype_name, "P::rnt");
}

// A nettype written through its package, or through `$unit`, is the nettype
// it names wherever it is written, so naming one as the type of anything but a
// net is reported as naming it bare is, under the name it is written with: a
// structure member, a function's return and argument, a parameter, a class
// property, a procedural variable and a cast (#7601).
TEST(NettypeElaboration,
     NettypeWrittenThroughAScopeNamedAsANonNetTypeRejected) {
  ElabFixture f;
  ElaborateSrc(
      "package P;\n"
      "  nettype logic [3:0] nt;\n"
      "endpackage\n"
      "nettype logic [3:0] cu_nt;\n"
      "module top;\n"
      "  typedef struct { P::nt m; $unit::cu_nt k; } s_t;\n"
      "  function P::nt f(P::nt a); return a; endfunction\n"
      "  parameter P::nt Q = 0;\n"
      "  logic [3:0] x;\n"
      "  class C;\n"
      "    P::nt p;\n"
      "  endclass\n"
      "  initial begin\n"
      "    P::nt b;\n"
      "    $unit::cu_nt c;\n"
      "    x = P::nt'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  const std::pair<uint32_t, std::string_view> kUses[] = {
      {6,
       "'P::nt' may declare only a net, and is named here as the type of "
       "member 'm'"},
      {6,
       "'$unit::cu_nt' may declare only a net, and is named here as the "
       "type of member 'k'"},
      {7,
       "'P::nt' may declare only a net, and is named here as the type of "
       "the return of function 'f'"},
      {7,
       "'P::nt' may declare only a net, and is named here as the type of "
       "argument 'a' of 'f'"},
      {8,
       "'P::nt' may declare only a net, and is named here as the type of "
       "parameter 'Q'"},
      {11,
       "'P::nt' may declare only a net, and is named here as the type of "
       "property 'p'"},
      {14,
       "'P::nt' may declare only a net, and is named here as the type of "
       "variable 'b'"},
      {15,
       "'$unit::cu_nt' may declare only a net, and is named here as the "
       "type of variable 'c'"},
      {16,
       "'P::nt' may declare only a net, and is named here as the type of "
       "a cast"}};
  for (const auto& [line, message] : kUses) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "6.6.7"));
  }
}

// The same report at the compilation unit's scope and in another package, which
// reach P's nettype through P as a module does: a member of the unit's
// structure, the return of its function, its class's property, and a parameter
// of package Q (#7601).
TEST(NettypeElaboration, NettypeWrittenThroughAPackageAtUnitScopeRejected) {
  ElabFixture f;
  ElaborateSrc(
      "package P;\n"
      "  nettype logic [3:0] nt;\n"
      "endpackage\n"
      "typedef struct { P::nt m; } s_t;\n"
      "function P::nt f(); return 0; endfunction\n"
      "class C;\n"
      "  P::nt p;\n"
      "endclass\n"
      "package Q;\n"
      "  parameter P::nt R = 0;\n"
      "endpackage\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  const std::pair<uint32_t, std::string_view> kUses[] = {
      {4, "member 'm'"},
      {5, "the return of function 'f'"},
      {7, "property 'p'"},
      {10, "parameter 'R'"}};
  for (const auto& [line, use] : kUses) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("nettype 'P::nt' may declare only a net, and is named "
                    "here as the type of {}",
                    use),
        line, "6.6.7"));
  }
}

// A.2.8 lets a block or a subroutine body declare a nettype among its items,
// and §6.6.7's list of the data types a nettype may name holds wherever one is
// declared: a string and an event are refused in an initial block and in a
// function body, and the logic vector beside them is not.
TEST(NettypeElaboration, BlockNettypeIsHeldToTheLegalDataTypes) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    nettype string ns;\n"
      "    nettype logic [3:0] ok;\n"
      "  end\n"
      "  function int f;\n"
      "    nettype event ne;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kRefused[] = {{3, "ns"},
                                                            {7, "ne"}};
  for (const auto& [line, name] : kRefused) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("data type of user-defined nettype '{}' is not a legal "
                    "nettype data type",
                    name),
        line, "6.6.7"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "is not a legal nettype", 4,
                             "6.6.7"));
}

// A.1.9 makes a class_property a data_declaration, a nettype among them, and
// §6.6.7's list holds there too: a string in a class of the compilation unit
// and a chandle in a class a module declares are refused, and a real is not.
TEST(NettypeElaboration, ClassNettypeIsHeldToTheLegalDataTypes) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  nettype string ns;\n"
      "  nettype real ok;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  class D;\n"
      "    nettype chandle nc;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kRefused[] = {{2, "ns"},
                                                            {8, "nc"}};
  for (const auto& [line, name] : kRefused) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("data type of user-defined nettype '{}' is not a legal "
                    "nettype data type",
                    name),
        line, "6.6.7"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "is not a legal nettype", 3,
                             "6.6.7"));
}

// A nettype a begin-end block, a fork-join block or a task body declares is a
// nettype for the declarations after it there and in the blocks inside it, and
// a procedural block declares variables alone, so each declaration below
// names a nettype without declaring a net.
TEST(NettypeElaboration, BlockNettypeNamedAsAVariablesTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    nettype bit nb;\n"
      "    nb w;\n"
      "    begin\n"
      "      nb inner;\n"
      "    end\n"
      "  end\n"
      "  task t;\n"
      "    nettype logic [1:0] tn;\n"
      "    tn v;\n"
      "  endtask\n"
      "  initial fork\n"
      "    nettype real fr;\n"
      "    fr r;\n"
      "  join\n"
      "endmodule\n",
      f);
  const std::array<std::tuple<uint32_t, std::string_view, std::string_view>, 4>
      kUses = {{{4, "nb", "w"},
                {6, "nb", "inner"},
                {11, "tn", "v"},
                {15, "fr", "r"}}};
  for (const auto& [line, nettype, var] : kUses) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("nettype '{}' may declare only a net, and is named here "
                    "as the type of variable '{}'",
                    nettype, var),
        line, "6.6.7"));
  }
}

// A nettype a class declares is a nettype for the class's properties, for the
// variables its methods declare and for a class nested in it, none of which
// declares a net.
TEST(NettypeElaboration, ClassNettypeNamedAsAPropertysTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  nettype logic [3:0] nt;\n"
      "  nt v;\n"
      "  function void f();\n"
      "    nt local_v;\n"
      "  endfunction\n"
      "  class Inner;\n"
      "    nt q;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f, "m");
  const std::pair<uint32_t, std::string_view> kUses[] = {
      {3, "property 'v'"}, {5, "variable 'local_v'"}, {8, "property 'q'"}};
  for (const auto& [line, use] : kUses) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("nettype 'nt' may declare only a net, and is named here "
                    "as the type of {}",
                    use),
        line, "6.6.7"));
  }
}

// The walk over a subroutine body steps over a null statement on its way to
// the body's nettypes and the declarations after them.
// Parser::ParseSubroutineBody keeps whatever Parser::ParseStmt answers, null
// included, and no source the tests parse has it answer null, so the body is
// built here. The module declares no nettype of its own, which leaves the
// body's the only one, and the statements carry no source location, so the
// report stands at line 0.
TEST(NettypeElaboration, SubroutineBodyNettypeScanStepsOverANullStatement) {
  ElabFixture f;
  auto* nettype = f.arena.Create<ModuleItem>();
  nettype->kind = ModuleItemKind::kNettypeDecl;
  nettype->name = "nb";
  nettype->typedef_type.kind = DataTypeKind::kBit;
  auto* nettype_stmt = f.arena.Create<Stmt>();
  nettype_stmt->kind = StmtKind::kBlockItemDecl;
  nettype_stmt->decl_item = nettype;
  auto* decl = f.arena.Create<Stmt>();
  decl->kind = StmtKind::kVarDecl;
  decl->var_decl_type.kind = DataTypeKind::kNamed;
  decl->var_decl_type.type_name = "nb";
  decl->var_name = "w";
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "fn";
  func->func_body_stmts = {nullptr, nettype_stmt, decl};
  ModuleDecl mod;
  mod.items.push_back(func);
  const CompilationUnit kUnit{};
  CheckNettypeUses(&mod, kUnit, {}, f.diag);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nettype 'nb' may declare only a net, and is "
                            "named here as the type of variable 'w'",
                            0, "6.6.7"));
}

// A.2.2.1 lets a data_type name a type through a class_scope, so `C::nt` names
// the nettype class C declares, and a block variable, a cast, a function's
// return and argument, and a property of another class each name it without
// declaring a net.
TEST(NettypeElaboration, ClassNettypeNamedThroughItsScopeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  nettype logic [3:0] nt;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C::nt v;\n"
      "    int i;\n"
      "    i = int'(C::nt'(i));\n"
      "  end\n"
      "  function C::nt f(C::nt a);\n"
      "    return a;\n"
      "  endfunction\n"
      "endmodule\n"
      "class D;\n"
      "  C::nt p;\n"
      "endclass\n",
      f, "m");
  const std::pair<uint32_t, std::string_view> kUses[] = {
      {6, "variable 'v'"},
      {8, "a cast"},
      {10, "the return of function 'f'"},
      {10, "argument 'a' of 'f'"},
      {15, "property 'p'"}};
  for (const auto& [line, use] : kUses) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("nettype 'C::nt' may declare only a net, and is named "
                    "here as the type of {}",
                    use),
        line, "6.6.7"));
  }
}

// A.2.1.3 writes a net of a nettype with the nettype's bare name, so an item
// whose type names a class's nettype through the class's scope declares a
// variable among a package's, the unit's or a module's items, written with
// `var` or not, and a package's such variable is no net with an implicit
// continuous assignment.
TEST(NettypeElaboration, ItemNamingAClassNettypeThroughItsScopeIsAVariable) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  nettype logic [3:0] nt;\n"
      "endclass\n"
      "package P;\n"
      "  C::nt pw = 0;\n"
      "endpackage\n"
      "C::nt uw;\n"
      "module m;\n"
      "  C::nt w;\n"
      "  var C::nt vw;\n"
      "endmodule\n",
      f, "m");
  const std::pair<uint32_t, std::string_view> kVariables[] = {
      {5, "pw"}, {7, "uw"}, {9, "w"}, {10, "vw"}};
  for (const auto& [line, name] : kVariables) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("nettype 'C::nt' may declare only a net, and is named "
                    "here as the type of variable '{}'",
                    name),
        line, "6.6.7"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "net declaration with implicit continuous "
                             "assignment is not allowed in a package",
                             5, "26.2"));
}

}  // namespace
