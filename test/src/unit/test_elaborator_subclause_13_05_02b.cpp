#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

using LineAndReport = std::pair<const char*, const char*>;

void ExpectEachReported(const std::string& src,
                        std::initializer_list<LineAndReport> cases,
                        const char* subclause) {
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const auto& [text, report] : cases) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), report,
                              LineHolding(src, text), subclause))
        << text;
  }
}

void ExpectNoneOfTheseReported(const std::string& src,
                               std::initializer_list<const char*> lines) {
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const char* text : lines) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, text)))
        << text;
  }
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

constexpr const char* kNotEquivalent = "whose data type is not equivalent";

std::string EquivalenceSrc(const std::string& callee) {
  return "module m;\n"
         "  typedef int myint;\n"
         "  byte b;\n"
         "  logic [31:0] l;\n"
         "  integer ig;\n"
         "  bit signed [31:0] bs;\n"
         "  myint mi;\n" +
         callee +
         "  initial begin\n"
         "    s(b);\n"
         "    s(l);\n"
         "    s(ig);\n"
         "    s(bs);\n"
         "    s(mi);\n"
         "  end\n"
         "endmodule\n";
}

TEST(PassByRefValidation, AFunctionRefActualOfEachNonEquivalentTypeIsReported) {
  ExpectEachReported(
      EquivalenceSrc("  function automatic void s(ref int x); endfunction\n"),
      {{"s(b);", kNotEquivalent},
       {"s(l);", kNotEquivalent},
       {"s(ig);", kNotEquivalent}},
      "13.5.2");
}

TEST(PassByRefValidation, AnEquivalentActualOfARefFormalIsAccepted) {
  const char* function_callee =
      "  function automatic void s(ref int x); endfunction\n";
  const char* task_callee = "  task automatic s(ref int x); endtask\n";
  ExpectNoneOfTheseReported(EquivalenceSrc(function_callee),
                            {"s(bs);", "s(mi);"});
  ExpectNoneOfTheseReported(EquivalenceSrc(task_callee), {"s(bs);", "s(mi);"});
}

TEST(PassByRefValidation,
     DISABLED_ATaskRefActualOfEachNonEquivalentTypeIsReported) {
  ExpectEachReported(EquivalenceSrc("  task automatic s(ref int x); endtask\n"),
                     {{"s(b);", kNotEquivalent},
                      {"s(l);", kNotEquivalent},
                      {"s(ig);", kNotEquivalent}},
                     "13.5.2");
}

TEST(PassByRefValidation,
     DISABLED_AnElementActualOfANonEquivalentTypeIsReported) {
  ExpectEachReported(
      "module m;\n"
      "  typedef bit [3:0] nib;\n"
      "  typedef bit [7:0] octet;\n"
      "  nib q [$];\n"
      "  byte ba [4];\n"
      "  byte aa [int];\n"
      "  function automatic void fo(ref octet e); endfunction\n"
      "  task automatic ti(ref int x); endtask\n"
      "  initial begin\n"
      "    fo(q[0]);\n"
      "    ti(ba[1]);\n"
      "    ti(aa[2]);\n"
      "  end\n"
      "endmodule\n",
      {{"fo(q[0]);", kNotEquivalent},
       {"ti(ba[1]);", kNotEquivalent},
       {"ti(aa[2]);", kNotEquivalent}},
      "13.5.2");
}

TEST(PassByRefValidation, AnElementActualOfAnEquivalentTypeIsAccepted) {
  ExpectAccepted(
      "module m;\n"
      "  typedef bit [7:0] octet;\n"
      "  octet q [$];\n"
      "  int ia [4];\n"
      "  int aa [int];\n"
      "  function automatic void fo(ref bit [7:0] e); endfunction\n"
      "  task automatic ti(ref int x); endtask\n"
      "  initial begin\n"
      "    fo(q[0]);\n"
      "    ti(ia[1]);\n"
      "    ti(aa[2]);\n"
      "  end\n"
      "endmodule\n");
}

std::string ActualKindSrc(const std::string& callee) {
  return "class C;\n"
         "  int p;\n"
         "endclass\n"
         "module m;\n"
         "  typedef struct { int a; } us_t;\n"
         "  typedef struct packed { int a; } ps_t;\n"
         "  typedef union packed { int a; bit [31:0] b; } pu_t;\n"
         "  int x, y;\n"
         "  int ia [4];\n"
         "  us_t us;\n"
         "  ps_t ps;\n"
         "  pu_t pu;\n"
         "  C c = new();\n"
         "  function int g(); return 1; endfunction\n" +
         callee +
         "  initial begin\n"
         "    s(x + y);\n"
         "    s(5);\n"
         "    s(g());\n"
         "    s(x);\n"
         "    s(c.p);\n"
         "    s(us.a);\n"
         "    s(ia[1]);\n"
         "    s(ps.a);\n"
         "    s(pu.b);\n"
         "  end\n"
         "endmodule\n";
}

TEST(PassByRefValidation, AnExpressionLiteralOrCallResultRefActualIsReported) {
  for (const char* callee :
       {"  function automatic void s(ref int r); endfunction\n",
        "  task automatic s(ref int r); endtask\n"}) {
    ExpectEachReported(ActualKindSrc(callee),
                       {{"s(x + y);",
                         "ref argument 'r' of 's' requires a "
                         "variable"},
                        {"s(5);",
                         "ref argument 'r' of 's' requires a "
                         "variable"},
                        {"s(g());",
                         "ref argument 'r' of 's' requires a "
                         "variable"}},
                       "13.5.2");
  }
}

TEST(PassByRefValidation,
     AVariablePropertyUnpackedMemberOrElementRefActualIsAccepted) {
  for (const char* callee :
       {"  function automatic void s(ref int r); endfunction\n",
        "  task automatic s(ref int r); endtask\n"}) {
    ExpectNoneOfTheseReported(ActualKindSrc(callee),
                              {"s(x);", "s(c.p);", "s(us.a);", "s(ia[1]);"});
  }
}

TEST(PassByRefValidation,
     DISABLED_APackedStructOrUnionMemberRefActualIsReported) {
  ExpectEachReported(
      ActualKindSrc("  task automatic s(ref int r); endtask\n"),
      {{"s(ps.a);", "cannot be passed by reference to argument 'r' of 's'"},
       {"s(pu.b);", "cannot be passed by reference to argument 'r' of 's'"}},
      "13.5.2");
}

TEST(PassByRefValidation, ARefFormalOfAStaticSubroutineIsReportedInEachScope) {
  ExpectEachReported(
      "module m;\n"
      "  task t1(ref int v1); endtask\n"
      "  function void f1(ref int r1); endfunction\n"
      "  function void f2(const ref int r2); endfunction\n"
      "  task static t2(ref int v2); endtask\n"
      "endmodule\n"
      "interface i;\n"
      "  task ti(ref int vi); endtask\n"
      "  function void fi(ref int ri); endfunction\n"
      "endinterface\n"
      "program p;\n"
      "  task tp(ref int vp); endtask\n"
      "  function void fp(ref int rp); endfunction\n"
      "endprogram\n"
      "module automatic ma;\n"
      "  task static ts(ref int vs); endtask\n"
      "endmodule\n"
      "module top;\n"
      "  i ii();\n"
      "  m um();\n"
      "  p up();\n"
      "  ma uma();\n"
      "endmodule\n",
      {{"t1(", "ref argument 'v1' not allowed in static subroutine 't1'"},
       {"f1(", "ref argument 'r1' not allowed in static subroutine 'f1'"},
       {"f2(", "ref argument 'r2' not allowed in static subroutine 'f2'"},
       {"t2(", "ref argument 'v2' not allowed in static subroutine 't2'"},
       {"ti(", "ref argument 'vi' not allowed in static subroutine 'ti'"},
       {"fi(", "ref argument 'ri' not allowed in static subroutine 'fi'"},
       {"tp(", "ref argument 'vp' not allowed in static subroutine 'tp'"},
       {"fp(", "ref argument 'rp' not allowed in static subroutine 'fp'"},
       {"ts(", "ref argument 'vs' not allowed in static subroutine 'ts'"}},
      "13.5.2");
}

TEST(PassByRefValidation,
     DISABLED_ARefFormalOfAStaticPackageSubroutineIsReported) {
  ExpectEachReported(
      "package pk;\n"
      "  task tk(ref int vk); endtask\n"
      "  function void fk(ref int rk); endfunction\n"
      "endpackage\n"
      "module top;\n"
      "  import pk::*;\n"
      "endmodule\n",
      {{"tk(", "ref argument 'vk' not allowed in static subroutine 'tk'"},
       {"fk(", "ref argument 'rk' not allowed in static subroutine 'fk'"}},
      "13.5.2");
}

TEST(PassByRefValidation, DISABLED_ARefStaticFormalOfAStaticTaskIsReported) {
  ExpectEachReported(
      "module m;\n"
      "  task t(ref static int a, b); endtask\n"
      "endmodule\n",
      {{"t(", "ref argument 'a' not allowed in static subroutine 't'"},
       {"t(", "ref argument 'b' not allowed in static subroutine 't'"}},
      "13.5.2");
}

TEST(PassByRefValidation,
     ARefFormalOfASubroutineAutomaticByItsScopeIsAccepted) {
  ExpectAccepted(
      "module automatic ma;\n"
      "  task t(ref int v); endtask\n"
      "  function void f(ref int r); endfunction\n"
      "endmodule\n"
      "package automatic pa;\n"
      "  task t(ref int v); endtask\n"
      "  function void f(ref int r); endfunction\n"
      "endpackage\n"
      "interface automatic ia;\n"
      "  task t(ref int v); endtask\n"
      "  function void f(ref int r); endfunction\n"
      "endinterface\n"
      "program automatic pga;\n"
      "  task t(ref int v); endtask\n"
      "  function void f(ref int r); endfunction\n"
      "endprogram\n"
      "module top;\n"
      "  ia ii();\n"
      "  ma uma();\n"
      "  pga upga();\n"
      "  import pa::*;\n"
      "endmodule\n");
}

constexpr const char* kTaskNba =
    "automatic task variable in nonblocking assignment";
constexpr const char* kTaskPca =
    "automatic task variable in procedural continuous assignment";
constexpr const char* kTaskEvent =
    "automatic task variable in intra-assignment event control of nonblocking "
    "assignment";
constexpr const char* kTaskTrace =
    "automatic task variable traced by system task";

std::string BarredContextTaskSrc(const std::string& qualifier) {
  return "module m;\n"
         "  logic [7:0] w;\n"
         "  task automatic t(" +
         qualifier +
         " logic [7:0] r);\n"
         "    r <= 1;\n"
         "    r[0] <= 1;\n"
         "    r[3:2] <= 2'b1;\n"
         "    assign r = 0;\n"
         "    force r = 1;\n"
         "    assign w = r;\n"
         "    force w = r;\n"
         "    w <= @(r) 3;\n"
         "    w <= repeat (2) @(r) 4;\n"
         "    w <= @(w iff r) 5;\n"
         "    $monitor(r);\n"
         "    $monitorb(r);\n"
         "    $monitorh(r);\n"
         "    $monitoro(r);\n"
         "    $dumpvars(0, r);\n"
         "    deassign r;\n"
         "    release r;\n"
         "  endtask\n"
         "endmodule\n";
}

TEST(PassByRefValidation, ARefFormalOfATaskIsReportedWhereAutomaticsAreBarred) {
  ExpectEachReported(BarredContextTaskSrc("ref"),
                     {{"r <= 1;", kTaskNba},
                      {"r[0] <= 1;", kTaskNba},
                      {"r[3:2] <= 2'b1;", kTaskNba},
                      {"assign r = 0;", kTaskPca},
                      {"force r = 1;", kTaskPca},
                      {"assign w = r;", kTaskPca},
                      {"force w = r;", kTaskPca},
                      {"w <= @(r) 3;", kTaskEvent},
                      {"w <= repeat (2) @(r) 4;", kTaskEvent},
                      {"w <= @(w iff r) 5;", kTaskEvent},
                      {"$monitor(r);", kTaskTrace},
                      {"$monitorb(r);", kTaskTrace},
                      {"$monitorh(r);", kTaskTrace},
                      {"$monitoro(r);", kTaskTrace},
                      {"$dumpvars(0, r);", kTaskTrace}},
                     "13.3.2");
}

TEST(PassByRefValidation, ADeassignOrReleaseOfARefFormalIsAccepted) {
  ExpectNoneOfTheseReported(BarredContextTaskSrc("ref"),
                            {"deassign r;", "release r;"});
}

TEST(PassByRefValidation,
     ARefFormalOfAClassTaskIsReportedWhereAutomaticsAreBarred) {
  const std::string kSrc =
      "class K;\n"
      "  logic [7:0] w;\n"
      "  task tm(ref logic [7:0] r);\n"
      "    assign r = 0;\n"
      "    w <= @(r) 3;\n"
      "  endtask\n"
      "endclass\n"
      "module top;\n"
      "  K k = new();\n"
      "endmodule\n";
  ExpectEachReported(
      kSrc, {{"assign r = 0;", kTaskPca}, {"w <= @(r) 3;", kTaskEvent}},
      "13.3.2");
}

TEST(PassByRefValidation,
     DISABLED_ARefFormalOfAFunctionIsReportedWhereAutomaticsAreBarred) {
  ExpectEachReported(
      "class K;\n"
      "  function void me(ref logic [7:0] r);\n"
      "    $monitor(r);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  logic [7:0] w;\n"
      "  K k = new();\n"
      "  function automatic void f(ref logic [7:0] r);\n"
      "    assign r = 0;\n"
      "    force r = 1;\n"
      "    assign w = r;\n"
      "    $monitor(r);\n"
      "    $dumpvars(0, r);\n"
      "  endfunction\n"
      "endmodule\n",
      {{"    $monitor(r);\n  endfunction", "traced by system task"},
       {"assign r = 0;", "in procedural continuous assignment"},
       {"force r = 1;", "in procedural continuous assignment"},
       {"assign w = r;", "in procedural continuous assignment"},
       {"    $monitor(r);\n    $dumpvars", "traced by system task"},
       {"$dumpvars(0, r);", "traced by system task"}},
      "13.5.2");
}

TEST(PassByRefValidation,
     DISABLED_ARefStaticFormalIsAcceptedWhereAutomaticsAreBarred) {
  ExpectAccepted(BarredContextTaskSrc("ref static"));
  ExpectAccepted(
      "module m;\n"
      "  logic [7:0] w;\n"
      "  function automatic void f(ref static logic [7:0] r);\n"
      "    r <= 1;\n"
      "    assign r = 0;\n"
      "    $monitor(r);\n"
      "  endfunction\n"
      "  task automatic tc(const ref static logic [7:0] r);\n"
      "    w <= @(r) 3;\n"
      "    $monitor(r);\n"
      "  endtask\n"
      "endmodule\n");
}

std::string RefStaticActualSrc(const std::string& callee) {
  return "class C;\n"
         "  int p;\n"
         "  static int sp;\n"
         "endclass\n"
         "package pk;\n"
         "  int pv;\n"
         "endpackage\n"
         "module m;\n"
         "  typedef struct { int a; } s_t;\n"
         "  int da [];\n"
         "  int q [$];\n"
         "  int aa [int];\n"
         "  int fa [4];\n"
         "  s_t sda [];\n"
         "  s_t ss;\n"
         "  int mv;\n"
         "  C c = new();\n" +
         callee +
         "  task automatic tr(ref int r); s(r); endtask\n"
         "  task automatic trs(ref static int r); s(r); endtask\n"
         "  task automatic tl;\n"
         "    static int sl;\n"
         "    int al;\n"
         "    s(sl);\n"
         "    s(al);\n"
         "  endtask\n"
         "  initial begin\n"
         "    s(da[0]);\n"
         "    s(q[0]);\n"
         "    s(aa[1]);\n"
         "    s(c.p);\n"
         "    s(sda[0].a);\n"
         "    s(C::sp);\n"
         "    s(c.sp);\n"
         "    s(fa[1]);\n"
         "    s(ss.a);\n"
         "    s(mv);\n"
         "    s(pk::pv);\n"
         "  end\n"
         "endmodule\n";
}

constexpr const char* kFunctionRefStatic =
    "  function automatic void s(ref static int x); endfunction\n";
constexpr const char* kTaskRefStatic =
    "  task automatic s(ref static int x); endtask\n";
constexpr const char* kNoStaticLifetime = "which has no static lifetime";

TEST(PassByRefValidation, ARefStaticFormalAcceptsAnActualOfStaticLifetime) {
  for (const char* callee : {kFunctionRefStatic, kTaskRefStatic}) {
    ExpectNoneOfTheseReported(RefStaticActualSrc(callee),
                              {"s(sl);", "s(C::sp);", "s(c.sp);", "s(fa[1]);",
                               "s(ss.a);", "s(mv);", "s(pk::pv);"});
  }
}

TEST(PassByRefValidation,
     DISABLED_ARefStaticFormalAcceptsAnotherRefStaticFormal) {
  for (const char* callee : {kFunctionRefStatic, kTaskRefStatic}) {
    ExpectNoneOfTheseReported(RefStaticActualSrc(callee),
                              {"task automatic trs("});
  }
}

TEST(PassByRefValidation,
     DISABLED_ARefStaticFormalRefusesADynamicElementOrInstanceProperty) {
  for (const char* callee : {kFunctionRefStatic, kTaskRefStatic}) {
    ExpectEachReported(RefStaticActualSrc(callee),
                       {{"s(da[0]);", kNoStaticLifetime},
                        {"s(q[0]);", kNoStaticLifetime},
                        {"s(aa[1]);", kNoStaticLifetime},
                        {"s(c.p);", kNoStaticLifetime},
                        {"s(sda[0].a);", kNoStaticLifetime}},
                       "13.5.2");
  }
}

TEST(PassByRefValidation,
     DISABLED_ATaskRefStaticFormalRefusesAnAutomaticActual) {
  ExpectEachReported(RefStaticActualSrc(kTaskRefStatic),
                     {{"s(al);", kNoStaticLifetime},
                      {"task automatic tr(", kNoStaticLifetime}},
                     "13.5.2");
}

TEST(PassByRefValidation,
     DISABLED_ARefStaticFormalRefusesAnInstancePropertyInsideAMethod) {
  ExpectEachReported(
      "class C;\n"
      "  int p;\n"
      "  function automatic void s(ref static int x);\n"
      "  endfunction\n"
      "  function void me();\n"
      "    s(p);\n"
      "    s(this.p);\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  C c = new();\n"
      "endmodule\n",
      {{"s(p);", kNoStaticLifetime}, {"s(this.p);", kNoStaticLifetime}},
      "13.5.2");
}

}  // namespace
