#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(EnumNameMethod, NameOfMiddleMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = GREEN;
    s = c.name();
    r = (s == "GREEN");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfFirstMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = RED;
    s = c.name();
    r = (s == "RED");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfLastMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = BLUE;
    s = c.name();
    r = (s == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfSingleMemberEnum) {
  const char* src = R"(
module m;
  typedef enum { SOLE } one_t;
  one_t o;
  string s;
  int r;
  initial begin
    o = SOLE;
    s = o.name();
    r = (s == "SOLE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfDefaultInitializedIsFirstMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    s = c.name();
    r = (s == "RED");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfDeclarationInitializedMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c = GREEN;
  string s;
  int r;
  initial begin
    s = c.name();
    r = (s == "GREEN");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameWithExplicitBaseType) {
  const char* src = R"(
module m;
  typedef enum bit [2:0] { A, B, C, D } e_t;
  e_t v;
  string s;
  int r;
  initial begin
    v = C;
    s = v.name();
    r = (s == "C");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameWithExplicitMemberValues) {
  const char* src = R"(
module m;
  typedef enum { LOW = 2, MID = 50, HIGH = 9999 } sparse_t;
  sparse_t v;
  string s;
  int r;
  initial begin
    v = MID;
    s = v.name();
    r = (s == "MID");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameFromCastToMemberValue) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = color_t'(2);
    s = c.name();
    r = (s == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfRangeExpandedMember) {
  const char* src = R"(
module m;
  typedef enum { OP[3] } op_t;
  op_t v;
  string s;
  int r;
  initial begin
    v = OP1;
    s = v.name();
    r = (s == "OP1");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameResultUsedDirectlyAsOperand) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = (c.name() == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameResultAsDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string nm = c.name();
  int r;
  initial r = (nm == "RED");
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfNonMemberIsEmpty) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = color_t'(99);
    s = c.name();
    r = (s == "");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfNonMemberIsNotAMemberName) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = color_t'(7);
    s = c.name();
    r = (s == "RED");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

TEST(EnumNameMethod, NameOfNextCallResult) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = GREEN;
    r = (c.next().name() == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfLastCallResult) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = (c.last().name() == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfFirstCallResultOnLastMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = (c.first().name() == "RED");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfPrevCallResult) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = (c.prev().name() == "GREEN");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfNextCallResultWithStepCount) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE, YELLOW } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = (c.next(2).name() == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfFirstThenNextChain) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = (c.first().next().name() == "GREEN");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NextChainedOnNextResult) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE, YELLOW } color_t;
  color_t c;
  int r;
  initial begin
    c = GREEN;
    r = (c.next().next() == YELLOW);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfNextCallResultInClassMethod) {
  const char* src = R"(
package p;
  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL } uvm_severity;
endpackage
import p::*;
class rep;
  function int check();
    uvm_severity s;
    s = s.first();
    return (s.next().name() == "UVM_WARNING");
  endfunction
endclass
module m;
  int r;
  initial begin
    rep h;
    h = new;
    r = h.check();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfLastCallResultInClassMethod) {
  const char* src = R"(
package p;
  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL } uvm_severity;
endpackage
import p::*;
class rep;
  function int check();
    uvm_severity s;
    s = s.first();
    return (s.last().name() == "UVM_FATAL");
  endfunction
endclass
module m;
  int r;
  initial begin
    rep h;
    h = new;
    r = h.check();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumNameMethod, NameOfNextCallResultWithStepCountInClassMethod) {
  const char* src = R"(
package p;
  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL } uvm_severity;
endpackage
import p::*;
class rep;
  function int check();
    uvm_severity sev;
    sev = UVM_WARNING;
    return (sev.next(2).name() == "UVM_FATAL");
  endfunction
endclass
module m;
  int r;
  initial begin
    rep h;
    h = new;
    r = h.check();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(EnumMethodNameSim, EnumTypedModuleParameterNamesItsValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("typedef enum {RED, GREEN, BLUE} color_t;\n"
                 "module sub #(parameter color_t P = RED);\n"
                 "  initial #1 $display(\"sub %s\", P.name());\n"
                 "endmodule\n"
                 "module t;\n"
                 "  parameter color_t PE = GREEN;\n"
                 "  localparam color_t LE = RED;\n"
                 "  sub #(.P(BLUE)) u();\n"
                 "  initial $display(\"%s %s %0d %s\", PE.name(), LE.name(),\n"
                 "                   PE.num(), PE.next().name());\n"
                 "endmodule\n",
                 f),
      "GREEN RED 3 BLUE\nsub BLUE\n");
}

TEST(EnumMethodNameSim, EnumTypedClassParameterNamesItsValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef enum {RED, GREEN, BLUE} color_t;\n"
          "module t;\n"
          "  class N #(color_t EC = GREEN);\n"
          "    function string ec(); return EC.name(); endfunction\n"
          "    function string nx(); return EC.next().name(); endfunction\n"
          "  endclass\n"
          "  N n; N #(RED) r;\n"
          "  initial begin\n"
          "    n = new; r = new;\n"
          "    $display(\"%s %s %s %s\", n.ec(), r.ec(), n.nx(), r.nx());\n"
          "  end\n"
          "endmodule\n",
          f),
      "GREEN RED BLUE GREEN\n");
}

TEST(EnumMethodNameSim, EveryVariableOfAnInlineEnumListIsOfTheEnum) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  enum {d, e, f} u, w, x;\n"
                       "  initial begin\n"
                       "    u = e; w = f; x = d;\n"
                       "    $display(\"%s %s %s %s %s %0d %0d\", u.name(),\n"
                       "             w.name(), x.name(), w.next().name(),\n"
                       "             x.next().name(), w.num(), x.num());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "e f d d e 3 3\n");
}

TEST(EnumMethodNameSim, NameOfAnXOrZMember) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  enum integer {IDLE, XX='x, S1='b01, S2='b10} s;\n"
                       "  enum logic [1:0] {A, Z='z, B=2} lz;\n"
                       "  enum integer {P, Q} u;\n"
                       "  initial begin\n"
                       "    s = XX; lz = Z;\n"
                       "    $display(\"%s %s %s [%s]\", s.name(), lz.name(),\n"
                       "             lz.next().name(), u.name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "XX Z B []\n");
}

TEST(EnumNameMethod, AnInlineEnumClassPropertyHasItsEnumerationsMethods) {
  SimFixture f;
  auto out = RunCapture(
      "class K;\n"
      "  enum {x1, x2, x3, x4} e;\n"
      "  function void show(); e = x3; $display(\"%s %0d\", e.name(), "
      "e.num()); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic K k = new;\n"
      "    k.show();\n"
      "    $display(\"%s %0d\", k.e.name(), k.e.num());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x3 4\nx3 4\n");
}

TEST(EnumNameMethod, ATypedefOfAnEnumTypedefHasItsEnumerationsMethods) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum {Y, N} choice;\n"
      "  typedef choice alias_t;\n"
      "  typedef alias_t alias2_t;\n"
      "  alias_t d = N;\n"
      "  alias2_t e = Y;\n"
      "  initial $display(\"%s %0d %s\", d.name(), d.num(), e.name());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "N 2 Y\n");
}

TEST(EnumNameMethod, AnEnumVariableReachedHierarchicallyHasItsMethods) {
  SimFixture f;
  auto out = RunCapture(
      "module sub;\n"
      "  initial #1 $display(\"%s %s\", t.c.name(), t.c.next().name());\n"
      "endmodule\n"
      "module t;\n"
      "  typedef enum {Y, N, M} choice;\n"
      "  choice c = N;\n"
      "  sub s();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "N M\n");
}

}  // namespace
