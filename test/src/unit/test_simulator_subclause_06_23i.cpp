#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kDeclarations =
    "package pk; typedef logic [11:0] t; logic [8:0] w9; endpackage\n"
    "module m #(type T = int) ();\n"
    "  T x;\n"
    "  initial #1 $display(\"%m %0d\", $bits(x));\n"
    "endmodule\n"
    "module b;\n"
    "  parameter type T = int;\n"
    "  T x;\n"
    "  initial #1 $display(\"%m %0d\", $bits(x));\n"
    "endmodule\n"
    "interface ifc #(type T = int) ();\n"
    "  T x;\n"
    "  initial #1 $display(\"%m %0d\", $bits(x));\n"
    "endinterface\n"
    "program prg #(type T = int) ();\n"
    "  T x;\n"
    "  initial #1 $display(\"%m %0d\", $bits(x));\n"
    "endprogram\n";

std::string UnitDeclaring(std::string_view unit, std::string_view body,
                          std::string_view rest) {
  return std::string(unit).append(body).append("end").append(unit).append(rest);
}

std::string Printed(std::string_view source) {
  SimFixture f;
  return RunCapture(std::string(kDeclarations) + std::string(source), f);
}

TEST(TypeRefDefaultSim, PortListDefaultOfAModuleAnInterfaceAndAProgram) {
  for (const char* unit : {"module", "interface", "program"}) {
    SCOPED_TRACE(unit);
    EXPECT_EQ(Printed(UnitDeclaring(
                  unit,
                  " d #(type T = type(logic [6:0]), int P = 1,\n"
                  "     localparam type U = type(real)) ();\n"
                  "  T x;\n"
                  "  U y;\n"
                  "  initial #P $display(\"%0d %0d\", $bits(x), $bits(y));\n",
                  "\n"
                  "module top;\n"
                  "  d u();\n"
                  "  d #(byte, 2) v();\n"
                  "endmodule\n")),
              "7 64\n8 64\n");
  }
}

TEST(TypeRefDefaultSim, PortListDefaultOfATopLevelModule) {
  EXPECT_EQ(Printed("module top #(type T = type(logic [6:0]), U = T) ();\n"
                    "  T x;\n"
                    "  U y;\n"
                    "  initial $display(\"%0d %0d\", $bits(x), $bits(y));\n"
                    "endmodule\n"),
            "7 7\n");
}

TEST(TypeRefDefaultSim, PortListDefaultNamesAnEarlierParameterOrAPackage) {
  EXPECT_EQ(
      Printed("module d #(shortint P = 3, int W = 4, type T = type(P),\n"
              "           type U = type(pk::w9), V = type(T),\n"
              "           X = type(pk::t), Y = type(logic [W-1:0]),\n"
              "           Z = type(P + 40'b0)) ();\n"
              "  T a; U b; V c; X d; Y e; Z f;\n"
              "  initial #W $display(\"%0d %0d %0d %0d %0d %0d\", $bits(a),\n"
              "      $bits(b), $bits(c), $bits(d), $bits(e), $bits(f));\n"
              "endmodule\n"
              "module top;\n"
              "  d u();\n"
              "  d #(.W(6), .T(byte)) v();\n"
              "endmodule\n"),
      "16 9 16 12 4 40\n8 9 8 12 6 40\n");
}

TEST(TypeRefDefaultSim, PortListDefaultTypesAPort) {
  EXPECT_EQ(Printed("module d #(type T = type(logic [6:0])) (input T i);\n"
                    "  initial #1 $display(\"%0d %0d\", $bits(i), i);\n"
                    "endmodule\n"
                    "module top;\n"
                    "  logic [7:0] s = 200;\n"
                    "  d u(s);\n"
                    "endmodule\n"),
            "7 72\n");
}

TEST(TypeRefDefaultSim, BodyDefaultOfAModuleAnInterfaceAndAProgram) {
  for (const char* unit : {"module", "interface", "program"}) {
    SCOPED_TRACE(unit);
    EXPECT_EQ(
        Printed(UnitDeclaring(
            unit,
            " d;\n"
            "  logic [4:0] s;\n"
            "  parameter type T = type(s);\n"
            "  localparam type U = type(s + 8'b0), V = type(pk::w9),\n"
            "                  X = type(pk::t);\n"
            "  T a; U b; V c; X e;\n"
            "  initial $display(\"%0d %0d %0d %0d\", $bits(a), $bits(b),\n"
            "                   $bits(c), $bits(e));\n",
            "\nmodule top; d u(); endmodule\n")),
        "5 8 9 12\n");
  }
}

TEST(TypeRefDefaultSim, BodyDefaultOfAGenerateBlock) {
  EXPECT_EQ(Printed("module top;\n"
                    "  logic [4:0] s;\n"
                    "  if (1) begin : g\n"
                    "    logic [2:0] s;\n"
                    "    localparam type T = type(s), U = type(s + 4'b0);\n"
                    "    T a; U b;\n"
                    "    initial $display(\"%0d %0d\", $bits(a), $bits(b));\n"
                    "  end\n"
                    "endmodule\n"),
            "3 4\n");
}

TEST(TypeRefDefaultSim, BodyDefaultIsEachInstancesOwn) {
  EXPECT_EQ(Printed("module d #(int W = 4) ();\n"
                    "  logic [W-1:0] s;\n"
                    "  parameter type T = type(s);\n"
                    "  localparam type U = type(s + 2'b0), V = type({s, s});\n"
                    "  T a; U b; V c;\n"
                    "  initial #W $display(\"%0d %0d %0d\", $bits(a), $bits(b),"
                    " $bits(c));\n"
                    "endmodule\n"
                    "module top;\n"
                    "  d #(3) u();\n"
                    "  d #(5) v();\n"
                    "endmodule\n"),
            "3 3 6\n5 5 10\n");
}

TEST(TypeRefOverrideSim, OverridesNameAVariableAnExpressionOrAType) {
  EXPECT_EQ(Printed("module top;\n"
                    "  logic [4:0] n;\n"
                    "  m #(type(n)) u1();\n"
                    "  m #(.T(type(n + 8'b0))) u2();\n"
                    "  m #(type(logic [2:0])) u3();\n"
                    "  m #(type(pk::w9)) u4();\n"
                    "  m #(.T(type(pk::t))) u5();\n"
                    "  b #(type(n)) u6();\n"
                    "  b #(.T(type({n, n}))) u7();\n"
                    "  prg #(type(n)) u8();\n"
                    "  ifc #(.T(type(n[1:0]))) u9();\n"
                    "endmodule\n"),
            "top.u1 5\ntop.u2 8\ntop.u3 3\ntop.u4 9\ntop.u5 12\ntop.u6 5\n"
            "top.u7 10\ntop.u9 2\ntop.u8 5\n");
}

TEST(TypeRefOverrideSim, OverridesNameAStructureAMemberAnEnumerationOrAString) {
  EXPECT_EQ(
      Printed("module s #(type T = int) ();\n"
              "  T x;\n"
              "  initial begin\n"
              "    x.a = 9;\n"
              "    x.f = 1;\n"
              "    #2 $display(\"%0d %0d\", $bits(x), x);\n"
              "  end\n"
              "endmodule\n"
              "module t #(type T = int) ();\n"
              "  T x;\n"
              "  initial begin x = \"abc\"; #3 $display(x.toupper()); end\n"
              "endmodule\n"
              "module e;\n"
              "  parameter type T = int;\n"
              "  T x;\n"
              "  initial begin\n"
              "    x = x.last();\n"
              "    #4 $display(\"%0d %s\", $bits(x), x.name());\n"
              "  end\n"
              "endmodule\n"
              "module top;\n"
              "  typedef struct packed { logic [3:0] a; bit f; } s_t;\n"
              "  typedef enum logic [1:0] { E, F, G } e_t;\n"
              "  s_t sv; e_t ev; string str;\n"
              "  s #(type(sv)) u1();\n"
              "  t #(type(str)) u2();\n"
              "  e #(type(ev)) u3();\n"
              "  m #(type(sv.a)) u4();\n"
              "endmodule\n"),
      "top.u4 4\n5 19\n"
      "ABC\n2 G\n");
}

TEST(TypeRefOverrideSim, OverridesOfAnInstanceArray) {
  EXPECT_EQ(Printed("module top;\n"
                    "  logic [4:0] n;\n"
                    "  m #(type(n)) u [1:0] ();\n"
                    "endmodule\n"),
            "top.u[0] 5\ntop.u[1] 5\n");
}

TEST(TypeRefOverrideSim, OverridesInAGenerateBlockReadItsOwnVariable) {
  EXPECT_EQ(Printed("module top;\n"
                    "  logic [4:0] n;\n"
                    "  for (genvar i = 1; i < 3; i++) begin : g\n"
                    "    logic [i:0] n;\n"
                    "    m #(type(n)) u();\n"
                    "    b #(type(n + 1'b0)) v();\n"
                    "  end\n"
                    "endmodule\n"),
            "top.g[1].u 2\ntop.g[1].v 2\ntop.g[2].u 3\ntop.g[2].v 3\n");
}

TEST(TypeRefOverrideSim, OverridesReadAVariableOfTheParentsWidth) {
  EXPECT_EQ(Printed("module q #(int W = 4) ();\n"
                    "  logic [W-1:0] n;\n"
                    "  m #(type(n)) u();\n"
                    "  b #(type(n)) v();\n"
                    "  m #(type({n, n})) w();\n"
                    "endmodule\n"
                    "module top;\n"
                    "  q #(3) a();\n"
                    "  q #(5) c();\n"
                    "endmodule\n"),
            "top.a.u 3\ntop.a.v 3\ntop.a.w 6\n"
            "top.c.u 5\ntop.c.v 5\ntop.c.w 10\n");
}

TEST(TypeParameterSim, OverridesRangeIsReadInTheInstantiatingScope) {
  EXPECT_EQ(Printed("module c #(int W = 9, type T = int) ();\n"
                    "  T x;\n"
                    "  initial #1 $display(\"%m %0d\", $bits(x));\n"
                    "endmodule\n"
                    "module q #(int W = 4) ();\n"
                    "  typedef logic [W-1:0] w_t;\n"
                    "  typedef struct packed { logic [W-1:0] a; bit f; } s_t;\n"
                    "  m #(logic [W-1:0]) u1();\n"
                    "  m #(bit [1:0][W-1:0]) u2();\n"
                    "  m #(w_t) u3();\n"
                    "  m #(s_t) u4();\n"
                    "  b #(logic [W-1:0]) u5();\n"
                    "  b #(w_t) u6();\n"
                    "  b #(s_t) u7();\n"
                    "  c #(.T(logic [W-1:0])) u8();\n"
                    "endmodule\n"
                    "module top;\n"
                    "  q #(3) a();\n"
                    "  q #(5) d();\n"
                    "endmodule\n"),
            "top.a.u1 3\ntop.a.u2 6\ntop.a.u3 3\ntop.a.u4 4\ntop.a.u5 3\n"
            "top.a.u6 3\ntop.a.u7 4\ntop.a.u8 3\n"
            "top.d.u1 5\ntop.d.u2 10\ntop.d.u3 5\ntop.d.u4 6\ntop.d.u5 5\n"
            "top.d.u6 5\ntop.d.u7 6\ntop.d.u8 5\n");
}

TEST(TypeParameterSim, OverrideNamesTheTypeOfTheInstantiatingScope) {
  EXPECT_EQ(Printed("module c;\n"
                    "  typedef byte t;\n"
                    "  parameter type U = int;\n"
                    "  parameter type V = t;\n"
                    "  U x;\n"
                    "  V y;\n"
                    "  initial $display(\"%0d %0d\", $bits(x), $bits(y));\n"
                    "endmodule\n"
                    "module top;\n"
                    "  typedef logic [6:0] t;\n"
                    "  typedef logic [4:0] U;\n"
                    "  c #(t) u();\n"
                    "  c #(U, t) v();\n"
                    "endmodule\n"),
            "7 8\n5 7\n");
}

TEST(TypeParameterSim, DefaultNamesTheEarlierParameterOfItsOwnList) {
  EXPECT_EQ(Printed("module c #(type T = byte, U = T) ();\n"
                    "  U x;\n"
                    "  initial $display(\"%0d\", $bits(x));\n"
                    "endmodule\n"
                    "module top;\n"
                    "  typedef logic [6:0] T;\n"
                    "  c u();\n"
                    "  c #(T) v();\n"
                    "endmodule\n"),
            "8\n7\n");
}

TEST(TypeRefOverrideSim, OverridesOfAModuleBoundIntoAnother) {
  EXPECT_EQ(Printed("module top;\n"
                    "  logic [4:0] n;\n"
                    "endmodule\n"
                    "bind top m #(type(n)) u1();\n"
                    "bind top b #(.T(type(n + 8'b0))) u2();\n"),
            "top.u1 5\ntop.u2 8\n");
}

TEST(TypeRefOverrideSim, HierarchicalOperandIsReportedAndAMemberIsNot) {
  for (bool hierarchical : {true, false}) {
    for (const char* child : {"m", "b", "ifc", "prg"}) {
      SCOPED_TRACE(child);
      SimFixture f;
      ElaborateSrc(
          std::string(kDeclarations) +
              "module n; logic [4:0] v; endmodule\n"
              "module top;\n"
              "  n i();\n"
              "  struct packed { logic [4:0] v; } s;\n" +
              "  " + child +
              (hierarchical ? " #(type(i.v)) u();\n" : " #(type(s.v)) u();\n") +
              "endmodule\n",
          f);
      EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                              "type operator argument uses a hierarchical "
                              "reference, which the type operator does not "
                              "accept",
                              23, "6.23"),
                hierarchical);
      EXPECT_EQ(f.has_errors, hierarchical);
    }
  }
}

TEST(TypeRefDefaultSim, HierarchicalOperandIsReported) {
  for (const char* header : {"#(type T = type(n.v)) ();\n",
                             ";\n  parameter type T = type(n.v);\n"}) {
    SCOPED_TRACE(header);
    SimFixture f;
    ElaborateSrc(std::string("module m2; logic v; endmodule\nmodule top ") +
                     header + "  m2 n();\nendmodule\n",
                 f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "type operator argument uses a hierarchical "
                              "reference, which the type operator does not "
                              "accept",
                              header[0] == '#' ? 2 : 3, "6.23"));
  }
}

TEST(TypeRefDefaultSim, OperandThatNamesNothingIsReported) {
  for (const char* operand : {"nosuch", "nosuch + 1", "pk::nosuch + 1"}) {
    for (const char* header :
         {" #(type T = type($)) ();\n", ";\n  parameter type T = type($);\n"}) {
      SCOPED_TRACE(operand);
      std::string decl = header;
      decl.replace(decl.find('$'), 1, operand);
      SimFixture f;
      ElaborateSrc(
          std::string(kDeclarations) + "module top" + decl + "endmodule\n", f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "type parameter 'T' can only be set to a data "
                                "type, not a value expression",
                                header[0] == ';' ? 20 : 19, "6.20.3"));
    }
  }
}

TEST(TypeRefOverrideSim, OperandThatNamesNothingIsReported) {
  for (const char* child : {"m", "b", "ifc", "prg"}) {
    SCOPED_TRACE(child);
    SimFixture f;
    ElaborateSrc(std::string(kDeclarations) + "module top;\n  " + child +
                     " #(type(nosuch)) u();\nendmodule\n",
                 f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "parameter value assignment for type parameter "
                              "'T' of '" +
                                  std::string(child) + "' does not name a type",
                              20, "6.20.3"));
  }
}

TEST(TypeRefOverrideSim, OperandNamesAClassACovergroupAParameterOrALabel) {
  EXPECT_EQ(
      Printed("class C; int v = 5; endclass\n"
              "module c #(type T = int) ();\n"
              "  T x = new;\n"
              "  initial $display(\"%0d\", x.v);\n"
              "endmodule\n"
              "module g #(type T = int) ();\n"
              "  T x = new;\n"
              "  initial #1 $display(\"%0d\", x.get_inst_coverage() < 1);\n"
              "endmodule\n"
              "module top #(parameter shortint P = 3) ();\n"
              "  enum logic [2:0] { A, B } e;\n"
              "  C h;\n"
              "  bit v;\n"
              "  covergroup cg; coverpoint v; endgroup\n"
              "  wire [5:0] w;\n"
              "  function logic [9:0] f(); return 0; endfunction\n"
              "  c #(type(C)) u1();\n"
              "  c #(type(h)) u2();\n"
              "  g #(type(cg)) u3();\n"
              "  m #(type(P)) u4();\n"
              "  m #(type(A)) u5();\n"
              "  m #(type(w)) u6();\n"
              "  m #(type(f())) u7();\n"
              "endmodule\n"),
      "5\n5\n1\ntop.u4 16\ntop.u5 3\ntop.u6 6\ntop.u7 10\n");
}

TEST(TypeParameterSim, OverridesEnumerationKeepsItsMethods) {
  EXPECT_EQ(Printed("module e #(type T = int) ();\n"
                    "  T x;\n"
                    "  initial begin\n"
                    "    x = x.last();\n"
                    "    $display(\"%0d %s\", $bits(x), x.name());\n"
                    "  end\n"
                    "endmodule\n"
                    "module e2;\n"
                    "  parameter type T = int;\n"
                    "  T x;\n"
                    "  initial begin\n"
                    "    x = x.last();\n"
                    "    $display(\"%0d %s\", $bits(x), x.name());\n"
                    "  end\n"
                    "endmodule\n"
                    "module top;\n"
                    "  typedef enum logic [1:0] { E, F, G } e_t;\n"
                    "  e_t ev;\n"
                    "  e #(e_t) u1();\n"
                    "  e #(type(ev)) u2();\n"
                    "  e2 #(e_t) u3();\n"
                    "  e2 #(type(ev)) u4();\n"
                    "endmodule\n"),
            "2 G\n2 G\n2 G\n2 G\n");
}

TEST(TypeParameterSim, EnumerationPassesThroughAPackageAndALowerInstance) {
  EXPECT_EQ(Printed("package q; typedef enum logic [1:0] { E, F, G } e_t;\n"
                    "endpackage\n"
                    "module e #(type T = int) ();\n"
                    "  T x;\n"
                    "  initial begin\n"
                    "    x = x.last();\n"
                    "    $display(\"%0d %s\", $bits(x), x.name());\n"
                    "  end\n"
                    "endmodule\n"
                    "module n #(type T = int) (); e #(T) i(); endmodule\n"
                    "module top;\n"
                    "  import q::e_t;\n"
                    "  q::e_t v = q::F;\n"
                    "  initial #1 $display(\"%s\", v.name());\n"
                    "  e #(q::e_t) u1();\n"
                    "  e #(e_t) u2();\n"
                    "  e #(type(v)) u3();\n"
                    "  n #(e_t) u4();\n"
                    "endmodule\n"),
            "2 G\n2 G\n2 G\n2 G\nF\n");
}

TEST(TypeParameterSim, PackedArrayOfATypedefIsAnOverride) {
  EXPECT_EQ(Printed("module top;\n"
                    "  typedef logic [1:0] t;\n"
                    "  t [3:0] v;\n"
                    "  m #(t [3:0]) u1();\n"
                    "  m #(type(v)) u2();\n"
                    "  b #(t [3:0]) u3();\n"
                    "  b #(type(v)) u4();\n"
                    "endmodule\n"),
            "top.u1 8\ntop.u2 8\ntop.u3 8\ntop.u4 8\n");
}

TEST(TypeParameterSim, ValueIsNoOverrideAndAForwardTypedefIs) {
  for (const char* child : {"m", "b"}) {
    for (const char* value : {"3", "1 + 2", "type(t)", "t"}) {
      SCOPED_TRACE(value);
      SimFixture f;
      ElaborateSrc(std::string(kDeclarations) +
                       "module top;\n"
                       "  typedef t;\n  " +
                       child + " #(" + value +
                       ") u();\n"
                       "  typedef logic [3:0] t;\n"
                       "endmodule\n",
                   f);
      const bool kNamesType = value[0] == 't';
      EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                              "parameter value assignment for type parameter "
                              "'T' of '" +
                                  std::string(child) + "' does not name a type",
                              21, "6.20.3"),
                !kNamesType);
      EXPECT_EQ(f.has_errors, !kNamesType);
    }
  }
}

TEST(PackageTypedefSim, EnumerationImportedByNameKeepsItsMethods) {
  constexpr std::string_view kBody =
      "  e_t x;\n"
      "  initial begin\n"
      "    x = x.last();\n"
      "    $display(\"%0d %s\", x, x.name());\n"
      "  end\n";
  for (const char* unit : {"module", "interface", "program"}) {
    for (const char* header :
         {" d;\n  import q::e_t;\n", " d import q::e_t; ();\n"}) {
      SCOPED_TRACE(std::string(unit) + header);
      EXPECT_EQ(Printed("package q; typedef enum logic [1:0] { E, F, G } e_t;\n"
                        "endpackage\n" +
                        UnitDeclaring(unit, std::string(header).append(kBody),
                                      "\nmodule top; d u(); endmodule\n")),
                "2 G\n");
    }
  }
  EXPECT_EQ(Printed("package q; typedef enum logic [1:0] { E, F, G } e_t;\n"
                    "endpackage\n"
                    "import q::e_t;\n"
                    "module top;\n" +
                    std::string(kBody) + "endmodule\n"),
            "2 G\n");
}

TEST(PackageTypedefSim, EnumerationImportedByNameBringsNoLiterals) {
  EXPECT_EQ(Printed("package q; typedef enum { E, F } e_t; endpackage\n"
                    "module top;\n"
                    "  import q::e_t;\n"
                    "  int F = 7;\n"
                    "  initial $display(\"%0d %0d\", F, q::F);\n"
                    "endmodule\n"),
            "7 1\n");
  SimFixture f;
  ElaborateSrc(
      "package q; typedef enum { E, F } e_t; endpackage\n"
      "module top;\n"
      "  import q::e_t;\n"
      "  e_t x = F;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'F'", 4,
                            "23.9"));
}

TEST(PackageTypedefSim, RangeNamesTheParameterOfThePackageOrTheUnit) {
  EXPECT_EQ(Printed("package q;\n"
                    "  parameter W = 12;\n"
                    "  typedef logic [W-1:0] t;\n"
                    "  typedef struct packed { logic [W-1:0] a; bit b; } s_t;\n"
                    "endpackage\n"
                    "parameter V = 6;\n"
                    "typedef logic [V-1:0] u_t;\n"
                    "module n import q::t; #(int W = 3, V = 2) ();\n"
                    "  import q::s_t;\n"
                    "  t a;\n"
                    "  q::t b;\n"
                    "  s_t c;\n"
                    "  q::s_t d;\n"
                    "  u_t e;\n"
                    "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(a),\n"
                    "                   $bits(b), $bits(c), $bits(d),\n"
                    "                   $bits(e));\n"
                    "  m #(t) u1();\n"
                    "  m #(q::t) u2();\n"
                    "  b #(t) u3();\n"
                    "  b #(q::t) u4();\n"
                    "  m #(u_t) u5();\n"
                    "endmodule\n"
                    "module top; n u(); endmodule\n"),
            "12 12 13 13 6\n"
            "top.u.u1 12\ntop.u.u2 12\ntop.u.u3 12\ntop.u.u4 12\n"
            "top.u.u5 6\n");
}

TEST(PackageTypedefSim, UnpackedDimensionNamesTheParameterOfItsScope) {
  EXPECT_EQ(Printed("package q;\n"
                    "  parameter W = 5;\n"
                    "  typedef byte t [W];\n"
                    "endpackage\n"
                    "parameter V = 6;\n"
                    "typedef byte u_t [V];\n"
                    "module top #(int W = 3, V = 2) ();\n"
                    "  u_t b;\n"
                    "  initial begin\n"
                    "    q::t a;\n"
                    "    $display(\"%0d %0d\", $size(a), $size(b));\n"
                    "  end\n"
                    "endmodule\n"),
            "5 6\n");
}

}  // namespace
