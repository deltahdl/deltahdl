#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

struct NamedSource {
  std::string name;
  std::string src;
};

void ExpectReportAtName(const NamedSource& item, const std::string& message,
                        const char* subclause, const std::string& at = "") {
  SCOPED_TRACE(item.src);
  ElabFixture f;
  ElaborateSrc(item.src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(item.src, at.empty() ? item.name : at),
                            subclause));
}

void ExpectUnresolved(const NamedSource& item, const std::string& at = "") {
  ExpectReportAtName(item,
                     "reference to unresolved identifier '" + item.name + "'",
                     "23.9", at);
}

void ExpectNoError(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

std::string InModule(const std::string& body) {
  return "module top;\n" + body + "endmodule\n";
}

std::vector<std::string> PlacesAround(const std::string& item) {
  return {
      "interface i;\n" + item +
          "endinterface\nmodule top;\n  i u();\n"
          "endmodule\n",
      "program p;\n" + item +
          "endprogram\nmodule top;\n  p u();\n"
          "endmodule\n",
      "checker k;\n" + item +
          "endchecker\nmodule top;\n  k u();\n"
          "endmodule\n",
      "package pk;\n" + item + "endpackage\nmodule top;\nendmodule\n",
      "module top;\n  if (1) begin : g\n" + item + "  end\nendmodule\n",
      item + "module top;\nendmodule\n",
  };
}

TEST(UndeclaredCallInAnExpression, DISABLED_EachExpressionPositionIsReported) {
  for (const char* body :
       {"  int y = nosuch();\n", "  int y;\n  initial y = nosuch(1) + 1;\n",
        "  wire w;\n  assign w = nosuch();\n",
        "  initial if (nosuch()) $display(\"x\");\n",
        ("  function int g(int a); return a; endfunction\n"
         "  initial $display(g(nosuch()));\n"),
        "  initial void'(nosuch());\n"}) {
    ExpectReportAtName({"nosuch", InModule(body)},
                       "undeclared identifier 'nosuch'", "23.9");
  }
}

TEST(UndeclaredCallInAnExpression,
     DISABLED_AnInitializerCallIsReportedInEveryScope) {
  std::vector<std::string> sources = {
      ("module top;\n  int y;\n  task t;\n    y = nosuch();\n  endtask\n"
       "endmodule\n"),
      ("module top;\n  function int f();\n    return nosuch();\n  endfunction\n"
       "endmodule\n"),
      ("module top;\n  class c;\n    function int m();\n      return "
       "nosuch();\n    endfunction\n  endclass\nendmodule\n"),
      ("package pk;\n  function int f();\n    return nosuch();\n  endfunction\n"
       "endpackage\nmodule top;\nendmodule\n"),
      ("function int f();\n  return nosuch();\nendfunction\nmodule top;\n"
       "endmodule\n"),
  };
  for (const auto& place : PlacesAround("  int y = nosuch();\n")) {
    if (place.find("package") != 0 && place.find("int y") != 0) {
      sources.push_back(place);
    }
  }
  for (const auto& src : sources) {
    ExpectReportAtName({"nosuch", src}, "undeclared identifier 'nosuch'",
                       "23.9");
  }
}

TEST(UndeclaredCallInAnExpression, CallsOfDeclaredFunctionsAreAccepted) {
  ExpectNoError(
      "package pk;\n  function int h(); return 3; endfunction\nendpackage\n"
      "function int u(); return 2; endfunction\n"
      "module top;\n  import pk::*;\n"
      "  function int g(int a = 0); return a; endfunction\n"
      "  int y = g();\n  int z;\n  wire w;\n  assign w = g();\n"
      "  initial begin\n    z = g(1) + 1;\n    if (g()) $display(\"x\");\n"
      "    $display(g(g()));\n    void'(g());\n    z = h() + u();\n  end\n"
      "endmodule\n");
}

const std::vector<NamedSource>& ModuleConstantPositions() {
  static const std::vector<NamedSource> kPositions = {
      {"W", "  logic [W-1:0] v;\n"},
      {"N", "  logic v [N];\n"},
      {"Q", "  localparam int P = Q + 1;\n"},
      {"EN", "  if (EN) begin : g end\n"},
      {"SEL", "  case (SEL) 0: begin : g end endcase\n"},
      {"D", "  wire #(D) w;\n"},
      {"D", "  wire w;\n  assign #D w = 1;\n"},
  };
  return kPositions;
}

TEST(UndeclaredNameInAConstantPosition,
     DISABLED_EachConstantPositionInAModuleIsReported) {
  for (const auto& position : ModuleConstantPositions()) {
    ExpectUnresolved({position.name, InModule(position.src)});
  }
  ExpectUnresolved({"Q", "module top #(parameter int P = Q);\nendmodule\n"});
}

TEST(UndeclaredNameInAConstantPosition,
     DISABLED_EachConstantPositionIsReportedInEveryScope) {
  for (const auto& position : ModuleConstantPositions()) {
    for (const auto& place : PlacesAround(position.src)) {
      bool in_checker = place.find("checker") == 0;
      bool in_package = place.find("package") == 0;
      bool unit_level = place.find(position.src) == 0;
      bool generate_item = position.name == "EN" || position.name == "SEL";
      bool net_item = position.name == "D";
      if (in_checker && (net_item || position.name == "Q")) continue;
      if ((in_package || unit_level) && (generate_item || net_item)) continue;
      ExpectUnresolved({position.name, place});
    }
  }
}

TEST(UndeclaredNameInAConstantPosition,
     DISABLED_AUnitParameterDeclaredAfterTheModuleIsUnresolved) {
  ExpectUnresolved({"W",
                    "module top;\n  logic [W-1:0] v;\nendmodule\n"
                    "localparam int W = 8;\n"});
}

TEST(UndeclaredNameInAConstantPosition,
     DeclaredNamesInEveryConstantPositionAreAccepted) {
  ExpectNoError(
      "package pk;\n  localparam int PW = 4;\nendpackage\n"
      "localparam int UW = 2;\n"
      "module top #(parameter int H = 1);\n  import pk::*;\n"
      "  localparam int W = 4, N = 2, Q = 1, EN = 1, SEL = 0, D = 1;\n"
      "  logic [W-1:0] v;\n  logic u [N];\n  localparam int P = Q + 1;\n"
      "  if (EN) begin : g end\n  case (SEL) 0: begin : c end endcase\n"
      "  wire #(D) w;\n  wire x;\n  assign #D x = 1;\n"
      "  logic [PW-1:0] pv;\n  logic [UW-1:0] uv;\n  logic [H:0] hv;\n"
      "  for (genvar i = 0; i < 2; i++) begin : l\n    logic [i:0] gv;\n"
      "  end\nendmodule\n");
}

const std::vector<NamedSource>& ClassConstantPositions() {
  static const std::vector<NamedSource> kPositions = {
      {"NOPE1", "    int x = NOPE1;\n"},
      {"NOPE5", "    static int s = NOPE5;\n"},
      {"NOPE2", "    bit [NOPE2-1:0] v;\n"},
      {"NOPE3", "    int arr[NOPE3];\n"},
      {"NOPE4", "    typedef bit [NOPE4:0] tt;\n"},
      {"NOPE6", "    localparam int LP = NOPE6;\n"},
      {"NOPE7", "    function void m(int a = NOPE7); endfunction\n"},
  };
  return kPositions;
}

TEST(UndeclaredNameInAClassDeclaration,
     DISABLED_EachClassPositionIsReportedWhereverTheClassIsDeclared) {
  for (const auto& position : ClassConstantPositions()) {
    std::string cls = "  class c;\n" + position.src + "  endclass\n";
    std::vector<std::string> places = PlacesAround(cls);
    places.push_back(InModule(cls));
    for (const auto& place : places) {
      if (place.find("checker") == 0) continue;
      ExpectUnresolved({position.name, place});
    }
  }
}

TEST(UndeclaredNameInAClassDeclaration,
     ADeclaredParameterInEveryClassPositionIsAccepted) {
  ExpectNoError(
      "module top;\n  class c #(parameter int P = 4);\n    int x = P;\n"
      "    static int s = P;\n    bit [P-1:0] v;\n    int arr[P];\n"
      "    typedef bit [P:0] tt;\n    localparam int LP = P;\n"
      "    function void m(int a = P); endfunction\n  endclass\n"
      "endmodule\n");
}

struct LikeNamedMembers {
  std::string body;
  std::string second;
};

TEST(ClassScopeRedeclaration, DISABLED_EachPairOfLikeNamedMembersIsReported) {
  const std::vector<LikeNamedMembers> kPairs = {
      {"    int x;\n", "    int x;\n"},
      {"    int x;\n", "    function int x(); return 0; endfunction\n"},
      {"    function int x(); return 0; endfunction\n", "    int x;\n"},
      {"    int x;\n", "    task x(); endtask\n"},
      {"    function void x(); endfunction\n",
       "    function void x(); endfunction\n"},
      {"    typedef int x;\n", "    int x;\n"},
      {"    localparam int x = 1;\n", "    int x;\n"},
      {"    parameter int x = 1;\n", "    int x;\n"},
      {"    class x;\n    endclass\n", "    int x;\n"},
  };
  for (const auto& pair : kPairs) {
    std::string src = "module top;\n  class c;\n" + pair.body + pair.second +
                      "  endclass\nendmodule\n";
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'",
                              LinesHolding(src, " x").back(), "23.9"));
  }
}

TEST(ClassScopeRedeclaration,
     DISABLED_TwoPureVirtualMethodsOfOneNameInAnInterfaceClassAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface class ic;\n"
      "  pure virtual function void x();\n"
      "  pure virtual function void x();\n"
      "endclass\n"
      "module top;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "23.9"));
}

TEST(ClassScopeRedeclaration, OneNameInDistinctScopesOfClassesIsAccepted) {
  ExpectNoError(
      "module top;\n"
      "  class a;\n    int x;\n    function int f();\n      int x;\n"
      "      return x;\n    endfunction\n  endclass\n"
      "  class b;\n    int x;\n  endclass\n"
      "  class d extends a;\n    int x;\n  endclass\n"
      "endmodule\n");
}

TEST(UninstantiatedGenerateRedeclaration,
     DISABLED_ADuplicateInABlockNeverInstantiatedIsReported) {
  for (const char* body :
       {"  if (0) begin : g\n    int a;\n    int a;\n  end\n",
        ("  for (genvar i = 0; i < 0; i++) begin : g\n    int a;\n    int a;\n"
         "  end\n"),
        ("  case (1)\n    0: begin : g\n      int a;\n      int a;\n    end\n"
         "    default: begin : h end\n  endcase\n")}) {
    std::string src = InModule(body);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'a'",
                              LinesHolding(src, "int a").back(), "6.5"));
  }
}

TEST(UninstantiatedGenerateRedeclaration,
     DISABLED_ADuplicateInAModuleNothingInstantiatesIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module other;\n"
      "  if (1) begin : g\n"
      "    int a;\n"
      "    int a;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'a'", 4, "6.5"));
}

TEST(UninstantiatedGenerateRedeclaration,
     DistinctNamesInABlockNeverInstantiatedAreAccepted) {
  ExpectNoError(InModule(
      "  if (0) begin : g\n    int a;\n    int b;\n  end\n"
      "  for (genvar i = 0; i < 0; i++) begin : l\n    int a;\n    int b;\n"
      "  end\n"));
}

TEST(UpwardSearchEdges,
     DISABLED_AnInnerBlocksVariableIsNotVisibleAfterTheBlockCloses) {
  ExpectUnresolved({"hv",
                    "module m;\n  int r;\n  initial begin : g\n"
                    "    begin : h\n      int hv;\n    end\n    r = hv;\n"
                    "  end\nendmodule\n"},
                   "= hv");
}

TEST(UpwardSearchEdges, AnInnerBlocksVariableIsReachedThroughItsName) {
  ExpectNoError(
      "module m;\n  int r;\n  initial begin : g\n"
      "    begin : h\n      int hv;\n    end\n    r = h.hv;\n"
      "  end\nendmodule\n");
}

TEST(UpwardSearchEdges, ASiblingTasksLocalIsNotVisible) {
  ExpectUnresolved({"loc",
                    "module m;\n  int r;\n  task t1;\n    int loc;\n  endtask\n"
                    "  task t2;\n    r = loc;\n  endtask\nendmodule\n"},
                   "= loc");
}

TEST(UpwardSearchEdges, AFunctionBodyStopsAtTheModuleEdge) {
  ExpectUnresolved({"v",
                    "module child;\n  function int f();\n    return v;\n"
                    "  endfunction\nendmodule\n"
                    "module top;\n  integer v;\n  child u1();\nendmodule\n"},
                   "return v");
}

TEST(UpwardSearchEdges, AnInterfaceAndAProgramStopAtTheirEdge) {
  for (const char* src :
       {("interface ifc;\n  initial outer_x = 1;\nendinterface\n"
         "module top;\n  logic outer_x;\n  ifc i();\nendmodule\n"),
        ("program p;\n  initial outer_x = 1;\nendprogram\n"
         "module top;\n  logic outer_x;\n  p u();\nendmodule\n")}) {
    ExpectReportAtName({"outer_x", src}, "undeclared identifier 'outer_x'",
                       "23.9");
  }
}

TEST(UpwardSearchEdges, ACheckerStopsAtItsEdge) {
  ExpectUnresolved(
      {"outer_x",
       "checker chk(logic clk);\n  assert property (@(posedge clk) outer_x);\n"
       "endchecker\nmodule top;\n  logic clk, outer_x;\n  chk c(clk);\n"
       "endmodule\n"});
}

TEST(UpwardSearchEdges, AParentDoesNotSeeItsChildsVariable) {
  ExpectReportAtName({"inner_x",
                      "module child;\n  logic inner_x;\nendmodule\n"
                      "module top;\n  child c();\n  initial inner_x = 1;\n"
                      "endmodule\n"},
                     "undeclared identifier 'inner_x'", "23.9", "inner_x = 1");
}

}  // namespace
