#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <initializer_list>
#include <utility>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ProceduralAssignmentElaboration, VariableLhsIsAccepted) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    v = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignmentElaboration, ProceduralAssignToNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
}

TEST(ProceduralAssignmentElaboration, NetInStreamingTargetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire [3:0] w, n;\n"
      "  logic [3:0] v, x;\n"
      "  initial begin\n"
      "    {>>{w, v}} = {x, x};\n"
      "    {>>{v, {<<{n}}}} = {x, x};\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'w' cannot be the target of a procedural assignment", 5, "10.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'n' cannot be the target of a procedural assignment", 6, "10.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "'v'", 5, "10.4"));
}

TEST(ProceduralAssignmentElaboration, NonblockingAssignToNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
}

TEST(ProceduralAssignmentElaboration, SelectOfNetBaseIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  initial begin\n"
      "    w[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
}

TEST(ProceduralAssignmentElaboration, ConcatenationContainingNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    {v, w} = 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            5, "10.4"));
}

TEST(ProceduralAssignmentElaboration, AssignToUndeclaredNonAnsiPortIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t(q);\n"
      "  output q;\n"
      "  initial begin\n"
      "    q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
}

TEST(ProceduralAssignmentElaboration, AssignToNonAnsiPortDeclaredAVariable) {
  SimFixture f;
  ElaborateSrc(
      "module t(q);\n"
      "  output q;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignmentElaboration, NetTargetInSubroutineOrGenerateIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  if (1) begin : g initial w = 1; end\n"
      "  task tk; w = 0; endtask\n"
      "  function void fn(); w = 0; endfunction\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "cannot be the target of a procedural assignment",
                              line, "10.4"));
  }
}

TEST(ProceduralAssignmentElaboration, LocalNameShadowingNetIsAccepted) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w, k;\n"
      "  initial begin logic w; w = 1; end\n"
      "  task tk(output logic w); w = 0; endtask\n"
      "  initial for (int k = 0; k < 2; k++) k = k;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(FindDiag(f, "cannot be the target of a procedural assignment"),
            nullptr);
}

TEST(ProceduralAssignmentElaboration, TimingControlOnAssignmentOfNewIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  class C; endclass\n"
      "  int d[]; C c; logic clk; int x;\n"
      "  initial d = #1 new[4];\n"
      "  initial c = @(posedge clk) new;\n"
      "  initial x = #1 3;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "an assignment of 'new' takes no "
                              "intra-assignment delay or event control",
                              line, "10.4"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "an assignment of 'new' takes no "
                             "intra-assignment delay or event control",
                             6, "10.4"));
}

TEST(ProceduralAssignmentElaboration,
     AssignmentOfAnEnumerationConstantIsError) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef enum {A, B} e_t;\n"
      "  logic q;\n"
      "  initial begin\n"
      "    A = B;\n"
      "    B <= A;\n"
      "    {q, A} = 2;\n"
      "    q = A;\n"
      "  end\n"
      "endmodule\n",
      f);
  const std::pair<const char*, uint32_t> kReports[] = {
      {"A", 5}, {"B", 6}, {"A", 7}};
  for (const auto& [name, line] : kReports) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("assignment of constant '{}', which is not a variable",
                    name),
        line, "10.4"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "of constant", 8, "10.4"));
}

struct EnumConstantWrite {
  const char* where;
  const char* src;
  uint32_t line;
};

TEST(ProceduralAssignmentElaboration,
     AssignmentOfAnEnumerationConstantOutsideAModuleIsError) {
  const EnumConstantWrite kWrites[] = {
      {"a compilation-unit function",
       "typedef enum {A, B} e_t;\nfunction void f();\n  A = B;\n"
       "endfunction\nmodule m;\nendmodule\n",
       3},
      {"a package function",
       "package p;\n  typedef enum {A, B} e_t;\n  function void f();\n"
       "    A = B;\n  endfunction\nendpackage\nmodule m;\nendmodule\n",
       4},
  };
  for (const EnumConstantWrite& write : kWrites) {
    SCOPED_TRACE(write.where);
    SimFixture f;
    ElaborateSrc(write.src, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "assignment of constant 'A', which is not a variable",
                      write.line, "10.4"));
  }
}

TEST(ProceduralAssignmentElaboration,
     AssignmentOfAnEnumerationVariableOutsideAModuleIsAccepted) {
  const char* const kSources[] = {
      "typedef enum {A, B} e_t;\ne_t v;\nfunction void f();\n  v = B;\n"
      "endfunction\nmodule m;\nendmodule\n",
      "package p;\n  typedef enum {A, B} e_t;\n  e_t v;\n"
      "  function void f();\n    v = B;\n  endfunction\nendpackage\n"
      "module m;\nendmodule\n",
  };
  for (const char* src : kSources) {
    SCOPED_TRACE(src);
    EXPECT_TRUE(ElabOk(src));
  }
}

TEST(ProceduralAssignmentElaboration,
     NetTargetInSubroutineInsideGenerateBlocksIsRejected) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "wire w;", "task t; w = 1; endtask"},
      "net 'w' cannot be the target of a procedural assignment", "10.4"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "wire w;", "function void f; w = 1; endfunction"},
      "net 'w' cannot be the target of a procedural assignment", "10.4"));
  EXPECT_TRUE(
      AcceptedInsideGenerateBlocks({"", "logic v;", "task t; v = 1; endtask"}));
}

}  // namespace
