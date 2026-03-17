#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- data_declaration ---

TEST(BlockItemDeclElaboration, DataDeclInInitialBlock) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    int x = 42;\n"
      "    x = x + 1;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(BlockItemDeclElaboration, DataDeclInFunctionBody) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  function int f(int a);\n"
      "    int temp;\n"
      "    temp = a + 1;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n"));
}

TEST(BlockItemDeclElaboration, DataDeclInTaskBody) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  task t;\n"
      "    int local_var;\n"
      "    local_var = 1;\n"
      "  endtask\n"
      "endmodule\n"));
}

// --- local_parameter_declaration ---

TEST(BlockItemDeclElaboration, LocalparamInBlock) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    localparam int W = 8;\n"
      "    $display(\"%0d\", W);\n"
      "  end\n"
      "endmodule\n"));
}

// --- parameter_declaration ---

TEST(BlockItemDeclElaboration, ParameterInBlock) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    parameter int D = 4;\n"
      "    $display(\"%0d\", D);\n"
      "  end\n"
      "endmodule\n"));
}

// --- let_declaration ---

TEST(BlockItemDeclElaboration, LetDeclInBlock) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    let add(a, b) = a + b;\n"
      "    $display(\"%0d\", add(1, 2));\n"
      "  end\n"
      "endmodule\n"));
}

// --- data_declaration subtypes ---

TEST(BlockItemDeclElaboration, TypedefInBlock) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    typedef int my_int;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(BlockItemDeclElaboration, ImportInBlock) {
  EXPECT_TRUE(ElabOk(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "module m;\n"
      "  initial begin\n"
      "    import pkg::*;\n"
      "  end\n"
      "endmodule\n"));
}

// --- mixed alternatives ---

TEST(BlockItemDeclElaboration, MixedAlternativesElaborate) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    localparam int W = 8;\n"
      "    parameter int D = 4;\n"
      "    int x;\n"
      "    let inc(a) = a + 1;\n"
      "    x = W + D;\n"
      "  end\n"
      "endmodule\n"));
}

// --- lifetime qualifiers ---

TEST(BlockItemDeclElaboration, AutomaticDataDeclElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x = 0;\n"
      "    x = x + 1;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(BlockItemDeclElaboration, StaticDataDeclElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    static int count = 0;\n"
      "    count = count + 1;\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
