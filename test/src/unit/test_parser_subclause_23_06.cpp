#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(HierarchicalNameParsing, HierarchicalReferenceSyntax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", top.sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, HierarchicalNameAsProceduralLhs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    top.sub.sig = 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, HierarchicalNameInEventControl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    @(top.sub.done);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, HierarchicalNameAsSubroutineCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    top.sub.my_task();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, HierarchicalPathThroughNamedBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin : blk\n"
              "    logic x;\n"
              "    x = 1;\n"
              "  end\n"
              "  initial begin\n"
              "    $display(\"%0d\", m.blk.x);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, HierarchicalPathThroughNamedForkBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork : f1\n"
              "    logic y;\n"
              "  join\n"
              "  initial begin\n"
              "    $display(\"%0d\", m.f1.y);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, HierarchicalNameInContinuousAssignLhs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic val;\n"
              "  assign top.sub.net1 = val;\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, HierarchicalNameInNonblockingAssignLhs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    top.sub.sig <= 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, RootPrefixedHierarchicalReference) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", $root.top.sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, HierarchicalReferenceWithInstanceSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", top.arr[3].sig);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, InstanceSelectFollowedByMoreThanOneMember) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", arr[3].sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, RootedNameTakesSeveralSelects) {
  EXPECT_TRUE(
      ParseOk("module sub;\n"
              "  initial #1 $display(\"v=%0d\", $root.top.arr[1][0]);\n"
              "endmodule\n"
              "module top;\n"
              "  logic arr [1:0][1:0];\n"
              "  sub c();\n"
              "endmodule\n"));
}

TEST(HierarchicalNameParsing, RootedNameTakesACall) {
  EXPECT_TRUE(
      ParseOk("class D;\n"
              "  rand int x;\n"
              "  function int f(); return 1; endfunction\n"
              "endclass\n"
              "module child;\n"
              "  D d = new;\n"
              "endmodule\n"
              "module m;\n"
              "  int i;\n"
              "  child u();\n"
              "  initial begin\n"
              "    i = $root.m.u.d.f();\n"
              "    $root.m.u.d.f();\n"
              "    i = $root.m.u.d.randomize() with { x > 0; };\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
