#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- R7/R14: Hierarchical name read in expression ---

TEST(HierarchicalNameParsing, HierarchicalReferenceSyntax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", top.sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

// --- R14: Hierarchical name written in procedural assignment ---

TEST(HierarchicalNameParsing, HierarchicalNameAsProceduralLhs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    top.sub.sig = 1;\n"
              "  end\n"
              "endmodule\n"));
}

// --- R14: Hierarchical name triggered off in event expression ---

TEST(HierarchicalNameParsing, HierarchicalNameInEventControl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    @(top.sub.done);\n"
              "  end\n"
              "endmodule\n"));
}

// --- R14: Hierarchical name used to reference subroutine ---

TEST(HierarchicalNameParsing, HierarchicalNameAsSubroutineCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    top.sub.my_task();\n"
              "  end\n"
              "endmodule\n"));
}

// --- R3: Named begin-end block is referenceable through hierarchical path ---

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

// --- R3: Named fork-join block is referenceable through hierarchical path ---

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

// --- R14: Hierarchical name on LHS of continuous assignment ---

TEST(HierarchicalNameParsing, HierarchicalNameInContinuousAssignLhs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic val;\n"
              "  assign top.sub.net1 = val;\n"
              "endmodule\n"));
}

// --- R14: Hierarchical name on LHS of nonblocking assignment ---

TEST(HierarchicalNameParsing, HierarchicalNameInNonblockingAssignLhs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    top.sub.sig <= 1;\n"
              "  end\n"
              "endmodule\n"));
}

// §23.6 Syntax 23-7: hierarchical_identifier ::= [ $root . ] { identifier
// constant_bit_select . } identifier.  The optional `$root .` prefix marks
// the absolute root of the design; the parser must accept it on a
// hierarchical reference.
TEST(HierarchicalNameParsing, RootPrefixedHierarchicalReference) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", $root.top.sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

// §23.6 Syntax 23-7: each non-final identifier in a hierarchical name may
// be followed by a constant_bit_select (the §23.6 "instance select"
// expression for array elements).  The parser must accept a hierarchical
// reference whose interior component carries a bit-select.
TEST(HierarchicalNameParsing, HierarchicalReferenceWithInstanceSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", top.arr[3].sig);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
