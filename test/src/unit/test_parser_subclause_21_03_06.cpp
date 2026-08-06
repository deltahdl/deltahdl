#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.3.6: file_flush_task ::= $fflush ( [ mcd | fd ] ) ;
// The flush task accepts an optional argument that is either a multi-channel
// descriptor or a single file descriptor; with no argument it flushes all open
// files. Each of the three forms must parse.
TEST(IoSystemTaskParsing, FflushNoArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $fflush();\n"
              "  end\n"
              "endmodule\n"));
}

// The optional argument is a single expression regardless of whether it names
// a multi-channel descriptor or a file descriptor, so one one-argument case
// exercises that grammar branch.
TEST(IoSystemTaskParsing, FflushSingleArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"w\");\n"
              "    $fflush(fd);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

// The argument slot admits any expression that yields a descriptor: a literal
// mcd, a parameter, or a computed value such as the OR of two mcd variables
// or an array element.
TEST(IoSystemTaskParsing, FflushArgumentExpressionForms) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter integer CON = 1;\n"
              "  integer m1, m2;\n"
              "  integer fds [0:3];\n"
              "  initial begin\n"
              "    $fflush(1);\n"
              "    $fflush(CON);\n"
              "    $fflush(m1 | m2);\n"
              "    $fflush(fds[2]);\n"
              "  end\n"
              "endmodule\n"));
}

// The descriptor handed to $fflush may come from a variable whose $fopen is
// its declaration initializer rather than a separate procedural assignment.
TEST(IoSystemTaskParsing, FflushDescriptorFromDeclarationInitializer) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd = $fopen(\"data.txt\", \"w\");\n"
              "  initial begin\n"
              "    $fflush(fd);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

// file_flush_task is a statement, so besides an initial block it can sit in
// any procedural context -- a task body and an always block here.
TEST(IoSystemTaskParsing, FflushInTaskBodyAndAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  reg clk;\n"
              "  task do_flush;\n"
              "    $fflush(fd);\n"
              "  endtask\n"
              "  always @(posedge clk) $fflush();\n"
              "endmodule\n"));
}

// Negative: an unterminated call -- the argument list never closes before the
// statement ends -- must be rejected.
TEST(IoSystemTaskParsing, FflushUnterminatedCallRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    $fflush(fd;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
