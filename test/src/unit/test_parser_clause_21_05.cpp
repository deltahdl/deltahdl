// §21.5, Syntax 21-13: the writemem_tasks production — $writememb and
// $writememh calls carrying a filename, a memory name, and the nested-optional
// start_addr / finish_addr pair. Each alternative parses as an ordinary
// system-task statement, so the generic call grammar accepts every form of the
// production.
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, WritememhCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritemembCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememb(\"out.bin\", mem);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): the production carries optional start_addr and
// finish_addr arguments after the memory name. The four-argument form must
// parse as well as the bare filename/memory form above.
TEST(IoSystemTaskParsing, WritememWithStartAndFinishAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem, 16, 31);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritemembWithStartAndFinishAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememb(\"out.bin\", mem, 16, 31);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): finish_addr is nested inside the start_addr option, so
// a three-argument call (filename, memory_name, start_addr) is a distinct,
// legal form of the production.
TEST(IoSystemTaskParsing, WritememWithStartAddrOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem, 16);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): memory_name follows the same forms as the §21.4 read
// side — a partially indexed multidimensional array naming a lesser-
// dimensioned memory is accepted in the memory_name position.
TEST(IoSystemTaskParsing, WritememWithPartiallyIndexedMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:3][0:255];\n"
              "  initial $writememh(\"out.hex\", mem[1]);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): the start-only nesting applies to the $writememb
// alternative just as it does to $writememh.
TEST(IoSystemTaskParsing, WritemembWithStartAddrOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememb(\"out.bin\", mem, 16);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): memory_name may also be a hierarchical name reaching
// a memory declared in an instantiated scope.
TEST(IoSystemTaskParsing, WritememWithHierarchicalMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  sub u1();\n"
              "  initial $writememh(\"out.hex\", u1.mem);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): memory_name may name a sub-range of the memory's
// lowest dimension with slice syntax, as on the §21.4 read side.
TEST(IoSystemTaskParsing, WritememWithSliceMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem[16:31]);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): the operands are ordinary expressions, not bare
// tokens — the filename may be a string variable and the address bounds may
// be parameters or arithmetic over them.
TEST(IoSystemTaskParsing, WritememOperandsMayBeExpressions) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter BASE = 16;\n"
              "  string fn;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(fn, mem, BASE, BASE + 15);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): writemem_tasks is a statement, so a call may sit in
// any procedural context — an always block or a task body, not only an
// initial block.
TEST(IoSystemTaskParsing, WritememInAlwaysAndTaskPositions) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg clk;\n"
              "  reg [7:0] mem [0:255];\n"
              "  task dump;\n"
              "    $writememb(\"out.bin\", mem);\n"
              "  endtask\n"
              "  always @(posedge clk) $writememh(\"out.hex\", mem);\n"
              "endmodule\n"));
}

// The negative form: an argument list left unterminated is not an instance of
// the production and must be rejected by the call grammar.
TEST(IoSystemTaskParsing, UnterminatedWritememRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem;\n"
              "endmodule\n"));
}

}  // namespace
